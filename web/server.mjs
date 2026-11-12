/**
 * GraphFold local UI server (Node.js 20+, no external packages).
 * Static HTML/JS is served at 127.0.0.1:8787 by default. POST /api/run
 * writes a temporary graph file and invokes the actual Lean executable.
 * No graph algorithm is reimplemented in JavaScript.
 */
import http from 'node:http';
import { readFile, mkdtemp, writeFile, rm } from 'node:fs/promises';
import { spawn } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join, dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

export const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const publicRoot = join(projectRoot, 'web', 'public');
const MAX_BODY = 256 * 1024;
const TIMEOUT_MS = 20_000;
const files = new Map([
  ['/', ['index.html', 'text/html; charset=utf-8']],
  ['/app.js', ['app.js', 'text/javascript; charset=utf-8']],
  ['/style.css', ['style.css', 'text/css; charset=utf-8']]
]);

/** Validate request shape, not graph semantics: the Lean parser owns those. */
export function requestInput(body) {
  if (typeof body !== 'object' || body === null || Array.isArray(body))
    throw new Error('Expected a JSON object');
  if (body.mode !== 'shortest' && body.mode !== 'paths' && body.mode !== 'optimal')
    throw new Error('mode must be "shortest", "paths", or "optimal"');
  if (typeof body.graph !== 'string' || Buffer.byteLength(body.graph, 'utf8') > MAX_BODY)
    throw new Error('graph must be a UTF-8 string of at most 256 KiB');
  return { mode: body.mode, graph: body.graph };
}

/** Run a process without a shell; collect bounded stdout/stderr. */
export function runProcess(command, args, cwd = projectRoot) {
  return new Promise((done, fail) => {
    const child = spawn(command, args, { cwd, shell: false, stdio: ['ignore', 'pipe', 'pipe'] });
    let out = '', err = '', bytes = 0, settled = false;
    const finish = (failure, result) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      if (failure) fail(failure); else done(result);
    };
    const timer = setTimeout(() => { child.kill('SIGKILL'); finish(new Error('Lean executable timed out')); }, TIMEOUT_MS);
    const collect = (stream, where) => stream.on('data', (chunk) => {
      bytes += chunk.length;
      if (bytes > MAX_BODY) { child.kill('SIGKILL'); finish(new Error('Lean output exceeded 256 KiB')); return; }
      if (where === 'stdout') out += chunk.toString('utf8'); else err += chunk.toString('utf8');
    });
    collect(child.stdout, 'stdout'); collect(child.stderr, 'stderr');
    child.once('error', (e) => finish(new Error(`Could not start ${command}: ${e.message}`)));
    child.once('close', (code, signal) => finish(null, { code, signal, stdout: out.trim(), stderr: err.trim() }));
  });
}

/** Prefer already-built Lake binaries; they are produced by `lake build`. */
export async function leanRunner(mode, graphFile, trace = false) {
  const command = trace ? 'trace' : mode;
  const args = trace ? [mode, graphFile] : [graphFile];
  const binary = join(projectRoot, '.lake', 'build', 'bin', command);
  try {
    return await runProcess(binary, args);
  } catch (error) {
    if (error.code === 'ENOENT' || /^Could not start/.test(error.message)) {
      return runProcess('lake', ['exe', command, ...args]);
    }
    throw error;
  }
}

const jsonHeaders = {
  'Content-Type': 'application/json; charset=utf-8',
  'Cache-Control': 'no-store',
  'X-Content-Type-Options': 'nosniff'
};
const securityHeaders = {
  'X-Content-Type-Options': 'nosniff',
  'Referrer-Policy': 'no-referrer',
  'Content-Security-Policy': "default-src 'self'; script-src 'self'; style-src 'self'; img-src 'self' data:; object-src 'none'; base-uri 'none'; frame-ancestors 'none'"
};
function sendJson(res, status, value) {
  res.writeHead(status, { ...securityHeaders, ...jsonHeaders });
  res.end(JSON.stringify(value));
}

/** Independent injectable runner makes the HTTP boundary testable without Lean. */
export function createApp({ runner = leanRunner } = {}) {
  return http.createServer(async (req, res) => {
    try {
      const url = new URL(req.url, 'http://localhost');
      if (req.method === 'GET' && files.has(url.pathname)) {
        const [fileName, contentType] = files.get(url.pathname);
        const contents = await readFile(join(publicRoot, fileName));
        res.writeHead(200, { ...securityHeaders, 'Content-Type': contentType, 'Cache-Control': 'no-cache' });
        res.end(contents);
        return;
      }
      if (req.method === 'GET' && url.pathname === '/api/health') {
        sendJson(res, 200, { status: 'ok' }); return;
      }
      if (req.method !== 'POST' || !['/api/run', '/api/trace'].includes(url.pathname)) {
        sendJson(res, 404, { error: 'Not found' }); return;
      }
      const chunks = [];
      let total = 0;
      for await (const chunk of req) {
        total += chunk.length;
        if (total > MAX_BODY + 2048) {
          sendJson(res, 413, { error: 'Request too large' }); return;
        }
        chunks.push(chunk);
      }
      let body;
      try { body = JSON.parse(Buffer.concat(chunks).toString('utf8')); }
      catch { sendJson(res, 400, { error: 'Malformed JSON' }); return; }
      let input;
      try { input = requestInput(body); }
      catch (e) { sendJson(res, 400, { error: e.message }); return; }
      const directory = await mkdtemp(join(tmpdir(), 'graphfold-'));
      try {
        const graphFile = join(directory, 'input.txt');
        await writeFile(graphFile, input.graph, 'utf8');
        const trace = url.pathname === '/api/trace';
        const result = await runner(input.mode, graphFile, trace);
        if (result.code !== 0) {
          sendJson(res, 422, { error: result.stderr || result.stdout || `Process exited with code ${result.code}` });
        } else {
          sendJson(res, 200, { mode: input.mode, output: result.stdout });
        }
      } finally {
        await rm(directory, { recursive: true, force: true });
      }
    } catch (error) {
      sendJson(res, 500, { error: error.message || 'Internal server error' });
    }
  });
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const port = Number(process.env.PORT || '8787');
  const host = process.env.HOST || '127.0.0.1';
  if (!Number.isInteger(port) || port < 0 || port > 65535) {
    process.stderr.write('PORT must be an integer between 0 and 65535\n');
    process.exitCode = 1;
  } else {
    createApp().listen(port, host, () => {
      process.stdout.write(`GraphFold UI: http://${host}:${port}\n`);
      process.stdout.write('Use Ctrl+C to stop. Build Lean binaries with: lake build\n');
    });
  }
}
