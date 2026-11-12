import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { createApp, requestInput, projectRoot } from '../server.mjs';
import { join } from 'node:path';

function fixtureRunner(mode, path) {
  return readFile(path, 'utf8').then(graph => {
    assert.match(graph, /vertices 4/);
    return { code: 0, stdout: mode === 'shortest' ? '0: 0\n1: 2\n2: 5\n3: 3'
      : mode === 'optimal' ? '0: min=0,count=1\n1: min=2,count=1\n2: min=5,count=2\n3: min=3,count=1'
      : '0: 1\n1: 1\n2: 2\n3: 3', stderr: '' };
  });
}
const fixture = await readFile(join(projectRoot,'examples','diamond.txt'), 'utf8');

const server = createApp({runner:fixtureRunner});
await new Promise(ok => server.listen(0, '127.0.0.1', ok));
const base = `http://127.0.0.1:${server.address().port}`;
test.after(async () => { await new Promise(ok => server.close(ok)); });

test('UI serves editor, visualization, and three buttons', async () => {
  const response = await fetch(base);
  assert.equal(response.status, 200);
  const html = await response.text();
  for (const text of ['graph-text','graph-svg','run-shortest','run-paths','run-optimal','result-output']) assert.ok(html.includes(text));
  assert.equal((await fetch(base+'/app.js')).status,200);
  assert.equal((await fetch(base+'/style.css')).status,200);
});
test('health check', async () => {
  assert.deepEqual(await (await fetch(base+'/api/health')).json(), {status:'ok'});
});
test('all three modes send graph files to runner', async () => {
  for (const mode of ['shortest','paths','optimal']) {
    const r = await fetch(base+'/api/run',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({mode,graph:fixture})});
    assert.equal(r.status,200);
    assert.match((await r.json()).output, mode === 'optimal' ? /2: min=5,count=2/ : /3: 3/);
  }
});
test('rejects unknown modes and missing graph', async () => {
  for (const body of [{mode:'rm',graph:fixture},{mode:'paths'}]) {
    const r = await fetch(base+'/api/run',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body)});
    assert.equal(r.status,400);
  }
  assert.throws(()=>requestInput({mode:'shortest',graph:1}));
});
test('propagates Lean parser errors', async () => {
  const broken = createApp({runner:async()=>({code:1,stdout:'',stderr:'error: expected FROM < TO'})});
  await new Promise(ok=>broken.listen(0,'127.0.0.1',ok));
  try {
    const response = await fetch(`http://127.0.0.1:${broken.address().port}/api/run`,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({mode:'paths',graph:fixture})});
    assert.equal(response.status,422);
    assert.match((await response.json()).error,/FROM < TO/);
  } finally { await new Promise(ok=>broken.close(ok)); }
});

test('trace endpoint delegates to a distinct Lean trace executable', async () => {
  const records = [];
  const runner = async (mode, file, isTrace) => {
    records.push({mode, graph:await readFile(file, 'utf8'), isTrace});
    return { code:0, stdout:'start|0|0\nfinish|0|0', stderr:'' };
  };
  const app = createApp({runner});
  await new Promise(ok=>app.listen(0,'127.0.0.1',ok));
  try {
    for (const mode of ['shortest','paths','optimal']) {
      const r = await fetch(`http://127.0.0.1:${app.address().port}/api/trace`, {
        method:'POST',headers:{'Content-Type':'application/json'},
        body:JSON.stringify({mode,graph:fixture})
      });
      assert.equal(r.status,200);
      assert.equal((await r.json()).output,'start|0|0\nfinish|0|0');
    }
    assert.equal(records.length,3);
    assert.ok(records.every(r=>r.isTrace === true && r.graph === fixture));
  } finally { await new Promise(ok=>app.close(ok)); }
});
