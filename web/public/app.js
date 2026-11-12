/** Browser-only visualization and syntax checking. Evaluation uses /api/run (Lean). */
const editor = document.querySelector('#graph-text');
const numbers = document.querySelector('#line-numbers');
const parseStatus = document.querySelector('#parse-status');
const graphCount = document.querySelector('#graph-count');
const svg = document.querySelector('#graph-svg');
const graphError = document.querySelector('#graph-error');
const resultOutput = document.querySelector('#result-output');
const resultName = document.querySelector('#result-name');
const resultDescription = document.querySelector('#result-description');
const buttons = [document.querySelector('#run-shortest'), document.querySelector('#run-paths'), document.querySelector('#run-optimal')];
const original = editor.value;
let graph = null;
let requestSerial = 0;
let selectedMode = null;
let traceEvents = [];
let traceIndex = 0;
let traceTimer = null;
let traceRequestSerial = 0;
const NS = 'http://www.w3.org/2000/svg';

/** Parse the same declared syntax and topological constraint as Format.parse. */
export function parseGraph(text) {
  const lines = text.split(/\r?\n/).map((raw, index) => ({
    text: raw.split('#')[0].trim(), line: index + 1
  })).filter(x => x.text);
  const fail = (line, detail) => { throw new Error(`Line ${line}: ${detail}`); };
  if (lines.length < 2) throw new Error('Expected vertices N and source S header lines');
  const fields = (item) => item.text.split(/\s+/);
  const nat = (s, line) => {
    if (!/^\d+$/.test(s)) fail(line, `expected a nonnegative integer, got “${s}”`);
    const n = Number(s);
    if (!Number.isSafeInteger(n)) fail(line, 'integer is too large for graph visualization');
    return n;
  };
  const h1 = fields(lines[0]), h2 = fields(lines[1]);
  if (h1.length !== 2 || h1[0] !== 'vertices') fail(lines[0].line, 'expected vertices N');
  if (h2.length !== 2 || h2[0] !== 'source') fail(lines[1].line, 'expected source S');
  const count = nat(h1[1], lines[0].line);
  const source = nat(h2[1], lines[1].line);
  if (count < 1) fail(lines[0].line, 'vertex count must be positive');
  if (count > 150) fail(lines[0].line, 'visualizer supports at most 150 vertices');
  if (source >= count) fail(lines[1].line, 'source must be smaller than vertex count');
  const edges = [];
  for (const line of lines.slice(2)) {
    const tokens = fields(line);
    if (tokens.length !== 4 || tokens[0] !== 'edge') fail(line.line, 'expected edge FROM TO WEIGHT');
    const from = nat(tokens[1], line.line), to = nat(tokens[2], line.line);
    const weight = nat(tokens[3], line.line);
    if (from >= count || to >= count) fail(line.line, `vertex index must be less than ${count}`);
    if (from >= to) fail(line.line, 'expected FROM < TO (topological order)');
    edges.push({ from, to, weight });
  }
  if (edges.length > 800) throw new Error('Visualizer supports at most 800 edges');
  return { count, source, edges };
}

function el(name, attrs = {}, parent = svg, text = null) {
  const node = document.createElementNS(NS, name);
  for (const [key, value] of Object.entries(attrs)) node.setAttribute(key, String(value));
  if (text !== null) node.textContent = String(text);
  parent.append(node);
  return node;
}

/** Deterministic DAG layers; no CDN or external JavaScript dependency. */
export function layoutGraph(g) {
  // A compact tutorial graph is easier to read when intermediate vertices
  // occupy two visibly separate tracks, even if an edge connects those tracks.
  // This also prevents direct and transitive edges from lying on top of one another.
  if (g.count >= 2 && g.count <= 8) {
    const y = [225, 132, 318, 225, 128, 318, 190, 225];
    return Array.from({ length: g.count }, (_, v) => ({
      x: 76 + (608 * v) / (g.count - 1),
      y: y[v]
    }));
  }
  const layer = Array(g.count).fill(0);
  for (let v = 0; v < g.count; v++) {
    for (const e of g.edges) if (e.from === v) layer[e.to] = Math.max(layer[e.to], layer[v] + 1);
  }
  const maxLayer = Math.max(...layer, 1);
  const groups = Array.from({ length: maxLayer + 1 }, () => []);
  for (let v = 0; v < g.count; v++) groups[layer[v]].push(v);
  const x0 = 80, x1 = 680, y0 = 73, y1 = 381;
  return layer.map((l, v) => {
    const peers = groups[l];
    const index = peers.indexOf(v);
    return { x: x0 + (x1 - x0) * l / maxLayer, y: y0 + (y1 - y0) * (index + 1) / (peers.length + 1) };
  });
}

function draw(g) {
  svg.replaceChildren();
  const defs = el('defs');
  const marker = el('marker', { id: 'arrow', markerWidth: 8, markerHeight: 8, refX: 7, refY: 4, orient: 'auto', markerUnits: 'userSpaceOnUse' }, defs);
  el('path', { d: 'M 0 0 L 8 4 L 0 8 Z', fill: '#91a6a0' }, marker);
  const pos = layoutGraph(g);
  const doubles = new Map();
  for (const e of g.edges) {
    const k = `${e.from}-${e.to}`;
    doubles.set(k, (doubles.get(k) ?? 0) + 1);
  }
  const used = new Map();
  for (const [edgeIndex, e] of g.edges.entries()) {
    const a = pos[e.from], b = pos[e.to], dx = b.x - a.x, dy = b.y - a.y;
    const length = Math.hypot(dx, dy) || 1;
    const normalX = -dy / length, normalY = dx / length;
    const k = `${e.from}-${e.to}`, index = used.get(k) ?? 0;
    used.set(k, index + 1);
    const offset = (index - (doubles.get(k) - 1) / 2) * 22;
    const x1 = a.x + dx / length * 25, y1 = a.y + dy / length * 25;
    const x2 = b.x - dx / length * 31, y2 = b.y - dy / length * 31;
    const mx = (x1 + x2) / 2 + normalX * offset;
    const my = (y1 + y2) / 2 + normalY * offset;
    const d = `M ${x1} ${y1} Q ${mx} ${my} ${x2} ${y2}`;
    el('path', { d, fill: 'none', stroke: '#8da49b', 'stroke-width': 2, 'marker-end': 'url(#arrow)', opacity: .9, 'data-edge': edgeIndex, class: 'graph-edge' });
    const labelX = .25*x1+.5*mx+.25*x2 + normalX * (12 + Math.sign(offset)*3);
    const labelY = .25*y1+.5*my+.25*y2 + normalY * (12 + Math.sign(offset)*3);
    const label = String(e.weight);
    const width = Math.max(24, 11 + label.length*8);
    el('rect', { x: labelX-width/2, y: labelY-12, width, height: 24, rx: 6, fill: '#ffffff', stroke: '#d4dfd8' });
    el('text', { x: labelX, y: labelY+4, fill: '#4b5c53', 'font-family': 'ui-monospace, monospace', 'font-size': 13, 'text-anchor': 'middle' }, svg, label);
  }
  for (let v = 0; v < g.count; v++) {
    const p = pos[v], source = v === g.source;
    el('circle', { cx:p.x, cy:p.y, r:24, fill:source?'#e2eee8':'#eef2ee',stroke:source?'#537f6e':'#9caf9f','stroke-width':2.3, 'data-vertex': v, class: 'graph-node' });
    el('text', { x:p.x,y:p.y+5,fill:source?'#315a4c':'#34443b','font-size':15,'font-weight':700,'text-anchor':'middle' },svg,v);
    if (source) el('text',{x:p.x,y:p.y-37,fill:'#537f6e','font-size':10,'letter-spacing':1.2,'font-weight':700,'text-anchor':'middle'},svg,'SOURCE');
  }
}

function update() {
  requestSerial++;
  invalidateTrace();
  numbers.textContent = editor.value.split('\n').map((_, i) => i+1).join('\n');
  try {
    graph = parseGraph(editor.value);
    parseStatus.textContent = `✓ Valid DAG · ${graph.count} vertices · ${graph.edges.length} edges`;
    parseStatus.parentElement.classList.remove('invalid');
    graphCount.textContent = `${graph.count} VERTICES / ${graph.edges.length} EDGES`;
    graphError.hidden = true;
    draw(graph);
    buttons.forEach(b => b.disabled = false);
  } catch (err) {
    graph = null;
    parseStatus.textContent = `✕ ${err.message}`;
    parseStatus.parentElement.classList.add('invalid');
    graphError.hidden = false;
    graphError.textContent = err.message + '\nCorrect the input to update the graph.';
    svg.replaceChildren();
    graphCount.textContent = 'INVALID INPUT';
    buttons.forEach(b => b.disabled = true);
  }
  selectedMode = null;
  resultName.textContent = 'No evaluation yet';
  resultDescription.textContent = 'Select an algorithm.';
  resultOutput.replaceChildren();
  const placeholder = document.createElement('span');
  placeholder.className = 'empty-output';
  placeholder.textContent = 'No results';
  resultOutput.append(placeholder);
}

async function evaluate(mode) {
  if (!graph) return;
  invalidateTrace();
  selectedMode = mode;
  document.querySelector('#trace-prepare').disabled = false;
  document.querySelector('#animation-mode').textContent = modeLabels[mode].toUpperCase();
  const serial = ++requestSerial;
  buttons.forEach(b => b.disabled = true);
  const shortest = mode === 'shortest';
  resultName.textContent = mode === 'optimal' ? 'Minimum cost and optimal path count'
    : shortest ? 'Shortest-path costs' : 'Number of paths';
  resultDescription.textContent = mode === 'optimal'
    ? 'List path costs; report the minimum cost and its multiplicity.'
    : shortest ? 'Min-plus semiring. Edge weights are nonnegative costs; unreachable vertices are INF.'
    : 'Plus-times semiring. Each edge counts as one path regardless of its weight.';
  resultOutput.replaceChildren();
  const waiting = document.createElement('span');
  waiting.className = 'empty-output';
  waiting.textContent = 'Running Lean executable…';
  resultOutput.append(waiting);
  try {
    const res = await fetch('/api/run', { method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify({mode,graph:editor.value}) });
    const payload = await res.json();
    if (serial !== requestSerial) return;
    if (!res.ok) throw new Error(payload.error || `HTTP ${res.status}`);
    resultOutput.replaceChildren();
    for (const line of payload.output.split('\n')) {
      const match = line.match(/^(\d+):\s*(\S+)$/);
      if (!match) {
        const raw = document.createElement('span'); raw.textContent = line;
        resultOutput.append(raw); continue;
      }
      const item = document.createElement('div'); item.className = 'value-box';
      const index = document.createElement('span'); index.className = 'value-index'; index.textContent = `VERTEX ${match[1]}`;
      const value = document.createElement('span'); value.className = 'value-value';
      const optimum = match[2].match(/^min=(\d+),count=(\d+)$/);
      value.textContent = optimum ? `${optimum[1]} · ${optimum[2]} route${optimum[2] === '1' ? '' : 's'}`
        : match[2] === 'INF,count=0' ? 'INF · 0 routes' : match[2];
      item.append(index, value); resultOutput.append(item);
    }
    // Results and step traces come from separate Lean executables.
    // Preload the trace paused at its first step, ready for the student to play.
    traceControls.prepare.click();
  } catch (error) {
    if (serial !== requestSerial) return;
    resultOutput.replaceChildren();
    const message = document.createElement('span');
    message.className = 'error-text';
    message.textContent = error.message;
    resultOutput.append(message);
  } finally {
    if (serial === requestSerial) buttons.forEach(b => b.disabled = false);
  }
}

editor.addEventListener('input', update);
editor.addEventListener('scroll', () => { numbers.scrollTop = editor.scrollTop; });
document.querySelector('#reset').addEventListener('click', () => { editor.value = original; update(); });
document.querySelector('#run-shortest').addEventListener('click', () => evaluate('shortest'));
document.querySelector('#run-paths').addEventListener('click', () => evaluate('paths'));
document.querySelector('#run-optimal').addEventListener('click', () => evaluate('optimal'));

/* --- Trace replay: no graph algorithm, aggregation, or semiring math here. --- */
const modeLabels = {
  shortest: 'Shortest paths · min / plus',
  paths: 'Path counting · plus / times',
  optimal: 'Cost spectra · concatenate / extend'
};
const traceControls = {
  prepare: document.querySelector('#trace-prepare'),
  previous: document.querySelector('#trace-prev'),
  next: document.querySelector('#trace-next'),
  play: document.querySelector('#trace-play'),
  reset: document.querySelector('#trace-reset'),
  speed: document.querySelector('#trace-speed'),
  speedLabel: document.querySelector('#speed-label'),
  counter: document.querySelector('#trace-counter'),
  title: document.querySelector('#trace-title'),
  explanation: document.querySelector('#trace-explanation'),
  equation: document.querySelector('#trace-equation'),
  values: document.querySelector('#trace-value-grid'),
  progress: document.querySelector('#trace-progress-fill')
};

/** Strictly parse the transport protocol emitted by `GraphFold.Trace.encode`. */
export function parseTrace(raw) {
  const events = raw.trim().split(/\r?\n/).filter(Boolean).map((line, lineIndex) => {
    const p = line.split('|');
    const positive = (s) => /^\d+$/.test(s) && Number.isSafeInteger(Number(s));
    if (p[0] === 'start' && p.length === 3 && positive(p[1]))
      return { kind: 'start', vertex: Number(p[1]), base: p[2] };
    if (p[0] === 'edge' && p.length === 8 && p.slice(1, 4).every(positive))
      return { kind: 'edge', vertex:Number(p[1]), predecessor:Number(p[2]),
        weight:Number(p[3]), prior:p[4], contribution:p[5], before:p[6], after:p[7] };
    if (p[0] === 'finish' && p.length === 3 && positive(p[1]))
      return { kind: 'finish', vertex:Number(p[1]), value:p[2] };
    throw new Error(`Malformed trace event at line ${lineIndex+1}`);
  });
  if (!events.length) throw new Error('Trace is empty');
  return events;
}

function stopPlayback() {
  if (traceTimer !== null) clearTimeout(traceTimer);
  traceTimer = null;
  traceControls.play.textContent = '▶ Play';
}

function invalidateTrace() {
  stopPlayback();
  traceRequestSerial++;
  traceEvents = [];
  traceIndex = 0;
  if (!traceControls) return;
  for (const button of [traceControls.previous, traceControls.next, traceControls.play, traceControls.reset]) button.disabled = true;
  traceControls.prepare.disabled = true;
  traceControls.counter.textContent = 'NO TRACE LOADED';
  traceControls.title.textContent = 'No trace loaded';
  traceControls.explanation.textContent = 'Run an algorithm, then load its trace.';
  traceControls.equation.textContent = 'F(v) = b(v) ⊕ Σ(F(u) ⊗ w(u,v))';
  traceControls.progress.style.width = '0%';
  traceControls.values.replaceChildren();
  updateHighlights(null);
}

function updateHighlights(event) {
  svg.querySelectorAll('.graph-node').forEach(node => {
    node.classList.toggle('node-active', Boolean(event && event.vertex === Number(node.dataset.vertex)));
    node.classList.toggle('node-predecessor', Boolean(event && event.kind === 'edge' && event.predecessor === Number(node.dataset.vertex)));
  });
  let edgeId = -1;
  if (event?.kind === 'edge') {
    // Distinguish parallel equal-weight edges by their occurrence in the trace.
    const earlier = traceEvents.slice(0, traceIndex).filter(e =>
      e.kind === 'edge' && e.vertex === event.vertex &&
      e.predecessor === event.predecessor && e.weight === event.weight).length;
    const matches = graph.edges.map((e,i) => ({...e,i})).filter(e =>
      e.from === event.predecessor && e.to === event.vertex && e.weight === event.weight);
    edgeId = matches[earlier]?.i ?? -1;
  }
  svg.querySelectorAll('.graph-edge').forEach(path => {
    path.classList.toggle('edge-active', Boolean(event && Number(path.dataset.edge) === edgeId));
  });
}

/** Mode-specific, plain-language descriptions of what each trace event means. */
function startExplanation(mode, event) {
  const isSource = mode === 'shortest' ? event.base !== 'INF' : event.base !== '0' && event.base !== '[]';
  if (mode === 'shortest') return isSource
    ? `Vertex ${event.vertex} is the source, so its running best distance starts at 0.`
    : `Vertex ${event.vertex} has no known distance yet, so it starts at ∞ (unreachable) until an edge reaches it.`;
  if (mode === 'paths') return isSource
    ? `Vertex ${event.vertex} is the source, so it starts with 1 path already counted — the empty path that starts and ends here.`
    : `Vertex ${event.vertex} starts with 0 paths counted; incoming edges will add to this total.`;
  return isSource
    ? `Vertex ${event.vertex} is the source, so its running cost spectrum starts as [0] — the zero-cost empty path.`
    : `Vertex ${event.vertex} starts with an empty cost spectrum []; incoming edges will append to this list.`;
}

function edgeExplanation(mode, event) {
  if (mode === 'shortest') {
    const reachable = event.prior !== 'INF';
    if (!reachable) return `Vertex ${event.predecessor} is still unreachable (∞), so this edge offers no usable distance; the running best stays ${event.before}.`;
    return `Vertex ${event.predecessor}'s distance (${event.prior}) plus this edge's weight (${event.weight}) gives a candidate distance of ${event.contribution}. Compare it against the current best (${event.before}) and keep the smaller: ${event.after}.`;
  }
  if (mode === 'paths') {
    return `Vertex ${event.predecessor} already has ${event.prior} path(s) reaching it; every one of them extends across this edge, contributing ${event.contribution} path(s) (edge weight does not affect counting). Add that to the running total ${event.before} to get ${event.after}.`;
  }
  return `Vertex ${event.predecessor}'s reached costs (${event.prior}) each get this edge's weight (${event.weight}) added, giving the extended costs ${event.contribution}. Append that list to the running spectrum ${event.before} to get ${event.after}.`;
}

function finishExplanation(mode, event) {
  if (mode === 'shortest') return event.value === 'INF'
    ? `Vertex ${event.vertex} is unreachable from the source: no incoming edge ever produced a finite distance.`
    : `Vertex ${event.vertex}'s shortest distance is finalized at ${event.value}; later vertices can now use this value.`;
  if (mode === 'paths') return `Vertex ${event.vertex} has ${event.value} total path(s) from the source; later vertices can now use this count.`;
  return `Vertex ${event.vertex}'s full cost spectrum is finalized as ${event.value} — its minimum entry and how often it occurs give the optimal cost and the number of tied optimal routes.`;
}

function paintTrace() {
  if (!traceEvents.length || !graph) return;
  const current = traceEvents[traceIndex];
  traceControls.counter.textContent = `STEP ${traceIndex+1} OF ${traceEvents.length}`;
  traceControls.progress.style.width = `${100*(traceIndex+1)/traceEvents.length}%`;
  traceControls.previous.disabled = traceIndex === 0;
  traceControls.next.disabled = traceIndex >= traceEvents.length-1;
  traceControls.play.disabled = traceIndex >= traceEvents.length-1;
  traceControls.reset.disabled = false;
  updateHighlights(current);
  if (current.kind === 'start') {
    traceControls.title.textContent = `Vertex ${current.vertex} · initialize`;
    traceControls.explanation.textContent = startExplanation(selectedMode, current);
    traceControls.equation.textContent = `acc ← ${current.base}`;
  } else if (current.kind === 'edge') {
    traceControls.title.textContent = `Edge ${current.predecessor} → ${current.vertex} · contribute`;
    traceControls.explanation.textContent = edgeExplanation(selectedMode, current);
    const operators = selectedMode === 'shortest' ? ['min', '+'] :
      selectedMode === 'paths' ? ['+', '×'] : ['++', '⊗'];
    traceControls.equation.textContent = `${current.prior} ${operators[1]} ${selectedMode === 'paths' ? '1' : current.weight} = ${current.contribution}    ·    ${operators[0]}(${current.before}, ${current.contribution}) = ${current.after}`;
  } else {
    traceControls.title.textContent = `Vertex ${current.vertex} · finalized`;
    traceControls.explanation.textContent = finishExplanation(selectedMode, current);
    traceControls.equation.textContent = `F(${current.vertex}) = ${current.value}`;
  }
  const finalized = Array(graph.count).fill('—');
  for (let i=0; i<=traceIndex; i++) if (traceEvents[i].kind === 'finish') finalized[traceEvents[i].vertex] = traceEvents[i].value;
  if (current.kind === 'start') finalized[current.vertex] = current.base;
  if (current.kind === 'edge') finalized[current.vertex] = current.after;
  traceControls.values.replaceChildren();
  for (let v=0; v<graph.count; v++) {
    const item = document.createElement('div');
    item.className = 'trace-value' + (current.vertex === v ? ' current' : '');
    const vertex = document.createElement('span'); vertex.textContent = `v${v}`;
    const value = document.createElement('strong'); value.textContent = finalized[v];
    item.append(vertex,value);
    traceControls.values.append(item);
  }
}

function setTraceIndex(index) {
  traceIndex = Math.max(0, Math.min(index, traceEvents.length-1));
  paintTrace();
}

function schedulePlayback() {
  if (traceIndex >= traceEvents.length-1) { stopPlayback(); return; }
  traceTimer = setTimeout(() => {
    setTraceIndex(traceIndex+1);
    schedulePlayback();
  }, Number(traceControls.speed.value));
}

traceControls.prepare.addEventListener('click', async () => {
  if (!graph || !selectedMode) return;
  stopPlayback();
  const request = ++traceRequestSerial;
  traceControls.prepare.disabled = true;
  traceControls.title.textContent = 'Loading Lean trace…';
  traceControls.explanation.textContent = 'Loading trace from Lean executable.';
  try {
    const response = await fetch('/api/trace', {
      method: 'POST', headers: {'Content-Type':'application/json'},
      body: JSON.stringify({mode:selectedMode, graph:editor.value})
    });
    const payload = await response.json();
    if (request !== traceRequestSerial) return;
    if (!response.ok) throw new Error(payload.error || `HTTP ${response.status}`);
    traceEvents = parseTrace(payload.output);
    if (traceEvents.some(e => e.vertex >= graph.count || (e.kind === 'edge' && e.predecessor >= graph.count)))
      throw new Error('Trace references a vertex outside the input graph');
    setTraceIndex(0);
    traceControls.prepare.textContent = '↻ Reload trace';
    traceControls.play.disabled = traceEvents.length < 2;
  } catch (error) {
    if (request !== traceRequestSerial) return;
    traceControls.title.textContent = 'Could not load trace';
    traceControls.explanation.textContent = error.message;
    traceControls.equation.textContent = 'Run lake build and restart the local server if necessary.';
  } finally {
    if (request === traceRequestSerial) traceControls.prepare.disabled = false;
  }
});
traceControls.previous.addEventListener('click', () => { stopPlayback(); setTraceIndex(traceIndex-1); });
traceControls.next.addEventListener('click', () => { stopPlayback(); setTraceIndex(traceIndex+1); });
traceControls.reset.addEventListener('click', () => { stopPlayback(); setTraceIndex(0); });
traceControls.play.addEventListener('click', () => {
  if (traceTimer !== null) { stopPlayback(); return; }
  if (traceIndex >= traceEvents.length-1) setTraceIndex(0);
  traceControls.play.textContent = 'Ⅱ Pause';
  schedulePlayback();
});
traceControls.speed.addEventListener('input', () => {
  traceControls.speedLabel.textContent = `${(Number(traceControls.speed.value)/1000).toFixed(2).replace(/0$/, '').replace(/\.$/, '')} s`;
  if (traceTimer !== null) { stopPlayback(); traceControls.play.textContent = 'Ⅱ Pause'; schedulePlayback(); }
});

update();
