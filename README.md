# GraphFold — a simple case study on auto-formalization errors

The prominent researcher into autoformalization of mathematics in
Lean, Kevin Buzzard, has written an easy, non-technical [blog post
(link)](https://xenaproject.wordpress.com/2026/11/12/and-the-proof-is-checked-in-lean/) on what can still go wrong even
if you think you've formalized the mathematical theory of your
domain in Lean 4 and proven your implemnentation correct against
it. Take five minutes to read it then continue through the rest of
this explanatory document, which provides a concrete case study one
of the failure modes Buzzard explains, namely errors not in proofs
but in the AI-generated statements of the propositions to be proved.

This repository purportedly presents (1) a Lean-checked formalization
of abstract graph folds; (2) three different graph algorithms each as
a specialization of the theory over a specific concrete semiring; (3)
compilation of all of that to both three compiled executables and one
package Lean library making it all available for use by other clients;
and (4) a pedagogical, web-based, interactive interface for (a) giving
graph inputs as text, (b) selecting and running one of the three graph
algorithms on the given graph, and (c) a pedagogical animation tool for
seeing the algorithm run step by step to fold the acyclic graph input
you give it down to a final result, e.g., shortest path. I found it
useful to better see and compare how each of the algoriths works.

I vibe-coded this entire project in Lean 4 (and HTML) in about two
hours. I did not check the proofs because Lean 4 is so good at that.
So am I done? Is all well. Should I ship it? Well, it's now time to
put on your engineer's hard hat, think like a genuinely well trained
engineer, and ask the most vital question of all: *what else could,
in in this case study did, go wrong?*

To proceed follow the quick and easy Getting Started instructions,
play around with the tool for a bit to get a good sense of what it
intended to do for you, then return to read the rest of this study.

## Quick start

1. Open this folder in VS Code. It will prompt you to install the recommended **Lean 4** extension if you don't already have it — accept that prompt. (If you missed or dismissed it, open the Extensions panel — **Cmd+Shift+X** on macOS, **Ctrl+Shift+X** on Windows/Linux — search for "Lean 4", and install it manually.) Then open any `.lean` file; this triggers a one-time download of the Lean toolchain and dependencies — wait for it to finish before continuing.
2. Open a terminal in VS Code and run:

   ```sh
   lake build
   ```

3. Open a terminal in VS Code.
4. Start the local web server:

   ```sh
   cd web && npm start
   ```

5. Open [http://localhost:8787](http://localhost:8787) in your browser. The page shows the graph visually, but you edit it through its textual
   edge-list representation on the left. Edit it, click **Reset example** to
   get back the default graph, or just run one of the three semiring-instance
   buttons (**Shortest paths**, **Count paths**, **Optimal routes**) on the
   graph as it stands. Once a run completes, its trace becomes available to
   drive the step-by-step animated display of the fold's operation on that
   graph, directly beneath the graph.
6. This formalization has not yet been rigorously checked. If you find an
   issue, please report it via [GitHub Issues](https://github.com/kevinsullivan/GraphFold/issues), or feel free to send a pull request.

## Overview

GraphFold presents a formalized **theory of generalized folds over directed acyclic graphs (DAGs)**, parameterized by the choice of an algebra—typically a semiring. A GUI lets you enter graph specifications and animate execution traces for three distinct graph algorithms, each selected just by choosing a concrete `Algebra` instance. Rather than treating shortest-path calculation, path counting, and path-cost enumeration as unrelated programs, it reveals their shared mathematical structure: values propagated along edges are combined at each vertex according to algebraic operations chosen for the particular problem. A single graph-recursion pattern consequently yields several notably different graph algorithms.

The project also illustrates a broader role for dependent type theory. **Beyond enabling verification of individual programs, an expressive type system allows the common mathematical foundations of distinct computations to be represented explicitly as reusable definitions, specifications, and proofs.** In Lean 4, the algebra and graph dependency structure can be separated from implementations, while independently developed *proof bridges* establish how each concrete implementation realizes the abstract recurrence. The objective is not merely to verify three algorithms but to understand, in a precise and reusable way, *why they are instances of the same theory*.

For a vertex `v`, the governing equation is

$$
F(v)=b(v)\oplus\bigoplus_{u\to v}\bigl(F(u)\otimes w(u,v)\bigr).
$$

- `F(v)` is the value computed at `v`: the quantity the fold produces (e.g., shortest-path cost, number of paths, or the multiset of all path costs to `v`, depending on the algebra chosen).
- `b(v)` is the initial, edge-independent contribution at `v` (e.g., the base case for a source vertex).
- `u → v` ranges over every edge into `v` from a predecessor `u`, tying the recurrence to the graph structure.
- `F(u)` is the already-computed value at predecessor `u`; a topological evaluation order guarantees it is known before `F(v)` is needed.
- `w(u,v)` is the weight on the edge from `u` to `v`.
- `⊗` *extends* a predecessor's value across an edge, combining `F(u)` with `w(u,v)` into that edge's contribution to `v`.
- the inner `⊕` (over all `u → v`) *aggregates* the contributions of all incoming edges into a single combined value.
- the outer `⊕` combines that aggregated value with the base contribution `b(v)` to produce `F(v)`.

Different choices of `⊕`, `⊗`, and `b` give different meanings to the same graph computation. GraphFold implements three examples: minimum path cost, number of paths, and the multiset of all path costs (from which minima and counts of optimal paths can be extracted). For finite DAGs, a topological evaluation order makes the recurrence a well-founded fold; cyclic graphs require a separate fixed-point or closure treatment and are outside the present executables' scope.

All of that is so cool. But engineering (as everyone knows) is not about cool. It's about solving problems,
usually by technological means (including processes), without inadvertently causing or unacceptably risking harmful outcomes.

So beyond getting some of it right, GraphFold is also a small case
study in the dependability of casually vibe-coded systems with formal proofs
of correctness, by virtue of its having been vibe-coded in Lean 4 rather than
in an industrial imperative language, for example.

It's impressive-sounding for the bot to proclaim your system — and here
I do quote the bot — fully tested, with no `sorry` anywhere. Sounds great,
ship it! Uh, wait one moment please. All that is true, and yet, alas, it has
several specification gaps and other basic quality problems. Proofs plus AI
is without question a new kind of rocket fuel. And that means you really can
get burned.
See the "What can still go wrong" section near the end of this document, and
[`whatCanGoWrongSpecGaps.lean`](whatCanGoWrongSpecGaps.lean), for technical
details. And now back to the show.

**Historical context.** This repo provides an abstract formalization and three verified instances of it, applying the established *algebraic path problem*. B. A. Carré's 1971 paper, [“An Algebra for Network Routing Problems”](https://doi.org/10.1093/imamat/7.3.273), is a direct early articulation of the common algebra underlying different routing computations. Related developments include R. C. Backhouse and Carré's *Regular Algebra Applied to Path-Finding Problems* (1975), [Michel Minoux's generalization of algebraic path structures](https://www.numdam.org/item/RO_1976__10_2_33_0/) (1976), and [Daniel J. Lehmann's closed-semiring treatment of transitive closure](https://doi.org/10.1016/0304-3975(77)90056-1) (1977). These developments built on earlier path, automata, and dynamic-programming algorithms. Mehryar Mohri's [“Semiring Frameworks and Algorithms for Shortest-Distance Problems”](https://cs.nyu.edu/~mohri/pub/jalc.pdf), *Journal of Automata, Languages and Combinatorics*, vol. 7, no. 3, pp. 321–350, 2002, gives the modern statement of this correctness pattern: the shortest distance is defined independently of any algorithm, as a sum over the actual set of paths, and an algorithm's output is only equated to it under an explicit hypothesis (acyclicity, or more generally k-closedness). For a recent treatment connecting semiring algebras to dynamic programming more broadly — including a new operation for counting minimal-cost solutions — see A. Baril, M. Couceiro, and V. Lagerkvist, [“New Perspectives on Semiring Applications to Dynamic Programming”](https://doi.org/10.1016/j.dam.2025.12.035), *Discrete Applied Mathematics*, vol. 383, pp. 243–279, 2026.

**Formalization scope.** GraphFold uses **Lean 4 / Lake, without Mathlib**, and term-mode proofs with explicit types. Its core `Algebra α` asks only for the two laws on `⊕` that the implemented recurrence and fold proofs actually use — associativity and a right identity (`zero`) — and imposes no laws on `⊗` at all; a separate `SemiringLaws` record states the stronger axioms of a full semiring (commutativity of `⊕`, associativity of `⊗`, an identity `one` for `⊗`, etc.). Consequently, the implementation bridges certify the recurrence at the abstraction level actually used; they should not be mistaken for proofs of every semiring law or for graph-theoretic correctness over arbitrary cyclic graphs. The source code and tests are intended as a pedagogical formalization, and building them with Lean remains necessary to check kernel acceptance.

## 1. Project organization

| File | Purpose |
|---|---|
| `GraphFold/Abstract/Core.lean` | Algebra and semiring-law interfaces, graph rows, right-fold recurrence, relational `Derives` specification, generic fold lemma |
| `GraphFold/Implementations/Shortest.lean` | Min-plus shortest-cost implementation and source/weight adapter |
| `GraphFold/Implementations/Paths.lean` | Natural-number path-count implementation and source/edge adapter |
| `GraphFold/Implementations/Optimal.lean` | Cost-spectrum interpreter and minimum-cost/tie-count summarizer |
| `GraphFold/Bridges/Shortest.lean` | Term-mode proof that shortest-cost implementation satisfies `Derives` |
| `GraphFold/Bridges/Paths.lean` | Independent term-mode proof for path counts |
| `GraphFold/Bridges/Optimal.lean` | Independent term-mode proof for the full path-cost spectrum |
| `GraphFold/IO/Format.lean` | One shared edge-list parser, validation, conversion to graph rows |
| `GraphFold/Trace.lean`, `TraceMain.lean` | Lean-level trace events, algebraic fold replay, runtime result agreement check, CLI transport |
| `ShortestMain.lean`, `PathsMain.lean`, `OptimalMain.lean` | Original command-line executable entry points |
| `Tests/Main.lean`, `test-cli.sh` | Library examples, parser checks, executable integration tests |
| `examples/` | Example input files, including deliberately invalid input |
| `web/server.mjs`, `web/public/` | Local HTTP server and interactive HTML/SVG interface |
| `web/test/` | HTTP integration tests independent of the Lean toolchain |

The parser and the algebraic interpretation are **separate**. The input graph
contains vertex identifiers, a designated source, and directed edges with
nonnegative integer labels. It contains **no algebra-specific base values**.

## 2. Build and run

First, in VS Code, click on any `.lean` file in this project. If Lean is
already installed natively, this just confirms it; if not, it triggers a
one-time download of [elan](https://lean-lang.org/lean4/doc/setup.html),
Lean 4, and Lake — wait for that download to finish before continuing.

```sh
cd GraphFold
lake update
lake build
lake exe graphfold_tests
lake exe shortest examples/diamond.txt
lake exe paths examples/diamond.txt
lake exe optimal examples/diamond.txt
lake exe optimal examples/tied-optima.txt
bash test-cli.sh
```

The `lean-toolchain` file specifies `leanprover/lean4:v4.35.0`.

## 3. Textual graph input format

Each nonblank, noncomment line is a declaration. Comments begin with `#`;
inline comments are also allowed. The first two declarations are mandatory:

```text
vertices N
source S
edge FROM TO WEIGHT
edge FROM TO WEIGHT
...
```

- `vertices N` declares **N vertices**, numbered from `0` through `N-1`.
- `source S` selects the vertex from which paths are evaluated.
- `edge U V W` declares a **directed edge U → V** with nonnegative cost `W`.
- There may be zero or more edge lines, in any order; repeated lines represent
  distinct parallel edges (and count separately as paths).
- Each edge must satisfy `0 ≤ U < V < N`. This is the input's **topological
  ordering constraint**: all edges move from an earlier to a later numbered
  vertex. It excludes cycles and permits a single forward fold.
- The parser reports invalid headers, integers, endpoints, and ordering.

For example, `examples/diamond.txt` is:

```text
# A four-vertex DAG with five weighted directed edges.
vertices 4
source 0
edge 0 1 2
edge 0 2 5
edge 1 2 3
edge 1 3 1
edge 2 3 1
```

The graph is visualized textually as:

```text
0 --2--> 1 --1--> 3
 \        |        ^
  5       3        1
   \      v       /
    ----> 2 -----
```

The **same input file** can be given to all three executables. The integer labels
are costs for shortest paths, but **not multiplicities** for path counting.
The path-count executable interprets every listed edge as multiplicity `1`.

### Shortest-path specialization (min-plus)

The carrier is `Option Nat`, with `some d` indicating a cost and `none`
representing infinity. `⊕` chooses the minimum and `⊗` adds costs. The
adapter `Shortest.fromRaw S` sets `b(S) = some 0`, `b(v) = none` otherwise,
and preserves all edge costs as `some W`.

```sh
lake exe shortest examples/diamond.txt
```

Expected output:

```text
0: 0
1: 2
2: 5
3: 3
```

Vertex `3` can be reached via `0 → 1 → 3` at cost `2 + 1 = 3`. The alternative
`0 → 2 → 3` costs `5 + 1 = 6`, and `0 → 1 → 2 → 3` costs `2 + 3 + 1 = 6`.

### Path-count specialization (natural-number plus-times)

The carrier is `Nat`; `⊕` adds counts and `⊗` multiplies by an edge
multiplicity. The file adapter `Paths.fromRaw S` sets `b(S) = 1`, `b(v) = 0`
for other vertices, and maps **every edge label to multiplicity 1**. This
counts paths in the graph independently of their costs, including one empty
path at the source.

```sh
lake exe paths examples/diamond.txt
```

Expected output:

```text
0: 1
1: 1
2: 2
3: 3
```

There is one path to vertex `1`; two to vertex `2` (`0 → 2` and `0 → 1 → 2`);
and three to vertex `3` (`0 → 1 → 3`, `0 → 2 → 3`, and `0 → 1 → 2 → 3`).

Unlike the executable file adapter, the lower-level `Paths.run` library
function still accepts arbitrary natural-number edge multiplicities and base
values. This is useful for illustrating the general algebra.

### Optimal-route specialization

The third interpretation answers **two questions simultaneously**: what is the
cheapest route, and *how many different routes attain that cost*? This is a
useful distinction in scheduling, routing, and redundancy analysis. For
example, if two equally inexpensive routes exist, losing one of them need not
increase the minimum cost.

Rather than computing only a `(cost, number-of-ties)` pair, this pedagogical
implementation uses the carrier `Spectrum := List Nat`: each entry is one
route's **total cost**, with duplicates intentionally retained.

- `⊕` is list concatenation (`++`). Alternative routes keep their identities
  as separate entries, even when their costs agree.
- `⊗` is a Cartesian product of alternatives, adding two path costs. For
  example, extending `[2, 5]` by an edge of cost 3 gives `[5, 8]`.
- `0` for the alternative operator is `[]`; the empty source path has
  spectrum `[0]`.
- At the end, `Optimal.summarize` extracts the minimum and how many times it
  occurs. It returns `none` for an unreachable vertex.

For the diamond input, the complete spectra are:

| Vertex | All route costs (`Optimal.run`) | Minimum | Cheapest routes |
|---|---|---:|---:|
| 0 | `[0]` | 0 | 1 |
| 1 | `[2]` | 2 | 1 |
| 2 | `[5, 5]` | 5 | 2 |
| 3 | `[3, 6, 6]` | 3 | 1 |

```sh
lake exe optimal examples/diamond.txt
```

```text
0: min=0,count=1
1: min=2,count=1
2: min=5,count=2
3: min=3,count=1
```

The extra example `examples/tied-optima.txt` has two **equally cheapest** routes
to vertex 3, both of cost five:

```text
vertices 4
source 0
edge 0 1 2
edge 0 2 1
edge 1 3 3
edge 2 3 4
```

```sh
lake exe optimal examples/tied-optima.txt
# Vertex 3: min=5,count=2
```

**Algebraic nuance:** Lists form an associative monoid under concatenation,
which is *all the abstract `Algebra` interface and the fold proof require*.
But concatenation is not commutative, so this concrete list carrier is **not**
a full commutative-addition semiring. Mathematically, the spectrum represents
a finite bag (multiset) of route costs; quotienting by permutation, or using a
finite cost-to-multiplicity map with convolution, yields the familiar
**polynomial / generating-function semiring**. If `x^d` denotes a path of cost
`d`, the diamond graph has the generating polynomials
`P₂(x) = 2x⁵` and `P₃(x) = x³ + 2x⁶`.

This is an intentionally transparent introductory implementation: its
**enumeration can grow exponentially** in the number of vertices. A useful
advanced exercise is to replace the spectrum list with canonical cost
coefficients, or a direct tropical-with-tie-counting semiring, and prove a new
refinement theorem without enumerating every route.

## 4. Using GraphFold as a library

```lean
import GraphFold
open GraphFold

-- This is the graph as converted by the shared edge-list parser:
def raw : Graph Nat :=
  [ { base := 0, incoming := [] }
  , { base := 0, incoming := [(0, 2)] }
  , { base := 0, incoming := [(0, 5), (1, 3)] }
  , { base := 0, incoming := [(1, 1), (2, 1)] } ]

-- Each adapter supplies the specialization's source value and edge semantics.
#eval Shortest.run (Shortest.fromRaw 0 raw)
-- [some 0, some 2, some 5, some 3]

#eval Paths.run (Paths.fromRaw 0 raw)
-- [1, 1, 2, 3]

#eval Optimal.run (Optimal.fromRaw 0 raw)
-- [[0], [2], [5, 5], [3, 6, 6]]

#eval Optimal.runSummary (Optimal.fromRaw 0 raw)
-- [some (0, 1), some (2, 1), some (5, 2), some (3, 1)]

-- Term-mode proofs connecting computed results to the abstract recurrence:
example : Satisfies Paths.algebra (Paths.fromRaw 0 raw)
    (Paths.run (Paths.fromRaw 0 raw)) :=
  Paths.sound (Paths.fromRaw 0 raw)

example : Satisfies Shortest.algebra (Shortest.fromRaw 0 raw)
    (Shortest.run (Shortest.fromRaw 0 raw)) :=
  Shortest.sound (Shortest.fromRaw 0 raw)

example : Satisfies Optimal.algebra (Optimal.fromRaw 0 raw)
    (Optimal.run (Optimal.fromRaw 0 raw)) :=
  Optimal.sound (Optimal.fromRaw 0 raw)
```

The abstract `Graph α` is a list of rows, with a base value and incoming edges
for each vertex. `Format.toGraph` maps the file's edge declarations into
those rows; the three adapters independently assign their bases and edge values.

## 5. Proof architecture and explicit typing

`specStep` uses a **right fold** of incoming edge contributions. Each concrete
`step` uses a **left fold**: unlike `foldr`, which combines the rightmost
element first and works inward (`f x1 (f x2 (... (f xn init))))`), `foldl`
walks the list left to right, combining the accumulator so far with each next
element (`f (... (f (f init x1) x2) ...) xn`). The generic `foldl_eq_foldr`
theorem proves their agreement from monoid laws. Each independent bridge constructs a `Derives`
certificate recursively, showing that its `run` produces the abstract
specification's value at each vertex. All proofs use **term mode** (no `by`
blocks or tactics), with annotated argument and important intermediate types.

Types you will see:

| Lean syntax | Meaning |
|---|---|
| `Nat` | Nonnegative integers, also used for vertex IDs |
| `Option Nat` | `some n` is a finite cost; `none` is infinity |
| `Optimal.Spectrum` | `List Nat`: all path costs, including duplicates |
| `Option (Nat × Nat)` | Minimum cost and number of cheapest routes (or unreachable) |
| `List α` | List of elements having type `α` |
| `Nat × α` | Incoming edge: predecessor index and algebraic edge weight |
| `Graph α` | List of `Row α`, in vertex-number order |
| `Algebra α` | Operations `plus`, `times`, and required aggregate laws |
| `Satisfies A g out` | Proposition that output has a recurrence derivation |
| `List.rec` | Structural recursion constructing data or proof terms |

For instance, the path-count bridge contains an explicitly typed induction
hypothesis of the following mathematical shape:

```lean
ih : ∀ (pre : List Nat),
  Derives algebra pre rs (runFrom pre rs)
```

The proof is valid for any already-computed prefix and remaining row list.
The separate DAG ordering check guarantees that, for parsed files, every
referenced predecessor is in the computed prefix when evaluated.

## 6. Scope and limitations

The algebra and abstract recurrence can be *stated* for arbitrary finite graphs.
The sequential implementation assumes all predecessors are processed earlier,
enforced by the **file parser** by its `FROM node label < TO node label` constraint. Cyclic graphs are *not* within the scope of our algorithm, and need a separate fixed-point semantics and corresponding algorithm and proof.

`SemiringLaws` states the stronger full-semiring axioms, but none of the three
implementations need to or do fully prove their operations satisfy all of them.
Each implementation proves only the smaller `Algebra` laws that the fold proof
needs.

Suggested exercises.

Picking one implementation and defining a `SemiringLaws` instance for
it (proving, for example, that `⊕` is commutative or that `⊗` distributes
over `⊕`) would be a good follow-on exercise.

List-based prefix appends are intentionally simple rather than asymptotically optimized, and profiling for performance bugs and fixing them is another.

Or do it all. Prove the uniqueness of `Derives`. Certify the full semiring laws.
Derive an optimized implementation by replacing list accumulation with arrays or
hash tables and proving that the fast code is equivalent to the liproof-friendly  refinement, add a general topological-sort phase, and formalize a *fixed-point* semantics for cycles.

## 7. Interactive local HTML interface

A zero-dependency **Node.js 20+** HTTP server serves the graphical interface.
The browser provides **live graph rendering** with native SVG (a small,
self-contained alternative to D3). It does **not** implement any graph
algorithm: each of the three Run buttons invokes its corresponding compiled
Lean executable through the server, using the **exact contents of the editor**
as a temporary `.txt` input file. The temporary file is removed after the
run. Each result is displayed by vertex in the page.

From the project root, build the Lean targets and start the server:

```sh
lake build
node web/server.mjs
```

Open **http://127.0.0.1:8787** in a browser. Use `Ctrl+C` to stop the server.
The process listens on **127.0.0.1 only** by default: it is not exposed to
the network. To choose a different port:

```sh
PORT=9090 node web/server.mjs
```

An explicit `HOST` environment variable can change the bind address. Do not
set `HOST=0.0.0.0` on an untrusted network: the interface has no authentication
and permits invoking the local Lean executables with user-supplied graph files.

### User interface

- **Top**: **Shortest paths**, **Count paths**, and **Optimal routes**
  buttons submit the input to their corresponding Lean executables. The output area shows a field for
  each vertex or a detailed error emitted by the Lean parser/executable.
- **Below that, left**: an editable graph text area. The header must be
  `vertices N`, `source S`, followed by zero or more `edge U V W` lines. `#`
  comments and blank lines are allowed. As the text changes, syntax errors
  are shown.
- **Below that, right**: an automatically updated SVG visualization of the
  directed graph. Vertices are positioned in topological layers, edges have
  arrows, and edge weights appear beside the edges. The source is
  highlighted. Directly beneath it sit the trace playback controls (**Load
  trace**, **Previous**, **Play**, **Next**, **Restart**, and the step-delay
  slider) and, below those, a plain-text step counter, title, explanation,
  and equation for the current trace step — all right under the graph
  they're animating.
- The visualizer imposes a display limit of 150 vertices and 800 edges. This
  is a browser rendering limit, not part of the Lean theory. The Lean input
  parser additionally requires `U < V`, so the executable graph is a DAG.

The server first tries the binaries generated by `lake build` in
`.lake/build/bin/`, falling back to `lake exe` if needed. A missing Lean/Lake
installation or an unbuilt project is reported in the output panel rather
than silently producing a JavaScript-computed result.

### Web interface tests

```sh
node --test web/test/*.test.mjs
```

These test static HTML delivery, endpoint input validation, Lean-runner
invocation boundaries, output, and error propagation. They use a **fake runner**
to exercise the HTTP layer independently of Lean. For true end-to-end Lean
checks, first execute `bash test-cli.sh`, and then use the browser buttons.
No web assets are loaded from a CDN and no `npm install` is necessary.

## 8. Animated execution traces

The local interface also supports a **runtime-checked trace replay** of all
three specializations. This is useful in class or when learning the connection
between a graph recurrence and a fold. The playback controls and the
step-by-step explanation both sit directly beneath the graph display, right
below the graph they're animating.

1. Edit the graph input, which instantly updates the SVG on the right.
2. Click **Shortest paths**, **Count paths**, or **Optimal routes**. The existing
   Lean executable calculates and displays the answer. The separate Lean `trace`
   executable records the computation and loads its timeline at step one.
3. Click **Play** for timed playback; **Pause**, **Previous**, **Next**, or
   **Restart** to explore. The step-delay slider defaults to **1 second**
   and ranges from **0.35 to 4 seconds**.
4. The active destination vertex turns **gold**; the predecessor turns **blue**;
   the active edge is highlighted. The explanation names the current step,
   describes in plain language what it's doing, and shows the underlying
   equation with the edge's weight, predecessor value, contribution, and
   accumulator before and after the step.

The local endpoint `POST /api/trace` takes the same JSON request as `/api/run`:
`{"mode":"shortest", "graph":"vertices 4\\nsource 0\\n..."}`. The server
invokes the **Lean trace executable**, not a JS reimplementation of the fold:

```sh
lake exe trace shortest examples/diamond.txt
lake exe trace paths examples/diamond.txt
lake exe trace optimal examples/diamond.txt
```

The trace line protocol is deliberately simple: `start|vertex|base`,
`edge|vertex|predecessor|weight|prior|contribution|before|after`, and
`finish|vertex|value`. The browser parses and *replays* these events without
performing algebra. The tracer computes a left fold from the same `Algebra`
operations and specialization adapters; before emitting a trace, its executable
**checks that its final values exactly match the corresponding original Lean
implementation**, failing if they differ. This is a runtime consistency check,
**not a Lean theorem of trace refinement**. The existing term-mode soundness
proofs continue to relate each original evaluator to the abstract recurrence.

The trace is held in browser memory and discarded whenever the input changes.
For large or densely connected graphs, choose step-by-step controls rather
than rapid playback. The spectrum example may produce very long text because
it deliberately enumerates every path cost.

### Animation testing and limitations

The HTTP tests cover the trace endpoint's delegation to the injected runner:

```sh
node --test web/test/*.test.mjs
```

A Chromium visual inspection was performed with a controlled synthetic trace,
at 1440px desktop and 768px tablet widths. Its five diamond edges and the
three simultaneous highlight roles were visually inspected; the page had no
horizontal overflow at tablet width. Screenshots are included as
`animation-desktop.png` and `animation-tablet.png`. The optional
`python web/test/browser_smoke.py` replays a synthetic trace in Chromium,
checks Play/Pause, stepping, validation, active highlights, and overflow, and
regenerates the screenshots (requires Python Playwright and Chromium).

### Interface styling

The local interface uses a light, Material-inspired visual system: neutral surfaces,
subtle section borders, conventional controls, restrained typography, and muted green,
blue, and amber accents. Amber indicates the current vertex/edge in an execution
trace, while blue identifies its predecessor. The editor, SVG graph, and execution
controls remain functional without external fonts, stylesheets, or JavaScript libraries.

The desktop and tablet screenshots are generated by `python web/test/browser_smoke.py`
using Chromium with a controlled trace fixture.

## 9. What Went Wrong?

AI + proof assistants represent a radical advance in science and
technology. In its current state, this project is the result of about
two hours of vibe coding in Lean. That's remarkable. It's all based on
well developed mathematics: the algebraic path problem is decades old
and well-studied since 1971. It's all "verified" — the proofs compile,
there's no `sorry` anywhere, the test suite passes, the CLI and web UI
both produce correct-looking answers on every input anyone has tried.
So we're good, right?

No. Again, think like an engineer with a moral obligation to protect
users from errors that cause unacceptable harms. Real engineers ask
relentlessly *what else could go wrong* and then they make sure that
that doesn't happen. 

Knuth is widely quoted as having warned: "Beware of bugs in the above
code; I have only proved it correct, not tried it." The failure modes
he had in mind included compiler (today kernel) bugs, hardware errors,
and *specification gaps*. Some have interpreted Knuth as shilling for
testing, but what he was really telling us is that a proof only proves
that the code satisfies the specification, not that the specification
itself is right. That's the failure mode this case study is about.

To see proofs and a code-based explanation of the failure, se  the file 
called [`whatCanGoWrongSpecGaps.lean`](whatCanGoWrongSpecGaps.lean). An
AI, prompted to check our formalization against the actual published work
found the failure in this case within a minute: `Shortest.run`, `Paths.run`, 
and `Optimal.run` all accept a graph with a genuine cycle and silently 
return a plausible-looking answer. The file-based CLI and web UI are 
protected, as the parser rejects `FROM < TO` violations. The *library*
API, on the other hand, which the "Using GraphFold as a library" section
above tells you to use directly in Lean — does not. The soundness theorems
(`Shortest.sound`, `Paths.sound`, `Optimal.sound`) typecheck without error
on cyclic inputs, because `Derives`/`Satisfies` never asserted acyclicity
in the first place. The proof isn't wrong. It just proves less than you
think because the AI bot got the *statement* of the theorem wrong.

You can mostly trust vibe-coded proofs to *verify* your construction, but
the claims that they they're actually proving are up to *you* to validate.

A specification can have exactly the same kind of gap as an implementation.
Curry-Howard tells us that large proofs constructions are just *software*.
It's thus vulnerable to oh so many other software engineering failure modes.
Examples of incorrect theorem *statements* could include missing preconditions (as here); a false precondition, in which case anything can be proved *vacuously*,
or a check that is correct but is never actually called (also see in this case).

Formally *verified* vibe-coded Lean 4 does *not* entail readiness to ship, as
it bypasses the vital orthogonal process of *validating* what has been vibed.
Knuth's quip about proving code correct without trying it could be read as
"testing still matters." But his real message was that even with proofs, much
can still go wrong including in particular gaps in the *specifications* proved
to have been satisfied. This is why, in my view, fluency in reading formal
specifications in higher-order type theories is now such an important skill.

### The Actual Error

Further investigation shows one fundamental gap: the autoformalization of the  original publication, Mehryar Mohri's "Semiring Frameworks and Algorithms for Shortest-Distance Problems" (2002) always defines the target quantity — the
shortest distance itself, for example — independently of any algorithm, as a
sum over the actual set of paths. He only ever equates an algorithm's output
to that target *under an explicit hypothesis* (his Corollary 2: the graph is
acyclic).

GraphFold simply lacks a formalization of that independent target and
condition in our formalization of the abstract theory: `Core.lean`.
`Derives`/`Satisfies` only assert that two renderings of `specStep`'s
recursive unfolding agree with each other — a claim about the algorithm's
self-consistency, whereas what's needed is a proof of correctness against
the actual,independent mathematical theory. With no independent truth,
there is nothing for a cyclic input's output to be wrong *relative to*.
The `Algebra` laws themselves are not erroneous here. The error is the
dropping during machine formalization of an essential hypothesis. It's
present in the original peer-reviewed, human-derived mathematics, but
was simply dropped by Claude when it ingested and auto-formalized that
earlier work.

This case study suggests that fatal specification errors can plaugue even
the simplest of Lean formalizations, particularly AI-generated ones. So how
might one, not *verify* a major claim with proof of tens of millions of lines
of Lean code, but *validate* the proposition that the specifications of what
is to be proved reflect that actual mathematics of the domain? Hint: it's now
a large-scale software engineering problem in all respects: intellectual control,
careful modularizations, both automated and human code reviews, regression and
other forms of testing, process quality control.

The programming languages, software engineering, and AI resaerch communities
have given us practically miraculous tools for verifying mathematical claims. Validating the claims themselves remains an unsolved problem for formal code
at scale. Indeed, building on the remarkable success in research mathematics
applications of formal verification of very hard propositions requiring very
large proof constructions, the problem of *validation* remains largely open.
You built the thing right (it's proven) is *not* the same as you built the
right thing.
