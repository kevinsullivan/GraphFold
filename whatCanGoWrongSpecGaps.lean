import GraphFold

/-!
# What can still go wrong: spec gaps in a "proven" system

> "Beware of bugs in the above code; I have only proved it correct, not
> tried it." — Donald Knuth

Knuth's warning is usually read as "a proof is not a substitute for testing."
This file is about the opposite direction, which is less discussed and, for
a formalized system, more dangerous: **running the code is not a substitute
for checking what the theorem actually says.** GraphFold's three evaluators
come with term-mode soundness proofs (`Shortest.sound`, `Paths.sound`,
`Optimal.sound`). That can feel like a settled question. It is not.

Once you have a formalization, the decisive engineering question stops being
"does it crash on the inputs I tried?" and becomes:

> **What could still be wrong — and what would make us certain it isn't?**

Trying it on many inputs is part of the answer, but it is a weak part: you
can run the executables on dozens of graphs, see sensible-looking answers
every time, and still never trigger the one input shape that defeats a
hidden assumption. The stronger part is reading the *statement* of each
proof and asking what it does **not** assert. A proof is a precise claim
about a specific proposition; it is exactly as strong as that proposition,
no stronger, no matter how it was obtained.

This file is a working log of such gaps, developed incrementally. Each entry:
states the gap, demonstrates it with a concrete runnable example, and
diagnoses the root cause in the source. Fixes, if and when we make them,
belong in the library itself — this file stays a case study of what to
distrust and why.

-/

open GraphFold

/-!
## Gap 1 — cyclic graphs are silently "solved"

The file-based CLI and web UI reject cycles: `GraphFold.IO.Format.parseEdge`
requires every edge to satisfy `FROM < TO`, so no cyclic graph can reach
`Shortest.run`, `Paths.run`, or `Optimal.run` through that path. That part
of the system is fine — it just isn't the part that advertises a correctness
proof. The proofs are about the **library-level** API: `Graph α`, `run`,
`Derives`, `Satisfies`. Nothing stops you from calling that API directly,
exactly as `README.md` §4 demonstrates, and nothing in it checks acyclicity.
-/

/-- Row 0 depends on vertex 1 (not yet computed); row 1 depends on vertex 0.
    A genuine mutual dependency — this cannot come from the file parser,
    which forbids `FROM < TO` violations, but nothing stops constructing it
    directly as a `Graph`. -/
def cyclicNat : Graph Nat :=
  [ { base := 0, incoming := [(1, 10)] }
  , { base := 0, incoming := [(0, 100)] } ]

def cyclicOpt : Graph (Option Nat) :=
  [ { base := some 0, incoming := [(1, some 10)] }
  , { base := none,   incoming := [(0, some 100)] } ]

def cyclicSpec : Graph Optimal.Spectrum :=
  [ { base := [0], incoming := [(1, [10])] }
  , { base := [],  incoming := [(0, [100])] } ]

-- No error. No warning. Each produces a plausible-looking answer.
#eval Paths.run cyclicNat        -- [0, 0]
#eval Shortest.run cyclicOpt     -- [some 0, some 100]
#eval Optimal.run cyclicSpec     -- [[0], [100]]

-- `isOrdered` exists precisely to catch this, and it does: all three say
-- `false`. The detector is correct. It is just never called by anything.
#eval isOrdered cyclicNat        -- false
#eval isOrdered cyclicOpt        -- false
#eval isOrdered cyclicSpec       -- false

/-- The soundness theorem typechecks on the cyclic graph above, with no
    hypothesis excluding it. This is the heart of the gap: `Satisfies`
    is defined purely as "this sequence arises from applying `specStep`
    in list order," which is unconditionally true regardless of whether
    the graph is a DAG. The proof is not wrong — it is just not a proof
    of what README.md's prose implies it is. -/
example : Satisfies Paths.algebra cyclicNat (Paths.run cyclicNat) :=
  Paths.sound cyclicNat

/-!
### Root cause

Three things compound to produce a *silent*, plausible-looking wrong answer
instead of a crash:

1. **`lookup` defaults to `A.zero` for an unknown index**
   (`GraphFold/Abstract/Core.lean`, `lookup`). When row 0 asks for vertex 1's
   value before vertex 1 has been processed, it receives `A.zero` — e.g.
   `none` (unreachable) or `[]` (empty spectrum) — which is indistinguishable
   from a vertex that is *legitimately* unreachable. There is no way, from
   the output alone, to tell "unreachable" apart from "I asked too early."

2. **`isOrdered` / `isOrderedFrom` are dead code.** They correctly detect
   exactly this condition, but `run`, `runFrom`, `step`, `Derives`, and the
   three `sound` theorems never call them. The file parser re-implements an
   equivalent check independently (`FROM < TO`), rather than reusing this
   function, which is why only the file-sourced path is actually protected.

3. **The specification has no acyclicity hypothesis to violate.**
   `Derives`/`Satisfies` make a claim about agreement with a particular
   (zero-defaulting) recursive computation, not a claim about shortest
   paths, path counts, or cost spectra being *correct* for an arbitrary
   graph. A proof of the former says nothing about the latter unless you
   also know the input was a DAG — and nothing enforces that at this layer.

-/

/-!
## Engineering checklist: what else should we distrust?

This section is intentionally a list of open questions, not resolved ones.
Each is a candidate for its own "Gap N" section once investigated.

- **Precondition laundering.** `Format.lean`'s `FROM < TO` check and
  `Core.lean`'s `isOrdered` are two independent implementations of what
  should be one invariant. Do they actually agree on every input? (We have
  not proven they do — only observed that they don't disagree yet.)

- **Uniqueness of `Derives`.** The `sound` theorems show *a* derivation
  exists for `run`'s output. Do they rule out some *other* list also
  satisfying `Derives` for the same graph? If `Derives` is not provably
  functional, "sound" may be compatible with multiple, inconsistent
  "correct" answers.

- **State reuse / stale `done`.** `lookup` takes an arbitrary `List α` as
  `done`. Nothing in its type ties `done`'s length to "exactly the rows
  processed so far." Could a caller (not going through `runFrom`) pass a
  `done` list that is too long, too short, or from a different graph
  entirely, and get a silently wrong but well-typed answer?

- **The trace's own blind spot.** `TraceMain.lean`'s runtime check compares
  the tracer's output to the original evaluator's output and only fails if
  they *disagree*. If both are built on the same zero-defaulting `lookup`,
  they will agree on a cyclic graph too — the cross-check cannot catch a
  bug that both sides share.

- **Does "no `sorry`, no `by`" imply what we think it implies?** Term-mode,
  tactic-free proofs are a strong signal about *how* a proof was built, not
  about what *proposition* it establishes. Every gap above is consistent
  with every current proof being accepted by the kernel.

The decisive move is not running more examples. It is picking one of the
questions above, stating it as a proposition Lean can check, and seeing
whether it's provable, disprovable, or — as with Gap 1 — true in a much
weaker sense than the English prose around it suggests.
-/
