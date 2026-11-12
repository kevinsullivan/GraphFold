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
exactly as README.md's "Using GraphFold as a library" section demonstrates,
and nothing in it checks acyclicity.
-/

/-- Recall from `Core.lean`: a `Graph α` is a `List (Row α)`, one `Row` per
    vertex, in vertex-number order. Each `Row` has a `base : α` (the vertex's
    own starting contribution) and an `incoming : List (Nat × α)` — one
    `(predecessor vertex, edge weight)` pair per incoming edge.

    Below, row 0 ("vertex 0") lists vertex 1 as a predecessor — but vertex 1
    is row *1*, which comes *after* row 0 in the list, so it hasn't been
    computed yet when row 0 is processed. Row 1, in turn, lists vertex 0 as
    a predecessor. That's a genuine mutual dependency: this exact shape
    cannot come from the file parser, which forbids `FROM < TO` violations
    (vertex 1 → vertex 0 would have to be written as an edge from a higher
    index to a lower one), but nothing stops constructing it directly as a
    `Graph` value, bypassing the parser entirely. -/
def cyclicNat : Graph Nat :=
  [ { base := 0, incoming := [(1, 10)] }
  , { base := 0, incoming := [(0, 100)] } ]

/-- The same cyclic shape as `cyclicNat` above, retyped for `Shortest`'s
    carrier `Option Nat` (`none` = unreachable) so we can run it through
    `Shortest.run` instead of `Paths.run`. -/
def cyclicOpt : Graph (Option Nat) :=
  [ { base := some 0, incoming := [(1, some 10)] }
  , { base := none,   incoming := [(0, some 100)] } ]

/-- The same cyclic shape again, retyped for `Optimal`'s carrier
    `Spectrum = List Nat` (`[]` = no paths reach this vertex yet) so we can
    run it through `Optimal.run`. -/
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

### Where exactly is the missing math?

Both the file-based CLI and the library API bottom out in the *same* code:
`lookup`, `specStep`, `step`, `run`, `Derives` — all in `Core.lean` and the
three `Implementations/*.lean` files. Grep the whole project for
`isOrdered` or `FROM < TO` and you find exactly one place either check is
performed: `Format.lean`'s `parseEdge`, which only the file-based path ever
calls. The library API shares every line of the evaluator with the CLI and
none of its gate — which is precisely why it's exposed and the CLI isn't.

That asymmetry is the tell. The `FROM < TO` check is not a property of the
*theory* — not of `Algebra`, `Graph`, `Derives`, or `Satisfies` — it's a
property of one specific input adapter, bolted on after the fact. Put
mathematically: `Graph α` is defined as plain `List (Row α)`, with nothing
in the type recording that it came from a topologically valid construction.
`Derives`/`Satisfies` are stated for *any* `Graph α` — DAG or not — so no
amount of using them correctly can recover a guarantee the type never
carried. The missing mathematics isn't a missing `if`-check; it's a missing
*witness* — some proof-carrying evidence of "this `Row` list is
topologically ordered" that would have to live in the shared core
(`Core.lean`) to protect every caller, rather than in one caller's input
adapter after the type has already erased the information needed to tell.

(Candidate shapes for that witness — not attempted here, per this file's
own rule that fixes belong in the library, not in this case study: thread
an `isOrdered g = true` hypothesis through `Derives`/`Satisfies` themselves;
index `Graph` by a separately-defined "this is a DAG" proposition so an
un-ordered graph is simply not a term of the right type; or change `lookup`
to return `Option α` and force every caller to handle "not yet known"
instead of silently reading `A.zero`.)

### Checked against the literature: where this actually went wrong

This isn't a hunch — it matches a precise, well-known pattern in the
algebraic-path-problem literature, and GraphFold deviates from it in an
identifiable way. Take Mehryar Mohri, *"Semiring Frameworks and Algorithms
for Shortest-Distance Problems,"* Journal of Automata, Languages and
Combinatorics 7(3):321–350, 2002 (one of the sources `README.md`'s
Historical Context section already points to for this project's lineage).

Mohri's framework defines the target quantity — the shortest distance
δ(s, q) — **independently of any algorithm**, as a sum over the actual set
of paths P(q) from the source to q:

```
δ(s, s) = 1̄
δ(s, q) = ⊕_{π ∈ P(q)} w[π]        (his Equation 1, for q ≠ s)
```

That sum is only guaranteed to be well-defined under a stated hypothesis:
the semiring must be *k-closed for G* (Definition 8). His correctness
theorems are then always conditional on that hypothesis — most sharply in
his Corollary 2: *"Let G be an acyclic weighted directed graph... If we run
the [topological-order algorithm]... then... d[q] = δ(s, q)."* Its own proof
is one line: *"When G is acyclic, by definition, any semiring is right
k-closed for G."* Acyclicity isn't a side remark there — it's the exact
premise that licenses equating the algorithm's output with the independently
stated target quantity.

GraphFold has no analogue of δ(s, q)/Equation (1) anywhere in `Core.lean`.
There is no proposition in this codebase that characterizes "the correct
shortest distance (or path count, or cost spectrum)" independently of
`specStep`'s own recursive unfolding. `Derives`/`Satisfies` instead *define*
correctness as "agrees with `specStep` applied in list order" — which means
`Satisfies`/`sound` are claims that two renderings of the **same** procedure
(a left fold and a right fold of the same `specStep`) agree with each other,
not claims that the procedure's output equals an independently specified
mathematical quantity. That is a strictly weaker kind of theorem than the
ones in the literature this project cites as its own motivation, and it is
weaker in exactly the place that matters: it has no target for the cyclic
case to be *wrong relative to*, so there is nothing for a cyclic input to
contradict. The acyclicity hypothesis in Mohri's Corollary 2 is precisely
what `isOrdered` was presumably meant to formalize — but, as diagnosed
above, it never appears as a hypothesis of `Derives`, `Satisfies`, or any
`sound` theorem. The error wasn't choosing the wrong algebraic laws for
`Algebra` (those match the literature fine for the acyclic case — Mohri's
own proof shows acyclicity alone, with no closure or idempotence
requirement, suffices); the error was omitting the hypothesis and the
independent target specification that the cited literature always states
explicitly, and silently treating "the algorithm's self-consistency" as if
it were a proof of "the algorithm's correctness."
-/

/-!
## Resolved — `Derives` is provably unique

One item from the checklist below turned out not to be a gap. It's worth
keeping the resolution visible, not just the open questions: the engineering
process is supposed to produce both.

> Do the `sound` theorems rule out some *other* list also satisfying
> `Derives` for the same graph? If `Derives` isn't provably functional,
> "sound" could be compatible with multiple, inconsistent "correct" answers.
-/

/-- `Derives` is **right-unique**: fixing the starting prefix `computed` and
    the graph `g`, there is at most one `result` that `Derives A computed g`
    can relate them to. (Two different proofs of `Derives A computed g r₁`
    and `Derives A computed g r₂` always force `r₁ = r₂`.) Proved by
    recursion on the graph, tracking that both derivations' single step
    (`eq_step`) computes the same deterministic `specStep`, hence the same
    next prefix, hence (by the induction hypothesis) the same final result.
    No tactics; no `sorry`. -/
theorem Derives.unique {α : Type} {A : Algebra α} :
    ∀ {computed : List α} {g : Graph α} {result1 result2 : List α},
    Derives A computed g result1 → Derives A computed g result2 → result1 = result2
  -- Empty graph: `Derives.done` is the only constructor, and its own type
  -- forces the result to equal `computed` — so both sides are literally
  -- the same term, and `rfl` (reflexivity) closes it.
  | _, [], _, _, Derives.done _, Derives.done _ => rfl
  -- Nonempty graph: `Derives.next` is the only constructor. Both proofs
  -- compute `value1`/`value2` from the *same* `computed` and `r` via the
  -- deterministic function `specStep`, so `eq1.trans eq2.symm` (chain the
  -- first equation with the second, reversed) gives `value1 = value2`.
  | _, _ :: _remaining, _, _,
    Derives.next _ _ _ value1 _ eq1 tail1,
    Derives.next _ _ _ value2 _ eq2 tail2 =>
      have hval : value1 = value2 := eq1.trans eq2.symm
      -- `tail1 : Derives A (computed ++ [value1]) remaining result1`
      -- `tail2 : Derives A (computed ++ [value2]) remaining result2`
      -- These don't look like the same proposition yet, because `value1`
      -- and `value2` are different variables — even though `hval` says
      -- they're equal. `hval ▸ tail2` ("transport tail2 along hval")
      -- rewrites every occurrence of `value2` in `tail2`'s type to
      -- `value1`, producing `Derives A (computed ++ [value1]) remaining
      -- result2` — now the same prefix as `tail1`'s type, so the
      -- recursive call to `Derives.unique` type-checks and finishes the
      -- proof by induction on the (structurally smaller) `remaining`.
      Derives.unique tail1 (hval ▸ tail2)

/-!
This closes the uniqueness question cleanly: `specStep` is a plain
(non-relational) function, so each `next` step is forced, and by induction
the whole derivation is forced. "Sound" is therefore not compatible with
multiple answers for a fixed, well-formed input — that particular worry
was unfounded. (It says nothing about Gap 1: uniqueness of the *derivation*
and *correctness of the recurrence for cyclic input* are different claims,
and this theorem doesn't touch the second one.)
-/

/-!
## Engineering checklist: what else should we distrust?

This section is intentionally a list of open questions, not resolved ones.
Each is a candidate for its own "Gap N" section once investigated. (One
item that used to be here — uniqueness of `Derives` — is resolved above.)

- **Precondition laundering.** (Naming the smell: a precondition gets
  re-derived from scratch in a second place instead of being stated once
  and reused, so the two copies can silently drift apart.) `Format.lean`'s
  `FROM < TO` check and `Core.lean`'s `isOrdered` are two independent
  implementations of what should be one invariant. Do they actually agree
  on every input? (We have not proven they do — only observed that they
  don't disagree yet.)

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
