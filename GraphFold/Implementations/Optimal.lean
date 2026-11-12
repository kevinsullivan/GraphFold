import GraphFold.Abstract.Core

/-!
# Optimal-route multiplicities from a path-cost spectrum

This third interpretation is deliberately richer than a single shortest cost.
At each vertex we retain the *list of costs of every path* from the source.
Lists preserve multiplicity: `[5, 5]` represents two different routes
that both cost five. We then extract the minimum and its multiplicity.

The carrier `List Nat` has an associative alternative operator `++` and
empty alternative `[]`; extending a set of routes across an edge is a
Cartesian product with ordinary addition of costs. This is the concrete
list-valued algebra required by `GraphFold.Algebra`. Unlike a canonical
polynomial semiring, list concatenation is NOT commutative: this example
teaches the weaker algebraic laws actually needed by the fold theorem.
The full path spectrum can be exponentially large in the input graph.
-/
namespace GraphFold.Optimal

/-- A spectrum lists one total cost for every distinct path to a vertex. -/
abbrev Spectrum := List Nat

/-- Alternative routes are concatenated, preserving equal-cost multiplicity. -/
def choice (a b : Spectrum) : Spectrum := a ++ b

/-- Every left path can be extended by every right-hand edge alternative. -/
def extend (a b : Spectrum) : Spectrum :=
  a.flatMap (fun (prefixCost : Nat) =>
    b.map (fun (edgeCost : Nat) => prefixCost + edgeCost))

/-- Lists under append give the monoidal aggregation laws required by folds. -/
def algebra : Algebra Spectrum where
  zero := ([] : Spectrum)
  plus := choice
  times := extend
  plus_assoc := List.append_assoc
  plus_zero := List.append_nil

/-- An independent left-fold interpreter; the abstract specification uses foldr. -/
def step (done : List Spectrum) (r : Row Spectrum) : Spectrum :=
  let contribution : (Nat × Spectrum) → Spectrum :=
    fun (u, edgeSpectrum) => extend (lookup algebra done u) edgeSpectrum
  let accumulate : Spectrum → (Nat × Spectrum) → Spectrum :=
    fun (allCosts : Spectrum) (edge : Nat × Spectrum) =>
      choice allCosts (contribution edge)
  r.incoming.foldl accumulate r.base

/-- Sequentially evaluate all vertices, retaining every path-cost spectrum. -/
def runFrom (done : List Spectrum) : Graph Spectrum → List Spectrum
  | [] => done
  | r :: rest =>
      let value : Spectrum := step done r
      let newDone : List Spectrum := done ++ [value]
      runFrom newDone rest

/-- Pure library entry point. The result includes *all* path costs. -/
def run (g : Graph Spectrum) : List Spectrum := runFrom [] g

/-- Translate a graph file: a source path costs zero; every edge contributes
    its declared cost. Other vertices have no zero-length source path. -/
def fromRawFrom (source : Nat) : Nat → Graph Nat → Graph Spectrum
  | _, [] => []
  | i, r :: rs =>
      let base : Spectrum := if i == source then [0] else []
      let incoming : List (Nat × Spectrum) :=
        r.incoming.map (fun (edge : Nat × Nat) => (edge.1, [edge.2]))
      ({ base := base, incoming := incoming } : Row Spectrum) ::
        fromRawFrom source (i + 1) rs

/-- Convert the same input used by shortest paths and path counting. -/
def fromRaw (source : Nat) (g : Graph Nat) : Graph Spectrum :=
  fromRawFrom source 0 g

/-- The result is `(minimum total cost, number of minimum-cost paths)`.
    `none` means unreachable. Distinct equal-cost paths are counted separately. -/
def summarize : Spectrum → Option (Nat × Nat)
  | [] => none
  | cost :: remaining =>
      match summarize remaining with
      | none => some (cost, 1)
      | some (best, ways) =>
          if cost < best then some (cost, 1)
          else if cost == best then some (best, ways + 1)
          else some (best, ways)

/-- Report optimal cost and tie count for every vertex, without altering the
    proven spectrum evaluator. -/
def runSummary (g : Graph Spectrum) : List (Option (Nat × Nat)) :=
  (run g).map summarize

end GraphFold.Optimal
