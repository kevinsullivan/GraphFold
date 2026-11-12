import GraphFold.Abstract.Core

/-!
# Counting weighted paths
`Nat` with ordinary addition and multiplication. An edge weight is an algebraic multiplicity. The file adapter maps each
listed edge to multiplicity one; its source gets base one.
-/
namespace GraphFold.Paths

/-- The standard natural-number semiring restricted to the fold interface. -/
def algebra : Algebra Nat where
  zero := 0
  plus := Nat.add
  times := Nat.mul
  plus_assoc := Nat.add_assoc
  plus_zero := Nat.add_zero

/-- Concrete left-fold implementation: accumulate the number of paths. -/
def step (done : List Nat) (r : Row Nat) : Nat :=
  let contribution : (Nat × Nat) → Nat :=
    fun (u, weight) => (lookup algebra done u) * weight
  let accumulate : Nat → (Nat × Nat) → Nat :=
    fun count edge => count + contribution edge
  r.incoming.foldl accumulate r.base

/-- Compute values in vertex order using the path-counting recurrence. -/
def runFrom (done : List Nat) : Graph Nat → List Nat
  | [] => done
  | r :: rs =>
      let nextValue : Nat := step done r
      let nextPrefix : List Nat := done ++ [nextValue]
      runFrom nextPrefix rs

/-- Pure library entry point for path counts. -/
def run (g : Graph Nat) : List Nat := runFrom [] g


/-- Interpret each listed edge as one path choice, regardless of its cost.
    The source contributes one empty path; every other base is zero. -/
def fromRawFrom (source : Nat) : Nat → Graph Nat → Graph Nat
  | _, [] => []
  | i, r :: rs =>
      let baseValue : Nat := if i == source then 1 else 0
      let edges : List (Nat × Nat) :=
        r.incoming.map (fun (edge : Nat × Nat) => (edge.1, 1))
      ({ base := baseValue, incoming := edges } : Row Nat) ::
        fromRawFrom source (i + 1) rs

/-- Adapt a parsed graph to unweighted path-count semantics. -/
def fromRaw (source : Nat) (g : Graph Nat) : Graph Nat :=
  fromRawFrom source 0 g

end GraphFold.Paths
