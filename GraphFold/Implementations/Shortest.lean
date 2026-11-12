import GraphFold.Abstract.Core

/-!
# Shortest paths, min-plus with infinity
`none` means infinity/unreachable; `some n` means cost `n`.
All input edge weights are nonnegative natural numbers.
-/
namespace GraphFold.Shortest

/-- Minimum with an infinite element represented by `none`. -/
def choice : Option Nat → Option Nat → Option Nat
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

/-- Extend a path by an edge; infinity remains infinity. -/
def extend : Option Nat → Option Nat → Option Nat
  | some a, some b => some (a + b)
  | _, _ => none

/-- Associativity of minimum with infinity, proved by pattern matching.
    The only non-definitional case is finite/finite/finite. -/
private theorem choice_assoc : (a b c : Option Nat) →
    choice (choice a b) c = choice a (choice b c)
  | none, _, _ => rfl
  | some _, none, _ => rfl
  | some _, some _, none => rfl
  | some a, some b, some c => congrArg some (Nat.min_assoc a b c)

/-- Infinity is a right identity for alternative-path choice. -/
private theorem choice_zero : (a : Option Nat) → choice a none = a
  | none => rfl
  | some _ => rfl

/-- Min-plus satisfies exactly the aggregation laws required by the fold. -/
def algebra : Algebra (Option Nat) where
  zero := none
  plus := choice
  times := extend
  plus_assoc := choice_assoc
  plus_zero := choice_zero

/-- A distinct, executable *left-fold* implementation of the recurrence. -/
def step (done : List (Option Nat)) (r : Row (Option Nat)) : Option Nat :=
  let contribution : (Nat × Option Nat) → Option Nat :=
    fun (u, weight) => extend (lookup algebra done u) weight
  let accumulate : Option Nat → (Nat × Option Nat) → Option Nat :=
    fun best edge => choice best (contribution edge)
  r.incoming.foldl accumulate r.base

/-- Iterate in input vertex order, retaining all intermediate answers. -/
def runFrom (done : List (Option Nat)) : Graph (Option Nat) → List (Option Nat)
  | [] => done
  | r :: rs =>
      let nextValue : Option Nat := step done r
      let nextPrefix : List (Option Nat) := done ++ [nextValue]
      runFrom nextPrefix rs

/-- Public pure library function: one cost (or infinity) for each vertex. -/
def run (g : Graph (Option Nat)) : List (Option Nat) := runFrom [] g

/-- Convert one graph row into a min-plus row. The CLI source is injected
    through the base value; other vertices begin at infinity. -/
def fromRawFrom (source : Nat) : Nat → Graph Nat → Graph (Option Nat)
  | _, [] => []
  | i, r :: rs =>
      let baseValue : Option Nat := if i == source then some 0 else none
      let edges : List (Nat × Option Nat) :=
        r.incoming.map (fun (u, w) => (u, some w))
      ({ base := baseValue, incoming := edges } : Row (Option Nat)) ::
        fromRawFrom source (i + 1) rs

/-- Convert the common natural-weight graph to shortest-path semantics. -/
def fromRaw (source : Nat) (g : Graph Nat) : Graph (Option Nat) :=
  fromRawFrom source 0 g

end GraphFold.Shortest
