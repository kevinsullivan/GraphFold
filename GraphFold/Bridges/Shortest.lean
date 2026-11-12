import GraphFold.Implementations.Shortest

/-!
# Bridge: shortest implementation refines the abstract recurrence
All proofs are explicit terms. In particular, `runFrom_sound` is built by
`List.rec` with one `Derives.next` certificate per processed graph row.
-/
namespace GraphFold.Shortest

/-- The concrete left fold computes the same value as the specification's
    right fold. Definitional reduction exposes the generic monoid lemma. -/
theorem step_refines (done : List (Option Nat)) (r : Row (Option Nat)) :
    step done r = specStep algebra done r :=
  foldl_eq_foldr algebra r.incoming
    (fun (e : Nat × Option Nat) => extend (lookup algebra done e.1) e.2) r.base

/-- Construct a recurrence derivation, one constructor at a time.
    The induction hypothesis is parametrized over the computed prefix. -/
theorem runFrom_sound (done : List (Option Nat)) (g : Graph (Option Nat)) :
    Derives algebra done g (runFrom done g) :=
  List.rec
    (motive := fun (rows : Graph (Option Nat)) => ∀ (pre : List (Option Nat)),
      Derives algebra pre rows (runFrom pre rows))
    (fun (pre : List (Option Nat)) => Derives.done pre)
    (fun (r : Row (Option Nat)) (rs : Graph (Option Nat))
         (ih : ∀ (pre : List (Option Nat)),
           Derives algebra pre rs (runFrom pre rs))
         (pre : List (Option Nat)) =>
      Derives.next pre r rs (step pre r)
        (runFrom (pre ++ [step pre r]) rs)
        (step_refines pre r)
        (ih (pre ++ [step pre r])))
    g done

/-- Main library correctness theorem, specialized to an empty prefix. -/
theorem sound (g : Graph (Option Nat)) : Satisfies algebra g (run g) :=
  runFrom_sound [] g

end GraphFold.Shortest
