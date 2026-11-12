import GraphFold.Implementations.Optimal

/-!
# Third independent proof bridge: optimal-route spectra

The implementation's `foldl` and specification's `foldr` agree because
concatenation has an identity and is associative. This is a proof about the
*entire path-cost spectrum*, stronger than a proof only about its min/count
summary. All proofs are explicit Lean terms, not tactics.
-/
namespace GraphFold.Optimal

/-- The concrete edge aggregation equals the abstract recurrence step. -/
theorem step_refines (done : List Spectrum) (r : Row Spectrum) :
    step done r = specStep algebra done r :=
  foldl_eq_foldr algebra r.incoming
    (fun (e : Nat × Spectrum) => extend (lookup algebra done e.1) e.2) r.base

/-- Construct the recurrence derivation by induction on remaining rows. -/
theorem runFrom_sound (done : List Spectrum) (g : Graph Spectrum) :
    Derives algebra done g (runFrom done g) :=
  List.rec
    (motive := fun (rows : Graph Spectrum) => ∀ (pre : List Spectrum),
      Derives algebra pre rows (runFrom pre rows))
    (fun (pre : List Spectrum) => Derives.done pre)
    (fun (r : Row Spectrum) (rs : Graph Spectrum)
         (ih : ∀ (pre : List Spectrum),
           Derives algebra pre rs (runFrom pre rs))
         (pre : List Spectrum) =>
      Derives.next pre r rs (step pre r)
        (runFrom (pre ++ [step pre r]) rs)
        (step_refines pre r)
        (ih (pre ++ [step pre r])))
    g done

/-- The entire spectrum evaluation satisfies the abstract specification. -/
theorem sound (g : Graph Spectrum) : Satisfies algebra g (run g) :=
  runFrom_sound [] g

end GraphFold.Optimal
