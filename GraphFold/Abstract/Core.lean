/-!
# Abstract weighted graph folds

The abstract algebra separates alternative-path aggregation (`plus`) from
edge extension (`times`). It intentionally requires only the monoid laws
needed to establish a fold: multiplication can be an arbitrary edge action.
A full semiring is a special case. No graph acyclicity is required to *state*
the recurrence; the finite evaluator assumes predecessors have already been
computed, so executables separately reject non-topological edges.
-/
namespace GraphFold

/-- Algebra of path alternatives, with a monoidal sum and an edge extension. -/
structure Algebra (α : Type) where
  /-- The carrier `α` holds both vertex values and edge weights. -/
  zero : α
  plus : α → α → α
  times : α → α → α
  plus_assoc : ∀ (a b c : α), plus (plus a b) c = plus a (plus b c)
  plus_zero : ∀ (a : α), plus a zero = a

/-- Optional *full semiring* axioms. The recurrence and bridge theorems
    need only the weaker `Algebra` laws; algorithms for general semirings can
    additionally provide this certificate. `one` is the empty-path weight. -/
structure SemiringLaws {α : Type} (A : Algebra α) where
  one : α
  plus_comm : ∀ (a b : α), A.plus a b = A.plus b a
  plus_zero_left : ∀ (a : α), A.plus A.zero a = a
  times_assoc : ∀ (a b c : α), A.times (A.times a b) c = A.times a (A.times b c)
  times_one : ∀ (a : α), A.times a one = a
  one_times : ∀ (a : α), A.times one a = a
  times_zero : ∀ (a : α), A.times a A.zero = A.zero
  zero_times : ∀ (a : α), A.times A.zero a = A.zero
  left_distrib : ∀ (a b c : α), A.times a (A.plus b c) =
    A.plus (A.times a b) (A.times a c)
  right_distrib : ∀ (a b c : α), A.times (A.plus a b) c =
    A.plus (A.times a c) (A.times b c)

/-- A node carries an initial contribution and weighted incoming edges. -/
structure Row (α : Type) where
  base : α
  /-- Each pair is `(predecessor vertex, edge weight)`. -/
  incoming : List (Nat × α)
  deriving Repr, BEq, DecidableEq

/-- A graph is ordered by increasing vertex number, starting at zero. -/
abbrev Graph (α : Type) := List (Row α)

/-- Lookup of a previously computed value; missing values contribute zero. -/
def lookup {α : Type} (A : Algebra α) (done : List α) (u : Nat) : α :=
  (done[u]?).getD A.zero

/-- The mathematical single-vertex recurrence, written as a right fold. -/
def specStep {α : Type} (A : Algebra α) (done : List α) (r : Row α) : α :=
  let contribution : (Nat × α) → α :=
    fun (u, weight) => A.times (lookup A done u) weight
  let combine : (Nat × α) → α → α :=
    fun edge total => A.plus (contribution edge) total
  let incomingTotal : α := r.incoming.foldr combine A.zero
  A.plus r.base incomingTotal

/-- Derivation certificates document every sequential recurrence step. -/
inductive Derives {α : Type} (A : Algebra α) : List α → Graph α → List α → Prop where
  | done (computed : List α) : Derives A computed [] computed
  | next (computed : List α) (r : Row α) (remaining : Graph α)
      (value : α) (result : List α)
      (eq_step : value = specStep A computed r)
      (tail : Derives A (computed ++ [value]) remaining result) :
      Derives A computed (r :: remaining) result

/-- A correct output admits a derivation of the original graph recurrence. -/
def Satisfies {α : Type} (A : Algebra α) (g : Graph α) (out : List α) : Prop :=
  Derives A [] g out

/-- Strict topological validation: an incoming edge must point backward. -/
def isOrderedFrom {α : Type} (i : Nat) : Graph α → Bool
  | [] => true
  | r :: rs => r.incoming.all (fun e => e.1 < i) && isOrderedFrom (i + 1) rs

/-- File-based graphs are accepted only when all predecessors are earlier. -/
def isOrdered {α : Type} (g : Graph α) : Bool := isOrderedFrom 0 g

/-- Generic monoid lemma. The proof is a structural recursion on the
    input list. Its nil case uses the right identity, while the cons case
    composes the induction hypothesis with associativity. No tactics. -/
theorem foldl_eq_foldr {α β : Type} (A : Algebra α) (xs : List β) (f : β → α)
    (start : α) :
    xs.foldl (fun a x => A.plus a (f x)) start =
      A.plus start (xs.foldr (fun x a => A.plus (f x) a) A.zero) :=
  List.rec
    (motive := fun (ys : List β) => ∀ (acc : α),
      ys.foldl (fun a x => A.plus a (f x)) acc =
        A.plus acc (ys.foldr (fun x a => A.plus (f x) a) A.zero))
    (fun (acc : α) => (A.plus_zero acc).symm)
    (fun (x : β) (ys : List β)
         (ih : ∀ (acc : α),
           ys.foldl (fun (a : α) (y : β) => A.plus a (f y)) acc =
             A.plus acc (ys.foldr (fun (y : β) (a : α) => A.plus (f y) a) A.zero))
         (acc : α) =>
      Eq.trans
        (ih (A.plus acc (f x)))
        (A.plus_assoc acc (f x)
          (ys.foldr (fun (y : β) (a : α) => A.plus (f y) a) A.zero)))
    xs start

end GraphFold
