import GraphFold

/-!
# Library and executable-parser tests

The `example` declarations are checked by Lean's elaborator. Runtime tests
exercise the algebra-neutral edge-list parser and all three graph adapters.
-/
open GraphFold

/-- Raw graph rows keep the file's costs and have neutral placeholder bases. -/
private def sample : Graph Nat :=
  [ { base := 0, incoming := [] }
  , { base := 0, incoming := [(0, 2)] }
  , { base := 0, incoming := [(0, 5), (1, 3)] }
  , { base := 0, incoming := [(1, 1), (2, 1)] } ]

/-- The source is seeded and each file edge becomes multiplicity one. -/
private def counted : Graph Nat := Paths.fromRaw 0 sample

/-- One empty source path; counts at vertices 1,2,3 are 1,2,3. -/
example : Paths.run counted = ([1, 1, 2, 3] : List Nat) := Eq.refl _

/-- Minimum costs from source 0 are 0,2,5,3. -/
example : Shortest.run (Shortest.fromRaw 0 sample) =
  ([some 0, some 2, some 5, some 3] : List (Option Nat)) := Eq.refl _

/-- The new algebra remembers all path costs, including equal-cost routes. -/
private def spectra : Graph Optimal.Spectrum := Optimal.fromRaw 0 sample

/-- Vertex 2 has two distinct paths of cost five. -/
example : Optimal.run spectra =
  ([[0], [2], [5, 5], [3, 6, 6]] : List Optimal.Spectrum) := Eq.refl _

/-- Extracting optimal cost and its multiplicity preserves tie information. -/
example : Optimal.runSummary spectra =
  ([some (0, 1), some (2, 1), some (5, 2), some (3, 1)] :
    List (Option (Nat × Nat))) := Eq.refl _

/-- A dedicated graph exhibits two equally cheap routes to vertex 3. -/
private def tied : Graph Nat :=
  [ { base := 0, incoming := [] }
  , { base := 0, incoming := [(0, 2)] }
  , { base := 0, incoming := [(0, 1)] }
  , { base := 0, incoming := [(1, 3), (2, 4)] } ]

example : Optimal.runSummary (Optimal.fromRaw 0 tied) =
  ([some (0, 1), some (2, 1), some (1, 1), some (5, 2)] :
    List (Option (Nat × Nat))) := Eq.refl _

/-- Each implementation has a separate proof of the abstract recurrence. -/
example : Satisfies Paths.algebra counted (Paths.run counted) :=
  Paths.sound counted
example : Satisfies Shortest.algebra (Shortest.fromRaw 0 sample)
    (Shortest.run (Shortest.fromRaw 0 sample)) :=
  Shortest.sound (Shortest.fromRaw 0 sample)
example : Satisfies Optimal.algebra spectra (Optimal.run spectra) :=
  Optimal.sound spectra

private def input : String :=
  "vertices 4\nsource 0\nedge 0 1 2\nedge 0 2 5\nedge 1 2 3\nedge 1 3 1\nedge 2 3 1\n"

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw <| IO.userError s!"FAILED: {name}"
  IO.println s!"PASS: {name}"

private def Except.isError : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

/-- Test the APIs, parser, source seeding, and invalid input rejection. -/
def main : IO UInt32 := do
  try
    check "counting-library adapter" (Paths.run counted == [1, 1, 2, 3])
    check "shortest-path library"
      (Shortest.run (Shortest.fromRaw 0 sample) ==
        [some 0, some 2, some 5, some 3])
    check "spectrum library"
      (Optimal.run spectra == [[0], [2], [5, 5], [3, 6, 6]])
    check "minimum and tied route counts"
      (Optimal.runSummary (Optimal.fromRaw 0 tied) ==
        [some (0, 1), some (2, 1), some (1, 1), some (5, 2)])
    match (Format.parse input : Except String Format.Input) with
    | .error e => throw <| IO.userError e
    | .ok parsed =>
        check "parse edge-list DAG" (parsed.graph == sample)
        check "count parsed DAG"
          (Paths.run (Paths.fromRaw parsed.source parsed.graph) == [1, 1, 2, 3])
        check "optimal parsed DAG"
          (Optimal.runSummary (Optimal.fromRaw parsed.source parsed.graph) ==
            [some (0, 1), some (2, 1), some (5, 2), some (3, 1)])
        check "shortest parsed DAG"
          (Shortest.run (Shortest.fromRaw parsed.source parsed.graph) ==
            [some 0, some 2, some 5, some 3])
    check "unreachable spectrum"
      (Optimal.runSummary (Optimal.fromRaw 0
        [ { base := 0, incoming := [] },
          { base := 0, incoming := [(0, 7)] },
          { base := 0, incoming := [] } ]) ==
         [some (0, 1), some (7, 1), none])
    check "reject cycle"
      ((Format.parse "vertices 2\nsource 0\nedge 0 1 2\nedge 1 0 3\n").isError)
    check "reject malformed weight"
      ((Format.parse "vertices 2\nsource 0\nedge 0 1 x\n").isError)
    check "reject out-of-range endpoint"
      ((Format.parse "vertices 2\nsource 0\nedge 0 2 1\n").isError)
    check "reject incomplete header"
      ((Format.parse "vertices 2\nedge 0 1 2\n").isError)
    check "reject zero vertices"
      ((Format.parse "vertices 0\nsource 0\n").isError)
    check "source may differ from vertex zero"
      (match Format.parse "vertices 3\nsource 1\nedge 1 2 7\n" with
       | .ok parsed =>
          Paths.run (Paths.fromRaw parsed.source parsed.graph) == [0, 1, 1] &&
          Optimal.runSummary (Optimal.fromRaw parsed.source parsed.graph) ==
            [none, some (0, 1), some (7, 1)]
       | .error _ => false)
    IO.println "All tests passed."
    return 0
  catch e =>
    IO.eprintln s!"{e}"
    return 1
