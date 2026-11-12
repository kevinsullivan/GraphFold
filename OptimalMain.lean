import GraphFold

/-!
# CLI: minimum cost together with the number of tied minimum-cost routes

The calculation itself is performed by `Optimal.run` in the library;
`summarize` is a postprocessing function on its fully evaluated spectra.
-/

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      try
        let input : GraphFold.Format.Input ← GraphFold.Format.read path
        let graph : GraphFold.Graph GraphFold.Optimal.Spectrum :=
          GraphFold.Optimal.fromRaw input.source input.graph
        let answers : List (Option (Nat × Nat)) :=
          GraphFold.Optimal.runSummary graph
        for (answer, i) in answers.zipIdx do
          let text : String := match answer with
            | none => "INF,count=0"
            | some (cost, count) => s!"min={cost},count={count}"
          IO.println s!"{i}: {text}"
        return 0
      catch e =>
        IO.eprintln s!"error: {e}"
        return 1
  | _ =>
      IO.eprintln "usage: lake exe optimal <graph.txt>"
      return 2
