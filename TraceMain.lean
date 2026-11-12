import GraphFold.Trace

/-!
# Trace executable

`lake exe trace <shortest|paths|optimal> <graph.txt>` emits explicit, typed
steps from Lean. Each `edge` event describes the before/after left-fold
accumulator, allowing the HTML interface to replay the computation.
-/

open GraphFold

def main (args : List String) : IO UInt32 := do
  match args with
  | [mode, path] =>
    try
      let input : Format.Input ← Format.read path
      let events : List Trace.Event ←
        if mode == "shortest" then
          let g : Graph (Option Nat) := Shortest.fromRaw input.source input.graph
          let output : List (Option Nat) × List Trace.Event :=
            Trace.evaluate Shortest.algebra Trace.showShortest g input.graph
          if output.1 != Shortest.run g then
            throw <| IO.userError "trace/evaluator disagreement (shortest)"
          pure output.2
        else if mode == "paths" then
          let g : Graph Nat := Paths.fromRaw input.source input.graph
          let output : List Nat × List Trace.Event :=
            Trace.evaluate Paths.algebra Trace.showPaths g input.graph
          if output.1 != Paths.run g then
            throw <| IO.userError "trace/evaluator disagreement (paths)"
          pure output.2
        else if mode == "optimal" then
          let g : Graph Optimal.Spectrum := Optimal.fromRaw input.source input.graph
          let output : List Optimal.Spectrum × List Trace.Event :=
            Trace.evaluate Optimal.algebra Trace.showSpectrum g input.graph
          if output.1 != Optimal.run g then
            throw <| IO.userError "trace/evaluator disagreement (optimal)"
          pure output.2
        else
          throw <| IO.userError "expected shortest, paths, or optimal"
      for e in events do
        IO.println (Trace.encode e)
      return 0
    catch e =>
      IO.eprintln s!"error: {e}"
      return 1
  | _ =>
    IO.eprintln "usage: lake exe trace <shortest|paths|optimal> <graph.txt>"
    return 2
