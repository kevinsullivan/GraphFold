import GraphFold

/-! CLI: print one weighted path count per vertex. -/

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      try
        let input : GraphFold.Format.Input ← GraphFold.Format.read path
        let values : List Nat := GraphFold.Paths.run (GraphFold.Paths.fromRaw input.source input.graph)
        for (n, i) in values.zipIdx do
          IO.println s!"{i}: {n}"
        return 0
      catch e =>
        IO.eprintln s!"error: {e}"
        return 1
  | _ =>
      IO.eprintln "usage: lake exe paths <graph.txt>"
      return 2
