import GraphFold

/-! CLI: print one shortest-path distance per vertex (`INF` if unreachable). -/

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      try
        let input : GraphFold.Format.Input ← GraphFold.Format.read path
        let values : List (Option Nat) := GraphFold.Shortest.run
          (GraphFold.Shortest.fromRaw input.source input.graph)
        for (x, i) in values.zipIdx do
          IO.println s!"{i}: {match x with | none => "INF" | some n => toString n}"
        return 0
      catch e =>
        IO.eprintln s!"error: {e}"
        return 1
  | _ =>
      IO.eprintln "usage: lake exe shortest <graph.txt>"
      return 2
