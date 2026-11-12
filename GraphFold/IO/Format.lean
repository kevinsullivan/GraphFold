import GraphFold.Abstract.Core

/-!
# Shared edge-list input format

The input describes topology and nonnegative edge costs, independently of
any semiring. After removing blank lines and `#` comments:

```
vertices 4
source 0
edge 0 1 2
edge 0 2 5
edge 1 2 3
edge 1 3 1
edge 2 3 1
```

Each `edge FROM TO WEIGHT` is directed FROM → TO. Vertices are numbered
`0, ..., N-1`. The simple one-pass interpreters require `FROM < TO`;
this restriction is checked by the parser (it implies an acyclic graph).
The shortest-path and optimal-route specializations use weights as costs;
path counting ignores costs and assigns multiplicity one per listed edge.
-/
namespace GraphFold.Format

/-- A validated, semiring-independent graph and designated source vertex. -/
structure Input where
  source : Nat
  graph : Graph Nat
  deriving Repr

/-- An edge before conversion to destination-indexed incoming-edge rows. -/
structure Edge where
  src : Nat
  dst : Nat
  weight : Nat
  deriving Repr, BEq

/-- Read a nonnegative decimal integer with a helpful error on failure. -/
def nat (s : String) : Except String Nat :=
  match s.toNat? with
  | some (n : Nat) => (.ok n : Except String Nat)
  | none => (.error s!"expected nonnegative integer, got '{s}'" : Except String Nat)

/-- Split whitespace-delimited fields; tabs are treated as spaces. -/
def tokens (s : String) : List String :=
  let words : List String := (s.replace "\t" " ").splitOn " "
  words.filter (fun (t : String) => !t.isEmpty)

/-- Discard comments and empty lines, including inline `#` comments. -/
def meaningful (s : String) : List String :=
  let lines : List String := s.splitOn "\n"
  let uncommented : List String := lines.map (fun (line : String) =>
    ((line.splitOn "#").head!).trimAscii.toString)
  uncommented.filter (fun (line : String) => !line.isEmpty)

/-- Parse the three numbers of a single directed edge declaration. -/
def parseEdge (n : Nat) (s : String) : Except String Edge := do
  match tokens s with
  | ["edge", fromText, toText, weightText] =>
      let u : Nat ← nat fromText
      let v : Nat ← nat toText
      let w : Nat ← nat weightText
      if u >= n || v >= n then
        throw s!"edge {u} → {v}: vertex index must be less than {n}"
      if u >= v then
        throw s!"edge {u} → {v}: expected FROM < TO (topological order)"
      return { src := u, dst := v, weight := w }
  | _ => throw s!"expected 'edge FROM TO WEIGHT', got '{s}'"

/-- Convert an edge list into the destination-indexed rows used by the library.
    Graph-row bases are placeholders: each interpreter supplies its own seed. -/
def toGraph (n : Nat) (edges : List Edge) : Graph Nat :=
  (List.range n).map (fun (v : Nat) =>
    let incoming : List (Nat × Nat) := edges.filterMap (fun (e : Edge) =>
      if e.dst == v then some (e.src, e.weight) else none)
    ({ base := 0, incoming := incoming } : Row Nat))

/-- Parse `vertices N`, `source S`, followed by zero or more `edge` lines.
    Edge declarations must follow both header lines, in any edge order. -/
def parse (s : String) : Except String Input := do
  match meaningful s with
  | vertexLine :: sourceLine :: edgeLines =>
      match tokens vertexLine, tokens sourceLine with
      | ["vertices", nText], ["source", sourceText] =>
          let n : Nat ← nat nText
          let source : Nat ← nat sourceText
          if n == 0 then throw "vertices must be positive"
          if source >= n then throw "source must be less than vertex count"
          let edges : List Edge ← edgeLines.mapM (parseEdge n)
          let graph : Graph Nat := toGraph n edges
          return { source := source, graph := graph }
      | _, _ => throw "expected header lines 'vertices N' and 'source S'"
  | _ => throw "expected header lines 'vertices N' and 'source S'"

/-- Load and parse a graph file, retaining its filename in error messages. -/
def read (path : System.FilePath) : IO Input := do
  let contents : String ← IO.FS.readFile path
  match parse contents with
  | .ok (input : Input) => return input
  | .error (msg : String) => throw <| IO.userError s!"{path}: {msg}"

end GraphFold.Format
