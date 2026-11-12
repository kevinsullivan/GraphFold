import GraphFold

/-!
# Human-readable execution trace

A trace records vertex initialization, each left-fold contribution, and vertex
completion. The `computed` field is assembled by exactly the same left-fold
operations as the three concrete evaluators. The browser only replays events.

Every event is serialized as a pipe-delimited line; value printers never emit
pipes. This simple transport deliberately avoids depending on a JSON library.
-/

namespace GraphFold.Trace

/-- A single evaluation event. Each value is a printable rendering of `α`. -/
inductive Event where
  | start (vertex : Nat) (base : String)
  | edge (vertex predecessor weight : Nat) (prior contribution before after : String)
  | finish (vertex : Nat) (value : String)
  deriving Repr

/-- Encode one event for the local Node server. -/
def encode : Event → String
  | .start vertex base => s!"start|{vertex}|{base}"
  | .edge vertex predecessor weight prior contribution before after =>
      s!"edge|{vertex}|{predecessor}|{weight}|{prior}|{contribution}|{before}|{after}"
  | .finish vertex value => s!"finish|{vertex}|{value}"

/-- Accumulate a single vertex, appending an event after each edge contribution.
    Edge labels supplied separately preserve the graph file's original costs
    even for path counting (which interprets each edge multiplicity as one). -/
def traceEdges {α : Type} (A : Algebra α) (showValue : α → String)
    (vertex : Nat) (done : List α) (base : α)
    (edges : List (Nat × α × Nat)) : α × List Event :=
  edges.foldl
    (fun (state : α × List Event) (e : Nat × α × Nat) =>
      let before : α := state.1
      let previous : α := lookup A done e.1
      let contribution : α := A.times previous e.2.1
      let after : α := A.plus before contribution
      let record : Event := .edge vertex e.1 e.2.2
        (showValue previous) (showValue contribution)
        (showValue before) (showValue after)
      (after, state.2 ++ [record]))
    (base, [])

/-- Evaluate all rows, collecting events and the computed vertex values.
    `weights` is the corresponding graph with original numeric edge labels. -/
def evaluateFrom {α : Type} (A : Algebra α) (showValue : α → String)
    (done : List α) (vertex : Nat) : Graph α → Graph Nat → List α × List Event
  | [], _ => (done, [])
  | row :: remaining, raw :: rawRemaining =>
      let labeled : List (Nat × α × Nat) :=
        (row.incoming.zip raw.incoming).map
          (fun (pair : (Nat × α) × (Nat × Nat)) =>
            (pair.1.1, pair.1.2, pair.2.2))
      let folded : α × List Event :=
        traceEdges A showValue vertex done row.base labeled
      let suffix : List α × List Event :=
        evaluateFrom A showValue (done ++ [folded.1]) (vertex + 1)
          remaining rawRemaining
      let events : List Event :=
        [.start vertex (showValue row.base)] ++ folded.2 ++
        [.finish vertex (showValue folded.1)] ++ suffix.2
      (suffix.1, events)
  | _, [] => (done, [])

/-- A complete trace: pair of final values and pedagogical events. -/
def evaluate {α : Type} (A : Algebra α) (showValue : α → String)
    (graph : Graph α) (original : Graph Nat) : List α × List Event :=
  evaluateFrom A showValue [] 0 graph original

/-- Printer for infinite or finite shortest-path costs. -/
def showShortest : Option Nat → String
  | none => "INF"
  | some n => toString n

/-- Printer for natural-number path counts. -/
def showPaths (n : Nat) : String := toString n

/-- Printer for cost spectra; duplicates are visible as separate entries. -/
def showSpectrum (xs : List Nat) : String :=
  "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

end GraphFold.Trace
