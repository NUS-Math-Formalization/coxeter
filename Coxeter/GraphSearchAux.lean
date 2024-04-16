--import Mathlib.Init.Control.Combinators
import Mathlib.Data.MLList.DepthFirst
import Std.Data.List.Basic
/-!
# Graph search and graph algorithms with edge labeling

This file is a more advanced version of `Std.Data.MLList.Basic` that supports graph search on edge labeling graphs. This functionality make it easier to tackle with computational group theory and automata problems.

-/

--set_option autoImplicit true


namespace graph

/- A Depth-first graph search based on List. For the time being, I fail to adapt the nodup version. -/
partial def depthFirstList {α: Type} (g : α → List α) (start : α) : List α :=
  match g start with
  | [] => [start]
  | _ => start :: (List.join $ List.map (depthFirstList g) (g start))


-- partial def depthFirstListLabeling {α β : Type} (g : α → List (α × β)) (start : α) : List α × List (α × α × β) :=
--   match g start with
--   | [] => ([start], [])
--   | _ =>
--     let v := start :: (List.join $ List.map (fun a => (depthFirstListLabeling g a).1) (List.map Prod.fst (g start)))
--     let e := List.map (fun l => (start, l)) (g start) ++
--       (List.join $ List.map (fun a => (depthFirstListLabeling g a).2) (List.map Prod.fst (g start)))
--     (v, e)

def getEdge {α β : Type} [DecidableEq α] (g : α → List (α × β)) (vl : List α) : List (α × α × β) :=
  List.pwFilter (fun e1 e2 => ¬ (e1.1 = e2.2.1 ∧ e1.2.1 = e2.1))
    (List.join $ List.map (fun v : α => (List.map (fun e : α × β => (v, e)) (g v))) vl)





end graph
open graph
def a1 (a : Fin 4) : List (Fin 4) :=
  match a with
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [1, 2]

def a1_labeling (a : Fin 3) : List (Fin 3 × String) :=
  match a with
  | 0 => []
  | 1 => [(0, "move0"), (0, "move1"), (0, "move2")]
  | 2 => [(1, "move1")]

def a1_dup (a : Fin 4) : List (Fin 4) :=
  match a with
  | 0 => [3, 1]
  | 1 => [2]
  | 2 => [1, 0]
  | 3 => [1, 0]

def a1_dup_labeling (a : Fin 4) : List (Fin 4 × String) :=
  match a with
  | 0 => [(3, "move9"), (1, "move8")]
  | 1 => [(0, "move5"), (0, "move6"), (0, "move7")]
  | 2 => [(1, "move3"), (0, "move4")]
  | 3 => [(1, "move1"), (0, "move2")]
-- #eval a1 2
-- #eval depthFirstLabeling a1_labeling 2
-- #eval depthFirstLabelingNoDup a1_dup_labeling 3 [3]
-- #eval depthFirst a1 3
