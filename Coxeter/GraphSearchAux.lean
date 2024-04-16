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

namespace Attempt1

variable [BEq α] [LawfulBEq α]
-- #synth Decidable (1 ∈ [1,3])

def next (g : α → List α) (last : α) (current : Option α) : Option α :=
  match current  with
  | .none => (g last).head?
  | .some a =>
    match (g last).indexOf? a  with
    | .none => .none -- impossible case if our input is legal
    | .some n => (g last).get? (n+1)

partial def nodup_next (g : α → List α) (path : List α) (current : Option α) : Option α :=
  match current, path with
  | .some _, [] => .none -- impossible
  | .some a, z :: _ =>
    match next g z a with
    | .none => .none
    | .some b =>
      if b ∈ path then
        nodup_next g path b
      else
        .some b
  | .none, [] => .none -- impossible
  | .none, z :: _ =>
    match (g z).head? with
    | .none => .none
    | .some b =>
      if b ∈ path then
        nodup_next g path b
      else
        .some b

partial def nodup_g (g : α → List α) (path : List α) (current : Option α): List α :=
  let new := (nodup_next g path current)
  match new with
  | .some b  =>
    b :: nodup_g g path new
  | .none =>
    []

def nodup_g' (g : α → List α) (path : List α) (current : α) : List α := nodup_g g (current :: path) .none

def g₅ (x : Fin 5) : List (Fin 5) :=
  match x with
  | 0 => [1, 2]
  | 1 => [0, 2 , 3]
  | 2 => [0, 1 , 3 , 4]
  | 3 => [1, 2]
  | 4 => [2]

#eval nodup_g' g₅ ([0]: List (Fin 5)) (2)

/- A Depth-first graph search based on List. For the time being, I fail to adapt the nodup version. -/
partial def depthFirstList' (g : List α → α → List α) (path : List α) (start : α) : List (List α) :=
  match g path start with
  | [] => [start :: path]
  | _ =>
    let new_path := start :: path
    new_path :: (List.join $ List.map (depthFirstList' g new_path) (g new_path start))

#eval depthFirstList' (nodup_g' g₅)  ([] : List (Fin 5)) 0

end Attempt1








namespace Attempt2

variable [BEq α] [LawfulBEq α]
-- #synth Decidable (1 ∈ [1,3])

def next (g : α → List α) (last : α) (current : Option α) : Option α :=
  match current  with
  | .none => (g last).head?
  | .some a =>
    match (g last).indexOf? a  with
    | .none => .none -- impossible case if our input is legal
    | .some n => (g last).get? (n+1)

partial def nodup_parallel_next (g : α → List α) (path : List α) (visited : List α) (current : Option α) : Option α := -- path and visited will not be changed in this function
  match current, path with
  | .some _, [] => .none -- impossible
  | .some a, z :: _ =>
    match next g z a with
    | .none => .none
    | .some b =>
      if b ∈ visited then
        nodup_parallel_next g path visited b
      else
        .some b
  | .none, [] => .none -- impossible
  | .none, z :: _ =>
    match (g z).head? with
    | .none => .none
    | .some b =>
      if b ∈ visited then
        nodup_parallel_next g path visited b
      else
        .some b

partial def nodup_next (g : α → List α) (path : List α) (visited : List α) (current : α) : Option α := -- visited and path does not include current, visited should contain path
  match g current with
  | [] => nodup_parallel_next g path visited current
  | a :: _ =>
    if a ∈ visited then
      nodup_parallel_next g (current :: path) (current :: visited) a
    else
      a

def g₅ (x : Fin 5) : List (Fin 5) :=
  match x with
  | 0 => [1, 2]
  | 1 => [0, 2 , 3]
  | 2 => [0, 1 , 3 , 4]
  | 3 => [1, 2]
  | 4 => [2]

#eval nodup_next g₅ (path := [0,1]) (visited := [0,1, 3, 4]) (2)

/- A Depth-first graph search based on List. For the time being, I fail to adapt the nodup version. -/
partial def depthFirstList' (g : List α → List α → α → List α) (path : List α) (visited : List α) (current : α) : (List α) :=
  match path, nodup_next (g visited path) path visited current with
  | [], .none => current :: depthFirstList'
  | [], .some a => sorry
  | z :: past_path, .none => sorry
  | z :: past_path, .some a => sorry


#eval depthFirstList' (nodup_g' g₅)  ([] : List (Fin 5)) 0


end Attempt2
