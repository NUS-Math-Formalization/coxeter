--import Mathlib.Init.Control.Combinators

/-!
# Graph search and graph algorithms with edge labeling

This file is a more advanced version of `Std.Data.MLList.Basic` that supports graph search on edge labeling graphs. This functionality make it easier to tackle with computational group theory and automata problems.

-/

--set_option autoImplicit true

partial def depthFirst {α: Type} (g : α → List α) (start : α) : List α :=
  match g start with
  | [] => [start]
  | _ => start :: (List.join $ List.map (depthFirst g) (g start))


partial def depthFirstNoDup {α : Type} [BEq α] (g : α → List α) (start : α) (s : List α) : List α :=
  match g start with
  | [] => [start]
  | _ =>
    let f_nodup := fun a => (g a).filter (fun x => !s.contains x)
    start :: (List.join $ List.map (fun a => depthFirstNoDup g a (s ++ f_nodup a)) (f_nodup start))

partial def depthFirstLabeling {α β : Type} (g : α → List (α × β)) (start : α) : List α × List (α × α × β) :=
  match g start with
  | [] => ([start], [])
  | _ =>
    let v := start :: (List.join $ List.map (fun a => (depthFirstLabeling g a).1) (List.map Prod.fst (g start)))
    let e := List.map (fun l => (start, l)) (g start) ++
      (List.join $ List.map (fun a => (depthFirstLabeling g a).2) (List.map Prod.fst (g start)))
    (v, e)

partial def depthFirstLabelingNoDup {α β : Type} [BEq α] (g : α → List (α × β)) (start : α) (s : List α) : List α × List (α × α × β) :=
  match g start with
  | [] => ([start], [])
  | _ =>
    let f_nodup := fun a => (List.map Prod.fst (g a)).filter (fun x => !s.contains x)
    let v := start :: (List.join $ List.map (fun a => (depthFirstLabelingNoDup g a (s ++ f_nodup a)).1) (f_nodup start))
    let e := List.map (fun l => (start, l)) (g start) ++ (List.join $ List.map (fun a => (depthFirstLabelingNoDup g a (s ++ f_nodup a)).2) (f_nodup start))
    (v, e)

def a1 (a : Fin 3) : List (Fin 3) :=
  match a with
  | 0 => []
  | 1 => [0, 0, 0]
  | 2 => [1, 0]

def a1_labeling (a : Fin 3) : List (Fin 3 × String) :=
  match a with
  | 0 => []
  | 1 => [(0, "move0"), (0, "move1"), (0, "move2")]
  | 2 => [(1, "move1")]

def a1_dup (a : Fin 3) : List (Fin 3) :=
  match a with
  | 0 => [1, 1]
  | 1 => [0, 0, 0]
  | 2 => [1, 0, 0]

def a1_dup_labeling (a : Fin 3) : List (Fin 3 × String) :=
  match a with
  | 0 => [(1, "move1"), (1, "move10")]
  | 1 => [(0, "move01"), (0, "move14"), (0, "move2")]
  | 2 => [(1, "move1"), (0, "move30")]
-- #eval a1 2
#eval depthFirstLabeling a1_labeling 2
#eval depthFirstNoDup a1_dup 2 []
#eval depthFirstLabelingNoDup a1_dup_labeling 2 [2]
-- #eval @depthFirst (Fin 3) a1 2
