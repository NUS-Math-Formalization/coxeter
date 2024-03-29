import Mathlib.Data.List.Duplicate
import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.MLList.DepthFirst

import Coxeter.CoxeterMatrix

abbrev S' := Fin 3

def m : Matrix (Fin 3) (Fin 3) ℕ :=
  Matrix.of fun i j => match i, j with
  | 0, 0 => 1
  | 0, 1 => 5
  | 0, 2 => 2
  | 1, 0 => 5
  | 1, 1 => 1
  | 1, 2 => 3
  | 2, 0 => 2
  | 2, 1 => 3
  | 2, 2 => 1

instance : CoxeterMatrix m where
  symmetric := fun i j => match i, j with
  | 0, 1 => by rfl
  | 1, 0 => by rfl
  | 0, 2 => by rfl
  | 2, 0 => by rfl
  | 1, 2 => by rfl
  | 2, 1 => by rfl
  | 2, 2 => by rfl
  | 1, 1 => by rfl
  | 0, 0 => by rfl
  oneIff := by sorry


inductive S : Type :=
  | a : S
  | b : S
  | c : S
  deriving Repr

#eval S.a

instance beqs : BEq S where
  beq := fun x y => match x, y with
  | S.a, S.a => true
  | S.b, S.b => true
  | S.c, S.c => true
  | _, _ => false

instance HashableS : Hashable S where
  hash s := match s with
  | S.a => 1
  | S.b => 2
  | S.c => 3

-- instance : LawfulBEq S where
--   eq_of_beq :=
--   fun x y => match x, y with
--   | S.a, S.a => isTrue rfl
--   | S.b, S.b => isTrue rfl
--   | S.c, S.c => isTrue rfl
--   | u, v => sorry

instance : Inhabited S where
  default := S.a

structure BraidRelation where
  s1 : S
  s2 : S
  m12 : Nat

-- Primitive way to define a Coxeter System
def br12 : BraidRelation := { s1 := S.a, s2 := S.b, m12 := 5 }
def br13 : BraidRelation := { s1 := S.a, s2 := S.c, m12 := 2 }
def br23 : BraidRelation := { s1 := S.b, s2 := S.c, m12 := 3 }
def br21 : BraidRelation := { s1 := S.b, s2 := S.a, m12 := 5 }
def br31 : BraidRelation := { s1 := S.c, s2 := S.a, m12 := 2 }
def br32 : BraidRelation := { s1 := S.c, s2 := S.b, m12 := 3 }


structure Pattern where
  pattern1 : List S'
  pattern2 : List S'


def brs : List BraidRelation := [br12, br23, br13, br21, br31, br32]


open S

def w : List S := [a, b, c, c, b, a, b, a, b, a]
def w' : List S' := [0, 1, 2, 2, 1, 0, 1, 0, 1, 0]
def w_ttt : List S := [a, a, a, a, a, a, a, a, a, a]

def nil_move : List S → List S :=
  fun l => match l with
  | [] => []
  | [x] => [x]
  | x :: y :: xs =>
    match x == y with
    | true => nil_move xs
    | false => x :: nil_move (y :: xs)

def nil_move_Nth (s : S) (w : List S) (n : Nat) : List S :=
  match n with
  | 0 => nil_move w
  | n + 1 => match w with
    | [] => []
    | x :: xs =>
      match nil_move_Nth s xs n with
      | [] => [x]
      | y :: ys =>
        match x == y with
        | true => ys
        | false => x :: y :: ys


def pattern (s1 : S) (s2 : S) (m12 : Nat) : S × List S × List S :=
  match m12 with
  | 0 => (s1, [], [])
  | 1 => (s2, [s1], [s2])
  | n + 1 =>
    let (s, p1, p2) := pattern s1 s2 n
    match s == s1 with
    | true => (s2, s1 :: p1, s2 :: p2)
    | false => (s1, s2 :: p1, s1 :: p2)

def braid_move_aux (pattern1 : List S) (pattern2 : List S) (pattern_length : Nat) : List S → List S :=
  fun l => match l with
  | [] => []
  | [x] => [x]
  | x :: xs =>
    match l.take pattern_length == pattern1 with
    | true => pattern2 ++ l.drop pattern_length
    | false => x :: braid_move_aux pattern1 pattern2 pattern_length xs


def braid_move (br : BraidRelation) : List S → List S :=
  fun l =>
    let (_, p1, p2) := pattern br.s1 br.s2 br.m12
    braid_move_aux p1 p2 p1.length l

def braid_move_Nth (br : BraidRelation) (w : List S) (n : Nat) : List S :=
  match n with
  | 0 => braid_move br w
  | n + 1 => match w with
    | [] => []
    | x :: xs =>
      let p1 := (pattern br.s1 br.s2 br.m12).2.1
      match w.take p1.length == p1 with
      | true => x :: (braid_move_Nth br xs n)
      | false => x :: (braid_move_Nth br xs (n+1))


def nil_move_rec (w : List S) : List S :=
  if (nil_move w).length < w.length then nil_move_rec (nil_move w) else w
  termination_by w.length

#eval nil_move_rec w

def pattern_any (gens : List S) (brl : List BraidRelation) : List (List S × List S) :=
  gens.map (fun s => ([s, s], [])) ++
  brl.map (fun br => (pattern br.s1 br.s2 br.m12).2)

def move_aux (pattern : List S × List S) (w : List S) : List S :=
  match w with
  | [] => []
  | [x] => [x]
  | wh :: wt =>
    match w.take pattern.1.length == pattern.1 with
    | true => pattern.2 ++ w.drop pattern.1.length
    | false => wh :: move_aux pattern wt

def move_Nth (pattern : List S × List S) (w : List S) (n : Nat) : List S :=
    match n with
    | 0 => move_aux pattern w
    | n_pos + 1 => match w with
      | [] => []
      | x :: xs =>
        match w.take pattern.1.length == pattern.1 with
        | true => x :: (move_Nth pattern xs n_pos)
        | false => x :: (move_Nth pattern xs (n_pos+1))

-- return a list of removing all possible moves of a specific pattern
partial def move_loop_pos_aux (pattern : List S × List S) (w : List S) (n : Nat) : List (List S) :=
  let w' := move_Nth pattern w n
  if w' == w then [] else w' :: move_loop_pos_aux pattern w (n+1)

def move_gen_aux (l_pattern : List (List S × List S)) (w : List S) : List (List S) :=
  match l_pattern with
  | [] => []
  | pattern :: l_pattern_t =>
    let l_w := move_loop_pos_aux pattern w 0
    l_w ++ move_gen_aux l_pattern_t w

def nodup' (l : List (List S)) : List (List S) :=
  l.foldr (fun x IH => if ¬ List.elem x IH then x :: IH else IH) []

def move_gen (l_pattern : List (List S × List S)) (w : List S) : List (List S) :=
  let l_w := move_gen_aux l_pattern w
  nodup' l_w


def WD (l_pattern : List (List S × List S)) (w : List S) : List (List S) :=
  @depthFirstRemovingDuplicates' (List S) _ _ (fun x => move_gen l_pattern x) w none


def length_aux (l_pattern : List (List S × List S)) (w : List S) : Nat :=
  (List.map (fun x => x.length) (WD l_pattern w)).minimum.getD 1

#check depthFirstRemovingDuplicates'

def w3 := [c, b, c, a, c, b, a, b, a, c]

#eval @depthFirstRemovingDuplicates' (List S) _ _ (fun x => move_gen (pattern_any [a, b, c] brs) x) w3 none

#eval pattern_any [a, b, c] brs


#eval move_loop_pos_aux (pattern_any [a, b, c] brs)[7] w3 0
#eval move_loop_pos_aux (pattern_any [a, b, c] brs)[0] w_ttt 0

-- #eval @depthFirstRemovingDuplicates' (List S) _ _ (fun x => move_gen (pattern_any [a, b, c] brs) x) w none


#eval braid_move_Nth br23 w3 0
#eval pattern brs[0].s1 brs[0].s2 brs[0].m12
