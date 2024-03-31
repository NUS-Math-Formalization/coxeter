import Mathlib.Data.List.Duplicate
import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.MLList.DepthFirst

import Coxeter.CoxeterMatrix

abbrev N := 3

/- Consider only finite case -/
abbrev S := Fin N
/- Specifying a matrix [H₃] for example -/
def m := ![![1, 5, 2], ![5, 1, 3], ![2, 3, 1]]

/- Proof that Given matrix is a Coxeter Matrix (Should be simpler) -/
instance : CoxeterMatrix m where
  symmetric := by
    intro i j; fin_cases i;
    fin_cases j; simp[m]; simp[m]; simp[m]
    fin_cases j; simp[m]; simp[m]; simp[m]
    fin_cases j; simp[m]; simp[m]; simp[m]
  oneIff := by
    intro i j; constructor;
    . contrapose!; intro h; fin_cases i;
      fin_cases j; simp [m]; contradiction; simp [m]; simp [m]; simp [m];
      fin_cases j; simp [m]; contradiction; simp [m]; simp [m];
      fin_cases j; simp [m]; simp [m]; contradiction;
    . intro h; fin_cases i;
      fin_cases j; simp [m]; contradiction; contradiction;
      fin_cases j; simp [m]; contradiction; simp [m]; contradiction;
      fin_cases j; simp [m]; contradiction; contradiction; simp [m]

abbrev G := CoxeterMatrix.toGroup m
abbrev S' := CoxeterMatrix.SimpleRefl m

section tits_solution
/- Define a substution pattern (apply for arbituary presentation group) -/
structure Pattern where
  pattern1 : List S
  pattern2 : List S
  deriving Repr

/- Braid move recursion for Coxeter group [αₛₜ] [αₜₛ]-/
def braid_pattern_aux (s1 s2 : S) (m12 : ℕ) : S × Pattern :=
  match m12 with
  | 0 => (s1, Pattern.mk [] [])
  | 1 => (s2, Pattern.mk [s1] [s2])
  | n + 1 =>
    let (s, pattern) := braid_pattern_aux s1 s2 n
    match s == s1 with
    | true => (s2, Pattern.mk (s1 :: pattern.1) (s2 :: pattern.2))
    | false => (s1, Pattern.mk (s2 :: pattern.1) (s1 :: pattern.2))

/- Pattern for braid move -/
def braid_pattern (m : Matrix S S ℕ) (s1 s2 : S) : Pattern :=
  (braid_pattern_aux s2 s1 (m s1 s2)).2

/- Pattern for nil-move-/
def nil_pattern (s : S) : Pattern := Pattern.mk [s, s] []


def pattern_gen_aux (m : Matrix S S ℕ) (n : ℕ)(i j : ℕ) : List Pattern :=
  match i, j with
  | 0, 0 =>  nil_pattern 0 :: []
  | 0, s + 1 =>
    braid_pattern m 0 (s+1) :: pattern_gen_aux m n 0 s
  | t + 1, 0 =>
    braid_pattern m (t+1) 0 :: pattern_gen_aux m n t n
  | s + 1, t + 1 =>
    if s = t then
      nil_pattern s :: pattern_gen_aux m n (s+1) t
    else
      braid_pattern m (s+1) (t+1) :: pattern_gen_aux m n (s+1) t

def pattern_gen (m : Matrix S S ℕ) : List Pattern :=
  pattern_gen_aux m (N-1) (N-1) (N-1)

def move_aux (pattern : Pattern) (w : List S) : List S :=
  match w with
  | [] => []
  | [x] => [x]
  | wh :: wt =>
    match w.take pattern.1.length == pattern.1 with
    | true => pattern.2 ++ w.drop pattern.1.length
    | false => wh :: move_aux pattern wt

/- Apply a substitution to the word (apply to all presentation group) -/
def move_Nth (pattern : Pattern) (w : List S) (n : Nat) : List S :=
    match n with
    | 0 => move_aux pattern w
    | n_pos + 1 => match w with
      | [] => []
      | x :: xs =>
        match w.take pattern.1.length == pattern.1 with
        | true => x :: (move_Nth pattern xs n_pos)
        | false => x :: (move_Nth pattern xs (n_pos+1))

/- Get a list of removing all possible moves of a specific pattern (Sub-loop) -/
partial def move_loop_pos_aux (pattern : Pattern) (w : List S) (n : Nat) : List (List S) :=
  let w' := move_Nth pattern w n
  if w' = w then [] else w' :: move_loop_pos_aux pattern w (n+1)

def move_gen_aux (l_pattern : List Pattern) (w : List S) : List (List S) :=
  match l_pattern with
  | [] => []
  | pattern :: l_pattern_t =>
    let l_w := move_loop_pos_aux pattern w 0
    l_w ++ move_gen_aux l_pattern_t w

/- Graph generating function -/
def move_gen (m : Matrix S S ℕ) (w : List S) : List (List S) :=
  let l_pattern := pattern_gen m
  let l_w := move_gen_aux l_pattern w
  List.eraseDup l_w

/- All possible words resulted by braid-move and nil-move, trigger built-in depthfirst graph search -/
def WD (m : Matrix S S ℕ) (w : List S) : List (List S) :=
  @depthFirstRemovingDuplicates' (List S) _ _ (fun x => move_gen m x) w none



/- A strateforward realization for ℓ function -/
def length_aux (m : Matrix S S ℕ) (w : List S) : Nat :=
  (List.map (fun x => x.length) (WD m w)).minimum.getD 1

def is_reduced (m : Matrix S S ℕ) (w : List S) : Bool :=
  length_aux m w = w.length

def RD (m : Matrix S S ℕ) (w : List S) : List (List S) :=
  let l := length_aux m w
  List.filter (fun x => x.length = l) (WD m w)

/- Get reduced word arithmatically -/
def reduced_word (m : Matrix S S ℕ) (w : List S) : List S :=
  (RD m w).head!

def group_eq (m : Matrix S S ℕ) (w1 w2 : List S) : Bool :=
  List.inter (RD m w1) (RD m w2) ≠ []


-- theorem word (m : Matrix S S ℕ) : ℓ((List.map (CoxeterMatrix.toSimpleRefl m) w).gprod) = length_aux m w := by
--   simp[length_aux, WD, depthFirstRemovingDuplicates', depthFirstRemovingDuplicates]

#check depthFirstRemovingDuplicates'

def w3 := [2, 1, 2, 0, 2, 1, 0, 1, 0, 2]
def w31 := [0, 2, 1, 0, 1, 2]
def w4 := [0, 1, 2, 0, 2, 0]

#eval WD m w3
#eval length_aux m w3
#eval RD m w3
#eval is_reduced m w3
#eval group_eq m w3 w31
#eval group_eq m w3 w4

end tits_solution
