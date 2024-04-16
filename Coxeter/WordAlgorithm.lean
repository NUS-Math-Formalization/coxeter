import Mathlib.Data.List.Duplicate
import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.MLList.DepthFirst

import Coxeter.CoxeterMatrix.CoxeterMatrix
import Coxeter.GraphSearchAux
import Coxeter.Aux_

abbrev N := 3

/- Consider only finite case -/
abbrev S := Fin N


/- Proof that Given matrix is a Coxeter Matrix (Should be simpler) -/
-- instance : CoxeterMatrix m where
--   symmetric := by
--     intro i j; fin_cases i;
--     fin_cases j; simp[m]; simp[m]; simp[m]
--     fin_cases j; simp[m]; simp[m]; simp[m]
--     fin_cases j; simp[m]; simp[m]; simp[m]
--   oneIff := by
--     intro i j; constructor;
--     . contrapose!; intro h; fin_cases i;
--       fin_cases j; simp [m]; contradiction; simp [m]; simp [m]; simp [m];
--       fin_cases j; simp [m]; contradiction; simp [m]; simp [m];
--       fin_cases j; simp [m]; simp [m]; contradiction;
--     . intro h; fin_cases i;
--       fin_cases j; simp [m]; contradiction; contradiction;
--       fin_cases j; simp [m]; contradiction; simp [m]; contradiction;
--       fin_cases j; simp [m]; contradiction; contradiction; simp [m]

-- abbrev G := CoxeterMatrix.toGroup m
-- abbrev S' := CoxeterMatrix.SimpleRefl m

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

def nil_move : List S → List S :=
  fun l => match l with
  | [] => []
  | [x] => [x]
  | x :: y :: xs =>
    match x == y with
    | true => nil_move xs
    | false => x :: nil_move (y :: xs)

def pattern_gen_aux (m : Matrix S S ℕ) (n : ℕ)(i j : ℕ) : List Pattern :=
  match i, j with
  | 0, 0 =>  nil_pattern 0 :: []
  | 0, s + 1 =>
    braid_pattern m 0 (s+1) :: pattern_gen_aux m n 0 s
  | t + 1, 0 =>
    braid_pattern m (t+1) 0 :: pattern_gen_aux m n t n
  | s + 1, t + 1 =>
    if s = t then
      nil_pattern (s+1) :: pattern_gen_aux m n (s+1) t
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
partial def move_loop_pos_aux (pattern : Pattern) (n : Nat) (w : List S) : List (List S × Pattern × Nat) :=
  let w' := move_Nth pattern w n
  if w' = w then [] else (w', pattern, n) :: move_loop_pos_aux pattern (n+1) w

def move_gen_aux (l_pattern : List Pattern) (w : List S) : List (List S × Pattern × Nat) :=
  match l_pattern with
  | [] => []
  | pattern :: l_pattern_t =>
    let l_w := move_loop_pos_aux pattern 0 w
    l_w ++ move_gen_aux l_pattern_t w

/- Graph generating function -/
def move_gen (m : Matrix S S ℕ) (w : List S) : List (List S) :=
  let l_pattern := pattern_gen m
  let l_w := move_gen_aux l_pattern w
  List.eraseDup $
  List.map Prod.fst l_w

def move_gen' (m : Matrix S S ℕ) (w : List S) : List (List S × Pattern × Nat) :=
  let l_pattern := pattern_gen m
  let l_w := move_gen_aux l_pattern w
  --List.pwFilter (fun x y => x.1 = y.1)
  l_w


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

def NF (m : Matrix S S ℕ) (w : List S) : List S :=
  let min := List.minimum (RD m w)
  match min with
  | none => w
  | some x => x

/- Get reduced word arithmatically -/
def reduced_word (m : Matrix S S ℕ) (w : List S) : List S :=
  (RD m w).head!

def group_eq (m : Matrix S S ℕ) (w1 w2 : List S) : Bool :=
  List.inter (RD m w1) (RD m w2) ≠ []

def getEdge {α β : Type} [DecidableEq α] (g : α → List (α × β)) (vl : List α) : List (α × α × β) :=
  List.pwFilter (fun e1 e2 => True)
    (List.join $ List.map (fun v : α => (List.map (fun e : α × β => (v, e)) (g v))) vl)

def Pattern.toString (p : Pattern) : String :=
  "[" ++ p.1.toString ++ ", " ++ p.2.toString ++ "]"

instance : ToString (List S × List S × Pattern × ℕ) :=
  ⟨fun x => "{"
    ++ "'v1': " ++ x.1.toString ++ ", "
    ++ "'v2': " ++ x.2.1.toString ++ ", "
    ++ "'e': " ++ x.2.2.1.toString ++ "}"⟩
-- theorem word (m : Matrix S S ℕ) : ℓ((List.map (CoxeterMatrix.toSimpleRefl m) w).gprod) = length_aux m w := by
--   simp[length_aux, WD, depthFirstRemovingDuplicates', depthFirstRemovingDuplicates]

end tits_solution

section GroupComputation

def mul (m : Matrix S S ℕ) (w u : List S) : List S := NF m (w ++ u)
/- Convenient for reflection computing -/
def mul' (m : Matrix S S ℕ) (w u v : List S) : List S := NF m (w ++ u ++ v)
def inv (m : Matrix S S ℕ) (w : List S) : List S := NF m w.reverse

def group_gen_fun (m : Matrix S S ℕ) (gen : List S) (w : List S) : (List (List S)) :=
  List.map (fun s => mul m [s] w) gen

def refl_gen_fun (m : Matrix S S ℕ) (gen : List S) (w : List S) : List (List S) :=
  List.map (fun s => mul' m [s] w [s]) gen

/- Enumerate all group elements by Graph search algorithm -/
def elements (m : Matrix S S ℕ) (gen : List S) : List (List S) :=
  depthFirstRemovingDuplicates' (group_gen_fun m gen) []

/- Enumerate all reflections by Graph search algorithm -/
def reflections (m : Matrix S S ℕ) (gen : List S) : List (List S) :=
  --List.eraseDup $
  depthFirstRemovingDuplicates' (refl_gen_fun m gen) [0]


end GroupComputation


section BruhatOrder



end BruhatOrder


#check depthFirstRemovingDuplicates'

/- Specifying a matrix [H₃] for example -/
def m := ![![1, 5, 2],
            ![5, 1, 3],
            ![2, 3, 1]]
def m0 := ![![1, 3, 2, 2, 2],
           ![3, 1, 3, 2, 2],
           ![2, 3, 1, 3, 2],
           ![2, 2, 3, 1, 3],
           ![2, 2, 2, 3, 1]]

def w3 := [2, 1, 2, 0, 2, 1, 0, 1, 0, 2]
def w31 := [0, 2, 1, 0, 1, 2]
def w4 := [0, 1, 2, 0, 2, 0]


#eval elements m [0,1,2]
#eval [2,3,4] > [2,2,4]
#eval reflections m [0,1,2]
#eval (graph.getEdge (move_gen' m) (WD m w3)).toString
#eval pattern_gen m
#eval move_loop_pos_aux (pattern_gen m)[0] 0 [1,2,2,2,0]
#eval move_gen m [1, 2, 2, 1, 0, 2, 1, 0, 1, 2]
#eval (WD m w4)
#eval NF m w4
#eval inv m w4
#eval length_aux m w3
#eval RD m w3
#eval is_reduced m w3
#eval group_eq m w3 w31
#eval group_eq m w3 w4
