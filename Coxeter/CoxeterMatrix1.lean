import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.RingTheory.RootsOfUnity.Basic
import Coxeter.CoxeterSystem
import Coxeter.OrderTwoGen

open BigOperators

--open Classical
<<<<<<< HEAD
-- test222224444
=======

--test 12
-- test56
>>>>>>> origin/master

section
variable {α : Type*} [DecidableEq α]

variable (m : Matrix α  α ℕ)

class CoxeterMatrix : Prop where
  symmetric : ∀ (a b : α ), m a b = m b a
  oneIff: ∀  (a b : α), m a b = 1 ↔ a=b
end

open Classical

namespace CoxeterMatrix
variable {α} (m : Matrix α α ℕ) [hm: CoxeterMatrix m]

--variable {m' : Matrix α α ℕ} [hm': CoxeterMatrix m']


lemma one_iff :∀ (a b:α), m a b = 1 ↔ a=b := hm.oneIff

lemma diagonal_one {s : α} : m s s = 1 := by rw [hm.oneIff]

lemma off_diagonal_ne_one {s : α} : s ≠ t → m s t ≠ 1 := by simp [hm.oneIff]


local notation  "F" => FreeGroup α

@[simp] def toRelation (s t : α) (n : ℕ ) : F := (FreeGroup.of s * FreeGroup.of t)^n

@[simp] def toRelation'  (s : α × α ) : F :=toRelation s.1 s.2 (m s.1 s.2)

def toRelationSet : (Set F) := Set.range <| toRelation' m

def toGroup := PresentedGroup <| toRelationSet m

local notation "N" => Subgroup.normalClosure (toRelationSet m)
local notation "G" => toGroup m

instance : Group <| toGroup m := QuotientGroup.Quotient.group _

def of (x : α) : G := QuotientGroup.mk' N (FreeGroup.of x)


-- The set of simple reflections
@[simp]
abbrev SimpleRefl := Set.range (of m)


local notation "S" => (SimpleRefl m)

@[simp]
abbrev Refl : Set G := Set.range <| fun ((g, s) : G × S) => g * s * g⁻¹

local notation "T" => (Refl m)



@[simp]
lemma SimpleRefl_subset_Refl : ∀ {g : G}, g ∈ S → g ∈ T := by
  rintro g ⟨s, hs⟩
  use ⟨1, ⟨g, by rw [Set.mem_range]; use s⟩⟩
  simp

@[simp]
def toSimpleRefl (a : α) : SimpleRefl m := ⟨of m a, by simp⟩

instance coe_group: Coe α (toGroup m) where
  coe := of m

instance coe_simple_refl: Coe α (SimpleRefl m) where
  coe := toSimpleRefl m

def liftHom_aux {A:Type*} [Group A] (f : α → A)  (h : ∀ (s t: α ), (f s * f t)^(m s t) = 1) : ∀ r ∈ toRelationSet m, (FreeGroup.lift f) r = 1 := by
  intro r hr
  obtain ⟨⟨s,t⟩,hst⟩ := hr
  simp only [toRelation', toRelation] at hst
  simp only [<- hst, map_pow, map_mul, FreeGroup.lift.of, h]

-- Lift map from α→ A to Coxeter group → A
def lift {A : Type _} [Group A] (f : α → A)  (h : ∀ (s t: α ), (f s * f t)^(m s t) = 1) : G →* A := PresentedGroup.toGroup <| liftHom_aux m f h


lemma lift.of {A : Type _} [Group A] (f : α → A) (h : ∀ (s t: α ), (f s * f t)^(m s t) = 1) (s : α) : lift m f h (of m s) = f s := by
  apply PresentedGroup.toGroup.of


abbrev μ₂ := rootsOfUnity 2 ℤ
@[simp]
abbrev μ₂.gen :μ₂ := ⟨-1, by norm_cast⟩

lemma μ₂.gen_ne_one : μ₂.gen ≠ 1 := by rw [μ₂.gen]; norm_cast

lemma μ₂.not_iff_not : ∀ (z : μ₂), ¬ z = 1 ↔ z = μ₂.gen := by sorry

lemma μ₂.not_iff_not' : ∀ (z : μ₂), ¬ z = μ₂.gen ↔ z = 1 := by
  intro z
  constructor
  . contrapose; rw [not_not]; exact (μ₂.not_iff_not z).mp
  contrapose; rw [not_not]; exact (μ₂.not_iff_not z).mpr

lemma μ₂.gen_square : μ₂.gen * μ₂.gen = 1 := by rw [μ₂.gen]; norm_cast

lemma μ₂.gen_inv : μ₂.gen⁻¹ = μ₂.gen := by rw [μ₂.gen]; norm_cast

lemma μ₂.gen_order_two : orderOf μ₂.gen = 2 := by sorry

lemma μ₂.even_pow_iff_eq_one {n : ℕ} : μ₂.gen ^ n = 1 ↔ Even n := by
  rw [even_iff_two_dvd, ← μ₂.gen_order_two, orderOf_dvd_iff_pow_eq_one]

lemma μ₂.odd_pow_iff_eq_gen {n : ℕ} : μ₂.gen ^ n = μ₂.gen ↔ Odd n := by
  rw [Nat.odd_iff_not_even, ← μ₂.even_pow_iff_eq_one, not_iff_not]

@[simp]
def epsilon : G →* μ₂  := lift m (fun _=> μ₂.gen) (by intro s t; ext;simp)

lemma epsilon_of (s : α) : epsilon m (of m s) = μ₂.gen := by
  simp only [epsilon, lift.of m]



--@[simp] lemma of_mul (x y: α) : (of m x) * (of m y) =
--QuotientGroup.mk' _  (FreeGroup.mk [(x,tt), (y,tt)]):= by rw [of];


-- DLevel 1
@[simp]
lemma of_relation (s t: α) : ((of m s) * (of m t))^(m s t) = 1  :=  by
  set M := toRelationSet m
  set k := ((FreeGroup.of s) * (FreeGroup.of t))^(m s t)
  have kM : (k ∈ M) := by exact Exists.intro (s, t) rfl
  have MN : (M ⊆ N) := by exact Subgroup.subset_normalClosure
  have kN : (k ∈ N) := by exact MN kM
  rw [of, of]
  have : (((QuotientGroup.mk' N) (FreeGroup.of s) * (QuotientGroup.mk' N) (FreeGroup.of t)) ^ (m s t)
    = (QuotientGroup.mk' N) ((FreeGroup.of (s) * FreeGroup.of (t)) ^ (m s t))) := by rfl
  rw [this]
  apply (QuotientGroup.eq_one_iff k).2
  exact kN

-- DLevel 1
@[simp]
lemma of_square_eq_one {s : α} : (of m s) * (of m s) = 1  :=  by
  have : m s s = 1 := diagonal_one m
  rw [← pow_one ((of m s) * (of m s)), ←this]
  apply of_relation m s s

@[simp]
lemma of_square_eq_one' : s ∈ SimpleRefl m → s * s = 1 := by
  simp only [SimpleRefl, Set.mem_range, forall_exists_index]
  intro x h
  simp_all only [← h, of_square_eq_one]

lemma of_inv_eq_of {x : α} :  (of m x)⁻¹ =  of m x  :=
  inv_eq_of_mul_eq_one_left (@of_square_eq_one α m hm x)

def getS (L: List (α × Bool)) := L.map (fun (a, b) => toSimpleRefl m a)

-- DLevel 1
lemma toGroup_expression : ∀ x :G, ∃ L : List S,  x = L.gprod := by
  intro x
  have k : ∃ y : F, QuotientGroup.mk y = x := by exact Quot.exists_rep x
  rcases k with ⟨y, rep⟩
  set a := getS m y.toWord
  use a
  have : x = a.gprod := by sorry
  apply this



lemma generator_ne_one  (s: α) : of m s ≠ 1 :=  by
  intro h
  have h1 :epsilon m (of m s) = 1 := by rw [h];simp
  have h2 :epsilon m (of m s) = μ₂.gen := by rw [epsilon_of]
  rw [h2] at h1; exact μ₂.gen_ne_one h1


lemma generator_ne_one'  {x: G} : x ∈ S → x ≠ 1 :=  by
  rintro ⟨s, hs⟩
  rw [← hs]
  exact generator_ne_one m s

lemma order_two :  ∀ (x: G) , x ∈ S →  x * x = (1 : G) ∧ x ≠ 1 :=  by
  rintro x ⟨s, hs⟩
  rw [← hs]
  exact ⟨of_square_eq_one m, generator_ne_one m s⟩


instance ofOrderTwoGen : OrderTwoGen (SimpleRefl m)  where
  order_two := order_two m
  expression := toGroup_expression m

end CoxeterMatrix


namespace CoxeterMatrix
open OrderTwoGen

variable {α} {m : Matrix α α ℕ} [hm: CoxeterMatrix m]

local notation "G" => toGroup m
local notation "S" => SimpleRefl m
local notation "T" => Refl m

-- DLevel 1
-- Moving to OrderTwoGen?
@[simp]
lemma Refl.simplify {t : G} : t ∈ T ↔ ∃ g : G, ∃ s : S, g * s * g⁻¹ = t := by
  constructor
  · intro h1
    dsimp at h1
    have h3 : ∃ x : G × S, x.1 * ↑x.2 * x.1⁻¹ = t := by
      apply Set.mem_range.mpr h1
    rcases h3 with ⟨x, h4⟩
    use x.1, x.2
  · intro h2
    dsimp
    apply Set.mem_range.mpr
    rcases h2 with ⟨g, s, h3⟩
    use (g, s)

@[simp]
lemma Refl.conjugate_closed {s : α} {t : T} : (s : G) * t * (s : G)⁻¹ ∈ T := by
  dsimp
  apply Set.mem_range.mpr
  have h1 : ∃ g1 : G, ∃ s1 : S, g1 * (s1 : G) * g1⁻¹ = (t : G) := by
    apply Refl.simplify.mp
    apply Subtype.mem
  rcases h1 with ⟨g1, s1, h2⟩
  have h3 : (of m s * g1) * ↑s1 * (of m s * g1)⁻¹ = of m s * ↑t * (of m s)⁻¹ := by
    rw [← h2]
    group
  use (of m s * g1, s1)

-- DLevel 1
@[simp]
lemma Refl.conjugate_closed' [CoxeterMatrix m ] {s : α} {t : T} : (s : G) * t * (s : G) ∈ T := by
  dsimp
  have h4 : (of m s)⁻¹ = of m s := by
    apply of_inv_eq_of
  nth_rw 2 [← h4]
  apply Set.mem_range.mpr
  have h1 : ∃ g1 : G, ∃ s1 : S, g1 * (s1 : G) * g1⁻¹ = (t : G) := by
    apply Refl.simplify.mp
    apply Subtype.mem
  rcases h1 with ⟨g1, s1, h2⟩
  have h3 : (of m s* g1) * ↑s1 * (of m s * g1)⁻¹ = of m s * ↑t * (of m s)⁻¹ := by
    rw [← h2]
    group
  use (of m s * g1, s1)

@[simp]
lemma Refl.conjugate_closed_G {g : G} {t : T} : g * t * g⁻¹ ∈ T := by
  dsimp
  apply Set.mem_range.mpr
  have h1 : ∃ g1 : G, ∃ s1 : S, g1 * (s1 : G) * g1⁻¹ = (t : G) := by
    apply Refl.simplify.mp
    apply Subtype.mem
  rcases h1 with ⟨g1, s1, h2⟩
  have h3 : (g * g1) * ↑s1 * (g * g1)⁻¹ = g * ↑t * g⁻¹ := by
    rw [← h2]
    group
  use (g * g1, s1)


lemma sq_refl_eq_one [CoxeterMatrix m] {t : T} : (t : G) ^ 2 = 1 := by
  rcases t with ⟨t, ⟨g, s⟩, feqt⟩
  simp only [feqt]
  have gsgeqt : g * s * g⁻¹ = t := feqt
  rw [← gsgeqt, sq]
  group
  have hs : s * s = (1 : G) :=
    of_square_eq_one' m (Subtype.mem s)
  rw [mul_assoc g s, hs]
  group

lemma inv_refl_eq_self [CoxeterMatrix m] {t : T} : (t : G)⁻¹ = t := by
  rcases t with ⟨t, ⟨g, s⟩, feqt⟩
  simp only [feqt]
  have gsgeqt : g * s * g⁻¹ = t := feqt
  sorry

local notation : max "ℓ(" g ")" => (OrderTwoGen.length S g)

-- DLevel 1
lemma epsilon_length  {g : G} : epsilon m g = (μ₂.gen)^(ℓ(g)) := by
  sorry


-- DLevel 1
lemma length_smul_neq {g : G} {s:S} : ℓ(g) ≠ ℓ(s*g) := by
  sorry

-- DLevel 1
lemma length_muls_neq {g : G} {s:S} : ℓ(g) ≠ ℓ(g*s) := by
  sorry

-- DLevel 1
lemma length_diff_one  {g : G} {s:S} : ℓ(s*g) = ℓ(g) + 1  ∨ ℓ(g) = ℓ(s*g) + 1 := by
  by_cases h : ℓ(s*g) > ℓ(g)
  . left
    have : ℓ(s*g) ≤ ℓ(g) + 1:= length_smul_le_length_add_one
    linarith
  . right
    have : ℓ(g) ≤ ℓ(s*g) + 1 := sorry--length_smul_le_length_add_one
    have : ℓ(g) ≠ ℓ(s*g) := by sorry
    sorry

-- DLevel 1
lemma length_smul_lt_of_le {g : G} {s : S} (hlen : ℓ(s * g) ≤ ℓ(g)) : ℓ(s * g) < ℓ(g):= by
  sorry

-- In the following section, we prove the strong exchange property
section ReflRepresentation

variable {β:Type*}
-- For a list L := [b₀, b₁, b₂, ..., bₙ], we define the Palindrome of L as [b₀, b₁, b₂, ..., bₙ, bₙ₋₁, ..., b₁, b₀]
@[simp]
abbrev toPalindrome   (L : List β) : List β := L ++ L.reverse.tail

-- Note that 0-1 = 0
lemma toPalindrome_length {L : List β} : (toPalindrome L).length = 2 * L.length - 1 := by
  simp only [toPalindrome, List.length_append, List.length_reverse, List.length_tail]
  by_cases h: L.length=0
  . simp [h]
  . rw [<-Nat.add_sub_assoc]
    zify; ring_nf
    apply Nat.pos_of_ne_zero h

lemma reverseList_nonEmpty {L : List S} (hL : L ≠ []) : L.reverse ≠ [] := by
  apply (List.length_pos).1
  rw [List.length_reverse]
  apply (List.length_pos).2
  exact hL

lemma rtr_append {L : List S} (hL : L ≠ []) :
  L.reverse.tail.reverse ++ [L.getLast hL] = L := by
  set n := L.length
  have : n > 0 := by exact List.length_pos.mpr hL
  have : L.reverse.tail.reverse = L.dropLast := by
    induction L with
    | nil => contradiction
    | cons hd tail ih =>
      by_cases k : tail = []
      . rw [k]
        simp
      . push_neg at k
        have htd : (hd :: tail).dropLast = hd :: (tail.dropLast) := by
          exact List.dropLast_cons_of_ne_nil k
        rw [htd]
        have trht : (tail.reverse ++ [hd]).tail = (tail.reverse.tail) ++ [hd] := by
          apply List.tail_append_of_ne_nil
          apply reverseList_nonEmpty k
        have : (hd :: tail).reverse.tail = (hd :: tail).dropLast.reverse := by
          rw [htd]
          simp
          rw [trht]
          apply (List.append_left_inj [hd]).2
          apply (List.reverse_eq_iff).1
          apply ih k
          exact List.length_pos.2 k
        rw [this, List.reverse_reverse, htd]
  rw [this]
  exact List.dropLast_append_getLast hL

-- DLevel 2
lemma toPalindrome_in_Refl [CoxeterMatrix m] {L:List S} (hL : L ≠ []) : (toPalindrome L:G) ∈ T := by
  apply Refl.simplify.mpr
  use L.reverse.tail.reverse.gprod, (L.getLast hL)
  rw [← gprod_reverse, List.reverse_reverse]
  have : L.reverse.tail.reverse.gprod * (L.getLast hL) = L.gprod := by
    have : L = L.reverse.tail.reverse ++ [L.getLast hL] := by
      apply Eq.symm
      apply rtr_append hL
    nth_rw 3 [this]
    apply Eq.symm
    apply gprod_append_singleton
  rw [this]
  dsimp
  rw [gprod_append]

-- Our index starts from 0
def toPalindrome_i  (L : List S) (i : ℕ) := toPalindrome (L.take (i+1))
local notation:210 "t(" L:211 "," i:212 ")" => toPalindrome_i L i

--def toPalindromeList (L : List S) : Set (List S):= List.image (toPalindrome_i L)'' Set.univ
lemma toPalindrome_i_in_Refl [CoxeterMatrix m] {L : List S} (i : Fin L.length) :
    (toPalindrome_i L i : G) ∈ T := by
  rw [toPalindrome_i]
  have tklen : (L.take (i+1)).length = i + 1 :=
    List.take_le_length L (by linarith [i.prop] : i + 1 ≤ L.length)
  have tkpos : (L.take (i+1)).length ≠ 0 := by
    linarith
  have h : List.take (i + 1) L ≠ [] := by
    contrapose! tkpos
    exact List.length_eq_zero.mpr tkpos
  exact toPalindrome_in_Refl h

--DLevel 3
lemma mul_Palindrome_i_cancel_i [CoxeterMatrix m] {L : List S} (i : Fin L.length) : (t(L, i):G) * L = (L.removeNth i) := by sorry

-- DLevel 1
lemma removeNth_of_palindrome_prod (L : List S) (n : Fin L.length) :
  (toPalindrome_i L n:G) * L = (L.removeNth n) := by sorry

lemma distinct_toPalindrome_i_of_reduced [CoxeterMatrix m] {L : List S} : reduced_word L →
    (∀ (i j : Fin L.length),  (hij : i ≠ j) → (toPalindrome_i L i) ≠ (toPalindrome_i L j)) := by
  intro rl
  by_contra! eqp
  rcases eqp with ⟨i, j, ⟨inej, eqp⟩⟩
  wlog iltj : i < j generalizing i j
  · have jlei : j ≤ i := by
      push_neg at iltj
      exact iltj
    have ilej : i ≤ j := by
      have njlei : ¬j < i :=
        this j i inej.symm eqp.symm
      push_neg at njlei
      exact njlei
    exact inej (le_antisymm ilej jlei)
  · have h : (toPalindrome_i L i).gprod * (toPalindrome_i L j) = 1 := by
      calc
        _ = (toPalindrome_i L i).gprod * (toPalindrome_i L i).gprod := by
          rw [← eqp]
        _ = 1 := by
          have tirefl := toPalindrome_i_in_Refl i
          set ti : T := ⟨(t(L, i)).gprod, tirefl⟩
          have tisq : (ti.val : G) ^ 2 = 1 := sq_refl_eq_one
          rw [sq] at tisq
          exact tisq
    have lenremNjp : (L.removeNth j).length + 1 = L.length := by
      rw [List.removeNth_length]
    have hi : i < (L.removeNth j).length := by
      rw [List.length_removeNth j.2]; exact Nat.lt_of_lt_of_le iltj (Nat.le_pred_of_lt j.2)
    have h2 : L.gprod = ((L.removeNth j).removeNth i) := by
      calc
        _ = (toPalindrome_i L i).gprod * (toPalindrome_i L j) * L := by
          rw [h]
          group
        _ = (toPalindrome_i L i).gprod * (L.removeNth j) := by
          rw [mul_assoc, removeNth_of_palindrome_prod]
        _ = (toPalindrome_i (L.removeNth j) i).gprod * (L.removeNth j) := by
          repeat rw [toPalindrome_i]
          congr 3
          apply (List.take_of_removeNth L (Nat.add_one_le_iff.mpr iltj)).symm
        _ = ((L.removeNth j).removeNth i) := by
          rw [removeNth_of_palindrome_prod (L.removeNth j) ⟨i.val, hi⟩]
    have h3 : L.length ≤ ((L.removeNth j).removeNth i).length :=
      rl ((L.removeNth j).removeNth i) h2
    have h4 : ((L.removeNth j).removeNth i).length + 2 = L.length := by
      have lenremNip : ((L.removeNth j).removeNth i).length + 1 = (L.removeNth j).length := by
        rw [List.removeNth_length (L.removeNth j) ⟨i.val, hi⟩]
      calc
        _ = ((L.removeNth j).removeNth i).length + 1 + 1 := by ring
        _ = (L.removeNth j).length + 1 := by rw [lenremNip]
        _ = L.length := by rw [lenremNjp]
    linarith [h3, h4]

noncomputable def eta_aux (s : α) (t:T) : μ₂ := if s = t.val then μ₂.gen else 1

noncomputable def eta_aux' (s : S) (t:T) : μ₂ := if s.val = t.val then μ₂.gen else 1

@[simp]
lemma eta_aux_aux'  (s : α ) (t:T) : eta_aux s t = eta_aux' s t := by congr


noncomputable def nn (L : List S) (t : T) : ℕ := List.count (t : G) <| List.map (fun i => (toPalindrome_i L i : G)) (List.range L.length)

-- DLevel 5
-- [BB] (1.15)
-- lemma nn_prod_eta_aux [CoxeterMatrix m] (L: List S) (t:T) : ∏ i:Fin L.length, eta_aux'  (L.nthLe i.1 i.2) ⟨((L.take (i.1+1)).reverse:G) * t * L.take (i.1+1),by sorry⟩ := by sorry

lemma SimpleRefl_Refl_SimpleRefl_in_Refl (s : S) (t : T) : (s : G) * t * (s : G) ∈ T := by
  rcases s with ⟨_, ⟨_, hy⟩⟩
  exact hy.subst (motive := fun x : G ↦ x * t * x ∈ T) Refl.conjugate_closed'

lemma Refl_palindrome_in_Refl {i : ℕ} (L : List S) (t : T) : ((L.take i).reverse : G) * t * L.take i ∈ T := by
  induction i with
  | zero =>
    rw [List.take, List.reverse_nil]
    rcases t with ⟨_, ht⟩
    rw [gprod_nil]
    group
    exact ht
  | succ j hi =>
    by_cases hj : j < L.length
    · set jf : Fin L.length := ⟨j, hj⟩
      have h : ((L.take (Nat.succ j)).reverse : G) * t * L.take (Nat.succ j) =
          L.get jf * (((L.take j).reverse : G) * t * L.take j) * L.get jf := by
        rw [List.take_succ, List.get?_eq_get hj]
        simp only [Option.toList]
        rw [List.reverse_append, List.reverse_singleton, gprod_append, gprod_append, gprod_singleton]
        group
      rw [h]
      exact SimpleRefl_Refl_SimpleRefl_in_Refl (L.get jf) ⟨_, hi⟩
    · push_neg at hj
      have h : ((L.take (Nat.succ j)).reverse : G) * t * L.take (Nat.succ j) =
          ((L.take j).reverse : G) * t * L.take j := by
        rw [List.take_succ, List.get?_eq_none.mpr hj]
        simp only [Option.toList]
        rw [List.append_nil]
      rw [h]
      exact hi

-- DLevel 4 (1.15)
lemma nn_prod_eta_aux [CoxeterMatrix m] (L : List S) (t : T) : μ₂.gen ^ (nn L t) =  ∏ i : Fin L.length,
    eta_aux' (L.get i) ⟨((L.take i.1).reverse : G) * t * L.take i.1, by apply Refl_palindrome_in_Refl⟩ := by
  revert t
  induction L with
  | nil =>
    simp only [nn]
    dsimp
    intro t
    norm_num
  | cons hd tail ih =>
    intro t
    set sts : T := ⟨hd * t * hd, SimpleRefl_Refl_SimpleRefl_in_Refl hd t⟩
    simp only [nn]
    dsimp
    have hzero : 0 < (hd :: tail).length := by
      rw [List.length]
      exact Nat.lt_add_left tail.length (by norm_num)
    have zerof : Fin (hd :: tail).length := ⟨0, hzero⟩
    have h2 (x : Fin (Nat.succ (List.length tail))) (hx : x.1 ≠ 0) : x.1 - 1 < tail.length :=
      have h : 1 ≤ x.1 := Nat.one_le_iff_ne_zero.mpr hx
      --apply lt_sub
      sorry --lt_trans x.prop
    sorry
    /-calc
      _ = μ₂.gen ^ (List.filter (fun i => ((toPalindrome_i (hd :: tail) i) : G) = t) (List.range (Nat.succ tail.length))).length := by
        congr
      _ = μ₂.gen ^ (List.filter (fun i => if i = 0 then (hd : G) = t else ((toPalindrome_i tail (i - 1)) : G) = hd * t * hd) (List.range (Nat.succ tail.length))).length := by
        sorry
      _ = ∏ i : Fin (Nat.succ (List.length tail)), if hi : i.1 = 0 then eta_aux' hd t
          else eta_aux' (tail.get ⟨i.1 - 1, h2 i hi⟩) ⟨(tail.take (i.1 - 1)).reverse * sts * (tail.take (i.1 - 1)), by apply Refl_palindrome_in_Refl⟩ := by
        have h := ih sts
        sorry --rw [List.]
      _ = ∏ i : Fin (Nat.succ (List.length tail)), eta_aux' ((hd :: tail).get i) ⟨((hd :: tail).take i.1).reverse * ↑t * ((hd :: tail).take i.1), by apply Refl_palindrome_in_Refl⟩ := by
        sorry-/

lemma exists_of_nn_ne_zero [CoxeterMatrix m] (L : List S) (t:T) : nn L t > 0 →
  ∃ i:Fin L.length, (toPalindrome_i L i:G) = t := by
  intro h
  unfold nn at h
  sorry


local notation "R" => T × μ₂

namespace ReflRepn
noncomputable def pi_aux (s : α) (r : R) : R :=
  ⟨⟨(s:G) * r.1 * (s:G)⁻¹, Refl.conjugate_closed⟩ , r.2 * eta_aux s r.1⟩

-- DLevel 3
lemma pi_aux_square_identity [CoxeterMatrix m] (s : α) (r : R) : pi_aux s (pi_aux s r) = r := by sorry

noncomputable def pi_aux'  [CoxeterMatrix m] (s:α) : Equiv.Perm R where
  toFun r := pi_aux s r
  invFun r := pi_aux s r
  left_inv := by intro r; simp [pi_aux_square_identity]
  right_inv := by intro r; simp [pi_aux_square_identity]

-- DLevel 5
lemma pi_relation (s t : α) : ((pi_aux' s : Equiv.Perm R ) * (pi_aux' t : Equiv.Perm R)) = 1 := by
  sorry

noncomputable def pi : G →* Equiv.Perm R := lift m (fun s => pi_aux' s) (by simp [pi_relation])

-- DLevel 2
-- Use MonoidHom.ker_eq_bot_iff
lemma pi_inj : Function.Injective (pi : G→ Equiv.Perm R) := by sorry


end ReflRepn

noncomputable def eta (g : G) (t : T) : μ₂ := (ReflRepn.pi g⁻¹ ⟨t, 1⟩).2

-- DLevel 1
lemma eta_lift_eta_aux {s :α} {t : T} : eta_aux s t = eta s t := by sorry


-- DLevel 4
lemma eta_equiv_nn {g:G} {t:T} : ∀ {L : List S}, g = L → eta g t = (μ₂.gen)^(nn L t) := by  sorry

lemma eta_equiv_nn' {L : List S} {t : T} : eta L t = (μ₂.gen) ^ (nn L t) := by sorry

lemma eta_t (t : T) : eta (t : G) t = μ₂.gen := by sorry
  -- rw [eta_lift_eta_aux, eta_aux, if_pos rfl]

lemma pi_eval (g : G) (t : T) (ε : μ₂): ReflRepn.pi g (t, ε) = (⟨(g : G) * t * (g : G)⁻¹, Refl.conjugate_closed_G⟩, ε * eta g⁻¹ t) := by
  sorry


end ReflRepresentation


lemma lt_iff_eta_eq_gen (g : G) (t : T) : ℓ(t * g) < ℓ(g) ↔ eta g t = μ₂.gen := by
  have mpr (g : G) (t : T) : eta g t = μ₂.gen → ℓ(t * g) < ℓ(g) := by
    intro h
    obtain ⟨L, hL⟩ := exists_reduced_word S g
    have h1 : nn L t > 0 := by
      have : (μ₂.gen)^(nn L t) = μ₂.gen := by rw [← eta_equiv_nn']; rw [← hL.right]; assumption
      exact Odd.pos (μ₂.odd_pow_iff_eq_gen.mp this)
    have : ∃ i : Fin L.length, (toPalindrome_i L i:G) = t := exists_of_nn_ne_zero L t h1
    obtain ⟨i, hi⟩ := this;
    rw [← hi, hL.right, removeNth_of_palindrome_prod L i]
    have h2 : (L.removeNth i).length < L.length := by
      rw [List.length_removeNth i.2]
      exact Nat.pred_lt' i.2
    rw [←OrderTwoGen.length_eq_iff.mp hL.left]
    exact lt_of_le_of_lt length_le_list_length h2

  have mp (g : G) (t : T) : ℓ(t * g) < ℓ(g) → eta g t = μ₂.gen := by
    contrapose
    intro h
    rw [μ₂.not_iff_not'] at h
    -- let g_inv_t_g := toRefl' m (g⁻¹ * t * g) t g rfl
    have g_inv_t_g_in_T : g⁻¹ * t * g ∈ T := by nth_rw 2 [← (inv_inv g)]; exact Refl.conjugate_closed_G
    let g_inv_t_g : T := ⟨(g⁻¹ * t * g), g_inv_t_g_in_T⟩
    have eq1 : ReflRepn.pi ((t : G) * g)⁻¹ (t, μ₂.gen) = (⟨(g⁻¹ * t * g), g_inv_t_g_in_T⟩, μ₂.gen * eta ((t : G) * g) t) := by
      rw [pi_eval]
      apply Prod.eq_iff_fst_eq_snd_eq.mpr
      constructor
      . simp only [Refl, SimpleRefl, mul_inv_rev, inv_mul_cancel_right, inv_inv, Subtype.mk.injEq, ←mul_assoc]
      simp only [Subtype.mk.injEq, inv_inv]
    have eq2 : ReflRepn.pi ((t : G) * g)⁻¹ (t, μ₂.gen) = (g_inv_t_g, 1) := by
      rw [mul_inv_rev, map_mul, Equiv.Perm.coe_mul, Function.comp_apply, inv_refl_eq_self]
      calc
        (ReflRepn.pi g⁻¹) ((ReflRepn.pi ↑t) (t, μ₂.gen)) = (ReflRepn.pi g⁻¹) (t, 1) := by
          congr; rw [pi_eval];
          simp only [Refl, SimpleRefl, mul_inv_cancel_right, Prod.mk.injEq, true_and]
          rw [inv_refl_eq_self, eta_t]; exact μ₂.gen_square
        _ = (g_inv_t_g, 1) := by
          rw [pi_eval]
          simp only [Refl, SimpleRefl, inv_inv, one_mul, Prod.mk.injEq, true_and]; exact h;
    have : eta ((t : G) * g) t = μ₂.gen := by
      rw [eq1] at eq2
      have : μ₂.gen * eta ((t : G) * g) t = 1 := (Prod.eq_iff_fst_eq_snd_eq.mp eq2).right
      apply (@mul_left_cancel_iff _ _ _ μ₂.gen).mp
      rw [μ₂.gen_square]; assumption;
    let hh := mpr (t * g) t this
    rw [←mul_assoc, ←pow_two, sq_refl_eq_one, one_mul] at hh
    rw [not_lt]
    exact le_of_lt hh
  exact Iff.intro (mp g t) (mpr g t)



-- DLevel 2
lemma lt_iff_eta_eq_gen' (g : G) (t : T) : ℓ(t * g) ≤ ℓ(g) ↔ eta g t = μ₂.gen := by
  sorry



-- DLevel 4
lemma strong_exchange : ∀ (L : List S) (t : T) , ℓ((t:G) * L) < ℓ(L) →
  ∃ (i : Fin L.length), (t : G) * L = (L.removeNth i) := by
  intro L t h
  have eta_eq_gen : eta L t = μ₂.gen := (lt_iff_eta_eq_gen L t).mp h
  have h1 : nn L t > 0 := by
    have : (μ₂.gen)^(nn L t) = μ₂.gen := by rw [← eta_equiv_nn']; assumption
    exact Odd.pos (μ₂.odd_pow_iff_eq_gen.mp this)
  have : ∃ i : Fin L.length, (toPalindrome_i L i:G) = t := exists_of_nn_ne_zero L t h1
  obtain ⟨i, hi⟩ := this; use i; rw [← hi]
  exact removeNth_of_palindrome_prod L i


lemma exchange: OrderTwoGen.ExchangeProp S:= by
  intro L t _ h2
  obtain ⟨i, hi⟩ := strong_exchange L ⟨t.val, (SimpleRefl_subset_Refl m t.prop)⟩ (length_smul_lt_of_le h2)
  exact ⟨i, hi⟩

-- DLevel 3
instance ReflSet.fintype : Fintype (ReflSet S g) := sorry

-- DLevel 3
lemma length_eq_card_reflset  [OrderTwoGen S] : ℓ(g) = Fintype.card (ReflSet S g) := by sorry

end CoxeterMatrix


namespace CoxeterMatrix
open OrderTwoGen

variable {α : Type*} [DecidableEq α] {m : Matrix α α ℕ} [CoxeterMatrix m]

-- We will covert the lean3 proof to lean4

instance ofCoxeterSystem : CoxeterSystem (SimpleRefl m) where
  order_two := order_two m
  expression := toGroup_expression m
  exchange :=  exchange


instance ofCoxeterGroup : CoxeterGroup  (toGroup m)  where
  S := SimpleRefl m
  order_two := order_two m
  expression := toGroup_expression m
  exchange := exchange

end CoxeterMatrix
