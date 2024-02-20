import Coxeter.Basic

import Mathlib.Data.Set.Card


variable {G : Type _} [Group G] {S :Set G} [orderTwoGen S] [CoxeterSystem G S]

variable (u w :G)

local notation :max "ℓ(" g ")" => (@length G  _ S _ g)

def ltone (u w: G) := ∃ t: T S, w = u * t ∧ ℓ(u) < ℓ(w)

def lt (u w:G):= ∃ L:List G, List.Forall₂ (@ltone G _ S _) (u::L) (L++[w])

def le (u w:G):= u=w ∨ @lt G _ S _ u w

def Bruhat_rel : G → G → Prop := fun u w => ∃ t ∈ T S, u * t = w ∧ ℓ(u) < ℓ(w)

lemma Bruhat_rel_refl : ∀ x : G,  Bruhat_rel x x := by intro x; use 1; exact ⟨sorry,sorry⟩

def Bruhat_le (u w : G) := ∃ L : List G, List.Chain Bruhat_rel u (L ++ [w]) ∨ u = w

def Bruhat_lt (u w : G) := ∃ L : List G, List.Chain Bruhat_rel u (L ++ [w])

instance Bruhat.LE : LE G where
  le := Bruhat_le

instance Bruhat.LT : LT G where
  lt := Bruhat_lt

namespace Bruhat

lemma one_le_all : ∀ w : G, 1 ≤ w :=sorry

lemma lt_mul_generator_iff_length_lt {t : T S} : u < u * t ↔ ℓ(u) < ℓ(u * t) :=sorry

lemma le_of_lt : u < w → u ≤ w := by intro le; rcases le with ⟨L,h⟩; use L; left; assumption

lemma lt_of_ne_of_le : u ≠ w → u ≤ w → u < w := sorry

instance : PartialOrder G where
le := Bruhat_le
lt := Bruhat_lt
le_refl  := fun x => (by use [];simp)
le_trans := fun (x y z:G) => by{
  intros lxy lyz
  dsimp [Bruhat_le] at *
  sorry
}
lt_iff_le_not_le  := sorry
le_antisymm:= fun (x y:G) => sorry

lemma SubwordAux {L L₁ : List S} (red:reduced_word L) (red₁: reduced_word L₁) (sub: List.Sublist L' L) : ∃ (L₂ : List S), reduced_word L₂ ∧ L₁.gprod < L₂.gprod ∧ ℓ(L₂.gprod) = ℓ(L₁.gprod ) + 1 :=by
  sorry

theorem SubwordProp (L: List S) (hred:reduced_word L) (hw: (w:G) = L.gprod) : u ≤ w ↔ ∃ (L': List S), reduced_word L' ∧ List.Sublist L' L ∧ u = L'.gprod where
  mp := by sorry
  mpr := fun
    | .intro w h => by
      sorry

def Icc : Set G := Set.Icc u w

def Iic : Set G := Set.Iic w

lemma Iic_one : Iic (1:G) = {1} := sorry

lemma Icc_is_fin : Set.ncard (Icc u w) ≠ 0 := by
  simp [Icc]
  sorry

lemma Iic_is_fin : Set.ncard (Iic w) ≠ 0 := sorry

noncomputable instance : Fintype (Icc u w) := Set.Finite.fintype $ Set.finite_of_ncard_ne_zero (Icc_is_fin u w)

noncomputable instance : Fintype (Iic w) := Set.Finite.fintype $ Set.finite_of_ncard_ne_zero (Iic_is_fin w)

#check Set.toFinset (Icc u w)

lemma leIffInvle (u w : G) :  u ≤ w ↔ u⁻¹ ≤ w⁻¹ := sorry

theorem ChainProp (u w :G) (hlt: u < w) : ∃ (L: List G) (h:L ≠ [])(n:Fin L.length), u = L.head h∧ w =L.ilast' w ∧ ℓ(L.get n) = ℓ(u) + n:= sorry

def OrderCovering (u w:G) := u < w ∧ ℓ(u) + 1 = ℓ(w)

local notation lhs:65 " ◁  " rhs:65 => (@OrderCovering G  _ S _ _ lhs rhs)

lemma LiftingProp (u w : G) (h:s∈ D_L w) : u ≤ s*w ∧ s*u ≤ w := sorry

instance : IsDirected G (· ≤ ·) where
  directed := by sorry

lemma Bruhat'Congr' (x y :G) (t:T S) (hlt: x < x*t) (hlt: y < (t:G)*y) : x * y < x * t * y :=by
  let t' :=x * t * x⁻¹
  have hc :x*t*y = t'*x*y := by simp
  by_contra hf
  sorry
  -- have hredx := @reduced_word_exist G A _ _ S _ x
  -- have hredy := @reduced_word_exist G A _ _ S _ y
  -- --have hf' := @le_of_not_lt G _ (x * t * y) (x * y) hf
  -- let ⟨L1,hL1⟩ := hredx
  -- let ⟨L2,hL2⟩ := hredy


lemma mul_le_of_lt_of_mul_lt (s:S) (w:G) (h: s*w < w) : x < w → s*w ≤ w:=by {
  intro h1
  if (s*x < x) then {sorry}
  else {sorry}
}
