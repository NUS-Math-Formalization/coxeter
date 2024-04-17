import Coxeter.OrderTwoGen
import Coxeter.CoxeterMatrix.Characterization
open OrderTwoGen
section

class CoxeterSystem {G : Type*} [Group G] (S : Set G) extends OrderTwoGen S where
  exchange : ExchangeProp S
  exchange' : ExchangeProp' S := (exchange_iff_exchange' S).1 exchange
  deletion : DeletionProp S := exchange_imp_deletion S exchange

class CoxeterGroup (G:Type*) extends HOrderTwoGenGroup G where
  exchange : OrderTwoGen.ExchangeProp S
  exchange': OrderTwoGen.ExchangeProp' S := (OrderTwoGen.exchange_iff_exchange' S).1 exchange
  deletion: OrderTwoGen.DeletionProp S := OrderTwoGen.exchange_imp_deletion S exchange

end

namespace CoxeterGroup
open HOrderTwoGenGroup

instance SimpleRefl_isCoxeterSystem  {G:Type*} [hG:CoxeterGroup G]: CoxeterSystem (SimpleRefl G) where
  exchange := hG.exchange
  exchange' := hG.exchange'
  deletion := hG.deletion

instance SimpleRefl_isCoxeterSystem'  {G:Type*} [hG:CoxeterGroup G]: CoxeterSystem (hG.S) where
  exchange := hG.exchange
  exchange' := hG.exchange'
  deletion := hG.deletion

instance {G:Type*} [hG:CoxeterGroup G]: HMul hG.S G G where
  hMul := fun s g => s.1 * g

instance {G:Type*} [hG:CoxeterGroup G]: HMul G hG.S G where
  hMul := fun g s => g * s.1

instance {G:Type*} [hG:CoxeterGroup G]: CoeOut hG.S G where
  coe := fun s => s.1

-- The length function defines a metric on the Coxeter group
noncomputable instance metric [CoxeterGroup G]: MetricSpace G := OrderTwoGen.metric <| SimpleRefl G

def leftAssocRefls (w : G) [CoxeterGroup G] := {t : G | t ∈ Refl G ∧ ℓ(((t:G)*w)) < ℓ(w)}

def rightAssocRefls (w : G) [CoxeterGroup G] := {t : G | t ∈ Refl G ∧ ℓ((w*(t:G))) < ℓ(w)}

def leftDescent (w : G) [hG:CoxeterGroup G] := leftAssocRefls w ∩ hG.S

def rightDescent (w : G) [hG:CoxeterGroup G] := rightAssocRefls w ∩ hG.S

section HeckeAux
variable {G : Type*} {w : G} [hG:CoxeterGroup G]

-- following lemmas assume G is CoxeterGroup, we can also have CoxeterMatrix version.
-- these lemmas are needed in Hecke.lean, because the def of Hecke use [CoxeterGroup G],
-- for convenience, the statements also use [CoxeterGroup G]
-- some lemmas are symmetric, such as muls_twice : w*s*s = w, the symm version is s*s*w = w.
-- this section only contain lemmas that needed in Hecke.lean, you can also formulate the symms if u want.
lemma leftDescent_NE_of_ne_one  (h : w ≠ 1) : Nonempty $ leftDescent w:= sorry

lemma leftDescent_NE_iff_ne_one  : w ≠ 1 ↔ Nonempty (leftDescent w) := sorry

lemma rightDescent_NE_of_ne_one  (h : w ≠ 1) : Nonempty $ rightDescent w:= sorry

lemma rightDescent_NE_iff_ne_one  : w ≠ 1 ↔ Nonempty (rightDescent w) := sorry

lemma ne_one_of_length_smul_lt {s : hG.S} {w:G} (lt: ℓ(s*w) < ℓ(w)) : w ≠ 1:= sorry

lemma length_smul_neq (s:hG.S) (w:G) : ℓ(s*w) ≠ ℓ(w) := sorry

lemma length_muls_neq (w:G) (t:hG.S) : ℓ(w*t) ≠ ℓ(w) := sorry

lemma length_diff_one {s:hG.S} {g : G} : ℓ(s*g) = ℓ(g) + 1  ∨ ℓ(g) = ℓ(s*g) + 1 :=sorry

lemma length_smul_of_length_lt {s : hG.S} {w:G} (lt: ℓ(s*w) < ℓ(w)) : ℓ(s*w) = ℓ(w) - 1 := sorry

lemma length_muls_of_length_lt {s : hG.S} {w:G} (lt: ℓ(w*s) < ℓ(w)) : ℓ(w*s) = ℓ(w) - 1 := sorry

lemma length_smul_of_length_gt {s : hG.S} {w:G} (gt: ℓ(w) < ℓ(s*w)) : ℓ(s*w) = ℓ(w) + 1 := sorry

lemma length_muls_of_length_gt {s : hG.S} {w:G} (gt: ℓ(w) < ℓ(w*s)) : ℓ(w*s) = ℓ(w) + 1 := sorry

lemma length_muls_of_mem_leftDescent (s : leftDescent w) : ℓ(s*w) = ℓ(w) - 1 :=sorry

lemma length_muls_of_mem_rightDescent (s : rightDescent w) : ℓ(w*s) = ℓ(w) - 1 :=sorry

lemma length_muls_lt_of_mem_rightDescent (s : rightDescent w) : ℓ(w*s) < ℓ(w) := by
  rw [length_muls_of_mem_rightDescent]
  have hwne1: w ≠ 1 := rightDescent_NE_iff_ne_one.2 (Nonempty.intro s)
  have : 0 < ℓ(w) := Nat.ne_zero_iff_zero_lt.1 $ (Function.mt length_zero_iff_one.1) hwne1
  rw [←Nat.pred_eq_sub_one]
  exact Nat.pred_lt_self this

lemma mem_rightDescent_of_length_muls_lt {w:G} {s: hG.S} (h: ℓ(w*s) < ℓ(w)) : s.1 ∈ rightDescent w := by
  sorry

lemma muls_twice (w:G) (s:hG.S) : w*s*s = w := sorry

lemma smul_eq_muls_of_length_eq (s t:hG.S) (w:G) :ℓ(s*w*t) = ℓ(w) ∧ ℓ(s*w)=ℓ(w*t) → s*w=w*t:= sorry

lemma length_smul_eq_length_muls_of_length_neq (s t :hG.S) (w:G): ℓ(s*w*t) ≠ ℓ(w) → ℓ(s*w)=ℓ(w*t):= sorry

-- ℓ(s*w*t) = ℓ(w) or ℓ(s*w*t) = ℓ(w) + 2 or ℓ(s*w*t) = ℓ(w) - 2
-- ℓ(s*w*t) < ℓ(w) →  ℓ(s*w*t) < ℓ(s*w) <ℓ(w) ∧ ℓ(s*w*t) < ℓ(w*t) <ℓ(w)
lemma length_lt_of_length_smuls_lt {s t:hG.S} {w:G} (h: ℓ(s*w*t) < ℓ(w)) : ℓ(s*w*t) < ℓ(s*w) := sorry

lemma length_lt_of_length_smuls_lt' {s t:hG.S} {w:G} (h: ℓ(s*w*t) < ℓ(w)) : ℓ(s*w) < ℓ(w) := sorry

lemma length_gt_of_length_smuls_gt {s t:hG.S} {w:G} (h: ℓ(w) < ℓ(s*w*t)) : ℓ(w) < ℓ(s*w) :=sorry

lemma length_gt_of_length_smuls_gt' {s t:hG.S} {w:G} (h: ℓ(w) < ℓ(s*w*t)) : ℓ(s*w) <ℓ(s*w*t) :=sorry

end HeckeAux

end CoxeterGroup
