import Coxeter.OrderTwoGen
import Coxeter.CoxeterMatrix.Characterization
import Mathlib.Tactic

/-!
# Coxeter System
This file provides the definition of a Coxeter group, and some basic properties of Coxeter groups.

## Main definitions
1. `CoxeterSystem` : a typeclass for Coxeter systems, given by a Group `G` and order 2
generating set `S`, with `ExchangeProp`.
2. `CoxeterGroup` : a typeclass for Coxeter groups, the same as `CoxeterSystem`, but
without set `S`.
-/

open OrderTwoGen
section

class CoxeterSystem (G : Type*) [Group G] (S : Set G) extends OrderTwoGen S where
  exchange : ExchangeProp S
  exchange' : ExchangeProp' S := (exchange_iff_exchange' S).1 exchange
  deletion : DeletionProp S := exchange_imp_deletion S exchange

class CoxeterGroup (G : Type*) extends HOrderTwoGenGroup G where
  exchange : ExchangeProp S
  exchange': ExchangeProp' S := (exchange_iff_exchange' S).1 exchange
  deletion: DeletionProp S := exchange_imp_deletion S exchange

end

namespace CoxeterGroup
open HOrderTwoGenGroup

instance SimpleRefl_isCoxeterSystem {G : Type*} [hG:CoxeterGroup G]: CoxeterSystem G (SimpleRefl G) where
  exchange := hG.exchange
  exchange' := hG.exchange'
  deletion := hG.deletion

instance SimpleRefl_isCoxeterSystem' {G : Type*} [hG:CoxeterGroup G]: CoxeterSystem G (hG.S) where
  exchange := hG.exchange
  exchange' := hG.exchange'
  deletion := hG.deletion

instance {G : Type*} [hG : CoxeterGroup G]: HMul hG.S G G where
  hMul := fun s g => s.1 * g

instance {G : Type*} [hG : CoxeterGroup G]: HMul G hG.S G where
  hMul := fun g s => g * s.1

instance {G : Type*} [hG : CoxeterGroup G]: CoeOut hG.S G where
  coe := fun s => s.1

/-- The length function defines a metric on the Coxeter group -/
noncomputable instance metric [CoxeterGroup G]: MetricSpace G := OrderTwoGen.metric <| SimpleRefl G

def leftAssocRefls (w : G) [CoxeterGroup G] := {t : G | t ∈ Refl G ∧ ℓ(((t:G)*w)) < ℓ(w)}

def rightAssocRefls (w : G) [CoxeterGroup G] := {t : G | t ∈ Refl G ∧ ℓ((w*(t:G))) < ℓ(w)}

def leftDescent (w : G) [hG:CoxeterGroup G] := leftAssocRefls w ∩ hG.S

def rightDescent (w : G) [hG:CoxeterGroup G] := rightAssocRefls w ∩ hG.S

lemma rightDescent_inv_eq_leftDescent (w : G) [hG : CoxeterGroup G] :
    rightDescent w⁻¹ = leftDescent w := by
  simp only [leftDescent, rightDescent, rightAssocRefls,
    leftAssocRefls, HOrderTwoGenGroup.length]
  ext s
  have h1 (hs : s ∈ S) : OrderTwoGen.length hG.S (w⁻¹ * s) = OrderTwoGen.length hG.S (s * w) := by
    nth_rw 1 [inv_eq_self (S := hG.S) s hs]
    rw [← mul_inv_rev]
    exact (@length_eq_inv_length G _ hG.S).symm
  have h2 : OrderTwoGen.length hG.S w⁻¹ = OrderTwoGen.length hG.S w :=
    (@length_eq_inv_length G _ hG.S).symm
  constructor
  · exact fun h ↦ ⟨⟨h.1.1, (by rw [← h1 h.2, ← h2]; exact h.1.2)⟩, h.2⟩
  · exact fun h ↦ ⟨⟨h.1.1, (by rw [h1 h.2, h2]; exact h.1.2)⟩, h.2⟩

end CoxeterGroup
