import Coxeter.CoxeterSystem
import Coxeter.CoxeterMatrix.CoxeterMatrix
import Coxeter.WellFounded
--import Coxeter.Morphism

import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Polynomial.Reverse
import Mathlib.Data.Polynomial.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Data.Polynomial.Laurent
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Equiv


open Classical List CoxeterSystem OrderTwoGen CoxeterGroup HOrderTwoGenGroup CoxeterMatrix

variable {G :(Type _)} [hG:CoxeterGroup G]
variable {w:G}
--#check toMatrix hG.S
--#check CoxeterMatrix.length_smul_neq (m:=toMatrix hG.S) (g:=equiv.invFun w)
--#check Presentation.map hG.S

noncomputable def q :=@LaurentPolynomial.T ℤ _ 1

local notation : max "q⁻¹" => @LaurentPolynomial.T ℤ _ (-1)

@[simp] lemma q_inv_mul : q⁻¹ * q = 1 := by
  simp only [q,←LaurentPolynomial.T_add]
  apply LaurentPolynomial.T_zero

@[simp] lemma mul_q_inv : q * q⁻¹ = 1 := by
  simp only [q,←LaurentPolynomial.T_add]
  apply LaurentPolynomial.T_zero
def Hecke (G : Type*) [CoxeterGroup G] := G →₀ (LaurentPolynomial ℤ)

namespace Hecke

noncomputable def TT : G → Hecke G:= fun w => Finsupp.single w 1

noncomputable instance Hecke.AddCommMonoid : AddCommMonoid (Hecke G):= Finsupp.addCommMonoid

noncomputable instance Hecke.Module : Module (LaurentPolynomial ℤ) (Hecke G):= Finsupp.module _ _

noncomputable instance Hecke.AddCommGroup : AddCommGroup (Hecke G) := Module.addCommMonoidToAddCommGroup (LaurentPolynomial ℤ)

noncomputable instance Hecke.Module.Free : Module.Free (LaurentPolynomial ℤ) (Hecke G):= Module.Free.finsupp _ _ _

instance Hecke.funLike : FunLike (Hecke G) G (LaurentPolynomial ℤ):= Finsupp.instFunLike

noncomputable instance LaurentPolynomial.CommSemiring : CommSemiring (LaurentPolynomial ℤ):=
AddMonoidAlgebra.commSemiring

noncomputable instance TT.Basis : Basis G (LaurentPolynomial ℤ) (Hecke G) := Finsupp.basisSingleOne

@[simp]
lemma TT.Basis_on {w : G} : TT.Basis w = TT w:=rfl

--lemma Hecke.repr_respect_TT : ∀ h:Hecke G, h = finsum (fun w =>(h w) • TT w) :=sorry
-- ∀ h:Hecke G, h = ∑ᶠ w, (h w) * TT w
lemma Hecke.repr_respect_TT : ∀ h:Hecke G, h = Finsupp.sum h (fun w =>(fun p =>p • TT w)) :=by{
  intro h
  rw [←Finsupp.total_apply]
  conv =>
    lhs
    rw [←Basis.total_repr TT.Basis h]
}

@[simp]
lemma TT_apply_self {w : G} : (TT w) w = 1 := by rw [TT,Finsupp.single_apply];simp [ite_true]

--Ts *Tw = Ts*Ts*Tu= (q-1)Ts*Tu+qTu=(qSS1) Tw + qT(s*w) if s∈D_L w

section HeckeMul
--DFinsupp.single w (q-1) + DFinsupp.single (s*w) q))
noncomputable def mulsw (s:hG.S) (w:G)  : Hecke G :=
  if s.1 ∈ rightDescent w then
  ((q-1) • (TT w) + q • (TT (s*w)))
  else TT (s*w)

--Ts* ∑ᶠ w, h (w) * TT w = ∑ᶠ h w * Ts * T w
noncomputable def muls (s:hG.S) (h:Hecke G) : Hecke G:=
    finsum (fun w:G =>  (h w) • (mulsw s w) )

--∑ᶠ (w :G), ((h w) • (mulsw s w):Hecke G)
noncomputable def mulws (w:G) (s:hG.S) : Hecke G :=
  if s.val ∈ rightDescent w then
  ((q-1) • (TT w) + q • (TT (w*s)))
  else TT (w*s)

noncomputable def muls_right (h:Hecke G) (s:hG.S)  : Hecke G:=
finsum (fun w:G =>  (h w) • (mulws w s) )

noncomputable def mulw.F {G:Type*} [CoxeterGroup G] (u :G) (F:(w:G) → adjL w u → Hecke G → Hecke G) (v:Hecke G): Hecke G:=
if h:u =1 then v
  else(
    let s:= Classical.choice (@leftDescent_NE_of_ne_one G u _ (by rwa [ne_eq]))
    have :s.val ∈ HOrderTwoGenGroup.SimpleRefl G:= Set.mem_of_mem_inter_right s.2
    muls ⟨s,this⟩ (F (s.val*u) (@adjL_of_mem_leftDescent G _ _ u s ) v))

noncomputable def mulw {G:Type*} [CoxeterGroup G]:G → Hecke G → Hecke G := @WellFounded.fix G (fun _ => Hecke G → Hecke G) adjL well_founded_adjL (mulw.F (G:=G))

lemma mulsw_apply_of_length_lt {s:hG.S} (h:ℓ(w)<ℓ((s*w))):mulsw s w = TT (s*w):=sorry

lemma mulsw_apply_of_length_gt {s:hG.S} (h:ℓ((s*w))<ℓ(w)):mulsw s w = (q-1) • (TT w) + q • (TT (s*w)):=sorry

lemma mulws_apply_of_length_lt {s:hG.S} (h:ℓ(w)<ℓ((w*s))):mulws w s = TT (w * s):=by{
    rw [mulws]
    have not_smemD_R :¬ (s.1 ∈ rightDescent w):= sorry --non_mem_D_R_of_length_mul_gt w h
    simp only[not_smemD_R,ite_false]
}

lemma mulws_apply_of_length_gt {s:hG.S} (h:ℓ((w*s))<ℓ(w)):mulws w s = (q-1) • (TT w) + q • (TT (w*s)):=by{
  rw [mulws]
  have smemD_R : s.1 ∈ rightDescent w := sorry
  --Set.mem_inter (Set.mem_setOf.2 ⟨(Set.mem_of_subset_of_mem S_subset_T s.2),h⟩) (s.2)
  simp only [smemD_R,ite_true]
}


lemma finsupp_mulsw_of_finsupp_Hecke (x:Hecke G) :Set.Finite (Function.support (fun w => x w • mulsw s w)):=by{
  have : Function.support (fun w => x w • mulsw s w) ⊆ {i | (x i) ≠ 0}:=by{
      simp only [ne_eq, Function.support_subset_iff, Set.mem_setOf_eq]
      intro w
      apply Function.mt
      intro h
      rw [h]
      simp
    }
  exact Set.Finite.subset (Finsupp.finite_support x) this
}

lemma finsupp_mulws_of_finsupp_Hecke (x:Hecke G) :Set.Finite (Function.support (fun w => x w • mulws w s)):=by{
  have : Function.support (fun w => x w • mulws w s) ⊆ {i | (x i) ≠ 0}:=by{
      simp only [ne_eq, Function.support_subset_iff, Set.mem_setOf_eq]
      intro w
      apply Function.mt
      intro h
      rw [h]
      simp
    }
  exact Set.Finite.subset (Finsupp.finite_support x) this
}

lemma finsupp_mul_of_directsum  (a c: Hecke G): Function.support (fun w ↦ ↑(a w) • mulw w c) ⊆  {i | ↑(a i) ≠ 0} := by {
  simp only [ne_eq, Function.support_subset_iff, Set.mem_setOf_eq]
  intro x
  apply Function.mt
  intro h
  rw [h]
  simp
}
end HeckeMul

end Hecke

namespace Hecke
variable (s : hG.S)

local notation : max "End_ε" => Module.End (LaurentPolynomial ℤ) (Hecke G)

noncomputable instance End_ε.Algebra : Algebra (LaurentPolynomial ℤ) End_ε :=
Module.End.instAlgebra (LaurentPolynomial ℤ) (LaurentPolynomial ℤ) (Hecke G)


noncomputable def opl  : (Hecke G)→ (Hecke G) := fun h:(Hecke G) => muls s h

--noncomputable def opl1 (w:G) := DirectSum.toModule  (LaurentPolynomial ℤ) G (Hecke G) (fun w:G => (fun (Hecke G) w => mulw w ))

noncomputable def opr : (Hecke G )→ (Hecke G) := fun h:(Hecke G) => muls_right h s
#check Set.Finite.subset
noncomputable def opl' : End_ε :=
{
  toFun:=opl s
  map_add':=by{
    intro x y
    simp[opl,muls]
    rw [←finsum_add_distrib (finsupp_mulsw_of_finsupp_Hecke x) (finsupp_mulsw_of_finsupp_Hecke y)]
    congr
    apply funext
    intro w
    rw [Finsupp.add_apply,add_smul]
  }
  map_smul':=by{
    intro r x
    simp[opl,muls]
    rw[smul_finsum' r _]
    apply finsum_congr
    intro g
    rw [Finsupp.smul_apply,smul_smul]
    simp only [smul_eq_mul]
    exact finsupp_mulsw_of_finsupp_Hecke x
  }
}

noncomputable def opr' : End_ε :={
  toFun:=opr s
  map_add':=by{
    intro x y
    simp[opr,muls_right]
    rw [←finsum_add_distrib (finsupp_mulws_of_finsupp_Hecke x) (finsupp_mulws_of_finsupp_Hecke y)]
    congr
    apply funext
    intro w
    rw [Finsupp.add_apply,add_smul]
  }
  map_smul':=by{
    intro r x
    simp[opr,muls_right]
    rw[smul_finsum' r _]
    apply finsum_congr
    intro g
    rw [Finsupp.smul_apply,smul_smul]
    simp only [smul_eq_mul]
    exact finsupp_mulws_of_finsupp_Hecke x
  }
}

lemma TT_apply_ne_mul' (w:G) :∀x, x≠w → (TT w) x • mulsw s x = 0:=
  by exact fun x hx=>(by rw [TT,Finsupp.single_eq_of_ne (Ne.symm hx)];simp)

lemma TT_apply_ne_mul (w:G) :∀x, x≠w → (TT w) x • mulws x s = 0:=
  by exact fun x hx=>(by rw [TT,Finsupp.single_eq_of_ne (Ne.symm hx)];simp)

lemma TT_muls_eq_mul_of_length_lt {s:hG.S} (h:ℓ(w)<ℓ(s*w)): opl' s (TT w)  = TT (s*w):=by
  rw [←mulsw_apply_of_length_lt h]
  dsimp [opl',opl,muls]
  simp [finsum_eq_single _ _ (TT_apply_ne_mul' s w)]

lemma TT_muls_eq_mul_of_length_gt {s:hG.S} (h:ℓ(s*w)<ℓ(w)) : opl' s (TT w) = (q-1) • TT w + q • TT (s*w):=by
  rw [←mulsw_apply_of_length_gt h]
  dsimp [opl',opl,muls]
  simp [finsum_eq_single _ _ (TT_apply_ne_mul' s w)]

lemma TT_muls_right_eq_mul_of_length_lt {s:hG.S} (h:ℓ(w)<ℓ(w*s)):  opr' s (TT w)  = TT (w*s):=by
  rw [←mulws_apply_of_length_lt h]
  dsimp [opr',opr,muls_right]
  simp [finsum_eq_single _ _ (TT_apply_ne_mul s w)]

lemma TT_muls_right_eq_mul_of_length_gt {s:hG.S} (h:ℓ(w*s)<ℓ(w)):  opr' s (TT w)  = (q-1) • TT w + q • TT (w*s):=by
  rw [←mulws_apply_of_length_gt h]
  dsimp [opr',opr,muls_right]
  simp [finsum_eq_single _ _ (TT_apply_ne_mul s w)]

lemma opl_commute_opr : ∀ s t:hG.S, LinearMap.comp (opr' t) (opl' s) = LinearMap.comp (opl' s) (opr' t):=by
{
  intro s t
  have haux: ∀ w:G, (opr' t ∘ₗ opl' s) (TT.Basis w) = (opl' s ∘ₗ opr' t) (TT.Basis w):=by
  {
    simp only [TT.Basis_on, LinearMap.coe_comp, Function.comp_apply]
    intro w
    by_cases h:ℓ((s*w*t)) = ℓ(w)
    {
      by_cases h1:ℓ(s*w) < ℓ(w)
      {
        by_cases h2: ℓ(w*t) < ℓ(w)
        --(c) ℓ(s*w)=ℓ(w*t) <ℓ(s*w*t) = ℓ(w)
        {
          have wne1 := ne_one_of_length_smul_lt h1
          have h3:ℓ(s*w) < ℓ(s*w*t):=by rw [h];assumption
          have h4:ℓ(w*t) < ℓ(s*(w*t)):=by rw [←mul_assoc,h];assumption
          simp_rw[TT_muls_eq_mul_of_length_gt h1,LinearMap.map_add,LinearMap.map_smul,TT_muls_right_eq_mul_of_length_gt h2,TT_muls_right_eq_mul_of_length_lt h3,LinearMap.map_add,LinearMap.map_smul,TT_muls_eq_mul_of_length_gt h1,TT_muls_eq_mul_of_length_lt h4,←mul_assoc]
          nth_rewrite 2 [smul_eq_muls_of_length_eq s t w]
          rfl
          exact ⟨h,(by rw[length_smul_of_length_lt wne1 h1,length_muls_of_length_lt wne1 h2])⟩
        }
        --(e) length (↑s * w) < length w = ℓ(s*w*t) < length (w * ↑t)
        {
          push_neg at h2
          have h2': ℓ(w) <ℓ(w*t):=Ne.lt_of_le (ne_comm.1 (length_muls_neq w t)) h2
          have h3:ℓ(s*w) < ℓ(s*w*t):=by rw [h];assumption
          have h4:ℓ(s*(w*t)) < ℓ(w*t):=by rw [←mul_assoc,h];assumption
          have h4':ℓ(s*w*t) < ℓ(w*t):=by rw [mul_assoc];assumption
          rw [TT_muls_eq_mul_of_length_gt h1,LinearMap.map_add,LinearMap.map_smul,TT_muls_right_eq_mul_of_length_lt h2',LinearMap.map_smul,TT_muls_right_eq_mul_of_length_lt h3,TT_muls_eq_mul_of_length_gt h4,mul_assoc]
        }
      }
      {
        by_cases h2: ℓ(w*t) < ℓ(w)
        --(d) ℓ(wt) < ℓ{w) = ℓ(swt) < ℓ(sw)
        {
          push_neg at *
          have h1' := Ne.lt_of_le ( ne_comm.1 <| length_smul_neq s w)  h1
          have h3 : ℓ(↑s * w * ↑t) < ℓ(↑s * w):= (eq_comm.1 h) ▸ h1'
          have h4 : ℓ(w * ↑t) < ℓ(↑s * w * ↑t):= (eq_comm.1 h) ▸ h2
          rw [mul_assoc] at h4
          simp_rw [TT_muls_eq_mul_of_length_lt h1',TT_muls_right_eq_mul_of_length_gt h3,TT_muls_right_eq_mul_of_length_gt h2,LinearMap.map_add,LinearMap.map_smul,TT_muls_eq_mul_of_length_lt h1',TT_muls_eq_mul_of_length_lt h4,mul_assoc]
        }
        --(f) ℓ(w) = ℓ(swt) < ℓ(wt) = ℓ(sw)
        {
          push_neg at *
          have h1' := Ne.lt_of_le ( ne_comm.1 <| length_smul_neq s w)  h1
          have h2' := Ne.lt_of_le ( ne_comm.1 <| length_muls_neq w t)  h2
          have h3  := eq_comm.1 h ▸ h1'
          have h4  := eq_comm.1 h ▸ h2'
          have h5  : ℓ(s*w) = ℓ(w*t) := by rw [length_smul_of_length_gt h1',length_muls_of_length_gt h2']
          rw [mul_assoc] at h4
          simp_rw [TT_muls_eq_mul_of_length_lt h1',TT_muls_right_eq_mul_of_length_gt h3,TT_muls_right_eq_mul_of_length_lt h2',TT_muls_eq_mul_of_length_gt h4,mul_assoc,smul_eq_muls_of_length_eq s t w ⟨h,h5⟩]
        }
      }
    }
    {
      have h1:=length_smul_eq_length_muls_of_length_neq s t w h
      rcases( Ne.lt_or_lt h) with hl|hr
      --(b) length (↑s * w * ↑t) < length (↑s * w) = length (w * ↑t)< length w
      {
        have h2 := length_lt_of_length_smuls_lt hl
        have h3 := length_lt_of_length_smuls_lt' hl
        have h4 := h1 ▸ h3
        have h5 : ℓ(↑s * w * ↑t) < length (w * t) := by rwa [h1] at h2
        rw [mul_assoc] at h5
        simp_rw [TT_muls_eq_mul_of_length_gt h3,LinearMap.map_add,LinearMap.map_smul,TT_muls_right_eq_mul_of_length_gt h4,TT_muls_right_eq_mul_of_length_gt h2,LinearMap.map_add,LinearMap.map_smul,TT_muls_eq_mul_of_length_gt h3,TT_muls_eq_mul_of_length_gt h5,mul_assoc]
        simp only [smul_add]
        rw [smul_smul (q-1) q,smul_smul q (q-1),mul_comm (q-1),mul_smul,mul_comm,mul_smul]
        conv =>
          lhs
          rw [add_assoc]
          congr
          . skip
          rw [←add_assoc,add_comm (q • (q - 1) • TT (w * ↑t)),add_assoc]
        rw [add_assoc]
      }
      -- (a) ℓ(w) < ℓ(wt) = ℓ(sw) < ℓ(swt)
      {
        have h2 := length_gt_of_length_smuls_gt hr
        have h3 := length_gt_of_length_smuls_gt' hr
        have h4 := h1 ▸ h2
        have h5 := h1 ▸ h3
        rw [mul_assoc] at h5
        rw [TT_muls_eq_mul_of_length_lt h2,TT_muls_right_eq_mul_of_length_lt h3,TT_muls_right_eq_mul_of_length_lt h4,TT_muls_eq_mul_of_length_lt h5,mul_assoc]
      }
    }
  }
  exact @Basis.ext G (LaurentPolynomial ℤ) (Hecke G) _ _ _ TT.Basis  (LaurentPolynomial ℤ) _ (@RingHom.id (LaurentPolynomial ℤ) _) (Hecke G) _ _  (LinearMap.comp (opr' t) (opl' s)) (LinearMap.comp (opl' s) (opr' t) ) haux
}

def generator_set (G:Type*) [Group G] [CoxeterGroup G] := opl' (G:=G) '' (Set.univ)
def generator_set' (G:Type*) [Group G] [CoxeterGroup G] :=  opr' (G:=G) '' (Set.univ)

noncomputable def subalg (G:Type*) [Group G] [CoxeterGroup G] := Algebra.adjoin (LaurentPolynomial ℤ) (generator_set G)

--aux.lean
lemma Algebra.mem_adjoin_of_mem_s {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A] {s : Set A} {x : A} : x ∈ s → x ∈ Algebra.adjoin R s:=by{
  intro h
  have := @Algebra.subset_adjoin R A _ _ _ s
  exact Set.mem_of_mem_of_subset h this
}

@[simp]
noncomputable def alg_hom_aux : subalg G → (Hecke G) := fun f => f.1 (TT 1)
--compiler IR check failed at 'alg_hom_aux._rarg', error: unknown declaration 'TT'

noncomputable def subalg' (G:Type*) [Group G] [CoxeterGroup G]
:= Algebra.adjoin (LaurentPolynomial ℤ) (generator_set' G )

@[simp]
noncomputable def alg_hom_aux' : subalg' G → (Hecke G) := fun f => f.1 (TT 1)

noncomputable instance subalg.Algebra: Algebra (LaurentPolynomial ℤ) (subalg G) := Subalgebra.algebra (subalg G)
noncomputable instance subalg'.Algebra: Algebra (LaurentPolynomial ℤ) (subalg' G) := Subalgebra.algebra (subalg' G)

lemma opl'_mem_subalg (s:hG.S) : opl' s ∈ subalg G := Algebra.mem_adjoin_of_mem_s (Set.mem_image_of_mem _ (Set.mem_univ s))
lemma opr'_mem_subalg' (s:hG.S) : opr' s ∈ subalg' G := Algebra.mem_adjoin_of_mem_s (Set.mem_image_of_mem _ (Set.mem_univ s))

def p_subalg_commute_subalg' (f:subalg G) :=∀ g:subalg' G, f.1 ∘ₗ g.1 = g.1 ∘ₗ f.1

lemma p_subalg_commute_subalg'_proof (x:End_ε)(h:x∈ generator_set G) :∀ g:subalg' G, x ∘ₗ g.1 = g.1 ∘ₗ x:=by
  rcases (Set.mem_image _ _ _).1 h with ⟨f,hf⟩
  rw [←hf.2]
  apply @Algebra.adjoin_induction' (LaurentPolynomial ℤ) (End_ε)
  . simp ;intro y hy
    rcases (Set.mem_image _ _ _).1 hy with ⟨g,hg⟩
    rw [←hg.2,opl_commute_opr]
  . simp;intro r;ext x;simp [Module.algebraMap_end_apply]
  . intro f1 f2 h1 h2
    rw [Subalgebra.coe_add,LinearMap.add_comp ,LinearMap.comp_add,h1,h2]
  . intro f1 f2 h1 h2
    rw [Subalgebra.coe_mul,LinearMap.mul_eq_comp,LinearMap.comp_assoc,←h2,←LinearMap.comp_assoc,h1,LinearMap.comp_assoc]

lemma subalg_commute_subalg' (f:subalg G) (g:subalg' G): f.1 ∘ₗ g.1 = g.1 ∘ₗ f.1:=by
  apply @Algebra.adjoin_induction' (LaurentPolynomial ℤ) (End_ε) _ _ _ ((generator_set G) ) p_subalg_commute_subalg'
  . simp [p_subalg_commute_subalg']
    intro x hx a ha
    exact  p_subalg_commute_subalg'_proof x hx ⟨a,ha⟩
  . simp [p_subalg_commute_subalg',Algebra.commutes']
    intro r a _
    ext x
    simp [Module.algebraMap_end_apply]
  . intro f1 f2 h1 h2
    rw [p_subalg_commute_subalg'] at *
    intro g
    rw [Subalgebra.coe_add,LinearMap.add_comp g.1,h1 g,h2 g,LinearMap.comp_add]
  . intro f1 f2 h1 h2
    rw [p_subalg_commute_subalg'] at *
    intro g
    rw [Subalgebra.coe_mul,LinearMap.mul_eq_comp,LinearMap.comp_assoc,h2 g,←LinearMap.comp_assoc,h1 g,LinearMap.comp_assoc]

noncomputable instance alg_hom_aux.IsLinearMap : IsLinearMap (LaurentPolynomial ℤ) (alg_hom_aux: subalg G → Hecke G) where
  map_add:=by intro x y; simp
  map_smul := by intro c x; simp
  noncomputable instance alg_hom_aux'.IsLinearMap : IsLinearMap (LaurentPolynomial ℤ) (alg_hom_aux': subalg' G → Hecke G) where
    map_add:=by
      intro x y; simp
    map_smul:=by
      intro c x; simp

lemma TT_subset_image_of_alg_hom_aux'_aux : ∀ l, ∀ w:G, l = ℓ(w) →∃ f:subalg' G, TT w = alg_hom_aux' f:= by{
  intro l
  induction' l with n hn
  {
    intro w h
    have := length_zero_iff_one.1 (eq_comm.1 h)
    rw [this]
    use 1
    simp [alg_hom_aux']}
  {
    intro w h
    have hw:w≠1:= Function.mt length_zero_iff_one.2 (h ▸ Nat.succ_ne_zero n)
    let s:= Classical.choice (rightDescent_NE_of_ne_one hw)
    have :s.val ∈ S:= Set.mem_of_mem_of_subset s.2 (Set.inter_subset_right _ S)
    have h1:=length_muls_of_mem_rightDescent hw s
    rw [←h,Nat.succ_sub_one] at h1
    have h2:= hn (w * s) (eq_comm.1 h1)
    rcases h2 with ⟨f',hf⟩
    have h3: ℓ(w*s) < ℓ(w*s*s):=by
      rw[muls_twice w ⟨s.1,this⟩,h1,←h]
      simp
    rw [←muls_twice w ⟨s.1,this⟩,←TT_muls_right_eq_mul_of_length_lt h3,hf]
    use ⟨opr' ⟨s.1,this⟩,opr'_mem_subalg' ⟨s.1,this⟩⟩*f'
    simp
  }
}

lemma TT_subset_image_of_alg_hom_aux' : ∀ w:G, ∃ f:subalg' G, TT w = alg_hom_aux' f := by
  intro w
  exact TT_subset_image_of_alg_hom_aux'_aux (ℓ(w)) w rfl

noncomputable def preimage: G → subalg' G := fun w =>(Classical.choose (TT_subset_image_of_alg_hom_aux' w) )

lemma preimage_apply {w:G}: TT w = alg_hom_aux' (preimage w) :=by{
  rw [preimage]
  exact Classical.choose_spec (TT_subset_image_of_alg_hom_aux' w)
}

lemma alg_hom_aux_surjective: Function.Surjective (@alg_hom_aux G _ ) := by {
  sorry
}

lemma alg_hom_aux'_surjective: Function.Surjective (@alg_hom_aux' G _ ) := by
  rw [Function.Surjective]
  intro b
  rw [Hecke.repr_respect_TT b]
  use (Finsupp.sum b fun w p => p • (preimage w))
  simp_rw [preimage_apply]
  simp [alg_hom_aux']
  have : ∀ (b:Hecke G) ,(fun (w:G) (p:LaurentPolynomial ℤ ) =>(p • ((preimage w).val b)))= fun (w:G) (p:LaurentPolynomial ℤ ) => (p • (preimage w)).val b:=by intro b ;simp
  simp[this]
  convert LinearMap.finsupp_sum_apply b (fun w p => ((p • (preimage w)): End_ε)) (TT 1)
  have h2 :(Finsupp.sum b fun w p => p • preimage w).val = Finsupp.sum b fun w p => p • (preimage w).val:=by{
    simp_rw [Finsupp.sum]
    norm_cast
  }
  assumption

lemma alg_hom_injective_aux (f: subalg G) (h: alg_hom_aux f = 0) : f = 0 := by {
  simp at h
  have : ∀ w:G, f.1 (TT w) = 0:=by{
    intro w
    by_cases h1:w=1
    {rw[h1,h]}
    {
      have h1: ∀ g:subalg' G, g.1 (f.1 (TT 1)) = 0:=by{
        rw[h]
        intro g
        rw[map_zero]}
      have h2: ∀ g:subalg' G, f.1 (g.1 (TT 1)) = 0:=by{
        intro g
        rw [←LinearMap.comp_apply,subalg_commute_subalg' f g]
        exact h1 g
      }
      have :=@alg_hom_aux'_surjective G _ (TT w)
      simp [alg_hom_aux'] at this
      rcases this with ⟨g,⟨hg1,hg2⟩⟩
      rw [←hg2]
      exact h2 ⟨g,hg1⟩
    }
  }
  ext x
  simp
  rw [Hecke.repr_respect_TT x,map_finsupp_sum]
  simp[@IsLinearMap.map_smul (LaurentPolynomial ℤ),this]
}

lemma alg_hom_aux_injective : Function.Injective  (alg_hom_aux :subalg G → Hecke G) := by
  rw [Function.Injective]
  intro a1 a2 h
  have : alg_hom_aux (a1 - a2) = 0:=by
    have := sub_eq_zero_of_eq h
    rw [←@IsLinearMap.map_sub (LaurentPolynomial ℤ) ] at this
    assumption
    exact alg_hom_aux.IsLinearMap
  exact sub_eq_zero.1 (alg_hom_injective_aux _ this)

lemma alg_hom_aux_bijective : Function.Bijective (@alg_hom_aux G _) := ⟨alg_hom_aux_injective, alg_hom_aux_surjective⟩

noncomputable def alg_hom (G :Type*) [Group G] [CoxeterGroup G]:
LinearEquiv (@RingHom.id (LaurentPolynomial ℤ) _) (subalg G) (Hecke G) where
  toFun:= alg_hom_aux
  map_add' := by simp
  map_smul' := by simp
  invFun := Function.surjInv alg_hom_aux_surjective
  left_inv := Function.leftInverse_surjInv alg_hom_aux_bijective
  right_inv := Function.rightInverse_surjInv alg_hom_aux_surjective

lemma alg_hom_id : alg_hom G 1 = TT 1 := by simp [alg_hom]

lemma subalg.id_eq :(alg_hom G).symm (TT 1) = 1:=by
  simp_rw [←alg_hom_id, LinearEquiv.symm_apply_eq]

lemma subalg.zero :(alg_hom G).symm 0 = 0:=by
  simp only [alg_hom, map_zero]

@[simp]
noncomputable def HeckeMul : Hecke G → Hecke G → Hecke G := fun x =>(fun y => alg_hom G <| (alg_hom G).symm x * (alg_hom G).symm y)

noncomputable instance (F : Type*)  (R : outParam (Type*)) (M : outParam (Type*)) (M₂ : outParam (Type*)) [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂] [FunLike F M M₂] [LinearMapClass F R M M₂] : ZeroHomClass F  M M₂ where
  map_zero := fun f:F => by simp [LinearMap.map_zero]

noncomputable instance (F : Type*)  (R : outParam (Type*)) (M : outParam (Type*)) (M₂ : outParam (Type*)) [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂] [EquivLike F M M₂] [LinearEquivClass F R M M₂] : ZeroHomClass F  M M₂ where
  map_zero := fun f:F => by simp [LinearMap.map_zero]

noncomputable instance : Mul (Hecke G) where
  mul := HeckeMul

@[simp]
lemma heckeMul {x y : Hecke G} : HeckeMul x y = x * y := rfl

lemma mul_zero : ∀ (a : Hecke G), HeckeMul a 0 = 0 := by
  intro a
  simp only [HeckeMul,map_zero]
  calc
    _ = alg_hom G 0 := by congr;simp only [MulZeroClass.mul_zero]
    _ = 0 := by simp_rw [map_zero]


lemma Hecke.zero_mul : ∀ (a : Hecke G),  HeckeMul 0 a = 0 := by
  intro a
  simp

--f (f⁻¹( f (f⁻¹(a)*f⁻¹(b)) ) * f⁻¹(c)) = f (f⁻¹ (a) * f⁻¹  (f (f⁻¹(b)*f⁻¹(c)) ))
lemma Hecke.mul_assoc :∀ (a b c : Hecke G), HeckeMul (HeckeMul a b) c = HeckeMul a (HeckeMul b c):=by
  intro a b c
  simp only [HeckeMul]
  rw [LinearEquiv.symm_apply_apply (alg_hom G),_root_.mul_assoc,LinearEquiv.symm_apply_apply]

lemma Hecke.one_mul : ∀ (a : Hecke G), HeckeMul (TT 1) a = a := by
  intro a
  rw [HeckeMul, subalg.id_eq]
  simp

lemma Hecke.mul_one : ∀ (a : Hecke G), HeckeMul a (TT 1) = a := by
  intro a
  rw [HeckeMul,subalg.id_eq]
  simp

lemma Hecke.left_distrib : ∀ (a b c : Hecke G), HeckeMul a (b + c) = HeckeMul a b + HeckeMul a c := by
  intro a b c
  simp only[HeckeMul]
  rw [LinearEquiv.map_add,mul_add,LinearEquiv.map_add]

lemma Hecke.right_distrib : ∀ (a b c : Hecke G),  HeckeMul (a + b)  c =  HeckeMul a c + HeckeMul b c :=by
  intro a b c
  simp only[HeckeMul]
  nth_rw 1 [LinearEquiv.map_add,add_mul]
  rw [LinearEquiv.map_add]

noncomputable instance Hecke.Semiring : Semiring (Hecke G) where
  mul:=HeckeMul
  mul_zero:= Hecke.mul_zero
  zero_mul:= Hecke.zero_mul
  left_distrib:= Hecke.left_distrib
  right_distrib:= Hecke.right_distrib
  mul_assoc:=Hecke.mul_assoc
  one:=TT 1
  one_mul:=Hecke.one_mul
  mul_one:=Hecke.mul_one

noncomputable instance : NonUnitalSemiring (Hecke G) := Semiring.toNonUnitalSemiring (α := Hecke G)

noncomputable instance : NonUnitalNonAssocSemiring (Hecke G) := NonUnitalSemiring.toNonUnitalNonAssocSemiring (α := Hecke G)

noncomputable instance : NonUnitalNonAssocRing (Hecke G) :=
  {instNonUnitalNonAssocSemiringHecke with
    add_left_neg := by simp}

lemma Hecke.smul_assoc : ∀ (r : LaurentPolynomial ℤ) (x y : Hecke G), HeckeMul (r • x) y = r • (HeckeMul x y):=by
  intro r x y
  simp_rw [HeckeMul]
  rw [LinearEquiv.map_smul,smul_mul_assoc,LinearEquiv.map_smul]

lemma Hecke.smul_comm : ∀ (r : LaurentPolynomial ℤ) (x y : Hecke G), HeckeMul x (r • y) = r • (HeckeMul x y):=by
  intro r x y
  simp only [HeckeMul]
  rw [LinearEquiv.map_smul,mul_smul_comm,LinearEquiv.map_smul]

noncomputable instance Hecke.algebra : Algebra (LaurentPolynomial ℤ) (Hecke G):=
Algebra.ofModule (Hecke.smul_assoc) (Hecke.smul_comm)

--how to simp * to def?
lemma HeckeMul.gt : ℓ(w) < ℓ(s*w) → TT s.1 * TT w = TT (s.1*w) := by
  intro hl
  --unfold Hecke.Mul
  sorry

lemma HeckeMul.lt : ℓ(s*w) < ℓ(w) → TT s.1 * TT w = (q-1) • (TT w) + q • (TT (s*w)) := sorry

@[simp]
lemma Ts_square : TT s.1 * TT s.1 = (q - 1) • TT s.1 + q • 1 := sorry

noncomputable def listToHecke : List hG.S → Hecke G := fun L => (List.map (TT (G:=G)) L).prod

noncomputable def TT' : G → Hecke G := fun g => listToHecke (@choose_reduced_word G _ hG.S (@SimpleRefls.toOrderTwoGen' G _) g)

@[simp]
lemma listToHecke_cons : listToHecke (s :: L) = TT s.1 * listToHecke L :=by
  dsimp [listToHecke]
  rw [List.prod_cons]
  rfl

@[simp]
lemma listToHecke_nil_eq_one : listToHecke ([] : List hG.S) = 1 :=rfl

theorem TTw_eq_reduced_word_TTmul : ∀ L : List S,∀ w:G, reduced_word L → w = L.gprod → TT w = listToHecke L := by
  intro L
  induction' L with s L hL
  · intros w red heq
    simp [heq]
    rfl
  · intro w red heq
    have redL : reduced_word L:= reduced_imp_tail_reduced red
    have lgt: ℓ(L.gprod) < ℓ(((s :: L):G)) := sorry
    rw [gprod_cons] at heq lgt
    have : L.gprod = L.gprod := rfl
    rw [heq,←HeckeMul.gt s lgt,listToHecke_cons,←hL L.gprod redL this]

--define (TT s)⁻¹

noncomputable def TT_inv_s (s:hG.S) := q⁻¹ • (TT s.val) - (1-q⁻¹) • 1

@[simp]
lemma TT_inv_mul {s:hG.S}:  TT s.1 * (TT_inv_s s) = 1 := by
  dsimp [TT_inv_s]
  set qinv := @LaurentPolynomial.T ℤ _ (-1)
  simp_rw [mul_sub (TT s.1),mul_smul_comm,Ts_square,smul_add,smul_smul,mul_sub,mul_one,q_inv_mul,add_sub_right_comm,sub_self]
  simp

noncomputable def listToHeckeInv : List hG.S → Hecke G := fun L => (List.map TT_inv_s L.reverse).prod

@[simp]
lemma listToHeckeInv_nil_eq_one : listToHeckeInv ([] : List hG.S) = 1 := rfl

theorem is_inv_aux (red : reduced_word L) : listToHecke (G := G) L * (listToHeckeInv L) = 1 := by
  induction' L with s L hL
  · simp
  · simp only [listToHecke,listToHeckeInv,reverse_cons,map_append,prod_append,gprod_cons,prod_cons]
    rw [←listToHecke,←listToHeckeInv,listToHecke_cons]
    have : TT s.1 * listToHecke L * (listToHeckeInv L *  prod (map TT_inv_s [s])) =
    TT s.1 * (listToHecke L * listToHeckeInv L) * prod (map TT_inv_s [s]) := by
      simp_rw [mul_assoc]
    rw [this,hL (reduced_imp_tail_reduced red)]
    dsimp
    simp only [mul_one,TT_inv_mul,prod_singleton]

theorem is_inv_aux' (red : reduced_word L) :  (listToHeckeInv L) * listToHecke (G:=G) L = 1 := by sorry

noncomputable def TTInv : G → Hecke G := fun g =>  listToHeckeInv <| choose_reduced_word hG.S g

lemma mul_TTInv {w : G} : TT w * TTInv w = 1 := by
  dsimp [TTInv]
  set L := choose_reduced_word hG.S w
  rw [TTw_eq_reduced_word_TTmul L w (choose_reduced_word_spec w).1 (choose_reduced_word_spec w).2]
  exact is_inv_aux (choose_reduced_word_spec w).1

lemma TTInv_mul {w : G} : TTInv w * TT w = 1 := by
  dsimp [TTInv]
  set L := choose_reduced_word hG.S w
  rw [TTw_eq_reduced_word_TTmul L w (choose_reduced_word_spec w).1 (choose_reduced_word_spec w).2]
  exact is_inv_aux' (choose_reduced_word_spec w).1

end Hecke
