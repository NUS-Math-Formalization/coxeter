import Coxeter.OrderTwoGen
import Coxeter.Aux_
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Coxeter.Inversion

/-!
# A Characterization

/-! ### The exchange properties and deletion property -/

The right exchange property:
Let $w = s_{i_1} \cdots s_{i_\ell}$ be a reduced expression for an element $w \in W$
and let $t \in W$.
The following are equivalent:
* $t$ is a right inversion of $w$.
* $t$ appears in the right inversion sequence of the word $s_{i_1} \cdots s_{i_\ell}$.
* There exists $j$ with $1 \leq j \leq \ell$ such that
  $$wt = s_{i_1} \cdots \widehat{s_{i_j}} \cdots s_{i_\ell}$$
  (i.e. the result of multiplying all of the simple reflections $s_{i_1}, \ldots, s_{i_\ell}$
  except $s_{i_j}$).

The left exchange property:
Let $w = s_{i_1} \cdots s_{i_\ell}$ be a reduced expression for an element $w \in W$
and let $t \in W$.
The following are equivalent:
* $t$ is a left inversion of $w$.
* $t$ appears in the left inversion sequence of the word $s_{i_1} \cdots s_{i_\ell}$.
* There exists $j$ with $1 \leq j \leq \ell$ such that
  $$tw = s_{i_1} \cdots \widehat{s_{i_j}} \cdots s_{i_\ell}$$
  (i.e. the result of multiplying all of the simple reflections $s_{i_1}, \ldots, s_{i_\ell}$
  except $s_{i_j}$).
-/

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs: CoxeterSystem M W)

local prefix:max "s" => cs.simple
local prefix:max "ℓ" => cs.length
local prefix:max "ris" => cs.rightInvSeq
local prefix:max "lis" => cs.leftInvSeq
local prefix:max "π" => cs.wordProd

namespace CoxeterGroup

-- I prove a bunch of auxiliary lemmas before proceeding with exchange property.
lemma mem_right_inv_seq {ω : List B} {t : W} (h : t ∈ ris ω) :
  ∃ n : ℕ, n < ω.length ∧ t = (π (ω.drop (n + 1)))⁻¹ * ((Option.map (cs.simple) (ω.get? n)).getD 1) * (π (ω.drop (n + 1))) := by
  induction ω with
  | nil => simp only [CoxeterSystem.rightInvSeq_nil, List.not_mem_nil] at *
  | cons hd tail ih =>
    rw [CoxeterSystem.rightInvSeq, List.mem_cons] at h
    rcases h with h₁ | h₂
    . use 0
      constructor
      . norm_num
      . simp only [zero_add, List.drop_succ_cons, List.drop_zero, List.get?_cons_zero,
          Option.map_some', Option.getD_some]
        exact h₁
    . obtain ⟨n, hn, hprod⟩ := ih h₂
      use (n + 1)
      constructor
      . rw [List.length_cons, Nat.succ_eq_add_one, add_lt_add_iff_right]
        exact hn
      . simp only [List.drop_succ_cons, List.get?_cons_succ]
        exact hprod

lemma drop_reverse {ω : List B} {n : ℕ} (h : n ≤ ω.length) :
  ω.reverse.drop n = (ω.take (ω.length - n)).reverse := by
  apply List.reverse_injective
  have : n = ω.reverse.length - (ω.reverse.length - n) := by rw [List.length_reverse]; omega
  nth_rw 1 [this]
  rw [← List.reverse_take (ω.reverse.length - n) (by omega), List.reverse_reverse,
    List.reverse_reverse, List.length_reverse]

lemma mem_left_inv_seq {ω : List B} {t : W} (h : t ∈ cs.leftInvSeq ω) :
  ∃ n : ℕ, n < ω.length ∧ t = (π (ω.take n)) * (Option.map (cs.simple) (ω.get? n)).getD 1 * (π (ω.take n))⁻¹ := by
  rw [← List.reverse_reverse ω, CoxeterSystem.leftInvSeq_reverse] at h
  have := List.mem_reverse.1 h
  obtain ⟨k, hk, hk_prod⟩ := mem_right_inv_seq cs this
  rw [List.length_reverse] at hk
  rw [drop_reverse (by omega), CoxeterSystem.wordProd_reverse, inv_inv,
    List.get?_reverse k (by exact hk), Nat.sub_sub, Nat.add_comm] at hk_prod
  use ω.length - (1 + k)
  constructor
  . omega
  . exact hk_prod

-- I prove a property of eraseIdx
lemma eraseIdx_eq_take_append_drop {ω : List B} {i : ℕ} :
  ω.eraseIdx i = (ω.take i) ++ (ω.drop (i + 1)) := by
  induction ω generalizing i with
  | nil => simp only [List.eraseIdx_nil, List.take_nil, List.drop_nil, List.append_nil]
  | cons hd tail ih =>
    by_cases h : i = 0
    . rw [h]
      simp only [List.eraseIdx_cons_zero, List.take_zero, zero_add, List.drop_succ_cons,
        List.drop_zero, List.nil_append]
    . have := Nat.pos_iff_ne_zero.2 h
      have := (Nat.sub_eq_iff_eq_add this).mp rfl
      simp only [List.drop_succ_cons]
      rw [this]
      simp only [Nat.reduceSucc, List.eraseIdx_cons_succ, List.take_cons_succ, List.cons_append,
        List.cons.injEq, true_and]
      apply ih

lemma eraseIdx_length {ω : List B} {i : ℕ} (h : i < ω.length) :
  (ω.eraseIdx i).length = ω.length - 1 := by
  rw [eraseIdx_eq_take_append_drop, List.length_append, List.length_take, List.length_drop]
  omega

lemma eraseIdx_reverse {ω : List B} {i : ℕ} (h : i < ω.length) :
  (ω.eraseIdx i).reverse = ω.reverse.eraseIdx (ω.length - i - 1) := by
  rw [eraseIdx_eq_take_append_drop, List.reverse_append]
  have i_one : i + 1 = ω.length - (ω.length - (i + 1)) := by omega
  have : i = ω.length - (ω.length - i) := by omega
  rw [i_one, ← List.reverse_take]
  nth_rw 2 [this]
  rw [← drop_reverse, eraseIdx_eq_take_append_drop]
  congr 2; omega; omega; omega

lemma drop_head {ω : List B} {n : ℕ} (h : ω.drop n ≠ []) :
  s ((ω.drop n).head h) = (Option.map (cs.simple) (ω.get? n)).getD 1 := by
  induction ω generalizing n with
  | nil => simp only [List.drop_nil, ne_eq, not_true_eq_false] at h
  | cons hd tail ih =>
    by_cases h' : n = 0
    . simp_rw [h', List.drop_zero, List.head_cons, List.get?_cons_zero, Option.map_some',
        Option.getD_some]
    . have n_pos := Nat.pos_iff_ne_zero.2 h'
      have n_sub_add : n = n - 1 + 1 := by rw [Nat.sub_add_cancel]; exact n_pos
      have : (hd :: tail).drop n = tail.drop (n - 1) := by nth_rw 1 [n_sub_add, List.drop_succ_cons]
      simp_rw [this]; rw [this] at h
      rw [ih]; congr 2
      nth_rw 2 [n_sub_add]
      apply List.get?_cons_succ.symm

lemma left_inversion_iff_right_inversion_reverse {ω : List B} {t : W} :
  cs.IsLeftInversion (π ω) t ↔ cs.IsRightInversion (π ω.reverse) t := by
  constructor
  . intro h
    simp only [CoxeterSystem.IsRightInversion]
    constructor
    . exact h.1
    . rw [← CoxeterSystem.inv_reflection_eq cs h.1, CoxeterSystem.wordProd_reverse, ← mul_inv_rev,
        CoxeterSystem.length_inv, CoxeterSystem.length_inv]
      exact h.2
  . intro h
    simp only [CoxeterSystem.IsLeftInversion]
    constructor
    . exact h.1
    . rw [← CoxeterSystem.inv_reflection_eq cs h.1, ← inv_inv (π ω), ← mul_inv_rev,
        ← CoxeterSystem.wordProd_reverse, CoxeterSystem.length_inv, CoxeterSystem.length_inv]
      exact h.2

lemma isReflection_iff_isReflection_inverse {t : W} : cs.IsReflection t ↔ cs.IsReflection t⁻¹ := by
  constructor
  . intro h; rw [← CoxeterSystem.inv_reflection_eq cs h, inv_inv]; exact h
  . intro h; rw [← inv_inv t, CoxeterSystem.inv_reflection_eq cs h]; exact h

lemma word_mul_t_imp_isReflection_t {ω : List B} {t : W} {n : ℕ} (h₀ : n < ω.length)
  (hprod : π ω * t = π (ω.eraseIdx n)) : cs.IsReflection t := by
  rw [CoxeterSystem.IsReflection]
  rw [← CoxeterSystem.wordProd_mul_getD_rightInvSeq, mul_right_inj,
    CoxeterSystem.getD_rightInvSeq] at hprod
  have : ω.drop n ≠ [] := by rw [← List.length_pos, List.length_drop]; omega
  use (π (ω.drop (n + 1)))⁻¹, ((ω.drop n).head this)
  rw [inv_inv, drop_head cs this]
  exact hprod

lemma t_mul_word_imp_isReflection_t {ω : List B} {t : W} {n : ℕ} (h₀ : n < ω.length)
  (hprod : t * π ω = π (ω.eraseIdx n)) : cs.IsReflection t := by
  rw [← inv_inj, mul_inv_rev, ← CoxeterSystem.wordProd_reverse cs,
    ← CoxeterSystem.wordProd_reverse cs, eraseIdx_reverse (by exact h₀),
    ← List.length_reverse] at hprod
  rw [isReflection_iff_isReflection_inverse]
  rw [← List.length_reverse] at h₀
  have : ω.reverse.length - n - 1 < ω.reverse.length := by omega
  apply word_mul_t_imp_isReflection_t cs this hprod

theorem right_exchange {ω : List B} {t : W} (h : cs.IsRightInversion (π ω) t) : t ∈ ris ω := sorry

/-- Mirrored version of Exchange Property -/
theorem left_exchange {ω : List B} {t : W} (h : cs.IsLeftInversion (π ω) t) : t ∈ lis ω := by
  rw [← List.mem_reverse, ← CoxeterSystem.rightInvSeq_reverse]
  apply right_exchange cs ((left_inversion_iff_right_inversion_reverse cs).1 h)

private lemma right_exchange'_aux {ω : List B} {t : W} (h : t ∈ ris ω) :
  ∃ j < ω.length, π ω * t = π (ω.eraseIdx j) := by
  obtain ⟨n, hn, hprod⟩ := mem_right_inv_seq cs h
  use n
  constructor
  . exact hn
  . rw [← CoxeterSystem.wordProd_mul_getD_rightInvSeq, mul_right_inj, CoxeterSystem.getD_rightInvSeq]
    exact hprod

theorem right_exchange' {ω : List B} {t : W} (h : cs.IsRightInversion (π ω) t) :
  ∃ j < ω.length, π ω * t = π (ω.eraseIdx j) := right_exchange'_aux cs (right_exchange cs h)

private lemma left_exchange'_aux {ω : List B} {t : W} (h : t ∈ lis ω) :
  ∃ j < ω.length, t * π ω = π (ω.eraseIdx j) := by
  obtain ⟨n, hn, hprod⟩ := mem_left_inv_seq cs h
  use n
  constructor
  . exact hn
  . rw [← CoxeterSystem.getD_leftInvSeq_mul_wordProd, mul_left_inj, CoxeterSystem.getD_leftInvSeq]
    exact hprod

theorem left_exchange' {ω : List B} {t : W} (h : cs.IsLeftInversion (π ω) t) :
  ∃ j < ω.length, t * π ω = π (ω.eraseIdx j) := left_exchange'_aux cs (left_exchange cs h)

theorem right_exchange_tfae_of_reduced {ω : List B} (t : W) (rω : cs.IsReduced ω) :
    List.TFAE [
      cs.IsRightInversion (π ω) t,
      t ∈ ris ω,
      ∃ j < ω.length, (π ω) * t = π (ω.eraseIdx j)
    ] := by
  tfae_have 1 → 2
  . exact right_exchange cs
  tfae_have 2 → 3
  . exact right_exchange'_aux cs
  tfae_have 3 → 1
  . intro h
    rcases h with ⟨n, hn, hprod⟩
    rw [CoxeterSystem.IsRightInversion]
    constructor
    . exact word_mul_t_imp_isReflection_t cs hn hprod
    . rw [hprod, rω]
      have : ℓ (π (ω.eraseIdx n)) ≤ ω.length - 1 := by
        rw [← eraseIdx_length hn]
        exact CoxeterSystem.length_wordProd_le cs (ω.eraseIdx n)
      omega
  tfae_finish

theorem left_exchange_tfae_of_reduced {ω : List B} (t : W) (rω : cs.IsReduced ω) :
    List.TFAE [
      cs.IsLeftInversion (π ω) t,
      t ∈ lis ω,
      ∃ j < ω.length, t * (π ω) = π (ω.eraseIdx j)
    ] := by
  tfae_have 1 → 2
  . exact left_exchange cs
  tfae_have 2 → 3
  . exact left_exchange'_aux cs
  tfae_have 3 → 1
  . intro h
    rcases h with ⟨n, hn, hprod⟩
    rw [CoxeterSystem.IsLeftInversion]
    constructor
    . exact t_mul_word_imp_isReflection_t cs hn hprod
    . rw [hprod, rω]
      have : ℓ (π (ω.eraseIdx n)) ≤ ω.length - 1 := by
        rw [← eraseIdx_length hn]
        exact CoxeterSystem.length_wordProd_le cs (ω.eraseIdx n)
      omega
  tfae_finish

def non_reduced_p (ω : List B) := fun k => ¬cs.IsReduced (ω.drop k)

lemma max_non_reduced_word_index_aux (ω : List B) (hω : ¬cs.IsReduced ω) :
  ∃ n, non_reduced_p cs ω n := by
  use 0
  rw [non_reduced_p, List.drop_zero]
  exact hω

noncomputable def max_non_reduced_word_index (ω : List B) :=
  @Nat.findGreatest (non_reduced_p cs ω) (Classical.decPred _) (ω.length)

lemma empty_is_reduced : cs.IsReduced [] := by
  show ℓ (π []) = [].length
  simp only [CoxeterSystem.wordProd_nil, CoxeterSystem.length_one, List.length_nil]

private lemma not_reduced_imp_not_empty (ω : List B) (h : ¬cs.IsReduced ω) : ω ≠ [] := by
  by_contra!
  rw [this] at h
  have := empty_is_reduced cs
  contradiction

-- I prove some properties of maximum index. Could be generalized to arbitrary predicate.
private lemma max_index_is_not_reduced (ω : List B) (i : ℕ) (h₀ : ¬cs.IsReduced ω)
  (h₁ : i = max_non_reduced_word_index cs ω) : ¬cs.IsReduced (ω.drop i) := by
  rw [← non_reduced_p]
  by_cases h : i = 0
  . rw [h, non_reduced_p, List.drop_zero]; exact h₀
  . apply @Nat.findGreatest_of_ne_zero i (non_reduced_p cs ω) (Classical.decPred _) (ω.length)
    . rw [max_non_reduced_word_index] at h₁; exact h₁.symm
    . exact h

private lemma beyond_max_index_is_reduced (ω : List B) (n : ℕ) (h₀ : n ≤ ω.length)
  (h₁ : n > max_non_reduced_word_index cs ω) : cs.IsReduced (ω.drop n) := by
  apply of_not_not
  simp only [max_non_reduced_word_index] at h₁
  apply @Nat.findGreatest_is_greatest n (non_reduced_p cs ω) (Classical.decPred _) (ω.length)
  exact h₁; exact h₀

private lemma max_index_lt_length (ω : List B) (i : ℕ) (h : i = max_non_reduced_word_index cs ω)
  (hω : ¬cs.IsReduced ω) : i < ω.length := by
  have ω_not_empty := not_reduced_imp_not_empty cs ω hω
  have := @Nat.findGreatest_le (non_reduced_p cs ω) (Classical.decPred _) (List.length ω)
  have i_ne_len : i ≠ ω.length := by
    simp only [max_non_reduced_word_index] at h
    by_contra!
    rw [h] at this
    have : ¬cs.IsReduced (ω.drop ω.length) := by
      rw [← non_reduced_p]
      apply @Nat.findGreatest_of_ne_zero (ω.length) (non_reduced_p cs ω) (Classical.decPred _)
      apply this
      have := List.length_pos.2 ω_not_empty
      omega
    simp only [List.drop_length] at this
    have := empty_is_reduced cs
    contradiction
  rw [h, max_non_reduced_word_index] at *
  exact Nat.lt_of_le_of_ne this i_ne_len

-- The proof closely follows Bjorner-Brenti.
theorem DeletionProp (ω : List B) (hω : ¬cs.IsReduced ω) : ∃ j < ω.length, ∃ i < j, π ω = π ((ω.eraseIdx j).eraseIdx i) := by
  let i := max_non_reduced_word_index cs ω
  have := max_index_lt_length cs ω i rfl hω
  let ω1 := ω.drop i; let ω2 := ω.drop (i + 1)
  have : ω1 ≠ [] := by
    apply List.length_pos.1
    rw [List.length_drop]
    omega
  let si := ω1.head this
  have hd_tail : ω1 = si :: ω2 := by
    simp only [ω1, ω2, si, (List.tail_drop ω i).symm, List.head_cons_tail]
  have := max_index_is_not_reduced cs ω i hω rfl
  have ω2_reduced : cs.IsReduced ω2 := by apply beyond_max_index_is_reduced; omega; omega
  have : ℓ (π ω1) < ℓ (π ω2) := by
    rw [hd_tail, CoxeterSystem.wordProd_cons]
    by_contra!
    have : ℓ ((s si) * (π ω2)) = ℓ (π ω2) + 1 := by
      apply (CoxeterSystem.length_simple_mul cs (π ω2) si).resolve_right; omega
    have : cs.IsReduced ω1 := by
      show ℓ (π ω1) = ω1.length
      rw [hd_tail, CoxeterSystem.wordProd_cons, List.length_cons, Nat.succ_eq_add_one, this,
        add_left_inj]
      exact ω2_reduced
    contradiction
  have exch_prop : ∃ j < ω2.length, π ω1 = π (ω2.eraseIdx j) := by
    rw [hd_tail, CoxeterSystem.wordProd_cons]
    apply left_exchange'
    rw [CoxeterSystem.IsLeftInversion]
    constructor
    . rw [CoxeterSystem.IsReflection]
      use 1, si
      simp only [one_mul, inv_one, mul_one]
    . rw [← CoxeterSystem.wordProd_cons, ← hd_tail]; exact this
  obtain ⟨j, hj, hj_prod⟩ := exch_prop
  use (j + i + 1)
  constructor
  . simp only [ω2, List.length_drop] at hj; omega
  . use i
    constructor
    . omega
    . nth_rw 1 [← List.take_append_drop i ω]
      rw [CoxeterSystem.wordProd_append, eraseIdx_eq_take_append_drop, eraseIdx_eq_take_append_drop,
        CoxeterSystem.wordProd_append, List.take_append_of_le_length (by rw [List.length_take]; omega),
        List.take_take, min_eq_left_of_lt (by omega), mul_right_inj,
        List.drop_append_of_le_length (by rw [List.length_take]; omega), List.drop_take]
      simp only [Nat.succ_sub_succ_eq_sub, add_tsub_cancel_right]
      have : j + i + 1 + 1 = (j + 1) + (i + 1) := by exact (Nat.add_right_comm j 1 (i + 1)).symm
      rw [this]
      nth_rw 2 [← List.drop_drop]
      rw [← eraseIdx_eq_take_append_drop]
      exact hj_prod

/-

theorem nodup_rightInvSeq_iff (ω : List B) :
    List.Nodup (ris ω) ↔ cs.IsReduced ω := by
  sorry

theorem nodup_leftInvSeq_iff (ω : List B) :
    List.Nodup (lis ω) ↔ cs.IsReduced ω := by
  sorry

-/
