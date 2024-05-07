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
lemma mem_rightInvSeq {ω : List B} {t : W} (h : t ∈ ris ω) :
  ∃ n : ℕ, n < ω.length ∧ t = (π (ω.drop (n + 1)))⁻¹ * ((Option.map (cs.simple) (ω.get? n)).getD 1) * (π (ω.drop (n + 1))) := by
  induction ω with
  | nil => simp only [CoxeterSystem.rightInvSeq_nil, List.not_mem_nil] at *
  | cons hd tail ih =>
    rw [CoxeterSystem.rightInvSeq, List.mem_cons] at h
    rcases h with h₁ | h₂
    · use 0
      constructor
      · norm_num
      · simp only [zero_add]
        simp only [List.drop_succ_cons, List.drop_zero, List.get?_cons_zero]
        simp only [Option.map_some', Option.getD_some]
        exact h₁
    · obtain ⟨n, hn, hprod⟩ := ih h₂
      use (n + 1)
      constructor
      · rw [List.length_cons]
        rw [Nat.succ_eq_add_one, add_lt_add_iff_right]
        exact hn
      · simp only [List.drop_succ_cons, List.get?_cons_succ]
        exact hprod

lemma drop_reverse {ω : List B} {n : ℕ} (h : n ≤ ω.length) :
  ω.reverse.drop n = (ω.take (ω.length - n)).reverse := by
  apply List.reverse_injective
  have : n = ω.reverse.length - (ω.reverse.length - n) := by rw [List.length_reverse]; omega
  nth_rw 1 [this]
  rw [← List.reverse_take (ω.reverse.length - n) (by omega)]
  repeat rw [List.reverse_reverse]
  rw [List.length_reverse]

lemma mem_leftInvSeq {ω : List B} {t : W} (h : t ∈ cs.leftInvSeq ω) :
  ∃ n : ℕ, n < ω.length ∧ t = (π (ω.take n)) * (Option.map (cs.simple) (ω.get? n)).getD 1 * (π (ω.take n))⁻¹ := by
  rw [← List.reverse_reverse ω, CoxeterSystem.leftInvSeq_reverse] at h
  have := List.mem_reverse.1 h
  obtain ⟨k, hk, hk_prod⟩ := mem_rightInvSeq cs this
  rw [List.length_reverse] at hk
  rw [drop_reverse (by omega)] at hk_prod
  rw [CoxeterSystem.wordProd_reverse] at hk_prod
  rw [inv_inv] at hk_prod
  rw [List.get?_reverse k (by exact hk)] at hk_prod
  rw [Nat.sub_sub, Nat.add_comm] at hk_prod
  use ω.length - (1 + k)
  constructor
  · omega
  · exact hk_prod

-- I prove a new property of eraseIdx
lemma eraseIdx_reverse {ω : List B} {i : ℕ} (h : i < ω.length) :
  (ω.eraseIdx i).reverse = ω.reverse.eraseIdx (ω.length - i - 1) := by
  rw [List.eraseIdx_eq_take_drop_succ, Nat.succ_eq_add_one]
  rw [List.reverse_append]
  have : ∀ k ≤ ω.length, k = ω.length - (ω.length - k) := by omega
  rw [this (i + 1) (by omega)]
  rw [← List.reverse_take (ω.length - (i + 1)) (by omega)]
  nth_rw 2 [this i (by omega)]
  rw [← drop_reverse (by omega)]
  rw [List.eraseIdx_eq_take_drop_succ]
  congr 2; omega

lemma drop_head {ω : List B} {n : ℕ} (h : ω.drop n ≠ []) :
  s ((ω.drop n).head h) = (Option.map (cs.simple) (ω.get? n)).getD 1 := by
  induction ω generalizing n with
  | nil => simp only [List.drop_nil, ne_eq, not_true_eq_false] at h
  | cons hd tail ih =>
    by_cases h' : n = 0
    · simp_rw [h']
      simp_rw [List.drop_zero]
      rw [List.head_cons, List.get?_cons_zero]
      rw [Option.map_some', Option.getD_some]
    · have n_pos := Nat.pos_iff_ne_zero.2 h'
      have n_sub_add : n = n - 1 + 1 := by rw [Nat.sub_add_cancel]; exact n_pos
      have : (hd :: tail).drop n = tail.drop (n - 1) := by nth_rw 1 [n_sub_add, List.drop_succ_cons]
      simp_rw [this]; rw [this] at h
      rw [ih]; congr 2
      nth_rw 2 [n_sub_add]
      apply List.get?_cons_succ.symm

lemma drop_take_head_mul_wordProd {ω : List B} {n m : ℕ} (h : m < n) (h' : n ≤ ω.length) :
  π ((ω.take n).drop m) =
    (Option.map (cs.simple) (ω.get? m)).getD 1 * π ((ω.take n).drop (m + 1)) := by
  have : (ω.take n).drop m ≠ [] := by
    rw [← List.length_pos, List.length_drop, List.length_take]; omega
  rw [← List.get?_take h]
  rw [← drop_head cs this]
  rw [← CoxeterSystem.wordProd_cons]
  rw [← List.tail_drop, List.head_cons_tail]

lemma left_inversion_iff_right_inversion_reverse {ω : List B} {t : W} :
  cs.IsLeftInversion (π ω) t ↔ cs.IsRightInversion (π ω.reverse) t := by
  constructor
  · intro h
    simp only [CoxeterSystem.IsRightInversion]
    constructor
    · exact h.1
    · rw [← CoxeterSystem.inv_reflection_eq cs h.1]
      rw [CoxeterSystem.wordProd_reverse]
      rw [← mul_inv_rev]
      repeat rw [CoxeterSystem.length_inv]
      exact h.2
  · intro h
    simp only [CoxeterSystem.IsLeftInversion]
    constructor
    · exact h.1
    · rw [← CoxeterSystem.inv_reflection_eq cs h.1]
      rw [← inv_inv (π ω), ← mul_inv_rev]
      rw [← CoxeterSystem.wordProd_reverse]
      repeat rw [CoxeterSystem.length_inv]
      exact h.2

lemma isReflection_iff_isReflection_inverse {t : W} : cs.IsReflection t ↔ cs.IsReflection t⁻¹ := by
  constructor
  · intro h; rw [← CoxeterSystem.inv_reflection_eq cs h, inv_inv]; exact h
  · intro h; rw [← inv_inv t, CoxeterSystem.inv_reflection_eq cs h]; exact h

lemma word_mul_t_imp_isReflection_t {ω : List B} {t : W} {n : ℕ} (h₀ : n < ω.length)
  (hprod : π ω * t = π (ω.eraseIdx n)) : cs.IsReflection t := by
  rw [CoxeterSystem.IsReflection]
  rw [← CoxeterSystem.wordProd_mul_getD_rightInvSeq] at hprod
  rw [mul_right_inj] at hprod
  rw [CoxeterSystem.getD_rightInvSeq] at hprod
  have : ω.drop n ≠ [] := by rw [← List.length_pos, List.length_drop]; omega
  use (π (ω.drop (n + 1)))⁻¹, ((ω.drop n).head this)
  rw [inv_inv]
  rw [drop_head cs this]
  exact hprod

lemma t_mul_word_imp_isReflection_t {ω : List B} {t : W} {n : ℕ} (h₀ : n < ω.length)
  (hprod : t * π ω = π (ω.eraseIdx n)) : cs.IsReflection t := by
  rw [← inv_inj, mul_inv_rev] at hprod
  repeat rw [← CoxeterSystem.wordProd_reverse cs] at hprod
  rw [eraseIdx_reverse (by exact h₀)] at hprod
  rw [← List.length_reverse] at hprod
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
  obtain ⟨n, hn, hprod⟩ := mem_rightInvSeq cs h
  use n
  constructor
  · exact hn
  · rw [← CoxeterSystem.wordProd_mul_getD_rightInvSeq]
    rw [mul_right_inj]
    rw [CoxeterSystem.getD_rightInvSeq]
    exact hprod

theorem right_exchange' {ω : List B} {t : W} (h : cs.IsRightInversion (π ω) t) :
  ∃ j < ω.length, π ω * t = π (ω.eraseIdx j) := right_exchange'_aux cs (right_exchange cs h)

private lemma left_exchange'_aux {ω : List B} {t : W} (h : t ∈ lis ω) :
  ∃ j < ω.length, t * π ω = π (ω.eraseIdx j) := by
  obtain ⟨n, hn, hprod⟩ := mem_leftInvSeq cs h
  use n
  constructor
  · exact hn
  · rw [← CoxeterSystem.getD_leftInvSeq_mul_wordProd]
    rw [mul_left_inj]
    rw [CoxeterSystem.getD_leftInvSeq]
    exact hprod

theorem left_exchange' {ω : List B} {t : W} (h : cs.IsLeftInversion (π ω) t) :
  ∃ j < ω.length, t * π ω = π (ω.eraseIdx j) := left_exchange'_aux cs (left_exchange cs h)

theorem right_exchange_tfae_of_reduced {ω : List B} (t : W) (rω : cs.IsReduced ω) :
    List.TFAE [
      cs.IsRightInversion (π ω) t,
      t ∈ ris ω,
      ∃ j < ω.length, (π ω) * t = π (ω.eraseIdx j)
    ] := by
  tfae_have 1 → 2; exact right_exchange cs
  tfae_have 2 → 3; exact right_exchange'_aux cs
  tfae_have 3 → 1
  · intro h
    rcases h with ⟨n, hn, hprod⟩
    rw [CoxeterSystem.IsRightInversion]
    constructor
    · exact word_mul_t_imp_isReflection_t cs hn hprod
    · rw [hprod, rω]
      have : ℓ (π (ω.eraseIdx n)) ≤ ω.length - 1 := by
        rw [← List.length_eraseIdx_add_one hn]
        exact CoxeterSystem.length_wordProd_le cs (ω.eraseIdx n)
      omega
  tfae_finish

theorem left_exchange_tfae_of_reduced {ω : List B} (t : W) (rω : cs.IsReduced ω) :
    List.TFAE [
      cs.IsLeftInversion (π ω) t,
      t ∈ lis ω,
      ∃ j < ω.length, t * (π ω) = π (ω.eraseIdx j)
    ] := by
  tfae_have 1 → 2; exact left_exchange cs
  tfae_have 2 → 3; exact left_exchange'_aux cs
  tfae_have 3 → 1
  · intro h
    rcases h with ⟨n, hn, hprod⟩
    rw [CoxeterSystem.IsLeftInversion]
    constructor
    · exact t_mul_word_imp_isReflection_t cs hn hprod
    · rw [hprod, rω]
      have : ℓ (π (ω.eraseIdx n)) ≤ ω.length - 1 := by
        rw [← List.length_eraseIdx_add_one hn]
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
  · rw [h, non_reduced_p, List.drop_zero]; exact h₀
  · apply @Nat.findGreatest_of_ne_zero i (non_reduced_p cs ω) (Classical.decPred _) (ω.length)
    exact h₁.symm; exact h

private lemma beyond_max_index_is_reduced (ω : List B) (n : ℕ) (h₀ : n ≤ ω.length)
  (h₁ : n > max_non_reduced_word_index cs ω) : cs.IsReduced (ω.drop n) := by
  apply of_not_not
  apply @Nat.findGreatest_is_greatest n (non_reduced_p cs ω) (Classical.decPred _) (ω.length)
  exact h₁; exact h₀

private lemma max_index_lt_length (ω : List B) (i : ℕ) (h : i = max_non_reduced_word_index cs ω)
  (hω : ¬cs.IsReduced ω) : i < ω.length := by
  have := @Nat.findGreatest_le (non_reduced_p cs ω) (Classical.decPred _) (List.length ω)
  have i_ne_len : i ≠ ω.length := by
    simp only [max_non_reduced_word_index] at h
    by_contra!
    rw [h] at this
    have : ¬cs.IsReduced (ω.drop ω.length) := by
      rw [← non_reduced_p]
      apply @Nat.findGreatest_of_ne_zero (ω.length) (non_reduced_p cs ω) (Classical.decPred _)
      apply this
      have := List.length_pos.2 (not_reduced_imp_not_empty cs ω hω)
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
  have : ω1 ≠ [] := by rw [← List.length_pos, List.length_drop]; omega
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
      rw [hd_tail]
      rw [CoxeterSystem.wordProd_cons]
      rw [List.length_cons, Nat.succ_eq_add_one]
      rw [this]
      rw [add_left_inj]
      exact ω2_reduced
    contradiction
  have exch_prop : ∃ j < ω2.length, π ω1 = π (ω2.eraseIdx j) := by
    rw [hd_tail, CoxeterSystem.wordProd_cons]
    apply left_exchange'
    rw [CoxeterSystem.isLeftInversion_simple_iff_isLeftDescent]
    rw [CoxeterSystem.IsLeftDescent]
    rw [← CoxeterSystem.wordProd_cons]
    rw [← hd_tail]
    exact this
  obtain ⟨j, hj, hj_prod⟩ := exch_prop
  use (j + i + 1)
  constructor
  · simp only [ω2, List.length_drop] at hj; omega
  · use i
    constructor
    · omega
    · nth_rw 1 [← List.take_append_drop i ω]
      rw [CoxeterSystem.wordProd_append]
      repeat rw [List.eraseIdx_eq_take_drop_succ]
      rw [CoxeterSystem.wordProd_append]
      rw [List.take_append_of_le_length (by rw [List.length_take]; omega)]
      rw [List.take_take, min_eq_left_of_lt (by omega), mul_right_inj]
      rw [List.drop_append_of_le_length (by rw [List.length_take]; omega)]
      rw [List.drop_take]
      simp only [Nat.succ_eq_add_one, Nat.succ_sub_succ_eq_sub, add_tsub_cancel_right]
      have : j + i + 1 + 1 = (j + 1) + (i + 1) := (Nat.add_right_comm j 1 (i + 1)).symm
      rw [this]
      nth_rw 2 [← List.drop_drop]
      rw [← List.eraseIdx_eq_take_drop_succ]
      exact hj_prod

private lemma DeletionProp_corollary_pre (ω : List B) (h : ¬cs.IsReduced ω) :
   ∃ j < ω.length, ∃ i < j, π ((ω.take (j + 1)).drop i) = π ((ω.take j).drop (i + 1)) := by
  rcases (DeletionProp cs ω h) with ⟨j, hj, i, hi, jprod⟩
  use j
  constructor
  · exact hj
  · use i
    constructor
    · exact hi
    · simp_rw [List.eraseIdx_eq_take_drop_succ] at jprod
      rw [List.take_append_of_le_length (by rw [List.length_take]; omega)] at jprod
      rw [List.take_take, min_eq_left_of_lt (by omega)] at jprod
      rw [List.drop_append_of_le_length (by rw [List.length_take]; omega)] at jprod
      nth_rw 1 [← List.take_append_drop i ω] at jprod
      simp_rw [CoxeterSystem.wordProd_append, mul_right_inj] at jprod
      nth_rw 1 [← List.take_append_drop (j + 1) ω] at jprod
      rw [List.drop_append_of_le_length (by rw [List.length_take]; omega)] at jprod
      rw [CoxeterSystem.wordProd_append, mul_left_inj] at jprod
      assumption

private lemma DeletionProp_corollary (ω : List B) (h : ¬cs.IsReduced ω) :
  ∃ j < ω.length, ∃ i < j,  ((ris ω).getD i 1) = ((ris ω).getD j 1) := by
  rcases (DeletionProp_corollary_pre cs ω h) with ⟨j, hj, i, hi, jprod⟩
  use j
  constructor
  · exact hj
  · use i
    constructor
    · exact hi
    · have : (π ω) * ((ris ω).getD j 1) * ((ris ω).getD i 1) = π ω := by
        nth_rw 2 [← mul_one (π ω)]
        nth_rw 3 [← CoxeterSystem.getD_rightInvSeq_mul_self cs ω i]
        rw [← mul_assoc, mul_left_inj]
        simp_rw [CoxeterSystem.wordProd_mul_getD_rightInvSeq]
        simp_rw [List.eraseIdx_eq_take_drop_succ]
        simp_rw [CoxeterSystem.wordProd_append, Nat.succ_eq_add_one]
        nth_rw 4 [← List.take_append_drop (j + 1) ω]
        rw [List.drop_append_of_le_length (by rw [List.length_take]; omega)]
        nth_rw 1 [← List.take_append_drop i ω]
        rw [List.take_append_eq_append_take]
        rw [List.take_take, min_eq_right (by omega)]
        simp_rw [CoxeterSystem.wordProd_append]
        rw [← mul_assoc, mul_left_inj, mul_right_inj]
        rw [List.length_take, min_eq_left (by omega)]
        rw [List.take_drop, Nat.add_sub_cancel' (by omega)]
        rw [drop_take_head_mul_wordProd cs (by exact hi) (by omega)]
        rw [← jprod]
        rw [drop_take_head_mul_wordProd cs (by omega) (by exact hj)]
        rw [← mul_assoc, mul_left_eq_self]
        rw [List.get?_eq_get (by omega)]
        rw [Option.map_some', Option.getD_some]
        rw [CoxeterSystem.simple_mul_simple_self]
      rw [mul_assoc, mul_right_eq_self] at this
      nth_rw 3 [← CoxeterSystem.getD_rightInvSeq_mul_self cs ω i] at this
      rw [mul_left_inj] at this
      exact this.symm

-- i realize i have to use fintype in some way. uhh any other ideas...???
theorem nodup_rightInvSeq_iff (ω : List B) : List.Nodup (ris ω) ↔ cs.IsReduced ω := by
  constructor
  · intro h; by_contra h'
    rcases (DeletionProp_corollary cs ω h') with ⟨j, hj, i, hi, ieqj⟩
    have : ¬List.Nodup (ris ω) := by
      rw [List.nodup_iff_injective_get, Function.Injective]
      simp only [not_forall, exists_prop]
      rw [← CoxeterSystem.length_rightInvSeq cs] at hj
      use ⟨i, by omega⟩, ⟨j, by exact hj⟩
      rw [List.getD_eq_get, List.getD_eq_get] at ieqj
      constructor
      · exact ieqj
      · exact Fin.ne_of_lt hi
    contradiction
  · exact CoxeterSystem.nodup_rightInvSeq_of_reduced cs

theorem nodup_leftInvSeq_iff (ω : List B) : List.Nodup (lis ω) ↔ cs.IsReduced ω := by
  constructor
  · intro h
    rw [← CoxeterSystem.isReduced_reverse]
    rw [← nodup_rightInvSeq_iff]
    rw [← List.nodup_reverse] at h
    rw [← CoxeterSystem.rightInvSeq_reverse] at h
    exact h
  · exact CoxeterSystem.nodup_leftInvSeq_of_reduced cs
