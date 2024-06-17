import Coxeter.ForMathlib.PosetChain
import Coxeter.ForMathlib.PosetGraded
import Coxeter.ForMathlib.PosetShelling

namespace PartialOrder
variable {P : Type*} [PartialOrder P] [Fintype P]
variable {A : Type*} [PartialOrder A]

instance {x y : P} : Fintype (Set.Icc x y) := sorry -- temporary

/-
Definition: Let `P` and `A` be posets. An edge labelling of `P` in `A` is a map from the set of edges of `P` to the poset `A`.
-/
@[simp]
abbrev edgeLabeling (P A : Type*) [PartialOrder P] := edges P → A

/-
Definition: Let `P` and `A` be posets and `l` be an edge labelling of `P` in `A`.
Then for any maximal chain `m : x_0 ⋖ x_1 ⋖ ⋯ ⋖ x_n` in `P`, we define a list in `A` by `[l(x_0 ⋖ x_1), l(x_1 ⋖ x_2), ⋯, l (x_{n-1} ⋖ x_n)]`.
-/
def mapMaxChain (l : edgeLabeling P A) (m : maximalChains P) : List A := List.map (fun e => l e) <| edgePairs m

def replace_nth (L: List P) (x : P) (n : Fin L.length) : List P := List.modifyNth (fun ?_ ↦ x) n L

lemma replace_concat (L : List P) (x : P) (n : Fin L.length) (h : n.1 > 2) : (replace_nth L x n) = L.take (n.1 - 2) ++ [x] ++ L.drop (n.1 - 1) := by
  sorry

/-
Definition: Given any two nonempty chains in `P`, `m₁ : x_0 < ⋯ < x_n` and `m₂ : x_{n+1} < ⋯ < x_k` with
x_n < x_{n+1}, the concatenation `m : x_0 < ⋯ < x_n < x_{n+1} < ⋯ < x_k` is a chain.
-/
lemma addChain (L L' : List P) (h₀ : chain L ∧ chain L') (h₁: L ≠ [] ∧ L' ≠ []) (h₂ : L.getLast h₁.1 < L'.head h₁.2) : chain (L ++ L') := by
  let L₀ := (L ++ L')
  have : List.Chain' (· < ·) (L₀) := by
    refine List.Chain'.append ?_ ?_ ?_
    · exact h₀.1
    · exact h₀.2
    · let x₀ := L.getLast h₁.1
      let y₀ := L'.head h₁.2
      intro x xlast y yhead
      have : x = x₀ ∧ y = y₀ := by
        constructor
        · exact (getLast_eq_of_getLast?_eq_coe h₁.1 xlast).symm
        · exact (head_eq_of_head?_eq_coe h₁.2 yhead).symm
      rw [this.1, this.2]
      exact h₂
  exact this

lemma pos_sub_length (L : List P) (h₀ : n < L.length) (h₁ : n > 0) : (L.take n).length > 0 ∧ (L.drop n).length > 0 := by
  constructor
  · have len : (L.take n).length = n := by
      simp
      exact Nat.le_of_succ_le h₀
    rw [len]
    exact h₁
  · exact List.lt_length_drop L h₀

lemma split_tail (L : List P) (n : Fin L.length) (h₀ : n.1 > 2) (h : (L.take (n.1 - 2)) ≠ []) : L[n.1 - 3] = (L.take (n.1-2)).getLast h := by
  have : n.1 - 3 < (L.take (n.1-2)).length := by sorry
  have : L[n.1-3] = (L.take (n.1-2))[n.1-3] := by
    apply L.get_take
    have : n.1 - 3 < n.1 - 2 := by exact Nat.sub_succ_lt_self (n.1) 2 h₀
    exact this
  rw [this]
  sorry

lemma split_head (L: List P) (n : Fin L.length) (h₁ : n.1 > 2) (h : (L.drop (n.1 - 1)) ≠ []) : L[n.1 - 1] = (L.drop (n.1 - 1)).head h := by
  sorry

lemma nonempty_split_chain (L : List P) (n : Fin L.length) (h : n.1 > 2) : L.take (n.1 - 2) ≠ [] ∧ L.drop (n.1 - 1) ≠ [] := by
  have nle1 : n.1 - 1 < L.length := by
    refine Nat.sub_one_lt_of_le ?_ ?_
    · exact Nat.zero_lt_of_lt h
    · exact Fin.is_le'
  have nle2 : n.1 - 2 < L.length := by
    have : n.1 - 2 < n.1 - 1 := by
      refine Nat.sub_succ_lt_self n.1 1 ?_
      exact Nat.lt_of_succ_lt h
    exact Nat.lt_trans this nle1
  have ngt2 : n.1 - 2 > 0 := by exact Nat.zero_lt_sub_of_lt h
  have ngt1 : n.1 - 1 > 0 := by exact Nat.lt_of_lt_pred ngt2
  have l1 : (L.take (n.1 - 2)).length > 0 := by apply (pos_sub_length L nle2 ngt2).1
  have l2 : (L.drop (n.1 - 1)).length > 0 := by apply (pos_sub_length L nle1 ngt1).2
  constructor
  · exact List.length_pos.mp l1
  · exact List.length_pos.mp l2

/-
Lemma : Let P be a poset and L : x_0 < x_1 < ⋯ < x_k be a chain in P with k ≥ 2.
Given some x ∈ P s.t. x_{n-1} < x < x_{n+1} where 0 < n < k, L' : x_0 < ⋯ x_{n-1} < x < x_{n+1} < ⋯ < x_k is also a chain.
-/
lemma exchainge (L : List P) (x : P) (n : Fin L.length) (h : n.1 > 2) (h₀ : chain L) : L[n.1 - 3] < x ∧ x < L[n.1 - 1] → chain (swap_nth L x n) := by
  intro hyp
  let L' := replace_nth L x n
  have : chain L' := by
    let l₁ := L.take (n.1 - 2)
    let l₂ := L.drop (n.1 - 1)
    have ne : l₁ ≠ [] ∧ l₂ ≠ [] := by apply nonempty_split_chain L n h
    have nel : l₁ ++ [x] ≠ [] := by
      refine List.append_ne_nil_of_ne_nil_right l₁ [x] ?_
      simp
    have tail : L[n.1 - 3] = l₁.getLast ne.1 := by exact split_tail L n h ne.1
    have head : L[n.1 - 1] = l₂.head ne.2 := by exact split_head L n h ne.2
    have c : L' = l₁ ++ [x] ++ l₂ := by exact replace_concat L x n h
    have : chain (l₁ ++ [x]) := by
      apply addChain
      constructor
      · exact List.Chain'.take h₀ (n.1 - 2)
      · exact chain_singleton
      · have : [x] ≠ [] := by simp
        have : List.head [x] this = x := by rfl
        rw [tail.symm, this]
        exact hyp.1
        constructor
        · exact ne.1
        · simp
    rw [c]
    apply addChain
    constructor
    · exact this
    · exact List.Chain'.drop h₀ (n.1 - 1)
    · have : List.getLast (l₁ ++ [x]) nel = x := by exact List.getLast_append l₁ nel
      rw [this, head.symm]
      exact hyp.2
      constructor
      · exact nel
      · exact ne.2
  exact this

/-
Definition: Let P and A be posets and l be an edge labelling of P in A.
Then any maximal chain m : x_0 ⋖ x_1 ⋖ ⋯ ⋖ x_n in [x,y] ⊂ P, we define a list in A by [l(x_0 ⋖ x_1),l(x_1 ⋖ x_2), ⋯ ,l(x_{n-1} ⋖ x_n)].
-/
def mapMaxChain_interval (l : edgeLabeling P A) {x y : P} (m : maximalChains <| Set.Icc x y) : List A := List.map (fun e : edges (Set.Icc x y) => l ( sorry
    -- e : edges P
    )) <| edgePairs m

/-Defines the set of risingChains in an interval [x,y]-/
abbrev risingChains (l : edgeLabeling P A) (x y: P) := {m : maximalChains <| Set.Icc x y | List.Chain' (. ≤ .) <| mapMaxChain_interval l m}

/-
Definition: An edge labelling of P is called an EL-labelling if for every interval [x,y] in P,
  (1) there is a unique increasing maximal chain c in [x,y],
  (2) c <_L c' for all other maximal chains c' in [x,y].
Here <_L denotes the lexicographic ordering for the tuples in the labelling poset A.
-/
class ELLabeling (l : edgeLabeling P A) where
  unique {x y: P} (h : x<y) : Unique (risingChains l x y)
  unique_min {x y: P} (h : x<y): ∀ (m' : maximalChains <| Set.Icc x y), m' ≠ (unique h).default → (mapMaxChain_interval l (unique h).default.val < mapMaxChain_interval l m')

/- define lexicographical index as inductive type; want to unravel the above; use bottom element -/

open AbstractSimplicialComplex
open List Classical

def diff_max_chain (k m : List P) (h : k < m) (h₀ : maximal_chain k ∧ maximal_chain m) : ℕ := sorry
/- k[j] < m[j] ∧ ∀ i : Fin j, k[i] = m[i] -/

/-
Lemma : Let P be a graded finite poset with an EL-labelling l to a poset A.
Then for any two maximal chains s.t. k < m, there exists a maximal chain c such that its list is less than the list of m in A, and k ∩ m ⊆ c ∩ m
-/

lemma min_max_chain [GradedPoset P] (k m : List P) (l : edgeLabeling P A) (h : ELLabeling l) (h₀ : maximal_chain k ∧ maximal_chain m) : k < m → ∃ c : List P, maximal_chain c ∧ k ∩ m ⊆ c ∩ m := by
  intro klem
  sorry

/-
Theorem: Let P be a graded finite poset with an EL-labelling l to a poset A. Then P is shellable.
-/
theorem shellable_of_ELLabeling [GradedPoset P] (l : edgeLabeling P A) (h: ELLabeling l) (k m : List P): ShellableDelta P := by
  have : Shellable (Delta P) := by
    apply (shellable_iff_shellable').mpr
    letI : Nonempty {L // L ∈ maximalChains P} := by
      have : ∃ L : List P, maximal_chain L := by apply exist_maximal_chain
      rcases this with ⟨L, mc⟩
      use L
      simp
      exact mc
    let r := rank P
    have len : ∀ L ∈ maximalChains P, L.length = r := by
      intro L mc
      have : rank P = L.length := by
        apply GradedPoset.rank_def L
        exact mc
      exact id this.symm
    constructor
    · have mchains : maximal_chain k ∧ maximal_chain m := by sorry
      have klem : k < m := by sorry
      have newmc : ∃ c : List P, maximal_chain c ∧ k ∩ m ⊆ c ∩ m := by apply min_max_chain k m l h mchains klem
      sorry
    · use (maximalChains P).card
      refine Finset.card_pos.mpr ?_
      simp
      apply exist_maximal_chain
  exact this

   /- have : ShellableDelta P iff -/
  /- have Delta.ASC (P) -/

  /- rw goal as ShellableDelta P → Shellable (Delta P) → Shellable' (Delta P) i.e. ∃ (m : ℕ+) (l : Fin m ≃ Facets Delta P), Shelling' l -/

  /- fix map l from labelling -/

  /- let k : k_0 ⋖ k_1 ⋖ ⋯ ⋖ k_r, m : m_0 ⋖ m_1 ⋖ ⋯ ⋖ m_r be two maximal chains s.t. k < m -/

  /- let d be the greatest integer s.t. kᵢ = mᵢ for i ∈ [0, d], and g the greatest integer s.t. d < g and k_g = m_g -/

  /- then for the interval [m_g, m_d], m_d ⋖ ⋯ ⋖ m_g is not the unique max chain  -/

  /- ∃e ∈ (d, g) s.t. l(m_{e-1} ⋖ m_e) > l(m_e ⋖ m_{e+1})  -/

  /- have a unique increasing max chain in [m_{e-1}, m_{e+1}] : m_{e-1} ⋖ x ⋖ m_{e+1} -/

  /- then c : m_0 ⋖ ⋯ ⋖ m_{e-1} ⋖ x ⋖ m_{e+1} ⋖ ⋯ ⋖ m_r satisfies Shelling' l -/

  /- 'gluing' chains lemma, compare chains -/

end PartialOrder
