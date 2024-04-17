import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.List.Lex
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Chain
import Mathlib.Order.Cover
import Mathlib.Tactic.Linarith.Frontend
import Coxeter.ForMathlib.AdjacentPair


namespace PartialOrder
/- Let P be a finite poet. -/
variable {P : Type*} [PartialOrder P]


/- Recall that : We say a is covered by b if x < y and there is no element z such that x < z < y. -/

/- Defintion: We define the set of edges of P as the set of all pairs (a,b) such that a is covered by b.-/
def edges (P : Type*) [PartialOrder P] : Set (P × P) := {(a, b) | a ⋖ b }


/-
Definition: A chain in the poset P is a finite sequence x₀ < x₁ < ⋯ < x_n.
-/
abbrev chain (L : List P) : Prop := List.Chain' (· < ·) L

abbrev Chains (P : Type*) [PartialOrder P] : Set (List P) := { L | chain L}

section chain

attribute [-instance] List.instLEList
attribute [-instance] List.LT'
attribute [-instance] List.instLTList

/-
instance: The set of all chains in P admits a partial ordering by set-theoretical inclusion.
-/
instance poset_chain {P : Type*} [PartialOrder P] : PartialOrder (Chains P) where
  le := fun C₁ C₂ => C₁.val.Sublist C₂.val
  le_refl := by simp
  le_trans := fun _ _ _ h1 h2 ↦ List.Sublist.trans h1 h2
  le_antisymm := fun _ _ h1 h2 => Subtype.ext <| List.Sublist.antisymm h1 h2

/-
instance: The set of all chains in P is a lattice.
-/
instance lattice_chain {P : Type*} [PartialOrder P] : Lattice (Chains P) := sorry

end chain

section maximal_chain

/-
Definition: A chain in the poset P is maximal if it is not a proper subset of any other chains.
In other words, all relations are cover relations with x_0 being a minimal element and x_n be a maximal element.
-/

abbrev maximal_chain (L: List P) : Prop := chain L ∧
  ∀ L' : List P, chain L' -> List.Sublist L L' -> L = L'

/-
We also define the notion of maximal_chain' in the sense that if for any chain L' whose head and tail are the same as that of L, then L is sublist of L' implies L = L'.
 -/
abbrev maximal_chain' (L: List P) : Prop := chain L ∧ ∀ L' : List P, chain L' → (L.head? = L'.head? ∧ L.getLast? = L'.getLast?) → List.Sublist L L' -> L = L'

/-
Lemma: If a chain L in P is maximal, then its adjacent relations are cover relations.
-/
lemma maximal_chain'_of_maximal_chain {L: List P} : maximal_chain L → maximal_chain' L := by
  intro h
  constructor
  . exact h.1
  . intro L' hL' _ h2
    exact h.2 L' hL' h2

/-
Lemma: A singleton is a chain by definition.
-/
lemma chain_singleton {a : P} : chain [a] := by simp

lemma chain_singleton_of_head_eq_tail  {L : List P} (a : P) : chain L → L.head? = some a → L.getLast? = some a → L.length = 1  := by
  sorry

lemma maximal_chain'_singleton {a : P}: maximal_chain' [a] := by
  sorry


lemma maximal_chain'_nil : maximal_chain' ([] : List P) := by
  constructor
  . simp
  . intro L' hL' h1 h2
    have : L'.head? = none := by simp [<-h1.1]
    cases L'
    . simp
    . simp at this


lemma maximal_chain'_head {a b: P} {tail : List P} : maximal_chain' (a :: b :: tail) → a ⋖ b := by
  apply Function.mtr
  intro h H
  have hab : a < b := (List.chain'_cons.1 H.1).1
  obtain ⟨c, hc1⟩ := (not_covBy_iff hab).1 h
  let L' := a :: c :: b :: tail
  have chainL' : chain L' := by
    rw [ (by simp : L' = [a,c] ++ b:: tail)]
    apply (List.chain'_split (a := b) (l₂ := tail)).2
    constructor
    . simp [hc1]
    . exact (List.chain'_cons.1 H.1).2
  have hL' : List.Sublist (a :: b :: tail) L' := by
    apply  List.cons_sublist_cons.2
    apply  List.sublist_cons
  have neqL' : a :: b :: tail ≠ L' := by
    intro h
    rw [List.cons_eq_cons,List.cons_eq_cons] at h
    exact List.cons_ne_self _ _ (Eq.symm h.2.2)
  exact H.2 L' chainL' ⟨rfl, rfl⟩ hL' |> neqL'


lemma maximal_chain'_tail {a : P} {tail : List P} : maximal_chain' (a :: tail) → maximal_chain' tail := by
  rintro ⟨C, MAX⟩
  cases tail with
  | nil => exact maximal_chain'_nil
  | cons b t =>
  constructor
  . exact List.Chain'.tail C
  . intros L' hL' h1 h2
    let tail := b ::t
    let L'' := a :: L'
    have chainL'' : chain L'' := by
      apply List.chain'_cons'.2
      constructor
      . intro t ht
        rw [<-h1.1] at ht
        have : b=t := by simp [List.head?_cons] at ht; exact ht
        rw [<-this]
        exact (List.chain'_cons.1 C).1
      . exact hL'
    have htL''1 : (a :: tail).head? = L''.head?  := by simp
    have htL''2 : (a :: tail).getLast? = L''.getLast? := by
      cases L' with
      | nil => simp at h2
      | cons c d =>
        simp only [List.getLast?_cons_cons, h1.2]
    have sublistL'' : List.Sublist (a :: tail) L'' := by
      apply List.cons_sublist_cons.2
      exact h2
    have : a :: tail = L'' := MAX L'' chainL'' ⟨htL''1, htL''2⟩ sublistL''
    exact (List.cons_eq_cons.1 this).2

lemma maximal_chain'_cons {a b : P} {L : List P} : maximal_chain' (b :: L) → a ⋖ b → maximal_chain' (a :: b :: L) := by sorry

/-
Lemma: A pair of element is a maximal chain if and only if the pair is a cover relation.
-/
lemma maximal_chain'₂_iff_ledot {a b : P} : maximal_chain' [a,b] ↔ (a ⋖ b) := by sorry

/-
Lemma: If a chain L : x₀ < x₁ < ⋯ < x_n is maximal', then we have x_0 ⋖ x_1 ⋖ x_2 ⋯ ⋖ x_n.
-/
lemma cover_chain_of_maximal_chain' {P : Type*} [PartialOrder P] {L: List P} :
  maximal_chain' L → List.Chain' (· ⋖ ·) L := by
  intro h
  induction' L with a t ih
  . simp
  . match t with
    | [] => simp
    | b :: t' =>
      apply List.chain'_cons.2
      exact ⟨maximal_chain'_head h, ih (maximal_chain'_tail h)⟩



/-
Lemma: If a chain L : x₀ < x₁ < ⋯ < x_n is maximal, then we have x_0 ⋖ x_1 ⋖ x_2 ⋯ ⋖ x_n.
-/
lemma maximal_chain_cover {P : Type*} [PartialOrder P] {L: List P} :
  maximal_chain L → List.Chain' (· ⋖ · ) L := fun h =>
  cover_chain_of_maximal_chain' <| maximal_chain'_of_maximal_chain h


/-
Lemma: Assume P is a bounded poset. Let L : x₀ < x₁ < ⋯ < x_n  be a chain of P
such that the adjacent relations are cover relations; x_0 is the minimal element and x_n is the maximal element.
Then L is a maximal chain.
-/
lemma maximal_chain'_of_cover_chain {P :Type*} [PartialOrder P]  {L: List P} :
  List.Chain' (· ⋖ ·) L → maximal_chain' L := by sorry

/-
Lemma: Assume P is a bounded poset. Let L : x₀ < x₁ < ⋯ < x_n  be a chain of P
such that the adjacent relations are cover relations; x_0 is the minimal element and x_n is the maximal element.
Then L is a maximal chain.
-/
lemma maximal_chain_of_cover_chain {P :Type*} [PartialOrder P] [BoundedOrder P] {L: List P} :
  List.Chain' (· ⋖ · ) L ∧ L.head? = some ⊥ ∧ L.getLast? = some ⊤ → maximal_chain L := by
  rintro ⟨h1, h2, h3⟩
  by_contra h4
  rw [maximal_chain] at h4
  push_neg at h4
  sorry


/- Definition: We say a poset P is bounded, if it has a unique minimal and a unique maximal element. -/
/-
Lemma: Let P be a bounded finite poset. Then a maximal chain exsits.
-/
lemma exist_maximal_chain {P : Type*} [PartialOrder P] [BoundedOrder P] [Fintype P] :
  ∃ L : List P, maximal_chain L := by sorry


/-
(Programming) Note that the assumption that P is a BoundedOrder implies that P is nonempty, and so a maximal chain is nonempty.
-/
lemma maximal_chain_nonempty {P : Type*} [PartialOrder P] [BoundedOrder P]  [Fintype P] (L: List P) :
  maximal_chain L → L ≠ [] := by
  intro h1
  by_contra h2
  rw [h2] at h1
  simp only [maximal_chain] at h1
  have h3 : List.Sublist [] (⊥ :: []) := by
    apply List.nil_sublist ((⊥ : P) :: [])
  have h4 : chain (⊥ :: []) := by
    exact List.chain'_singleton (⊥ : P)
  have h5 : [] = (⊥ :: []) := by
    apply h1.2
    · exact h4
    · exact h3
  have h6 : 0 = 1 := by
    rw [←List.length_nil, h5, List.length_singleton]
  linarith

/-
Lemma: Let P be a bounded finite poset. Let L = [x_0, ⋯, x_m] be a list of elements in P.
Then L is a maximal chain if and only if  x_0 is the minimal element, x_n is the maximal element, and x_i ⋖ x_{i+1} for all i.
-/
lemma maximal_chain_iff_cover {P : Type*} [PartialOrder P] [BoundedOrder P]  [Fintype P] (L: List P) :
  maximal_chain L ↔ ((L.head? = (⊥ : P)) ∧ (L.getLast? = (⊤ : P)) ∧ (List.Chain' (· ⋖ · ) L)) := by sorry

/-
Lemma: Let L : x_0 < x_1 < ⋯ < x_n be a maximal chain of P. Then (x_i, x_{i+1}) is an (cover) edge of P.
-/
lemma max_chain_mem_edge {P : Type*} [PartialOrder P] {L: List P} {e: P × P} :
  maximal_chain L →  e ∈ L.adjPairs → e ∈ edges P:= sorry


/-
We define the set of all maximal chains of P.
-/
abbrev maximalChains (P : Type*) [PartialOrder P] : Set (List P) := { L | maximal_chain L }

/-
(Programming)
-/

def edgePairs {P : Type*} [PartialOrder P] (L : maximalChains P) : List (edges P) :=
  List.map (fun e => ⟨e.val, max_chain_mem_edge L.prop  e.prop⟩) <| L.val.adjEPairs

/- Definition: Define rank to be the Sup of the lenghts of all maximal chains.

  Note that if the length is unbounded,then rank = 0.
 -/
noncomputable def rank (P : Type*) [PartialOrder P] : ℕ :=
⨆ L ∈ maximalChains P, L.length


end maximal_chain

-- @[deprecated Set.Icc]
-- def Interval {P : Type*} [PartialOrder P] (x y : P) : Set P := {z | x ≤ z ∧ z ≤ y}

-- instance Interval.bounded {P : Type*} [PartialOrder P] {x y : P} (h : x ≤ y) : BoundedOrder (Set.Icc x y) where
--   top := ⟨y, And.intro h (le_refl y)⟩
--   bot := ⟨x, And.intro (le_refl x) h⟩
--   le_top := fun x ↦ x.2.2
--   bot_le := fun x ↦ x.2.1

-- instance Interval.poset {P : Type*} [PartialOrder P] {x y : P} :
-- PartialOrder (Set.Icc x y) := by exact Subtype.partialOrder _

-- instance Interval.edge_coe {P : Type*} [PartialOrder P] {x y : P} : CoeOut (edges (Set.Icc x y)) (edges P) where
--   coe := fun z => ⟨(z.1.1, z.1.2),sorry ⟩



end PartialOrder
