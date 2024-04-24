import Mathlib.Data.Set.Card
import Coxeter.ForMathlib.AbstractSimplicialComplex

namespace AbstractSimplicialComplex
variable {V : Type*}

/--
Definition: Let `F` be a pure abstract simplicial complex of rank `d + 1` with finite facets.
A shelling of `F` is an linear ordering `l₁`, ⋯ , `lₘ` of all (maximal) facets of F such that
 `lᵢ ⊓ (⨆ {j < i}, lⱼ)`  is an abstract simplicial complex pure of rank `d`.
-/
def Shelling {F : AbstractSimplicialComplex V} {m : ℕ} (l : Fin m ≃ Facets F) := F.rank > 0 ∧
  ∀ k : Fin m, 0 < k.1 → IsPure' ((⨆ j : {j // j < k}, closure {(l j).1}) ⊓ (closure {(l k).1})) (F.rank - 1)

open Classical
/--
Definition': Let `F` be a pure abstract simplicial complex of rank `d + 1`.
A shelling of `F` is an linear ordering `l₁`, ⋯ , `lₘ` of all (maximal) facets of `F` such that
 for any `i < k`, there exists `j < k`, such that `lᵢ ∩ lₖ ⊆ lⱼ ∩ lₖ` and `|lⱼ ∩ lₖ| = d`.
-/
def Shelling' {F :  AbstractSimplicialComplex V} {m : ℕ} (l : Fin m ≃ Facets F) :=
  F.rank > 0 ∧
  ∀ k i : Fin m, i < k → ∃ j : Fin m, j < k ∧
    (closure {(l i).1} ⊓ closure {(l k).1} ≤ closure {(l j).1} ⊓ closure {(l k).1}) ∧
    (closure {(l j).1} ⊓ closure {(l k).1}).rank + 1 = F.rank

/-- Lemma: The two definitions of shellings are equivalent.
-/
lemma shelling_iff_shelling' {F : AbstractSimplicialComplex V}  [hpure: Pure F] {m : ℕ} (l : Fin m ≃ Facets F) :
    Shelling l ↔ Shelling' l := by
    constructor
    · sorry
    · refine fun ⟨a, b⟩ ↦ ⟨a, ?_⟩
      intro k kge0 s hs
      have : ∃j : Fin m, j < k ∧ ∀i : Fin m, i < k → closure {(l i).1} ⊓ closure {(l k).1} ≤ closure {(l j).1} ⊓ closure {(l k).1} := by sorry
      rw [iSup_inf_eq] at hs
      sorry

/-- Definition: An abstract simplicial complex `F` is called shellable, if it admits a shelling. -/
def Shellable (F : AbstractSimplicialComplex F) := ∃ (m : ℕ) (l : Fin m ≃ Facets F), Shelling l

-- lemma cone_Shellabe_iff {F G : AbstractSimplicialComplex V} {r : ℕ} [Pure F] [Pure G] (x : V) (hcone: Cone F G x) :
--   Shellable F ↔ Shellable G  := by sorry

end AbstractSimplicialComplex
