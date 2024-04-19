--import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card
import Coxeter.ForMathlib.AbstractSimplicialComplex

namespace AbstractSimplicialComplex
variable {V : Type*} --[DecidableEq V]

/--
Definition: Let `F` be a pure abstract simplicial complex of rank `d + 1` with finite facets.
A shelling of `F` is an linear ordering `l₁`, ⋯ , `lₘ` of all (maximal) facets of F such that
 `lᵢ ⊓ (⨆ {j < i}, lⱼ)`  is an abstract simplicial complex pure of rank `d`.
-/
def Shelling {F : AbstractSimplicialComplex V} [hpure : Pure F] {m : ℕ} (l : Fin m ≃ Facets F) := F.rank > 0 ∧
  ∀ i : Fin m, 1 < i.val → IsPure' ((⨆ j : {j // j < i}, closure {(l j).val}) ⊓ (closure {(l i).val})) (F.rank - 1)

/--
Definition': Let `F` be a pure abstract simplicial complex of rank `d + 1`.
A shelling of `F` is an linear ordering `l₁`, ⋯ , `lₘ` of all (maximal) facets of `F` such that
 for any `i < k`, there exists `j < k`, such that `lᵢ ∩ lₖ ⊆ lⱼ ∩ lₖ` and `|lⱼ ∩ lₖ| = d`.
-/
def Shelling' [DecidableEq V] {F :  AbstractSimplicialComplex V} [hpure : Pure F] {m : ℕ} (l : Fin m ≃ Facets F) :=
  F.rank > 0 ∧
  ∀ k i : Fin m, i < k → ∃ j : Fin m, j < k ∧
    ((l i).val ∩ (l k).val ⊆ (l j).val ∩ (l k).val) ∧
    ((l j).val ∩ (l k).val).card + 1 = F.rank

/-- Lemma: The two definitions of shellings are equivalent.
-/
lemma shelling_iff_shelling' [DecidableEq V] {F : AbstractSimplicialComplex V}  [hpure: Pure F]    {m : ℕ} (l : Fin m ≃ Facets F) :
    Shelling l ↔ Shelling' l := by
    constructor
    · refine fun a ↦ ⟨a.1, ?_⟩
      intro k i ilek
      sorry
    · refine fun a ↦ ⟨a.1, ?_⟩
      intro i ige1
      sorry

/-- Definition: An abstract simplicial complex `F` is called shellable, if it admits a shelling. -/
def Shellable (F : AbstractSimplicialComplex F) [Pure F] := ∃ (m: ℕ) (l : Fin m ≃ Facets F), Shelling l

lemma cone_Shellabe_iff [DecidableEq V] {F G : AbstractSimplicialComplex V} {r : ℕ} [Pure F] [Pure G] (x : V)  (hcone: Cone F G x) :
  Shellable F ↔ Shellable G  := by sorry

end AbstractSimplicialComplex
