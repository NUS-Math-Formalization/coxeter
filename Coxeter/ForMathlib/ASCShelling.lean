--import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card
import Coxeter.ForMathlib.AbstractSimplicialComplex




namespace AbstractSimplicialComplex
variable {V : Type*} --[DecidableEq V]

/-
Definition: Let F be a pure abstract simplicial complex of rank d+1.
A shelling of F is an linear ordering l_1, ⋯ , l_m of all (maximal) facets of F such that
 l_i ⊓ (⨆ {j < i}, l_j)  is an abstract simplicial complex pure of rank d.
-/

def shelling {F : AbstractSimplicialComplex V} [hpure: Pure F] {m : ℕ } (l : Fin m ≃ Facets F) := F.rank > 0 ∧
  ∀ i : Fin m, 1 < i.val → IsPure' ((⨆ j ∈ {j | j<i}, closure {(l j).val}) ⊓ (closure {(l i).val})) (F.rank-1)


/-
Definition': Let F be a pure abstract simplicial complex of rank d+1.
A shelling of F is an linear ordering l_1, ⋯ , l_m of all (maximal) facets of F such that
 for any i < k, there exists j < k, such that l_i ∩ l_k ⊆ l_j ∩ l_k and |l_j ∩ l_k| = d.
-/
def shelling' [DecidableEq V] {F :  AbstractSimplicialComplex V} [hpure:Pure F]  {m : ℕ } (l : Fin m ≃ Facets F) :=
  F.rank > 0 ∧
  ∀ k i : Fin m, i < k → ∃ j : Fin m, j < k ∧
    ((l i).val ∩ (l k).val ⊆ (l j).val ∩ (l k).val) ∧
    ((l j).val ∩ (l k).val).card + 1 = F.rank


/- Lemma: The two definitions of shellings are equivalent.
-/
lemma shelling_iff_shelling' [DecidableEq V] {F : AbstractSimplicialComplex V}  [hpure: Pure F]    {m : ℕ} (l : Fin m ≃ Facets F) :
    shelling l ↔ shelling' l := by sorry

/- Definition: An abstract simplicial complex F is called shellable, if it admits a shelling.
-/
def shellable (F : AbstractSimplicialComplex F) [Pure F] := ∃ (m: ℕ) (l : Fin m ≃ Facets F), shelling l

lemma cone_shellabe_iff [DecidableEq V] {F G : AbstractSimplicialComplex V} {r : ℕ} [Pure F] [Pure G] (x : V)  (hcone: Cone F G x) :
  shellable F ↔ shellable G  := by sorry

end AbstractSimplicialComplex
