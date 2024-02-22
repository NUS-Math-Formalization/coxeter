import Coxeter.CoxeterMatrix1


variable {G : Type*} [Group G] {S : Set G} [hS: CoxeterSystem S]

noncomputable section
namespace CoxeterSystem
open CoxeterMatrix

@[simp]
abbrev toMatrix (S : Set G) [CoxeterSystem S] : Matrix S S ℕ := fun s t => orderOf (s.1*t.1)

instance isCoxeterMatrix {S:Set G} [CoxeterSystem S]: CoxeterMatrix (toMatrix S) where
  symmetric := by sorry
  oneIff := by sorry

namespace Presentation

@[simp]
def map (S:Set G) [CoxeterSystem S] : CoxeterMatrix.toGroup (toMatrix S) →* G := CoxeterMatrix.lift (toMatrix S) (fun s => s.1)
 ( by intro s t; rw [toMatrix,pow_orderOf_eq_one])

local notation "m" => (toMatrix S)
local notation "G'" => CoxeterMatrix.toGroup m
local notation "N" => Subgroup.normalClosure (toRelationSet m)

lemma map_injective : Function.Injective (map S) := by sorry

lemma map_surjective : Function.Surjective (map S) := by sorry

lemma map_bijective : Function.Bijective (map S) := ⟨map_injective,map_surjective⟩

def equiv : G' ≃ G := Equiv.ofBijective _ map_bijective


-- Better to establish properties of morphisms between Coxeter systems


end Presentation

end CoxeterSystem
end
