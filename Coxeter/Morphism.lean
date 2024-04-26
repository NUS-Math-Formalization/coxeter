import Coxeter.CoxeterMatrix.CoxeterMatrix'

open OrderTwoGen

variable {G : Type*} [Group G] {S : Set G} [hS: CoxeterSystem S]
--variable {G' : Type*} [Group G'] {S' : Set G'} [hS: CoxeterSystem S']


namespace CoxeterMatrix
variable {α} {m : Matrix α α ℕ} [hm : CoxeterMatrix m] {x : α}

def of_eq  {x:α} : of m x  = (PresentedGroup.of x :toGroup m) := by rfl

end CoxeterMatrix


noncomputable section



namespace CoxeterSystem

variable {M: Type*} [Monoid M]

def reducedWords (w : G) := { L : List S| w = L ∧ reduced_word L}

namespace monoidLift
def alpha (f : S → M) (s s' : S) : M := if orderOf ((s :G) * s') = 0 then 1 else
 (f s * f s')^(orderOf ((s :G) * s') /2 ) * (f s')^(orderOf ((s :G) * s') % 2)

lemma alpha.zero {f : S → M} {s s' :S} :
  orderOf ((s:G) * s') =0 → alpha f s s' = 1 := by
  intro h; simp only [↓alpha,↓h,↓reduceIte]

lemma alpha.even {f : S → M} {s s' :S} {l : ℕ} :
  orderOf ((s:G) * s') = 2*l → alpha f s s' = (f s * f s')^l := by sorry

lemma alpha.odd {f : S → M} {s s' :S} {l : ℕ} :
  orderOf ((s:G) * s') = 2*l+1 → alpha f s s' = (f s * f s')^l*f s' := by sorry


def constant (f : S → M) (h : ∀ s s', alpha f s s' = alpha f s' s) :
  ∀ w:G,  ∀ L L' : List S, L ∈ reducedWords w → L' ∈ reducedWords w →
    List.prod (L.map f) = List.prod  (L'.map f) := by sorry

lemma aux_symm_of_power {f : S → M} {s s' :S } : (f s * f s')^orderOf ((s :G) * s') = 1 ↔ alpha f s s' = alpha f s' s := by sorry

def mapLift {f : S → M} (h : ∀ s s', (f s * f s')^orderOf ((s :G) * s') = 1) :
  G →* M where
    toFun := fun w => List.prod <| (choose_reduced_word S w).map f
    map_one' := by sorry
    map_mul' := by sorry

lemma mapLift.of {f : S → M} {h : ∀ s s', (f s * f s')^orderOf ((s :G) * s') = 1} (s:S) :
  mapLift h s = f s := by sorry


end monoidLift

open CoxeterMatrix

@[simp]
abbrev toMatrix (S : Set G) [CoxeterSystem S] : Matrix S S ℕ := fun s t => orderOf (s.1*t.1)

instance CoxeterMatrix {S:Set G} [CoxeterSystem S]: CoxeterMatrix (toMatrix S) where
  symmetric := by sorry
  oneIff := by sorry

namespace Presentation


def map_aux (S:Set G) [CoxeterSystem S]: ∀ (s t : S), ((fun s => (s:G) ) s * (fun s => (s:G)) t) ^ toMatrix S s t = 1 := by  intro s t; rw [toMatrix,pow_orderOf_eq_one]

@[simp]
def map (S:Set G) [CoxeterSystem S] : CoxeterMatrix.toGroup (toMatrix S) →* G := CoxeterMatrix.lift (toMatrix S) (fun s => s.1)
  (map_aux S)

#check PresentedGroup.toGroup.of

lemma map.of_eq {S:Set G} [CoxeterSystem S] (s:S) : map S s = s := by
  simp_rw [map,CoxeterMatrix.lift,CoxeterMatrix.of_eq]
  have h : ∀ r ∈ toRelationSet (toMatrix S), (FreeGroup.lift fun (s:S) => (s:G) ) r = 1 := CoxeterMatrix.liftHom_aux (toMatrix S) (fun s => (s:G)) (map_aux S)
  calc
    _ = (fun (s:S) => (s:G)) s := PresentedGroup.toGroup.of h
    _ = s := by rfl

local notation "m" => (toMatrix S)
local notation "G'" => CoxeterMatrix.toGroup (toMatrix S)
local notation "S'" => CoxeterMatrix.SimpleRefl (toMatrix S)
--local notation "N" => Subgroup.normalClosure (toRelationSet m)

def invmap (S:Set G) [CoxeterSystem S] : G →* CoxeterMatrix.toGroup (toMatrix S) := monoidLift.mapLift (CoxeterMatrix.of_relation (toMatrix S))

lemma invmap.of_eq {S:Set G} [CoxeterSystem S] {s :S} : invmap S s = s := by
  sorry

def invmap_map_eq_id : MonoidHom.comp (invmap S)  (map S) = MonoidHom.id G':= by
  ext x
  have h : ∀ r ∈ toRelationSet m, (FreeGroup.lift fun (s:S) => CoxeterMatrix.of m s) r = 1 := by sorry
  calc
  _ = PresentedGroup.toGroup h x := by
    apply PresentedGroup.toGroup.unique h --(MonoidHom.id G')
    intro s
    simp_rw [MonoidHom.comp_apply,<-CoxeterMatrix.of_eq]
    calc
    _ = invmap S s := by congr; exact map.of_eq s
    _ = _ := invmap.of_eq
  _ = MonoidHom.id G' x := by
    apply Eq.symm
    apply PresentedGroup.toGroup.unique h --(MonoidHom.id G')
    intro x
    simp_rw [CoxeterMatrix.of_eq,CoxeterMatrix.toGroup,MonoidHom.id_apply]


lemma invmap_injective : Function.Injective (invmap S) := by sorry


lemma invmap_surjective : Function.Surjective (invmap S) := by
  sorry

lemma invmap_bijective : Function.Bijective (invmap S) := ⟨invmap_injective,invmap_surjective⟩



def equiv : G ≃* G' := MulEquiv.ofBijective _ invmap_bijective


def equiv.SimpleRefl : S ≃ S' where
  toFun := fun s => ⟨s,by sorry⟩
  invFun := fun s => ⟨map S s.1, by sorry⟩
  left_inv := by sorry
  right_inv := by sorry

lemma equiv.SimpleRefl.def (s : S) : (equiv.SimpleRefl s).val = equiv s.val := by
  simp_rw [equiv.SimpleRefl,equiv,<-invmap.of_eq]
  dsimp

def equiv.Refl : Refl S ≃ Refl S'  where
  toFun := fun t => ⟨equiv t,by sorry⟩
  invFun := fun t => ⟨map S t.1, by sorry⟩
  left_inv := by sorry
  right_inv := by sorry

lemma equiv.Refl.def  (t : OrderTwoGen.Refl S)  : (equiv.Refl t).val = equiv t.val := by
  rw [Refl]; dsimp

@[simp]
lemma gprod_eq (L : List S) : @equiv _ _ _ hS (L:G) = L.map equiv.SimpleRefl := by sorry

local notation : max "ℓ(" g ")" => (OrderTwoGen.length S g)

local notation : max "ℓ'(" g ")" => (OrderTwoGen.length S' g)

lemma reduced_iff (L : List S) : reduced_word L ↔ reduced_word (L.map equiv.SimpleRefl) := by sorry

lemma length_eq (g :G) : ℓ(g) = ℓ'(equiv g) := by sorry


theorem _root_.CoxeterSystem.strong_exchange : ∀ (L : List S) (t : Refl S), ℓ((t:G) * L) < ℓ(L) →
  ∃ (i : Fin L.length), (t : G) * L = (L.removeNth i) := by
  intro L t hl
  set L' :=  L.map equiv.SimpleRefl
  have hl0 :L'.length = L.length := by simp only [List.length_map]
  set t' := equiv.Refl t
  have hl1 : ℓ'(t'.val * L') = ℓ(t.val * L) := by sorry
  have hl2 : ℓ'(L') = ℓ(L) := by sorry
  have hl' : ℓ'(t'.val * L') < ℓ'(L') := by sorry
  obtain ⟨i, hi⟩:= CoxeterMatrix.strong_exchange L' t' hl'
  let i' : Fin L.length := ⟨i.val, by simp_rw [<-hl0,i.prop]⟩
  use i'
  apply (MulEquiv.apply_eq_iff_eq <| @equiv _ _ _ hS).1
  simp only [map_mul,gprod_eq,<-equiv.Refl.def,hi,List.map_removeNth_comm]

end Presentation

-- Better to establish properties of morphisms between Coxeter systems

noncomputable section Morphism
variable {H : Type*} [Group H] {S' : Set H} [hS': CoxeterSystem S']

class Morphism {G:Type*} [Group G] {S : Set G} [CoxeterSystem S] {H :Type*} [Group H] {S' : Set H} [CoxeterSystem S']
(f : S → S') where
  preservesOrder : ∀ s1 s2: S, orderOf (s1.val * s2) = orderOf ((f s1).val * (f s2))

namespace Morphism

lemma relation (f: S → S') [Morphism f] :
  ∀ s1 s2, ((fun s => (f s).val) s1 * (fun s => (f s).val ) s2)^(orderOf (s1.val*s2))= 1 := by sorry

def toGroupHom (f : S → S') [Morphism f]  : G →* H := monoidLift.mapLift (relation f)



end Morphism

end Morphism



end CoxeterSystem
