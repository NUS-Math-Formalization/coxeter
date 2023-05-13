import Mathlib.Data.List.Basic
import Mathlib.Data.Subtype
import Mathlib.Data.Set.Basic

variable {G : Type _} {S : Set G}

#check Coe (List ↑S) (List G)

def mapList : List (↑S) → List G  
| []    => [] 
| a:: as => a.val :: mapList as

instance (priority := low) list_coe {G : Type _} {S : Set G} : CoeTC (List (↑S)) (List G) where 
coe (L : List ↑S) := @mapList G S L 

lemma coe_eq_coe  {hd : ↑S} {tail :   List ↑S} : (hd :: tail : List G) = hd.1 :: (tail : List G) := by {
  simp
}

 