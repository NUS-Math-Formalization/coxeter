import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Subgroup.Basic

open Classical

variable {G : Type _} [Group G] {S: Set G}

@[simp]
def List.gprod {S : Set G} (L : List S) := (L : List G).prod 

class orderTwoGen {G : Type _}[Group G] (S:outParam (Set G))where 
  order_two :  ∀ (x:G) , x ∈ S →  x * x = (1 :G) ∧  x ≠ (1 :G)  
  expression : ∀ (x:G) , ∃ (L : List S),  x = L.gprod 

def expressionSet (g:G) [orderTwoGen S]:= {L:List S| g = L.gprod}

#check List S
#check Set.Elem S
#check Set S
#check orderTwoGen

variable [orderTwoGen S]

lemma eqSubsetProd [orderTwoGen S] (g : G) : ∃ (L : List S),  g = L.gprod := by {
    have H:= @orderTwoGen.expression G  _ S _ g   
    exact H
   }

@[simp]
def reduced_word (L : List S) := ∀ (L' : List S),  L.gprod =  L'.gprod →  L.length ≤ L'.length

def length_aux (g : G) [orderTwoGen S]: ∃ (n:ℕ) , ∃ (L : List S), L.length = n ∧ g = L.gprod := by
  let ⟨L,hL⟩ := @orderTwoGen.expression G _ S _ g
  use L.length,L

#check length_aux 

noncomputable def length (x : G): ℕ := Nat.find (@length_aux G _ S x _) 

#check length

local notation :max "ℓ(" g ")" => (@length G  _ S _ g)

def T (S:Set G):= {x:G| ∃ (w:G)(s:S) , x = w*(s:G)*w⁻¹}

def T_L (w:G):= {t ∈ T S | ℓ(t*w) < ℓ(w)}
def T_R (w:G):= {t ∈ T S | ℓ(w*t) < ℓ(w)}

def D_L (w:G):= T_L w ∩ S
def D_R (w:G):= T_R w ∩ S
#check T

def StrongExchangeProp:= ∀ (L:List S) (t: T S) ,ℓ(t*L.gprod) < ℓ(L.gprod) → ∃ (i:Fin L.length), t * L.gprod = (L.removeNth i).gprod

def ExchangeProp := ∀ (L:List S) (s:S) ,reduced_word L →  
      ℓ((s * L.gprod)) ≤ ℓ(L.gprod) → ∃ (i: Fin L.length) ,s * L.gprod = (L.removeNth i).gprod

def DeletionProp := ∀ (L:List S),ℓ(L.gprod) < L.length → ∃ (j: Fin L.length), ∃ (i:Fin j), L.gprod = ((L.removeNth j).removeNth i).gprod


class CoxeterSystem (G : Type _) (S : Set G) [Group G] [orderTwoGen S] where 
  exchange : @ExchangeProp G _ S _
  deletion : @DeletionProp G _ S _



