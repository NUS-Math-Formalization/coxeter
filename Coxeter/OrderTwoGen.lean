import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.IntervalCases

import Coxeter.Aux_
open Classical

section CoeM
universe u
variable {α β : Type u}  [(a :α) -> CoeT α a β]

lemma coeM_nil_eq_nil : (([] : List α) : List β) = ([]:List β)  := by rfl


@[simp]
lemma coeM_cons {hd : α} {tail : List α} :
  ( (hd::tail : List α) : List β) = (hd : β) :: (tail : List β) := by rfl


@[simp]
lemma coeM_append {l1 l2: List α} :
  ((l1 ++ l2): List β) = (l1 : List β ) ++ (l2 : List β ) := by
  simp only [Lean.Internal.coeM, List.bind_eq_bind, List.append_bind]


@[simp]
lemma coeM_reverse {l: List α} : (l.reverse: List β) = (l: List β ).reverse := by
  induction l with
  | nil  => trivial
  | cons hd tail ih => simp; congr

@[simp]
lemma mem_subtype_list {x : α} {S : Set α} {L : List S}: x ∈ (L : List α) → x ∈ S := by {
  intro H
  induction L with
  | nil => trivial
  | cons hd tail ih => {
    simp only [coeM_cons, List.mem_cons] at H
    cases H with
    | inl hh => {
      have :CoeT.coe hd = (hd :α) := rfl
      simp only [hh, this, Subtype.coe_prop]
    }
    | inr hh => {exact ih hh}
  }
}

end CoeM


section list_properties

variable {G : Type _} [Group G] {S: Set G}

noncomputable instance HasBEq : BEq S where
  beq := fun s1 s2 => (s1:G) = s2

@[coe]
abbrev List.gprod {S : Set G} (L : List S) := (L : List G).prod

instance List.ListGtoGroup : CoeOut (List G) G where
  coe := fun L => (L : List G).prod

instance List.ListStoGroup : CoeOut (List S) G where
  coe := fun L => L.gprod

lemma gprod_nil : ([]: List S) = (1 : G):=by exact List.prod_nil

lemma gprod_singleton {s : S}: ([s] : G) = s := by
  calc
   _ = List.prod [(s:G)] := by congr
   _ = ↑s := by simp

lemma gprod_eq_of_list_eq {L1 L2 : List S} (h : L1 = L2) : (L1 : G) = (L2 : G) := by rw [h]

-- Some automation regarding List S
--instance HasHMulListList : HMul (List S) (List S) (List S) where
--  hMul := fun L1 L2 => (L1 ++ L2 : List S)

instance HasHMulListS : HMul (List S) S G where
  hMul := fun L g => (L : G) * g

instance HasHMulGList : HMul G (List S) G where
  hMul := fun g L => g * (L : G)

lemma gprod_cons (hd : S)  (tail : List S) : (hd::tail :G) = hd * (tail :G) := by {
  simp_rw [←List.prod_cons]
  congr
}

@[simp]
lemma gprod_append {l1 l2: List S} : (l1 ++ l2 : G) = l1 * l2 := by {
  rw [←List.prod_append]
  congr
  simp [List.gprod, Lean.Internal.coeM]
}

@[simp]
lemma gprod_append_singleton {l1 : List S} {s : S}: (l1 ++ [s] : G) = l1 * s := by {
  rw [←gprod_singleton, gprod_append]
}



@[simp]
abbrev inv_reverse (L : List S) : List G := (List.map (fun x => (x:G)⁻¹) L).reverse

lemma gprod_inv_eq_inv_reverse (L: List S) : (L :G)⁻¹ = inv_reverse L   := by rw [List.prod_inv_reverse]


lemma inv_reverse_prod_prod_eq_one {L: List S}  : inv_reverse L * (L :G) = 1 :=
  by simp [←gprod_inv_eq_inv_reverse]

end list_properties



class OrderTwoGen {G : Type*} [Group G] (S: Set G) where
  order_two :  ∀ (x:G) , x ∈ S →  x * x = (1 : G) ∧ x ≠ (1 :G)
  expression : ∀ (x:G) , ∃ (L : List S),  x = L.gprod

namespace OrderTwoGen

variable {G : Type _} [Group G] {S: Set G} [h:OrderTwoGen S]

@[simp]
lemma gen_square_eq_one : ∀ x∈S, x * x = 1:=fun x hx => (h.order_two x hx).1

@[simp]
lemma gen_square_eq_one' (s:S): (s:G) * s = 1:= by simp [gen_square_eq_one s.1 s.2]

@[simp]
lemma inv_eq_self [h : OrderTwoGen S]: ∀ x : G,  x ∈ S → x = x⁻¹ :=
fun x hx => mul_eq_one_iff_eq_inv.1 (h.order_two x hx).1

@[simp]
lemma inv_eq_self' : ∀ (x : S),  x = (x:G)⁻¹ := fun x =>  inv_eq_self x.1 x.2

@[simp]
lemma inv_eq_self'' : ∀ (x : S), (x:G)⁻¹ = x := fun x =>  Eq.symm (inv_eq_self x.1 x.2)

-- The lemma was called non_one
lemma gen_ne_one : ∀ x∈S, x ≠ 1 :=
fun x hx => (h.order_two x hx).2

lemma gen_ne_one' : ∀ (x:S),  (x :G) ≠ 1 :=
fun x => gen_ne_one x.1 x.2


--lemma mul_generator_inv {s:S} {w:G} [orderTwoGen S]: (w*s)⁻¹ = s*w⁻¹:= by rw []

lemma inv_reverse_eq_reverse (L : List S) :  (L.reverse : List G) = inv_reverse L := by {
  simp only [coeM_reverse, inv_reverse, List.reverse_inj]
  calc
  _ = List.map (id) (L : List G) := by simp only [List.map_id]
  _ = _ := List.map_congr (fun x hx => inv_eq_self x (mem_subtype_list hx))
}

lemma reverse_prod_prod_eq_one {L: List S}  : (L.reverse :G) * L = 1:= by {
  calc
    _ =  (inv_reverse L : G) * L := by rw [←inv_reverse_eq_reverse L]
    _ = _ := inv_reverse_prod_prod_eq_one
}

@[simp]
lemma gprod_reverse (L: List S) : L.reverse.gprod = (L.gprod)⁻¹ :=
 mul_eq_one_iff_eq_inv.1 reverse_prod_prod_eq_one


@[simp]
lemma gprod_reverse' (L: List S) : (L.reverse:G)⁻¹ = L := by simp

lemma exists_prod (g : G) : ∃ (L : List S),  g = L := h.expression g

--def AllExpression (g:G) := {L : List S| g = L}

@[simp]
def reduced_word (L : List S) := ∀ (L' : List S),  (L :G) =  L' →  L.length ≤ L'.length

end OrderTwoGen

namespace OrderTwoGen
variable {G : Type*} [Group G] (S : Set G) [OrderTwoGen S]

def length_aux (g : G) : ∃ (n:ℕ) , ∃ (L : List S), L.length = n ∧ g = L := by
  let ⟨(L : List S), hL⟩ := exists_prod g
  use L.length,L

noncomputable def length (x : G): ℕ := Nat.find (length_aux S x)


--scoped notation: max "ℓ" S " (" g ")" => (length S g)


end OrderTwoGen


namespace OrderTwoGen
variable {G : Type*} [Group G] {S : Set G} [OrderTwoGen S]

local notation: max "ℓ(" g ")" => (length S g)

lemma length_le_list_length {L : List S} :  ℓ(L) ≤ L.length :=
  Nat.find_le (by use L)


-- The lemma was called ``inv''
lemma reverse_is_reduced {L: List S} (h: reduced_word L): reduced_word L.reverse:= by
   contrapose h
   rw [reduced_word] at *
   push_neg at *
   rcases h with ⟨LL,hL⟩
   use LL.reverse
   rw [gprod_reverse,List.length_reverse] at *
   rw [←hL.1,inv_inv]
   exact ⟨rfl,hL.2⟩

-- The lemma was called ``nil''
lemma nil_is_reduced: reduced_word ([] : List S) := by
   rintro _ _
   norm_num

-- The lemma was called singleton
lemma singleton_is_reduced {s:S}: reduced_word [s]:= by
   rintro L hL
   contrapose hL
   push_neg at *
   rw [List.length_singleton] at hL
   have : List.length L = 0:=by{linarith}
   have h1 :=List.length_eq_zero.1 this
   rw [h1,gprod_nil,gprod_singleton]
   exact gen_ne_one s.1 s.2

lemma pos_length_of_non_reduced_word {L : List S} : ¬reduced_word L → 1 ≤ L.length := by
  contrapose
  simp_rw [not_le, not_not, Nat.lt_one_iff]
  rw [List.length_eq_zero]
  intro H
  simp only [H, nil_is_reduced]

lemma two_le_length_of_non_reduced_word {L : List S} : ¬reduced_word L → 2 ≤ L.length := by
  contrapose
  simp_rw [not_le, not_not]
  intro h
  interval_cases hL : L.length
  · rw [List.length_eq_zero] at hL
    simp only [hL, nil_is_reduced]
  · rw [List.length_eq_one] at hL
    rcases hL with ⟨s, hs⟩
    rw [hs]
    exact singleton_is_reduced


lemma length_le_iff {L: List S} : reduced_word L ↔ L.length ≤ ℓ(L):= by
   rw [length, (Nat.le_find_iff _)]
   apply Iff.intro
   .  intro h m hm
      contrapose hm
      rw [not_not] at hm
      let ⟨L', HL'⟩ := hm
      rw [not_lt,←HL'.1]
      exact h L'  HL'.2
   .  intro H
      rw [reduced_word]
      intro L' HL'
      contrapose H
      rw [not_le] at H
      rw [not_forall]
      use L'.length
      rw [←not_and,not_not]
      constructor
      . exact H
      . use L'

lemma length_eq_iff {L: List S} : reduced_word L ↔ L.length = ℓ(L.gprod) := by
   constructor
   . intro H
     exact ge_antisymm length_le_list_length (length_le_iff.1 H)
   . intro H
     exact (length_le_iff).2 (le_of_eq H)



lemma exists_reduced_word (S : Set G) [OrderTwoGen S] (g : G) : ∃ (L: List S) , reduced_word L ∧ g = L.gprod := by
   let ⟨L',h1,h2⟩ := Nat.find_spec (@length_aux G  _ S _ g)
   use L'
   have C1 := (@length_eq_iff _ _ _ _ L').2
   rw [length] at C1
   simp_rw [h2] at h1
   exact ⟨C1 h1,h2⟩


lemma length_eq_inv_length: ℓ(g) = ℓ(g⁻¹) := by {
  obtain ⟨L,HL1,HL2⟩ := exists_reduced_word S g
  repeat rw [HL2]
  calc
  _ = L.length := by rw [←length_eq_iff.1 HL1]
  _ = L.reverse.length :=  by simp
  _ = ℓ(L.reverse) := length_eq_iff.1 (reverse_is_reduced HL1)
  _=_ := by simp [gprod_reverse]
}



@[simp]
lemma inv_length_eq_length: ℓ(g⁻¹) = ℓ(g) := Eq.symm length_eq_inv_length

lemma length_eq_reverse_length (L:List S): ℓ(L) = ℓ(L.reverse) := by {
  calc
  _ = ℓ((L:G)⁻¹) := length_eq_inv_length
  _ = _ :=  by simp [gprod_reverse]
}

@[simp]
lemma reverse_length_eq_length (L:List S): ℓ(L.reverse)=ℓ(L)  := Eq.symm (length_eq_reverse_length L)

lemma length_cons {hd : S} {tail : List S} : ℓ(hd::tail) ≤ ℓ(tail) + 1 := by {
  obtain ⟨rtail, h1, h2⟩ := exists_reduced_word S tail
  calc
  _ = ℓ(hd::rtail) := by congr 1; simp_rw [gprod_cons,h2]
  _ ≤ (hd::rtail).length :=  length_le_list_length
  _ = rtail.length + 1:= by simp [List.length_cons]
  _ = _ := by simp [h2,length_eq_iff.1 h1]
}


lemma length_mul_le_length_sum  {w1 w2 : G} : ℓ(w1 * w2) ≤ ℓ(w1) + ℓ(w2) := by
  obtain ⟨L1, h1, h2⟩ := exists_reduced_word S w1
  obtain ⟨L2, h3, h4⟩ := exists_reduced_word S w2
  calc
  _ = ℓ(L1 ++ L2) := by congr; simp only [h2, h4, gprod_append]
  _ ≤  (L1 ++ L2).length := length_le_list_length
  _ = L1.length + L2.length := by simp
  _ = _ := by simp [h2,h4,length_eq_iff.1 h1,length_eq_iff.1 h3]

-- DLevel 1
lemma length_smul_le_length_add_one {w:G} : ℓ(s*w) ≤ ℓ(w) + 1 := by
  sorry

-- DLevel 1
lemma length_le_length_smul_add_one {w:G} : ℓ(w) ≤ ℓ(s*w) + 1 := by
  sorry


-- DLevel 1
lemma length_muls_le_length_add_one {w:G} : ℓ(w*s) ≤ ℓ(w) + 1 := by
  sorry

-- DLevel 1
lemma length_le_length_muls_add_one {w:G} : ℓ(w) ≤ ℓ(w*s) + 1 := by
  sorry

lemma length_bound  {w1 w2 : G} : ℓ(w1)  - ℓ(w2) ≤ ℓ(w1 * w2 ⁻¹) := by
  have := @length_mul_le_length_sum _ _ S _ (w1 * w2⁻¹) w2
  simp only [inv_mul_cancel_right] at this
  simp only [tsub_le_iff_right, ge_iff_le,this]


-- DLevel 1
lemma length_zero_iff_one {w:G} : ℓ(w) = 0 ↔ w = 1 := by
  sorry


-- DLevel 2
lemma reduced_take_of_reduced {S: Set G} [OrderTwoGen S] {L: List S} (H : reduced_word L) (n:ℕ) : reduced_word (L.take n) := by sorry


-- DLevel 1
lemma reduced_drop_of_reduced {S: Set G} [OrderTwoGen S] {L: List S} (H : reduced_word L) (n:ℕ) : reduced_word (L.drop n) := by sorry



-- Cannot define the metric as an instance as there are various choices of S for a fixed G
-- On the other hand, the metric is well defined for Coxeter Group
noncomputable def metric {G :Type*} [Group G] (S : Set G) [@OrderTwoGen G _ S] : MetricSpace G where
  dist := fun x y => length S (x * y⁻¹)
  dist_self := by sorry
  dist_comm := by sorry
  dist_triangle := by sorry
  eq_of_dist_eq_zero := by sorry
  edist_dist := by sorry


noncomputable def choose_reduced_word (S : Set G) [OrderTwoGen S]  (g:G) : List S := Classical.choose (exists_reduced_word S g)

lemma choose_reduced_word_spec (g : G) : reduced_word (choose_reduced_word S g) ∧ g = (choose_reduced_word S g) :=
   Classical.choose_spec (exists_reduced_word S g)



def non_reduced_p  (L : List S) := fun k => ¬ reduced_word (L.take (k+1))

lemma max_reduced_word_index_aux (L: List S) (H : ¬ reduced_word L) : ∃ n, non_reduced_p  L n := by
   use L.length
   rw [non_reduced_p,List.take_all_of_le (le_of_lt (Nat.lt_succ_self L.length))]
   exact H

noncomputable def max_reduced_word_index {L : List S} (H : ¬ reduced_word L):= Nat.find (max_reduced_word_index_aux  L H)

lemma nonreduced_succ_take_max_reduced_word {L : List S} (H : ¬ reduced_word L) : ¬ reduced_word (L.take ((max_reduced_word_index  H)+1)) := by
   let j:= max_reduced_word_index  H
   have Hj : j = max_reduced_word_index H := rfl
   rw [←Hj]
   rw [max_reduced_word_index]  at Hj
   have HH:= (Nat.find_eq_iff _).1 Hj
   rw [←Hj,non_reduced_p] at HH
   exact HH.1

lemma reduced_take_max_reduced_word {L : List S} (H : ¬ reduced_word L) : reduced_word (L.take (max_reduced_word_index H)) := by
   let j:= max_reduced_word_index H
   have Hj : j = max_reduced_word_index H := rfl
   match j with
   | 0 =>
      rw [←Hj,List.take_zero]
      exact nil_is_reduced
   | n+1 =>
      rw [←Hj]
      have := (Nat.le_find_iff _ _).1 (le_of_eq Hj) n (Nat.lt_succ_self n)
      rw [non_reduced_p,not_not] at this
      exact this

lemma max_reduced_word_index_lt {L : List S} (H : ¬ reduced_word L) : max_reduced_word_index H < L.length := by
   have Hlen := pos_length_of_non_reduced_word H
   rw [max_reduced_word_index, Nat.find_lt_iff _ L.length]
   use L.length -1
   rw [non_reduced_p]
   have Hlen' : 0<L.length := by linarith
   constructor
   . exact Nat.sub_lt Hlen' (by simp)
   . have : L.length -1 +1  = L.length := by rw [←Nat.sub_add_comm Hlen,Nat.add_sub_cancel]
     rw [this,List.take_length]
     exact H

noncomputable def max_reduced_word_index' {L : List S} (H : ¬ reduced_word L) : Fin L.length:= ⟨max_reduced_word_index H, max_reduced_word_index_lt  H⟩

lemma length_lt_iff_non_reduced {L : List S} : ℓ(L) < L.length ↔ ¬ reduced_word L := by {
   rw [iff_not_comm,not_lt]
   exact length_le_iff
}

lemma reduced_imp_tail_reduced : reduced_word (L : List S) → reduced_word L.tail :=
 match L with
  | [] => by simp
  | hd::tail =>  by {
    simp only [List.length_cons, List.tail_cons]
    intro h
    have len1:= (length_eq_iff).1 h
    by_contra H
    have H:= length_lt_iff_non_reduced.2 H
    have :tail.length +1 < tail.length + 1 := by {
      calc
      tail.length + 1 = _ := by simp
      _ = _ := len1
      _ ≤  ℓ(tail)+1 := length_cons
      _ < tail.length +1 := by linarith
    }
    linarith
  }



lemma reduced_nonreduced_length_le  {L : List S} {s : S} (H1: reduced_word L) (H2: ¬ reduced_word (L ++ [s])) :ℓ(L.gprod * s) ≤ ℓ(L.gprod) := by {
    rw [←(length_eq_iff).1 H1]
    contrapose H2
    have Hs :[s].gprod = s := gprod_singleton
    have Hlen : (L++[s]).length = Nat.succ L.length := by rw [List.length_append, List.length_singleton]
    rw [not_le,←gprod_singleton,←gprod_append,←Nat.succ_le_iff,←Hlen] at H2
    rw [not_not,length_le_iff]
    exact H2
}

end OrderTwoGen
