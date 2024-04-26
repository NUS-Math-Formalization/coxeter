import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.IntervalCases

import Coxeter.Aux_
open Classical

class OrderTwoGen {G : Type*} [Group G] (S : Set G) where
  order_two : ∀ (x : G), x ∈ S → x * x = (1 : G) ∧ x ≠ (1 : G)
  expression : ∀ (x : G), ∃ (L : List S), x = L.gprod

namespace OrderTwoGen

variable {G : Type _} [Group G] {S : Set G} [h : OrderTwoGen S]


@[simp]
lemma gen_square_eq_one : ∀ x ∈ S, x * x = 1 := fun x hx ↦ (h.order_two x hx).1

@[simp]
lemma gen_square_eq_one' (s : S) : (s : G) * s = 1:= by simp [gen_square_eq_one s.1 s.2]

--@[simp] -- makes expression more complex
lemma inv_eq_self [h : OrderTwoGen S]: ∀ x : G, x ∈ S → x = x⁻¹ :=
  fun x hx ↦ mul_eq_one_iff_eq_inv.1 (h.order_two x hx).1

--@[simp] -- makes expression more complex
lemma inv_eq_self' : ∀ (x : S), x = (x : G)⁻¹ := fun x ↦ inv_eq_self x.1 x.2

@[simp, gprod_simps]
lemma inv_eq_self'' : ∀ (x : S), (x : G)⁻¹ = x := fun x ↦ Eq.symm (inv_eq_self x.1 x.2)

-- The lemma was called non_one
lemma gen_ne_one : ∀ x ∈ S, x ≠ 1 :=
  fun x hx ↦ (h.order_two x hx).2

lemma gen_ne_one' : ∀ (x : S), (x : G) ≠ 1 :=
  fun x ↦ gen_ne_one x.1 x.2


lemma symm_gen_eq_gen (S : Set G) [hS : OrderTwoGen S]: {z | z ∈ S ∨ z⁻¹ ∈ S} = S:= by
  ext z; constructor
  . intro h
    rcases h with h | h
    . assumption
    . have :=hS.inv_eq_self _ h; rw [inv_inv] at this;rw [<-this]; exact h
  . intro _; left; assumption

lemma monoid_closure_gen_eq_top : Submonoid.closure S = ⊤ := by
  apply eq_top_iff.2
  intro x _
  obtain ⟨L, hL⟩ := h.expression x
  have im:= (Submonoid.mem_monoid_closure_iff_prod (T:=S) x).2
  exact im ⟨L,by assumption⟩

lemma mem_monoid_closure (g: G) : g ∈ Submonoid.closure S := by rw [monoid_closure_gen_eq_top]; exact Submonoid.mem_top g


lemma closure_gen_eq_top : Subgroup.closure S = ⊤ := by
  apply eq_top_iff.2
  rw [<-Subgroup.toSubmonoid_le,Subgroup.top_toSubmonoid, Subgroup.closure_toSubmonoid S]
  calc
  _ = Submonoid.closure S:= by rw [monoid_closure_gen_eq_top (S := S)]
  _ ≤ _ := Submonoid.closure_mono (by simp : S ⊆ S ∪ S⁻¹)


/-- If `p : G → Prop` holds for all elements in S, it holds for the identity, and it is
preserved under multiplication, then it holds for all elements of `G`. -/
theorem gen_induction {p : G → Prop} (g : G) (Hs : ∀ s : S, p s.val) (H1 : p 1)
    (Hmul : ∀ g g', p g → p g' → p (g * g')) : p g := by
  apply Submonoid.closure_induction (p:=p) (mem_monoid_closure (S := S) g)
  . exact fun x hx => Hs ⟨x,hx⟩
  . exact H1
  . exact Hmul

/-- If `p : G → Prop` holds for the identity and it is preserved under multiplying on the left
by a generator, then it holds for all elements of `G`. -/
theorem gen_induction_left {p : G → Prop} (g : G) (H1 : p 1)
    (Hmul : ∀  (s : S) (g : G), p g → p (s * g)) : p g := by
  apply Submonoid.induction_of_closure_eq_top_left (p:=p) (monoid_closure_gen_eq_top (S:=S))
  . exact H1
  . exact fun x hx => Hmul ⟨x,hx⟩


/-- If `p : G → Prop` holds for the identity and it is preserved under multiplying on the right
by a generator, then it holds for all elements of `G`. -/
theorem gen_induction_right {p : G → Prop} (g : G) (H1 : p 1)
    (Hmul : ∀  (g : G) (s : S)  , p g → p (g * s)) : p g := by
  apply Submonoid.induction_of_closure_eq_top_right (p:=p) (monoid_closure_gen_eq_top (S:=S))
  . exact H1
  . exact fun g x hx => Hmul g ⟨x,hx⟩


--lemma mul_generator_inv {s:S} {w:G} [orderTwoGen S]: (w*s)⁻¹ = s*w⁻¹:= by rw []

lemma inv_reverse_eq_reverse (L : List S) : (L.reverse : List G) = inv_reverse L := by
  induction' L with hd tl ih
  . trivial
  . simp only [List.reverse_cons, List.bind_eq_bind, List.append_bind, List.cons_bind,
    List.nil_bind, List.append_nil, inv_reverse, List.map_append, List.reverse_append]
    congr; simp only [inv_eq_self'']

lemma reverse_prod_prod_eq_one {L : List S} : (L.reverse : G) * L = 1 := by {
  calc
    _ = (inv_reverse L : G) * L := by rw [← inv_reverse_eq_reverse L]
    _ = _ := inv_reverse_prod_prod_eq_one
}

@[simp, gprod_simps]
lemma gprod_reverse (L : List S) : L.reverse.gprod = (L.gprod)⁻¹ :=
  mul_eq_one_iff_eq_inv.1 reverse_prod_prod_eq_one

@[simp, gprod_simps]
lemma gprod_reverse' (L : List S) : (L.reverse : G)⁻¹ = L := by simp

lemma exists_prod (g : G) : ∃ (L : List S), g = L := h.expression g

--def AllExpression (g : G) := {L : List S| g = L}

@[simp]
def reduced_word (L : List S) := ∀ (L' : List S), (L : G) = L' → L.length ≤ L'.length

end OrderTwoGen

namespace OrderTwoGen
variable {G : Type*} [Group G] (S : Set G) [OrderTwoGen S]

def length_aux (g : G) : ∃ (n : ℕ), ∃ (L : List S), L.length = n ∧ g = L := by
  let ⟨(L : List S), hL⟩ := exists_prod g
  use L.length, L

noncomputable def length (x : G) : ℕ := Nat.find (length_aux S x)

--scoped notation: max "ℓ" S " (" g ")" => (length S g)

end OrderTwoGen

namespace OrderTwoGen
variable {G : Type*} [Group G] {S : Set G} [OrderTwoGen S]

local notation: max "ℓ(" g ")" => (length S g)

lemma length_le_list_length {L : List S} : ℓ(L) ≤ L.length :=
  Nat.find_le (by use L)

-- The lemma was called ``inv''
lemma reverse_is_reduced {L : List S} (h : reduced_word L) : reduced_word L.reverse := by
  contrapose h
  rw [reduced_word] at *
  push_neg at *
  rcases h with ⟨LL, hL⟩
  use LL.reverse
  rw [gprod_reverse, List.length_reverse] at *
  rw [← hL.1, inv_inv]
  exact ⟨rfl, hL.2⟩

-- The lemma was called ``nil''
lemma nil_is_reduced: reduced_word ([] : List S) := by
  rintro _ _
  norm_num

-- The lemma was called singleton
lemma singleton_is_reduced {s : S}: reduced_word [s] := by
  rintro L hL
  contrapose hL
  push_neg at *
  rw [List.length_singleton] at hL
  have : List.length L = 0 := by linarith
  have h1 := List.length_eq_zero.1 this
  rw [h1, gprod_nil, gprod_singleton]
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

lemma length_le_iff {L : List S} : reduced_word L ↔ L.length ≤ ℓ(L) := by
  rw [length, (Nat.le_find_iff _)]
  apply Iff.intro
  . intro h m hm
    contrapose hm
    rw [not_not] at hm
    let ⟨L', HL'⟩ := hm
    rw [not_lt, ← HL'.1]
    exact h L' HL'.2
  . intro H
    rw [reduced_word]
    intro L' HL'
    contrapose H
    rw [not_le] at H
    rw [not_forall]
    use L'.length
    rw [← not_and, not_not]
    constructor
    . exact H
    . use L'

lemma length_eq_iff {L : List S} : reduced_word L ↔ L.length = ℓ(L.gprod) := by
  constructor
  . intro H
    exact ge_antisymm length_le_list_length (length_le_iff.1 H)
  . intro H
    exact (length_le_iff).2 (le_of_eq H)

lemma exists_reduced_word (S : Set G) [OrderTwoGen S] (g : G) : ∃ (L : List S), reduced_word L ∧ g = L.gprod := by
  let ⟨L', h1, h2⟩ := Nat.find_spec (@length_aux G _ S _ g)
  use L'
  have C1 := (@length_eq_iff _ _ _ _ L').2
  rw [length] at C1
  simp_rw [h2] at h1
  exact ⟨C1 h1, h2⟩

lemma length_eq_inv_length: ℓ(g) = ℓ(g⁻¹) := by {
  obtain ⟨L, HL1, HL2⟩ := exists_reduced_word S g
  repeat rw [HL2]
  calc
    _ = L.length := by rw [← length_eq_iff.1 HL1]
    _ = L.reverse.length := by simp
    _ = ℓ(L.reverse) := length_eq_iff.1 (reverse_is_reduced HL1)
    _ = _ := by simp [gprod_reverse]
}

@[simp]
lemma inv_length_eq_length: ℓ(g⁻¹) = ℓ(g) := Eq.symm length_eq_inv_length

lemma length_eq_reverse_length (L:List S): ℓ(L) = ℓ(L.reverse) := by {
  calc
  _ = ℓ((L:G)⁻¹) := length_eq_inv_length
  _ = _ :=  by simp [gprod_reverse]
}

@[simp]
lemma reverse_length_eq_length (L : List S): ℓ(L.reverse) = ℓ(L) := (length_eq_reverse_length L).symm

lemma length_cons {hd : S} {tail : List S} : ℓ(hd :: tail) ≤ ℓ(tail) + 1 := by {
  obtain ⟨rtail, h1, h2⟩ := exists_reduced_word S tail
  calc
  _ = ℓ(hd :: rtail) := by congr 1; simp_rw [gprod_cons, h2]
  _ ≤ (hd :: rtail).length := length_le_list_length
  _ = rtail.length + 1 := by simp [List.length_cons]
  _ = _ := by simp [h2, length_eq_iff.1 h1]
}

lemma length_mul_le_length_sum {w1 w2 : G} : ℓ(w1 * w2) ≤ ℓ(w1) + ℓ(w2) := by
  obtain ⟨L1, h1, h2⟩ := exists_reduced_word S w1
  obtain ⟨L2, h3, h4⟩ := exists_reduced_word S w2
  calc
    _ = ℓ(L1 ++ L2) := by congr; simp only [h2, h4, gprod_append]
    _ ≤ (L1 ++ L2).length := length_le_list_length
    _ = L1.length + L2.length := by simp
    _ = _ := by simp [h2, h4, length_eq_iff.1 h1,length_eq_iff.1 h3]

-- DLevel 1
lemma length_smul_le_length_add_one {w : G} {s : S} : ℓ(s * w) ≤ ℓ(w) + 1 := by
  obtain ⟨L, ⟨hL1 , hL2⟩ ⟩ := exists_reduced_word S w
  have : s * w = (s :: L) := by simp only [gprod_cons, hL2]
  rw [this]
  calc
    _ ≤ (s :: L).length := length_le_list_length
    _ = L.length + 1 := by simp only [List.length_cons]
    _ = ℓ(w) + 1 := by rw [length_eq_iff.1 hL1, hL2]

-- DLevel 1
lemma length_le_length_smul_add_one {w : G} {s : S} : ℓ(w) ≤ ℓ(s * w) + 1 := by
  have h1 : w = s * (s * w) := by
    calc
      w = 1 * w := by group
      _ = (s * s) * w := by rw [gen_square_eq_one']
      _ = s * (s * w) := by group
  nth_rw 1 [h1]
  apply length_smul_le_length_add_one

-- DLevel 1
lemma length_muls_le_length_add_one {w : G} {s : S} : ℓ(w * s) ≤ ℓ(w) + 1 := by
  obtain ⟨L, ⟨hL1, hL2⟩⟩ := exists_reduced_word S w
  have : w * s = (L ++ [s]) := by simp only [gprod_append_singleton, hL2]
  rw [this]
  calc
    _ ≤ (L ++ [s]).length := length_le_list_length
    _ = L.length + [s].length := by simp only [List.length_append]
    _ = L.length + 1 := by rw [List.length_singleton]
    _ = ℓ(w) + 1 := by rw [length_eq_iff.1 hL1, hL2]

-- DLevel 1
lemma length_le_length_muls_add_one {w : G} {s : S} : ℓ(w) ≤ ℓ(w * s) + 1 := by
  have h1 : w = (w * s) * s := by
    calc
      w = w * 1 := by group
      _ = w * (s * s) := by rw [gen_square_eq_one']
      _ = (w * s) * s := by group
  nth_rw 1 [h1]
  apply length_muls_le_length_add_one

lemma length_bound {w1 w2 : G} : ℓ(w1) - ℓ(w2) ≤ ℓ(w1 * w2⁻¹) := by
  have := @length_mul_le_length_sum _ _ S _ (w1 * w2⁻¹) w2
  simp only [inv_mul_cancel_right] at this
  simp only [tsub_le_iff_right, ge_iff_le, this]

lemma length_of_one : ℓ((1 : G)) = 0 := by
  rw [length]
  simp only [Nat.find_eq_zero]
  use []
  simp only [List.length_nil, gprod_nil, and_self]

-- Dlevel 1
lemma length_zero_iff_one {w : G} : ℓ(w) = 0 ↔ w = 1 := by
  constructor
  · intro h1
    let ⟨L, h4, h5⟩ := Nat.find_spec (@length_aux G _ S _ w)
    have h6 : List.length L = 0 := by
      calc
        List.length L = length S w := by
          rw [h4]
          simp only [length]
        _ = 0 := h1
    have h7 : L = [] := by
      apply List.length_eq_zero.1 h6
    rw [h5, ← gprod_nil, h7]
  · intro h2
    rw [h2, ← gprod_nil]
    have h3 : ℓ(([] : List S)) ≤ 0 := length_le_list_length
    apply Nat.le_zero.1 h3

lemma take_drop_get' (L: List S) (n : ℕ) (h : n < L.length):
  L = (L.take n).gprod * [L.get ⟨n, h⟩] * L.drop (n+1) := by
  rw [←gprod_append, ←gprod_append]
  apply congr_arg
  exact List.take_drop_get L n h

-- DLevel 2
lemma reduced_take_of_reduced {S : Set G} [OrderTwoGen S] {L : List S} (h : reduced_word L) (n : ℕ) :
    reduced_word (L.take n) := by
  contrapose! h
  simp only [reduced_word] at *
  push_neg at *
  rcases h with ⟨L', hL'⟩
  use L' ++ L.drop n
  rw [gprod_append, hL'.1.symm, List.length_append, ← gprod_append, List.take_append_drop]
  apply And.intro rfl
  by_cases h : n ≤ L.length
  · rw [List.length_drop]
    rw [List.length_take_of_le h] at hL'
    apply lt_of_lt_of_le (add_lt_add_right hL'.2 (L.length - n))
    rw [← Nat.add_sub_assoc h, add_comm, Nat.add_sub_cancel]
  · rw [List.length_drop, Nat.sub_eq_zero_of_le (by linarith [h])]
    apply lt_of_lt_of_le hL'.2
    rw [List.length_take]
    exact min_le_iff.mpr (Or.inr le_rfl)

-- DLevel 2
lemma reduced_drop_of_reduced {S : Set G} [OrderTwoGen S] {L : List S} (h : reduced_word L) (n : ℕ) :
    reduced_word (L.drop n) := by
  apply reverse_is_reduced at h
  rw [← List.reverse_reverse (L.drop n)]
  apply reverse_is_reduced
  rw [List.reverse_drop]
  exact reduced_take_of_reduced h (L.length - n)

/-- If `p : G → Prop` holds for the identity and it is preserved under multiplying on the left
by a generator to form a reduced word, then it holds for all elements of `G`. -/
theorem gen_induction_reduced_word_left {p : G → Prop} (g : G) (H1 : p 1)
    (Hmul : ∀ (s : S) (L : List S), reduced_word (s :: L) → p L.gprod → p (s :: L).gprod) : p g := by
  obtain ⟨L, hr, hL⟩ := @exists_reduced_word G _ S _ g
  induction L generalizing g with
  | nil => rw [hL, gprod_nil]; exact H1
  | cons hd tail ih =>
    rw [hL]
    exact Hmul hd tail hr (ih tail.gprod (reduced_drop_of_reduced hr 1) rfl)


-- Cannot define the metric as an instance as there are various choices of S for a fixed G
-- On the other hand, the metric is well defined for Coxeter Group
noncomputable def metric {G : Type*} [Group G] (S : Set G) [@OrderTwoGen G _ S] : MetricSpace G where
  dist := fun x y => length S (x * y⁻¹)
  dist_self := fun _ ↦ by simp only [dist, mul_right_inv]; norm_num; exact length_zero_iff_one.mpr rfl
  dist_comm := fun _ _ ↦ by simp only [dist]; rw [length_eq_inv_length]; group
  dist_triangle := fun x y z ↦ by
    simp only [dist]
    rw [(by group : x * z⁻¹ = (x * y⁻¹) * (y * z⁻¹))]
    rw [← Nat.cast_add]
    apply (@Nat.cast_le ℝ _ _ _ _ _ (length S (x * y⁻¹ * (y * z⁻¹))) (length S (x * y⁻¹) + length S (y * z⁻¹))).mpr
    exact length_mul_le_length_sum
  eq_of_dist_eq_zero := fun {x y} h ↦ by
    simp only [Nat.cast_eq_zero, length_zero_iff_one] at h
    rw [← one_mul y, ← h, mul_assoc, mul_left_inv, mul_one]
  edist_dist := fun x y ↦ by
    simp only [Nonneg.mk_natCast, ENNReal.ofReal_natCast]
    exact rfl


noncomputable def choose_reduced_word (S : Set G) [OrderTwoGen S] (g:G) : List S := Classical.choose (exists_reduced_word S g)

lemma choose_reduced_word_spec (g : G) : reduced_word (choose_reduced_word S g) ∧ g = (choose_reduced_word S g) :=
  Classical.choose_spec (exists_reduced_word S g)

def non_reduced_p (L : List S) := fun k => ¬reduced_word (L.take (k + 1))

lemma max_reduced_word_index_aux (L : List S) (H : ¬reduced_word L) : ∃ n, non_reduced_p L n := by
  use L.length
  rw [non_reduced_p,List.take_all_of_le (le_of_lt (Nat.lt_succ_self L.length))]
  exact H

noncomputable def max_reduced_word_index {L : List S} (H : ¬reduced_word L) := Nat.find (max_reduced_word_index_aux L H)

lemma nonreduced_succ_take_max_reduced_word {L : List S} (H : ¬reduced_word L) : ¬reduced_word (L.take (max_reduced_word_index H + 1)) := by
  let j := max_reduced_word_index H
  have Hj : j = max_reduced_word_index H := rfl
  rw [← Hj]
  rw [max_reduced_word_index] at Hj
  have HH := (Nat.find_eq_iff _).1 Hj
  rw [← Hj, non_reduced_p] at HH
  exact HH.1

lemma reduced_take_max_reduced_word {L : List S} (H : ¬reduced_word L) : reduced_word (L.take (max_reduced_word_index H)) := by
  let j := max_reduced_word_index H
  have Hj : j = max_reduced_word_index H := rfl
  match j with
  | 0 =>
    rw [← Hj, List.take_zero]
    exact nil_is_reduced
  | n + 1 =>
    rw [← Hj]
    have := (Nat.le_find_iff _ _).1 (le_of_eq Hj) n (Nat.lt_succ_self n)
    rw [non_reduced_p, not_not] at this
    exact this

lemma max_reduced_word_index_lt {L : List S} (H : ¬reduced_word L) : max_reduced_word_index H < L.length := by
  have Hlen := pos_length_of_non_reduced_word H
  rw [max_reduced_word_index, Nat.find_lt_iff _ L.length]
  use L.length - 1
  rw [non_reduced_p]
  have Hlen' : 0 < L.length := by linarith
  constructor
  . exact Nat.sub_lt Hlen' (by simp)
  . have : L.length - 1 + 1 = L.length := by rw [← Nat.sub_add_comm Hlen, Nat.add_sub_cancel]
    rw [this, List.take_length]
    exact H

noncomputable def max_reduced_word_index' {L : List S} (H : ¬reduced_word L) : Fin L.length := ⟨max_reduced_word_index H, max_reduced_word_index_lt H⟩

lemma length_lt_iff_non_reduced {L : List S} : ℓ(L) < L.length ↔ ¬reduced_word L := by {
  rw [iff_not_comm, not_lt]
  exact length_le_iff
}

lemma reduced_imp_tail_reduced : reduced_word (L : List S) → reduced_word L.tail :=
 match L with
  | [] => by simp
  | hd :: tail => by {
    simp only [List.length_cons, List.tail_cons]
    intro h
    have len1 := length_eq_iff.1 h
    by_contra H
    have H := length_lt_iff_non_reduced.2 H
    have : tail.length + 1 < tail.length + 1 := by {
      calc
        tail.length + 1 = _ := by simp
        _ = _ := len1
        _ ≤ ℓ(tail) + 1 := length_cons
        _ < tail.length + 1 := by linarith
    }
    linarith
  }

lemma reduced_nonreduced_length_le {L : List S} {s : S} (H1 : reduced_word L) (H2 : ¬reduced_word (L ++ [s])) : ℓ(L.gprod * s) ≤ ℓ(L.gprod) := by {
  rw [← (length_eq_iff).1 H1]
  contrapose H2
  have Hs : [s].gprod = s := gprod_singleton
  have Hlen : (L ++ [s]).length = Nat.succ L.length := by rw [List.length_append, List.length_singleton]
  rw [not_le, ← gprod_singleton, ← gprod_append, ← Nat.succ_le_iff, ← Hlen] at H2
  rw [not_not, length_le_iff]
  exact H2
}

abbrev SimpleRefl (S : Set G) [OrderTwoGen S]: Set G := S

--abbrev Refl (S:Set G) [OrderTwoGen S]: Set G:= {x:G| ∃ (w:G) (s : S) , x = w*s*w⁻¹}

abbrev Refl (S : Set G) [OrderTwoGen S] : Set G := {x : G | ∃ (w : G) (s : S), x = w * s * w⁻¹}

-- TODO add some lemmes about conj of Refl is in Refl
-- DLevel1

def ReflSet (S : Set G) [OrderTwoGen S] (g : G) : Set (Refl S) := {t | length S (t * g) ≤ length S g}

local notation "T" => Refl S


lemma SimpleRefl_is_Refl : ∀ {g : G}, g ∈ S → g ∈ T := by
  intro g hg
  use 1, ⟨g, hg⟩
  simp


lemma SimpleRefl_subseteq_Refl : S ⊆ T := by
  simp_rw [Set.subset_def]
  exact fun g => SimpleRefl_is_Refl  (S:=S) (g:=g)


@[deprecated SimpleRefl_is_Refl]
lemma SimpleRefl_subset_Refl : ∀ {g : G}, g ∈ S → g ∈ T := by
  intro g hg
  use 1, ⟨g, hg⟩
  simp

lemma Refl.simplify {t : G} : t ∈ T ↔ ∃ g : G, ∃ s : S, g * s * g⁻¹ = t := by
  constructor
  · intro h1
    rcases h1 with ⟨g, s, hgs⟩
    use g, s; rw [hgs]
  · intro h1
    rcases h1 with ⟨g, s, hgs⟩
    use g, s; rw [hgs]

@[simp]
lemma Refl.conjugate_closed {g : G} {t : T} : g * t * g⁻¹ ∈ T := by
  dsimp
  have h1 : ∃ g1 : G, ∃ s1 : S, g1 * (s1 : G) * g1⁻¹ = (t : G) := by
    apply Refl.simplify.mp
    apply Subtype.mem
  rcases h1 with ⟨g1, s1, h2⟩
  have h3 : (g * g1) * ↑s1 * (g * g1)⁻¹ = g * ↑t * g⁻¹ := by
    rw [← h2]
    group
  use g * g1, s1; rw [h3]

lemma Refl.mul_SimpleRefl_in_Refl (s : S) (t : T) : (s : G) * t * (s : G) ∈ T := by
  convert Refl.conjugate_closed
  rw [inv_eq_self'']

/-- If `p : T → Prop` holds for all elements in S and it is preserved under
multiplication on both sides by elements in s, then it holds for all elements
of `T`. -/
theorem Refl.induction' {p : T → Prop} (t : T) (Hs : ∀ s : S, p ⟨s.val, SimpleRefl_is_Refl (Subtype.mem s)⟩)
    (Hmul : ∀ (t : T) (s : S), p t → p ⟨(s : G) * t * s, Refl.mul_SimpleRefl_in_Refl s t⟩) : p t := by
  rcases Subtype.mem t with ⟨g, s, tgsg⟩
  have : t = ⟨t.1, ⟨g, s, tgsg⟩⟩ := rfl
  rw [this]
  simp only [tgsg]
  have gsgT (g : G) (s : S) : g * s * g⁻¹ ∈ T :=
    @Refl.conjugate_closed _ _ _ _ g ⟨s.val, SimpleRefl_is_Refl (Subtype.mem s)⟩
  refine @gen_induction_left G _ S _ (fun g ↦ p ⟨g * s * g⁻¹, gsgT g s⟩) g ?h1 ?hmul
  · group; exact Hs s
  · intro s' g' hp
    dsimp only
    have := (Hmul ⟨g' * s * g'⁻¹, gsgT g' s⟩ s') hp
    convert this using 2
    simp_rw [mul_assoc, mul_left_cancel_iff, mul_inv_rev]
    congr 1
    exact inv_eq_self'' s'

/-- If `p : G → Prop` holds for all elements in S and it is preserved under
multiplication on both sides by elements in s, then it holds for all elements
of `T`. -/
theorem Refl.induction {p : G → Prop} (t : T) (Hs : ∀ s : S, p s.val)
    (Hmul : ∀ (g : G) (s : S), p g → p ((s : G) * g * s)) : p t := by
  rcases Subtype.mem t with ⟨g, s, tgsg⟩
  have : t = ⟨t.1, ⟨g, s, tgsg⟩⟩ := rfl
  rw [this]
  simp only [tgsg]
  refine @gen_induction_left G _ S _ (fun g ↦ p (g * s * g⁻¹)) g ?h1 ?hmul
  · group; exact Hs s
  · intro s' g' hp
    dsimp only
    have := (Hmul (g' * s * g'⁻¹) s') hp
    convert this using 1
    simp_rw [mul_assoc, mul_left_cancel_iff, mul_inv_rev]
    congr 1
    exact inv_eq_self'' s'

lemma Refl.square_eq_one [OrderTwoGen S] {t : Refl S} : (t : G) ^ 2 = 1 := by
  rcases t with ⟨t, g, s, teqgsg⟩
  simp only []
  rw [sq, teqgsg]
  group
  have hs : s * s = (1 : G) := by
    apply gen_square_eq_one (S := S)
    exact Subtype.mem s
  rw [mul_assoc g s, hs]
  group

@[deprecated Refl.square_eq_one]
lemma sq_refl_eq_one [OrderTwoGen S] {t : Refl S} : (t : G) ^ 2 = 1 := by
  rcases t with ⟨t, g, s, teqgsg⟩
  simp only []
  rw [sq, teqgsg]
  group
  have hs : s * s = (1 : G) := by
    apply gen_square_eq_one (S := S)
    exact Subtype.mem s
  rw [mul_assoc g s, hs]
  group

lemma Refl.inv_eq_self {t : T} : (t : G)⁻¹ = t :=
mul_eq_one_iff_inv_eq.1 (by rw [← sq]; convert Refl.square_eq_one)

@[deprecated Refl.inv_eq_self]
lemma inv_refl_eq_self {t : T} : (t : G)⁻¹ = t :=
mul_eq_one_iff_inv_eq.1 (by rw [← sq]; convert Refl.square_eq_one)

/--
Let `T` be the set of reflections in `G`.
If `p : G → Prop` holds for all elements in `S`, and it is
preserved under conjugate by ` s∈ S`, then it holds for all elements of `T`. -/
theorem refl_induction {p : G → Prop} {t : G} (ht : t ∈ T) (Hs : ∀ s, s ∈ S → p s)
(Hconj : ∀ s t, s ∈ S → t ∈ T → p t → p (s * t * s⁻¹)) :
   p t := by
  obtain ⟨g, s0, hs0⟩ := ht
  revert t
  apply gen_induction_left (S := S) g
  . intro t ht
    replace ht: t = s0.val := by rw [ht];group
    rw [ht]
    exact Hs s0.val s0.prop
  . intro s g ht t' ht'
    let t := g * s0 * g⁻¹
    have pt := ht (t:=t) rfl
    have := Hconj s t s.prop (by use g,s0) pt
    have tt' : t' = s.val * t * s.val⁻¹ := by simp_rw [ht',t];group
    convert this


theorem refl_induction' {p : T → Prop} (t : T) (Hs : ∀ s : S, p ⟨s,SimpleRefl_is_Refl s.prop⟩)
(Hconj : ∀ (s : S) (t : T), p t → p ⟨s.val * t * s.val⁻¹,Refl.conjugate_closed⟩ )
  : p t := by
  obtain ⟨g,s0,hs0⟩ := t.prop
  revert t
  induction' g using gen_induction_left with s g ht
  . exact fun t ht => Hs ⟨t.val, by simp [ht,s0.prop]⟩
  . intro t' ht'
    let t : T := ⟨g * s0 * g⁻¹, by use g, s0⟩
    have pt := ht t (rfl)
    have := Hconj s t pt
    have tt': t' = s.val * t * s.val⁻¹ := by rw [ht']; group
    convert this
  assumption

end OrderTwoGen

class HOrderTwoGenGroup (G: Type*) extends Group G where
  S: Set G
  order_two :  ∀ (x:G) , x ∈ S →  x * x = (1 :G) ∧  x ≠ (1 :G)
  expression : ∀ (x:G) , ∃ (L : List S),  x = L.gprod

namespace HOrderTwoGenGroup
variable (G :Type*) [hG: HOrderTwoGenGroup G]
variable {H :Type*} [hH: HOrderTwoGenGroup H]

@[simp]
abbrev SimpleRefl := hG.S
@[simp,deprecated SimpleRefl]
abbrev SimpleRefls := hG.S

abbrev Refl (G:Type*) [HOrderTwoGenGroup G]: Set G:= {x:G| ∃ (w:G)(s : SimpleRefl G) , x = w*s*w⁻¹}

@[deprecated Refl]
abbrev Refls (G:Type*) [HOrderTwoGenGroup G]: Set G:= {x:G| ∃ (w:G)(s : SimpleRefl G) , x = w*s*w⁻¹}

instance SimpleRefls.toOrderTwoGen  : @OrderTwoGen H _ (SimpleRefl H) where
  order_two := hH.order_two
  expression := hH.expression


instance SimpleRefls.toOrderTwoGen'  : @OrderTwoGen H _ (hH.S) where
  order_two := hH.order_two
  expression := hH.expression

noncomputable def length  (g :H) := OrderTwoGen.length (hH.S) g

notation:65 "ℓ(" g:66 ")" => (length g)
variable (s w :G)
end HOrderTwoGenGroup
