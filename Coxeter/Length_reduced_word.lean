import Coxeter.OrderTwoGen
import Coxeter.Bruhat
import Coxeter.Auxi

import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.Linarith.Frontend
import Std.Data.Nat.Lemmas

open Classical

open OrderTwoGen

variable {G: Type _} [Group G] {S : Set G} [OrderTwoGen S] [CoxeterSystem G S]
local notation:max "ℓ(" g ")" => (@length G _ S _ g)





namespace reduced_word

lemma length_le (L : List S) :  ℓ(L.gprod) ≤ L.length := by
   have h: ∃ (L1 : List S), L1.length = L.length ∧ L.gprod = L1.gprod:=by{use L}
   exact Nat.find_le h

lemma inv (L: List S) (h: reduced_word L): reduced_word L.reverse:= by
   contrapose h
   rw [reduced_word] at *
   push_neg at *
   rcases h with ⟨LL,hL⟩
   use LL.reverse
   rw [gprod_reverse,List.length_reverse] at *
   rw [←hL.1,inv_inv]
   exact ⟨rfl,hL.2⟩

lemma nil: reduced_word ([] : List S) := by
   rintro _ _
   norm_num

lemma singleton {s:S}: reduced_word [s]:= by
   rintro L hL
   contrapose hL
   push_neg at *
   rw [List.length_singleton] at hL
   have : List.length L = 0:=by{linarith}
   have h1 :=List.length_eq_zero.1 this
   rw [h1,gprod_nil,gprod_singleton]
   exact gen_ne_one s.1 s.2

lemma pos_length_of_non_reduced_word (L : List S): ¬ reduced_word L → 1 ≤  L.length := by
   contrapose
   simp_rw [not_le,not_not,Nat.lt_one_iff]
   rw [List.length_eq_zero];
   intro H
   simp only [H,nil]

lemma length_le_iff (L: List S) : reduced_word L ↔ L.length ≤ ℓ(L.gprod):= by
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

lemma length_eq_iff (L: List S) : reduced_word L ↔ L.length = ℓ(L.gprod) := by
   constructor
   . intro H
     exact ge_antisymm  (length_le  L)  ((length_le_iff  L).1 H)
   . intro H
     exact (length_le_iff  L).2 (le_of_eq H)

lemma exist (g : G) :∃ (L: List S) , reduced_word L ∧ g = L.gprod := by
   let ⟨L',h1,h2⟩ := Nat.find_spec (@length_aux G  _ S _ g)
   use L'
   have C1 := (length_eq_iff  L').2
   rw [length] at C1
   simp_rw [h2] at h1
   exact ⟨C1 h1,h2⟩

noncomputable def choose (g:G) : List S := Classical.choose (exist g)

lemma choose_spec (g : G) : reduced_word (choose g) ∧ g = (choose g).gprod :=
   Classical.choose_spec <| exist g


def non_reduced_p  (L : List S) := fun k => ¬ reduced_word (L.take (k+1))

lemma max_reduced_word_index_aux (L: List S) (H : ¬ reduced_word L) : ∃ n, non_reduced_p  L n := by
   use L.length
   rw [non_reduced_p,List.take_all_of_le (le_of_lt (Nat.lt_succ_self L.length))]
   exact H

noncomputable def max_reduced_word_index (L : List S) (H : ¬ reduced_word L):= Nat.find (max_reduced_word_index_aux  L H)

lemma nonreduced_succ_take_max_reduced_word (L : List S) (H : ¬ reduced_word L) : ¬ reduced_word (L.take ((max_reduced_word_index  L H)+1)) := by
   let j:= max_reduced_word_index  L H
   have Hj : j = max_reduced_word_index  L H := rfl
   rw [←Hj]
   rw [max_reduced_word_index]  at Hj
   have HH:= (Nat.find_eq_iff _).1 Hj
   rw [←Hj,non_reduced_p] at HH
   exact HH.1

lemma reduced_take_max_reduced_word (L : List S) (H : ¬ reduced_word L) : reduced_word (L.take (max_reduced_word_index L H)) := by
   let j:= max_reduced_word_index L H
   have Hj : j = max_reduced_word_index  L H := rfl
   match j with
   | 0 =>
      rw [←Hj,List.take_zero]
      exact nil
   | n+1 =>
      rw [←Hj]
      have := (Nat.le_find_iff _ _).1 (le_of_eq Hj) n (Nat.lt_succ_self n)
      rw [non_reduced_p,not_not] at this
      exact this

lemma max_reduced_word_index_lt (L : List S) (H : ¬ reduced_word L) : max_reduced_word_index L H < L.length := by
   have Hlen := pos_length_of_non_reduced_word  L H
   rw [max_reduced_word_index, Nat.find_lt_iff _ L.length]
   use L.length -1
   rw [non_reduced_p]
   have Hlen' : 0<L.length := by linarith
   constructor
   . exact Nat.sub_lt Hlen' (by simp)
   . have : L.length -1 +1  = L.length := by rw [←Nat.sub_add_comm Hlen,Nat.add_sub_cancel]
     rw [this,List.take_length]
     exact H

noncomputable def max_reduced_word_index' (L : List S) (H : ¬ reduced_word L) : Fin L.length:= ⟨max_reduced_word_index  L H, max_reduced_word_index_lt  L H⟩

lemma length_lt_iff_non_reduced (L : List S) : ℓ(L.gprod) < L.length ↔ ¬ reduced_word L := by {
   rw [iff_not_comm,not_lt]
   exact length_le_iff  L
}

lemma tail_reduced : reduced_word (L : List S) → reduced_word L.tail := sorry
end reduced_word

open reduced_word

lemma length_inv (g : G) : ℓ(g⁻¹)  =  ℓ(g) := by{
   rcases reduced_word.exist g with ⟨L,h1⟩
   have h2:=reduced_word.inv L h1.1
   have h3:=gprod_reverse L
   rw [←h1.2] at h3
   rw [←h3,h1.2,←(reduced_word.length_eq_iff L).1 h1.1,←(reduced_word.length_eq_iff L.reverse).1 h2,List.length_reverse]
}

lemma lr_symm {motive: (ℕ → ℕ → Prop)}  (s:S) (w:G) (h : ∀ (s : S), ∀ (w : G), motive ℓ(w) ℓ(s*w)) : motive ℓ(w) ℓ(w*s):=by
   -- intro s w
   have := h s w⁻¹
   rw [←length_inv,←length_inv (w*s),mul_generator_inv]
   assumption

@[simp]
lemma length_one_eq_zero : ℓ((1 : G)) = 0 := by {
   have h := (length_eq_iff []).1 (@nil G _ S)
   simp at h
   apply symm
   assumption
}

lemma eq_one_of_length_eq_zero (w:G) : ℓ(w)=0 → w =1 := by{
   intro h
   simp [length] at h
   rcases h with ⟨L,⟨hL,hLL⟩⟩
   have : L = []:= List.eq_nil_of_length_eq_zero hL
   rw [this] at hLL
   assumption
}

lemma length_eq_zero_of_eq_one {w:G} : w=1 → ℓ(w) =0:=fun hw =>(by rw [hw];simp)

lemma length_neq_zero_of_neq_one {w:G} : ¬w=1 →¬ℓ(w)=0:= mt (eq_one_of_length_eq_zero w)

lemma ne_one_of_length_ne_zero {w:G} :  ¬ℓ(w)=0 → ¬w=1 :=fun h => fun hw =>h (length_eq_zero_of_eq_one hw)

lemma length_generator_eq_one (s : S) : ℓ(s) = 1 := by{
   apply (Nat.find_eq_iff (length_aux S s)).2
   constructor
   .  {
      use [s]
      exact ⟨List.length_singleton s,eq_comm.1 gprod_singleton⟩
   }
   .  {
      intro n hn
      have hn': n = 0:=by {linarith}
      push_neg
      intro L hL
      rw [hn'] at hL
      have :=List.eq_nil_of_length_eq_zero hL
      rw [this, gprod_nil]
      exact gen_ne_one s.1 s.2
   }
}

lemma length_lt_not_nil (L : List S) (s : S) : ℓ(L.gprod * s) < ℓ(L.gprod) → L ≠ [] := by {
   contrapose
   rw  [ne_eq, not_not, not_lt]
   intro h
   rw [h,gprod_nil,length_one_eq_zero]
   exact zero_le (ℓ((1:G) * s))
}

lemma reduced_nonreduced_length_le  (L : List S) (s : S) (H1: reduced_word L) (H2: ¬ reduced_word (L ++ [s])) :ℓ(L.gprod * s) ≤ ℓ(L.gprod) := by {
    rw [←(length_eq_iff L).1 H1]
    contrapose H2
    have Hs :[s].gprod = s := gprod_singleton
    have Hlen : (L++[s]).length = Nat.succ L.length := by rw [List.length_append, List.length_singleton]
    rw [not_le,←gprod_singleton,←gprod_append,←Nat.succ_le_iff,←Hlen] at H2
    rw [not_not,length_le_iff (L++[s])]
    exact H2
}


lemma mul_le_of_lt_of_mul_lt (s:S) (w:G) (h: s*w < w) : x < w → s*w ≤ w:=by {
  intro h1
  if (s*x < x) then {sorry}
  else {sorry}
}

lemma length_mul_le_sum  (u v:G): ℓ(u*v) ≤ ℓ(u) + ℓ(v):= by{
   rcases exist u with ⟨Lu,⟨hu1,hu2⟩⟩
   rcases exist v with ⟨Lv,⟨hv1,hv2⟩⟩
   have : u*v =(Lu ++ Lv).gprod:=by{
      rw [hu2,hv2]
      exact eq_comm.1 gprod_append
   }
   have hlu: Lu.length = length S u:=by{
      rw [hu2]
      exact (length_eq_iff Lu).1 hu1
   }
   have hlv:Lv.length = length S v:=by{
      rw [hv2]
      exact (length_eq_iff Lv).1 hv1
   }
   rw [this]
   have H:length S (List.gprod (Lu ++ Lv)) ≤ Lu.length + Lv.length:= by{
      have :=length_le (Lu ++ Lv)
      rw [List.length_append] at this
      assumption
   }
   rw [←hlu,←hlv]
   assumption
}

lemma length_mul_ge_sub (u v :G) : ℓ(u) - ℓ(v) ≤ ℓ(u*v) :=by{
   if h:ℓ(u) ≤ ℓ(v) then {
      have := Nat.sub_eq_zero_iff_le.2 h
      rw [this]
      exact Nat.zero_le (length S (u * v))
   }
   else{
      have := length_mul_le_sum (u*v) v⁻¹
      rw [mul_inv_cancel_right,length_inv] at this
      push_neg at h
      exact Nat.sub_le_iff_le_add.2 this
   }
}

lemma length_mul_ge_sub' (u v :G) : ℓ(v) - ℓ(u) ≤ ℓ(u*v) := by{
   have :=length_mul_le_sum (v⁻¹*u⁻¹) u
   rw [mul_assoc] at this
   simp at this
   rw [←mul_inv_rev,length_inv] at this
   exact Nat.sub_le_of_le_add this
}



section  generator_mul

lemma generator_mul_eq_one (s:S) (w:G) : s*w=1 → w=s:=by{
   intro h
   rw [mul_eq_one_iff_inv_eq]at h
   rw [←inv_eq_self'',h]
}

lemma mul_generator_eq_one (w:G) (s:S) : w*s=1 → w=s:=by{
   intro h
   rw [mul_eq_one_iff_eq_inv]at h
   rw [←inv_eq_self'',h]
}

lemma eq_generator_mul_of_generator_mul_eq {s:S} {w u:G} : s*w=u → w=s*u := by
   intro h
   rw [←h, ←mul_assoc, gen_square_eq_one', one_mul]


lemma generator_mul_eq_iff (s : S) (w u : G) :
   s * w = u ↔ w = s * u :=
   ⟨eq_generator_mul_of_generator_mul_eq, fun h => (by rw [h,←mul_assoc,gen_square_eq_one',one_mul])⟩

lemma length_generator_mul_le_sum (s:S) (w:G) : ℓ(s*w) ≤ 1+ℓ(w) := by {
   have :=length_mul_le_sum s.val w
   rw [length_generator_eq_one] at this
   assumption
}

@[simp] lemma generator_mul_twice (w:G) (s:S): s*s*w=w:=by rw [gen_square_eq_one',one_mul]

@[simp] lemma mul_generator_twice (w:G) (s:S): w*s*s=w:=by rw [mul_assoc,gen_square_eq_one',mul_one]

lemma length_generator_mul_le_sub (s:S) (w:G) : ℓ(w) - 1 ≤ ℓ(s*w):=by{
   have :=length_mul_ge_sub' s.1 w
   rw [length_generator_eq_one] at this
   assumption
}


lemma length_generator_mul_neq_length_self (s:S) (w:G) : ℓ(s*w) ≠ ℓ(w):=by {
   rcases exist w with ⟨L,h⟩
   by_cases h0: w =1
   {
      rw [h0,mul_one,length_generator_eq_one,length_one_eq_zero]
      simp
   }
   {
      by_cases h1: ℓ(w) < ℓ(s*w)
      {linarith}
      {
         push_neg at h1
         rw [h.2] at h1
         have := @CoxeterSystem.exchange G S _ _ _ L s h.1 h1
         rw [←h.2] at this
         rcases this with ⟨i,hi⟩
         have h3:=length_generator_mul_le_sub s w
         have h4: reduced_word (List.removeNth L i):=by{
            apply (length_le_iff (List.removeNth L i)).2
            simp_rw [←hi,List.length_removeNth (Fin.is_lt i),(length_eq_iff L).1 h.1,←h.2]
            assumption
         }
         rw [length_eq_iff (List.removeNth L ↑i),List.length_removeNth (Fin.is_lt i),←hi,(length_eq_iff L).1 h.1,←h.2] at h4
         rw [←h4]
         have h5:= length_neq_zero_of_neq_one h0
         exact Nat.pred_ne_self h5
      }
   }
}

lemma inv_mul (w:G) (s:S): (w*s)⁻¹ = s.1⁻¹*w⁻¹ :=mul_inv_rev w s


lemma length_mul_generator_neq_length_self (w:G) (s:S) : ℓ(w*s) ≠ ℓ(w):=fun h => (by{
   rw [←length_inv,mul_inv_rev,←inv_eq_self s.1 s.2,←length_inv w] at h
   exact length_generator_mul_neq_length_self s w⁻¹ h
})

lemma length_generator_mul (s:S) (w:G) : ℓ(s*w) = ℓ(w)+1 ∨ ℓ(s*w) = ℓ(w)-1:=by{
   have h1:=Nat.lt_or_gt.1 (length_generator_mul_neq_length_self s w)
   exact Or.elim h1 (fun hlt => (Or.inr ((LE.le.ge_iff_eq (Nat.le_sub_one_of_lt hlt)).1 (length_generator_mul_le_sub s w)))) (by{
      intro h2
      left
      have h3:= length_generator_mul_le_sum s w
      linarith
   })
}
#check length_generator_mul

lemma length_mul_generator (w:G) (s:S) : ℓ(w*s) = ℓ(w)+1 ∨ ℓ(w*s) = ℓ(w)-1:= lr_symm (motive := fun (n:ℕ) (m:ℕ) => m = n+1 ∨ m = n-1) _ _ length_generator_mul
   -- have :=length_generator_mul s w⁻¹
   -- exact Or.elim this (fun h =>(by rw [←length_inv,inv_mul,←generator_inv s,←length_inv w];left;assumption)) (
   --    fun h => (by rw [←length_inv,inv_mul,←generator_inv s,←length_inv w];right;assumption)
   -- )


@[simp]lemma length_generator_mul_of_length_lt (s:S) (w:G) : ℓ(s*w) < ℓ(w) ↔ ℓ(s*w) = ℓ(w)-1:= by{
   constructor
   .  intro h
      have h1:=length_generator_mul s w
      exact Or.elim h1 (fun h2=> (by{
         have : length S (↑s * w) > length S w:= by linarith
         have hlt_self : ℓ(w)<ℓ(w):= by linarith
         exact byContradiction (fun _ => (LT.lt.false hlt_self))
      })) (fun h2 =>h2)
   .  intro h
      by_cases h1:w=1
      .  rw [h1] at h
         simp only[mul_one,length_one_eq_zero,length_generator_eq_one] at h
      .  rw [h,←Nat.pred_eq_sub_one]
         exact Nat.pred_lt (length_neq_zero_of_neq_one h1)
}


lemma length_generator_mul_of_length_gt (s:S) (w:G) : ℓ(w) < ℓ(s*w) ↔ ℓ(s*w) = ℓ(w)+1:=sorry

@[simp]lemma length_mul_generator_of_length_lt (w:G) (s:S) : ℓ(w*s) < ℓ(w) ↔ ℓ(w*s) = ℓ(w)-1:=sorry

lemma length_mul_generator_of_length_gt (w:G) (s:S) : ℓ(w) < ℓ(w*s) ↔ ℓ(w*s) = ℓ(w)+1:=sorry

lemma reduced_word_of_generator_mul_of_length_gt {s:S} {w:G} {L:List S} (h:reduced_word L) (heq:w=L.gprod) : ℓ(w) < ℓ(s*w) → reduced_word (s::L) ∧ (s::L).gprod = s*w:=by{
   intro h1
   have h2: (s::L).gprod = s*w:= by{rw [gprod_cons s L,heq]}
   have h3: (s::L).length = ℓ(w)+1:=by{rw[List.length_cons,heq,(length_eq_iff L).1 h]}
   have hle : (s :: L).length ≤ ℓ(s*w):=by linarith
   rw [←h2] at hle
   rw [heq]
   exact ⟨(length_le_iff (s :: L)).2 hle,gprod_cons s L⟩
}

lemma reduced_word_of_mul_generator_of_length_gt {w:G} {s:S} {L:List S} (h:reduced_word L) (heq:w=L.gprod) : ℓ(w) < ℓ(w*s) → reduced_word (L++[s]) ∧ (L++[s]).gprod = w*s:=by{
   sorry
}

lemma length_mul_lt_of_mem_D_L (w:G) (h:w≠ 1) (h2:s ∈ D_L w) : ℓ(s*w) < ℓ(w):=by{
   rw [D_L] at h2
   have :s ∈ T_L w:= ((Set.mem_inter_iff s (T_L w) S).1 h2).1
   exact this.2
}

lemma non_mem_D_L_of_length_mul_gt (w:G) (h2:ℓ(w) < ℓ(s*w)) : s ∉ D_L w := by{
   contrapose h2
   push_neg at *
   apply le_of_lt
   have :=Set.mem_of_mem_inter_left h2
   simp [T_L] at this
   exact this.2
}

lemma length_mul_lt_of_mem_D_R (w:G) (h:w≠ 1) (h2:s ∈ D_R w) : ℓ(w*s) < ℓ(w):=by{
   rw [D_R] at h2
   have :s ∈ T_R w:= ((Set.mem_inter_iff s (T_R w) S).1 h2).1
   exact this.2
}

lemma non_mem_D_R_of_length_mul_gt (w:G) (h2:ℓ(w) < ℓ(w*s)) : s ∉ D_R w := by{
   contrapose h2
   push_neg at *
   sorry
}
-- lemma Nat.le_sub_one_of_lt (h : m < n) :m ≤ n - 1 :=sorry

lemma length_mul_of_mem_D_L (w:G) (h:w≠1) (h2:s ∈ D_L w) : ℓ(s*w) = ℓ(w) -1 :=by{
   have hs: s∈S:=((Set.mem_inter_iff s (T_L w) S).1 h2).2
   have h3:=length_generator_mul_le_sub ⟨s,hs⟩ w
   simp at h3
   have h4: ℓ(w) - 1 ≤ ℓ(s*w):=by{
      simp
      assumption}
   have h5: ℓ(s*w) ≤ ℓ(w) -1:= by {exact Nat.le_sub_one_of_lt (length_mul_lt_of_mem_D_L w h h2)}
   linarith
}

lemma length_mul_of_mem_D_R (w:G) (h:w≠1) (h2:s ∈ D_R w) : ℓ(w*s) = ℓ(w) -1 :=by{
   sorry
}

lemma length_lt_S_mul_of_length_S_mul_S_lt (s t :S) (w:G) : ℓ(s*w*t) < ℓ(w) → ℓ(s*w*t) <ℓ(s*w) :=by{
   have h:= length_mul_generator (s*w) t
   intro hlt
   rcases h with hadd|hsub
   {
      have h1:=length_generator_mul_le_sub s w
      rw [Nat.sub_le_iff_le_add,←hadd] at h1
      exact byContradiction (fun _ =>(lt_iff_not_ge _ _).1 hlt h1)
   }
   {
      by_cases h2: s*w=1
      {
         have : w=s:=generator_mul_eq_one _ _ h2
         rw [h2,one_mul,this,length_generator_eq_one,length_generator_eq_one]at hlt
         linarith
      }
      {
         rw [hsub]
         exact Nat.pred_lt (length_neq_zero_of_neq_one h2)
      }
   }
}

lemma length_S_mul_lt_of_length_S_mul_S_lt (s t :S) (w:G) : ℓ(s*w*t) < ℓ(w) → ℓ(s*w) <ℓ(w) :=by{
   intro hlt
   have hsub: length S (s * w * t) = length S (↑s * w) - 1:=(length_mul_generator_of_length_lt (s*w) t).1 (length_lt_S_mul_of_length_S_mul_S_lt s t w hlt)
   have h1:=length_generator_mul s w
   rcases h1 with hadd'|hsub'
   {
      rw [hadd'] at hsub
      rw [hsub] at hlt
      exact byContradiction (fun _ => LT.lt.false hlt)}
   {
      by_cases h2: w=1
      {
         rw [h2,length_one_eq_zero] at hlt
         by_contra!
         exact ((lt_iff_not_ge _ _).1 hlt ) (Nat.zero_le ℓ(s * 1 * t))
      }
      {
         rw [hsub']
         exact Nat.pred_lt (length_neq_zero_of_neq_one h2)
      }
   }
}

lemma length_S_mul_gt_of_length_S_mul_S_gt (s t :S) (w:G) : ℓ(w) < ℓ(s*w*t) → ℓ(w) <ℓ(s*w) :=sorry

lemma length_gt_S_mul_of_length_S_mul_S_gt (s t :S) (w:G) : ℓ(w) < ℓ(s*w*t) → ℓ(s*w) <ℓ(s*w*t) :=sorry

lemma length_S_mul_eq_length_mul_S_of_neq (s t :S) (w:G): ℓ(s*w*t) ≠ ℓ(w) → ℓ(s*w)=ℓ(w*t):=by{
   intro h
   cases (Ne.lt_or_lt h) with
   | inl => (sorry)
   | inr => (sorry)
}


lemma S_mul_eq_mul_S_of_length_eq_aux {s t:S} (w:G) (h_1:ℓ(s*w*t) = ℓ(w)) (h_2:ℓ(s*w)=ℓ(w*t)): ℓ(w) < ℓ(w*t) → s*w=w*t:=by{
   rcases exist w with ⟨L,hL⟩
   intro h1
   have h2:=reduced_word_of_mul_generator_of_length_gt hL.1 hL.2 h1
   rw [←h_1] at h1
   have :=@CoxeterSystem.exchange G S _ _ _ (L++[t]) s h2.1
   rw [h2.2,←mul_assoc] at this
   rcases (this (le_of_lt h1)) with ⟨i,hi⟩
   by_cases haux:i = L.length
   .  rw [haux,←List.concat_eq_append,List.removeNth_concat L,←hL.2,mul_assoc,generator_mul_eq_iff s (w*t) w,eq_comm] at hi
      assumption
   .  have haux' : i < L.length :=by {
         have h3:=Fin.is_lt i
         simp only [List.length_append]at h3
         exact Ne.lt_of_le haux (Nat.le_of_lt_succ h3)
      }
      rw [List.removeNth_append_lt,mul_assoc] at hi
      have h3:=(generator_mul_eq_iff s (w*t) _).1 hi
      have h4:=mul_generator_twice w t
      rw [h3,gprod_append,gprod_singleton,mul_assoc,mul_assoc,gen_square_eq_one',mul_one] at h4
      have h5 :=(generator_mul_eq_iff ..).1 h4
      have h6:= h5 ▸ (length_le (List.removeNth L ↑i))
      rw [List.length_removeNth,(length_eq_iff L).1 hL.1,←hL.2] at h6
      by_contra
      rw [h_1,←h_2] at h1
      exact (lt_self_iff_false _).1 (lt_of_lt_of_le (lt_of_lt_of_le h1 h6) (Nat.pred_le ℓ(w)))
      assumption
      assumption
}
#check lt_self_iff_false

lemma S_mul_eq_mul_S_of_length_eq (s t:S) (w:G) :ℓ(s*w*t) = ℓ(w) ∧ ℓ(s*w)=ℓ(w*t) → s*w=w*t:=by{
   intro h
   by_cases h1: ℓ(w) < ℓ(w*t)
   .  exact  S_mul_eq_mul_S_of_length_eq_aux w h.1 h.2 h1
   .  push_neg at h1
      have := Ne.lt_of_le (length_mul_generator_neq_length_self w t) h1
      nth_rw 2[←mul_generator_twice w t] at this
      have h1':ℓ(s*(w*t)*t)=ℓ(w*t):=by rw[mul_assoc,mul_generator_twice,h.2]
      have h2':ℓ(s*(w*t))=ℓ(w*t*t):=by rw[mul_generator_twice,←mul_assoc,h.1]
      have h3:= S_mul_eq_mul_S_of_length_eq_aux (w*t) h1' h2' this
      rw [generator_mul_eq_iff,mul_generator_twice,eq_comm] at h3
      assumption
}


end generator_mul

section epsilon_map

noncomputable def eps : G → ℤ:= fun w => (-1)^ℓ(w)

lemma eps_ne_zero : ∀w:G, eps w ≠ 0:= by{
   intro w
   rw [eps]
   apply pow_ne_zero
   linarith
}
@[simp]
lemma eps_one : eps (1:G) = 1:=by simp[eps]

@[simp]
lemma eps_generator {s:S}: eps s.1 = -1:= by{
   rw [eps,length_generator_eq_one]
   linarith
}


lemma eps_s_mul (s:S) (u:G) : eps (s*u) = eps s.1 * eps u := by{
   by_cases h0: u = 1
   {rw [h0,mul_one,eps_one,mul_one]}
   {
      repeat
         rw [eps]
      have :=length_generator_mul s u
      exact Or.elim this (fun h1 => by{
         rw [h1,length_generator_eq_one,pow_add]
         simp}) (fun h2 => (by{
            rw [h2,length_generator_eq_one,←pow_add]
            conv =>
               lhs
               rw [←mul_one ((-1) ^ (length S u - 1))]
               arg 2
               rw [ ←neg_one_pow_two]
            rw [←pow_add,←@Nat.sub_add_comm,add_comm]
            simp
            exact Nat.one_le_iff_ne_zero.2 (length_neq_zero_of_neq_one h0)
      }))}
}

lemma eps_is_homo_aux : ∀l, ∀ (u v:G), l = ℓ(u) → eps u * eps v = eps (u*v):=by{
   intro l
   induction' l with l hl
   {
      intro u v h
      have := eq_one_of_length_eq_zero u (eq_comm.1 h)
      rw [this,eps_one]
      simp
   }
   {
      intro u v h
      have : u ≠ 1 :=by{
         have : ℓ(u) ≠ 0 :=by {
            rw [←h]
            exact Nat.succ_ne_zero l
         }
         contrapose this
         push_neg at *
         rw [this]
         exact length_one_eq_zero
      }
      let s:= Classical.choice (nonemptyD_L u this)
      have hsub_one :=length_mul_of_mem_D_L u this s.2
      rw [←h,Nat.succ_sub_one] at hsub_one
      have h1:= hl (s*u) v (eq_comm.1 hsub_one)
      have hs:s.1∈S := Set.mem_of_mem_inter_right s.2
      --have htest: s.val = (Subtype.mk s.1 hs).val :=sorry
      rw [eps_s_mul ⟨s.1,hs⟩ u,mul_assoc s.val u v,eps_s_mul ⟨s.1,hs⟩ ,eps_generator] at h1
      linarith
   }
}

lemma eps_is_homo : ∀ (u v:G), eps u * eps v = eps (u*v):=by{
   intro u v
   have := eps_is_homo_aux ℓ(u) u v
   exact this rfl
}


end epsilon_map
