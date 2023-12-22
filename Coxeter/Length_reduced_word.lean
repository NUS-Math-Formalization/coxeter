import Coxeter.Basic
import Coxeter.Bruhat

import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.Linarith.Frontend
import Std.Data.Nat.Lemmas

open Classical

variable {G: Type _} [Group G] {S : Set G} [orderTwoGen S] [CoxeterSystem G S]
local notation:max "ℓ(" g ")" => (@length G _ S _ g)

lemma length_le (L : List S) :  ℓ(L.gprod) ≤ L.length := by{
   have h: ∃ (L1 : List S), L1.length = L.length ∧ L.gprod = L1.gprod:=by{use L}
   exact Nat.find_le h
}



lemma reduced_word_inv (L: List S) (h: reduced_word L): reduced_word L.reverse:= by{
   contrapose h
   rw [reduced_word] at *
   push_neg at *
   rcases h with ⟨LL,hL⟩
   use LL.reverse
   rw [gprod_reverse,List.length_reverse] at *
   rw [←hL.1,inv_inv]
   exact ⟨rfl,hL.2⟩
}

lemma length_inv_eq_length_self (g : G) : ℓ(g⁻¹)  =  ℓ(g) := sorry

lemma nil_is_reduced_word: reduced_word ([] : List S) := by {
   rintro _ _
   norm_num
}

lemma singleton_is_reduced_word {s:S}: reduced_word [s]:= by{
   rintro L hL
   contrapose hL
   push_neg at *
   rw [List.length_singleton] at hL
   have : List.length L = 0:=by{linarith}
   have h1 :=List.length_eq_zero.1 this
   rw [h1,gprod_nil,gprod_singleton]
   exact non_one s.1 s.2
}

lemma pos_length_of_non_reduced_word (L : List S): ¬ reduced_word L → 1 ≤  L.length := by {
   contrapose
   simp_rw [not_le,not_not,Nat.lt_one_iff]
   rw [List.length_eq_zero];
   intro H
   simp only [H,nil_is_reduced_word]
}

lemma reduced_word_iff_length_le (L: List S) :
   reduced_word L  ↔   L.length ≤ ℓ(L.gprod):= by {
      rw [length, (Nat.le_find_iff _)]
      apply Iff.intro
      . {
         intro h m hm
         contrapose hm
         rw [not_not] at hm
         let ⟨L', HL'⟩ := hm
         rw [not_lt,<-HL'.1]
         exact h L'  HL'.2
       }
      . {
         intro H
         rw [reduced_word]
         intro L' HL'
         contrapose H
         rw [not_le] at H
         rw [not_forall]
         use L'.length
         rw [<-not_and,not_not]
         constructor
         . exact H
         . {
            use L'
            --exact ⟨rfl,HL'⟩
         }
      }
   }

lemma reduced_word_iff_length_eq (L: List S) :
   reduced_word L  ↔ L.length = ℓ(L.gprod) := by
{
   constructor
   . {
     intro H
     exact ge_antisymm  (length_le  L)  ((reduced_word_iff_length_le  L).1 H)
   }
   . {
     intro H
     exact (reduced_word_iff_length_le  L).2 (le_of_eq H)
   }
}



lemma length_one_eq_zero : ℓ((1 : G)) = 0 := by {
   have h:= (reduced_word_iff_length_eq  []).1 (@nil_is_reduced_word G _ S _)
   simp at h
   rw [h]
}

lemma eq_one_of_length_eq_zero (w:G) : ℓ(w)=0 → w =1 := by{
   intro h
   simp [length] at h
   rcases h with ⟨L,⟨hL,hLL⟩⟩
   have : L = []:= List.eq_nil_of_length_eq_zero hL
   rw [this] at hLL
   simp at hLL
   assumption
}


lemma length_generator_eq_one (s:S) : ℓ(s) = 1:= by{
   apply (Nat.find_eq_iff (length_aux s.1)).2
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
      exact non_one s.1 s.2
   }
}

lemma reduced_word_exist (g : G) :∃ (L: List S) , reduced_word L ∧ g = L.gprod := by
{
   let ⟨L',h1,h2⟩ := Nat.find_spec (@length_aux G  _ S  g _)
   use L'
   have C1 := (reduced_word_iff_length_eq  L').2
   rw [length] at C1
   simp_rw [h2] at h1
   exact ⟨C1 h1,h2⟩
}



def non_reduced_p  (L : List S) := fun k => ¬ reduced_word (L.take (k+1))

lemma max_reduced_word_index_aux (L: List S) (H : ¬ reduced_word L) : ∃ n, non_reduced_p  L n := by {
   use L.length
   rw [non_reduced_p,List.take_all_of_le (le_of_lt (Nat.lt_succ_self L.length))]
   exact H
}

noncomputable def max_reduced_word_index (L : List S) (H : ¬ reduced_word L):= Nat.find (max_reduced_word_index_aux  L H)

lemma nonreduced_succ_take_max_reduced_word (L : List S) (H : ¬ reduced_word L) : ¬ reduced_word (L.take ((max_reduced_word_index  L H)+1)) := by {
   let j:= max_reduced_word_index  L H
   have Hj : j = max_reduced_word_index  L H := rfl
   rw [<-Hj]
   rw [max_reduced_word_index]  at Hj
   have HH:= (Nat.find_eq_iff _).1 Hj
   rw [<-Hj,non_reduced_p] at HH
   exact HH.1
}

lemma reduced_take_max_reduced_word (L : List S) (H : ¬ reduced_word L) : reduced_word (L.take (max_reduced_word_index L H)) := by {
   let j:= max_reduced_word_index L H
   have Hj : j = max_reduced_word_index  L H := rfl
   match j with
   | 0 =>  {
      rw [<-Hj,List.take_zero]
      exact nil_is_reduced_word
    }
   | n+1 => {
      rw [<-Hj]
      have := (Nat.le_find_iff _ _).1 (le_of_eq Hj) n (Nat.lt_succ_self n)
      rw [non_reduced_p,not_not] at this
      exact this
   }
}


lemma length_lt_not_nil (L : List S) (s : S) : ℓ(L.gprod * s) < ℓ(L.gprod) → L ≠ [] := by {
   contrapose
   rw  [ne_eq, not_not, not_lt]
   intro h
   rw [h,gprod_nil,length_one_eq_zero]
   exact zero_le (ℓ((1:G) * s))
}

lemma max_reduced_word_index_lt (L : List S)
(H : ¬ reduced_word L) : max_reduced_word_index  L H < L.length := by {
   have Hlen := pos_length_of_non_reduced_word  L H
   rw [max_reduced_word_index, Nat.find_lt_iff _ L.length]
   use L.length -1
   rw [non_reduced_p]
   have Hlen' : 0<L.length := by linarith
   constructor
   . exact Nat.sub_lt Hlen' (by simp)
   . {
      have : L.length -1 +1  = L.length := by rw [<-Nat.sub_add_comm Hlen,Nat.add_sub_cancel]
      rw [this,List.take_length]
      exact H
   }
}

noncomputable def max_reduced_word_index' (L : List S) (H : ¬ reduced_word L) : Fin L.length:= ⟨max_reduced_word_index  L H, max_reduced_word_index_lt  L H⟩

lemma length_lt_iff_non_reduced (L : List S) :
ℓ(L.gprod) < L.length ↔ ¬ reduced_word L := by {
   rw [iff_not_comm,not_lt]
   exact reduced_word_iff_length_le  L
}



lemma reduced_nonreduced_length_le  (L : List S) (s:S) (H1: reduced_word L) (H2: ¬ reduced_word (L ++ [s])) :
ℓ(L.gprod * s) ≤ ℓ(L.gprod) := by {
    rw [<-(reduced_word_iff_length_eq L).1 H1]
    contrapose H2
    have Hs :[s].gprod = s := gprod_singleton
    have Hlen : (L++[s]).length = Nat.succ L.length := by rw [List.length_append, List.length_singleton]
    rw [not_le,←gprod_singleton,←gprod_append,<-Nat.succ_le_iff,<-Hlen] at H2
    rw [not_not,reduced_word_iff_length_le (L++[s])]
    exact H2
}


lemma mul_le_of_lt_of_mul_lt (s:S) (w:G) (h: s*w < w) : x < w → s*w ≤ w:=by {
  intro h1
  if (s*x < x) then {sorry}
  else {sorry}
}



--map all s∈S to -1,extends to a group homo :W → {-1,1}

-- noncomputable def eps.F (w:G) (f: (u:G) → llr u w → ℤ) : ℤ:= if h:w = 1 then 1
-- else(
--   let s:= Classical.choice (nonemptyD_R w h)
--   (f (s*w) (sorry))* -1
-- )

-- noncomputable def eps : G → ℤ:=@WellFounded.fix G (fun _ => ℤ) llr well_founded_llr (eps.F )

-- lemma eps_apply_aux : ∀l, ∀w, l = ℓ(w) → @eps G _ S _ w = (-1)^ℓ(w):=by{
--   intros l w
--   induction' l with l hl
--   {
--     intro h
--     rw [←h]
--     have hh:= eq_one_of_length_eq_zero  _ (eq_comm.1 h)
--     simp [hh]

--   }

-- }

-- lemma eps_apply (w:G) : eps w = (-1)^ℓ(w):= by{
--   induction ℓ(w)
-- }

lemma length_mul_le_sum  (u v:G): ℓ(u*v) ≤ ℓ(u) + ℓ(v):= by{
   rcases reduced_word_exist u with ⟨Lu,⟨hu1,hu2⟩⟩
   rcases reduced_word_exist v with ⟨Lv,⟨hv1,hv2⟩⟩
   have : u*v =(Lu ++ Lv).gprod:=by{
      rw [hu2,hv2]
      exact eq_comm.1 gprod_append
   }
   have hlu: Lu.length = length u:=by{
      rw [hu2]
      exact (reduced_word_iff_length_eq Lu).1 hu1
   }
   have hlv:Lv.length = length v:=by{
      rw [hv2]
      exact (reduced_word_iff_length_eq Lv).1 hv1
   }
   rw [this]
   have H:length (List.gprod (Lu ++ Lv)) ≤ Lu.length + Lv.length:= by{
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
      exact Nat.zero_le (length (u * v))
   }
   else{
      have := length_mul_le_sum (u*v) v⁻¹
      rw [mul_inv_cancel_right,length_inv_eq_length_self] at this
      push_neg at h
      exact Nat.sub_le_iff_le_add.2 this
   }
}

lemma length_mul_ge_sub' (u v :G) : ℓ(v) - ℓ(u) ≤ ℓ(u*v) := sorry

lemma length_generator_mul_le_sum (s:S) (w:G) : ℓ(s*w) ≤ 1+ℓ(w) := by {
   have :=length_mul_le_sum s.val w
   rw [length_generator_eq_one] at this
   assumption
}

lemma length_generator_mul_le_sub (s:S) (w:G) : ℓ(w) - 1 ≤ ℓ(s*w):=by{
   have :=length_mul_ge_sub' s.1 w
   rw [length_generator_eq_one] at this
   assumption
}


lemma length_mul_lt_of_mem_D_L (w:G) (h:w≠ 1) (h2:s ∈ D_L w) : ℓ(s*w) < ℓ(w):=by{
   rw [D_L] at h2
   have :s ∈ T_L w:= ((Set.mem_inter_iff s (T_L w) S).1 h2).1
   exact this.2
}

lemma length_mul_lt_of_mem_D_R (w:G) (h:w≠ 1) (h2:s ∈ D_R w) : ℓ(w*s) < ℓ(w):=by{
   rw [D_R] at h2
   have :s ∈ T_R w:= ((Set.mem_inter_iff s (T_R w) S).1 h2).1
   exact this.2
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
section epsilon_map

noncomputable def eps : G → ℤ:= fun w => (-1)^ℓ(w)

lemma eps_ne_zero : ∀w:G, eps w ≠ 0:= by{
   intro w
   rw [eps]
   apply pow_ne_zero
   linarith
}

lemma eps_one : eps (1:G) = 1:=by {
   simp[eps]
   rw [length_one_eq_zero]
   linarith
   }

lemma eps_generator {s:S}: eps s.1 = -1:= by{
   rw [eps,length_generator_eq_one]
   linarith
}


lemma eps_s_mul (s:S) (u:G) : eps (s*u) = eps s.1 * eps u := by{
   repeat
      rw [eps]
   sorry
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

lemma length_generator_mul_neq_length_self (s:S) (w:G) : ℓ(s*w) ≠ ℓ(w):=by {
      have :eps (s*w) ≠ eps (w):= by {
      rw [←eps_is_homo,eps_generator,neg_mul,one_mul]
      apply (neg_ne_self ℤ ℤ).2
      exact eps_ne_zero w
      }
      rw [eps,eps] at this
      contrapose this
      push_neg at *
      rw [this]
}

lemma length_generator_mul_neq_length_self1 (s:S) (w:G) : ℓ(s*w) ≠ ℓ(w):=by {
   rcases reduced_word_exist w with ⟨L,h⟩
   sorry
}

end epsilon_map
