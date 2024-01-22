import Coxeter.Length_reduced_word


variable {G: Type _} [Group G] {S : Set G} [orderTwoGen S] [CoxeterSystem G S]
local notation :max "ℓ(" g ")" => (@length G  _ S _ g)


def llr (u v:G) := ℓ(u) < ℓ(v) ∧ ∃ s∈S , s*u=v

def llr' (u v:G) := ℓ(u) < ℓ(v)

lemma well_founded_aux : ∀l ,∀ x, l = ℓ(x) → Acc llr x :=by {
  intro l
  induction' l with l h
  {
    intros x hx
    have :x=1:=sorry
    apply Acc.intro
    intros y hy
    rw [llr,←hx] at hy
    linarith
  }
  {
    intro x hx
    apply Acc.intro
    intro y hy
    rw [llr] at hy
    sorry
  }
}

lemma well_founded_aux' {x:G}:  Acc llr' x :=
  match (ℓ(x) :ℕ) with 
  | 0 => by sorry
  | i + 1 => by sorry


theorem well_founded_llr : WellFounded (@llr G _ S _ ) :=by{
  apply WellFounded.intro
  intro x
  exact well_founded_aux ℓ(x) x rfl
}

lemma length_of_llr {u v :G} (h: llr u v) : ℓ(u) = ℓ(v) - 1:= by{
  rw [llr] at h
  obtain ⟨s,⟨hs1,hs2⟩⟩ :=h.2
  rw [←hs2] at h
  have :=length_generator_mul_le_sum ⟨s,hs1⟩ u
  simp at this
  rw [←hs2]
  have h3: ℓ(u) ≤ ℓ(s*u) - 1 := Nat.le_sub_one_of_lt h.1
  apply (LE.le.ge_iff_eq h3).1
  rw [Nat.add_comm] at this
  exact Nat.sub_le_of_le_add this
}

lemma llr_of_generator_mul_of_length_lt {u v :G} {s:S} (h:s*u = v) (hlt: ℓ(u) < ℓ(v)) : llr u v:= by{
  rw [llr]
  exact ⟨hlt,⟨s,⟨s.2,h⟩⟩⟩
}

lemma llr_of_mem_D_L  {u:G} (s:D_L u) : llr (s*u) u:= by {
  sorry
}


#check WellFounded.fix
