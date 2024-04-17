import Coxeter.CoxeterMatrix.Basic

open HOrderTwoGenGroup CoxeterGroup
variable {G: Type _} [Group G] [hG :CoxeterGroup G]

def adjL (u v:G) := ℓ(u) < ℓ(v) ∧ ∃ s∈S , s*u=v

lemma well_founded_aux : ∀l ,∀ x, l = ℓ(x) → Acc (@adjL G _ _) x:=by
  intro l
  induction' l with l h
  · intro x hx
    have :x = 1 := sorry
    apply Acc.intro
    intros y hy
    simp [adjL,←hx] at hy
  · intro x hx
    apply Acc.intro
    intro y hy
    rw [adjL] at hy
    have : l = length y := sorry
    exact h y this

theorem well_founded_adjL : WellFounded (@adjL G _ _ ) :=by{
  apply WellFounded.intro
  intro x
  exact well_founded_aux (ℓ(x)) x rfl
}

lemma length_of_adjL {u v :G} (h: adjL u v) : ℓ(u) = ℓ(v) - 1:= by
  rw [adjL ] at h
  obtain ⟨s,⟨hs1,hs2⟩⟩ :=h.2
  rw [←hs2] at h
  sorry
  -- have :=length_generator_mul_le_sum ⟨s,hs1⟩ u
  -- simp at this
  -- rw [←hs2]
  -- have h3: ℓ(u) ≤ ℓ(s*u) - 1 := Nat.le_sub_one_of_lt h.1
  -- apply (LE.le.ge_iff_eq h3).1
  -- rw [Nat.add_comm] at this
  -- exact Nat.sub_le_of_le_add this


lemma adjL_of_generator_mul_of_length_lt {u v :G} {s:hG.S} (h:s*u = v) (hlt: ℓ(u) < ℓ(v)) : adjL u v:= by{
  rw [adjL]
  exact ⟨hlt,⟨s,⟨s.2,h⟩⟩⟩
}


lemma adjL_of_mem_leftDescent  {u:G} (s: leftDescent u) : adjL (s*u) u:= by {
  sorry
}


#check WellFounded.fix
