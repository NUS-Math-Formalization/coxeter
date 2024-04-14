import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Data.Int.Order.Units

namespace TestGroup

/- Let μ₂ be the group of ℤ/2ℤ. (μ₂ is usually for the algebra group. Maybe we change to ℤ/2ℤ.)
-/
abbrev μ₂ := rootsOfUnity 2 ℤ
@[simp]
abbrev μ₂.gen :μ₂ := ⟨-1, by norm_cast⟩

lemma μ₂.gen_ne_one : μ₂.gen ≠ 1 := by rw [μ₂.gen]; norm_cast

lemma μ₂.mem_iff {z} : z ∈ μ₂ ↔ z = 1 ∨ z = μ₂.gen := by
  constructor
  . intro _
    have : z.val^2 = 1 := by norm_cast; simp only [Int.units_sq, Units.val_one]
    replace := sq_eq_one_iff.1 this
    rcases this with h1|h2
    . exact Or.inl (by simp only [Units.val_eq_one] at h1; exact h1)
    . right; ext; rw [h2]; rfl
  . intro h
    rcases h with h1|h2
    . simp [h1]
    . simp [h2]

lemma μ₂.mem_iff' (z : μ₂) : z = 1 ∨ z = μ₂.gen := by
  have := μ₂.mem_iff.1 z.2
  rcases this with h1|h2
  . left; norm_cast at h1
  . right; norm_cast at h2

lemma μ₂.not_iff_not : ∀ (z : μ₂), ¬z = 1 ↔ z = μ₂.gen := by
  intro z
  constructor
  . have := (μ₂.mem_iff' z)
    rcases this with h1|h2
    . intro h; contradiction
    . intro _; exact h2
  . intro h; rw [h]; simp [gen_ne_one]


lemma μ₂.not_iff_not' : ∀ (z : μ₂), ¬z = μ₂.gen ↔ z = 1 := by
  intro z
  constructor
  . contrapose; rw [not_not]; exact (μ₂.not_iff_not z).mp
  contrapose; rw [not_not]; exact (μ₂.not_iff_not z).mpr

lemma μ₂.gen_square : μ₂.gen * μ₂.gen = 1 := by rw [μ₂.gen]; norm_cast

lemma μ₂.gen_inv : μ₂.gen⁻¹ = μ₂.gen := by rw [μ₂.gen]; norm_cast

lemma μ₂.gen_order_two : orderOf μ₂.gen = 2 := by
  apply orderOf_eq_prime
  . norm_cast
  . exact gen_ne_one

lemma μ₂.even_pow_iff_eq_one {n : ℕ} : μ₂.gen ^ n = 1 ↔ Even n := by
  rw [even_iff_two_dvd, ← μ₂.gen_order_two, orderOf_dvd_iff_pow_eq_one]

lemma μ₂.odd_pow_iff_eq_gen {n : ℕ} : μ₂.gen ^ n = μ₂.gen ↔ Odd n := by
  rw [Nat.odd_iff_not_even, ← μ₂.even_pow_iff_eq_one, not_iff_not]
