-- import Mathlib.Algebra.Field.Basic
-- import Mathlib.Data.Polynomial.RingDivision
-- import Mathlib.FieldTheory.Subfield
-- import Mathlib.GroupTheory.SpecificGroups.Cyclic
-- import Mathlib.Data.Multiset.Basic


-- #check Field.isDomain
-- #check List.maximum_of_length_pos
-- #check Nat.dvd_of_factors_subperm
-- #check Nat.dvd_of_factors_subperm
-- #check isCyclic_of_card_pow_eq_one_le
-- #check Multiset.card

-- variable {G' K : Type _} [Field K] [SetLike G' K]

-- --variable {G : Set K} [DecidableEq G] [Group G] [Fintype G]
-- variable [SubfieldClass G' K] {G : G'} [Fintype G] [DecidableEq G]

-- open
-- instance : SubgroupClass G' K := SubfieldClass.toSubgroupClass G'

-- instance : Group G := SubgroupClass.toGroup G' (G := K)
-- #check Subgroup.zpowers
-- section solution1

-- lemma finite_group_exi_greater_order [Fintype G] :
--     ∃ x : G, ∀ y : G, orderOf y ≤ orderOf x :=sorry

-- noncomputable def greater_order_ele :=
--     Classical.choose (finite_group_exi_greater_order (G := G))

-- lemma finiteCommGroup.order_of_ele_dvd  :
--     ∀ x : G, orderOf x ∣ orderOf (greater_order_ele (G := G)) :=sorry

-- def factor_power (p n : ℕ)  : ℕ := List.count p (Nat.factors n)

-- lemma exi_prime_factor_pow_gt_of_not_dvd {m n : Nat} :
--     ¬ m ∣ n → ∃ p : Nat, (factor_power p n ) < factor_power p m := sorry

-- lemma dvd_order_of_goe [CommGroup G] : ∀ h : G, orderOf h∣orderOf (greater_order_ele (G := G)) := sorry

-- theorem finite_subgroup_of_field_is_cyclic_proof1 : IsCyclic G := by sorry

-- end solution1

-- section solution2
-- #check Multiset.card_le_of_le

-- lemma roots_in_subfield_subset_roots_in_field : ∀ n, 0 < n →
--     Finset.card (Finset.filter (α := G) (fun a => a ^ n = 1) Finset.univ) ≤ Multiset.card (Polynomial.nthRoots (R := K) n 1) := by
--         intro n hn
--         have : Finset.card (Finset.filter (α := G) (fun a => a ^ n = 1) Finset.univ) ≤ Finset.card  (Multiset.toFinset (Polynomial.nthRoots (R := K) n 1) )
--         -- have : Multiset.map (↑) ((Multiset.filter (α := G) (fun a => a ^ n = 1) Finset.univ.val)) ≤ Polynomial.nthRoots n 1 (R := K) := sorry
--         -- -- have heq : Multiset.card (Multiset.filter (α := G) (fun a => a ^ n = 1) Finset.univ.val) = Multiset.card (Multiset.map Subtype.val (Multiset.filter (α := G) (fun a => a ^ n = 1) Finset.univ.val)) := sorry
--         -- rw [←Multiset.card_map]
--         -- exact Multiset.card_le_of_le this

-- #check Polynomial.card_roots
-- lemma aux : ∀ n : ℕ, 0 < n →
--     Finset.card (α:=G) (Finset.filter (fun a => a ^ n = 1) Finset.univ) ≤ n := by
--         intro n hn
--         exact le_trans (roots_in_subfield_subset_roots_in_field (G := G) n hn) (by sorry)

-- theorem finite_subgroup_of_field_is_cyclic_proof2  : IsCyclic G :=
--     isCyclic_of_card_pow_eq_one_le (α := ↑G) (aux (G:=G))

-- end solution2
