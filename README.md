# Formalization of Coxeter groups with Lean 4
This repository formalizes the Coxeter groups in Lean 4.

Files sorted by dependencies:
* `Aux_` : Auxiliary lemmas about List, Nat.
* `OrderTwoGen` : More lemmas.
* `CoxeterSystem` : Defined by exchange property.
* `CoxeterMatrix`, `CoxeterMatrix1` : Defined by group presentation. Currently, work with `CoxeterMatrix1`. The aim here is to prove the strong exchange property.
* `Morphism` : Prove equivalence of Coxeter systems and Coxeter matrixes, as well as results about other maps.
* `BruhatOrder` : Prove things about Bruhat order.

Some notes for developers:
* We are using the Feature Branch workflow. Create a new branch to formalize in, then send a pull request to the master branch.
* `⟨i, hi : i < n⟩` is a `Fin n`, we can `rcases` to get the parts, or simply `.1` or `.val` it to take the value out and `.2` or `.prop` to get the inequality out.
* Consider using `@[deprecated]` if you want to change some stuff.
* Try to follow the conventional formatting of Mathematics in Lean.