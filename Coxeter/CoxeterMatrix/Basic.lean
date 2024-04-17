import Coxeter.CoxeterMatrix.CoxeterMatrix
import Coxeter.CoxeterMatrix.CoxeterSystem
import Coxeter.CoxeterMatrix.StrongExchange

/-!
# Coxeter System and Coxeter Matrix

We give basic definitions of Coxeter systems and Coxeter matrices.

## Main Definitions

* `CoxeterMatrix` is a symmetric matrix indexed by `S` and with values in `ℕ ∪ {∞}`.
* `OrderTwoGen.ExchangeProp` `OrderTwoGen.DeletionProp` are the properties for `OrderTwoGen` group.
* `CoxeterSystem` is a pair `(W, S)` where `W` is a group and `S` is a set of generators for `W`, satisfying
  `ExchangeProp`, `ExchangeProp'` and `DeletionProp`.
* `CoxeterGroup` is the group associated to a `CoxeterSystem`.

## Main Results

* `CoxeterMatrix.exchange` proves the strong exchange condition for Coxeter matrices.
* `CoxeterMatrix.ReflRepn.pi` gives the permutation representation.
* `CoxeterMatrix.ofCoxeterSystem` proves the Coxeter system by a Coxeter matrix.
* `OrderTwoGen.exchange_imp_deletion` proves that the strong exchange condition implies the deletion condition.
* `OrderTwoGen.deletion_imp_exchange` proves that the deletion condition implies the strong exchange condition.
-/
