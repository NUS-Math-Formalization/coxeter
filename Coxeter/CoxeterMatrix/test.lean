import Coxeter.CoxeterMatrix.Basic
import Lean
import Std.Tactic.Lint.Frontend

open Lean

#eval Std.Tactic.Lint.getDeclsInCurrModule

#eval (Std.Tactic.Lint.getDeclsInPackage "Coxeter")
