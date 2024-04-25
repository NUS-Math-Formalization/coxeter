import Coxeter.ForMathlib.AbstractSimplicialComplex

namespace AbstractSimplicialComplex
variable {V : Type*}

section dendrite

/-- An ASC is dendrite, if every face of it is contained in a facet.

Should be made into instance? -/
def Dendrite (F : AbstractSimplicialComplex V) :=
  ∀ f ∈ F, ∃ g ∈ F.Facets, f ⊆ g

end dendrite

section loc_finite

/-- An ASC `F` is locally finite, if for every face `f` of it, there is only finitely many faces `g` containing `f`.
Might be a BAD definition.

Should be made into instance? -/
def LocallyFinite (F : AbstractSimplicialComplex V) :=
  ∀ f ∈ F, Finite {g ∈ F | f ⊆ g}

end loc_finite
