import Coxeter.ForMathlib.PosetChain
import Coxeter.ForMathlib.PosetGraded
import Coxeter.ForMathlib.PosetShelling

namespace PartialOrder
variable {P : Type*} [PartialOrder P] [Fintype P]
variable {A : Type*} [PartialOrder A]

instance {x y : P} : Fintype (Set.Icc x y) := sorry -- temporary

/-
Definition: Let `P` and `A` be posets. An edge labelling of `P` in `A` is a map from the set of edges of `P` to the poset `A`.
-/
@[simp]
abbrev edgeLabeling (P A : Type*) [PartialOrder P] := edges P  → A

/-
Definition: Let `P` and `A` be posets and `l` be an edge labelling of `P` in `A`.
Then for any maximal chain `m : x_0 ⋖ x_1 ⋖ ⋯ ⋖ x_n` in `P`, we define a list in `A` by `[l(x_0 ⋖ x_1), l(x_1 ⋖ x_2), ⋯, l (x_{n-1} ⋖ x_n)]`.
-/
def mapMaxChain (l : edgeLabeling P A) (m : maximalChains P) : List A := List.map (fun e => l e) <| edgePairs m

/-
Definition: Let P and A be posets and l be an edge labelling of P in A.
Then any maximal chain m : x_0 ⋖ x_1 ⋖ ⋯ ⋖ x_n in [x,y] ⊂ P, we define a list in A by [l(x_0 ⋖ x_1),l(x_1 ⋖ x_2), ⋯ ,l(x_{n-1} ⋖ x_n)].
-/
def mapMaxChain_interval (l : edgeLabeling P A) {x y : P} (m : maximalChains <| Set.Icc x y)  : List A := List.map (fun e : edges (Set.Icc x y) => l ( sorry
    -- e : edges P
    )) <| edgePairs m

/-Defines the set of risingChains in an interval [x,y]-/
abbrev risingChains (l : edgeLabeling P A) (x y: P) := {m : maximalChains <| Set.Icc x y | List.Chain' (. ≤ .) <| mapMaxChain_interval l m}

/-
Definition: An edge labelling of P is called an EL-labelling if for every interval [x,y] in P,
  (1) there is a unique increasing maximal chain c in [x,y],
  (2) c <_L c' for all other maximal chains c' in [x,y].
Here <_L denotes the lexicographic ordering for the tuples in the labelling poset A.
-/
class ELLabeling (l : edgeLabeling P A) where
  unique {x y: P} (h : x<y) : Unique (risingChains l x y)
  unique_min {x y: P} (h : x<y): ∀ (m' : maximalChains <| Set.Icc x y), m' ≠ (unique h).default → (mapMaxChain_interval l (unique h).default.val < mapMaxChain_interval l m')

open AbstractSimplicialComplex
/-Theorem: Let P be a graded finite poset with an EL-labelling l to a poset A. Then P is shellable.
-/
theorem shellable_of_ELLabeling {P : Type*} [PartialOrder P] [PartialOrder A] [Fintype P] [GradedPoset P] (l : edgeLabeling P A) (h: ELLabeling l): ShellableDelta P := by
  have : Shellable (Delta P) := by
    apply (shellable_iff_shellable').mpr
    rcases h with ⟨uc, ll⟩





  sorry /- have : ShellableDelta P iff -/
  /- have Delta.ASC (P) -/

  /- rw goal as ShellableDelta P → Shellable (Delta P) → Shellable' (Delta P) i.e. ∃ (m : ℕ+) (l : Fin m ≃ Facets Delta P), Shelling' l -/

  /- fix map l from labelling -/

  /- let k : k_0 ⋖ k_1 ⋖ ⋯ ⋖ k_r, m : m_0 ⋖ m_1 ⋖ ⋯ ⋖ m_r be two maximal chains s.t. k < m -/

  /- let d be the greatest integer s.t. kᵢ = mᵢ for i ∈ [0, d], and g the greatest integer s.t. d < g and k_g = m_g -/

  /- then for the interval [m_g, m_d], m_d ⋖ ⋯ ⋖ m_g is not the unique max chain  -/

  /- ∃e ∈ (d, g) s.t. l(m_{e-1} ⋖ m_e) > l(m_e ⋖ m_{e+1})  -/

  /- have a unique increasing max chain in [m_{e-1}, m_{e+1}] : m_{e-1} ⋖ x ⋖ m_{e+1} -/

  /- then h : m_0 ⋖ ⋯ ⋖ m_{e-1} ⋖ x ⋖ m_{e+1} ⋖ ⋯ ⋖ m_r satisfies Shelling' l -/

  /- 'gluing' chains lemma, compare chains -/

end PartialOrder
