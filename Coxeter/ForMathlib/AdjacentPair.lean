import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic

namespace List
variable {α : Type*}

/- Definition: The adjacent pairs of a list [a_1,a_2, ⋯, a_n] is defined to be
  [(a_1, a_2), (a_2, a_3), ⋯, (a_{n-1}, a_n)].
  If the list L has length less than 2, the new list will be an empty list by convention. -/
@[simp]
def adjPairs : List α  → List (α × α)
  | [] => []
  | _ :: []  => []
  | a :: b :: l =>  ((a, b) : α  × α) ::  (b :: l).adjPairs

/-
Lemma: Let a b ∈ α, then for any list L of α, the pair (a,b) is an adjacent pair of the list [a,b,L].
-/
lemma adjPairs_cons {a b :α} {L : List α} : (a,b) ∈ (a::b::L).adjPairs:= by
  simp [List.adjPairs]

/-Lemma: Let h a b ∈ α and tail be a list of α. If (a,b) is an adjacent pair of tail, then (a,b) is an adjacent pair of [h, tail].
-/
lemma adjPairs_tail {h a b : α} {tail : List α} : (a,b) ∈ tail.adjPairs → (a,b) ∈ (h::tail).adjPairs:= by
  match tail with
  | [] => simp [adjPairs]
  | h' :: l' =>
    simp [adjPairs]
    intro h1
    right; exact h1


lemma mem_adjPairs_iff {a b : α} {L : List α} : (a,b) ∈ L.adjPairs ↔ ∃ l₁ l₂ : List α, L = l₁ ++ a :: b :: l₂ := by
  constructor
  · intro h
    induction L with
    | nil => simp at h
    | cons e tail he =>
        by_cases h' : (a, b) ∈ tail.adjPairs
        · have := he h'
          rcases this with ⟨l₁, l₂, hl⟩
          use e :: l₁, l₂
          simp [hl]
        · match tail with
          | [] => simp at h
          | f :: tail' =>
              simp at h
              rcases h with h'' | h''
              · simp [h'']
                use [], tail'
                simp
              · contradiction
  · intro h
    rcases h with ⟨l₁, l₂, h'⟩
    rw [h']
    revert L
    induction l₁ with
    | nil => simp
    | cons e tail he =>
        intro L hL
        have aux : L.tail = tail ++ a :: b :: l₂ := by simp [hL]
        have := he aux
        apply adjPairs_tail this


/- Definition (programming):
The adjacent extened pairs of a List L is a List of adjacent pairs of L together with the claim that e ∈ adjPairs L -/
def adjEPairs (L : List α) : List ({e : α × α  | e ∈ L.adjPairs}) := match L with
  | [] => []
  | _ :: [] => []
  | a :: b :: l =>  ⟨(a, b), List.adjPairs_cons⟩ :: (List.map (fun e => ⟨e.val, List.adjPairs_tail e.prop ⟩) <| List.adjEPairs (b :: l))



end List
