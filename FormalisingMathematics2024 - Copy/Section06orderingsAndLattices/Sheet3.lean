/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

/-

# A harder question about lattices

I learnt this fact when preparing sheet 2.

With sets we have `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`, and `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`.
In sheet 2 we saw an explicit example (the lattice of subspaces of a 2-d vector space)
of a lattice where neither `A ⊓ (B ⊔ C) = (A ⊔ B) ⊓ (A ⊔ C)` nor `A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C)`
held. But it turns out that in a general lattice, one of these equalities holds if and only if the
other one does! This was quite surprising to me.

The challenge is to prove it in Lean. My strategy would be to prove it on paper first
and then formalise the proof. If you're not in to puzzles like this, then feel free to skip
this question.

-/
open Lattice

lemma sup_self {L: Type} [Lattice L] (a: L): a ⊔ a = a := by
 simp

#check le_sup_right

example (L : Type) [Lattice L] :
    (∀ a b c : L, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)) ↔ ∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  constructor
  · intro h a b c
    have h1:= h (a ⊓ b) a c
    have h2:= h a a (b ⊔ c)
    simp only [sup_self] at h1 h2
    simp [h1,h2]
    apply le_antisymm
    · apply le_inf
      · exact inf_le_left
      · have ineq1: c ≤ (a ⊓ b) ⊔ c := by
         apply le_sup_right (a:=(a ⊓ b))
        sorry


    sorry
  sorry






    --simp only [sup_self] at h
