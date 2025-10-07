/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Jujian Zhang, Kevin Buzzard
-/
import Mathlib.Tactic

namespace Section10sheet1

noncomputable section

/-!

# Topological Spaces in Lean

For any `X : Type`, the type `TopologicalSpace X` is the type of topologies on `X`.
`TopologicalSpace` is a structure; its four fields are one data field `IsOpen : Set X → Prop` (the
predicate on subsets of `X` saying whether or not they're open) and then three proof fields
(`isOpen_univ` saying the whole space is open, `isOpen_inter` saying the intersection of two
opens is open, and `isOpen_sUnion` saying an arbitrary union of opens is open).

Here is a simple example: let's make the discrete topology on a type.
-/

open TopologicalSpace

variable (X : Type)

set_option linter.unusedVariables false -- please stop moaning about unused variables

example : TopologicalSpace X where
  IsOpen (s : Set X) := True -- "Is `s` open? Yes, always"
  isOpen_univ := by
    -- is the whole space open? The goal is `True`
    triv
  isOpen_inter := by
    -- let s and t be two sets
    intros s t
    -- assume they're open
    intros hs ht
    -- Is their intersection open?
    -- By definition, this means "can you prove `True`"?
    triv
  isOpen_sUnion := by
    -- say F is a family of sets
    intro F
    -- say they're all open
    intro hF
    -- Is their union open?
    triv

/-
A much more fiddly challenge is to formalise the indiscrete topology. You will be constantly
splitting into cases in this proof.
-/
#check Set.sUnion_mem_empty_univ
open Set in
example : TopologicalSpace X where
  IsOpen (s : Set X) := s = ∅ ∨ s = Set.univ
  isOpen_univ := Or.inr rfl
  isOpen_inter := fun s t hs ht ↦ by
    dsimp at *
    apply hs.elim <;> apply ht.elim
    iterate 3 (intro h1 h2; apply Or.inl ; simp [h1,h2])
    · intro h1 h2
      apply Or.inr
      simp [h1,h2]
  isOpen_sUnion := by
    intro F ht
    dsimp at *
    simp only [or_iff_not_imp_left,sUnion_eq_empty,not_forall] --mem_insert_iff, mem_singleton_iff,sUnion_eq_empty, not_forall]
    rintro ⟨s, hs, hne⟩
    have : s = Set.univ := by
     have := ht s
     rw [or_iff_not_imp_left] at this
     exact this hs hne
    rw [this] at hs
    exact univ_subset_iff.mp <| subset_sUnion_of_mem hs



-- `isOpen_empty` is the theorem that in a topological space, the empty set is open.
-- Can you prove it yourself? Hint: arbitrary unions are open


example (X : Type) [TopologicalSpace X] : IsOpen (∅ : Set X) := by
  rw [← Set.sUnion_empty]; exact isOpen_sUnion fun a f => f.elim


-- The reals are a topological space. Let's check Lean knows this already
#synth TopologicalSpace ℝ

-- Let's make it from first principles.

@[reducible]
def Real.IsOpen (s : Set ℝ) : Prop :=
  -- every element of `s` has a neighbourhood (x - δ, x + δ) such that all y in this
  -- neighbourhood are in `s`
  ∀ x ∈ s, ∃ δ > 0, ∀ y : ℝ, x - δ < y ∧ y < x + δ → y ∈ s


-- Now let's prove the axioms
lemma Real.isOpen_univ : Real.IsOpen (Set.univ : Set ℝ) := fun x hxs ↦ by refine ⟨1,⟨by linarith,fun y h ↦ by simp⟩⟩

lemma Real.isOpen_inter (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  rw [Real.IsOpen] at *
  intro x hxst
  obtain ⟨d1,hpd1,hd1⟩ := hs x hxst.1
  obtain ⟨d2,hpd2,hd2⟩ := ht x hxst.2
  use min d1 d2
  have : (min d1 d2 ≤ d1) ∧ (min d1 d2 ≤ d2) := by simp
  refine ⟨by simp [hpd1,hpd2], fun y ↦ ?_⟩
  rintro ⟨hmx1,hmx2⟩
  suffices hineq: (x - d1 < y ∧ x - d2 < y) ∧ (y < x + d1 ∧ y < x + d2) from ⟨hd1 y ⟨hineq.1.1,hineq.2.1⟩,hd2 y ⟨hineq.1.2,hineq.2.2⟩⟩
  refine ⟨?_,?_⟩
  <;> (constructor <;> linarith)

lemma Real.isOpen_sUnion (F : Set (Set ℝ)) (hF : ∀ s ∈ F, IsOpen s) : IsOpen (⋃₀ F) := by
  simp only [Real.IsOpen] at *
  intro x hxst
  apply hxst.elim
  intro a ha
  obtain ⟨d,hd,hdy⟩ := hF a ha.1 x ha.2
  exact ⟨d,hd, fun y hy ↦ ⟨a,ha.1,hdy y hy⟩⟩


-- now we put everything together using the notation for making a structure
example : TopologicalSpace ℝ where
  IsOpen := Real.IsOpen
  isOpen_univ := Real.isOpen_univ
  isOpen_inter := Real.isOpen_inter
  isOpen_sUnion := Real.isOpen_sUnion
