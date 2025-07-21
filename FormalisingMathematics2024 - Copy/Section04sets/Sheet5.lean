/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
 ext c
 constructor
 · intro hc
   rcases hc with (h|h) <;> exact h
 · intro hc
   apply Or.inl
   · exact hc

#check union_def
#check funext

example : A ∪ A = A :=
  have (z:X) := (Iff.intro (fun hAuA: z ∈ A ∪ A ↦ hAuA.elim (fun h ↦ h) (fun h ↦ h)) (fun hA:z ∈ A ↦ (@union_def X A A).symm.subst (Or.intro_left (z ∈ A) hA)))
   by exact funext (fun x ↦ propext (this x))



example : A ∩ A = A := by
 ext X
 exact ⟨fun hxAnA ↦ hxAnA.1 , fun hA ↦ ⟨hA,hA⟩⟩

example : A ∩ ∅ = ∅ := by
  ext x
  exact ⟨fun hxAnE ↦ hxAnE.2.elim,fun hxE ↦ hxE.elim⟩

example : A ∩ ∅ = ∅ := inter_empty A

example : A ∪ univ = univ := (union_univ (s := A))

example : A ∪ univ = univ := by
 ext x
 constructor
 · intro hxAuU
   rcases hxAuU with (h|h)
   · exact True.intro
   · exact h
 · intro xU
   exact Or.inr xU


example : A ⊆ B → B ⊆ A → A = B := by
 intro hab hba
 ext x
 exact ⟨fun hx ↦ hab hx,fun hx ↦ hba hx⟩

example : A ⊆ B → B ⊆ A → A = B := Set.eq_of_subset_of_subset

example : A ∩ B = B ∩ A := inter_comm A B

example : A ∩ B = B ∩ A := by
 ext x
 exact ⟨fun xAnB ↦ ⟨xAnB.2,xAnB.1⟩ , fun xBnA ↦ ⟨ xBnA.2, xBnA.1⟩⟩


example : A ∩ (B ∩ C) = A ∩ B ∩ C := (inter_assoc A B C).symm

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
 ext x
 constructor
 · intro xAn_BnC
   constructor
   · exact And.intro xAn_BnC.1 xAn_BnC.2.1
   . exact xAn_BnC.2.2
 · intro xAnB_nC
   constructor
   · exact xAnB_nC.1.1
   · constructor
     · exact xAnB_nC.1.2
     · exact xAnB_nC.2


example : A ∪ (B ∪ C) = A ∪ B ∪ C := (union_assoc A B C).symm

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
 ext x
 constructor
 · intro hxAu_BuC
   rcases hxAu_BuC with (hA|hB|hC)
   · exact Or.inl (Or.inl hA)
   · exact Or.inl (Or.inr hB)
   · exact Or.inr hC
 · rintro ((hA|hB)|hC)
   · exact Or.inl hA
   · exact Or.inr (Or.inl hB)
   · exact Or.inr (Or.inr hC)




example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by exact union_distrib_left A B C

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
 ext x
 constructor
 · rintro (hxa|⟨hb,hc⟩)
   · constructor <;> exact Or.inl hxa
   · exact ⟨Or.inr hb,Or.inr hc⟩
 · rintro ⟨(ha1|hb),(ha2|hc)⟩
   · exact Or.inl ha1
   · exact Or.inl ha1
   · exact Or.inl ha2
   · exact Or.inr ⟨hb,hc⟩



example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := inter_distrib_left A B C

example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
 ext x
 constructor
 · rintro ⟨hxA,(hxB|hxC)⟩
   · exact Or.inl ⟨hxA,hxB⟩
   · exact Or.inr ⟨hxA,hxC⟩
 · rintro (⟨hxA1,hxB ⟩|⟨hxA2,hxC ⟩)
   · exact ⟨hxA1, Or.inl hxB⟩
   · exact ⟨hxA2, Or.inr hxC⟩
