/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 3 : not in (`∉`) and complement `Aᶜ`

The definition in Lean of `x ∉ A` is `¬ (x ∈ A)`. In other words,
`x ∉ A`, `¬ (x ∈ A)` and `(x ∈ A) → False` are all equal *by definition*
in Lean.

The complement of a subset `A` of `X` is the subset `Aᶜ`; it's the terms of
type `X` which aren't in `A`. The *definition* of `x ∈ Aᶜ` is `x ∉ A`.

For example, if you have a hypothesis `h : x ∈ Aᶜ` and your goal
is `False`, then `apply h` will work and will change the goal to `x ∈ A`.
Think a bit about why, it's a good logic exercise.

-/


open Set

variable (X : Type) -- Everything will be a subset of `X`
  (A B C D E : Set X) [Inhabited A]-- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : x ∉ A → x ∈ A → False := by
 intro hnXA hXA
 exact hnXA hXA

example : x ∉ A → x ∈ A → False := by
 intro hnXA
 exact hnXA

 example : x ∉ A → x ∈ A → False := fun h: x ∉ A ↦ h

example : x ∈ A → x ∉ A → False := by
 intro hxA hnXA
 exact hnXA hxA




example : A ⊆ B → x ∉ B → x ∉ A := by
intro hAiB
contrapose!
revert x
rw [←subset_def (s:=A) (t:=B)]
assumption


-- Lean couldn't work out what I meant when I wrote `x ∈ ∅` so I had
-- to give it a hint by telling it the type of `∅`.
example : x ∉ (∅ : Set X) := by
 intro hx0
 exact hx0

example : x ∉ (∅ : Set X) := fun h ↦ h

example : x ∈ Aᶜ → x ∉ A := by
 intro hnA hxA
 exact hnA hxA

example : x ∈ Aᶜ → x ∉ A := fun hnA hxA ↦ hnA hxA


example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
 constructor
 · intro haX
   push_neg
   intro x
   specialize haX x
   intro hx
   exact (hx haX)
 · intro hnAx
   push_neg at hnAx
   intro x
   specialize hnAx x
   by_contra hC
   exact hnAx hC

example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ :=
 ⟨fun haX ⟨x,hxA⟩ ↦ hxA (haX x), fun hnAx x  ↦ (Classical.em (x ∈ A)).elim (fun h ↦ h) (fun nh ↦ False.elim (hnAx ⟨x,nh⟩)) ⟩


example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by
  constructor
  · rintro ⟨x',hxA⟩
    intro ha
    specialize ha x'
    exact ha hxA
  · intro hna
    push_neg at hna
    obtain ⟨x',hx'⟩ := hna
    by_contra! hC
    specialize hC x'
    exact hx' hC
#check not_forall

example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ :=
  ⟨ fun ⟨x',hXA⟩ ha ↦ (ha x') hXA,
    fun nhAx ↦
      have ⟨x'',hxa''⟩ := (not_forall (α := X) (p := fun x ↦ x ∈ Aᶜ)).mp nhAx;
      Exists.intro x'' ((Classical.em (x'' ∈ A)).elim (fun h ↦ h) (fun nh ↦ False.elim (hxa'' nh) )) ⟩
