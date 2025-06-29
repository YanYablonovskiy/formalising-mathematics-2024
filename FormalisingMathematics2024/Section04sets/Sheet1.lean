/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 1 : ∪ ∩ ⊆ and all that

Lean doesn't have "abstract" sets like `{π, ℝ², {1,2,3}}` whose elements can
be totally random; it only has *subsets* of a type. If `X : Type` is a type
then the type of subsets of `X` is called `Set X`. So for example the
subset `{1,2,3}` of `ℕ` is a term of type `Set ℕ`.

A term of type `set X` can be thought of in four ways:

1) A set of elements of `X` (i.e. a set of elements all of which have type `X`);
2) A subset of `X`;
3) An element of the power set of `X`;
4) A function from `X` to `Prop` (sending the elements of `A` to `True` and the other ones to `False`)

So `Set X` could have been called `Subset X` or `Powerset X`; I guess they chose `Set X`
because it was the shortest.

Note that `X` is a type, but if `A` is a subset of `X` then `A` is a *term*; the type of `A` is `Set X`.
This means that `a : A` doesn't make sense. What we say instead is `a : X` and `a ∈ A`.
Of course `a ∈ A` is a true-false statement, so `a ∈ A : Prop`.

All the sets `A`, `B`, `C` etc we consider will be subsets of `X`.
If `x : X` then `x` may or may not be an element of `A`, `B`, `C`,
but it will always be a term of type `X`.

-/

namespace Section4sheet1


-- set up variables
variable (X : Type) -- Everything will be a subset of `X`
  (A B C D : Set X) -- A,B,C,D are subsets of `X`

/-
# subset (`⊆`), union (`∪`) and intersection (`∩`)

Here are some mathematical facts:

`A ⊆ B` is equivalent to `∀ x, x ∈ A → x ∈ B`;
`x ∈ A ∪ B` is equivalent to `x ∈ A ∨ x ∈ B`;
`x ∈ A ∩ B` is equivalent to `x ∈ A ∧ x ∈ B`.

All of these things are true *by definition* in Lean. Let's
check this.

-/
theorem subset_def : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := by
  -- ↔ is reflexive so `rfl` works because LHS is defined to be equal to RHS
  rfl

-- Say `x` is an arbitrary element of `X`.
variable (x : X)

theorem mem_union_iff : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  rfl

theorem mem_inter_iff : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
  -- you don't even have to go into tactic mode to prove this stuff
  Iff.rfl
  -- note no `by` -- this is just the term

/-

So now to change one side of these `↔`s to the other, you can
`rw` the appropriate lemma, or you can just use `change`. Or
you can ask yourself whether you need to do this at all.

Let's prove some theorems.

-/

example : A ⊆ A := by
 intro x hxA
 assumption

example : A ⊆ A := fun _ hxA ↦ hxA

example : A ⊆ B → B ⊆ C → A ⊆ C := by
 intro hab hbc
 rw [subset_def]
 intro x hxA
 exact hbc (hab hxA)


example : A ⊆ B → B ⊆ C → A ⊆ C := fun hab hbc ↦ fun _ hxA ↦ hbc (hab hxA)

example : A ⊆ A ∪ B := by
 intro x hxa
 apply Or.inl hxa


example : A ⊆ A ∪ B := fun x hxA ↦ Or.inl hxA

example : A ∩ B ⊆ A := by
 intro x hxAB
 exact hxAB.1

example : A ∩ B ⊆ A := fun x hxAB ↦ hxAB.1

example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := by
 intro hab hac x hxa
 constructor
 · exact hab hxa
 · exact hac hxa

example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := fun hab hac _ hxa ↦ ⟨hab hxa,hac hxa⟩


example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A := by
 intro hba hca x hBuC
 rcases hBuC with (h1|h2)
 · exact hba h1
 · exact hca h2

example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A := fun hba hca _ hBuC ↦ hBuC.elim (fun h1 ↦ hba h1) (fun h2 ↦ hca h2)

example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D := by
 intro hab hcd x hAuC
 rcases hAuC with (ha|hc)
 · exact Or.inl (hab ha)
 · exact Or.inr (hcd hc)

example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D := fun hab hcd _ hAuC ↦ hAuC.elim (fun ha ↦ Or.inl (hab ha)) (fun hc ↦ Or.inr (hcd hc))

example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D := by
 intro hab hcd x hAnC
 constructor
 · exact hab hAnC.1
 · exact hcd hAnC.2

example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D := fun hab hcd _ ⟨hA,hC⟩ ↦ ⟨hab hA,hcd hC⟩
