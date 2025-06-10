/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 6 : pushforward and pullback

## Pushforward of a set along a map

If `f : X → Y` then given a subset `S : Set X` of `X` we can push it
forward along `f` to make a subset `f(S) : Set Y` of `Y`. The definition
of `f(S)` is `{y : Y | ∃ x : X, x ∈ S ∧ f x = y}`.

However `f(S)` doesn't make sense in Lean, because `f` eats
terms of type `X` and not `S`, which has type `Set X`.
In Lean we use the notation `f '' S` for this. This is notation
for `Set.image` and if you need any API for this, it's likely
to use the word `image`.

## Pullback of a set along a map

If `f : X → Y` then given a subset `T : Set Y` of `Y` we can
pull it back along `f` to make a subset `f⁻¹(T) : Set X` of `X`. The
definition of `f⁻¹(T)` is `{x : X | f x ∈ T}`.

However `f⁻¹(T)` doesn't make sense in Lean either, because
`⁻¹` is notation for `Inv.inv`, whose type in Lean
is `α → α`. In other words, if `x` has a certain type, then
`x⁻¹` *must* have the same type: the notation was basically designed
for group theory. In Lean we use the notation `f ⁻¹' T` for this pullback.

-/

#check Function.invFunOn_image_image_subset

variable (X Y : Type) (f : X → Y) (S : Set X) (T : Set Y)

example : S ⊆ f ⁻¹' (f '' S) := by
 intro x xS
 simp
 use x


example : S ⊆ f ⁻¹' (f '' S) := by
 intro x xS
 rw [Set.image,Set.preimage]
 use x



example : f '' (f ⁻¹' T) ⊆ T := by exact Set.image_preimage_subset f T


example : f '' (f ⁻¹' T) ⊆ T := by
 intro x hx
 simp at hx
 obtain ⟨x1,hx1⟩ := hx
 rw [hx1.2] at hx1
 exact hx1.1

-- `library_search` will do this but see if you can do it yourself.
example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
 constructor
 · intro h
   rw [Set.preimage]
   intro x xs
   rw [Set.image] at h
   rw [Set.mem_def,setOf]
   have: f x ∈ {x | ∃ a ∈ S, f a = x} := by
    use x
   exact h this
 · intro hsf y yfs
   rw [Set.image] at yfs
   obtain ⟨y1,fxy1⟩ := yfs
   specialize hsf fxy1.1
   rw [Set.preimage] at hsf
   rw [Set.mem_def,setOf] at hsf
   rw [fxy1.2] at hsf
   exact hsf
-- Pushforward and pullback along the identity map don't change anything
-- pullback is not so hard
example : id ⁻¹' S = S := by
 rfl

-- pushforward is a little trickier. You might have to `ext x, split`.
example : id '' S = S := by
 ext x
 constructor
 · intro hxf
   rw [Set.image] at hxf
   obtain ⟨x1,hx1⟩ := hxf
   rw [id] at hx1
   rw [hx1.2] at hx1
   exact hx1.1
 · intro hxS
   rw [Set.image]
   use x
   rw [id]
   constructor
   · exact hxS
   · rfl

-- Now let's try composition.
variable (Z : Type) (g : Y → Z) (U : Set Z)

-- preimage of preimage is preimage of comp
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
 ext x
 constructor
 · intro hx
   rw [Set.preimage,setOf] at *
   rw [Set.preimage]
   rw [Function.comp] at hx
   rw [setOf]
   rw [Set.mem_def] at *
   rw [Set.mem_def] at hx
   rw [Set.mem_def]
   assumption
 · intro hx
   simp only [Set.preimage,setOf,Function.comp] at *
   assumption






-- preimage of preimage is preimage of comp
example : g ∘ f '' S = g '' (f '' S) := by
 ext x
 constructor
 · intro hx
   rw [Set.image]
   simp only [Set.image,Function.comp] at hx
   obtain ⟨x1,hx1⟩ := hx
   use (f x1)
   rw [Set.image]
   constructor
   · use x1
     exact ⟨hx1.1,rfl⟩
   · exact hx1.2
 · intro hx
   simp only [Set.image,Function.comp]
   rw [Set.image] at hx
   obtain ⟨x1,hx1⟩ := hx
   simp only [Set.image] at hx1
   obtain ⟨a,ha⟩ := hx1.1
   use a
   constructor
   · exact ha.1
   · rw [ha.2]
     exact hx1.2
