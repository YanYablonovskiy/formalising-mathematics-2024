/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic


/-

# Bijections

Like finiteness, there are two ways to say that a function is bijective in Lean.
Furthermore, you will have heard of both of them, although it may well not
have occurred to you that these two ways were particularly different. It turns
out that one of them is more constructive than the other. Let's talk about
the nonconstructive (propositional) way of talking about bijections.

Let `X` and `Y` be types, and say `f : X → Y` is a function.

-/

variable (X Y : Type) (f : X → Y)

-- The `Prop`-valued way of saying that `f` is bijective is simply
-- to say literally that `f` is bijective, i.e., injective and surjective.
example : Prop :=
  Function.Bijective f

-- Because `f` is a function type, a little Lean hack introduced recently
-- actually enables you to use dot notation for this.
example : Prop :=
  f.Bijective

-- The definition of `Function.Bijective f` is
-- `Function.Injective f ∧ Function.Surjective f`, and the definitions of
-- injective and surjective are what you think they are.
example : f.Bijective ↔ f.Injective ∧ f.Surjective := by
  rfl

example : f.Bijective ↔
    (∀ x₁ x₂ : X, f x₁ = f x₂ → x₁ = x₂) ∧ ∀ y : Y, ∃ x : X, f x = y := by
  rfl

-- It's a theorem that `f` is bijective if and only if it has a two-sided
-- inverse. One way is not hard to prove: see if you can do it. Make
-- sure you know the maths proof first! If you can't do this then
-- please ask. There's lots of little Lean tricks which make this
-- question not too bad, but there are lots of little pitfalls too.
example : (∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id) → f.Bijective := by
  rintro ⟨g,hg1,hg2⟩
  rw [Function.Bijective]
  apply And.intro
  · rw [Function.Injective]
    intro a1 a2 hfa
    rw [←id_eq a1,←hg2,Function.comp_apply,hfa,←Function.comp_apply (f:=g),hg2,id_eq]
  · rw [Function.Surjective]
    intro b
    use g b
    rw [←Function.comp_apply (f:=f),hg1,id_eq]



example : (∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id) → f.Bijective :=
  fun ⟨g,hg1,hg2⟩ ↦
  ⟨fun a1 a2 hfa ↦ by rw  [←id_eq a1,←hg2,Function.comp_apply,hfa,←Function.comp_apply (f:=g),hg2,id_eq],
   fun b ↦ ⟨g b, by rw [←Function.comp_apply (f:=f),hg1,id_eq]⟩⟩

-- The other way is harder in Lean, unless you know about the `choose`
-- tactic. Given `f` and a proof that it's a bijection, how do you
-- prove the existence of a two-sided inverse `g`? You'll have to construct
-- `g`, and the `choose` tactic does this for you.
-- If `hfs` is a proof that `f` is surjective, try `choose g hg using hfs`.
example : f.Bijective → ∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id := by
  rintro ⟨hbij,hsurj⟩
  use (fun (y : Y) ↦ (hsurj y).choose)
  apply And.intro
  · ext x
    simp [Exists.choose_spec (_ : ∃ a, f a = x)]
  · ext x
    simp [hbij (Exists.choose_spec (_ : ∃ a, f a = f x))]


--golfed
example : f.Bijective → ∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id := fun ⟨hbij,hsurj⟩ ↦
  ⟨(fun (y : Y) ↦ (hsurj y).choose),⟨funext (fun x ↦ by simp [Exists.choose_spec (_ : ∃ a, f a = x)]),funext (fun x ↦ by simp [hbij (Exists.choose_spec (_ : ∃ a, f a = f x))])⟩⟩
