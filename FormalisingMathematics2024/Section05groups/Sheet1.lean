/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-

# Groups

## How to use Lean's groups

In previous courses I have made groups from scratch, but it's kind of irritating
to do (because all the lemma names like `mul_one` are already taken) and I'm
not entirely sure that most students want to know how to make their own
groups, rings, whatever: what's the point if these things are there already?

So in this sheet I explain how to use Lean's groups.

-/

-- let G be a group
variable (G : Type) [Group G]

example (g : G) : g⁻¹ * g = 1 :=
/-  Let's see what just happened.
    The tactic state now looks like this:

    G : Type
    inst✝ : Group G
    g : G
    ⊢ g⁻¹ * g = 1

    So G is what most mathematicians would call a "set", and what in this course
    we call a "type" (they're the same thing as far as you're concerned), and
    `g : G` just mean "g is an element of G". The remaining thing is this
    `inst✝` thing, and that means "G has a multiplication `*`, an identity `1`,
    an inverse function `⁻¹`, and satisfies all the group axioms; furthermore
    all of this will be taken care of by "instances", which are a part
    of Lean's "type class inference system". The type class inference system
    is the system which deals with stuff in square brackets. You don't have
    to worry about it right now -- all that matters is that you have access
    to all the group axioms. This one is called `inv_mul_self g`.
-/
  inv_mul_self g

-- Why don't you use `exact?` to see the names of the other axioms
-- of a group? Note that when `exact?` has run, you can click on
-- the output (the blue output in the infoview) and replace `exact?`
-- with the name of the axiom it found. Note also that you can instead *guess*
-- the names of the axioms. For example what do you think the proof of `1 * a = a` is called?
example (a b c : G) : a * b * c = a * (b * c) := by
  rw [mul_assoc]

-- can be found with `library_search` if you didn't know the answer already
example (a : G) : a * 1 = a := by
  exact mul_one a

-- Can you guess the last two?
example (a : G) : 1 * a = a := by
  exact one_mul a

example (a : G) : a * a⁻¹ = 1 := by
  exact (mul_inv_eq_one.mpr (Eq.refl a))

-- As well as the axioms, Lean has many other standard facts which are true
-- in all groups. See if you can prove these from the axioms, or find them
-- in the library.
-- let a,b,c be elements of G in the below.
variable (a b c : G)

example : a⁻¹ * (a * b) = b := by
  rw [←mul_assoc]
  rw [inv_mul_eq_one.mpr (Eq.refl a)]
  rw [one_mul]


example : a * (a⁻¹ * b) = b := by
  rw [←mul_assoc]
  rw [(mul_inv_eq_one.mpr (Eq.refl a))]
  rw [one_mul]

#check inv_eq_of_mul_eq_one_left

example {a b c : G} (h1 : b * a = 1) (h2 : a * c = 1) : b = c := by
  -- hint for this one if you're doing it from first principles: `b * (a * c) = (b * a) * c`
  have hn := h1
  rw [←h2] at hn
  have hbinv := inv_eq_of_mul_eq_one_left h1
  have hcinv := inv_eq_of_mul_eq_one_right h2
  rw [←hbinv,←hcinv]


example : a * b = 1 ↔ a⁻¹ = b := by
  constructor
  · intro hab1
    rw [←(mul_inv_eq_one.mpr (Eq.refl a))] at hab1
    have: a⁻¹*(a*b) = a⁻¹ * (a * a⁻¹) := by
     rw [hab1]
    rw [←mul_assoc] at *
    rw [(mul_inv_eq_one.mpr (Eq.refl a)),inv_mul_eq_one.mpr (Eq.refl a)] at this
    rw [mul_one,one_mul] at this
    exact this.symm
  · intro hab
    have: a*a⁻¹ = a*b := by rw [hab]
    rw [(mul_inv_eq_one.mpr (Eq.refl a))] at this
    exact this.symm


example : (1 : G)⁻¹ = 1 := by
  have : (1 : G)⁻¹*1 = 1*1⁻¹ := by
   rw [inv_mul_eq_one.mpr (Eq.refl (1:G)),(mul_inv_eq_one.mpr (Eq.refl (1: G)))]
  rw [mul_one,(mul_inv_eq_one.mpr (Eq.refl (1: G)))] at this
  assumption

example : a⁻¹⁻¹ = a := by
  have: a⁻¹⁻¹ * a⁻¹ * a = a * a⁻¹ * a  := by
   rw [inv_mul_eq_one.mpr (Eq.refl (a⁻¹:G)),(mul_inv_eq_one.mpr (Eq.refl (a: G)))]
  rw [mul_assoc,mul_assoc] at *
  rw [(inv_mul_eq_one.mpr (Eq.refl (a: G)))] at this
  rw [mul_one,mul_one] at this
  exact this

#check mul_eq_one_iff_eq_inv

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have: (a * b)⁻¹*(a * b) = b⁻¹ * a⁻¹ * (a * b) := by
   rw [inv_mul_eq_one.mpr (Eq.refl (a*b:G))]
   rw [←mul_assoc,mul_assoc b⁻¹,inv_mul_eq_one.mpr (Eq.refl a)]
   rw [mul_assoc,one_mul]
   rw [inv_mul_eq_one.mpr (Eq.refl (b:G))]
  rw [inv_mul_eq_one.mpr (Eq.refl (a*b:G))] at this
  have := mul_eq_one_iff_eq_inv.mp this.symm
  exact this.symm



/-

Remember the `ring` tactic which didn't look at hypotheses but which could
prove hypothesis-free identities in commutative rings? There's also a `group`
tactic which does the same thing for groups. This tactic would have solved
many of the examples above.  NB the way it works is that it just uses
Lean's simplifier but armed with all the examples above; a theorem of Knuth and Bendix
says that these examples and the axioms of a group give a "confluent rewrite system"
which can solve any identity in group theory. If you like you can
try and prove the next example manually by rewriting with the lemmas above
(if you know their names, which you can find out with `exact?` or by
educated guessing).

-/
example : (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by group

-- Try this trickier problem: if g^2=1 for all g in G, then G is abelian
example (h : ∀ g : G, g * g = 1) : ∀ g h : G, g * h = h * g := by
  intro g1 g2
  have h1 := h g1
  have h2 := h g2
  have h3 := mul_eq_one_iff_eq_inv.mp h1
  have h4 := mul_eq_one_iff_eq_inv.mp h2
  have h5 := h (g1*g2)
  have h6 := mul_eq_one_iff_eq_inv.mp h5
  have: (g1 * g2)⁻¹ = g2⁻¹ * g1⁻¹ := by group
  rw [←h3,←h4] at this
  rw [this] at h6
  exact h6
