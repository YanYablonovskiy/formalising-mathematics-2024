/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

/-

# Lattices

In a *linear* order like ℝ, any two elements have
a min and a max. Using fancier language, if `x` and `y`
are real numbers, then the set `{x,y}` has a least upper
bound or supremum (namely `max x y`) and an infimum
(namely `min x y`).

But partial orders can be pretty general objects. Consider
for example the partial order containing only the following four
elements (all subsets of ℕ):

a={1}
b={2}
c={1,2,3}
d={1,2,4}

This is a partial order, with the ordering `≤` given by `⊆`.
Note that `a ≰ b` and `b ≰ a`, so `max a b` doesn't seem
to make any sense. But what about `Sup {a, b}`? Well,
We have `a ≤ c` and `b ≤ c`, and also `a ≤ d` and `b ≤ d`.
So both `c` and `d` are upper bounds for the set `{a,b}`,
but neither of them are *least* upper bounds, because
`c ≰ d` and `d ≰ c`, so neither `c` nor `d` satisfy
the least upper bound axiom (they are not `≤` all other upper
bounds).

A *lattice* is a partial order where any two elements
have a least upper bound and a greatest lower bound. So
the example `{a,b,c,d}` above is a partial order but not
a lattice. But a total order such as the naturals or the
reals are a lattice, because the least upper bound of `{x,y}`
is just the max of `x` and `y`, and the greatest lower
bound is just the min.

Notation: if `L` is a lattice, and if `a : L` and `b : L`
then their least upper bound is denoted by `a ⊔ b` and
their greatest lower bound is denoted by `a ⊓ b`. Hover
over these symbols in VS Code to see how to type them
in Lean.

A nice example of a lattice is the subsets of
a type, ordered by `⊆`. In this example the least upper
bound `a ⊔ b` of subsets `a` and `b` is `a ∪ b`, and the greatest
lower bound `a ⊓ b` is `a ∩ b`.

An example which requires a little more thought is the
lattice of subspaces of a vector spaces. If `V` and `W` are subspaces
of `U` then their greatest lower bound `V ⊓ W` is just `V ∩ W`, which
is also a subspace. However their least upper bound is not so simple,
because `V ∪ W` is in general not a vector space.
The least upper bound is supposed to be the smallest subspace
containing `V` and `W`, so in this case `V ⊔ W` is the subspace
`V + W` generated by `V` and `W`.

We'll talk about subgroups later on; for now let's talk about
the general theory of lattices. The API you need to know is:

`a ⊔ b` is the least upper bound of `a` and `b`:
`le_sup_left : a ≤ a ⊔ b`
`le_sup_right : b ≤ a ⊔ b` -- these axioms say that `a ⊔ b` is an upper bound for `{a,b}`
`sup_le : a ≤ c → b ≤ c → a ⊔ b ≤ c` -- this says it's the least upper bound.

`a ⊓ b` is the greatest lower bound of `a` and `b`:
`inf_le_left : a ⊓ b ≤ a`
`inf_le_right : a ⊓ b ≤ b` -- `a ⊓ b` is a lower bound
`le_inf : a ≤ b → a ≤ c → a ≤ b ⊓ c` -- it's the greatest lower bound

Using these axioms, see if you can develop the basic theory of lattices.
-/

-- let L be a lattice, and let a,b,c be elements of L
variable (L : Type) [Lattice L] (a b c : L)

example : a ⊔ b = b ⊔ a := by
  -- you might want to start with `apply le_antisymm` (every lattice is a partial order so this is OK)
  -- You'll then have two goals so use `\.` and indent two spaces.
  apply le_antisymm
  · apply sup_le
    · exact le_sup_right (α:=L)
    · exact le_sup_left
  · apply sup_le
    · exact le_sup_right (α:=L)
    · exact le_sup_left


example : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      . exact le_sup_left
      · have hle1: b ≤ b ⊔ c := by
          exact le_sup_left (α := L)
        have hle2: b ⊔ c ≤ a ⊔ (b ⊔ c) := by
          exact le_sup_right
        exact hle1.trans hle2
    · have hle1: c ≤ b ⊔ c := by
       exact le_sup_right (α := L)
      have hle2: b ⊔ c ≤ a ⊔ (b ⊔ c) := by
        exact le_sup_right
      exact hle1.trans hle2
  . apply sup_le
    · have hle1: a ≤ a ⊔ b := by
       exact le_sup_left (α := L)
      have hle2: a ⊔ b ≤ (a ⊔ b) ⊔ c := by
        exact le_sup_left
      exact hle1.trans hle2
    · apply sup_le
      · have hle1: b ≤ a ⊔ b := by
         exact le_sup_right (α := L)
        have hle2: a ⊔ b ≤ (a ⊔ b) ⊔ c := by
         exact le_sup_left
        exact hle1.trans hle2
      · exact le_sup_right




-- could golf this entire proof into one (long) line
-- `a ⊓ _` preserves `≤`.
-- Note: this is called `inf_le_inf_left a h` in mathlib; see if you can prove it
-- directly without using this.
example (h : b ≤ c) : a ⊓ b ≤ a ⊓ c := by
  have: c ≥ (a ⊓ b) := by
   have: b ≥ (a ⊓ b) := by
    exact (inf_le_right (a:=a) (b:=b)).ge
   have h1 := h.ge
   exact this.trans h1
  apply le_inf (a:=a ⊓ b)
  · exact inf_le_left
  · exact this.ge



example (h : b ≤ c) : a ⊓ b ≤ a ⊓ c := le_inf (a:=a ⊓ b) inf_le_left (((inf_le_right (a:=a) (b:=b)).ge).trans (c:=c) h)
/-

We all know that multiplication "distributes" over addition, i.e. `p*(q+r)=p*q+p*r`,
but of course addition does not distribute over multiplication (`p+(q*r)≠(p+q)*(p+r)` in general).
In sets (rather surprisingly, in my view), ∩ distributes over ∪ and ∪ also
distributes over ∩! However this is not true in more general lattices. For example,
if `U`, `V` and `W` are three distinct lines in `ℝ²` (v perpendicular?) then `U ∩ (V + W) = U`
whereas `U ∩ V + U ∩ W = 0`, and `U + (V ∩ W) = U ≠ (U + V) ∩ (U + W) = ℝ²`. We
do have inclusions though, which is what you can prove in general.

-/
-- `inf_le_inf_left`, proved above, is helpful here.
example : (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c) := by
  apply sup_le
  · apply le_inf
    · exact inf_le_left
    · have hle := (inf_le_right (a:=a) (b:=b))
      have hge := (le_sup_left (a:=b) (b:=c))
      exact hle.trans hge
  · apply le_inf
    · exact inf_le_left
    · have hle := (inf_le_right (a:=a) (b:=c))
      have hge := (le_sup_right (a:=b) (b:=c))
      exact hle.trans hge

-- use `sup_le_sup_left` for this one.
example : a ⊔ b ⊓ c ≤ (a ⊔ b) ⊓ (a ⊔ c) := by
  apply sup_le
  · apply le_inf <;> exact le_sup_left (a:=a)
  · apply le_inf
    · have hle := (inf_le_left (a:=b) (b:=c))
      have hge := (le_sup_right (a:=a) (b:=b))
      exact hle.trans hge
    · have hle := (inf_le_right (a:=b) (b:=c))
      have hge := (le_sup_right (a:=a) (b:=c))
      exact hle.trans hge

-- Bonus question: look up the binding powers of ⊓ and ⊔ (by using crtl-click to jump
-- to their definitions) and figure out which brackets
-- can be removed in the statements of the previous two examples without changing
-- their meaning.
