/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro nt
  exact (nt True.intro)
  done

example : ¬True → False := fun nt ↦ (nt True.intro)


example : False → ¬True := by
  intro hf
  exfalso
  trivial
  done


example : False → ¬True := fun f ↦ fun _ ↦ f

example : ¬False → True := by
  intro nf
  change False → False at nf
  by_contra hc
  exact (hc True.intro)
  done

example : ¬False → True :=
  fun _ ↦
    match Classical.em True with
    | Or.inl h1 => h1
    | Or.inr h2 => False.elim (h2 True.intro)




example : True → ¬False := by
  intro t
  change False → False
  intro f
  exact f
  done

example : True → ¬False := fun _ ↦ fun f ↦ f

example : False → ¬P := by
  intro f
  exfalso
  trivial
  done

example : False → ¬P := fun f ↦ f.elim


example : P → ¬P → False := by
  intro p np
  exact np p
  done

example : P → ¬P → False := fun hp ↦ fun nhp ↦ nhp hp


example : P → ¬¬P := by
  intro p
  change ¬P → False
  intro np
  exact np p
  done

example : P → ¬¬P := fun hp ↦ fun np:¬P ↦ np hp

example : (P → Q) → ¬Q → ¬P := by
  intro hpq hnq hp
  exact hnq (hpq hp)
  done


example : (P → Q) → ¬Q → ¬P := fun hpq nq hp ↦ nq (hpq hp)


example : ¬¬False → False := by
  intro nf
  by_contra hf
  apply nf
  exact hf
  done

example : ¬¬False → False := fun nf ↦ nf (fun f ↦ f)

example : ¬¬P → P := by
  intro np
  by_cases hp:P
  · exact hp
  · specialize np hp
    exfalso
    trivial
  done

example: ¬¬P → P :=
 fun hnnp ↦
  match Classical.em P with
  | Or.inl hp => hp
  | Or.inr hnp => (hnnp hnp).elim



example : (¬Q → ¬P) → P → Q := by
  intro hnqnp hp
  by_cases hq:Q
  · exact hq
  · exfalso
    exact (hnqnp hq) hp
  done

example : (¬Q → ¬P) → P → Q :=
 fun hnqnp hp ↦
   match Classical.em Q with
   | Or.inl hq => hq
   | Or.inr hnq => ((hnqnp hnq) hp).elim
