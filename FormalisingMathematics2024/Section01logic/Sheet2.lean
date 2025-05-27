/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 2 : `True` and `False`

We learn about the `True` and `False` propositions.

## Tactics you will need

To solve the levels on this sheet you will need to know all previous
tactics, plus the following two new ones. Check out their explanations
in the course book. Or just try them out and hover over them to see
if you can understand what's going on.

* `triv`
* `exfalso`

-/


-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : True := by
  trivial
  done

--term
example : True := True.intro


example : True → True := by
  trivial
  done

example : True → True := fun t ↦ t


example : False → True := by
  trivial
  done

example : False → True := fun f ↦ f.elim


example : False → False := by
  trivial
  done


example : False → False := fun f ↦ f


example : (True → False) → False := by
  trivial
  done


example : (True → False) → False := fun tf ↦ tf True.intro




example : False → P := by
  intro f
  exfalso
  trivial
  done

example : True → False → True → False → True → False := by
  trivial
  done

example : True → False → True → False → True → False :=
 fun _ ↦ fun f ↦ fun _ _ _ ↦ f


example : P → (P → False) → False := by
  intro p hpf
  apply hpf
  exact p
  done

example : P → (P → False) → False :=
 fun hp ↦ fun hpf ↦ hpf hp


example : (P → False) → P → Q := by
  intro hpf hp
  specialize hpf hp
  trivial
  done

example : (P → False) → P → Q := fun hpf ↦ fun hp ↦ (hpf hp).elim


example : (True → False) → P := fun htf ↦ (htf True.intro).elim


example : (True → False) → P := by
  intro htf
  specialize htf True.intro
  exfalso
  exact htf
  done
