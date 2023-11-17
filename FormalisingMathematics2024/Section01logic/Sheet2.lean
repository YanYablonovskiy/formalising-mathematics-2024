/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic.Default

#align_import section01logic.sheet2

/-!

# Logic in Lean, example sheet 2 : `true` and `false`

We learn about the `true` and `false` propositions.

## Tactics you will need

To solve the levels on this sheet you will need to know all previous
tactics, plus the following two new ones. Check out their explanations
in the course book. Or just try them out and hover over them to see
if you can understand what's going on.

* `triv`
* `exfalso`

-/


-- imports all the Lean tactics
-- imports all the Lean tactics
-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : True := by sorry

example : True → True := by sorry

example : False → True := by sorry

example : False → False := by sorry

example : (True → False) → False := by sorry

example : False → P := by sorry

example : True → False → True → False → True → False := by sorry

example : P → (P → False) → False := by sorry

example : (P → False) → P → Q := by sorry

example : (True → False) → P := by sorry

