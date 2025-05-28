/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Doing algebra in the real numbers

The `ring` tactic will prove algebraic identities like
(x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 in rings, and Lean
knows that the real numbers are a ring. See if you can use
`ring` to prove these theorems.

## New tactics you will need

* `ring`
* `intro` (new functionality: use on a goal of type `⊢ ∀ x, ...`)

-/
variable (x y: ℝ)
#check mul_add (x*y) 
#check mul_one
#check add_assoc (x^2)
#check one_add_one_eq_two
#check add_pow_two

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  calc (x+y)^2 = (x+y)*(x+y)            := by rw [pow_two]
       _       =  (x+y)*x + (x+y)*y     := by rw [mul_add]
       _       =  x*x + y*x + x*y + y*y := by rw [add_mul,add_mul,←add_assoc]
       _       =  x^2 + x*y + x*y + y^2 := by rw [←pow_two,←pow_two,mul_comm]
       _       =  x^2 + x*y*2 + y^2     := by rw [←mul_one (x*y),add_assoc (x^2),←mul_add (x*y) 1 1,one_add_one_eq_two,mul_one]
       _       =  x^2 + 2*x*y + y^2     := by rw [mul_assoc x y,mul_comm y,←mul_assoc x 2,mul_comm 2]
  done

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
 ring

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
 apply add_pow_two

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := add_pow_two x y



example : ∀ a b : ℝ, ∃ x, (a + b) ^ 3 = a ^ 3 + x * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  intro a b
  sorry
  done

example : ∃ x : ℝ, ∀ y, y + y = x * y := by
  sorry
  done

example : ∀ x : ℝ, ∃ y, x + y = 2 := by
  sorry
  done

example : ∀ x : ℝ, ∃ y, x + y ≠ 2 := by
  sorry
  done
