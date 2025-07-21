/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Hofer
import Mathlib.Order.Basic
import Mathlib
 -- imports all the Lean tactics
/-
# Figuring out how to use the reals

## The `exact?` tactic

We saw in the previous sheet that we couldn't even prove something
as simple as "if `aₙ → L` then `-aₙ → -L`" because when you write down
the proof carefully, it relies on the fact that `|x - y| = |y - x|`
or, equivalently, that `|(-x)| = |x|`. I say "equivalently" because
`ring` will prove that `-(x - y) = y - x`.

You don't want to be proving stuff like `|x - y| = |y - x|` from first
principles. Someone else has already done all the hard work for you.
All you need to do is to learn how to find out the names of the lemmas.
The `exact?` tactic tells you the names of all these lemmas.
See where it says "try this" -- click there and Lean will replace
`exact?` with the actual name of the lemma. Once you've done
that, hover over the lemma name to see in what generality it holds.

## The `linarith` tactic

Some of the results below are bare inequalities which are too complex
to be in the library. The library contains "natural" or "standard"
results, but it doesn't contain a random inequality fact just because
it happens to be true -- the library just contains "beautiful" facts.
However `linarith` doesn't know about anything other than `=`, `≠`,
`<` and `≤`, so don't expect it to prove any results about `|x|` or
`max A B`.

Experiment with the `exact?` and `linarith` tactics below.
Try and learn something about the naming convention which Lean uses;
see if you can start beginning to guess what various lemmas should be called.

-/

example (x : ℝ) : |-x| = |x| := by exact?

#check mul_pos_of_neg_of_neg
#check mul_neg_of_neg_of_pos
#check neg_eq_neg_one_mul
#check neg_one_lt_zero
#check abs_of_nonpos
#check pow_two
#check neg_one_sq
#check le_iff_eq_or_lt
#check abs_zero
#check mul_zero
#check add_pos_of_nonneg_of_pos
#check neg_neg
example (x : ℝ) : |-x| = |x| := by exact abs_neg x


#check sub_pos_of_lt
#check sub_neg_of_lt
#check sub_neg_eq_add
#check neg_add_eq_sub




example (x : ℝ) : |-x| = |x| := by
 by_cases h:x>0
 · rw [neg_eq_neg_one_mul]
   push_neg at h
   have := mul_neg_of_neg_of_pos (α:=ℝ ) neg_one_lt_zero h
   rw [abs_of_neg this,neg_eq_neg_one_mul]
   rw [←mul_assoc,←pow_two,neg_one_sq,one_mul,abs_of_pos h]
 · rw [neg_eq_neg_one_mul]
   push_neg at h
   rw [le_iff_eq_or_lt] at h
   cases h with
   | inl h => rw [h,abs_zero,mul_zero,abs_zero]
   | inr h => have := mul_pos_of_neg_of_neg neg_one_lt_zero h; rw [abs_of_pos this,abs_of_neg h,←neg_eq_neg_one_mul]

example (x : ℝ) : |-x| = |x| := by simp



-- click where it says "try this" to replace
-- `exact?` with an "exact" proof
-- Why do this? Because it's quicker!

example (x y : ℝ) : |x - y| = |y - x| := by exact abs_sub_comm x y

--no tactic
example (x y : ℝ) : |x - y| = |y - x| := abs_sub_comm x y

example (x y : ℝ) : |x - y| = |y - x| := by
  by_cases h: y > x
  · have := sub_pos_of_lt h
    rw [abs_of_pos this]
    have := sub_neg_of_lt h
    rw [abs_of_neg this]
    rw [neg_eq_neg_one_mul,mul_sub]
    rw [←neg_eq_neg_one_mul,←neg_eq_neg_one_mul,sub_neg_eq_add]
    rw [add_comm]
    rfl
  · push_neg at h
    rw [le_iff_eq_or_lt] at h
    match h with
    | Or.inl h1 => rw [h1]
    | Or.inr h =>
      have := sub_pos_of_lt h;
      rw [abs_of_pos this];
      have := sub_neg_of_lt h ;
      rw [abs_of_neg this];
      rw [neg_eq_neg_one_mul,mul_sub,←neg_eq_neg_one_mul,←neg_eq_neg_one_mul,sub_neg_eq_add];rw [add_comm];rfl

#check max_le
#check le_max_left


-- Hmm. What would a theorem saying "the max is
-- less-or-equal to something iff something else
-- be called, according to Lean's naming conventions?"
example (A B C : ℕ) : max A B ≤ C ↔ A ≤ C ∧ B ≤ C := by exact Nat.max_le

example (A B C : ℕ) : max A B ≤ C ↔ A ≤ C ∧ B ≤ C := Nat.max_le

example (A B C : ℕ) : max A B ≤ C ↔ A ≤ C ∧ B ≤ C := by
 constructor
 · intro hml
   constructor
   · have := le_max_left A B
     exact this.trans hml
   · have := le_max_right A B
     exact this.trans hml
 · intro hb
   exact max_le hb.1 hb.2

example (A B C : ℕ) : max A B ≤ C ↔ A ≤ C ∧ B ≤ C :=
 ⟨fun hml ↦ And.intro ((le_max_left A B).trans hml) ((le_max_right A B).trans hml) ,fun hb ↦ max_le hb.1 hb.2⟩

#check lt_or_gt_of_ne

-- abs of something less than something...
example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y := by exact?

example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y := by exact abs_lt

example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y := abs_lt


#check lt_of_neg_lt_neg
#check max_def_lt
#check abs_eq_max_neg
#check lt_of_lt_of_le


example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · intro hxy
    rw [abs_eq_max_neg] at hxy
    constructor
    <;> rw [max_def_lt] at hxy <;>
        by_cases h: x < -x
          <;> simp only [h] at hxy
    · rw [←neg_neg y] at hxy
      have := lt_of_neg_lt_neg hxy
      exact this
    · rw [←neg_neg x,←neg_neg y] at hxy
      have := lt_of_neg_lt_neg hxy
      push_neg at h
      apply lt_of_lt_of_le this h
    · push_neg at h
      exact h.trans hxy
    assumption
  · intro hlt
    rw [abs]
    have := (max_lt (b := -x) (α := ℝ) (hlt.2))
    have hlt1 := hlt.1
    rw [←neg_neg x] at hlt1
    have hlt1' := lt_of_neg_lt_neg hlt1
    specialize this hlt1'
    assumption


#check div_eq_inv_mul
#check inv_eq_one_div
--#check Nat.pos_of_div_pos
--#check div_pos_iff_of_pos_left
#check div_pos
#check one_pos
#check two_pos
#check three_pos
#check mul_pos


example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 2 := by linarith



example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 2 := by
  rw [div_eq_inv_mul,inv_eq_one_div]
  have := div_pos (α:=ℝ) (b:=2) one_pos two_pos
  exact mul_pos this hε







-- or linarith, or guess the name...

example (a b x y : ℝ) (h1 : a < x) (h2 : b < y) : a + b < x + y := by exact?

example (a b x y : ℝ) (h1 : a < x) (h2 : b < y) : a + b < x + y := by exact add_lt_add h1 h2


example (a b x y : ℝ) (h1 : a < x) (h2 : b < y) : a + b < x + y := add_lt_add h1 h2

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 3 := by linarith

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 3 := by
  rw [div_eq_inv_mul,inv_eq_one_div]
  have := div_pos (α:=ℝ) (b:=3) one_pos three_pos
  exact mul_pos this hε

#check add_lt_add

-- This is too obscure for the library
example (a b c d x y : ℝ) (h1 : a + c < x) (h2 : b + d < y) : a + b + c + d < x + y := by linarith

example (a b c d x y : ℝ) (h1 : a + c < x) (h2 : b + d < y) : a + b + c + d < x + y := by
 rw [add_assoc a,add_comm b,←add_assoc]
 rw [add_assoc]
 exact add_lt_add h1 h2
-- note that add_lt_add doesn't work because
-- ((a+b)+c)+d and (a+c)+(b+d) are not definitionally equal
