/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
-- imports all the Lean tactics
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε
-- import the definition of `TendsTo` from a previous sheet

theorem tendsTo_def {a : ℕ → ℝ} {t : ℝ} :
    TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε := by
  rfl  -- true by definition

namespace Section2sheet5

#check mul_neg_one
#check sub_neg
-- you can maybe do this one now
theorem tendsTo_neg {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  rw [TendsTo] at *
  intro e he
  specialize ha e he
  use ha.choose
  intro n h
  have := ha.choose_spec n h
  rw [abs]
  rw [abs] at this
  conv =>
   lhs
   lhs
   simp
  conv =>
   lhs
   rhs
   rw [←mul_neg_one,sub_mul]
   rw [←mul_neg_one,←mul_neg_one t]
   rw [mul_assoc,←pow_two,neg_sq 1,one_pow,mul_one]
   rw [mul_assoc,←pow_two,neg_sq 1,one_pow,mul_one]
  conv at this =>
   lhs
   rhs
   rw [←mul_neg_one,sub_mul,mul_neg_one t,mul_neg_one]
   simp
  rw [max_comm]
  exact this


#check one_pow

/-
`tendsTo_add` is the next challenge. In a few weeks' time I'll
maybe show you a two-line proof using filters, but right now
as you're still learning I think it's important that you
try and suffer and struggle through the first principles proof.
BIG piece of advice: write down a complete maths proof first,
with all the details there. Then, once you know the maths
proof, try translating it into Lean. Note that a bunch
of the results we proved in sheet 4 will be helpful.
-/
/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/
theorem tendsTo_add {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n + b n) (t + u) :=
  by
  rw [tendsTo_def] at *
  -- let ε > 0 be arbitrary
  intro ε hε
  --  There's a bound X such that if n≥X then a(n) is within ε/2 of t
  specialize ha (ε / 2) (by linarith)
  cases' ha with X hX
  --  There's a bound Y such that if n≥Y then b(n) is within ε/2 of u
  obtain ⟨Y, hY⟩ := hb (ε / 2) (by linarith)
  --  use max(X,Y),
  use max X Y
  -- now say n ≥ max(X,Y)
  intro n hn
  rw [max_le_iff] at hn
  specialize hX n hn.1
  specialize hY n hn.2
  --  Then easy.
  rw [abs_lt] at *
  constructor <;>-- `<;>` means "do next tactic to all goals produced by this tactic"
    linarith

 #check sub_eq_add_neg

#check abs_add
#check le_max_left
#check add_lt_add
#check lt_of_le_of_lt




example {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n + b n) (t + u) := by
     rw [TendsTo] at *
     intro e he
     specialize ha (e/2) (by linarith)
     apply ha.elim
     intro B1 h
     obtain ⟨B2,hB⟩ := hb (e/2) (by linarith)
     use (max B1 B2)
     intro nfinal hnf
     conv =>
      lhs
      arg 1
      rw [sub_eq_add_neg,neg_add,←add_assoc]
      rw [add_assoc (a nfinal),add_comm (b nfinal),←add_assoc]
      rw [add_assoc,←sub_eq_add_neg,←sub_eq_add_neg]
     have: B1 ≤ nfinal ∧ B2 ≤ nfinal := by
      have l1 := le_max_left B1 B2
      have l2 := le_max_right B1 B2
      exact ⟨l1.trans hnf,l2.trans hnf⟩
     specialize h nfinal this.1
     specialize hB nfinal this.2
     have teq := abs_add (a nfinal - t) (b nfinal - u)
     have inq := add_lt_add (α := ℝ) h hB
     have := lt_of_le_of_lt teq inq
     simp at this
     exact this










/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n - b n) (t - u) := by
  -- this one follows without too much trouble from earlier results.
  conv =>
   arg 1
   intro n
   rw [sub_eq_add_neg]
  conv =>
   arg 2
   rw [sub_eq_add_neg]
  have := tendsTo_neg hb
  have := tendsTo_add ha this
  exact this

end Section2sheet5
