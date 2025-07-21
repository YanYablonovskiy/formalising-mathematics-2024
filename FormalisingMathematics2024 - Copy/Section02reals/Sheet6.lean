/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Hofer
--import Mathlib
import FormalisingMathematics2024.Solutions.Section02reals.Sheet5 -- import a bunch of previous stuff
#check neg_neg
--#check mul_lt_of_lt_div
#check lt_div_iff
namespace Section2sheet6

open Section2sheet3solutions Section2sheet5solutions

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in class,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/
-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`


#check abs_mul
#check abs_of_pos

#synth Field ℝ



example (a b c:ℝ) (h1:a < b/c) (h2:b>0) (h3:c>0): a*c < b := by exact (lt_div_iff h3).mp h1

#check Real.field.toAddCommGroup

theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
    rw [TendsTo] at *
    intro e he
    specialize h (e/37) (by linarith)
    obtain ⟨B,hB⟩ := h
    use B
    intro n hBn
    specialize hB n hBn
    simp only [←mul_sub,abs_mul]
    rw [abs_of_pos (a:=37) (by linarith)]
    linarith


#check neg_mul_eq_neg_mul


/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
    rw [TendsTo] at *
    intro e he
    have := pos_div_pow_pos he hc 1
    simp at this
    specialize h (e/c) (this)
    obtain ⟨B,hB⟩ := h
    use B
    intro n hBn
    specialize hB n hBn
    simp only [←mul_sub,abs_mul]
    rw [abs_of_pos (a:=c) (by linarith)]
    rw [mul_comm]
    apply (lt_div_iff hc).mp hB


/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  rw [←neg_neg c]
  have : -c > 0 := by linarith
  rw [←neg_mul_eq_neg_mul]
  have nh := tendsTo_pos_const_mul h this
  have nnh := tendsTo_neg nh
  conv =>
   arg 1
   intro n
   rw [←neg_mul_eq_neg_mul]
  assumption


#check lt_or_eq_of_le

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  by_cases hc:c>0
  · exact tendsTo_pos_const_mul h hc
  · push_neg at hc
    have := lt_or_eq_of_le hc
    cases' this with hc1 hc2
    · exact tendsTo_neg_const_mul h hc1
    · simp [hc2]
      rw [TendsTo]
      intro e he
      use 1
      intro n _
      simp
      exact he



/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by
      simp only [mul_comm]
      have := tendsTo_const_mul c h
      rw [mul_comm t]
      assumption

theorem tendsTo_const (c:ℝ): TendsTo (fun n ↦ c) c := by
 rw [TendsTo]
 intro e he
 use 1
 intro n hn
 simp [he]

-- another proof of this result
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by
  have : TendsTo (fun n ↦ (a n - b n) + b n) (t+u) := tendsTo_add h1 h2
  simp at this
  exact this

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
 constructor
 · intro hta
   have := tendsTo_sub hta (tendsTo_const t)
   simp at this
   assumption
 · intro htan
   have := tendsTo_of_tendsTo_sub htan (tendsTo_const t)
   simp at this
   assumption

#check Real.sqrt_pos_of_pos
#check le_of_max_le_left
#check mul_lt_mul
#check Real.sqrt_sq
#check Real.sq_sqrt

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
  rw [TendsTo] at *
  intro e he
  specialize ha (Real.sqrt e) (Real.sqrt_pos_of_pos he)
  specialize hb (Real.sqrt e) (Real.sqrt_pos_of_pos he)
  simp
  obtain ⟨⟨b1,hb1⟩,⟨b2,hb2⟩⟩ := And.intro ha hb
  use max b1 b2
  intro n
  simp at hb1 hb2
  intro hmn
  have: (b1 ≤ n) ∧ (b2 ≤ n) := by
   apply And.intro (le_of_max_le_left hmn) (le_of_max_le_right hmn)
  specialize hb1 n this.1; specialize hb2 n this.2
  rw [abs_mul]
  have := mul_lt_mul hb1 (hb2.le)
  simp at this
  by_cases hbo: b n = 0
  · simpa [hbo]
  · specialize this hbo (Real.sqrt_pos_of_pos he).le
    rw [←pow_two,Real.sq_sqrt he.le] at this
    assumption

#check abs_sub
#check abs_add
#check abs_sub_le
#check sub_eq_zero
#check lt_or_gt_of_ne
#check abs_pos

#check lt_of_lt_of_le
/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
      rw [TendsTo] at *
      intro e he
      have hc := And.intro (tendsTo_sub_lim_iff.mp ha) (tendsTo_sub_lim_iff.mp hb)
      have := tendsTo_zero_mul_tendsTo_zero hc.1 hc.2
      rw [TendsTo] at this
      simp at this
      have rarrange: ∀n, a n * b n - t * u = (a n - t) * (b n - u) + t*(b n - u) + u*(a n  - t) := by
       intro n
       ring
      conv =>
       arg 1
       intro B n hbn
       rw [rarrange n]
      have ht := this (|t|+|u|)

      by_cases ht0: t = 0
      · by_cases hu0: u = 0
        · simp [ht0,hu0]
          simp [ht0,hu0] at this
          exact this e he
        · simp [ht0]
          simp [ht0] at this ha
          specialize ha (e/(2*|u|)) (by have pos_denom := (abs_pos.mpr hu0);exact div_pos he (mul_pos (by linarith) (abs_pos.mpr hu0)))
          specialize this (e/3) (by linarith)
          obtain ⟨⟨b1,hb1⟩,⟨b2,hb2⟩⟩ := And.intro ha this
          use max b1 b2
          intro n hbN
          suffices hs:|a n * (b n - u)| + |u * a n| < e from lt_of_le_of_lt (abs_add (a n * (b n - u)) (u * a n)) hs
          rw [abs_mul u]
          have hbounds: (b1 ≤ n) ∧ (b2 ≤ n) := by
           apply And.intro (le_of_max_le_left hbN) (le_of_max_le_right hbN)
          specialize hb1 n hbounds.1
          specialize hb2 n hbounds.2
          have hineq1: |u| * |a n| < |u| * (e/(2*|u|)) := (mul_lt_mul_left (abs_pos.mpr hu0)).mpr hb1
          suffices hfs: e/3 + (|u| * (e/(2*|u|))) < e from (add_lt_add hb2 hineq1).trans hfs
          ring
          rw [mul_assoc e,mul_inv_cancel,mul_one]
          linarith
          exact ne_of_gt (abs_pos.mpr hu0)
      · by_cases hu0: u = 0
        · simp [hu0]
          simp [hu0] at this ha
          specialize hb (e/(2*|t|)) (by have pos_denom := (abs_pos.mpr ht0);exact div_pos he (mul_pos (by linarith) (abs_pos.mpr ht0)))
          specialize this (e/3) (by linarith)
          obtain ⟨⟨b1,hb1⟩,⟨b2,hb2⟩⟩ := And.intro hb this
          use max b1 b2
          intro n hbN
          have hbounds: (b1 ≤ n) ∧ (b2 ≤ n) :=
           And.intro (le_of_max_le_left hbN) (le_of_max_le_right hbN)
          specialize hb1 n hbounds.1
          specialize hb2 n hbounds.2
          simp [hu0] at hb1
          have hineq1: |t * b n| < |t| * (e/(2*|t|)) := by rw [abs_mul]; exact (mul_lt_mul_left (abs_pos.mpr ht0)).mpr hb1
          suffices hfs: e/3 + (|t| * (e/(2*|t|))) < e from lt_of_le_of_lt (abs_add ((a n - t) * b n) (t * b n)) ((add_lt_add hb2 hineq1).trans hfs)
          ring
          rw [mul_assoc e,mul_inv_cancel,mul_one]
          linarith
          exact ne_of_gt (abs_pos.mpr ht0)
        · have t_abs_pos := abs_pos.mpr ht0
          have u_abs_pos := abs_pos.mpr hu0
          -- have t_u_pos := add_pos t_abs_pos u_abs_pos
          specialize this (e/3) (by linarith)
          specialize ha ((e/(4*|u|))) (by have pos_denom := (abs_pos.mpr ht0);exact div_pos he (mul_pos (by linarith) (u_abs_pos)))
          specialize hb ((e/(4*|t|))) (by have pos_denom := (abs_pos.mpr ht0);exact div_pos he (mul_pos (by linarith) (t_abs_pos)))
          obtain ⟨⟨b1,hb1⟩,⟨b2,hb2⟩⟩ := (And.intro hb ha)
          obtain ⟨b3,hb3⟩ := this
          use max (max b1 b2) b3
          intro n hbN
          rw [add_assoc]
          suffices hs:|(a n - t) * (b n - u)| + |t * (b n - u) + u * (a n - t)| < e from lt_of_le_of_lt (abs_add ((a n - t) * (b n - u)) (t * (b n - u) + u * (a n - t))) hs
          suffices hs:|(a n - t) * (b n - u)| + (|t * (b n - u)| + |u * (a n - t)|) < e from  lt_of_le_of_lt (add_le_add_left (abs_add (t * (b n - u)) (u * (a n - t))) (|(a n - t) * (b n - u)|) ) hs
          rw [←add_assoc]
          simp [abs_mul] at *
          specialize hb1 n hbN.1.1
          specialize hb2 n hbN.1.2
          specialize hb3 n hbN.2
          have t_abs_pos := abs_pos.mpr ht0
          have u_abs_pos := abs_pos.mpr hu0
          calc |a n - t| * |b n - u| + |t| * |b n - u| + |u| * |a n - t| = (|a n - t| * |b n - u| + |t| * |b n - u|) + |u| * |a n - t| := by rw [add_assoc]
          _ < (|a n - t| * |b n - u| + |t| * |b n - u|) + |u| * (e/(4*|u|)) := add_lt_add_left ( (mul_lt_mul_left (u_abs_pos)).mpr hb2) _
          _ < (e/3 + |t| * (e / (4 * |t|))) + |u| * (e/(4*|u|)) := by apply add_lt_add_right (add_lt_add hb3 (((mul_lt_mul_left t_abs_pos)).mpr hb1))
          _ < e/3 + e/3 + e/4 := by ring; rw [mul_assoc e,mul_assoc e |u|,mul_inv_cancel,mul_inv_cancel,mul_one];linarith; exact ne_of_gt u_abs_pos;exact ne_of_gt t_abs_pos
          _ < e := by linarith


-- by rw [add_comm]
-- have ineq1: (|a n - t| * |b n - u| + |t| * |b n - u|) < e/3 + |t| * (e/(4*|t|)) := by exact add_lt_add hb3 ((mul_lt_mul_left (t_abs_pos)).mpr hb1)
--
#check add_lt_add_right
#check mul_lt_mul_left
example (a b c :ℝ) (ha: a> 0) (hb: b >0) (hc: c > 0): b < c → a*b < a*c := by exact?


#check mul_inv_cancel
-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  rw [←sub_eq_zero]
  rw [TendsTo] at *
  by_contra!
  have := abs_pos.mpr this
  specialize hs (|s-t|/4) (by linarith)
  specialize ht (|s-t|/4) (by linarith)
  obtain ⟨⟨b1,hb1⟩,⟨b2,hb2⟩⟩ := And.intro hs ht
  specialize hb1 (max b1 b2) (le_max_left b1 b2)
  specialize hb2 (max b1 b2) (le_max_right b1 b2)
  have hadd_le: |a (max b1 b2) - t| +  |a (max b1 b2) - s| <  |s - t| / 4 + |s - t| / 4 := by linarith
  have := abs_sub (a (max b1 b2) - t) (a (max b1 b2) - s)
  have t1 := this.trans hadd_le.le
  simp at t1
  linarith


/-
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
      rw [TendsTo] at *
      intro e he
      have := And.intro (tendsTo_sub_lim_iff.mp ha) (tendsTo_sub_lim_iff.mp hb)
      have := tendsTo_zero_mul_tendsTo_zero this.1 this.2
      rw [TendsTo] at this
      simp at this
      specialize this e he
      have hrw: ∀n, (a n - t) * (b n - u) = (a n * b n + t*u - (u * a n + t * b n) ) := by
       intro n
       ring
      conv at this =>
       arg 1
       intro B
       intro n hBn
       rw [hrw n]
      obtain ⟨B,hnB⟩ := this
      use B
      intro n hBn
      suffices hs:|a n * b n| + |t*u| < e from lt_of_le_of_lt (abs_sub (a n * b n) (t*u)) hs
      specialize hnB n hBn
      have := abs_sub_le  (a:=a n * b n + t * u) (u * (a n)) (u * a n + t * b n)
-/


end Section2sheet6
#check pos_div_pow_pos
