/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hp
  left
  trivial
  done

example : P → P ∨ Q := by
 intro hp
 apply Or.intro_left Q
 · exact hp

example : P → P ∨ Q := by
 intros
 first|right;assumption|left;assumption

example : P → P ∨ Q := fun hp ↦ Or.inl hp

example : P → P ∨ Q
| hp => Or.inl hp

--same proof as the other way
example : Q → P ∨ Q := by
  intros
  first|right;assumption|left;assumption
  done

example : Q → P ∨ Q := by
intro hq
right; assumption

example : Q → P ∨ Q := fun hq ↦ Or.inr hq

example : Q → P ∨ Q
| hq => by right; assumption

example : P ∨ Q → (P → R) → (Q → R) → R := by
  rintro (hp|hq) hpr hqr
  · exact hpr hp
  · exact hqr hq
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
 intro hpq hpr hqr
 cases' hpq with h h <;> first|exact hpr h|exact hqr h


example : P ∨ Q → (P → R) → (Q → R) → R := fun hpOq hpr hqr ↦ hpOq.elim (fun hp ↦ hpr hp) (fun hq ↦ hqr hq)

example : P ∨ Q → (P → R) → (Q → R) → R
| hpOq , hpr , hqr => hpOq.elim (fun hp ↦ hpr hp) (fun hq ↦ hqr hq)

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro hpOq
  cases' hpOq with hp hq <;> first|right; exact hp| left; exact hq
  done

example : P ∨ Q → Q ∨ P := by
 intro hpOq
 cases' hpOq with hp hq
 · apply Or.inr
   · assumption
 · constructor; assumption

example : P ∨ Q → Q ∨ P := by
rintro (hp|hq) ; exact Or.inr hp ; exact Or.inl hq

example : P ∨ Q → Q ∨ P :=
 fun pOq ↦
  pOq.elim (fun hp ↦ Or.inr hp) (fun hq ↦ Or.inl hq)

example : P ∨ Q → Q ∨ P
| pOq => pOq.elim (fun hp ↦ Or.inr hp) (fun hq ↦ Or.inl hq)


-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · intro pOqOr
    cases' pOqOr with hpOq hr
    · cases' hpOq with hp hq
      · apply Or.inl; assumption
      · apply Or.inr
        · apply Or.inl; assumption
    . apply Or.inr
      · apply Or.inr; assumption
  . intro pOqOr
    cases' pOqOr with hp hqOr
    · apply Or.inl
      · apply Or.inl; assumption
    · cases' hqOr with hq hr
      · apply Or.inl
        · apply Or.inr;assumption
      · apply Or.inr;assumption
  done


example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R :=
  ⟨fun h ↦ h.elim (fun hpOq ↦ hpOq.elim (fun hp ↦ Or.inl hp) (fun hq ↦ Or.inr (Or.inl hq))) (fun hr ↦ Or.inr (Or.inr hr)),
    fun h ↦ h.elim (fun hp ↦ Or.inl (Or.inl hp)) (fun hqOr ↦ hqOr.elim (fun hq ↦ Or.inl (Or.inr hq)) (fun hr ↦ Or.inr hr))⟩


example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  sorry
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  sorry
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  sorry
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  sorry
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry
  done
