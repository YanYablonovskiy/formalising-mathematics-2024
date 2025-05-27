/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  constructor <;> (intro hp; exact hp)
  done

example : P ↔ P := Iff.intro (fun hp ↦ hp) (fun hp ↦ hp)


example : (P ↔ Q) → (Q ↔ P) := by
  intro hpIffq
  constructor
  · exact hpIffq.mpr
  . exact hpIffq.mp
  done

example : (P ↔ Q) → (Q ↔ P) := by
    intro hpIffq; apply Iff.intro <;> first|exact hpIffq.mp|exact hpIffq.mpr

example : (P ↔ Q) → (Q ↔ P) := fun hpIffq ↦ Iff.intro (hpIffq.mpr) (hpIffq.mp)

example : (P ↔ Q) → (Q ↔ P)
| hpIffq => Iff.intro (hpIffq.mpr) (hpIffq.mp)


example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor <;> exact fun hpIffq ↦ ⟨hpIffq.mpr,hpIffq.mp⟩

example : (P ↔ Q) ↔ (Q ↔ P) := Iff.intro ( fun pIq: P ↔ Q ↦ Iff.intro (pIq.mpr) (pIq.mp)) (fun qIp: Q ↔ P ↦ Iff.intro (qIp.mpr) (qIp.mp))

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro pIq qIr
  constructor
  · intro hp
    exact qIr.mp (pIq.mp hp)
  · intro hr
    exact pIq.mpr (qIr.mpr hr)
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
 rintro ⟨hpq,hqp⟩ ⟨hqr,hrq⟩
 constructor
 · intro hp
   exact hqr (hpq hp)
 · intro hr
   exact hqp (hrq hr)

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
 fun ⟨hpq,hqp⟩ ⟨hqr,hrq⟩ ↦ ⟨fun hp ↦ hqr (hpq hp), fun hr ↦ hqp (hrq hr)⟩

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R)
| ⟨hpq,hqp⟩, ⟨hqr,hrq⟩ => ⟨fun hp ↦ hqr (hpq hp), fun hr ↦ hqp (hrq hr)⟩


example : P ∧ Q ↔ Q ∧ P := by
  constructor <;> (intro h ; exact And.intro h.2 h.1)
  done

example : P ∧ Q ↔ Q ∧ P := ⟨(fun ⟨hp,hq⟩ ↦ ⟨hq,hp⟩),(fun ⟨hp,hq⟩ ↦ ⟨hq,hp⟩)⟩


example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · intro h
    constructor
    · exact h.1.1
    · constructor
      · exact h.1.2
      · exact h.2
  · intro h
    constructor
    · constructor
      · exact h.1
      · exact h.2.1
    · exact h.2.2
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := ⟨fun h ↦ ⟨h.1.1,h.1.2,h.2⟩,fun h ↦ ⟨⟨h.1,h.2.1⟩,h.2.2⟩⟩


example : P ↔ P ∧ True := by
  exact ⟨fun hp ↦ ⟨hp,True.intro⟩, fun hpt ↦ hpt.1⟩
  done

example : P ↔ P ∧ True := by
 constructor
 · intro hp
   constructor <;> trivial
 · intro hpt
   exact hpt.1

example : P ↔ P ∧ True := ⟨fun hp ↦ ⟨hp,True.intro⟩, fun hpt ↦ hpt.1⟩


example : False ↔ P ∧ False := by
  constructor
  · intro f
    constructor
    · exact f.elim
    · exact f
  · intro pnF
    exact pnF.2
  done

example : False ↔ P ∧ False := ⟨fun f ↦ f.elim, fun f ↦ f.2⟩


example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hpIq hrIs
  constructor
  · intro hpr
    constructor
    · apply hpIq.mp
      · exact hpr.1
    · apply hrIs.mp
      · exact hpr.2
  · intro hqs
    constructor
    · apply hpIq.mpr
      · exact hqs.1
    · apply hrIs.mpr
      · exact hqs.2
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
 fun ⟨hpq,hqp⟩ ⟨hrs,hsr⟩ ↦ ⟨fun hpr ↦ ⟨hpq hpr.1,hrs hpr.2⟩, fun hqs ↦ ⟨hqp hqs.1,hsr hqs.2⟩⟩

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S)
| ⟨hpq,hqp⟩, ⟨hrs,hsr⟩ => ⟨fun hpr ↦ ⟨hpq hpr.1,hrs hpr.2⟩, fun hqs ↦ ⟨hqp hqs.1,hsr hqs.2⟩⟩


example : ¬(P ↔ ¬P) := by
  intro hpInp
  have := And.intro (hpInp.1) (hpInp.2)
  by_cases hp:P
  · exact (this.1 hp) hp
  · exact hp (this.2 hp)
  done

example : ¬(P ↔ ¬P) :=
 fun pInp ↦
  match Classical.em P with
  | Or.inl hp => (pInp.mp hp) hp
  | Or.inr hnp => hnp (pInp.mpr hnp)
