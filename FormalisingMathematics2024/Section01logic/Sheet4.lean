/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases'`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (A B P Q R : Prop)

example : P ∧ Q → P := by
  rintro ⟨hp,hq⟩ ; exact hp
  done

example : P ∧ Q → P := by
 intro hpnq
 cases hpnq
 · assumption

example : P ∧ Q → P := fun h ↦ h.1

example: P ∧ Q → P
| h => h.1


example : P ∧ Q → Q := by
  intro hpnq
  cases hpnq
  · assumption
  done


example : P ∧ Q → Q := by
 rintro ⟨_,hq⟩
 exact hq

example : P ∧ Q → Q := fun hpnq ↦ hpnq.2


example : P ∧ Q → Q
| h => h.2

example : (P → Q → R) → P ∧ Q → R := by
  rintro hpqr ⟨hp,hq⟩
  exact (hpqr hp) hq
  done

example : (P → Q → R) → P ∧ Q → R := by
 intro hpqr hpq
 rcases hpq with ⟨hp,hq⟩
 apply hpqr <;> assumption

example : (P → Q → R) → P ∧ Q → R := fun hpqr ⟨hp,hq⟩ ↦ (hpqr hp) hq

example : (P → Q → R) → P ∧ Q → R
| hpqr, hpq => (hpqr hpq.1) hpq.2

example : (P → Q → R) → P ∧ Q → R
| hpqr, ⟨hp,hq⟩ => (hpqr hp) hq


example : P → Q → P ∧ Q := by
  intro hp hq
  constructor ; exact hp ; exact hq
  done


example : P → Q → P ∧ Q := by
  intro hp hq
  apply And.intro <;> first|exact hp|exact hq
  done

example : P → Q → P ∧ Q
| hp, hq => ⟨hp,hq⟩


example : P → Q → P ∧ Q := fun hp hq ↦ ⟨hp,hq⟩

example : P → Q → P ∧ Q := by
  intro hp hq
  apply And.intro <;> first|exact hp|exact hq
  done
/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  rintro ⟨hp,hq⟩
  constructor ; exact hq ; exact hp
  done

example : P ∧ Q → Q ∧ P := by
  intro hpq
  constructor ; exact hpq.2 ; exact hpq.1
  done

example : P ∧ Q → Q ∧ P := by
  apply And.comm.mp

example : P ∧ Q → Q ∧ P := fun ⟨hp,hq⟩ ↦ ⟨hq,hp⟩


example : P ∧ Q → Q ∧ P
| ⟨hp,hq⟩ => ⟨hq,hp⟩

example : P → P ∧ True := by
  intro hp
  constructor; exact hp ; exact True.intro
  done


example : P → P ∧ True := by
 intro hp
 exact And.intro hp True.intro


example : P → P ∧ True := fun hp ↦ ⟨hp,True.intro⟩

example : P → P ∧ True := by tauto

example : P → P ∧ True
| hp => ⟨hp,True.intro⟩

example : False → P ∧ False := by
  intro hf
  exfalso
  trivial
  done

example : False → P ∧ False := by
 intro hf
 constructor <;> exact hf.elim

example : False → P ∧ False := fun hf ↦ ⟨hf.elim,hf⟩

example : False → P ∧ False
| hf => ⟨hf.elim,hf⟩


/-- `∧` is transitive -/ --trivially so?
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro hpq hqr
  constructor
  · exact hpq.1
  · exact hqr.2
  done
/-- `∧` is transitive -/ --trivially..
example : P ∧ A → B ∧ R → P ∧ R := by
  intro hpq hqr
  constructor
  · exact hpq.1
  · exact hqr.2
  done

example : P ∧ Q → Q ∧ R → P ∧ R := fun ⟨hp,_⟩ ⟨_,hr⟩ ↦ ⟨hp,hr⟩

example : P ∧ A → B ∧ R → P ∧ R := fun ⟨hp,_⟩ ⟨_,hr⟩ ↦ ⟨hp,hr⟩

example : P ∧ Q → Q ∧ R → P ∧ R
| ⟨hp,_⟩ , ⟨_,hr⟩ => ⟨hp,hr⟩

example : (P ∧ Q → R) → P → Q → R := by
  intro hpqr hp hq
  exact hpqr ⟨hp,hq⟩
  done

example : (P ∧ Q → R) → P → Q → R := fun hpqr hp hq ↦ hpqr ⟨hp,hq⟩

example : (P ∧ Q → R) → P → Q → R
| hpqr, hp, hq => hpqr ⟨hp,hq⟩
