import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

--Exercise 5.1.7.6

@[autograded 2]
example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  constructor
  · intro H
    rw [h] at H
    exact H
  · intro H
    rw [Iff.symm h] at H
    exact H

--Exercise 5.1.7.8

@[autograded 2]
example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  · intro h
    obtain h | h := h
    · right
      exact h
    · left
      exact h
  · intro h
    obtain h | h := h
    · right
      exact h
    · left
      exact h

--Exercise 5.1.7.9

@[autograded 2]
example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  · intro h
    constructor
    · intro H
      apply h
      left
      exact H
    · intro H
      apply h
      right
      exact H
  · intro h H
    obtain ⟨hP, hQ⟩ := h
    obtain HP | HQ := H
    · contradiction
    · contradiction

--Exercise 5.1.7.11

@[autograded 2]
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro H
    obtain ⟨x, hP⟩ := H
    use x
    have hPQ : P x ↔ Q x := h x
    rw [hPQ] at hP
    exact hP
  · intro H
    obtain ⟨x, hQ⟩ := H
    use x
    have hPQ : P x ↔ Q x := h x
    rw [Iff.symm hPQ] at hQ
    exact hQ

--Exercise 5.1.7.12

@[autograded 2]
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intro h
    obtain ⟨x, y, h⟩ := h
    use y, x
    exact h
  · intro h
    obtain ⟨y, x, h⟩ := h
    use x, y
    exact h

--Exercise 5.1.7.13

@[autograded 2]
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intro h
    intro y x
    apply h x y
  · intro h
    intro x y
    apply h y x

--Exercise 5.1.7.14

@[autograded 3]
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  sorry

--Exercise 5.2.7.2

@[autograded 3]
example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  sorry
