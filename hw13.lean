import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

/-# Exercise 3-/

--Exercise 10.1.5.4

section
local infix:50 "∼" => fun (x y : ℤ) ↦ y ≡ x + 1 [ZMOD 5]

example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 0
  dsimp [Int.ModEq]
  apply Int.not_dvd_of_exists_lt_and_lt
  use -1
  constructor
  · numbers
  · numbers

example : Symmetric (· ∼ ·) := by
  sorry

example : ¬ Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  push_neg
  use 0,6
  constructor
  · calc
      6 ≡ 1 + 1 * 5 [ZMOD 5] := by numbers
      _ ≡ 1 [ZMOD 5] := by extra
  · dsimp [Int.ModEq]
    apply Int.not_dvd_of_exists_lt_and_lt
    use -2
    constructor
    · numbers
    · numbers

example : AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  intro x y h1 h2
  dsimp [Int.ModEq] at *
  obtain ⟨k, h1⟩ := h1
  have H1 :=
  calc
    y - x = y - (x + 1) + 1 := by ring
    _ = 5 * k + 1 := by rw [h1]
  obtain ⟨n, h2⟩ := h2
  have H2 :=
  calc
    x - y = x - (y + 1) + 1 := by ring
    _ = 5 * n + 1 := by rw [h2]
  

example : ¬ AntiSymmetric (· ∼ ·) := by
  sorry

example : Transitive (· ∼ ·) := by
  sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 0,6,12
  constructor
  · calc
      6 ≡ 1 + 1 * 5 [ZMOD 5] := by numbers
      _ ≡ 1 [ZMOD 5] := by extra
  · constructor
    · calc
        12 ≡ 6 + 1 + 1 * 5 [ZMOD 5] := by numbers
        _ ≡ 6 + 1 [ZMOD 5] := by extra
    · dsimp [Int.ModEq]
      apply Int.not_dvd_of_exists_lt_and_lt
      use 2
      constructor
      · numbers
      · numbers

end

/-# Exercise 4-/

--Exercise 10.1.5.5

section
local infix:50 "∼" => fun (x y : ℤ) ↦ x + y ≡ 0 [ZMOD 3]

example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 1
  dsimp [Int.ModEq]
  apply Int.not_dvd_of_exists_lt_and_lt
  use 0
  constructor
  · numbers
  · numbers

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y h
  calc
    y + x = x + y := by ring
    _ ≡ 0 [ZMOD 3] := by rel [h]

example : ¬ Symmetric (· ∼ ·) := by
  sorry

example : AntiSymmetric (· ∼ ·) := by
  sorry

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 1,2
  constructor
  · calc
      1 + 2 = 0 + 1 * 3 := by numbers
      _ ≡ 0 + 1 * 3 [ZMOD 3] := by extra
      _ ≡ 0 [ZMOD 3] := by extra
  · constructor
    · calc
        1 + 2 = 0 + 1 * 3 := by numbers
        _ ≡ 0 + 1 * 3 [ZMOD 3] := by extra
        _ ≡ 0 [ZMOD 3] := by extra
    · numbers

example : Transitive (· ∼ ·) := by
  sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 1,2,4
  constructor
  · calc
      1 + 2 = 0 + 1 * 3 := by numbers
      _ ≡ 0 + 1 * 3 [ZMOD 3] := by extra
      _ ≡ 0 [ZMOD 3] := by extra
  · constructor
    · calc
        2 + 4 = 0 + 2 * 3 := by numbers
        _ ≡ 0 + 2 * 3 [ZMOD 3] := by extra
        _ ≡ 0 [ZMOD 3] := by extra
    · dsimp [Int.ModEq]
      apply Int.not_dvd_of_exists_lt_and_lt
      use 1
      constructor
      · numbers
      · numbers

end

/-# Problem 2-/

--Exercise 10.1.5.6

example : Reflexive ((· : Set ℕ) ⊆ ·) := by
  sorry

example : ¬ Reflexive ((· : Set ℕ) ⊆ ·) := by
  sorry

example : Symmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : ¬ Symmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : ¬ AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : Transitive ((· : Set ℕ) ⊆ ·) := by
  sorry

example : ¬ Transitive ((· : Set ℕ) ⊆ ·) := by
  sorry
