import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

--# Exercise 3

--Slides 18, Page 25

example (h : ∃x : Type, ∀y : Type, (x = y)) : (∀x : Type, ∀y : Type, (x = y)) := by
  intro x y
  obtain ⟨n, h⟩ := h
  have hx : n = x := by apply h
  have hy : n = y := by apply h
  calc
    x = n := by rw [hx]
    _ = y := by rw [hy]

--Slides 29 Part III, Page 8

example : (∃x : Type, ∀y : Type, (x = y)) → (∀v : Type, ∀w : Type, (v = w)) := by
  intro h v w
  obtain ⟨n, h⟩ := h
  have hv : n = v := by apply h
  have hw : n = w := by apply h
  calc
    v = n := by rw [hv]
    _ = w := by rw [hw]

--# Exercise 4

--Exercise 5.3.6.9

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t
  by_cases h : t > 4
  · left
    exact h
  · right
    push_neg at h
    calc
      t ≤ 4 := by rel [h]
      _ < 5 := by numbers

--Example 6.1.2

example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    left
    dsimp [Even]
    use 0
    numbers
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · right
      dsimp [Odd]
      use x
      calc
        k + 1 = x + x + 1 := by rw [hx]
        _ = 2 * x + 1 := by ring
    · left
      dsimp [Even]
      use x + 1
      calc
        k + 1 = 2 * x + 1 + 1 := by rw [hx]
        _ = x + 1 + (x + 1) := by ring

--Example 6.1.6

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2 ^ (k + 1) = 2 ^ k * 2 := by ring
      _ ≥ k ^ 2 * 2 := by rel [IH]
      _ = k ^ 2 + k * k := by ring
      _ ≥ k ^ 2 + 4 * k := by rel [hk]
      _ = k ^ 2 + 2 * k + 2 * k := by ring
      _ ≥ k ^ 2 + 2 * k + 2 * 4 := by rel [hk]
      _ = k ^ 2 + 2 * k + 1 + 7 := by ring
      _ ≥ k ^ 2 + 2 * k + 1 := by extra
      _ = (k + 1) ^ 2 := by ring

--# Problem 2

--Exercise 5.3.6.12

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry

--Exercise 6.1.7.2

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  sorry

--Exercise 6.1.7.3

example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  sorry
