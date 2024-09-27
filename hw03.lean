import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- # Exercise 3

/-2 points-/
theorem exercise2_3_6_2 {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h | h := h
  · rw [h]; numbers
  · rw [h]; numbers

/-2 points-/
theorem exercise2_3_6_3 {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain h | h := h
  · rw [h]; numbers
  · rw [h]; numbers

/-2 points-/
theorem exercise2_3_6_4 {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain h | h := h
  · calc
      x * y + 2 * x = 2 * y + 2 * 2 := by rw [h]
      _ = 2 * y + 4 := by ring
  · have h1 :=
    calc
      x * y + 2 * x = x * -2 + 2 * x := by rw [h]
      _ = 0 := by ring
    have h2 :=
    calc
      2 * y + 4 = 2 * -2 + 4 := by rw [h]
      _ = 0 := by ring
    calc
      x * y + 2 * x = 0 := by rw [h1]
      _ = 2 * y + 4 := by rw [h2]

-- # Exercise 4

/-2 points-/
theorem exercise2_3_6_12 {x : ℤ} : 2 * x ≠ 3 := by
  have h := le_or_succ_le x 1
  obtain h | h := h
  · apply ne_of_lt
    calc
      2 * x < 2 * x + 1 := by extra
      _ ≤ 2 * 1 + 1 := by rel [h]
  · apply ne_of_gt
    calc
      2 * x ≥ 2 * 2 := by rel [h]
      _ > 3 := by numbers

/-2 points-/
theorem exercise2_4_5_1 {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * a + b = a + (a + b) := by ring
    _ ≤ 1 + (a + b) := by rel [h1]
    _ ≤ 1 + 3 := by rel [h2]
    _ = 4 := by ring

/-2 points-/
theorem exercise2_4_5_6 {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  have h3 :=
  calc
    x + 2 * y = x + y + y := by ring
    _ = 5 + y := by rw [h1]
  rw [h2] at h3
  constructor
  · calc
      x = 5 - y := by addarith [h1]
      _ = 7 - 2 - y := by ring
      _ = 5 + y - 2 - y := by rw [h3]
      _ = 3 := by ring
  · addarith [h3]

-- # Problem 2

/-2 points-/
theorem exercise2_3_6_10 {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h1 :=
  calc
    t ^ 2 * (t - 1) = t ^ 3 - t ^ 2 := by ring
    _ = 0 := by addarith [ht]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h2 | h2 := h2
  · right
    have h3 :=
    calc
      t * t = t ^ 2 := by ring
      _ = 0 := by rw [h2]
    have h4 := eq_zero_or_eq_zero_of_mul_eq_zero h3
    obtain h4 | h4 := h4
    · exact h4
    · exact h4
  · left; addarith [h2]

/-2 points-/
theorem exercise2_3_6_14 {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  have h := le_or_succ_le m 5
  obtain h | h := h
  · apply ne_of_lt
    calc
      m ^ 2 + 4 * m = m * m + 4 * m := by ring
      _ ≤ 5 * 5 + 4 * 5 := by rel [h]
      _ < 46 := by numbers
  · apply ne_of_gt
    calc
      m ^ 2 + 4 * m = m * m + 4 * m := by ring
      _ ≥ 6 * 6 + 4 * 6 := by rel [h]
      _ > 46 := by numbers

/-2 points-/
theorem exercise2_4_5_7 {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) : a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  have h3 :=
  calc
    a = a * b := by rw [h1]
    _ = b := by rw [h2]
  have h4 :=
  calc
    a * (b - 1) = a * b - a := by ring
    _ = a - a := by rw [h1]
    _ = 0 := by ring
  have h5 := eq_zero_or_eq_zero_of_mul_eq_zero h4
  obtain h5 | h5 := h5
  · left
    constructor
    exact h5
    calc
      b = a := by rw [h3]
      _ = 0 := by rw [h5]
  · right
    constructor
    calc
      a = b := by rw [h3]
      _ = b - 1 + 1 := by ring
      _ = 0 + 1 := by rw [h5]
      _ = 1 := by ring
    addarith [h5]