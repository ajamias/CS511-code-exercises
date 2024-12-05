import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust

math2001_init

open Set Function Nat

/-# Exercise 4-/

--Exercise 6.4.3.1

theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain h | h := even_or_odd n
  · -- case 1: n is even
    dsimp [Even] at h
    obtain ⟨k, hk⟩ := h
    rw [hk] at hn
    cancel 2 at hn
    have IH := extract_pow_two k hn
    obtain ⟨a, ⟨x, h⟩⟩ := IH
    obtain ⟨h1, h2⟩ := h
    use a + 1, x
    constructor
    · apply h1
    · rw [h2] at hk
      calc
        n = 2 * (2 ^ a * x) := by rw [hk]
        _ = 2 ^ (a + 1) * x := by ring
  · -- case 2: n is odd
    use 0, n
    constructor
    · apply h
    · ring

/-# Exercise 5-/

------------------------------------------------------------------------------------
--Exercise 9.1.10.1

example : 4 ∈ {a : ℚ | a < 3} := by
  sorry

example : 4 ∉ {a : ℚ | a < 3} := by
  dsimp
  numbers

------------------------------------------------------------------------------------
--Exercise 9.1.10.2

example : 6 ∈ {n : ℕ | n ∣ 42} := by
  dsimp
  dsimp [(· ∣ ·)]
  use 7
  numbers

example : 6 ∉ {n : ℕ | n ∣ 42} := by
  sorry

------------------------------------------------------------------------------------
--Exercise 9.1.10.3

example : 8 ∈ {k : ℤ | 5 ∣ k} := by
  sorry

example : 8 ∉ {k : ℤ | 5 ∣ k} := by
  dsimp
  apply Int.not_dvd_of_exists_lt_and_lt
  use 1
  constructor
  · numbers
  · numbers

/-# Exercise 6-/
------------------------------------------------------------------------------------
--Exercise 9.1.10.6

example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
  dsimp [Set.subset_def]
  intro x hx
  obtain ⟨k, hk⟩ := hx
  use 4 * k
  calc
    x = 20 * k := by rw [hk]
    _ = 5 * (4 * k) := by ring

example : {a : ℕ | 20 ∣ a} ⊈ {x : ℕ | 5 ∣ x} := by
  sorry

------------------------------------------------------------------------------------
--Exercise 9.1.10.7

example : {a : ℕ | 5 ∣ a} ⊆ {x : ℕ | 20 ∣ x} := by
  sorry

example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  dsimp [Set.subset_def]
  push_neg
  use 5
  constructor
  · dsimp [(· ∣ ·)]
    use 1
    numbers
  · apply Nat.not_dvd_of_exists_lt_and_lt
    use 0
    constructor
    · numbers
    · numbers

------------------------------------------------------------------------------------
--Exercise 9.2.8.5

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp [Set.subset_def]
  intro x hx
  constructor
  · obtain ⟨k, hk⟩ := hx
    calc
      x = 7 + (x - 7) := by ring
      _ = 7 + 10 * k := by rw [hk]
      _ = 7 + 2 * (5 * k) := by ring
      _ ≡ 7 [ZMOD 2] := by extra
      _ ≡ 1 + 2 * 3 [ZMOD 2] := by numbers
      _ ≡ 1 [ZMOD 2] := by extra
  · obtain ⟨k, hk⟩ := hx
    calc
      x = 7 + (x - 7) := by ring
      _ = 7 + 10 * k := by rw [hk]
      _ = 7 + 5 * (2 * k) := by ring
      _ ≡ 7 [ZMOD 5] := by extra
      _ ≡ 2 + 5 * 1 [ZMOD 5] := by numbers
      _ ≡ 2 [ZMOD 5] := by extra

/-# Problem 2-/

--Exercise 9.2.8.6

example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  sorry

--Exercise 9.3.6.1

def r (s : Set ℕ) : Set ℕ := s ∪ {3}

example : ¬ Injective r := by
  sorry
