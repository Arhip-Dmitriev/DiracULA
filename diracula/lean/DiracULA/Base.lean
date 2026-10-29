/-
Copyright 2026 Arkhip A. Dmitriev
Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# Roots and phases

`√d`, `e^{2πiθ}` and `e^{2πi/d}` as complex numbers, and the facts about them the symbolic
sums use.
-/

namespace DiracULA

open Complex Finset

/-- `e^{2πiθ}`. -/
noncomputable def ex (θ : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * θ)

/-- `e^{2πi/d}`. -/
noncomputable def om (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)

theorem ex_zero : ex 0 = 1 := by simp [ex]

theorem ex_add (a b : ℝ) : ex (a + b) = ex a * ex b := by
  simp only [ex, ← Complex.exp_add]; congr 1; push_cast; ring

theorem ex_int (a : ℝ) (z : ℤ) : ex (a + z) = ex a := by
  rw [ex_add]
  have : ex z = 1 := by
    simp only [ex]
    rw [Complex.exp_eq_one_iff]
    exact ⟨z, by push_cast; ring⟩
  rw [this, mul_one]

theorem om_prim (d : ℕ) (hd : 0 < d) : IsPrimitiveRoot (om d) d := by
  have := Complex.isPrimitiveRoot_exp d hd.ne'
  simpa [om] using this

theorem conj_om (d : ℕ) : (starRingEnd ℂ) (om d) = (om d)⁻¹ := by
  simp only [om, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, Complex.conj_ofReal, map_ofNat]
  ring

theorem sqrt_mul_sqrt (d : ℕ) : (Real.sqrt d : ℂ) * Real.sqrt d = d := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]; simp

/-- `√d` as a complex number. -/
noncomputable abbrev rt (d : ℕ) : ℂ := (Real.sqrt d : ℂ)

theorem rt_ne (d : ℕ) (hd : 0 < d) : rt d ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  show (Real.sqrt d : ℂ) ≠ 0
  exact_mod_cast this.ne'

theorem rt_sq (d : ℕ) : rt d * rt d = d := sqrt_mul_sqrt d

theorem rt_sq' (d : ℕ) : rt d ^ 2 = d := by rw [sq, rt_sq]

theorem om_ne_zero (d : ℕ) (hd : 0 < d) : om d ≠ 0 := (om_prim d hd).ne_zero hd.ne'

theorem om_pow_self (d : ℕ) (hd : 0 < d) : om d ^ d = 1 := (om_prim d hd).pow_eq_one

/-- A sum below `a * b` as a double sum over the low and high parts. -/
theorem sum_range_mul (a b : ℕ) (f : ℕ → ℂ) :
    ∑ v ∈ range (a * b), f v = ∑ v ∈ range a, ∑ y ∈ range b, f (v + a * y) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [mul_add, mul_one, Finset.sum_range_add, ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_range_succ, add_comm (a * b) v]

end DiracULA
