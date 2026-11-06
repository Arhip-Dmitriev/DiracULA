/-
Copyright 2026 Arkhip A. Dmitriev
Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# The quadratic Gauss sum

`Σ_{y < d} e^(2πi y²/d) = √d (1 + i)(1 + (-i)^d)/2` for every `d ≥ 1`, from the functional
equation of the Jacobi theta function at the cusps `2/d` and `-d/2`.
-/

open Complex Real Filter Topology

namespace DiracULA.Gauss

/-- `(a w)^s = a^s w^s` for a positive real `a`. -/
theorem cpow_real_mul {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : w ≠ 0) (s : ℂ) :
    ((a : ℂ) * w) ^ s = (a : ℂ) ^ s * w ^ s := by
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.2 ha.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero ha' hw), cpow_def_of_ne_zero ha', cpow_def_of_ne_zero hw,
    log_ofReal_mul ha hw, ← Complex.exp_add, ofReal_log ha.le]
  ring_nf

theorem summable_theta {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun n : ℤ => cexp (π * I * (n : ℂ) ^ 2 * τ) := by
  have := (hasSum_jacobiTheta₂_term 0 hτ).summable
  refine this.congr fun n => ?_
  simp only [jacobiTheta₂_term, mul_zero, zero_add]

/-- The theta series split by residues modulo `c`. -/
theorem theta_split (c : ℕ) [NeZero c] {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta τ = ∑ r : Fin c, ∑' m : ℤ, cexp (π * I * ((m * c + r : ℤ) : ℂ) ^ 2 * τ) := by
  have hs := summable_theta hτ
  rw [jacobiTheta, ← (Int.divModEquiv c).symm.tsum_eq]
  have hs' : Summable fun p : ℤ × Fin c =>
      cexp (π * I * (((Int.divModEquiv c).symm p : ℤ) : ℂ) ^ 2 * τ) :=
    ((Int.divModEquiv c).symm.summable_iff).2 hs
  rw [← (Equiv.prodComm (Fin c) ℤ).tsum_eq] at *
  have hs'' : Summable fun p : Fin c × ℤ =>
      cexp (π * I * (((Int.divModEquiv c).symm ((Equiv.prodComm (Fin c) ℤ) p) : ℤ) : ℂ) ^ 2 * τ) :=
    ((Equiv.prodComm (Fin c) ℤ).summable_iff).2 hs'
  rw [hs''.tsum_prod, tsum_fintype]
  rfl

/-- One residue class through the functional equation of `jacobiTheta₂`. -/
theorem class_eq (c : ℕ) (hc : 0 < c) (r : ℤ) {z : ℂ} (hz : 0 < z.im) :
    ∑' m : ℤ, cexp (π * I * ((m * c + r : ℤ) : ℂ) ^ 2 * z) =
      1 / (-I * (z * c ^ 2)) ^ (1 / 2 : ℂ) * jacobiTheta₂ (r / c) (-1 / (z * c ^ 2)) := by
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have h1 : ∀ m : ℤ, cexp (π * I * ((m * c + r : ℤ) : ℂ) ^ 2 * z) =
      cexp (π * I * r ^ 2 * z) * jacobiTheta₂_term m (z * r * c) (z * c ^ 2) := by
    intro m
    simp only [jacobiTheta₂_term, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [tsum_congr h1, tsum_mul_left]
  rw [show ∑' m : ℤ, jacobiTheta₂_term m (z * r * c) (z * c ^ 2) =
      jacobiTheta₂ (z * r * c) (z * c ^ 2) from rfl,
    jacobiTheta₂_functional_equation]
  have e1 : z * r * c / (z * c ^ 2) = r / c := by field_simp
  have e2 : -π * I * (z * r * c) ^ 2 / (z * c ^ 2) = -(π * I * r ^ 2 * z) := by
    field_simp
  rw [e1, e2, Complex.exp_neg]
  have : cexp (π * I * r ^ 2 * z) ≠ 0 := Complex.exp_ne_zero _
  field_simp


/-- `(c²)^(1/2) = c` for `c ≥ 0`. -/
theorem sq_cpow_half (c : ℝ) (hc : 0 ≤ c) : (((c ^ 2 : ℝ)) : ℂ) ^ (1 / 2 : ℂ) = c := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
    ← Real.sqrt_eq_rpow, Real.sqrt_sq hc]

/-- `θ₂(x, τ) → 1` for real `x` as `im τ → ∞`. -/
theorem theta2_tendsto_one {α : Type*} {l : Filter α} (x : ℝ) (τ : α → ℂ)
    (hτ : Tendsto (fun a => (τ a).im) l atTop) :
    Tendsto (fun a => jacobiTheta₂ x (τ a)) l (𝓝 1) := by
  have hg : ∑' n : ℤ, (if n = 0 then (1 : ℂ) else 0) = 1 := by rw [tsum_ite_eq]
  rw [← hg]
  unfold jacobiTheta₂
  refine tendsto_tsum_of_dominated_convergence
    (f := fun a (n : ℤ) => jacobiTheta₂_term n x (τ a))
    (bound := fun n : ℤ => (|n| ^ 0 : ℝ) * rexp (-π * (1 * n ^ 2 - 2 * 0 * |n|)))
    (summable_pow_mul_jacobiTheta₂_term_bound 0 one_pos 0) (fun n => ?_) ?_
  · by_cases hn : n = 0
    · subst hn
      simpa [jacobiTheta₂_term] using tendsto_const_nhds
    · rw [if_neg hn, tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [norm_jacobiTheta₂_term, ofReal_im, mul_zero, sub_zero]
      have hn2 : (0 : ℝ) < π * (n : ℝ) ^ 2 := by
        have : (n : ℝ) ≠ 0 := Int.cast_ne_zero.2 hn
        positivity
      have h1 : Tendsto (fun a => π * (n : ℝ) ^ 2 * (τ a).im) l atTop := hτ.const_mul_atTop hn2
      have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
      refine h2.congr fun a => ?_
      simp only [Function.comp_apply]
      ring_nf
  · filter_upwards [hτ.eventually_ge_atTop 1] with a ha n
    simpa using norm_jacobiTheta₂_term_le one_pos (S := 0) (z := (x : ℂ)) (by simp) ha n

/-- `√(-i z) θ(x₀ + z) → S/c` as `im(-1/z) → ∞`, for `x₀` whose phases are periodic modulo `c`. -/
theorem cusp (c : ℕ) (hc : 0 < c) (x0 : ℝ)
    (hper : ∀ r m : ℤ, cexp (π * I * ((m * c + r : ℤ) : ℂ) ^ 2 * x0) = cexp (π * I * (r : ℂ) ^ 2 * x0))
    {α : Type*} {l : Filter α} (z : α → ℂ) (hz : ∀ a, 0 < (z a).im)
    (hz' : Tendsto (fun a => (-1 / z a).im) l atTop) :
    Tendsto (fun a => (-I * z a) ^ (1 / 2 : ℂ) * jacobiTheta (x0 + z a)) l
      (𝓝 ((∑ r : Fin c, cexp (π * I * ((r : ℤ) : ℂ) ^ 2 * x0)) / c)) := by
  haveI : NeZero c := ⟨hc.ne'⟩
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hcr : (0 : ℝ) < (c : ℝ) ^ 2 := by positivity
  have key : ∀ a, (-I * z a) ^ (1 / 2 : ℂ) * jacobiTheta (x0 + z a) =
      (∑ r : Fin c, cexp (π * I * ((r : ℤ) : ℂ) ^ 2 * x0) *
        jacobiTheta₂ ((r : ℤ) / c) (-1 / (z a * c ^ 2))) / c := by
    intro a
    have hza : 0 < (x0 + z a).im := by simpa using hz a
    have hz0 : z a ≠ 0 := fun h => by have := hz a; rw [h] at this; simp at this
    have hiz : -I * z a ≠ 0 := mul_ne_zero (neg_ne_zero.2 I_ne_zero) hz0
    have hrt : (-I * z a) ^ (1 / 2 : ℂ) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff, not_and_or]; exact Or.inl hiz
    have hsq : (-I * (z a * c ^ 2)) ^ (1 / 2 : ℂ) = c * (-I * z a) ^ (1 / 2 : ℂ) := by
      rw [show -I * (z a * c ^ 2) = (((c : ℝ) ^ 2 : ℝ) : ℂ) * (-I * z a) by push_cast; ring,
        cpow_real_mul hcr hiz]
      congr 1
      exact sq_cpow_half c (Nat.cast_nonneg c)
    rw [theta_split c hza, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hsplit : ∀ m : ℤ, cexp (π * I * ((m * c + r : ℤ) : ℂ) ^ 2 * (x0 + z a)) =
        cexp (π * I * ((r : ℤ) : ℂ) ^ 2 * x0) * cexp (π * I * ((m * c + r : ℤ) : ℂ) ^ 2 * z a) := by
      intro m
      rw [← hper r m, ← Complex.exp_add]
      congr 1
      ring
    rw [tsum_congr hsplit, tsum_mul_left, class_eq c hc r (hz a), hsq]
    field_simp
  refine Tendsto.congr (fun a => (key a).symm) ?_
  refine Tendsto.div_const ?_ _
  rw [show (∑ r : Fin c, cexp (π * I * ((r : ℤ) : ℂ) ^ 2 * x0)) =
      ∑ r : Fin c, cexp (π * I * ((r : ℤ) : ℂ) ^ 2 * x0) * 1 by simp]
  refine tendsto_finset_sum _ fun r _ => Tendsto.const_mul _ ?_
  have hx : ((r : ℤ) : ℂ) / c = (((r : ℤ) : ℝ) / c : ℝ) := by push_cast; ring
  rw [show (fun a => jacobiTheta₂ (((r : ℤ) : ℂ) / c) (-1 / (z a * c ^ 2))) =
      (fun a => jacobiTheta₂ ((((r : ℤ) : ℝ) / c : ℝ) : ℂ) (-1 / (z a * c ^ 2))) by rw [hx]]
  refine theta2_tendsto_one _ _ ?_
  have : ∀ a, (-1 / (z a * c ^ 2)).im = (-1 / z a).im / (c : ℝ) ^ 2 := by
    intro a
    rw [show -1 / (z a * c ^ 2) = (-1 / z a) / (((c : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring,
      div_ofReal_im]
  simp_rw [this]
  exact hz'.atTop_div_const hcr


theorem exp_int_two_pi (k : ℤ) (w : ℂ) : cexp (w + 2 * π * I * k) = cexp w := by
  rw [Complex.exp_add, show 2 * π * I * (k : ℂ) = k * (2 * π * I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem per_left (d : ℕ) (hd : 0 < d) (r m : ℤ) :
    cexp (π * I * ((m * d + r : ℤ) : ℂ) ^ 2 * ((2 / d : ℝ) : ℂ)) =
      cexp (π * I * (r : ℂ) ^ 2 * ((2 / d : ℝ) : ℂ)) := by
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  rw [← exp_int_two_pi (2 * m * r + m ^ 2 * d) (π * I * (r : ℂ) ^ 2 * ((2 / d : ℝ) : ℂ))]
  congr 1
  push_cast
  field_simp
  ring

theorem per_right (d : ℕ) (r m : ℤ) :
    cexp (π * I * ((m * (2 : ℕ) + r : ℤ) : ℂ) ^ 2 * ((-(d : ℝ) / 2 : ℝ) : ℂ)) =
      cexp (π * I * (r : ℂ) ^ 2 * ((-(d : ℝ) / 2 : ℝ) : ℂ)) := by
  rw [← exp_int_two_pi (-(d * (m * r + m ^ 2))) (π * I * (r : ℂ) ^ 2 * ((-(d : ℝ) / 2 : ℝ) : ℂ))]
  congr 1
  push_cast
  ring

theorem half_mul_half {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt x : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx,
    Real.sqrt_eq_rpow]

theorem neg_I_half : (-I) ^ (1 / 2 : ℂ) = (Real.sqrt 2 / 2 : ℝ) * (1 - I) := by
  rw [cpow_def_of_ne_zero (neg_ne_zero.2 I_ne_zero), log_neg_I,
    show -(π / 2 : ℂ) * I * (1 / 2) = ((-(π / 4) : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  push_cast
  ring

/-- The quadratic Gauss sum. -/
theorem gauss_sum (d : ℕ) (hd : 0 < d) :
    ∑ y ∈ Finset.range d, cexp (2 * π * I * (y : ℂ) ^ 2 / d) =
      (1 + I) * (1 + (-I) ^ d) / 2 * Real.sqrt d := by
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hdr : (0 : ℝ) < d := Nat.cast_pos.2 hd
  set s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hs
  have hspos : ∀ n, 0 < s n := fun n => by simp only [hs]; positivity
  set z : ℕ → ℂ := fun n => (s n : ℂ) * I with hz
  set τ : ℕ → ℂ := fun n => ((2 / d : ℝ) : ℂ) + z n with hτ
  have hτre : ∀ n, (τ n).re = 2 / d := fun n => by simp [hτ, hz]
  have hτim' : ∀ n, (τ n).im = s n := fun n => by simp [hτ, hz]
  have hzim : ∀ n, 0 < (z n).im := fun n => by simpa [hz] using hspos n
  have hτim : ∀ n, 0 < (τ n).im := fun n => by rw [hτim']; exact hspos n
  have hτ0 : ∀ n, τ n ≠ 0 := fun n h => by have := hτim n; rw [h] at this; simp at this
  have hnorm : ∀ n, normSq (τ n) = (2 / d) ^ 2 + s n ^ 2 := fun n => by
    rw [normSq_apply, hτre, hτim']; ring
  -- the left cusp
  have hL := cusp d hd (2 / d) (per_left d hd) (l := atTop) z hzim (by
    have : ∀ n : ℕ, (-1 / z n).im = (n : ℝ) + 1 := fun n => by
      have h1 := hspos n
      simp only [hz, div_im, neg_re, neg_im, one_re, one_im, mul_re, mul_im, ofReal_re, ofReal_im,
        I_re, I_im, normSq_apply]
      simp only [hs]
      field_simp
      ring
    simp_rw [this]
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  -- the right cusp
  set z' : ℕ → ℂ := fun n => -1 / τ n + d / 2 with hz'
  have hz'im : ∀ n, 0 < (z' n).im := fun n => by
    have h := UpperHalfPlane.im_inv_neg_coe_pos ⟨τ n, hτim n⟩
    have e : z' n = (-τ n)⁻¹ + ((d / 2 : ℝ) : ℂ) := by simp only [hz']; push_cast; field_simp
    rw [e, add_im, ofReal_im, add_zero]
    exact h
  have hzt : ∀ n, z' n * τ n = (((d : ℝ) * s n / 2 : ℝ) : ℂ) * I := fun n => by
    simp only [hz']
    rw [add_mul, div_mul_cancel₀ _ (hτ0 n)]
    simp only [hτ, hz]
    push_cast
    field_simp
    ring
  have hcpos : ∀ n, (0 : ℝ) < (d : ℝ) * s n / 2 := fun n => by have := hspos n; positivity
  have hz'0 : ∀ n, z' n ≠ 0 := fun n h => by have := hz'im n; rw [h] at this; simp at this
  have hinv : ∀ n, -1 / z' n = ((1 / ((d : ℝ) * s n / 2) : ℝ) : ℂ) * τ n * I := fun n => by
    rw [div_eq_iff (hz'0 n), show ((1 / ((d : ℝ) * s n / 2) : ℝ) : ℂ) * τ n * I * z' n =
      ((1 / ((d : ℝ) * s n / 2) : ℝ) : ℂ) * I * (z' n * τ n) by ring, hzt n,
      show ((1 / ((d : ℝ) * s n / 2) : ℝ) : ℂ) * I * ((((d : ℝ) * s n / 2 : ℝ) : ℂ) * I) =
        ((1 / ((d : ℝ) * s n / 2) * ((d : ℝ) * s n / 2) : ℝ) : ℂ) * (I * I) by push_cast; ring,
      one_div_mul_cancel (hcpos n).ne', I_mul_I]
    simp
  have hR := cusp 2 two_pos (-(d : ℝ) / 2) (per_right d) (l := atTop) z' hz'im (by
    have : ∀ n : ℕ, (-1 / z' n).im = 4 * ((n : ℝ) + 1) / (d : ℝ) ^ 2 := fun n => by
      rw [hinv n, mul_I_im, re_ofReal_mul, hτre]
      simp only [hs]
      field_simp
      ring
    simp_rw [this]
    refine Tendsto.atTop_div_const (by positivity) ?_
    exact (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_mul_atTop
      (by norm_num))
  -- the functional equation joins the cusps
  have hfe : ∀ n, jacobiTheta (τ n) * (-I * τ n) ^ (1 / 2 : ℂ) = jacobiTheta (-1 / τ n) := by
    intro n
    have h1 : (-I * τ n) ^ (1 / 2 : ℂ) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff, not_and_or]
      exact Or.inl (mul_ne_zero (neg_ne_zero.2 I_ne_zero) (hτ0 n))
    rw [jacobiTheta_eq_jacobiTheta₂, jacobiTheta_eq_jacobiTheta₂,
      jacobiTheta₂_functional_equation 0 (τ n)]
    simp only [zero_pow two_ne_zero, mul_zero, zero_div, Complex.exp_zero, mul_one]
    rw [neg_mul] at h1
    field_simp
  set M : ℕ → ℂ := fun n => (Real.sqrt (d / 2) : ℂ) * (-I * τ n) ^ (1 / 2 : ℂ) *
    (τ n)⁻¹ ^ (1 / 2 : ℂ) with hM
  have hLR : ∀ n, (-I * z' n) ^ (1 / 2 : ℂ) * jacobiTheta (((-(d : ℝ) / 2 : ℝ) : ℂ) + z' n) =
      ((-I * z n) ^ (1 / 2 : ℂ) * jacobiTheta (((2 / d : ℝ) : ℂ) + z n)) * M n := by
    intro n
    have e1 : ((-(d : ℝ) / 2 : ℝ) : ℂ) + z' n = -1 / τ n := by
      simp only [hz']; push_cast; ring
    have e2 : -I * z n = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hz, hs]
    have e3 : -I * z' n = (((d : ℝ) / (2 * ((n : ℝ) + 1)) : ℝ) : ℂ) * (τ n)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ (hτ0 n), mul_assoc, hzt n]
      simp only [hs]
      push_cast
      field_simp
      ring_nf
      rw [I_sq]
      ring
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hpos2 : (0 : ℝ) < (d : ℝ) / (2 * ((n : ℝ) + 1)) := by positivity
    have hsq : Real.sqrt ((d : ℝ) / (2 * ((n : ℝ) + 1))) =
        Real.sqrt (d / 2) * Real.sqrt (1 / ((n : ℝ) + 1)) := by
      rw [← Real.sqrt_mul (by positivity)]; congr 1; field_simp
    rw [e1, e2, e3, cpow_real_mul hpos2 (inv_ne_zero (hτ0 n)), half_mul_half hpos.le,
      half_mul_half hpos2.le, hsq, ← hfe n, hM]
    simp only [hτ]
    push_cast
    ring
  have hMt : Tendsto M atTop (𝓝 ((Real.sqrt (d / 2) : ℂ) * (-I * ((2 / d : ℝ) : ℂ)) ^ (1 / 2 : ℂ) *
      (((2 / d : ℝ) : ℂ))⁻¹ ^ (1 / 2 : ℂ))) := by
    have hzt : Tendsto z atTop (𝓝 0) := by
      have := ((continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat).mul_const I
      simp only [ofReal_zero, zero_mul] at this
      exact this
    have hτt : Tendsto τ atTop (𝓝 ((2 / d : ℝ) : ℂ)) := by
      have := hzt.const_add ((2 / d : ℝ) : ℂ)
      simpa [hτ] using this
    have hs1 : -I * ((2 / d : ℝ) : ℂ) ∈ slitPlane := by
      rw [mem_slitPlane_iff]; right; simp; positivity
    have hs2 : (((2 / d : ℝ) : ℂ))⁻¹ ∈ slitPlane := by
      rw [mem_slitPlane_iff]; left
      rw [← ofReal_inv, ofReal_re]; positivity
    have h2d : ((2 / d : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (2 / d : ℝ) ≠ 0 by positivity)
    refine ((tendsto_const_nhds.mul ?_).mul ?_)
    · exact (continuousAt_cpow_const hs1).tendsto.comp (hτt.const_mul (-I))
    · exact (continuousAt_cpow_const hs2).tendsto.comp (hτt.inv₀ h2d)
  have hR' := (hL.mul hMt)
  rw [show (fun n => (-I * z n) ^ (1 / 2 : ℂ) * jacobiTheta (((2 / d : ℝ) : ℂ) + z n) * M n) =
      (fun n => (-I * z' n) ^ (1 / 2 : ℂ) * jacobiTheta (((-(d : ℝ) / 2 : ℝ) : ℂ) + z' n)) from
      funext fun n => (hLR n).symm] at hR'
  have heq := tendsto_nhds_unique hR' hR
  -- evaluate the constants
  have hS : ∑ r : Fin d, cexp (π * I * ((r : ℤ) : ℂ) ^ 2 * ((2 / d : ℝ) : ℂ)) =
      ∑ y ∈ Finset.range d, cexp (2 * π * I * (y : ℂ) ^ 2 / d) := by
    rw [Finset.sum_range (fun y => cexp (2 * π * I * (y : ℂ) ^ 2 / d))]
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 1; push_cast; field_simp
  have hS' : ∑ r : Fin 2, cexp (π * I * ((r : ℤ) : ℂ) ^ 2 * ((-(d : ℝ) / 2 : ℝ) : ℂ)) =
      1 + (-I) ^ d := by
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, Int.cast_zero, Int.cast_one,
      zero_pow two_ne_zero, mul_zero, zero_mul, Complex.exp_zero, one_pow, mul_one]
    congr 1
    rw [show (π : ℂ) * I * ((-(d : ℝ) / 2 : ℝ) : ℂ) = d * (-(π / 2) * I) by push_cast; ring,
      Complex.exp_nat_mul, ← log_neg_I, Complex.exp_log (neg_ne_zero.2 I_ne_zero)]
  rw [hS, hS'] at heq
  have hc1 : (-I * ((2 / d : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt (2 / d) : ℂ) * (-I) ^ (1 / 2 : ℂ) := by
    rw [mul_comm, cpow_real_mul (by positivity) (neg_ne_zero.2 I_ne_zero),
      half_mul_half (by positivity)]
  have hc2 : (((2 / d : ℝ) : ℂ))⁻¹ ^ (1 / 2 : ℂ) = (Real.sqrt (d / 2) : ℂ) := by
    rw [← ofReal_inv, half_mul_half (by positivity), inv_div]
  rw [hc1, hc2, neg_I_half] at heq
  have hsd : Real.sqrt (d / 2) * Real.sqrt (2 / d) = 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (d : ℝ) / 2 * (2 / d) = 1 by field_simp]; simp
  have hs2 : Real.sqrt 2 * Real.sqrt (d / 2) = Real.sqrt d := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; field_simp
  have hsdp : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 hdr
  have hsdc : (Real.sqrt d : ℂ) ≠ 0 := by exact_mod_cast hsdp.ne'
  have hsq2 : (Real.sqrt d : ℂ) ^ 2 = d := by
    rw [← ofReal_pow, Real.sq_sqrt hdr.le]; simp
  have hsdc' : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = d := by rw [← sq, hsq2]
  set G := ∑ y ∈ Finset.range d, cexp (2 * π * I * (y : ℂ) ^ 2 / d)
  have hA : (Real.sqrt (d / 2) : ℂ) * ((Real.sqrt (2 / d) : ℂ) * ((Real.sqrt 2 / 2 : ℝ) * (1 - I))) *
      (Real.sqrt (d / 2) : ℂ) = (Real.sqrt d / 2 : ℝ) * (1 - I) := by
    have e : (Real.sqrt (d / 2) : ℂ) * (Real.sqrt (2 / d) : ℂ) = 1 := by exact_mod_cast hsd
    have e' : (Real.sqrt 2 : ℂ) * (Real.sqrt (d / 2) : ℂ) = Real.sqrt d := by exact_mod_cast hs2
    push_cast
    linear_combination (Real.sqrt 2 / 2 * (1 - I) * Real.sqrt (d / 2) : ℂ) * e +
      ((1 - I) / 2 : ℂ) * e'
  rw [hA] at heq
  have hne : ((Real.sqrt d / 2 : ℝ) : ℂ) * (1 - I) ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast (show (Real.sqrt d / 2 : ℝ) ≠ 0 by positivity)) ?_
    intro h; have := congrArg Complex.im h; simp at this
  have hG : G = (1 + (-I) ^ d) / 2 * d / (((Real.sqrt d / 2 : ℝ) : ℂ) * (1 - I)) := by
    rw [eq_div_iff hne]
    calc G * (((Real.sqrt d / 2 : ℝ) : ℂ) * (1 - I)) =
        d * (G / d * (((Real.sqrt d / 2 : ℝ) : ℂ) * (1 - I))) := by field_simp
      _ = (1 + (-I) ^ d) / 2 * d := by rw [heq]; push_cast; ring
  rw [hG, div_eq_iff hne]
  push_cast
  linear_combination (-(1 + (-I) ^ d) / 2) * hsdc' +
    ((1 + (-I) ^ d) * (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) / 4) * I_sq

end DiracULA.Gauss
