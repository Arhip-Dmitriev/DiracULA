/-
Copyright 2026 Arkhip A. Dmitriev
Licensed under the Apache License, Version 2.0.
-/
import DiracULA.Lang
import DiracULA.Gauss

/-!
# Quadratic Gauss sums in symbolic sums

A term whose last sum `Σ_{y < D}` is read only by one root of unity `ω_D^(± y²)` is rewritten into
four terms by the quadratic Gauss sum: `Σ_{y < D} ω_D^(k y²) = √D/2 (1 + i^k)(1 + ω_4^(-k D))`,
`D` read through a new atom of the dimension's value.
-/

namespace DiracULA.LGauss

open DiracULA.Sym DiracULA.LSym DiracULA.Lang Complex Finset

theorem om_four : om 4 = I := by
  simp only [om]
  rw [show 2 * (Real.pi : ℂ) * I / ((4 : ℕ) : ℂ) = (Real.pi / 2 : ℂ) * I by push_cast; ring,
    Complex.exp_pi_div_two_mul_I]

theorem ex_neg_quarter : ex (-1 / 4) = -I := by
  simp only [ex]
  rw [show 2 * (Real.pi : ℂ) * I * ((-1 / 4 : ℝ) : ℂ) = -((Real.pi / 2 : ℂ) * I) by push_cast; ring,
    Complex.exp_neg, Complex.exp_pi_div_two_mul_I, inv_I]

theorem om_pow_sq (d : ℕ) (j : ℕ) :
    om d ^ ((j : ℤ) * j) = Complex.exp (2 * Real.pi * I * (j : ℂ) ^ 2 / d) := by
  simp only [om]
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem conj_om_pow_sq (d : ℕ) (j : ℕ) :
    om d ^ (-((j : ℤ) * j)) = starRingEnd ℂ (om d ^ ((j : ℤ) * j)) := by
  rw [zpow_neg, om_pow_sq, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
    Complex.conj_natCast]
  ring

/-- `Σ_{j < d} ω_d^(k j²) = √d/2 (1 + i^k)(1 + ω_4^(-k d))` for `k = ±1`. -/
theorem gauss_om (d : ℕ) (hd : 0 < d) (k : ℤ) (hk : k = 1 ∨ k = -1) :
    ∑ j ∈ range d, om d ^ (k * ((j : ℤ) * j)) =
      rt d / 2 * (1 + ex (((k : ℚ) / 4 : ℚ) : ℝ)) * (1 + om 4 ^ (-k * (d : ℤ))) := by
  have hg := DiracULA.Gauss.gauss_sum d hd
  rcases hk with rfl | rfl
  · simp only [one_mul, Int.cast_one, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, neg_mul,
      one_mul]
    rw [Finset.sum_congr rfl fun j _ => om_pow_sq d j, hg, show ((1 : ℝ) / 4) = 1 / 4 from rfl,
      ex_quarter, om_four, zpow_neg, zpow_natCast, ← inv_pow, inv_I]
    simp only [rt]
    ring
  · simp only [neg_mul, one_mul, Int.cast_neg, Int.cast_one, neg_neg, zpow_natCast]
    rw [Finset.sum_congr rfl fun j _ => conj_om_pow_sq d j, ← map_sum,
      Finset.sum_congr rfl fun j _ => om_pow_sq d j, hg, om_four]
    rw [show (((-1 : ℚ) / 4 : ℚ) : ℝ) = -1 / 4 by push_cast; ring, ex_neg_quarter]
    simp only [map_mul, map_div₀, map_add, map_one, Complex.conj_I, map_pow, map_neg,
      Complex.conj_ofReal, map_ofNat, rt]
    rw [show (-(-I) : ℂ) = I by ring]
    ring

/-- The exponent `k` of a root of unity `ω_D^(k y²)`, `k = ±1`. -/
def gaussK (y : ℕ) (D : DMon) (f : Fac) : Option ℤ :=
  if f.1 = D then
    (if f.2 = [([y, y], 1)] then some 1 else if f.2 = [([y, y], -1)] then some (-1) else none)
  else none

theorem gaussK_spec (y : ℕ) (D : DMon) (f : Fac) (k : ℤ) (h : gaussK y D f = some k) :
    f = (D, [([y, y], k)]) ∧ (k = 1 ∨ k = -1) := by
  unfold gaussK at h
  obtain ⟨D', p⟩ := f
  simp only at h
  split_ifs at h with h1 h2 h3 <;> simp only [Option.some.injEq] at h <;> subst h
  · subst h1; subst h2; exact ⟨rfl, Or.inl rfl⟩
  · subst h1; subst h3; exact ⟨rfl, Or.inr rfl⟩

/-- The four terms of the Gauss sum of `t`, its last sum `p` closed. -/
def gaussOut (t : ATm) (p : ℕ × DMon) (pre post : List Fac) (k : ℤ) : List ATm :=
  let a := maxV t + 1
  let c := t.c.mul ((CMon.rtD p.2 1).mul (CMon.ofQ (1 / 2)))
  let ats := t.ats ++ [⟨a, 8, [], [p.2], []⟩]
  let w : Fac := (⟨4, []⟩, [([a], -k)])
  [⟨c, t.sums.dropLast, ats, t.dels, pre ++ post, t.aps⟩,
    ⟨c.mul (CMon.exQ ((k : ℚ) / 4)), t.sums.dropLast, ats, t.dels, pre ++ post, t.aps⟩,
    ⟨c, t.sums.dropLast, ats, t.dels, pre ++ post ++ [w], t.aps⟩,
    ⟨c.mul (CMon.exQ ((k : ℚ) / 4)), t.sums.dropLast, ats, t.dels, pre ++ post ++ [w], t.aps⟩]

/-- `gaussOut` at a split of the roots of unity whose middle one is `ω_D^(± y²)`, `y` read by
nothing else. -/
def gaussAt (t : ATm) (p : ℕ × DMon) (pre : List Fac) (f : Fac) (post : List Fac) :
    Option (List ATm) :=
  match gaussK p.1 p.2 f with
  | none => none
  | some k =>
    if 0 < p.2.c ∧ p.1 ∉ (t.dels ++ pre ++ post).flatMap facVars ∧ p.1 ∉ argVs t.ats ∧
        p.1 ∉ ids t.ats ∧ p.1 ∉ t.aps.flatMap apVs then
      some (gaussOut t p pre post k)
    else none

/-- The Gauss sum of a term's last sum. -/
def gaussOne (t : ATm) : Option (List ATm) :=
  match t.sums.getLast? with
  | none => none
  | some p => firstSome (fun sp => gaussAt t p sp.1 sp.2.1 sp.2.2) (splits t.phs)

/-- Every term with its Gauss sum closed. -/
def gaussA (e : List ATm) : List ATm := e.flatMap fun t => (gaussOne t).getD [t]

theorem bodyOf_split (dv : ℕ → ℕ) (ds pre post : List Fac) (f : Fac) (ν : ℕ → ℤ) :
    bodyOf dv ds (pre ++ f :: post) ν = bodyOf dv ds (pre ++ post) ν * phV dv ν f := by
  simp only [bodyOf, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  ring

theorem bodyOf_snoc (dv : ℕ → ℕ) (ds ps : List Fac) (f : Fac) (ν : ℕ → ℤ) :
    bodyOf dv ds (ps ++ [f]) ν = bodyOf dv ds ps ν * phV dv ν f := by
  simp only [bodyOf, List.map_append, List.map_cons, List.map_nil, List.prod_append,
    List.prod_cons, List.prod_nil, mul_one]
  ring

theorem gaussOut_ok (V : LV) (hρ : V.ρ.OK) (t : ATm) (p : ℕ × DMon) (pre post : List Fac)
    (k : ℤ) (hk : k = 1 ∨ k = -1) (hs : t.sums.getLast? = some p)
    (hph : t.phs = pre ++ (p.2, [([p.1, p.1], k)]) :: post) (hc : 0 < p.2.c)
    (hy : p.1 ∉ (t.dels ++ pre ++ post).flatMap facVars) (ha : p.1 ∉ argVs t.ats)
    (hi : p.1 ∉ ids t.ats) (hp : p.1 ∉ t.aps.flatMap apVs) (ν : ℕ → ℤ) :
    axDen V ν (gaussOut t p pre post k) = t.den V ν := by
  set a := maxV t + 1 with ha_def
  have hfresh : ∀ v ∈ allV t, v ≠ a := fun v hv => by
    have := le_foldr_max _ v hv
    simp only [maxV] at ha_def
    omega
  set y := p.1
  set D := p.2 with hD
  have hsum : t.sums = t.sums.dropLast ++ [p] := by
    rw [List.dropLast_append_getLast? p hs]
  set A : (ℕ → ℤ) → ℂ := fun μ => bodyOf V.ρ.dv t.dels (pre ++ post) (aext V t.ats μ) *
    apsV V t.aps μ with hA
  set G := ∑ j ∈ range (D.den V.ρ.dv), om (D.den V.ρ.dv) ^ (k * ((j : ℤ) * j)) with hG
  -- the term's value
  have hL : t.den V ν = t.c.den V.ρ * (G * sumsV V.ρ.dv t.sums.dropLast A ν) := by
    unfold ATm.den
    conv_lhs => rw [hsum, sumsV_append]
    congr 1
    rw [← sumsV_mul_left]
    refine sumsV_congr _ _ _ _ (fun μ => ?_) ν
    simp only [sumsV]
    rw [hG, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold abody
    rw [aext_upd V t.ats y (by simp only [List.mem_append, not_or]; exact ⟨ha, hi⟩),
      apsV_upd V t.aps y hp, hph, bodyOf_split]
    have hb : bodyOf V.ρ.dv t.dels (pre ++ post) (Function.update (aext V t.ats μ) y j) =
        bodyOf V.ρ.dv t.dels (pre ++ post) (aext V t.ats μ) :=
      bodyOf_reads _ _ _ _ _ fun x hx => Function.update_of_ne (fun e => hy (by
        rw [← e]; simpa [List.flatMap_append, List.append_assoc] using hx)) _ _
    have hf : phV V.ρ.dv (Function.update (aext V t.ats μ) y j) (D, [([y, y], k)]) =
        om (D.den V.ρ.dv) ^ (k * ((j : ℤ) * j)) := by
      simp [phV, ipDen, imDen, Function.update_self]
    rw [hb, hf, hA]
    ring
  -- the four terms' values
  have hX : ∀ μ, aext V (t.ats ++ [⟨a, 8, [], [D], []⟩]) μ =
      Function.update (aext V t.ats μ) a (D.den V.ρ.dv) := by
    intro μ
    rw [aext_append]
    simp [aext, aval, bfn]
  have hB : ∀ μ, bodyOf V.ρ.dv t.dels (pre ++ post) (aext V (t.ats ++ [⟨a, 8, [], [D], []⟩]) μ) =
      bodyOf V.ρ.dv t.dels (pre ++ post) (aext V t.ats μ) := by
    intro μ
    rw [hX]
    refine bodyOf_reads _ _ _ _ _ fun x hx => Function.update_of_ne (hfresh x ?_) _ _
    obtain ⟨g, hg, hxg⟩ := List.mem_flatMap.1 hx
    have hg' : g ∈ t.dels ++ t.phs := by
      rw [hph]
      simp only [List.mem_append, List.mem_cons] at hg ⊢
      tauto
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (fvs_fac (List.mem_flatMap.2 ⟨g, hg', hxg⟩))))
  have hW : ∀ μ, phV V.ρ.dv (aext V (t.ats ++ [⟨a, 8, [], [D], []⟩]) μ) (⟨4, []⟩, [([a], -k)]) =
      om 4 ^ (-k * (D.den V.ρ.dv : ℤ)) := by
    intro μ
    rw [hX]
    simp [phV, ipDen, imDen, Function.update_self, DMon.den, npow]
  have hT1 : ∀ m : CMon, ATm.den V ν ⟨m, t.sums.dropLast, t.ats ++ [⟨a, 8, [], [D], []⟩],
      t.dels, pre ++ post, t.aps⟩ = m.den V.ρ * sumsV V.ρ.dv t.sums.dropLast A ν := by
    intro m
    unfold ATm.den abody
    congr 1
    refine sumsV_congr _ _ _ _ (fun μ => ?_) ν
    simp only
    rw [hB]
  have hT2 : ∀ m : CMon, ATm.den V ν ⟨m, t.sums.dropLast, t.ats ++ [⟨a, 8, [], [D], []⟩],
      t.dels, pre ++ post ++ [(⟨4, []⟩, [([a], -k)])], t.aps⟩ =
      m.den V.ρ * (om 4 ^ (-k * (D.den V.ρ.dv : ℤ)) * sumsV V.ρ.dv t.sums.dropLast A ν) := by
    intro m
    unfold ATm.den abody
    congr 1
    rw [← sumsV_mul_left]
    refine sumsV_congr _ _ _ _ (fun μ => ?_) ν
    simp only
    rw [bodyOf_snoc, hB, hW, hA]
    ring
  have hDc : 0 < D.den V.ρ.dv := DMon.den_pos _ hρ.dpos D hc
  have hgauss := gauss_om (D.den V.ρ.dv) hDc k hk
  unfold gaussOut
  simp only [axDen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [hT1, hT1, hT2, hT2, hL, hG, hgauss]
  simp only [CMon.den_mul V.ρ hρ, ofQ_den, exQ_den, ← hD]
  have hr : (CMon.rtD D 1).den V.ρ = rt (D.den V.ρ.dv) := by rw [rtD_den V.ρ D hc, zpow_one]
  rw [hr]
  push_cast
  ring

theorem gaussOne_ok (V : LV) (hρ : V.ρ.OK) (t : ATm) (out : List ATm) (h : gaussOne t = some out)
    (ν : ℕ → ℤ) : axDen V ν out = t.den V ν := by
  unfold gaussOne at h
  split at h
  · simp at h
  · next p hp =>
    obtain ⟨sp, hsp, he⟩ := firstSome_spec _ _ _ h
    have hspl := splits_spec _ _ hsp
    unfold gaussAt at he
    split at he
    · simp at he
    · next k hk =>
      split_ifs at he with hcond
      simp only [Option.some.injEq] at he
      subst he
      obtain ⟨hf, hk1⟩ := gaussK_spec _ _ _ _ hk
      obtain ⟨hc, hy, ha, hi, hap⟩ := hcond
      rw [hf] at hspl
      exact gaussOut_ok V hρ t p sp.1 sp.2.2 k hk1 hp hspl hc hy ha hi hap ν

theorem axDen_gaussA (V : LV) (hρ : V.ρ.OK) (e : List ATm) (ν : ℕ → ℤ) :
    axDen V ν (gaussA e) = axDen V ν e := by
  induction e with
  | nil => rfl
  | cons t e ih =>
    simp only [gaussA, List.flatMap_cons] at ih ⊢
    rw [axDen_append, ih, axDen_cons]
    congr 1
    cases hg : gaussOne t with
    | none => simp [axDen]
    | some out => simpa using gaussOne_ok V hρ t out hg ν

/-- `certify_lit_c` with the normal form of the difference closed by Gauss sums and normalised
again. -/
theorem certify_gauss_c (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (p : Prog) (r e : List ATm)
    (ns ns2 : List (Option ATm)) (he : p.sym fl PW = some e)
    (hn : (e ++ axNeg r).map (normA fl PW AROUNDS) = ns)
    (hn2 : (gaussA ((ns.filterMap id).foldl (fun acc t => taAdd t acc) [])).map
      (normA fl PW AROUNDS) = ns2)
    (hz : (ns2.filterMap id).foldl (fun acc t => taAdd t acc) [] = [])
    (hv : ∀ c ∈ p.counts, ∀ v ∈ ipVs c, 2 * IN ≤ v) :
    ∀ ν, (∀ c ∈ p.counts, 0 ≤ ipDen ν c) → p.sem V ν = axDen V ν r := by
  intro ν hc
  have h1 := nfA_den V hρ fl hfl PW hPW (e ++ axNeg r) ν
  rw [nfA_of_lit fl PW _ ns hn] at h1
  have hz' := nfA_zero V hρ fl hfl PW hPW _ (by rw [nfA_of_lit fl PW _ ns2 hn2, hz]) ν
  rw [axDen_gaussA V hρ, h1, axDen_append, axDen_neg] at hz'
  rw [Prog.sym_ok V hρ fl hfl PW hPW p e he ν (hi_of p hv ν hc)]
  linear_combination hz'

end DiracULA.LGauss
