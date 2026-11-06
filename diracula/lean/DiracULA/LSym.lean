/-
Copyright 2026 Arkhip A. Dmitriev
Licensed under the Apache License, Version 2.0.
-/
import DiracULA.SymCanon

/-!
# Symbolic sums with integer atoms

An `ATm` is a symbolic term (`STm`) with a table of integer atoms: each atom is a variable whose
value is a function of integer polynomials, every argument reduced modulo a dimension monomial.
The table is read in order, so an atom's arguments may name the atoms before it. Built-in atoms
(digit products, exclusive or, digit conditions, repunits, bits, digit sums) have fixed
meanings; the others are arbitrary functions supplied by the valuation.

The eliminations of `Sym` apply unchanged to a variable no atom reads. A delta pins a variable
an atom reads when every argument reading it is reduced modulo a divisor of the delta's
modulus; the pinned value is substituted into the atoms' arguments.
-/

namespace DiracULA.LSym

open DiracULA.Sym Complex Finset

/-- The first atom variable; index variables lie below it. -/
def ABASE : ℕ := 3000000

/-- An integer atom: its variable, function, integer and dimension parameters, and arguments,
each reduced modulo its monomial. -/
structure Atom where
  id : ℕ
  f : ℕ
  ks : List ℤ
  dp : List DMon
  args : List (IPoly × DMon)
  deriving Repr

/-- Equality of atoms, field by field. -/
def Atom.beq (a b : Atom) : Bool :=
  decide (a.id = b.id) && decide (a.f = b.f) && decide (a.ks = b.ks) && decide (a.dp = b.dp) &&
    decide (a.args = b.args)

theorem Atom.beq_iff (a b : Atom) : a.beq b = true ↔ a = b := by
  cases a; cases b; simp [Atom.beq, and_assoc]

instance : DecidableEq Atom := fun a b => decidable_of_iff _ (Atom.beq_iff a b)

/-- A valuation of dimension symbols, coefficient atoms and the functions of integer atoms. -/
structure LV where
  ρ : Val
  fa : ℕ → List ℤ → ℤ
  fc : ℕ → ℤ → ℂ

/-- Digit `i` of `x` in base `d`. -/
def dig (d i : ℕ) (x : ℤ) : ℤ := x / (d : ℤ) ^ i % d

/-- The digit positions of values below `N` in base `d`. -/
def pos (d N : ℕ) : Finset ℕ := (range N).filter fun i => d ^ i < N

/-- `Σ_k c_k g(x_k)`. -/
def lsum (ks : List ℤ) (xs : List ℤ) (g : ℤ → ℤ) : ℤ := (List.zipWith (fun c x => c * g x) ks xs).sum

/-- The built-in atoms: `0` digit product, `1` exclusive or, `2` the reduced argument, `3`
digit condition, `4` repunit, `5` bit, `6` digit sum, `7` power `d^x` (`d = 2` by default), `8`
a dimension's value, `9` digit `j` of `x`, `10` the low `j` digits of `x`, `11` the digits of
`x` from `j` on, `12` the quotient of two dimensions, `13` the remainder modulo a dimension
less one. -/
def bfn (f : ℕ) (ks : List ℤ) (dp : List ℕ) (xs : List ℤ) : ℤ :=
  let d := dp.getD 0 2
  let N := dp.getD 1 1
  match f with
  | 0 => ∑ i ∈ pos d N, dig d i (xs.getD 0 0) * dig d i (xs.getD 1 0)
  | 1 => ((xs.getD 0 0).toNat ^^^ (xs.getD 1 0).toNat : ℕ)
  | 2 => xs.getD 0 0
  | 3 => ∑ i ∈ pos d N,
      ((lsum ks xs (dig d i) + if i = 0 then xs.getD ks.length 0 else 0) % d) * (d : ℤ) ^ i
  | 4 => ((N - 1) / (d - 1) : ℕ)
  | 5 => xs.getD 0 0 / 2 ^ (xs.getD 1 0).toNat % 2
  | 6 => ∑ i ∈ pos d N, dig d i (xs.getD 0 0)
  | 7 => (d : ℤ) ^ (xs.getD 0 0).toNat
  | 8 => ((dp.getD 0 1 : ℕ) : ℤ)
  | 9 => dig d (xs.getD 1 0).toNat (xs.getD 0 0)
  | 10 => xs.getD 0 0 % (d : ℤ) ^ (xs.getD 1 0).toNat
  | 11 => xs.getD 0 0 / (d : ℤ) ^ (xs.getD 1 0).toNat
  | 12 => ((dp.getD 0 0 / dp.getD 1 1 : ℕ) : ℤ)
  | 13 => xs.getD 0 0 % ((dp.getD 0 1 : ℤ) - 1)
  | _ => 0

/-- An argument's value. -/
def argV (dv : ℕ → ℕ) (ν : ℕ → ℤ) (p : IPoly × DMon) : ℤ := ipDen ν p.1 % ((p.2.den dv : ℕ) : ℤ)

/-- An atom's value. -/
def aval (V : LV) (ν : ℕ → ℤ) (a : Atom) : ℤ :=
  if a.f < 100 then bfn a.f a.ks (a.dp.map (·.den V.ρ.dv)) (a.args.map (argV V.ρ.dv ν))
  else V.fa (a.f - 100) (a.args.map (argV V.ρ.dv ν))

/-- `ν` with every atom of the table set, in order. -/
def aext (V : LV) : List Atom → (ℕ → ℤ) → ℕ → ℤ
  | [], ν => ν
  | a :: l, ν => aext V l (Function.update ν a.id (aval V ν a))

/-- The variables of a polynomial. -/
def ipVs (p : IPoly) : List ℕ := p.flatMap (·.1)

/-- The variables an atom's arguments read. -/
def atVs (a : Atom) : List ℕ := a.args.flatMap fun p => ipVs p.1

/-- The variables a table's arguments read. -/
def argVs (l : List Atom) : List ℕ := l.flatMap atVs

/-- A table's atom variables. -/
def ids (l : List Atom) : List ℕ := l.map (·.id)

/-- A power `ρ.atom a ^ p` of a coefficient atom by a polynomial `p` read through its own atom
table `L`. -/
abbrev APw := ℕ × IPoly × List Atom

/-- A term with atoms and powers of coefficient atoms. -/
structure ATm where
  c : CMon
  sums : List (ℕ × DMon)
  ats : List Atom
  dels : List Fac
  phs : List Fac
  aps : List APw := []
  deriving Repr

/-- Equality of terms, field by field. -/
def ATm.beq (a b : ATm) : Bool :=
  decide (a.c = b.c) && decide (a.sums = b.sums) && decide (a.ats = b.ats) &&
    decide (a.dels = b.dels) && decide (a.phs = b.phs) && decide (a.aps = b.aps)

theorem ATm.beq_iff (a b : ATm) : a.beq b = true ↔ a = b := by
  cases a; cases b; simp [ATm.beq, and_assoc]

instance : DecidableEq ATm := fun a b => decidable_of_iff _ (ATm.beq_iff a b)

/-- The variables a power of a coefficient atom reads, its own atoms included. -/
def apVs (a : APw) : List ℕ := ipVs a.2.1 ++ argVs a.2.2 ++ ids a.2.2

/-- The variables a term's factors read. -/
def fvs (t : ATm) : List ℕ := (t.dels ++ t.phs).flatMap facVars ++ t.aps.flatMap apVs

theorem fvs_fac {t : ATm} {y : ℕ} (h : y ∈ (t.dels ++ t.phs).flatMap facVars) : y ∈ fvs t :=
  List.mem_append_left _ h

/-- Every variable a term's summand reads. -/
def rvs (t : ATm) : List ℕ := fvs t ++ argVs t.ats ++ ids t.ats

/-- The bound variables. -/
def abvs (t : ATm) : List ℕ := t.sums.map (·.1)

/-- Every variable a term names. -/
def allV (t : ATm) : List ℕ := rvs t ++ abvs t

/-- The first index of an opaque function of an index among powers. -/
def FB : ℕ := 1000000

/-- The first index of a built-in value among powers. -/
def GB : ℕ := 2000000

/-- The built-in values of a dimension `N ≥ 2`: `f = 0` is `u_N = e^(i asin(N^(-1/2))) =
(√(N - 1) + i)/√N`, `f = 1` is `q_N = 1/(u_N + u_N⁻¹) = √N/(2 √(N - 1))`; `1` for `N < 2`. -/
noncomputable def gfn (f N : ℕ) : ℂ :=
  if 2 ≤ N then
    (if f % 2 = 0 then ((Real.sqrt ((N : ℝ) - 1) : ℂ) + I) / (Real.sqrt N : ℂ)
     else (Real.sqrt N : ℂ) / (2 * (Real.sqrt ((N : ℝ) - 1) : ℂ)))
  else 1

/-- `ρ.atom k ^ z` below `FB`; from `FB` the opaque function `(k - FB) / 2` at `z`, conjugated for
odd `k - FB`; from `GB` the built-in value `(k - GB) / 2 % 2` of dimension `(k - GB) / 4` to the
power `z`, conjugated for odd `k - GB`. -/
@[irreducible] noncomputable def apF (V : LV) (k : ℕ) (z : ℤ) : ℂ :=
  if k < FB then V.ρ.atom k ^ z
  else if k < GB then
    (if (k - FB) % 2 = 0 then V.fc ((k - FB) / 2) z else starRingEnd ℂ (V.fc ((k - FB) / 2) z))
  else if (k - GB) % 2 = 0 then gfn ((k - GB) / 2 % 2) (V.ρ.dv ((k - GB) / 4)) ^ z
  else starRingEnd ℂ (gfn ((k - GB) / 2 % 2) (V.ρ.dv ((k - GB) / 4))) ^ z

/-- Whether powers of index `k` multiply by adding exponents. -/
def apMerge (k : ℕ) : Bool := decide (k < FB) || decide (GB ≤ k)

theorem gfn_ne (f N : ℕ) : gfn f N ≠ 0 := by
  unfold gfn
  split_ifs with h hf
  · have hN : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < N by omega))
    refine div_ne_zero ?_ (by exact_mod_cast hN.ne')
    intro h0
    have := congrArg Complex.im h0
    simp at this
  · have hN : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < N by omega))
    have hM : (0 : ℝ) < Real.sqrt ((N : ℝ) - 1) := Real.sqrt_pos.2 (by
      have : (2 : ℝ) ≤ N := by exact_mod_cast h
      linarith)
    exact div_ne_zero (by exact_mod_cast hN.ne') (mul_ne_zero two_ne_zero (by exact_mod_cast hM.ne'))
  · exact one_ne_zero

theorem gfn_vals (N : ℕ) (h : 2 ≤ N) :
    let s : ℂ := Real.sqrt N
    let m : ℂ := Real.sqrt ((N : ℝ) - 1)
    s ≠ 0 ∧ m ≠ 0 ∧ gfn 0 N = (m + I) / s ∧ (gfn 0 N)⁻¹ = (m - I) / s ∧ gfn 1 N = s / (2 * m) := by
  intro s m
  have hN : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < N by omega))
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast h
    linarith
  have hs : s ≠ 0 := by simp only [s]; exact_mod_cast hN.ne'
  have hm : m ≠ 0 := by simp only [m]; exact_mod_cast (Real.sqrt_pos.2 hN1).ne'
  have hs2 : s ^ 2 = N := by
    simp only [s]; rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N)]; simp
  have hm2 : m ^ 2 = N - 1 := by
    simp only [m]; rw [← Complex.ofReal_pow, Real.sq_sqrt hN1.le]; push_cast; ring
  have g0 : gfn 0 N = (m + I) / s := by simp [gfn, h, s, m]
  have g1 : gfn 1 N = s / (2 * m) := by simp [gfn, h, s, m]
  refine ⟨hs, hm, g0, ?_, g1⟩
  rw [g0]
  refine inv_eq_of_mul_eq_one_right ?_
  field_simp
  linear_combination hm2 - hs2 - I_sq

theorem gfn_rel1 (N : ℕ) (h : 2 ≤ N) :
    (Real.sqrt N : ℂ) * gfn 0 N - (Real.sqrt N : ℂ) * (gfn 0 N)⁻¹ - 2 * I = 0 := by
  obtain ⟨hs, hm, g0, gi, g1⟩ := gfn_vals N h
  rw [gi, g0]
  field_simp
  ring

theorem gfn_rel2 (N : ℕ) (h : 2 ≤ N) :
    gfn 1 N * gfn 0 N + gfn 1 N * (gfn 0 N)⁻¹ - 1 = 0 := by
  obtain ⟨hs, hm, g0, gi, g1⟩ := gfn_vals N h
  rw [gi, g0, g1]
  field_simp
  ring

/-- The base of a power that multiplies by adding exponents. -/
noncomputable def apB (V : LV) (k : ℕ) : ℂ :=
  if k < FB then V.ρ.atom k
  else if (k - GB) % 2 = 0 then gfn ((k - GB) / 2 % 2) (V.ρ.dv ((k - GB) / 4))
  else starRingEnd ℂ (gfn ((k - GB) / 2 % 2) (V.ρ.dv ((k - GB) / 4)))

theorem apF_B (V : LV) (k : ℕ) (hk : apMerge k = true) (z : ℤ) : apF V k z = apB V k ^ z := by
  have hF : FB = 1000000 := rfl
  have hG : GB = 2000000 := rfl
  simp only [apMerge, Bool.or_eq_true, decide_eq_true_eq] at hk
  unfold apF apB
  by_cases h1 : k < FB
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1, if_neg (by omega)]
    split_ifs <;> rfl

theorem apB_ne (V : LV) (hρ : V.ρ.OK) (k : ℕ) : apB V k ≠ 0 := by
  unfold apB
  split_ifs
  · exact hρ.anz k
  · exact gfn_ne _ _
  · exact (map_ne_zero _).2 (gfn_ne _ _)

theorem apF_zero (V : LV) (k : ℕ) (hk : apMerge k = true) : apF V k 0 = 1 := by
  rw [apF_B V k hk, zpow_zero]

theorem apF_add (V : LV) (hρ : V.ρ.OK) (k : ℕ) (hk : apMerge k = true) (a b : ℤ) :
    apF V k (a + b) = apF V k a * apF V k b := by
  rw [apF_B V k hk, apF_B V k hk, apF_B V k hk, zpow_add₀ (apB_ne V hρ k)]

/-- The value of powers of coefficient atoms and opaque functions. -/
noncomputable def apsV (V : LV) (l : List APw) (μ : ℕ → ℤ) : ℂ :=
  (l.map fun a => apF V a.1 (ipDen (aext V a.2.2 μ) a.2.1)).prod

/-- The summand. -/
noncomputable def abody (V : LV) (t : ATm) (μ : ℕ → ℤ) : ℂ :=
  bodyOf V.ρ.dv t.dels t.phs (aext V t.ats μ) * apsV V t.aps μ

/-- The value of a term. -/
noncomputable def ATm.den (V : LV) (ν : ℕ → ℤ) (t : ATm) : ℂ :=
  t.c.den V.ρ * sumsV V.ρ.dv t.sums (abody V t) ν

/-- The value of an expression. -/
noncomputable def axDen (V : LV) (ν : ℕ → ℤ) (e : List ATm) : ℂ := (e.map (ATm.den V ν)).sum

theorem axDen_nil (V : LV) (ν : ℕ → ℤ) : axDen V ν [] = 0 := rfl

theorem axDen_cons (V : LV) (ν : ℕ → ℤ) (t : ATm) (e : List ATm) :
    axDen V ν (t :: e) = t.den V ν + axDen V ν e := by simp [axDen]

theorem axDen_append (V : LV) (ν : ℕ → ℤ) (a b : List ATm) :
    axDen V ν (a ++ b) = axDen V ν a + axDen V ν b := by simp [axDen]

/-! ## Reading -/

theorem bodyOf_reads (dv : ℕ → ℕ) (ds ps : List Fac) (μ μ' : ℕ → ℤ)
    (h : ∀ x ∈ (ds ++ ps).flatMap facVars, μ x = μ' x) : bodyOf dv ds ps μ = bodyOf dv ds ps μ' :=
  body_reads dv ⟨CMon.ofQ 1, [], ds, ps⟩ μ μ' h

theorem aval_reads (V : LV) (a : Atom) (μ μ' : ℕ → ℤ) (h : ∀ x ∈ atVs a, μ x = μ' x) :
    aval V μ a = aval V μ' a := by
  have : a.args.map (argV V.ρ.dv μ) = a.args.map (argV V.ρ.dv μ') :=
    List.map_congr_left fun p hp => by
      unfold argV
      rw [ipDen_reads p.1 μ μ' fun x hx => h x (List.mem_flatMap.2 ⟨p, hp, hx⟩)]
  unfold aval; rw [this]

theorem aext_agree (V : LV) (l : List Atom) (S : List ℕ) (hS : ∀ x ∈ argVs l ++ ids l, x ∈ S)
    (μ μ' : ℕ → ℤ) (h : ∀ x ∈ S, μ x = μ' x) : ∀ x ∈ S, aext V l μ x = aext V l μ' x := by
  induction l generalizing μ μ' with
  | nil => exact h
  | cons a l ih =>
    simp only [aext]
    refine ih (fun x hx => hS x ?_) _ _ fun x hx => ?_
    · simp only [argVs, ids, List.flatMap_cons, List.map_cons, List.mem_append,
        List.mem_cons] at hx ⊢
      tauto
    · have hv : aval V μ a = aval V μ' a := aval_reads V a μ μ' fun y hy => h y (hS y (by
        simp only [argVs, List.flatMap_cons, List.mem_append]; tauto))
      by_cases e : x = a.id
      · subst e; simp [hv]
      · rw [Function.update_of_ne e, Function.update_of_ne e]; exact h x hx

theorem apsV_reads (V : LV) (l : List APw) (μ μ' : ℕ → ℤ)
    (h : ∀ x ∈ l.flatMap apVs, μ x = μ' x) : apsV V l μ = apsV V l μ' := by
  unfold apsV
  congr 1
  refine List.map_congr_left fun a ha => ?_
  have hS : ∀ x ∈ apVs a, μ x = μ' x := fun x hx => h x (List.mem_flatMap.2 ⟨a, ha, hx⟩)
  have he := aext_agree V a.2.2 (apVs a) (fun x hx => by
    simp only [apVs, List.mem_append] at hx ⊢; tauto) μ μ' hS
  rw [ipDen_reads a.2.1 _ _ fun y hy => he y (by
    simp only [apVs, List.mem_append]; exact Or.inl (Or.inl hy))]

theorem apsV_upd (V : LV) (l : List APw) (x : ℕ) (h : x ∉ l.flatMap apVs) (μ : ℕ → ℤ) (j : ℤ) :
    apsV V l (Function.update μ x j) = apsV V l μ :=
  apsV_reads V l _ _ fun y hy => by
    have hne : y ≠ x := fun e => h (by rw [← e]; exact hy)
    rw [Function.update_of_ne hne]

theorem apsV_append (V : LV) (a b : List APw) (μ : ℕ → ℤ) :
    apsV V (a ++ b) μ = apsV V a μ * apsV V b μ := by
  simp [apsV, List.map_append, List.prod_append]

theorem abody_reads (V : LV) (t : ATm) : RD (rvs t) (abody V t) := by
  intro μ μ' h
  unfold abody
  have := aext_agree V t.ats (rvs t) (fun x hx => by
    simp only [rvs, List.mem_append] at hx ⊢; tauto) μ μ' h
  rw [bodyOf_reads _ _ _ _ _ fun x hx => this x (by simp only [rvs, fvs, List.mem_append]; tauto),
    apsV_reads V t.aps _ _ fun x hx => h x (by simp only [rvs, fvs, List.mem_append]; tauto)]

theorem den_reads (V : LV) (t : ATm) (ν ν' : ℕ → ℤ) (h : ∀ x ∈ rvs t, ν x = ν' x) :
    t.den V ν = t.den V ν' := by
  unfold ATm.den; congr 1; exact sumsV_reads _ _ _ (abody_reads V t) _ _ _ h

/-- The variables an expression's summands read. -/
def axVs (e : List ATm) : List ℕ := e.flatMap rvs

theorem axDen_reads (V : LV) (e : List ATm) (ν ν' : ℕ → ℤ) (h : ∀ x ∈ axVs e, ν x = ν' x) :
    axDen V ν e = axDen V ν' e := by
  unfold axDen; congr 1
  exact List.map_congr_left fun t ht =>
    den_reads V t ν ν' fun x hx => h x (List.mem_flatMap.2 ⟨t, ht, hx⟩)

/-! ## Renaming -/

/-- Every variable of a monomial renamed by `m`. -/
def imRen (m : ℕ → ℕ) (mon : IMon) : IMon := mon.foldr (fun x a => imIns (m x) a) []

/-- Every variable of a polynomial renamed by `m`. -/
def ipRen (m : ℕ → ℕ) (p : IPoly) : IPoly :=
  p.foldr (fun t acc => ipIns (imRen m t.1) t.2 acc) []

theorem imDen_ren (ν : ℕ → ℤ) (m : ℕ → ℕ) (mon : IMon) :
    imDen ν (imRen m mon) = imDen (ν ∘ m) mon := by
  induction mon with
  | nil => simp [imRen, imDen]
  | cons x mon ih =>
    simp only [imRen, List.foldr_cons] at ih ⊢
    rw [imDen_ins, ih, imDen_cons]; rfl

theorem ipDen_ren (ν : ℕ → ℤ) (m : ℕ → ℕ) (p : IPoly) :
    ipDen ν (ipRen m p) = ipDen (ν ∘ m) p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [ipRen, List.foldr_cons] at ih ⊢
    rw [ipDen_ins, ih, imDen_ren, ipDen_cons]

/-- A factor renamed. -/
def facRen (m : ℕ → ℕ) (f : Fac) : Fac := (f.1, ipRen m f.2)

/-- An atom renamed. -/
def atRen (m : ℕ → ℕ) (a : Atom) : Atom :=
  { a with id := m a.id, args := a.args.map fun p => (ipRen m p.1, p.2) }

/-- Every variable of a term renamed, bound ones included. -/
def tRen (m : ℕ → ℕ) (t : ATm) : ATm :=
  ⟨t.c, t.sums.map (fun p => (m p.1, p.2)), t.ats.map (atRen m), t.dels.map (facRen m),
    t.phs.map (facRen m), t.aps.map fun a => (a.1, ipRen m a.2.1, a.2.2.map (atRen m))⟩

/-- `m` is injective on `S`. -/
def injOn (m : ℕ → ℕ) (S : List ℕ) : Bool := S.all fun a => S.all fun b => m a != m b || a == b

theorem injOn_spec (m : ℕ → ℕ) (S : List ℕ) (h : injOn m S = true) (a b : ℕ) (ha : a ∈ S)
    (hb : b ∈ S) (e : m a = m b) : a = b := by
  simp only [injOn, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  exact (h a ha b hb).resolve_left (fun h' => h' e)

theorem aval_ren (V : LV) (m : ℕ → ℕ) (a : Atom) (μ : ℕ → ℤ) :
    aval V μ (atRen m a) = aval V (μ ∘ m) a := by
  have : (atRen m a).args.map (argV V.ρ.dv μ) = a.args.map (argV V.ρ.dv (μ ∘ m)) := by
    simp only [atRen, List.map_map]
    exact List.map_congr_left fun p _ => by simp [argV, ipDen_ren]
  unfold aval; rw [this]; rfl

theorem aext_ren (V : LV) (m : ℕ → ℕ) (l : List Atom) (U : List ℕ) (hm : injOn m U = true)
    (hU : ∀ x ∈ argVs l ++ ids l, x ∈ U) (μ1 μ2 : ℕ → ℤ) (h : ∀ x ∈ U, μ1 (m x) = μ2 x) :
    ∀ x ∈ U, aext V (l.map (atRen m)) μ1 (m x) = aext V l μ2 x := by
  induction l generalizing μ1 μ2 with
  | nil => exact h
  | cons a l ih =>
    simp only [List.map_cons, aext]
    have haU : a.id ∈ U := hU _ (by simp [ids])
    refine ih (fun x hx => hU x ?_) _ _ fun x hx => ?_
    · simp only [argVs, ids, List.flatMap_cons, List.map_cons, List.mem_append,
        List.mem_cons] at hx ⊢
      tauto
    · have hv : aval V μ1 (atRen m a) = aval V μ2 a := by
        rw [aval_ren]
        exact aval_reads V a _ _ fun y hy => h y (hU y (by
          simp only [argVs, List.flatMap_cons, List.mem_append]; tauto))
      by_cases e : x = a.id
      · subst e; simp only [atRen, Function.update_self]; exact hv
      · have e' : m x ≠ (atRen m a).id := fun h' => e (injOn_spec m U hm x a.id hx haU h')
        rw [Function.update_of_ne e', Function.update_of_ne e]; exact h x hx

theorem tRen_den (V : LV) (m : ℕ → ℕ) (t : ATm) (hm : injOn m (allV t) = true) (ν : ℕ → ℤ) :
    (tRen m t).den V ν = t.den V (ν ∘ m) := by
  unfold ATm.den
  show t.c.den V.ρ * _ = _
  congr 1
  have hbody : ∀ μ1 μ2 : ℕ → ℤ, (∀ x ∈ allV t, μ1 (m x) = μ2 x) →
      abody V (tRen m t) μ1 = abody V t μ2 := by
    intro μ1 μ2 h
    have he := aext_ren V m t.ats (allV t) hm (fun x hx => by
      simp only [allV, rvs, List.mem_append] at hx ⊢; tauto) μ1 μ2 h
    unfold abody
    simp only [tRen]
    have hb := bodyOf_sub
    rw [show bodyOf V.ρ.dv (t.dels.map (facRen m)) (t.phs.map (facRen m))
        (aext V (t.ats.map (atRen m)) μ1) =
        bodyOf V.ρ.dv t.dels t.phs (aext V (t.ats.map (atRen m)) μ1 ∘ m) by
      simp only [bodyOf, List.map_map]
      congr 2 <;> exact List.map_congr_left fun f _ => by
        simp [delV, phV, facRen, ipDen_ren]]
    have hap : apsV V (t.aps.map fun a => (a.1, ipRen m a.2.1, a.2.2.map (atRen m))) μ1 =
        apsV V t.aps μ2 := by
      simp only [apsV, List.map_map]
      congr 1
      refine List.map_congr_left fun a ha => ?_
      have hin : ∀ x ∈ apVs a, x ∈ allV t := fun x hx => by
        simp only [allV, rvs, fvs, List.mem_append, List.mem_flatMap]
        exact Or.inl (Or.inl (Or.inl (Or.inr ⟨a, ha, hx⟩)))
      have hU : ∀ x ∈ argVs a.2.2 ++ ids a.2.2, x ∈ allV t := fun x hx => hin x (by
        simp only [apVs, List.mem_append] at hx ⊢; tauto)
      have he2 := aext_ren V m a.2.2 (allV t) hm hU μ1 μ2 h
      simp only [Function.comp_apply]
      rw [ipDen_ren]
      congr 1
      exact ipDen_reads _ _ _ fun y hy => he2 y (hin y (by
        simp only [apVs, List.mem_append]; exact Or.inl (Or.inl hy)))
    congr 1
    · exact bodyOf_reads _ _ _ _ _ fun x hx => he x (by
        simp only [allV, rvs, fvs, List.mem_append]; tauto)
  have key : ∀ (s : List (ℕ × DMon)), (∀ p ∈ s, p.1 ∈ allV t) → ∀ μ1 μ2 : ℕ → ℤ,
      (∀ x ∈ allV t, μ1 (m x) = μ2 x) →
      sumsV V.ρ.dv (s.map fun p => (m p.1, p.2)) (abody V (tRen m t)) μ1 =
        sumsV V.ρ.dv s (abody V t) μ2 := by
    intro s
    induction s with
    | nil => intro _ μ1 μ2 h; exact hbody μ1 μ2 h
    | cons p s ih =>
      intro hs μ1 μ2 h
      simp only [List.map_cons, sumsV]
      refine Finset.sum_congr rfl fun j _ => ih (fun q hq => hs q (List.mem_cons_of_mem _ hq))
        _ _ fun x hx => ?_
      have hp := hs p List.mem_cons_self
      by_cases e : x = p.1
      · subst e; simp
      · have e' : m x ≠ m p.1 := fun h' => e (injOn_spec m _ hm x p.1 hx hp h')
        rw [Function.update_of_ne e', Function.update_of_ne e]; exact h x hx
  exact key t.sums (fun p hp => by simp only [allV, abvs, List.mem_append, List.mem_map]; exact Or.inr ⟨p, hp, rfl⟩) ν (ν ∘ m) fun _ _ => rfl

/-! ## Products -/

/-- The product of two terms. -/
def tMul (s t : ATm) : ATm := ⟨CMon.mul s.c t.c, s.sums ++ t.sums, s.ats ++ t.ats,
  s.dels ++ t.dels, s.phs ++ t.phs, s.aps ++ t.aps⟩

/-- Neither term's bound or atom variables are read by the other. -/
def tMulOK (s t : ATm) : Bool :=
  (abvs s ++ ids s.ats).all (fun x => !(rvs t).contains x) &&
    (abvs t ++ ids t.ats).all (fun x => !(rvs s).contains x)

theorem aext_append (V : LV) (a b : List Atom) (μ : ℕ → ℤ) :
    aext V (a ++ b) μ = aext V b (aext V a μ) := by
  induction a generalizing μ with
  | nil => rfl
  | cons x a ih => simp only [List.cons_append, aext, ih]

/-- The atoms of `l` leave every variable outside their table. -/
theorem aext_off (V : LV) (l : List Atom) (μ : ℕ → ℤ) (x : ℕ) (hx : x ∉ ids l) :
    aext V l μ x = μ x := by
  induction l generalizing μ with
  | nil => rfl
  | cons a l ih =>
    simp only [ids, List.map_cons, List.mem_cons, not_or] at hx
    simp only [aext]; rw [ih _ hx.2, Function.update_of_ne hx.1]

theorem tMul_den (V : LV) (hρ : V.ρ.OK) (s t : ATm) (h : tMulOK s t = true) (ν : ℕ → ℤ) :
    (tMul s t).den V ν = s.den V ν * t.den V ν := by
  simp only [tMulOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not, List.mem_append] at h
  obtain ⟨h1, h2⟩ := h
  have hb : ∀ μ, abody V (tMul s t) μ = abody V s μ * abody V t μ := by
    intro μ
    unfold abody
    simp only [tMul, aext_append]
    rw [show ∀ E, bodyOf V.ρ.dv (s.dels ++ t.dels) (s.phs ++ t.phs) E =
        bodyOf V.ρ.dv s.dels s.phs E * bodyOf V.ρ.dv t.dels t.phs E from fun E => by
      simp only [bodyOf, List.map_append, List.prod_append]; ring]
    have e1 : bodyOf V.ρ.dv s.dels s.phs (aext V t.ats (aext V s.ats μ)) =
        bodyOf V.ρ.dv s.dels s.phs (aext V s.ats μ) :=
      bodyOf_reads _ _ _ _ _ fun x hx => aext_off V t.ats _ x fun hm =>
        h2 x (Or.inr hm) (by simp only [rvs, fvs, List.mem_append]; tauto)
    have e2 : bodyOf V.ρ.dv t.dels t.phs (aext V t.ats (aext V s.ats μ)) =
        bodyOf V.ρ.dv t.dels t.phs (aext V t.ats μ) := by
      refine bodyOf_reads _ _ _ _ _ fun x hx => ?_
      refine aext_agree V t.ats (rvs t) (fun y hy => by
        simp only [rvs, List.mem_append] at hy ⊢; tauto) _ _ (fun y hy =>
          aext_off V s.ats μ y fun hm => h1 y (Or.inr hm) hy) x
        (by simp only [rvs, fvs, List.mem_append]; tauto)
    rw [apsV_append, e1, e2]
    ring
  unfold ATm.den
  simp only [tMul, CMon.den_mul V.ρ hρ]
  rw [show abody V ⟨CMon.mul s.c t.c, s.sums ++ t.sums, s.ats ++ t.ats, s.dels ++ t.dels,
    s.phs ++ t.phs, s.aps ++ t.aps⟩ = abody V (tMul s t) from rfl, sumsV_congr _ _ _ _ hb,
    sumsV_append]
  have inner : ∀ ν', sumsV V.ρ.dv t.sums (fun μ => abody V s μ * abody V t μ) ν' =
      abody V s ν' * sumsV V.ρ.dv t.sums (abody V t) ν' := fun ν' =>
    sumsV_const_mul _ _ (rvs s) _ _ (abody_reads V s)
      (fun x hx hb' => h2 x (Or.inl (by simpa [abvs] using hb')) hx) ν'
  rw [sumsV_congr _ _ _ _ inner]
  rw [sumsV_congr _ _ _ (fun ν' => sumsV V.ρ.dv t.sums (abody V t) ν' * abody V s ν')
    (fun _ => mul_comm _ _)]
  rw [sumsV_const_mul _ _ (rvs t) _ _ (sumsV_reads _ _ _ (abody_reads V t) _)
    (fun x hx hb' => h1 x (Or.inl (by simpa [abvs] using hb')) hx) ν]
  ring

/-- The product of two expressions. -/
def axMul (a b : List ATm) : List ATm := a.flatMap fun s => b.map fun t => tMul s t

/-- Every pair of terms multiplies without capture. -/
def axMulOK (a b : List ATm) : Bool := a.all fun s => b.all fun t => tMulOK s t

theorem axDen_mul (V : LV) (hρ : V.ρ.OK) (a b : List ATm) (h : axMulOK a b = true)
    (ν : ℕ → ℤ) : axDen V ν (axMul a b) = axDen V ν a * axDen V ν b := by
  induction a with
  | nil => simp [axMul, axDen]
  | cons s a ih =>
    simp only [axMulOK, List.all_cons, Bool.and_eq_true] at h
    simp only [axMul, List.flatMap_cons] at ih ⊢
    rw [axDen_append, ih h.2, axDen_cons, add_mul]
    congr 1
    have hb := h.1
    clear ih h
    induction b with
    | nil => simp [axDen]
    | cons t b ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hb
      rw [List.map_cons, axDen_cons, axDen_cons, ih hb.2, tMul_den V hρ s t hb.1 ν]; ring

/-! ## Eliminating a variable no atom reads -/

theorem aext_upd (V : LV) (l : List Atom) (x : ℕ) (hx : x ∉ argVs l ++ ids l) (μ : ℕ → ℤ)
    (j : ℤ) : aext V l (Function.update μ x j) = Function.update (aext V l μ) x j := by
  induction l generalizing μ with
  | nil => rfl
  | cons a l ih =>
    simp only [argVs, ids, List.flatMap_cons, List.map_cons, List.mem_append, List.mem_cons,
      not_or] at hx
    simp only [aext]
    have hv : aval V (Function.update μ x j) a = aval V μ a :=
      aval_reads V a _ _ fun y hy =>
        Function.update_of_ne (fun e => hx.1.1 (by rw [← e]; exact hy)) _ _
    rw [hv, Function.update_comm hx.2.1, ih (by
      simp only [argVs, ids, List.mem_append]; tauto)]

/-! ## Eliminating a variable atoms read, pinned by a delta -/

/-- `x` substituted by `v` in an atom's arguments. -/
def atSub (x : ℕ) (v : IPoly) (a : Atom) : Atom :=
  { a with args := a.args.map fun p => (ipSubst x v p.1, p.2) }

/-- The arguments reading `x` are reduced modulo divisors of `M`. -/
def argsPer (x : ℕ) (M : DMon) (l : List Atom) : Bool :=
  l.all fun a => a.args.all fun p => !ipHas x p.1 || p.2.dvd M

theorem ipHas_false_of (x : ℕ) (p : IPoly) (h : x ∉ ipVs p) : ipHas x p = false := by
  simp only [ipHas, List.any_eq_false, Bool.not_eq_true]
  intro t ht
  simp only [List.contains_eq_mem, decide_eq_false_iff_not]
  intro hx; exact h (List.mem_flatMap.2 ⟨t, ht, hx⟩)

theorem argV_congr (dv : ℕ → ℕ) (hdv : ∀ i, 0 < dv i) (x : ℕ) (M : DMon) (p : IPoly × DMon)
    (hp : !ipHas x p.1 || p.2.dvd M) (ν : ℕ → ℤ) (a b : ℤ)
    (hab : ((M.den dv : ℕ) : ℤ) ∣ a - b) :
    argV dv (Function.update ν x a) p = argV dv (Function.update ν x b) p := by
  unfold argV
  by_cases hx : ipHas x p.1 = true
  · simp only [hx, Bool.not_true, Bool.false_or] at hp
    have h1 := (Int.natCast_dvd_natCast.2 (DMon.dvd_den dv _ _ hp)).trans
      (hab.trans (ipDen_upd_dvd ν x a b p.1))
    exact (Int.modEq_iff_dvd.2 h1).symm
  · simp only [Bool.not_eq_true] at hx
    rw [ipDen_upd_of _ _ _ _ hx, ipDen_upd_of _ _ _ _ hx]

theorem aext_congr (V : LV) (hρ : V.ρ.OK) (x : ℕ) (M : DMon) (l : List Atom)
    (hl : argsPer x M l = true) (hx : x ∉ ids l) (μ : ℕ → ℤ) (a b : ℤ)
    (hab : ((M.den V.ρ.dv : ℕ) : ℤ) ∣ a - b) :
    aext V l (Function.update μ x a) =
      Function.update (aext V l (Function.update μ x b)) x a := by
  induction l generalizing μ with
  | nil => simp [aext]
  | cons t l ih =>
    simp only [argsPer, List.all_cons, Bool.and_eq_true] at hl
    simp only [ids, List.map_cons, List.mem_cons, not_or] at hx
    simp only [aext]
    have hv : aval V (Function.update μ x a) t = aval V (Function.update μ x b) t := by
      have : t.args.map (argV V.ρ.dv (Function.update μ x a)) =
          t.args.map (argV V.ρ.dv (Function.update μ x b)) :=
        List.map_congr_left fun p hp => argV_congr _ hρ.dpos x M p
          (by simpa using (List.all_eq_true.1 hl.1) p hp) μ a b hab
      unfold aval; rw [this]
    rw [hv, Function.update_comm hx.1, Function.update_comm hx.1 b _ μ]
    exact ih hl.2 hx.2 _

/-- The plain variables of a polynomial: none is an atom. -/
def plainP (l : List Atom) (p : IPoly) : Bool := (ipVs p).all fun y => !(ids l).contains y

theorem ipDen_aext (V : LV) (l : List Atom) (p : IPoly) (hp : plainP l p = true) (μ : ℕ → ℤ) :
    ipDen (aext V l μ) p = ipDen μ p := by
  refine ipDen_reads p _ _ fun y hy => aext_off V l μ y ?_
  simp only [plainP, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hp
  exact hp y hy

theorem aext_sub (V : LV) (l : List Atom) (x : ℕ) (hx : x ∉ ids l) (v : IPoly)
    (hv : plainP l v = true) (hvx : ipHas x v = false) (μ : ℕ → ℤ) :
    aext V l (Function.update μ x (ipDen μ v)) =
      Function.update (aext V (l.map (atSub x v)) μ) x (ipDen μ v) := by
  induction l generalizing μ with
  | nil => simp [aext]
  | cons t l ih =>
    simp only [ids, List.map_cons, List.mem_cons, not_or] at hx
    simp only [plainP, ids, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hv
    have hv' : plainP l v = true := by
      simp only [plainP, ids, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not]
      exact fun y hy h' => hv y hy (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ h')
    have ht : t.id ∉ ipVs v := fun hy => hv _ hy (by simp)
    simp only [aext, List.map_cons]
    have hval : aval V (Function.update μ x (ipDen μ v)) t = aval V μ (atSub x v t) := by
      have : (atSub x v t).args.map (argV V.ρ.dv μ) =
          t.args.map (argV V.ρ.dv (Function.update μ x (ipDen μ v))) := by
        simp only [atSub, List.map_map]
        exact List.map_congr_left fun p _ => by simp [argV, ipDen_subst]
      unfold aval; rw [this]; rfl
    have hden : ipDen (Function.update μ t.id (aval V μ (atSub x v t))) v = ipDen μ v :=
      ipDen_upd_of _ _ _ _ (ipHas_false_of _ _ ht)
    rw [hval, Function.update_comm hx.1, ← hden, ih hx.2 hv']; rfl

/-- The coefficient, factors and atoms an elimination leaves. -/
structure AElim where
  k : CMon
  ats : List Atom
  ds : List Fac
  ps : List Fac

/-- Summing `x` over `D` out of the atoms and factors gives `e`. -/
def AElimOK (V : LV) (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac) (e : AElim) : Prop :=
  ∀ ν, ∑ j ∈ range (D.den V.ρ.dv), bodyOf V.ρ.dv ds ps (aext V ats (Function.update ν x j)) =
    e.k.den V.ρ * bodyOf V.ρ.dv e.ds e.ps (aext V e.ats ν)

/-- An elimination of `Sym`, when no atom reads `x`. -/
def elimPlain (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac) : Option AElim :=
  if (argVs ats ++ ids ats).contains x then none else
    match elimVar x D ds ps with
    | some e => some ⟨e.k, ats, e.ds, e.ps⟩
    | none => none

theorem elimPlain_ok (V : LV) (hρ : V.ρ.OK) (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac)
    (e : AElim) (h : elimPlain x D ats ds ps = some e) : AElimOK V x D ats ds ps e := by
  unfold elimPlain at h
  split_ifs at h with hx
  split at h
  · next e' he =>
    simp only [Option.some.injEq] at h
    subst h
    intro ν
    have hx' : x ∉ argVs ats ++ ids ats := by simpa using hx
    simp only [aext_upd V ats x hx']
    exact elimVar_ok V.ρ hρ x D ds ps e' he _
  · simp at h

/-- `x` pinned by the delta `f = [M ∣ s x + b]`, `s = ±1`, `M ∣ D`, `b` free of atoms, every
other factor and atom argument reading `x` periodic modulo `M`. -/
def elimPin1 (x : ℕ) (D : DMon) (ats : List Atom) (pre : List Fac) (f : Fac) (post ps : List Fac) :
    Option AElim :=
  match ipLin x f.2 with
  | some (a, b) =>
    match ipConst a with
    | some s =>
      if (s == 1 || s == -1) && D.c != 0 && f.1.dvd D && !(ids ats).contains x &&
          plainP ats b && argsPer x f.1 ats &&
          (pre ++ post ++ ps).all (fun g => !facHas x g || g.1.dvd f.1) then
        some ⟨CMon.rtD (D.div f.1) 2, ats.map (atSub x (pinVal s b)),
          (pre ++ post).map (facSub x (pinVal s b)), ps.map (facSub x (pinVal s b))⟩
      else none
    | none => none
  | none => none

theorem plainP_smul (l : List Atom) (k : ℤ) (b : IPoly) (h : plainP l b = true) :
    plainP l (ipSmul k b) = true := by
  simp only [plainP, List.all_eq_true] at h ⊢
  intro y hy
  apply h
  unfold ipSmul at hy
  split_ifs at hy
  · simp [ipVs] at hy
  · simp only [ipVs, List.mem_flatMap, List.mem_map] at hy ⊢
    obtain ⟨_, ⟨t, ht, rfl⟩, hy⟩ := hy
    exact ⟨t, ht, hy⟩

theorem ipHas_smul (x : ℕ) (k : ℤ) (b : IPoly) (h : ipHas x b = false) :
    ipHas x (ipSmul k b) = false := by
  unfold ipSmul; split_ifs
  · rfl
  · simpa [ipHas] using h

theorem elimPin1_ok (V : LV) (hρ : V.ρ.OK) (x : ℕ) (D : DMon) (ats : List Atom) (pre : List Fac)
    (f : Fac) (post ps : List Fac) (e : AElim) (h : elimPin1 x D ats pre f post ps = some e) :
    AElimOK V x D ats (pre ++ f :: post) ps e := by
  unfold elimPin1 at h
  split at h
  · next a b hlin =>
    split at h
    · next s hs =>
      split_ifs at h with hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
        Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
        List.all_eq_true] at hc
      obtain ⟨⟨⟨⟨⟨⟨hs1, hD⟩, hdvd⟩, hxid⟩, hbp⟩, hper⟩, hfac⟩ := hc
      obtain ⟨ha, hb, hp⟩ := ipLin_spec x f.2 a b hlin
      have hsv : ∀ ν, ipDen ν a = s := fun ν => ipConst_spec a s hs ν
      have hMpos : 0 < f.1.den V.ρ.dv := by
        unfold DMon.dvd at hdvd
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hdvd
        exact DMon.den_pos _ hρ.dpos _ (Nat.pos_of_ne_zero hdvd.1.1)
      have hdD := DMon.den_div V.ρ.dv _ _ hdvd
      have hvp : plainP ats (pinVal s b) = true := plainP_smul _ _ _ hbp
      have hvx : ipHas x (pinVal s b) = false := ipHas_smul _ _ _ hb
      intro ν
      set v := ipDen ν (pinVal s b)
      have hv : v = -s * ipDen ν b := by simp [v, pinVal, ipDen_smul]
      set g : ℤ → ℂ := fun j => bodyOf V.ρ.dv (pre ++ post) ps (aext V ats (Function.update ν x j))
      have hsplit : ∀ j : ℤ, bodyOf V.ρ.dv (pre ++ f :: post) ps
          (aext V ats (Function.update ν x j)) =
          (if ((f.1.den V.ρ.dv : ℕ) : ℤ) ∣ j - v then g j else 0) := by
        intro j
        have hd : delV V.ρ.dv (aext V ats (Function.update ν x j)) f =
            if ((f.1.den V.ρ.dv : ℕ) : ℤ) ∣ j - v then 1 else 0 := by
          unfold delV
          rw [hp, hsv, ipDen_aext V ats b hbp, ipDen_upd_of _ _ _ _ hb,
            aext_off V ats _ x hxid, Function.update_self, hv]
          simp only [pin_dvd s hs1]
        simp only [g, bodyOf, List.map_append, List.map_cons, List.prod_append, List.prod_cons,
          hd]
        split_ifs <;> ring
      have hper' : ∀ c d : ℤ, ((f.1.den V.ρ.dv : ℕ) : ℤ) ∣ c - d → g c = g d := by
        intro c d hcd
        simp only [g]
        rw [aext_congr V hρ x f.1 ats hper hxid ν c d hcd]
        have hE : aext V ats (Function.update ν x d) =
            Function.update (aext V ats (Function.update ν x d)) x d := by
          conv_lhs => rw [← Function.update_eq_self x (aext V ats (Function.update ν x d))]
          rw [aext_off V ats _ x hxid, Function.update_self]
        conv_rhs => rw [hE]
        simp only [bodyOf]
        congr 1
        · congr 1; refine List.map_congr_left fun g' hg' => ?_
          by_cases hx : facHas x g' = true
          · have := hfac g' (by simp only [List.mem_append] at hg' ⊢; tauto)
            rw [hx] at this
            exact (fac_congr V.ρ.dv hρ.dpos x f.1 g' (by simpa using this) _ c d hcd).1
          · simp only [Bool.not_eq_true] at hx
            unfold delV; rw [ipDen_upd_of _ _ _ _ hx, ipDen_upd_of _ _ _ _ hx]
        · congr 1; refine List.map_congr_left fun g' hg' => ?_
          by_cases hx : facHas x g' = true
          · have := hfac g' (by simp only [List.mem_append]; tauto)
            rw [hx] at this
            exact (fac_congr V.ρ.dv hρ.dpos x f.1 g' (by simpa using this) _ c d hcd).2
          · simp only [Bool.not_eq_true] at hx
            unfold phV; rw [ipDen_upd_of _ _ _ _ hx, ipDen_upd_of _ _ _ _ hx]
      rw [Finset.sum_congr rfl fun (j : ℕ) _ => hsplit (j : ℤ),
        sum_delta_periodic _ _ hMpos ⟨_, hdD⟩ v g hper']
      have hq : D.den V.ρ.dv / f.1.den V.ρ.dv = (D.div f.1).den V.ρ.dv := by
        rw [hdD, Nat.mul_div_cancel_left _ hMpos]
      have hqc : 0 < (D.div f.1).c := by
        have hpos := DMon.den_pos V.ρ.dv hρ.dpos D (Nat.pos_of_ne_zero hD)
        rw [hdD] at hpos
        have := Nat.pos_of_mul_pos_left hpos
        by_contra hz
        simp only [not_lt, Nat.le_zero] at hz
        simp [DMon.den, hz] at this
      rw [hq, rtD_two V.ρ _ hqc]
      congr 1
      simp only [g, v]
      rw [aext_sub V ats x hxid _ hvp hvx ν, bodyOf_sub, ipDen_aext V _ _ (by
        simpa [plainP, ids, atSub] using hvp)]
    · simp at h
  · simp at h

/-- `x` pinned by the first delta that pins it. -/
def elimPin (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac) : Option AElim :=
  firstSome (fun p => elimPin1 x D ats p.1 p.2.1 p.2.2 ps) (splits ds)

theorem elimPin_ok (V : LV) (hρ : V.ρ.OK) (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac)
    (e : AElim) (h : elimPin x D ats ds ps = some e) : AElimOK V x D ats ds ps e := by
  obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h
  rw [splits_spec ds p hp]
  exact elimPin1_ok V hρ x D ats _ _ _ _ e he

/-- `a.2` added to the exponent of the power of index `a.1` without atoms of its own, in a list
whose such powers are sorted by index. -/
def apIns (a : ℕ × IPoly) : List APw → List APw
  | [] => if ipAdd [] a.2 = [] then [] else [(a.1, ipAdd [] a.2, [])]
  | b :: l =>
    if b.2.2 = [] ∧ b.1 = a.1 ∧ apMerge a.1 = true then
      (if ipAdd b.2.1 a.2 = [] then l else (b.1, ipAdd b.2.1 a.2, []) :: l)
    else if b.2.2 = [] ∧ apMerge b.1 = true ∧ a.1 < b.1 then
      (if ipAdd [] a.2 = [] then b :: l else (a.1, ipAdd [] a.2, []) :: b :: l)
    else b :: apIns a l

theorem ipDen_add0 (μ : ℕ → ℤ) (p : IPoly) : ipDen μ (ipAdd [] p) = ipDen μ p := by
  rw [ipDen_add, ipDen_nil, zero_add]

theorem apsV_apIns (V : LV) (hρ : V.ρ.OK) (a : ℕ × IPoly) (ha : apMerge a.1 = true)
    (l : List APw) (μ : ℕ → ℤ) : apsV V (apIns a l) μ = apF V a.1 (ipDen μ a.2) * apsV V l μ := by
  induction l with
  | nil =>
    simp only [apIns]
    split_ifs with h
    · have h0 : ipDen μ a.2 = 0 := by rw [← ipDen_add0, h, ipDen_nil]
      rw [h0, apF_zero V a.1 ha]; simp [apsV]
    · simp [apsV, aext, ipDen_add0]
  | cons b l ih =>
    simp only [apIns]
    split_ifs with h1 h2 h3 h4
    · obtain ⟨hb, hk, -⟩ := h1
      have h0 : ipDen μ b.2.1 + ipDen μ a.2 = 0 := by rw [← ipDen_add, h2, ipDen_nil]
      simp only [apsV, List.map_cons, List.prod_cons, hb, aext]
      rw [hk, ← mul_assoc, ← apF_add V hρ a.1 ha, add_comm, h0, apF_zero V a.1 ha, one_mul]
    · obtain ⟨hb, hk, -⟩ := h1
      simp only [apsV, List.map_cons, List.prod_cons, hb, aext]
      rw [ipDen_add, hk, apF_add V hρ a.1 ha]; ring
    · have h0 : ipDen μ a.2 = 0 := by rw [← ipDen_add0, h4, ipDen_nil]
      rw [h0, apF_zero V a.1 ha, one_mul]
    · simp only [apsV, List.map_cons, List.prod_cons, aext, ipDen_add0]
    · simp only [apsV, List.map_cons, List.prod_cons] at ih ⊢
      rw [ih]; ring

/-- Every power without atoms of its own merged into the powers of its index by `apIns`. -/
def apsCanon (l : List APw) : List APw :=
  l.foldr (fun a acc => if a.2.2 = [] ∧ apMerge a.1 = true then apIns (a.1, a.2.1) acc else a :: acc) []

theorem apsV_canon (V : LV) (hρ : V.ρ.OK) (l : List APw) (μ : ℕ → ℤ) :
    apsV V (apsCanon l) μ = apsV V l μ := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [apsCanon, List.foldr_cons] at ih ⊢
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      rw [apsV_apIns V hρ (a.1, a.2.1) h2, ih]
      obtain ⟨k, p, tb⟩ := a
      simp only at h1 ⊢
      subst h1
      simp [apsV, aext]
    · simp only [apsV, List.map_cons, List.prod_cons] at ih ⊢
      rw [ih]

end DiracULA.LSym
