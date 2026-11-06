/-
Copyright 2026 Arkhip A. Dmitriev
Licensed under the Apache License, Version 2.0.
-/
import DiracULA.LTable

/-!
# The normaliser of symbolic sums with atoms

`normA` alternates eliminations of bound variables (`elimPlain`, `elimPin`, `elimDigit`) with
canonicalisation: atom rules (zero digit products, digit conditions read as deltas, unused
atoms), the factor canonicalisation of `Sym`, renaming of bound and atom variables by first
occurrence and sorting of the sums and the table. `nfA` normalises every term of an expression
and merges terms of equal shape; `nfA_den` proves it keeps the value.
-/

namespace DiracULA.LSym

open DiracULA.Sym Complex Finset

/-- `t'` has the value of `t`, or `t` vanishes. -/
def ARes (V : LV) (t : ATm) : Option ATm → Prop
  | none => ∀ ν, t.den V ν = 0
  | some t' => ∀ ν, t'.den V ν = t.den V ν

theorem den_of_pw (V : LV) (t t' : ATm) (hs : t'.sums = t.sums)
    (h : ∀ μ, t'.c.den V.ρ * abody V t' μ = t.c.den V.ρ * abody V t μ) (ν : ℕ → ℤ) :
    t'.den V ν = t.den V ν := by
  unfold ATm.den
  rw [hs, ← sumsV_mul_left, ← sumsV_mul_left]
  exact sumsV_congr _ _ _ _ h ν

theorem den_zero_of_pw (V : LV) (t : ATm) (h : ∀ μ, abody V t μ = 0) (ν : ℕ → ℤ) :
    t.den V ν = 0 := by
  unfold ATm.den
  rw [sumsV_congr _ _ _ (fun _ => 0) h, sumsV_zero, mul_zero]

/-! ## Eliminations -/

/-- `x` summed over one value, read as `0`. -/
def elimOne (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac) : Option AElim :=
  if D.isConst && D.c == 1 && !(ids ats).contains x then
    some ⟨CMon.ofQ 1, ats.map (atSub x (ipC 0)), ds.map (facSub x (ipC 0)),
      ps.map (facSub x (ipC 0))⟩
  else none

theorem elimOne_ok (V : LV) (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac) (e : AElim)
    (h : elimOne x D ats ds ps = some e) : AElimOK V x D ats ds ps e := by
  unfold elimOne at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hc
  obtain ⟨⟨hD, hc1⟩, hx⟩ := hc
  intro ν
  have hden : D.den V.ρ.dv = 1 := by rw [DMon.den_isConst _ _ hD, hc1]
  rw [hden, Finset.sum_range_one, ofQ_den, Rat.cast_one, one_mul, bodyOf_sub, ipDen_C]
  have hpl : plainP ats (ipC 0) = true := by
    unfold plainP ipVs ipC ipIns; split_ifs <;> simp
  have hhs : ipHas x (ipC 0) = false := by
    unfold ipHas ipC ipIns; split_ifs <;> simp
  have e := aext_sub V ats x hx (ipC 0) hpl hhs ν
  rw [ipDen_C] at e
  rw [← e]
  rfl

/-! ## Pins to reduced atoms -/

theorem ids_atSub (l : List Atom) (x : ℕ) (v : IPoly) : ids (l.map (atSub x v)) = ids l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, ids] at ih ⊢; simp [atSub, ih]

/-- `x` pinned by `f = [D ∣ s x + b]`, `s = ±1`, `b` reading no atom, to the new atom
`u = mod(-s b, D)`, whatever else reads `x`. -/
def elimPinU1 (PW : List (DMon × DMon)) (x : ℕ) (D : DMon) (ats : List Atom) (pre : List Fac)
    (f : Fac) (post ps : List Fac) (u : ℕ) : Option AElim :=
  match ipLin x f.2 with
  | some (a, b) =>
    match ipConst a with
    | some s =>
      if (s == 1 || s == -1) && D.c != 0 && decide (f.1 = D) && !(ids ats).contains x &&
          plainP ats b && !(ids ats).contains u && !(argVs ats).contains u &&
          !((pre ++ post ++ ps).flatMap facVars).contains u && !(ipVs b).contains u &&
          decide (u ≠ x) && ps.all (fun g => !facHas x g || g.1.dvd f.1) &&
          (pre ++ post).all (fun g => !facHas x g || g.1.dvd f.1 || PW.contains (f.1, g.1)) then
        some ⟨CMon.ofQ 1, ⟨u, 2, [], [], [(pinVal s b, D)]⟩ :: ats.map (atSub x (ipV u)),
          (pre ++ post).map (facSub x (ipV u)), ps.map (facSub x (ipV u))⟩
      else none
    | none => none
  | none => none

/-- A variable greater than every variable the atoms and factors name. -/
def freshU (x : ℕ) (ats : List Atom) (ds ps : List Fac) : ℕ :=
  (x :: ids ats ++ argVs ats ++ (ds ++ ps).flatMap facVars).foldr max 0 + 1

/-- `x` pinned to a new reduced atom by the first delta of its range that pins it. -/
def elimPinU (PW : List (DMon × DMon)) (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac) :
    Option AElim :=
  firstSome (fun p => elimPinU1 PW x D ats p.1 p.2.1 p.2.2 ps (freshU x ats ds ps)) (splits ds)

theorem ipHas_of_facVars (u : ℕ) (g : Fac) (h : u ∉ facVars g) : ipHas u g.2 = false := by
  simp only [ipHas, List.any_eq_false, List.contains_eq_mem, decide_eq_true_eq]
  intro t ht hu
  exact h (by simp only [facVars, List.mem_flatMap]; exact ⟨t, ht, hu⟩)

theorem bodyOf_upd_free (dv : ℕ → ℕ) (ds ps : List Fac) (u : ℕ)
    (h : ∀ g ∈ ds ++ ps, ipHas u g.2 = false) (μ : ℕ → ℤ) (w : ℤ) :
    bodyOf dv ds ps (Function.update μ u w) = bodyOf dv ds ps μ := by
  simp only [bodyOf]
  congr 1
  · congr 1; refine List.map_congr_left fun g hg => ?_
    unfold delV; rw [ipDen_upd_of _ _ _ _ (h g (List.mem_append_left _ hg))]
  · congr 1; refine List.map_congr_left fun g hg => ?_
    unfold phV; rw [ipDen_upd_of _ _ _ _ (h g (List.mem_append_right _ hg))]

theorem elimPinU1_ok (V : LV) (hρ : V.ρ.OK) (PW : List (DMon × DMon)) (x : ℕ) (D : DMon)
    (ats : List Atom) (pre : List Fac) (f : Fac) (post ps : List Fac) (u : ℕ) (e : AElim)
    (h : elimPinU1 PW x D ats pre f post ps u = some e) : AElimOK V x D ats (pre ++ f :: post) ps e := by
  unfold elimPinU1 at h
  split at h
  · next a b hlin =>
    split at h
    · next s hs =>
      split_ifs at h with hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
        Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs1, hD⟩, hf⟩, hxid⟩, hbp⟩, huid⟩, huarg⟩, hufac⟩, hub⟩, hux⟩, -⟩, -⟩ := hc
      obtain ⟨-, hb, hp⟩ := ipLin_spec x f.2 a b hlin
      have hsv : ∀ ν, ipDen ν a = s := fun ν => ipConst_spec a s hs ν
      have hDpos : 0 < D.den V.ρ.dv := DMon.den_pos _ hρ.dpos _ (Nat.pos_of_ne_zero hD)
      intro ν
      set v : ℤ := -s * ipDen ν b
      set g : ℤ → ℂ := fun j => bodyOf V.ρ.dv (pre ++ post) ps (aext V ats (Function.update ν x j))
      have hsplit : ∀ j : ℤ, bodyOf V.ρ.dv (pre ++ f :: post) ps (aext V ats (Function.update ν x j)) =
          (if ((D.den V.ρ.dv : ℕ) : ℤ) ∣ j - v then g j else 0) := by
        intro j
        have hd : delV V.ρ.dv (aext V ats (Function.update ν x j)) f =
            if ((D.den V.ρ.dv : ℕ) : ℤ) ∣ j - v then 1 else 0 := by
          unfold delV
          rw [hp, hsv, ipDen_aext V ats b hbp, ipDen_upd_of _ _ _ _ hb, aext_off V ats _ x hxid,
            Function.update_self, hf]
          simp only [pin_dvd s hs1, v]
        simp only [g, bodyOf, List.map_append, List.map_cons, List.prod_append, List.prod_cons, hd]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl fun (j : ℕ) _ => hsplit (j : ℤ), sum_pin_exact _ hDpos v g,
        ofQ_den, Rat.cast_one, one_mul]
      -- the right side
      set w : ℤ := v % ((D.den V.ρ.dv : ℕ) : ℤ)
      have haval : aval V ν ⟨u, 2, [], [], [(pinVal s b, D)]⟩ = w := by
        simp only [aval, show (2 : ℕ) < 100 by norm_num, if_true, bfn, List.map_cons, List.map_nil,
          argV, List.getD_cons_zero, pinVal, ipDen_smul, w, v]
      simp only [aext]
      rw [haval]
      set μ := Function.update ν u w
      have hidu : u ∉ ids (ats.map (atSub x (ipV u))) := by rw [ids_atSub]; exact huid
      have hμu : μ u = w := by simp [μ]
      rw [bodyOf_sub, ipDen_V, aext_off V _ _ u hidu, hμu]
      have hvp : plainP ats (ipV u) = true := by simp [plainP, ipVs, ipV, huid]
      have hvx : ipHas x (ipV u) = false := by simp [ipHas, ipV]; exact Ne.symm hux
      have e2 := aext_sub V ats x hxid (ipV u) hvp hvx μ
      rw [ipDen_V, hμu] at e2
      rw [← e2]
      simp only [g, μ]
      have hfree : ∀ g' ∈ (pre ++ post) ++ ps, ipHas u g'.2 = false := by
        intro g' hg'
        apply ipHas_of_facVars
        intro hm
        apply hufac
        simp only [List.mem_flatMap]
        exact ⟨g', by simpa using hg', hm⟩
      have hnu : u ∉ argVs ats ++ ids ats := by
        simp only [List.mem_append, not_or]; exact ⟨huarg, huid⟩
      rw [Function.update_comm hux, aext_upd V ats u hnu _ w, bodyOf_upd_free _ _ _ u hfree]
    · simp at h
  · simp at h

theorem elimPinU_ok (V : LV) (hρ : V.ρ.OK) (PW : List (DMon × DMon)) (x : ℕ) (D : DMon)
    (ats : List Atom) (ds ps : List Fac) (e : AElim) (h : elimPinU PW x D ats ds ps = some e) :
    AElimOK V x D ats ds ps e := by
  obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h
  rw [splits_spec ds p hp]
  exact elimPinU1_ok V hρ PW x D ats _ _ _ _ _ e he

/-- The first elimination of `x` that applies. -/
def aElimVar (PW : List (DMon × DMon)) (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac) :
    Option AElim :=
  match elimPlain x D ats ds ps with
  | some e => some e
  | none =>
    match elimPin x D ats ds ps with
    | some e => some e
    | none =>
      match elimDigit PW x D ats ds ps with
      | some e => some e
      | none =>
        match elimPinC x D ats ds ps with
        | some e => some e
        | none =>
          match elimPinA x D ats ds ps with
          | some e => some e
          | none =>
            match elimLinC PW x D ats ds ps with
            | some e => some e
            | none =>
              match elimPinR x D ats ds ps with
              | some e => some e
              | none => elimOne x D ats ds ps

theorem aElimVar_ok (V : LV) (hρ : V.ρ.OK) (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ)
    (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac) (e : AElim)
    (h : aElimVar PW x D ats ds ps = some e) : AElimOK V x D ats ds ps e := by
  unfold aElimVar at h
  split at h
  · next e' he => simp only [Option.some.injEq] at h; subst h; exact elimPlain_ok V hρ _ _ _ _ _ _ he
  · split at h
    · next e' he => simp only [Option.some.injEq] at h; subst h; exact elimPin_ok V hρ _ _ _ _ _ _ he
    · split at h
      · next e' he =>
        simp only [Option.some.injEq] at h; subst h; exact elimDigit_ok V hρ PW hPW _ _ _ _ _ _ he
      · split at h
        · next e' he =>
          simp only [Option.some.injEq] at h; subst h; exact elimPinC_ok V _ _ _ _ _ _ he
        · split at h
          · next e' he =>
            simp only [Option.some.injEq] at h; subst h; exact elimPinA_ok V hρ _ _ _ _ _ _ he
          · split at h
            · next e' he =>
              simp only [Option.some.injEq] at h; subst h; exact elimLinC_ok V hρ PW hPW _ _ _ _ _ _ he
            · split at h
              · next e' he =>
                simp only [Option.some.injEq] at h; subst h; exact elimPinR_ok V x D ats ds ps e' he
              · exact elimOne_ok V x D ats ds ps e h

/-- One elimination of a bound variable, the first that applies. -/
def aElimStep (PW : List (DMon × DMon)) (t : ATm) : Option ATm :=
  firstSome (fun p => if ((p.1 ++ p.2.2).map (·.1) |>.contains p.2.1.1) ||
      (t.aps.flatMap apVs).contains p.2.1.1 then none else
    match aElimVar PW p.2.1.1 p.2.1.2 t.ats t.dels t.phs with
    | some e => some ⟨CMon.mul t.c e.k, p.1 ++ p.2.2, e.ats, e.ds, e.ps, t.aps⟩
    | none => none) (splits t.sums)

theorem aElimStep_ok (V : LV) (hρ : V.ρ.OK) (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ)
    (t t' : ATm) (h : aElimStep PW t = some t') (ν : ℕ → ℤ) : t'.den V ν = t.den V ν := by
  obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h
  obtain ⟨a, ⟨x, D⟩, b⟩ := p
  simp only at he
  split_ifs at he with hx
  split at he
  · next e hev =>
    simp only [Option.some.injEq] at he
    subst he
    have hok := aElimVar_ok V hρ PW hPW x D t.ats t.dels t.phs e hev
    have hs := splits_spec t.sums _ hp
    simp only at hs
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, List.contains_eq_mem,
      decide_eq_false_iff_not] at hx
    unfold ATm.den
    rw [hs, sumsV_pull _ a b x D (by simpa using hx.1)]
    show (CMon.mul t.c e.k).den V.ρ * sumsV V.ρ.dv (a ++ b)
        (fun μ => bodyOf V.ρ.dv e.ds e.ps (aext V e.ats μ) * apsV V t.aps μ) ν =
      t.c.den V.ρ * sumsV V.ρ.dv (a ++ b) (fun ν' => ∑ j ∈ range (D.den V.ρ.dv),
        bodyOf V.ρ.dv t.dels t.phs (aext V t.ats (Function.update ν' x j)) *
          apsV V t.aps (Function.update ν' x j)) ν
    have hc : ∀ ν', (∑ j ∈ range (D.den V.ρ.dv),
        bodyOf V.ρ.dv t.dels t.phs (aext V t.ats (Function.update ν' x j)) *
          apsV V t.aps (Function.update ν' x j)) =
        e.k.den V.ρ * (bodyOf V.ρ.dv e.ds e.ps (aext V e.ats ν') * apsV V t.aps ν') := by
      intro ν'
      simp only [apsV_upd V t.aps x hx.2]
      rw [← Finset.sum_mul, hok ν']
      ring
    rw [sumsV_congr _ _ _ _ hc, sumsV_mul_left, CMon.den_mul V.ρ hρ]
    ring
  · simp at he


/-- One pin of a bound variable to a new reduced atom, the first that applies. -/
def aElimStepU (PW : List (DMon × DMon)) (t : ATm) : Option ATm :=
  firstSome (fun p => if ((p.1 ++ p.2.2).map (·.1) |>.contains p.2.1.1) ||
      (t.aps.flatMap apVs).contains p.2.1.1 then none else
    match elimPinU PW p.2.1.1 p.2.1.2 t.ats t.dels t.phs with
    | some e => some ⟨CMon.mul t.c e.k, p.1 ++ p.2.2, e.ats, e.ds, e.ps, t.aps⟩
    | none => none) (splits t.sums)

theorem aElimStepU_ok (V : LV) (hρ : V.ρ.OK) (PW : List (DMon × DMon)) (t t' : ATm)
    (h : aElimStepU PW t = some t')
    (ν : ℕ → ℤ) : t'.den V ν = t.den V ν := by
  obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h
  obtain ⟨a, ⟨x, D⟩, b⟩ := p
  simp only at he
  split_ifs at he with hx
  split at he
  · next e hev =>
    simp only [Option.some.injEq] at he
    subst he
    have hok := elimPinU_ok V hρ PW x D t.ats t.dels t.phs e hev
    have hs := splits_spec t.sums _ hp
    simp only at hs
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, List.contains_eq_mem,
      decide_eq_false_iff_not] at hx
    unfold ATm.den
    rw [hs, sumsV_pull _ a b x D (by simpa using hx.1)]
    show (CMon.mul t.c e.k).den V.ρ * sumsV V.ρ.dv (a ++ b)
        (fun μ => bodyOf V.ρ.dv e.ds e.ps (aext V e.ats μ) * apsV V t.aps μ) ν =
      t.c.den V.ρ * sumsV V.ρ.dv (a ++ b) (fun ν' => ∑ j ∈ range (D.den V.ρ.dv),
        bodyOf V.ρ.dv t.dels t.phs (aext V t.ats (Function.update ν' x j)) *
          apsV V t.aps (Function.update ν' x j)) ν
    have hc : ∀ ν', (∑ j ∈ range (D.den V.ρ.dv),
        bodyOf V.ρ.dv t.dels t.phs (aext V t.ats (Function.update ν' x j)) *
          apsV V t.aps (Function.update ν' x j)) =
        e.k.den V.ρ * (bodyOf V.ρ.dv e.ds e.ps (aext V e.ats ν') * apsV V t.aps ν') := by
      intro ν'
      simp only [apsV_upd V t.aps x hx.2]
      rw [← Finset.sum_mul, hok ν']
      ring
    rw [sumsV_congr _ _ _ _ hc, sumsV_mul_left, CMon.den_mul V.ρ hρ]
    ring
  · simp at he

/-! ## Factors -/

/-- The factor canonicalisation of `Sym`: the coefficient gained and the factors, or `none`
when they vanish. -/
def canonF (fl : List ℕ) (ds ps : List Fac) : Option (CMon × List Fac × List Fac) :=
  let pp := pivPass ds.length [] ds ps
  match normDels fl pp.1 with
  | none => none
  | some ds' =>
    let np := normPhs (phMerge pp.2)
    some (np.1, ds'.foldr delIns [], np.2.foldr facIns [])

theorem canonF_none (ρ : Val) (hρ : ρ.OK) (fl : List ℕ) (hfl : FloorOK fl ρ) (ds ps : List Fac)
    (h : canonF fl ds ps = none) (μ : ℕ → ℤ) : bodyOf ρ.dv ds ps μ = 0 := by
  unfold canonF at h
  simp only at h
  split at h
  · next hn =>
    have := normDels_ok ρ fl hfl (pivPass ds.length [] ds ps).1 μ
    rw [hn] at this
    rw [← show bodyOf ρ.dv (pivPass ds.length [] ds ps).1 (pivPass ds.length [] ds ps).2 μ =
      bodyOf ρ.dv ds ps μ from by rw [pivPass_ok ρ.dv hρ.dpos]; rfl]
    simp only [bodyOf]; rw [this, zero_mul]
  · simp at h

theorem canonF_some (ρ : Val) (hρ : ρ.OK) (fl : List ℕ) (hfl : FloorOK fl ρ) (ds ps : List Fac)
    (k : CMon) (ds' ps' : List Fac) (h : canonF fl ds ps = some (k, ds', ps')) (μ : ℕ → ℤ) :
    k.den ρ * bodyOf ρ.dv ds' ps' μ = bodyOf ρ.dv ds ps μ := by
  unfold canonF at h
  simp only at h
  split at h
  · simp at h
  · next dsn hn =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hd := normDels_ok ρ fl hfl (pivPass ds.length [] ds ps).1 μ
    rw [hn] at hd
    rw [← show bodyOf ρ.dv (pivPass ds.length [] ds ps).1 (pivPass ds.length [] ds ps).2 μ =
      bodyOf ρ.dv ds ps μ from by rw [pivPass_ok ρ.dv hρ.dpos]; rfl]
    simp only [bodyOf, delSort_ok, facSort_ok]
    simp only [DelsRes] at hd
    rw [hd, ← phMerge_ok ρ.dv μ (pivPass ds.length [] ds ps).2,
      normPhs_ok ρ hρ (phMerge (pivPass ds.length [] ds ps).2) μ]
    ring

/-! ## Digits of equal values -/

theorem nat_digits_eq (d : ℕ) (hd : 0 < d) (n v w : ℕ) (hv : v < d ^ n) (hw : w < d ^ n) :
    (∀ i < n, v / d ^ i % d = w / d ^ i % d) ↔ v = w := by
  constructor
  · intro h
    induction n generalizing v w with
    | zero => simp at hv hw; omega
    | succ n ih =>
      have h0 := h 0 (by omega)
      simp only [pow_zero, Nat.div_one] at h0
      have hvd : v / d < d ^ n := by rw [Nat.div_lt_iff_lt_mul hd, ← pow_succ]; exact hv
      have hwd : w / d < d ^ n := by rw [Nat.div_lt_iff_lt_mul hd, ← pow_succ]; exact hw
      have e := ih (v / d) (w / d) hvd hwd fun i hi => by
        have := h (i + 1) (by omega)
        rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this
      rw [← Nat.mod_add_div v d, ← Nat.mod_add_div w d, h0, e]
  · rintro rfl _ _; rfl

theorem dig_lt (d i : ℕ) (hd : 0 < d) (a : ℤ) : 0 ≤ dig d i a ∧ dig d i a < d :=
  ⟨Int.emod_nonneg _ (by exact_mod_cast hd.ne'), Int.emod_lt_of_pos _ (by exact_mod_cast hd)⟩

/-- Two values reduced modulo `d^n` agree when every digit does. -/
theorem digits_eq_int (d n : ℕ) (hd : 0 < d) (a b : ℤ) :
    (∀ i < n, dig d i (a % ((d ^ n : ℕ) : ℤ)) = dig d i (b % ((d ^ n : ℕ) : ℤ))) ↔
      ((d ^ n : ℕ) : ℤ) ∣ a - b := by
  have hN : (0 : ℤ) < ((d ^ n : ℕ) : ℤ) := by positivity
  obtain ⟨v, hv⟩ : ∃ v : ℕ, a % ((d ^ n : ℕ) : ℤ) = v :=
    ⟨(a % ((d ^ n : ℕ) : ℤ)).toNat, (Int.toNat_of_nonneg (Int.emod_nonneg _ hN.ne')).symm⟩
  obtain ⟨w, hw⟩ : ∃ w : ℕ, b % ((d ^ n : ℕ) : ℤ) = w :=
    ⟨(b % ((d ^ n : ℕ) : ℤ)).toNat, (Int.toNat_of_nonneg (Int.emod_nonneg _ hN.ne')).symm⟩
  have hvl : v < d ^ n := by have := Int.emod_lt_of_pos a hN; omega
  have hwl : w < d ^ n := by have := Int.emod_lt_of_pos b hN; omega
  have e1 : (∀ i < n, dig d i (v : ℤ) = dig d i (w : ℤ)) ↔ v = w := by
    simp only [dig_nat, Nat.cast_inj]; exact nat_digits_eq d hd n v w hvl hwl
  rw [hv, hw, e1, ← Int.modEq_iff_dvd]
  unfold Int.ModEq
  rw [hv, hw]
  constructor <;> intro h <;> omega

theorem small_dvd (d u r : ℤ) (hu : 0 ≤ u ∧ u < d) (hr : 0 ≤ r ∧ r < d) (h : d ∣ u - r) :
    u = r := by
  obtain ⟨k, hk⟩ := h
  rcases lt_trichotomy k 0 with hk0 | rfl | hk0
  · nlinarith
  · simpa [sub_eq_zero] using hk
  · nlinarith

/-! ## Digit conditions read as deltas -/

/-- The digit `-c b` reduced: modulo `d` for a constant `d`. -/
def rOf (c b : ℤ) (d : DMon) : ℤ := if d.isConst then (-c * b) % (d.c : ℤ) else -c * b

/-- The polynomial `P` and modulus `N` of a digit condition with `[N ∣ z] = [N ∣ P]`. -/
def dzPoly (PW : List (DMon × DMon)) (ats : List Atom) (a : Atom) : Option (DMon × IPoly) :=
  if a.f = 3 then
    match a.dp, a.ks, a.args with
    | [d, N], [c], [(A, M1), (Bp, M2)] =>
      match ipConst Bp with
      | some b =>
        if (d, N) ∈ PW ∧ M1 = N ∧ M2 = d ∧ (c = 1 ∨ c = -1) ∧ 0 ≤ rOf c b d ∧
            (rOf c b d ≤ 1 ∨ d.isConst = true) ∧
            plainP ats A = true then some (N, ipSub A (ipC (rOf c b d)))
        else if (d, N) ∈ PW ∧ M1 = N ∧ M2 = d ∧ A = [] ∧ (b = 1 ∨ b = -1) then
          some (N, ipC 1)
        else none
      | none => none
    | [d, N], [c, c'], [(A1, M1), (A2, M2), (Bp, M3)] =>
      if (d, N) ∈ PW ∧ M1 = N ∧ M2 = N ∧ M3 = d ∧ (c = 1 ∨ c = -1) ∧
          (c' = -c ∨ (d.isConst = true ∧ (c + c') % (d.c : ℤ) = 0)) ∧
          ipConst Bp = some 0 ∧ plainP ats A1 = true ∧ plainP ats A2 = true then
        some (N, ipSub A1 A2) else none
    | _, _, _ => none
  else none

theorem dz_digit (d : ℕ) (hd : 2 ≤ d) (c u v : ℤ) (hc : c = 1 ∨ c = -1)
    (hu : 0 ≤ u ∧ u < d) (hv : 0 ≤ v ∧ v < d) (e : ℤ) (he : (d : ℤ) ∣ e + c * v) :
    (c * u + e) % d = 0 ↔ u = v := by
  rw [← Int.dvd_iff_emod_eq_zero]
  constructor
  · intro h
    have h2 : (d : ℤ) ∣ c * (u - v) := by
      have := dvd_sub h he
      rwa [show c * u + e - (e + c * v) = c * (u - v) by ring] at this
    have h3 : (d : ℤ) ∣ u - v := by
      rcases hc with rfl | rfl
      · simpa using h2
      · have : (d : ℤ) ∣ -(-1 * (u - v)) := dvd_neg.2 h2
        simpa using this
    exact small_dvd d u v hu hv h3
  · rintro rfl
    rwa [add_comm]

theorem dig_small (d i N : ℕ) (hd : 0 < d) (r : ℤ) (hr : 0 ≤ r ∧ r < d) (hN : d ≤ N) :
    dig d i (r % (N : ℤ)) = if i = 0 then r else 0 := by
  have e1 : r % (N : ℤ) = r := Int.emod_eq_of_lt hr.1 (by omega)
  rw [e1]
  unfold dig
  split_ifs with hi
  · subst hi; simp [Int.emod_eq_of_lt hr.1 hr.2]
  · have : (d : ℤ) ≤ (d : ℤ) ^ i := by
      have := Nat.le_self_pow hi d
      exact_mod_cast this
    rw [Int.ediv_eq_zero_of_lt hr.1 (by omega)]; simp

theorem bfn3_one (c b' : ℤ) (dd N : ℕ) (aN : ℤ) :
    bfn 3 [c] [dd, N] [aN, b'] =
      ∑ i ∈ pos dd N, ((c * dig dd i aN + if i = 0 then b' else 0) % dd) * (dd : ℤ) ^ i := by
  simp [bfn, lsum]

theorem bfn3_two (c c' b' : ℤ) (dd N : ℕ) (a1 a2 : ℤ) :
    bfn 3 [c, c'] [dd, N] [a1, a2, b'] = ∑ i ∈ pos dd N,
      ((c * dig dd i a1 + (c' * dig dd i a2 + if i = 0 then b' else 0)) % dd) * (dd : ℤ) ^ i := by
  simp only [bfn, lsum, List.zipWith_cons_cons, List.sum_cons, List.getD_cons_zero,
    List.getD_cons_succ, List.length_cons, List.length_nil, List.zipWith_nil_left, List.sum_nil]
  refine Finset.sum_congr rfl fun i _ => by congr 2; ring

/-- The digit conditions, digit by digit. -/
theorem dz_core (dd n : ℕ) (hd2 : 2 ≤ dd) (u v e : ℕ → ℤ) (c : ℤ) (hc : c = 1 ∨ c = -1)
    (hu : ∀ i, 0 ≤ u i ∧ u i < dd) (hv : ∀ i, 0 ≤ v i ∧ v i < dd)
    (he : ∀ i < n, (dd : ℤ) ∣ e i + c * v i) :
    (∀ i ∈ range n, (c * u i + e i) % dd = 0) ↔ (∀ i < n, u i = v i) := by
  constructor
  · intro h i hi
    exact (dz_digit dd hd2 c (u i) (v i) hc (hu i) (hv i) (e i) (he i hi)).1
      (h i (Finset.mem_range.2 hi))
  · intro h i hi
    have hi' := Finset.mem_range.1 hi
    exact (dz_digit dd hd2 c (u i) (v i) hc (hu i) (hv i) (e i) (he i hi')).2 (h i hi')

theorem dzPoly_ok (V : LV) (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (ats : List Atom)
    (a : Atom) (N : DMon) (P : IPoly) (h : dzPoly PW ats a = some (N, P)) (μ : ℕ → ℤ) :
    (((N.den V.ρ.dv : ℕ) : ℤ) ∣ aval V μ a) ↔ (((N.den V.ρ.dv : ℕ) : ℤ) ∣ ipDen μ P) := by
  unfold dzPoly at h
  split_ifs at h with hf
  split at h
  · next d N' c A M1 Bp M2 hdp hks hargs =>
    split at h
    · next b hb =>
      split_ifs at h with hc hc'
      swap
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        subst N; subst P
        obtain ⟨hpw, h3, h4, hA, hb1⟩ := hc'
        subst M1; subst M2; subst A
        obtain ⟨hd2, n, hNn⟩ := hPW _ hpw
        have hd2' : 2 ≤ d.den V.ρ.dv := hd2
        have hNn' : N'.den V.ρ.dv = d.den V.ρ.dv ^ n := hNn
        have hdd : 0 < d.den V.ρ.dv := by omega
        simp only [aval, hf, show (3 : ℕ) < 100 by norm_num, if_true, hdp, hks, hargs,
          List.map_cons, List.map_nil, argV, ipConst_spec Bp b hb, ipDen_C, ipDen_nil]
        rw [bfn3_one, hNn', pos_pow _ _ hd2', digits_zero _ n hdd _ fun i => ⟨Int.emod_nonneg _
          (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩]
        have hbd : ¬ (b % (d.den V.ρ.dv : ℤ)) % (d.den V.ρ.dv : ℤ) = 0 := by
          rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
          intro h0
          have := Int.dvd_of_emod_eq_zero h0
          rcases hb1 with rfl | rfl
          · have := Int.le_of_dvd (by norm_num) this; omega
          · have := Int.le_of_dvd (by norm_num) (dvd_neg.2 this); omega
        constructor
        · intro h
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · simp
          · exfalso
            have := h 0 (Finset.mem_range.2 hn)
            simp only [dig, Int.zero_emod, Int.zero_ediv, mul_zero, zero_add, ite_true] at this
            exact hbd this
        · intro h i hi
          have hn : n = 0 := by
            by_contra hn
            have h1 : (1 : ℤ) < ((d.den V.ρ.dv ^ n : ℕ) : ℤ) := by
              have : 1 < d.den V.ρ.dv ^ n := Nat.one_lt_pow hn (by omega)
              exact_mod_cast this
            have := Int.le_of_dvd (by norm_num) h
            omega
          subst hn; simp at hi
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        subst N; subst P
        obtain ⟨hpw, h3, h4, hc1, hr0, hr1, -⟩ := hc
        subst M1; subst M2
        obtain ⟨hd2, n, hNn⟩ := hPW _ hpw
        have hd2' : 2 ≤ d.den V.ρ.dv := hd2
        have hNn' : N'.den V.ρ.dv = d.den V.ρ.dv ^ n := hNn
        have hdd : 0 < d.den V.ρ.dv := by omega
        simp only [aval, hf, show (3 : ℕ) < 100 by norm_num, if_true, hdp, hks, hargs,
          List.map_cons, List.map_nil, argV, ipConst_spec Bp b hb, ipDen_sub, ipDen_C]
        rw [bfn3_one, hNn', pos_pow _ _ hd2', digits_zero _ n hdd _ fun i => ⟨Int.emod_nonneg _
          (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩, ← digits_eq_int _ n hdd]
        refine dz_core _ n hd2' _ _ _ c hc1 (fun i => dig_lt _ i hdd _) (fun i => dig_lt _ i hdd _)
          fun i hi => ?_
        have hn : d.den V.ρ.dv ≤ d.den V.ρ.dv ^ n := Nat.le_self_pow (by omega) _
        have hrl : rOf c b d < (d.den V.ρ.dv : ℤ) := by
          rcases hr1 with hr1 | hr1
          · omega
          · unfold rOf; rw [if_pos hr1, ← DMon.den_isConst V.ρ.dv d hr1]
            exact Int.emod_lt_of_pos _ (by omega)
        rw [dig_small _ i _ hdd (rOf c b d) ⟨hr0, hrl⟩ (by exact_mod_cast hn)]
        split_ifs
        · rw [Int.emod_def]
          unfold rOf
          split_ifs with hk
          · rw [← DMon.den_isConst V.ρ.dv d hk, Int.emod_def]
            rcases hc1 with rfl | rfl
            · exact ⟨-(b / (d.den V.ρ.dv : ℤ)) - (-1 * b / (d.den V.ρ.dv : ℤ)), by ring⟩
            · exact ⟨-(b / (d.den V.ρ.dv : ℤ)) + (-(-1) * b / (d.den V.ρ.dv : ℤ)), by ring⟩
          · rcases hc1 with rfl | rfl
            · exact ⟨-(b / (d.den V.ρ.dv : ℤ)), by ring⟩
            · exact ⟨-(b / (d.den V.ρ.dv : ℤ)), by ring⟩
        · simp
    · simp at h
  · next d N' c c' A1 M1 A2 M2 Bp M3 hdp hks hargs =>
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst N; subst P
    obtain ⟨hpw, h3, h4, h5, hc1, h6, hb, -, -⟩ := hc
    subst M1; subst M2; subst M3
    obtain ⟨hd2, n, hNn⟩ := hPW _ hpw
    have hd2' : 2 ≤ d.den V.ρ.dv := hd2
    have hNn' : N'.den V.ρ.dv = d.den V.ρ.dv ^ n := hNn
    have hdd : 0 < d.den V.ρ.dv := by omega
    simp only [aval, hf, show (3 : ℕ) < 100 by norm_num, if_true, hdp, hks, hargs,
      List.map_cons, List.map_nil, argV, ipConst_spec Bp 0 hb, ipDen_sub, Int.zero_emod]
    rw [bfn3_two, hNn', pos_pow _ _ hd2', digits_zero _ n hdd _ fun i => ⟨Int.emod_nonneg _
      (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩, ← digits_eq_int _ n hdd]
    refine dz_core _ n hd2' _ _ _ c hc1 (fun i => dig_lt _ i hdd _) (fun i => dig_lt _ i hdd _)
      fun i hi => ?_
    simp only [ite_self, add_zero]
    rcases h6 with h6 | ⟨hk, hm⟩
    · subst h6; exact ⟨0, by ring⟩
    · have hdiv : ((d.den V.ρ.dv : ℕ) : ℤ) ∣ c + c' := by
        rw [DMon.den_isConst _ _ hk]; exact Int.dvd_of_emod_eq_zero hm
      rw [show ∀ X : ℤ, c' * X + c * X = (c + c') * X from fun X => by ring]
      exact Dvd.dvd.mul_right hdiv _
  · simp at h

/-! ## Atom rules -/

/-- Same coefficient and sums; the summands agree pointwise. -/
def PWEq (V : LV) (t t' : ATm) : Prop :=
  t'.c = t.c ∧ t'.sums = t.sums ∧ ∀ μ, abody V t' μ = abody V t μ

theorem PWEq.den {V : LV} {t t' : ATm} (h : PWEq V t t') (ν : ℕ → ℤ) : t'.den V ν = t.den V ν :=
  den_of_pw V t t' h.2.1 (fun μ => by rw [h.1, h.2.2]) ν

theorem PWEq.trans {V : LV} {a b c : ATm} (h1 : PWEq V a b) (h2 : PWEq V b c) : PWEq V a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun μ => (h2.2.2 μ).trans (h1.2.2 μ)⟩

theorem aext_find (V : LV) (ats : List Atom) (z : ℕ) (a : Atom) (hnd : (ids ats).Nodup)
    (h : ats.find? (fun b => b.id == z) = some a) (μ : ℕ → ℤ) :
    ∃ μ', aext V ats μ z = aval V μ' a ∧ ∀ y, y ∉ ids ats → μ' y = μ y := by
  induction ats generalizing μ with
  | nil => simp at h
  | cons b l ih =>
    simp only [ids, List.map_cons, List.nodup_cons] at hnd
    simp only [List.find?_cons] at h
    by_cases hb : (b.id == z) = true
    · rw [hb] at h
      simp only [Option.some.injEq] at h
      subst h
      simp only [beq_iff_eq] at hb
      subst hb
      refine ⟨μ, ?_, fun _ _ => rfl⟩
      simp only [aext]; rw [aext_off V l _ _ hnd.1, Function.update_self]
    · simp only [Bool.not_eq_true] at hb
      rw [hb] at h
      obtain ⟨μ', h1, h2⟩ := ih hnd.2 h (Function.update μ b.id (aval V μ b))
      refine ⟨μ', h1, fun y hy => ?_⟩
      simp only [ids, List.map_cons, List.mem_cons, not_or] at hy
      rw [h2 y hy.2, Function.update_of_ne hy.1]

/-- A delta reading a digit condition, read as the delta it is equivalent to. -/
def dzFind (PW : List (DMon × DMon)) (ats : List Atom) (f : Fac) : Option Fac :=
  match f.2 with
  | [([z], 1)] =>
    match ats.find? (fun b => b.id == z) with
    | some a =>
      match dzPoly PW ats a with
      | some (N, P) => if f.1 = N ∧ plainP ats P = true then some (N, P) else none
      | none => none
    | none => none
  | _ => none

/-- Every delta reading a digit condition rewritten. -/
def dzRule (PW : List (DMon × DMon)) (ats : List Atom) (ds : List Fac) : List Fac :=
  ds.map fun f => (dzFind PW ats f).getD f

theorem dzRule_ok (V : LV) (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (ats : List Atom)
    (hnd : (ids ats).Nodup) (ds : List Fac) (μ : ℕ → ℤ) :
    ((dzRule PW ats ds).map (delV V.ρ.dv (aext V ats μ))).prod =
      (ds.map (delV V.ρ.dv (aext V ats μ))).prod := by
  unfold dzRule
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun f _ => ?_
  simp only [Function.comp_apply]
  unfold dzFind
  split
  · next z hz =>
    split
    · next a ha =>
      split
      · next N P hP =>
        split_ifs with hc
        · simp only [Option.getD_some]
          obtain ⟨μ', h1, h2⟩ := aext_find V ats z a hnd ha μ
          have hPμ : ipDen μ' P = ipDen (aext V ats μ) P := by
            rw [ipDen_aext V ats P hc.2]
            refine ipDen_reads P _ _ fun y hy => h2 y ?_
            have := hc.2
            simp only [plainP, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
              decide_eq_false_iff_not] at this
            exact this y hy
          unfold delV
          simp only [hz, hc.1]
          have : ipDen (aext V ats μ) [([z], 1)] = aext V ats μ z := by
            simp [ipDen, imDen]
          rw [this, h1, ← hPμ]
          by_cases hd : (((N.den V.ρ.dv : ℕ) : ℤ) ∣ ipDen μ' P)
          · rw [if_pos hd, if_pos ((dzPoly_ok V PW hPW ats a N P hP μ').2 hd)]
          · rw [if_neg hd, if_neg (fun h' => hd ((dzPoly_ok V PW hPW ats a N P hP μ').1 h'))]
        · rfl
      · rfl
    · rfl
  · rfl

/-- A digit product with a zero argument. -/
def isZeroDig (a : Atom) : Bool :=
  a.f == 0 && match a.args with
    | [(p, _), (q, _)] => p.isEmpty || q.isEmpty
    | _ => false

theorem aval_zeroDig (V : LV) (μ : ℕ → ℤ) (a : Atom) (h : isZeroDig a = true) :
    aval V μ a = 0 := by
  unfold isZeroDig at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hf, h⟩ := h
  split at h
  · next p M1 q M2 hargs =>
    simp only [aval, hf, show (0 : ℕ) < 100 by norm_num, if_true, bfn, hargs, List.map_cons,
      List.map_nil, argV, List.getD_cons_zero, List.getD_cons_succ]
    simp only [Bool.or_eq_true, List.isEmpty_iff] at h
    rcases h with rfl | rfl <;> simp [ipDen, dig]
  · simp at h

/-- A zero digit product at the split `p`, substituted by `0`. -/
def zeroAt (t : ATm) (p : List Atom × Atom × List Atom) : Option ATm :=
  if isZeroDig p.2.1 && !(ids p.2.2).contains p.2.1.id then
    some ⟨t.c, t.sums, p.1 ++ p.2.2.map (atSub p.2.1.id []), t.dels.map (facSub p.2.1.id []),
      t.phs.map (facSub p.2.1.id []), t.aps⟩
  else none

theorem zeroAt_ok (V : LV) (t t' : ATm) (p : List Atom × Atom × List Atom)
    (hp : t.ats = p.1 ++ p.2.1 :: p.2.2) (h : zeroAt t p = some t') : PWEq V t t' := by
  unfold zeroAt at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hc
  refine ⟨rfl, rfl, fun μ => ?_⟩
  unfold abody
  simp only
  rw [hp, aext_append, aext_append]
  simp only [aext]
  rw [aval_zeroDig V _ _ hc.1]
  have e := aext_sub V p.2.2 p.2.1.id hc.2 [] (by simp [plainP, ipVs]) rfl (aext V p.1 μ)
  simp only [ipDen_nil] at e
  rw [e, bodyOf_sub]
  rfl

/-- An atom nothing reads, at the split `p`, removed. -/
def dropAt (t : ATm) (p : List Atom × Atom × List Atom) : Option ATm :=
  if !(fvs t).contains p.2.1.id && !(argVs p.2.2).contains p.2.1.id &&
      !(ids p.2.2).contains p.2.1.id then
    some ⟨t.c, t.sums, p.1 ++ p.2.2, t.dels, t.phs, t.aps⟩
  else none

theorem dropAt_ok (V : LV) (t t' : ATm) (p : List Atom × Atom × List Atom)
    (hp : t.ats = p.1 ++ p.2.1 :: p.2.2) (h : dropAt t p = some t') : PWEq V t t' := by
  unfold dropAt at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  refine ⟨rfl, rfl, fun μ => ?_⟩
  unfold abody
  simp only
  rw [hp, aext_append, aext_append]
  simp only [aext]
  rw [aext_upd V p.2.2 p.2.1.id (by simp only [List.mem_append, not_or]; exact ⟨h2, h3⟩)]
  congr 1
  refine bodyOf_reads _ _ _ _ _ fun y hy => ?_
  have hy' : y ≠ p.2.1.id := fun e => h1 (e ▸ (by simp only [fvs, List.mem_append]; exact Or.inl hy))
  rw [Function.update_of_ne hy']

theorem find_id (l : List Atom) (hnd : (ids l).Nodup) (b : Atom) (hb : b ∈ l) :
    l.find? (fun a => a.id == b.id) = some b := by
  induction l with
  | nil => simp at hb
  | cons a l ih =>
    simp only [ids, List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    rcases List.mem_cons.1 hb with rfl | hb'
    · simp
    · have hne : a.id ≠ b.id := fun e => hnd.1 (e ▸ List.mem_map_of_mem hb')
      simp only [show (a.id == b.id) = false from by simpa using hne]
      exact ih hnd.2 hb'

/-- Whether two atoms compute the same function of the same arguments. -/
def sameAt (a b : Atom) : Bool := a.f == b.f && a.ks == b.ks && a.dp == b.dp && a.args == b.args

/-- The atom at the split `sp` read as an earlier atom computing the same value. -/
def dedupAt (t : ATm) (sp : List Atom × Atom × List Atom) : Option ATm :=
  match sp.1.find? (fun a => a.id != sp.2.1.id && sameAt a sp.2.1) with
  | some a =>
    if (ids t.ats).Nodup && sp.2.1.args.all (fun p => plainP t.ats p.1) &&
        !(argVs t.ats).contains sp.2.1.id then
      some ⟨t.c, t.sums, t.ats, t.dels.map (facSub sp.2.1.id (ipV a.id)),
        t.phs.map (facSub sp.2.1.id (ipV a.id)), t.aps⟩
    else none
  | none => none

theorem dedupAt_ok (V : LV) (t t' : ATm) (sp : List Atom × Atom × List Atom)
    (hsp : t.ats = sp.1 ++ sp.2.1 :: sp.2.2) (h : dedupAt t sp = some t') : PWEq V t t' := by
  unfold dedupAt at h
  split at h
  · next a ha =>
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not, List.all_eq_true] at hc
    obtain ⟨⟨hnd, hpl⟩, hna⟩ := hc
    have hnd : (ids t.ats).Nodup := of_decide_eq_true hnd
    obtain ⟨ha1, ha2⟩ := List.find?_some ha |> fun h' => (⟨h', List.mem_of_find?_eq_some ha⟩ :
      _ ∧ a ∈ sp.1)
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, sameAt, beq_iff_eq] at ha1
    obtain ⟨hid, ⟨⟨⟨hf, hks⟩, hdp⟩, hargs⟩⟩ := ha1
    refine ⟨rfl, rfl, fun μ => ?_⟩
    unfold abody
    simp only
    set E := aext V t.ats μ
    have hbm : sp.2.1 ∈ t.ats := by rw [hsp]; simp
    have ham : a ∈ t.ats := by rw [hsp]; exact List.mem_append_left _ ha2
    obtain ⟨μb, hb1, hb2⟩ := aext_find V t.ats sp.2.1.id sp.2.1 hnd (find_id _ hnd _ hbm) μ
    obtain ⟨μa, ha3, ha4⟩ := aext_find V t.ats a.id a hnd (find_id _ hnd _ ham) μ
    have hval : E sp.2.1.id = E a.id := by
      show aext V t.ats μ _ = aext V t.ats μ _
      rw [hb1, ha3]
      have : aval V μb sp.2.1 = aval V μa sp.2.1 := by
        refine aval_reads V _ _ _ fun y hy => ?_
        simp only [atVs, List.mem_flatMap] at hy
        obtain ⟨p, hp, hy⟩ := hy
        have := hpl p hp
        simp only [plainP, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
          decide_eq_false_iff_not] at this
        rw [hb2 y (this y hy), ha4 y (this y hy)]
      rw [this]
      unfold aval
      rw [hf, hks, hdp, hargs]
    rw [bodyOf_sub, ipDen_V, ← hval, Function.update_eq_self]
  · simp at h

/-- The pairs of coefficients and arguments of a digit condition without the zero arguments. -/
def nzPairs (ks : List ℤ) (args : List (IPoly × DMon)) : List (ℤ × (IPoly × DMon)) :=
  (List.zip ks args).filter fun p => !p.2.1.isEmpty

theorem lsum_nz (ks : List ℤ) (args : List (IPoly × DMon)) (g : ℤ → ℤ) (h0 : g 0 = 0)
    (f : IPoly × DMon → ℤ) (hf : ∀ M, f ([], M) = 0) :
    lsum ((nzPairs ks args).map (·.1)) ((nzPairs ks args).map (f ·.2)) g =
      lsum ks (args.map f) g := by
  induction ks generalizing args with
  | nil => simp [nzPairs, lsum]
  | cons c ks ih =>
    cases args with
    | nil => simp [nzPairs, lsum]
    | cons p args =>
      have ih' := ih args
      simp only [nzPairs, List.zip_cons_cons, List.filter_cons] at ih' ⊢
      by_cases hp : p.1.isEmpty = true
      · obtain ⟨q, M⟩ := p
        simp only at hp
        rw [List.isEmpty_iff] at hp
        subst hp
        simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false, ih']
        simp [lsum, hf, h0]
      · simp only [Bool.not_eq_true] at hp
        simp only [hp, Bool.not_false, ite_true, List.map_cons]
        simp only [lsum, List.zipWith_cons_cons, List.sum_cons] at ih' ⊢
        rw [ih']

/-- A digit condition without its zero arguments. -/
def dzDrop (a : Atom) : Option Atom :=
  if a.f = 3 ∧ a.args.length = a.ks.length + 1 ∧
      ((List.zip a.ks a.args).any fun p => p.2.1.isEmpty) = true ∧ nzPairs a.ks a.args ≠ [] then
    some { a with ks := (nzPairs a.ks a.args).map (·.1),
                  args := (nzPairs a.ks a.args).map (·.2) ++ a.args.drop a.ks.length }
  else none

theorem dzDrop_ok (V : LV) (a a' : Atom) (h : dzDrop a = some a') (μ : ℕ → ℤ) :
    aval V μ a' = aval V μ a := by
  unfold dzDrop at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨hf, hlen, -, -⟩ := hc
  obtain ⟨id, f, ks, dp, args⟩ := a
  simp only at hf hlen ⊢
  subst hf
  have hl : (nzPairs ks args).length ≤ ks.length := by
    unfold nzPairs; exact (List.length_filter_le _ _).trans (by simp)
  simp only [aval, show (3 : ℕ) < 100 by norm_num, if_true, bfn]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  rw [List.map_append, lsum_append _ _ _ _ (by simp), List.map_map]
  have e1 := lsum_nz ks args (dig (dp.map (·.den V.ρ.dv) |>.getD 0 2) i) (by simp [dig])
    (argV V.ρ.dv μ) (fun M => by simp [argV, ipDen])
  simp only [Function.comp_def] at e1 ⊢
  rw [e1]
  have e2 : (args.map (argV V.ρ.dv μ)).getD ks.length 0 =
      (((nzPairs ks args).map fun p => argV V.ρ.dv μ p.2) ++
        (args.drop ks.length).map (argV V.ρ.dv μ)).getD (nzPairs ks args).length 0 := by
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_map, Nat.sub_self]
    obtain ⟨B, hB⟩ : ∃ B, args.drop ks.length = [B] := by
      have : (args.drop ks.length).length = 1 := by simp [hlen]
      match h' : args.drop ks.length, this with
      | [B], _ => exact ⟨B, rfl⟩
    rw [hB]
    simp only [List.map_cons, List.map_nil, List.getD_cons_zero]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [show args[ks.length]? = some B by rw [← List.head?_drop, hB]; rfl]
    rfl
  rw [e2]
  simp only [List.length_map]

/-- The digit condition at the split `sp` without its zero arguments. -/
def dzDropAt (t : ATm) (sp : List Atom × Atom × List Atom) : Option ATm :=
  match dzDrop sp.2.1 with
  | some a' => some ⟨t.c, t.sums, sp.1 ++ a' :: sp.2.2, t.dels, t.phs, t.aps⟩
  | none => none

theorem dzDropAt_ok (V : LV) (t t' : ATm) (sp : List Atom × Atom × List Atom)
    (hsp : t.ats = sp.1 ++ sp.2.1 :: sp.2.2) (h : dzDropAt t sp = some t') : PWEq V t t' := by
  unfold dzDropAt at h
  split at h
  · next a' ha =>
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨rfl, rfl, fun μ => ?_⟩
    unfold abody
    simp only
    rw [hsp, aext_append, aext_append]
    simp only [aext]
    have hid : a'.id = sp.2.1.id := by
      unfold dzDrop at ha; split_ifs at ha; simp only [Option.some.injEq] at ha; rw [← ha]
    rw [hid, dzDrop_ok V _ _ ha]
  · simp at h

/-- One atom rule, the first that applies. -/
def aRule1 (t : ATm) : Option ATm :=
  match firstSome (zeroAt t) (splits t.ats) with
  | some t' => some t'
  | none =>
    match firstSome (dropAt t) (splits t.ats) with
    | some t' => some t'
    | none =>
      match firstSome (dedupAt t) (splits t.ats) with
      | some t' => some t'
      | none => firstSome (dzDropAt t) (splits t.ats)

theorem aRule1_ok (V : LV) (t t' : ATm) (h : aRule1 t = some t') : PWEq V t t' := by
  unfold aRule1 at h
  split at h
  · next t'' h' =>
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h'
    exact zeroAt_ok V t _ p (splits_spec _ p hp) he
  · split at h
    · next t'' h' =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h'
      exact dropAt_ok V t _ p (splits_spec _ p hp) he
    · split at h
      · next t'' h' =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h'
        exact dedupAt_ok V t _ p (splits_spec _ p hp) he
      · obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h
        exact dzDropAt_ok V t _ p (splits_spec _ p hp) he

/-- Atom rules repeated, at most `n` of them. -/
def aRules : ℕ → ATm → ATm
  | 0, t => t
  | n + 1, t => match aRule1 t with
    | some t' => aRules n t'
    | none => t

theorem aRules_ok (V : LV) (n : ℕ) (t : ATm) : PWEq V t (aRules n t) := by
  induction n generalizing t with
  | zero => exact ⟨rfl, rfl, fun _ => rfl⟩
  | succ n ih =>
    simp only [aRules]
    split
    · next t' h => exact (aRule1_ok V t t' h).trans (ih t')
    · exact ⟨rfl, rfl, fun _ => rfl⟩

/-! ## Free variables -/

theorem aext_agreeT (V : LV) (l : List Atom) (hl : wfA l = true) (T : List ℕ)
    (hT : ∀ v ∈ argVs l, v ∈ T ∨ v ∈ ids l) (μ μ' : ℕ → ℤ) (h : ∀ v ∈ T, μ v = μ' v) :
    ∀ v, v ∈ T ∨ v ∈ ids l → aext V l μ v = aext V l μ' v := by
  induction l generalizing T μ μ' with
  | nil => intro v hv; simp [ids] at hv; exact h v hv
  | cons a l ih =>
    simp only [wfA, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not] at hl
    have ha : ∀ v ∈ atVs a, v ∈ T := fun v hv => by
      rcases hT v (by simp only [argVs, List.flatMap_cons, List.mem_append]; exact Or.inl hv)
        with h' | h'
      · exact h'
      · exact absurd h' (hl.1 v hv)
    have hv : aval V μ a = aval V μ' a := aval_reads V a _ _ fun v hv' => h v (ha v hv')
    simp only [aext]
    intro v hvT
    refine ih hl.2 (a.id :: T) (fun w hw => ?_) _ _ (fun w hw => ?_) v ?_
    · rcases hT w (by simp only [argVs, List.flatMap_cons, List.mem_append]; exact Or.inr hw)
        with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · simp only [ids, List.map_cons, List.mem_cons] at h'
        rcases h' with h' | h'
        · exact Or.inl (h' ▸ List.mem_cons_self)
        · exact Or.inr h'
    · rcases List.mem_cons.1 hw with rfl | hw
      · simp [hv]
      · by_cases e : w = a.id
        · subst e; simp [hv]
        · rw [Function.update_of_ne e, Function.update_of_ne e]; exact h w hw
    · simp only [ids, List.map_cons, List.mem_cons] at hvT
      rcases hvT with hvT | hvT | hvT
      · exact Or.inl (List.mem_cons_of_mem _ hvT)
      · exact Or.inl (hvT ▸ List.mem_cons_self)
      · exact Or.inr hvT

/-- The variables a term reads that it neither binds nor computes. -/
def freeV (t : ATm) : List ℕ :=
  (fvs t ++ argVs t.ats).filter (fun v => !(ids t.ats).contains v && !(abvs t).contains v) ++
    (t.aps.flatMap apVs).filter fun v => !(abvs t).contains v

theorem sumsV_reads_free (dv : ℕ → ℕ) (S : List ℕ) (f : (ℕ → ℤ) → ℂ) (hf : RD S f)
    (s : List (ℕ × DMon)) (ν ν' : ℕ → ℤ)
    (h : ∀ v ∈ S, v ∉ s.map (·.1) → ν v = ν' v) : sumsV dv s f ν = sumsV dv s f ν' := by
  induction s generalizing ν ν' with
  | nil => exact hf _ _ fun v hv => h v hv (by simp)
  | cons p s ih =>
    simp only [sumsV]
    refine Finset.sum_congr rfl fun j _ => ih _ _ fun v hv hvs => ?_
    by_cases e : v = p.1
    · subst e; simp
    · rw [Function.update_of_ne e, Function.update_of_ne e]
      exact h v hv (by simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨e, hvs⟩)

theorem den_reads_free (V : LV) (t : ATm) (hw : wfA t.ats = true) (ν ν' : ℕ → ℤ)
    (h : ∀ v ∈ freeV t, ν v = ν' v) : t.den V ν = t.den V ν' := by
  unfold ATm.den
  congr 1
  set T := (fvs t ++ argVs t.ats).filter (fun v => !(ids t.ats).contains v) ++ t.aps.flatMap apVs
  have hbody : RD T (abody V t) := by
    intro μ μ' hμ
    have ha := aext_agreeT V t.ats hw T (fun v hv => by
      by_cases hi : v ∈ ids t.ats
      · exact Or.inr hi
      · exact Or.inl (List.mem_append_left _ (List.mem_filter.2 ⟨by simp [hv], by simpa using hi⟩)))
      μ μ' hμ
    unfold abody
    congr 1
    · refine bodyOf_reads _ _ _ _ _ fun v hv => ha v ?_
      by_cases hi : v ∈ ids t.ats
      · exact Or.inr hi
      · exact Or.inl (List.mem_append_left _ (List.mem_filter.2
          ⟨List.mem_append_left _ (List.mem_append_left _ hv), by simpa using hi⟩))
    · exact apsV_reads V t.aps μ μ' fun v hv => hμ v (List.mem_append_right _ hv)
  refine sumsV_reads_free _ T _ hbody _ _ _ fun v hv hb => h v ?_
  have hb' : (abvs t).contains v = false := by simpa [abvs] using hb
  simp only [T, List.mem_append, List.mem_filter] at hv
  simp only [freeV, List.mem_append, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
  rcases hv with hv | hv
  · exact Or.inl ⟨hv.1, by simpa using hv.2, hb'⟩
  · exact Or.inr ⟨hv, hb'⟩

/-! ## Canonical names -/

/-- The first occurrences of a list's elements. -/
def uniq (l : List ℕ) : List ℕ := l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- Bound variables renamed `RBASE + k` and atoms `ABASE + k` in order of first occurrence. -/
def cmap (bl al : List ℕ) (v : ℕ) : ℕ :=
  if bl.contains v then RBASE + bl.idxOf v else if al.contains v then ABASE + al.idxOf v else v

/-- The term renamed canonically, when the renaming is injective. -/
def canonRen (t : ATm) : ATm :=
  let occ := uniq (fvs t ++ ids t.ats ++ argVs t.ats ++ abvs t)
  let bl := occ.filter fun v => (abvs t).contains v
  let al := occ.filter fun v => (ids t.ats).contains v && !(abvs t).contains v
  if injOn (cmap bl al) (allV t) && wfA t.ats &&
      (t.aps.flatMap apVs).all (fun v => !(ids t.ats).contains v) then tRen (cmap bl al) t
  else t

theorem canonRen_ok (V : LV) (t : ATm) (ν : ℕ → ℤ) : (canonRen t).den V ν = t.den V ν := by
  unfold canonRen
  simp only
  split_ifs with hc
  · simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨hinj, hw⟩, hap0⟩ := hc
    have hap : ∀ v ∈ t.aps.flatMap apVs, v ∉ ids t.ats := by
      intro v hv hi
      have := List.all_eq_true.1 hap0 v hv
      simp [hi] at this
    rw [tRen_den V _ t hinj]
    refine den_reads_free V t hw _ _ fun v hv => ?_
    have key : v ∉ abvs t ∧ v ∉ ids t.ats := by
      simp only [freeV, List.mem_append, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
        List.contains_eq_mem, decide_eq_false_iff_not] at hv
      rcases hv with hv | hv
      · exact ⟨hv.2.2, hv.2.1⟩
      · exact ⟨hv.2, hap v hv.1⟩
    simp only [Function.comp_apply, cmap, List.contains_eq_mem, List.mem_filter,
      decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    rw [if_neg (fun h' => key.1 h'.2), if_neg (fun h' => key.2 h'.2.1)]
  · rfl

/-! ## Sorting the sums -/

/-- Sorted insertion of a sum by its variable. -/
def sIns (p : ℕ × DMon) : List (ℕ × DMon) → List (ℕ × DMon)
  | [] => [p]
  | q :: l => if p.1 ≤ q.1 then p :: q :: l else q :: sIns p l

/-- The sums sorted by variable. -/
def sSort (l : List (ℕ × DMon)) : List (ℕ × DMon) := l.foldr sIns []

theorem sIns_map (p : ℕ × DMon) (l : List (ℕ × DMon)) :
    ∀ v, v ∈ (sIns p l).map (·.1) ↔ v = p.1 ∨ v ∈ l.map (·.1) := by
  induction l with
  | nil => simp [sIns]
  | cons q l ih =>
    intro v
    simp only [sIns]
    split_ifs
    · simp
    · simp only [List.map_cons, List.mem_cons, ih]; tauto

theorem sumsV_sIns (dv : ℕ → ℕ) (p : ℕ × DMon) (l : List (ℕ × DMon)) (hp : p.1 ∉ l.map (·.1))
    (f : (ℕ → ℤ) → ℂ) (ν : ℕ → ℤ) : sumsV dv (sIns p l) f ν = sumsV dv (p :: l) f ν := by
  induction l generalizing ν with
  | nil => rfl
  | cons q l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hp
    simp only [sIns]
    split_ifs
    · rfl
    · simp only [sumsV]
      rw [Finset.sum_congr rfl fun j _ => ih hp.2 _]
      simp only [sumsV]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Function.update_comm hp.1]

theorem sSort_map (l : List (ℕ × DMon)) : ∀ v, v ∈ (sSort l).map (·.1) ↔ v ∈ l.map (·.1) := by
  induction l with
  | nil => simp [sSort]
  | cons q l ih =>
    intro v
    simp only [sSort, List.foldr_cons] at ih ⊢
    rw [sIns_map, ih]; simp

theorem sumsV_sSort (dv : ℕ → ℕ) (l : List (ℕ × DMon)) (hl : (l.map (·.1)).Nodup)
    (f : (ℕ → ℤ) → ℂ) (ν : ℕ → ℤ) : sumsV dv (sSort l) f ν = sumsV dv l f ν := by
  induction l generalizing ν with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.nodup_cons] at hl
    show sumsV dv (sIns p (sSort l)) f ν = _
    rw [sumsV_sIns _ _ _ (fun h => hl.1 ((sSort_map l _).1 h))]
    simp only [sumsV]
    exact Finset.sum_congr rfl fun j _ => ih hl.2 _

/-- The sums sorted, when their variables are distinct. -/
def sortSums (t : ATm) : ATm :=
  if (abvs t).Nodup then ⟨t.c, sSort t.sums, t.ats, t.dels, t.phs, t.aps⟩ else t

theorem sortSums_ok (V : LV) (t : ATm) (ν : ℕ → ℤ) : (sortSums t).den V ν = t.den V ν := by
  unfold sortSums
  split_ifs with h
  · unfold ATm.den; simp only
    rw [show abody V ⟨t.c, sSort t.sums, t.ats, t.dels, t.phs, t.aps⟩ = abody V t from rfl,
      sumsV_sSort _ _ h]
  · rfl

/-! ## Exact pins -/

/-- `x` read as `y` in a term whose sums are `a ++ (x, D) :: b` with `a ++ b = a' ++ (y, D) :: b'`
and whose factors are `pre ++ [D ∣ x - y] :: post`: for `x, y < D` the delta holds only at
`x = y`. -/
def xPin1 (t : ATm) (a b : List (ℕ × DMon)) (x : ℕ) (D : DMon) (pre : List Fac) (f : Fac)
    (post : List Fac) (a' : List (ℕ × DMon)) (y : ℕ) (D' : DMon) (b' : List (ℕ × DMon)) :
    Option ATm :=
  if decide (f.1 = D) && decide (D' = D) && decide (f.2 = ipSub (ipV x) (ipV y)) &&
      decide (x ≠ y) && !((a ++ b).map (·.1)).contains x && !((a' ++ b').map (·.1)).contains y &&
      !(ids t.ats).contains x && !(ids t.ats).contains y && !(t.aps.flatMap apVs).contains x then
    some ⟨t.c, a ++ b, t.ats.map (atSub x (ipV y)), (pre ++ post).map (facSub x (ipV y)),
      t.phs.map (facSub x (ipV y)), t.aps⟩
  else none

/-- The first exact pin of a term. -/
def xPin (t : ATm) : Option ATm :=
  firstSome (fun p => firstSome (fun q => firstSome
    (fun r => xPin1 t p.1 p.2.2 p.2.1.1 p.2.1.2 q.1 q.2.1 q.2.2 r.1 r.2.1.1 r.2.1.2 r.2.2)
    (splits (p.1 ++ p.2.2))) (splits t.dels)) (splits t.sums)

theorem dvd_range_eq (N : ℕ) (j k : ℕ) (hj : j < N) (hk : k < N)
    (h : ((N : ℕ) : ℤ) ∣ (j : ℤ) - (k : ℤ)) : j = k := by
  have h0 := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
  omega

theorem xPin1_ok (V : LV) (t t' : ATm) (a b : List (ℕ × DMon)) (x : ℕ) (D : DMon)
    (pre : List Fac) (f : Fac) (post : List Fac) (a' : List (ℕ × DMon)) (y : ℕ) (D' : DMon)
    (b' : List (ℕ × DMon)) (hs : t.sums = a ++ (x, D) :: b) (hd : t.dels = pre ++ f :: post)
    (hab : a ++ b = a' ++ (y, D') :: b')
    (h : xPin1 t a b x D pre f post a' y D' b' = some t') (ν : ℕ → ℤ) :
    t'.den V ν = t.den V ν := by
  unfold xPin1 at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hf1, hD'⟩, hf2⟩, hxy⟩, hx⟩, hy'⟩, hxa⟩, hya⟩, hxap⟩ := hc
  subst hD'
  unfold ATm.den
  congr 1
  rw [hs, sumsV_pull _ a b x D' hx, hab, sumsV_pull _ a' b' y D' hy',
    sumsV_pull _ a' b' y D' hy']
  refine sumsV_congr _ _ _ _ (fun μ => Finset.sum_congr rfl fun k hk => ?_) ν
  simp only [Finset.mem_range] at hk
  set ν' := Function.update μ y (k : ℤ) with hν'
  have hyv : ν' y = k := by simp [ν']
  have hR : ∀ S : List (ℕ × DMon), abody V ⟨t.c, S, t.ats.map (atSub x (ipV y)),
      (pre ++ post).map (facSub x (ipV y)), t.phs.map (facSub x (ipV y)), t.aps⟩ ν' =
      bodyOf V.ρ.dv (pre ++ post) t.phs (aext V t.ats (Function.update ν' x k)) *
        apsV V t.aps ν' := by
    intro S
    unfold abody
    simp only
    rw [bodyOf_sub]
    have hidy : y ∉ ids (t.ats.map (atSub x (ipV y))) := by rw [ids_atSub]; exact hya
    have h1 : ipDen (aext V (t.ats.map (atSub x (ipV y))) ν') (ipV y) = k := by
      rw [ipDen_V, aext_off V _ _ y hidy, hyv]
    rw [h1]
    have h2 := aext_sub V t.ats x hxa (ipV y) (by simp [plainP, ipVs, ipV, hya])
      (by simp [ipHas, ipV]; exact hxy) ν'
    rw [ipDen_V, hyv] at h2
    rw [← h2]
  rw [hR]
  have hsplit : ∀ j : ℕ, j < D'.den V.ρ.dv → abody V t (Function.update ν' x (j : ℤ)) =
      (if j = k then bodyOf V.ρ.dv (pre ++ post) t.phs
        (aext V t.ats (Function.update ν' x (j : ℤ))) else 0) * apsV V t.aps ν' := by
    intro j hj
    unfold abody
    rw [apsV_upd V t.aps x hxap]
    rw [hd]
    have hdel : delV V.ρ.dv (aext V t.ats (Function.update ν' x (j : ℤ))) f =
        if j = k then 1 else 0 := by
      unfold delV
      rw [hf2, ipDen_sub, ipDen_V, ipDen_V, aext_off V _ _ x hxa, aext_off V _ _ y hya,
        Function.update_self, Function.update_of_ne (Ne.symm hxy), hyv, hf1]
      by_cases hjk : j = k
      · subst hjk; simp
      · rw [if_neg hjk, if_neg]
        exact fun hdv => hjk (dvd_range_eq _ j k hj hk hdv)
    simp only [bodyOf, List.map_append, List.map_cons, List.prod_append, List.prod_cons, hdel]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun j hj => hsplit j (Finset.mem_range.1 hj), ← Finset.sum_mul,
    Finset.sum_ite_eq' (range (D'.den V.ρ.dv)) k, if_pos (Finset.mem_range.2 hk)]

theorem xPin_ok (V : LV) (t t' : ATm) (h : xPin t = some t') (ν : ℕ → ℤ) :
    t'.den V ν = t.den V ν := by
  obtain ⟨p, hp, h1⟩ := firstSome_spec _ _ _ h
  obtain ⟨q, hq, h2⟩ := firstSome_spec _ _ _ h1
  obtain ⟨r, hr, h3⟩ := firstSome_spec _ _ _ h2
  exact xPin1_ok V t t' p.1 p.2.2 p.2.1.1 p.2.1.2 q.1 q.2.1 q.2.2 r.1 r.2.1.1 r.2.1.2 r.2.2
    (splits_spec _ _ hp) (splits_spec _ _ hq) (splits_spec _ _ hr) h3 ν

/-! ## The normaliser -/

/-! ## Pins into powers of coefficient atoms -/

/-- `x` substituted by `v` in the arguments of a power's atoms. -/
def apSubA (x : ℕ) (v : IPoly) (a : APw) : APw := (a.1, a.2.1, a.2.2.map (atSub x v))

/-- Every power reads `x` only through atom arguments reduced modulo a divisor of `M`, and neither
`x` nor `v` names one of its atoms. -/
def apsPer (x : ℕ) (M : DMon) (v : IPoly) (l : List APw) : Bool :=
  l.all fun a => !ipHas x a.2.1 && argsPer x M a.2.2 && !(ids a.2.2).contains x && plainP a.2.2 v

theorem apsV_pin (V : LV) (hρ : V.ρ.OK) (x : ℕ) (M : DMon) (v : IPoly) (l : List APw)
    (h : apsPer x M v l = true) (hvx : ipHas x v = false) (μ : ℕ → ℤ)
    (hd : ((M.den V.ρ.dv : ℕ) : ℤ) ∣ μ x - ipDen μ v) :
    apsV V (l.map (apSubA x v)) μ = apsV V l μ := by
  unfold apsV
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun a ha => ?_
  simp only [apsPer, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨hp, hper⟩, hxid⟩, hvp⟩ := h a ha
  simp only [Function.comp_apply, apSubA]
  congr 1
  have e1 := aext_sub V a.2.2 x hxid v hvp hvx μ
  have e2 := aext_congr V hρ x M a.2.2 hper hxid μ (μ x) (ipDen μ v) hd
  rw [Function.update_eq_self] at e2
  have hl : ipDen (aext V (a.2.2.map (atSub x v)) μ) a.2.1 =
      ipDen (aext V a.2.2 (Function.update μ x (ipDen μ v))) a.2.1 := by
    rw [e1, ipDen_upd_of _ _ _ _ hp]
  have hr : ipDen (aext V a.2.2 μ) a.2.1 =
      ipDen (aext V a.2.2 (Function.update μ x (ipDen μ v))) a.2.1 := by
    rw [e2, ipDen_upd_of _ _ _ _ hp]
  rw [hl, hr]

/-- The powers read `x` as `v` for the delta `f = [M ∣ s x + b]` of `t`, `s = ±1`. -/
def apsPin1 (t : ATm) (x : ℕ) (pre : List Fac) (f : Fac) (post : List Fac) : Option ATm :=
  match ipLin x f.2 with
  | some (a, b) =>
    match ipConst a with
    | some s =>
      if (s == 1 || s == -1) && plainP t.ats f.2 && apsPer x f.1 (pinVal s b) t.aps &&
          (t.aps.flatMap apVs).contains x then
        some ⟨t.c, t.sums, t.ats, pre ++ f :: post, t.phs, t.aps.map (apSubA x (pinVal s b))⟩
      else none
    | none => none
  | none => none

theorem prod_zero_of_mem {l : List ℂ} (h : (0 : ℂ) ∈ l) : l.prod = 0 := List.prod_eq_zero h

theorem apsPin1_ok (V : LV) (hρ : V.ρ.OK) (t t' : ATm) (x : ℕ) (pre : List Fac) (f : Fac)
    (post : List Fac) (ht : t.dels = pre ++ f :: post) (h : apsPin1 t x pre f post = some t')
    (ν : ℕ → ℤ) : t'.den V ν = t.den V ν := by
  unfold apsPin1 at h
  split at h
  · next a b hlin =>
    split at h
    · next s hs =>
      split_ifs at h with hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨hs1, hfp⟩, hper⟩, _⟩ := hc
      obtain ⟨ha, hb, hp⟩ := ipLin_spec x f.2 a b hlin
      have hsv : ∀ ν, ipDen ν a = s := fun ν => ipConst_spec a s hs ν
      have hvx : ipHas x (pinVal s b) = false := ipHas_smul _ _ _ hb
      unfold ATm.den
      congr 1
      refine sumsV_congr _ _ _ _ (fun μ => ?_) ν
      unfold abody
      simp only
      rw [← ht]
      by_cases hd : ((f.1.den V.ρ.dv : ℕ) : ℤ) ∣ ipDen μ f.2
      · rw [apsV_pin V hρ x f.1 (pinVal s b) t.aps hper hvx μ (by
          rw [hp, hsv] at hd
          have := (pin_dvd s hs1 _ (μ x) (ipDen μ b)).1 hd
          simpa [pinVal, ipDen_smul] using this)]
      · have h0 : bodyOf V.ρ.dv t.dels t.phs (aext V t.ats μ) = 0 := by
          unfold bodyOf
          rw [ht]
          have : delV V.ρ.dv (aext V t.ats μ) f = 0 := by
            unfold delV; rw [ipDen_aext V t.ats f.2 hfp, if_neg hd]
          rw [prod_zero_of_mem (List.mem_map.2 ⟨f, by simp, this⟩), zero_mul]
        rw [h0, zero_mul, zero_mul]
    · simp at h
  · simp at h

/-- The first pin of a variable the powers read, by a delta of the term. -/
def apsPin (t : ATm) : Option ATm :=
  firstSome (fun x => firstSome (fun p => apsPin1 t x p.1 p.2.1 p.2.2) (splits t.dels))
    (abvs t)

theorem apsPin_ok (V : LV) (hρ : V.ρ.OK) (t t' : ATm) (h : apsPin t = some t') (ν : ℕ → ℤ) :
    t'.den V ν = t.den V ν := by
  obtain ⟨x, _, hx⟩ := firstSome_spec _ _ _ h
  obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ hx
  exact apsPin1_ok V hρ t t' x p.1 p.2.1 p.2.2 (splits_spec _ _ hp) he ν

/-- Eliminations repeated, at most `n` of them, the atom rules applied before each. -/
@[irreducible] def aElimAll (PW : List (DMon × DMon)) : ℕ → ATm → ATm
  | 0, t => t
  | n + 1, t => match aElimStep PW (aRules (t.ats.length + 1) t) with
    | some t' => aElimAll PW n t'
    | none => match xPin (aRules (t.ats.length + 1) t) with
      | some t' => aElimAll PW n t'
      | none => match aElimStepU PW (aRules (t.ats.length + 1) t) with
        | some t' => aElimAll PW n t'
        | none => match apsPin (aRules (t.ats.length + 1) t) with
          | some t' => aElimAll PW n t'
          | none => t

theorem aElimAll_ok (V : LV) (hρ : V.ρ.OK) (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ)
    (n : ℕ) (t : ATm) (ν : ℕ → ℤ) : (aElimAll PW n t).den V ν = t.den V ν := by
  induction n generalizing t with
  | zero => simp only [aElimAll]
  | succ n ih =>
    simp only [aElimAll]
    split
    · next t' h =>
      rw [ih, aElimStep_ok V hρ PW hPW _ t' h, (aRules_ok V (t.ats.length + 1) t).den]
    · split
      · next t' h =>
        rw [ih, xPin_ok V _ t' h, (aRules_ok V (t.ats.length + 1) t).den]
      · split
        · next t' h =>
          rw [ih, aElimStepU_ok V hρ PW _ t' h, (aRules_ok V (t.ats.length + 1) t).den]
        · split
          · next t' h =>
            rw [ih, apsPin_ok V hρ _ t' h, (aRules_ok V (t.ats.length + 1) t).den]
          · rfl

/-- Deltas reading digit conditions rewritten, when the table's variables are distinct. -/
def dzStep (PW : List (DMon × DMon)) (t : ATm) : ATm :=
  if (ids t.ats).Nodup then ⟨t.c, t.sums, t.ats, dzRule PW t.ats t.dels, t.phs, t.aps⟩ else t

theorem dzStep_ok (V : LV) (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (t : ATm) :
    PWEq V t (dzStep PW t) := by
  unfold dzStep
  split_ifs with hn
  · refine ⟨rfl, rfl, fun μ => ?_⟩
    unfold abody bodyOf
    simp only
    rw [dzRule_ok V PW hPW t.ats hn]
  · exact ⟨rfl, rfl, fun _ => rfl⟩

/-! ## Reduced arguments read under a divisor -/

/-- `K ∣ M` syntactically, or `M = K^n` with a floor of at least `2`. -/
def dvdP (fl : List ℕ) (PW : List (DMon × DMon)) (K M : DMon) : Bool :=
  K.dvd M || (PW.contains (K, M) && decide (2 ≤ M.den (flv fl)))

theorem dvdP_ok (ρ : Val) (fl : List ℕ) (hfl : FloorOK fl ρ) (PW : List (DMon × DMon))
    (hPW : PowOK PW ρ) (K M : DMon) (h : dvdP fl PW K M = true) :
    K.den ρ.dv ∣ M.den ρ.dv := by
  unfold dvdP at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
  rcases h with h | ⟨hm, h2⟩
  · exact DMon.dvd_den _ _ _ h
  · obtain ⟨-, n, hn⟩ := hPW _ hm
    have h3 : M.den (flv fl) ≤ M.den ρ.dv := DMon.den_mono _ _ hfl M
    simp only at hn
    rcases n with _ | n
    · rw [pow_zero] at hn; omega
    · rw [hn]; exact dvd_pow_self _ (Nat.succ_ne_zero n)

theorem fac_congr' (dv : ℕ → ℕ) (x : ℕ) (f : Fac) (ν : ℕ → ℤ) (a b : ℤ)
    (hab : ((f.1.den dv : ℕ) : ℤ) ∣ a - b) (hpos : 0 < f.1.den dv) :
    delV dv (Function.update ν x a) f = delV dv (Function.update ν x b) f ∧
      phV dv (Function.update ν x a) f = phV dv (Function.update ν x b) f := by
  have hN := hab.trans (ipDen_upd_dvd ν x a b f.2)
  constructor
  · unfold delV
    have : ((f.1.den dv : ℕ) : ℤ) ∣ ipDen (Function.update ν x a) f.2 ↔
        ((f.1.den dv : ℕ) : ℤ) ∣ ipDen (Function.update ν x b) f.2 := by
      constructor
      · intro h; have := dvd_sub h hN; simpa using this
      · intro h; have := dvd_add h hN; simpa using this
    simp only [this]
  · unfold phV
    obtain ⟨k, hk⟩ := hN
    have hz := om_ne_zero _ hpos
    rw [show ipDen (Function.update ν x a) f.2 = ipDen (Function.update ν x b) f.2 +
      (f.1.den dv : ℤ) * k by omega, zpow_add₀ hz, zpow_mul, zpow_natCast, om_pow_self _ hpos,
      one_zpow, mul_one]

/-- A reduced argument `mod(q, M)` at the split `sp`, read only by factors whose modulus divides
`M`, replaced by `q` there. -/
def modDropAt (fl : List ℕ) (PW : List (DMon × DMon)) (t : ATm)
    (sp : List Atom × Atom × List Atom) : Option ATm :=
  match sp.2.1.f, sp.2.1.args with
  | 2, [(q, M)] =>
    if (ipVs q).all (fun y => y != sp.2.1.id && !(ids sp.2.2).contains y) &&
        !(argVs t.ats).contains sp.2.1.id && !(ids sp.2.2).contains sp.2.1.id &&
        (t.dels ++ t.phs).all (fun g => !facHas sp.2.1.id g || (g.1.c != 0 && dvdP fl PW g.1 M)) then
      some ⟨t.c, t.sums, t.ats, t.dels.map (facSub sp.2.1.id q), t.phs.map (facSub sp.2.1.id q), t.aps⟩
    else none
  | _, _ => none

theorem modDropAt_ok (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (t t' : ATm)
    (sp : List Atom × Atom × List Atom) (hsp : t.ats = sp.1 ++ sp.2.1 :: sp.2.2)
    (h : modDropAt fl PW t sp = some t') : PWEq V t t' := by
  unfold modDropAt at h
  split at h
  · next q M hf hargs =>
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨hq, hna⟩, hnp⟩, hfac⟩ := hc
    refine ⟨rfl, rfl, fun μ => ?_⟩
    unfold abody
    simp only
    set E := aext V t.ats μ
    set P := aext V sp.1 μ
    have hE : E = aext V sp.2.2 (Function.update P sp.2.1.id (aval V P sp.2.1)) := by
      show aext V t.ats μ = _
      rw [hsp, aext_append]; rfl
    have hqE : ipDen E q = ipDen P q := by
      rw [hE]
      refine ipDen_reads q _ _ fun y hy => ?_
      rw [aext_off V sp.2.2 _ y (hq y hy).2, Function.update_of_ne (hq y hy).1]
    have hEa : E sp.2.1.id = ipDen P q % ((M.den V.ρ.dv : ℕ) : ℤ) := by
      rw [hE, aext_off V sp.2.2 _ _ hnp, Function.update_self]
      simp only [aval, hf, show (2 : ℕ) < 100 by norm_num, if_true, bfn, hargs, List.map_cons,
        List.map_nil, argV, List.getD_cons_zero]
    rw [bodyOf_sub, hqE]
    have hE2 : E = Function.update E sp.2.1.id (ipDen P q % ((M.den V.ρ.dv : ℕ) : ℤ)) := by
      rw [← hEa, Function.update_eq_self]
    conv_rhs => rw [hE2]
    have hcong : ∀ g ∈ t.dels ++ t.phs,
        delV V.ρ.dv (Function.update E sp.2.1.id (ipDen P q)) g =
          delV V.ρ.dv (Function.update E sp.2.1.id (ipDen P q % ((M.den V.ρ.dv : ℕ) : ℤ))) g ∧
        phV V.ρ.dv (Function.update E sp.2.1.id (ipDen P q)) g =
          phV V.ρ.dv (Function.update E sp.2.1.id (ipDen P q % ((M.den V.ρ.dv : ℕ) : ℤ))) g := by
      intro g hg
      rcases hfac g hg with hn | ⟨hc0, hd⟩
      · have hn' : ipHas sp.2.1.id g.2 = false := by simpa [facHas] using hn
        unfold delV phV
        rw [ipDen_upd_of _ _ _ _ hn', ipDen_upd_of _ _ _ _ hn']
        exact ⟨rfl, rfl⟩
      · have hK := dvdP_ok V.ρ fl hfl PW hPW _ _ hd
        refine fac_congr' _ _ g E _ _ ?_ (DMon.den_pos _ hρ.dpos _ (Nat.pos_of_ne_zero hc0))
        refine (Int.natCast_dvd_natCast.2 hK).trans ?_
        rw [Int.emod_def]; exact ⟨ipDen P q / ((M.den V.ρ.dv : ℕ) : ℤ), by ring⟩
    simp only [bodyOf]
    congr 1
    congr 1
    · congr 1; exact List.map_congr_left fun g hg => (hcong g (List.mem_append_left _ hg)).1
    · congr 1; exact List.map_congr_left fun g hg => (hcong g (List.mem_append_right _ hg)).2
  · simp at h

/-! ## Repunit deltas -/

theorem geom_one_add (D m : ℕ) (hD : 2 ≤ D) (hm : 1 ≤ m) :
    ∃ K : ℕ, (D ^ m - 1) / (D - 1) = 1 + D * K := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [← Nat.geomSum_eq hD, Finset.sum_range_succ']
  refine ⟨∑ i ∈ range k, D ^ i, ?_⟩
  rw [Finset.mul_sum]
  simp only [pow_succ, pow_zero]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem rep_dvd (D m : ℕ) (hD : 2 ≤ D) (hm : 1 ≤ m) (p q : ℤ) (hp0 : 0 ≤ p) (hp1 : p < D)
    (hq0 : 0 ≤ q) (hq1 : q < D) :
    ((D ^ m : ℕ) : ℤ) ∣ p * (((D ^ m - 1) / (D - 1) : ℕ) : ℤ) - q * (((D ^ m - 1) / (D - 1) : ℕ) : ℤ) ↔
      (D : ℤ) ∣ p - q := by
  obtain ⟨K, hK⟩ := geom_one_add D m hD hm
  rw [hK]
  constructor
  · intro h
    have hDm : (D : ℤ) ∣ ((D ^ m : ℕ) : ℤ) := by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact ⟨((D ^ k : ℕ) : ℤ), by push_cast; ring⟩
    have h2 := hDm.trans h
    have e : p * (((1 + D * K : ℕ)) : ℤ) - q * (((1 + D * K : ℕ)) : ℤ) =
        (p - q) + (D : ℤ) * ((p - q) * K) := by push_cast; ring
    rw [e] at h2
    exact (Int.dvd_add_left (Dvd.intro _ rfl)).1 h2
  · intro h
    have h0 := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    have : p = q := by omega
    subst this
    simp

theorem aext_mem (V : LV) (ats : List Atom) (a : Atom) (hnd : (ids ats).Nodup) (ha : a ∈ ats)
    (μ : ℕ → ℤ) : ∃ μ', aext V ats μ a.id = aval V μ' a := by
  induction ats generalizing μ with
  | nil => simp at ha
  | cons b l ih =>
    simp only [ids, List.map_cons, List.nodup_cons] at hnd
    simp only [aext]
    rcases List.mem_cons.1 ha with rfl | hl
    · exact ⟨μ, by rw [aext_off V l _ _ hnd.1, Function.update_self]⟩
    · exact ih hnd.2 hl _

/-- `f = [N ∣ u R - v R]` read as `[d ∣ u - v]` for the repunit `R = (N - 1)/(d - 1)` of
`N = d^m`, `m ≥ 1`, and atoms `u, v` reduced modulo `d`. -/
def repDel1 (fl : List ℕ) (PW : List (DMon × DMon)) (t : ATm) (pre : List Fac) (f : Fac)
    (post : List Fac) (r u v : Atom) : Option ATm :=
  match r.dp, u.args, v.args with
  | [d, N], [(_, du)], [(_, dv')] =>
    if r.f == 4 && u.f == 2 && v.f == 2 && decide (du = d) && decide (dv' = d) &&
        decide (f.1 = N) &&
        decide (f.2 = ipSub (ipMul (ipV u.id) (ipV r.id)) (ipMul (ipV v.id) (ipV r.id))) &&
        PW.contains (d, N) && dvdP fl PW d N && decide ((ids t.ats).Nodup) &&
        t.ats.contains r && t.ats.contains u && t.ats.contains v then
      some ⟨t.c, t.sums, t.ats, pre ++ (d, ipSub (ipV u.id) (ipV v.id)) :: post, t.phs, t.aps⟩
    else none
  | _, _, _ => none

/-- The first repunit delta of a term. -/
def repDel (fl : List ℕ) (PW : List (DMon × DMon)) (t : ATm) : Option ATm :=
  firstSome (fun q => firstSome (fun r => firstSome (fun u => firstSome
    (fun v => repDel1 fl PW t q.1 q.2.1 q.2.2 r u v) t.ats) t.ats) t.ats) (splits t.dels)

theorem repDel1_ok (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (t t' : ATm) (pre : List Fac) (f : Fac)
    (post : List Fac) (r u v : Atom) (hd : t.dels = pre ++ f :: post)
    (h : repDel1 fl PW t pre f post r u v = some t') : PWEq V t t' := by
  unfold repDel1 at h
  split at h
  · next d N qu du qv dv' hr hu hv =>
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hr4, hu2⟩, hv2⟩, hdu⟩, hdv⟩, hfN⟩, hf2⟩, hpw⟩, hdvd⟩, hnd⟩, hra⟩, hua⟩, hva⟩ := hc
    refine ⟨rfl, rfl, fun μ => ?_⟩
    unfold abody
    set E := aext V t.ats μ
    obtain ⟨hD2, m, hm⟩ := hPW _ hpw
    have hdN := dvdP_ok V.ρ fl hfl PW hPW _ _ hdvd
    set Dn := d.den V.ρ.dv
    have hm1 : 1 ≤ m := by
      rcases m with _ | m
      · simp only [pow_zero] at hm
        rw [hm] at hdN
        have := Nat.le_of_dvd one_pos hdN
        omega
      · omega
    have hval : ∀ a : Atom, a ∈ t.ats → a.f = 2 → (∃ q, a.args = [(q, d)]) →
        0 ≤ E a.id ∧ E a.id < Dn := by
      intro a ha hf ⟨q, hargs⟩
      obtain ⟨μ', hμ'⟩ := aext_mem V t.ats a hnd ha μ
      rw [show E a.id = aval V μ' a from hμ']
      simp only [aval, hf, show (2 : ℕ) < 100 by norm_num, if_true, bfn, hargs, List.map_cons,
        List.map_nil, argV, List.getD_cons_zero]
      have hpos : (0 : ℤ) < (Dn : ℤ) := by exact_mod_cast (show 0 < Dn by omega)
      exact ⟨Int.emod_nonneg _ (ne_of_gt hpos), Int.emod_lt_of_pos _ hpos⟩
    have hu' := hval u hua hu2 ⟨qu, by rw [hu, hdu]⟩
    have hv' := hval v hva hv2 ⟨qv, by rw [hv, hdv]⟩
    have hR : E r.id = (((N.den V.ρ.dv - 1) / (Dn - 1) : ℕ) : ℤ) := by
      obtain ⟨μ', hμ'⟩ := aext_mem V t.ats r hnd hra μ
      rw [show E r.id = aval V μ' r from hμ']
      simp only [aval, hr4, show (4 : ℕ) < 100 by norm_num, if_true, bfn, hr, List.map_cons,
        List.map_nil, List.getD_cons_zero, List.getD_cons_succ, Dn]
    have key := rep_dvd Dn m (by omega) hm1 (E u.id) (E v.id) hu'.1 hu'.2 hv'.1 hv'.2
    have hdel : delV V.ρ.dv E f = delV V.ρ.dv E (d, ipSub (ipV u.id) (ipV v.id)) := by
      unfold delV
      rw [hf2, hfN, ipDen_sub, ipDen_mul, ipDen_mul, ipDen_V, ipDen_V, ipDen_V, ipDen_sub, ipDen_V,
        ipDen_V, hR, hm]
      exact if_congr key rfl rfl
    show bodyOf V.ρ.dv (pre ++ (d, ipSub (ipV u.id) (ipV v.id)) :: post) t.phs E *
        apsV V t.aps μ = bodyOf V.ρ.dv t.dels t.phs E * apsV V t.aps μ
    congr 1
    rw [hd]
    simp only [bodyOf, List.map_append, List.map_cons, List.prod_append, List.prod_cons, hdel]
  · simp at h

theorem repDel_ok (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (t t' : ATm) (h : repDel fl PW t = some t') :
    PWEq V t t' := by
  obtain ⟨q, hq, h1⟩ := firstSome_spec _ _ _ h
  obtain ⟨r, -, h2⟩ := firstSome_spec _ _ _ h1
  obtain ⟨u, -, h3⟩ := firstSome_spec _ _ _ h2
  obtain ⟨v, -, h4⟩ := firstSome_spec _ _ _ h3
  exact repDel1_ok V hρ fl hfl PW hPW t t' q.1 q.2.1 q.2.2 r u v (splits_spec _ _ hq) h4

/-- Reduced arguments read under divisors replaced, at most `n` times. -/
def modRules (fl : List ℕ) (PW : List (DMon × DMon)) : ℕ → ATm → ATm
  | 0, t => t
  | n + 1, t => match firstSome (modDropAt fl PW t) (splits t.ats) with
    | some t' => modRules fl PW n t'
    | none => match repDel fl PW t with
      | some t' => modRules fl PW n t'
      | none => t

theorem modRules_ok (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (n : ℕ) (t : ATm) :
    PWEq V t (modRules fl PW n t) := by
  induction n generalizing t with
  | zero => exact ⟨rfl, rfl, fun _ => rfl⟩
  | succ n ih =>
    simp only [modRules]
    split
    · next t' h =>
      obtain ⟨sp, hsp, he⟩ := firstSome_spec _ _ _ h
      exact (modDropAt_ok V hρ fl hfl PW hPW t t' sp (splits_spec _ sp hsp) he).trans (ih t')
    · split
      · next t' h => exact (repDel_ok V hρ fl hfl PW hPW t t' h).trans (ih t')
      · exact ⟨rfl, rfl, fun _ => rfl⟩

/-! ## Constant atoms, exclusive or of bit patterns and shared atoms -/

/-- An atom replaced by one of the same variable whose value agrees after the atoms before it. -/
theorem swap_pw (V : LV) (t : ATm) (sp : List Atom × Atom × List Atom)
    (hsp : t.ats = sp.1 ++ sp.2.1 :: sp.2.2) (a' : Atom) (hid : a'.id = sp.2.1.id)
    (hv : ∀ μ, aval V (aext V sp.1 μ) a' = aval V (aext V sp.1 μ) sp.2.1) :
    PWEq V t ⟨t.c, t.sums, sp.1 ++ a' :: sp.2.2, t.dels, t.phs, t.aps⟩ := by
  refine ⟨rfl, rfl, fun μ => ?_⟩
  unfold abody
  simp only
  rw [hsp, aext_append, aext_append]
  simp only [aext]
  rw [hid, hv]

/-- The value of an atom that is constant: `d^0 = 1` and the low `0` digits, `0`. -/
def cstVal (a : Atom) : Option ℤ :=
  match a.f, a.args with
  | 7, [(p, _)] => if p = [] then some 1 else none
  | 10, [_, (p, _)] => if p = [] then some 0 else none
  | 2, [(p, M)] =>
    match ipConst p with
    | some c => if M.isConst then some (c % (M.c : ℤ)) else if c = 0 then some 0 else none
    | none => none
  | 13, [(p, _)] => if p = [] then some 0 else none
  | _, _ => none

theorem aval_cst (V : LV) (μ : ℕ → ℤ) (a : Atom) (c : ℤ) (h : cstVal a = some c) :
    aval V μ a = c := by
  unfold cstVal at h
  split at h
  · next p M hf hargs =>
    split_ifs at h with hp
    simp only [Option.some.injEq] at h
    subst h hp
    simp [aval, hf, hargs, bfn, argV, ipDen]
  · next q p M hf hargs =>
    split_ifs at h with hp
    simp only [Option.some.injEq] at h
    subst h hp
    simp [aval, hf, hargs, bfn, argV, ipDen]
  · next p M hf hargs =>
    split at h
    · next c hc =>
      split_ifs at h with hM hc0
      · simp only [Option.some.injEq] at h
        subst h
        simp [aval, hf, hargs, bfn, argV, ipConst_spec p c hc, DMon.den_isConst _ _ hM]
      · simp only [Option.some.injEq] at h
        subst h hc0
        simp [aval, hf, hargs, bfn, argV, ipConst_spec p 0 hc]
    · simp at h
  · next p M hf hargs =>
    split_ifs at h with hp
    simp only [Option.some.injEq] at h
    subst h hp
    simp [aval, hf, hargs, bfn, argV, ipDen]
  · simp at h

/-- A constant atom at the split `p`, substituted by its value. -/
def cstAt (t : ATm) (p : List Atom × Atom × List Atom) : Option ATm :=
  match cstVal p.2.1 with
  | some c =>
    if (ids p.2.2).contains p.2.1.id then none else
      some ⟨t.c, t.sums, p.1 ++ p.2.2.map (atSub p.2.1.id (ipC c)),
        t.dels.map (facSub p.2.1.id (ipC c)), t.phs.map (facSub p.2.1.id (ipC c)), t.aps⟩
  | none => none

theorem ipC_plain (l : List Atom) (c : ℤ) : plainP l (ipC c) = true := by
  unfold plainP ipVs ipC ipIns; split_ifs <;> simp

theorem ipC_has (x : ℕ) (c : ℤ) : ipHas x (ipC c) = false := by
  unfold ipHas ipC ipIns; split_ifs <;> simp

theorem cstAt_ok (V : LV) (t t' : ATm) (p : List Atom × Atom × List Atom)
    (hp : t.ats = p.1 ++ p.2.1 :: p.2.2) (h : cstAt t p = some t') : PWEq V t t' := by
  unfold cstAt at h
  split at h
  · next c hc =>
    split_ifs at h with hz
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.not_eq_true, List.contains_eq_mem, decide_eq_false_iff_not] at hz
    refine ⟨rfl, rfl, fun μ => ?_⟩
    unfold abody
    simp only
    rw [hp, aext_append, aext_append]
    simp only [aext]
    rw [aval_cst V _ _ c hc]
    have e := aext_sub V p.2.2 p.2.1.id hz (ipC c) (ipC_plain _ c) (ipC_has _ c) (aext V p.1 μ)
    rw [ipDen_C] at e
    rw [e, bodyOf_sub, ipDen_C]
  · simp at h

/-- Exclusive or with a zero argument read as the other argument reduced. -/
def xorZ (a : Atom) : Option Atom :=
  match a.f, a.args with
  | 1, [(p, M), (q, M2)] =>
    if q = [] ∧ M.c ≠ 0 then some { a with f := 2, args := [(p, M)] }
    else if p = [] ∧ M2.c ≠ 0 then some { a with f := 2, args := [(q, M2)] } else none
  | _, _ => none

theorem xorZ_ok (V : LV) (hρ : V.ρ.OK) (a a' : Atom) (h : xorZ a = some a') (μ : ℕ → ℤ) :
    aval V μ a' = aval V μ a := by
  unfold xorZ at h
  split at h
  · next p M q M2 hf hargs =>
    split_ifs at h with h1 h2
    · simp only [Option.some.injEq] at h
      subst h
      obtain ⟨rfl, hc⟩ := h1
      have hpos : 0 < M.den V.ρ.dv := DMon.den_pos _ hρ.dpos _ (Nat.pos_of_ne_zero hc)
      have h0 : 0 ≤ ipDen μ p % ((M.den V.ρ.dv : ℕ) : ℤ) := Int.emod_nonneg _ (by omega)
      simp [aval, hf, hargs, bfn, argV, ipDen_nil, Int.toNat_of_nonneg h0]
    · simp only [Option.some.injEq] at h
      subst h
      obtain ⟨rfl, hc⟩ := h2
      have hpos : 0 < M2.den V.ρ.dv := DMon.den_pos _ hρ.dpos _ (Nat.pos_of_ne_zero hc)
      have h0 : 0 ≤ ipDen μ q % ((M2.den V.ρ.dv : ℕ) : ℤ) := Int.emod_nonneg _ (by omega)
      simp [aval, hf, hargs, bfn, argV, ipDen_nil, Int.toNat_of_nonneg h0]
  · simp at h

/-- The reduced argument `mod(p, M)` for a constant `M`, its coefficients reduced modulo `M`. -/
def modC (a : Atom) : Option Atom :=
  match a.f, a.args with
  | 2, [(p, M)] =>
    if M.isConst ∧ M.c ≠ 0 ∧ ipModC M.c p ≠ p then some { a with args := [(ipModC M.c p, M)] }
    else none
  | _, _ => none

theorem modC_ok (V : LV) (a a' : Atom) (h : modC a = some a') (μ : ℕ → ℤ) :
    aval V μ a' = aval V μ a := by
  unfold modC at h
  split at h
  · next p M hf hargs =>
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    have hden : M.den V.ρ.dv = M.c := DMon.den_isConst _ _ hc.1
    simp only [aval, hf, hargs, show (2 : ℕ) < 100 by norm_num, if_true, bfn, List.map_cons,
      List.map_nil, argV, List.getD_cons_zero, hden]
    exact Int.modEq_iff_dvd.2 (ipDen_modC μ M.c p)
  · simp at h

/-- A digit product with its arguments in canonical order. -/
def ddotSwap (a : Atom) : Option Atom :=
  match a.f, a.args with
  | 0, [(p, M1), (q, M2)] =>
    if zLt (ipKey q ++ dmKey M2) (ipKey p ++ dmKey M1) then
      some { a with args := [(q, M2), (p, M1)] }
    else none
  | _, _ => none

theorem ddotSwap_ok (V : LV) (a a' : Atom) (h : ddotSwap a = some a') (μ : ℕ → ℤ) :
    aval V μ a' = aval V μ a := by
  unfold ddotSwap at h
  split at h
  · next p M1 q M2 hf hargs =>
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    simp only [aval, hf, hargs, show (0 : ℕ) < 100 by norm_num, if_true, bfn, List.map_cons,
      List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · simp at h

/-- A bit `mod(q, 2)`. -/
def isBit (a : Atom) : Bool :=
  a.f == 2 && match a.args with
    | [(_, M)] => M == ⟨2, []⟩
    | _ => false

/-- A power of two. -/
def isPw2 (a : Atom) : Bool := a.f == 7 && a.args.length == 1 && (a.dp == [] || a.dp == [⟨2, []⟩])

/-- The atom of a table with variable `z`. -/
def findAt (l : List Atom) (z : ℕ) : Option Atom := l.find? fun b => b.id == z

/-- `(a xor c (P - 1)) xor c P` as `a xor c (2 P - 1)`, `c` a bit, `P` a power of two, every
modulus a power of two. -/
def xorX (PW : List (DMon × DMon)) (pre : List Atom) (o : Atom) : Option Atom :=
  match o.f, o.args with
  | 1, [(A, M1), (Bq, M2)] =>
    match A, Bq with
    | [([w], 1)], [([u, v], 1)] =>
      match findAt pre w with
      | some wa =>
        match wa.f, wa.args with
        | 1, [(a, Ma), (C1, Mb)] =>
          if Ma = M1 ∧ Mb = M1 ∧ M2 = M1 ∧ (⟨2, []⟩, M1) ∈ PW then
            if (findAt pre u).any isBit ∧ (findAt pre v).any isPw2 ∧
                C1 = ipSub (ipMul (ipV u) (ipV v)) (ipV u) then
              some { o with args := [(a, M1), (ipSub (ipSmul 2 (ipMul (ipV u) (ipV v))) (ipV u), M1)] }
            else if (findAt pre v).any isBit ∧ (findAt pre u).any isPw2 ∧
                C1 = ipSub (ipMul (ipV v) (ipV u)) (ipV v) then
              some { o with args := [(a, M1), (ipSub (ipSmul 2 (ipMul (ipV v) (ipV u))) (ipV v), M1)] }
            else none
          else none
        | _, _ => none
      | none => none
    | _, _ => none
  | _, _ => none

theorem xor_mod_pow (a b k : ℕ) : (a % 2 ^ k) ^^^ (b % 2 ^ k) = (a ^^^ b) % 2 ^ k := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor, Nat.testBit_mod_two_pow]
  cases decide (i < k) <;> simp

theorem pow_xor_pow (m : ℕ) : (2 ^ m - 1) ^^^ 2 ^ m = 2 ^ (m + 1) - 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
  by_cases h : i < m
  · simp [h, show m ≠ i by omega, show i < m + 1 by omega]
  · by_cases h2 : m = i
    · subst h2; simp
    · simp [h, h2, show ¬ i < m + 1 by omega]

theorem toNat_mod_pow (z : ℕ) (k : ℕ) :
    ((z : ℤ) % ((2 ^ k : ℕ) : ℤ)).toNat = z % 2 ^ k := by
  rw [← Int.natCast_mod, Int.toNat_natCast]

theorem xor_step (A c N P : ℤ) (k m : ℕ) (hN : N = ((2 ^ k : ℕ) : ℤ))
    (hP : P = ((2 ^ m : ℕ) : ℤ)) (hc : c = 0 ∨ c = 1) :
    (((((((A % N).toNat ^^^ ((c * P - c) % N).toNat : ℕ) : ℤ) % N).toNat) ^^^ ((c * P) % N).toNat : ℕ) : ℤ) = (((A % N).toNat ^^^ ((2 * (c * P) - c) % N).toNat : ℕ) : ℤ) := by
  subst hN hP
  have hN : (0 : ℤ) < ((2 ^ k : ℕ) : ℤ) := by positivity
  have ha : (A % ((2 ^ k : ℕ) : ℤ)).toNat < 2 ^ k := by
    have := Int.emod_lt_of_pos A hN
    have h0 := Int.emod_nonneg A hN.ne'
    omega
  have hm : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rcases hc with rfl | rfl
  · simp only [zero_mul, sub_zero, mul_zero, Int.zero_emod, Int.toNat_zero, Nat.xor_zero]
    rw [toNat_mod_pow, Nat.mod_eq_of_lt ha]
  · simp only [one_mul]
    have e1 : ((2 ^ m : ℕ) : ℤ) - 1 = ((2 ^ m - 1 : ℕ) : ℤ) := by push_cast [hm]; ring
    have e2 : 2 * ((2 ^ m : ℕ) : ℤ) - 1 = ((2 ^ (m + 1) - 1 : ℕ) : ℤ) := by
      have : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
      push_cast [this]; ring
    rw [e1, e2, toNat_mod_pow, toNat_mod_pow, toNat_mod_pow]
    have hx : (A % ((2 ^ k : ℕ) : ℤ)).toNat ^^^ (2 ^ m - 1) % 2 ^ k < 2 ^ k :=
      Nat.xor_lt_two_pow ha (Nat.mod_lt _ (by positivity))
    rw [toNat_mod_pow, Nat.mod_eq_of_lt hx, Nat.xor_assoc, xor_mod_pow, pow_xor_pow]

theorem findAt_spec (l : List Atom) (z : ℕ) (b : Atom) (h : findAt l z = some b) :
    b ∈ l ∧ b.id = z := by
  unfold findAt at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem xorX_ok (V : LV) (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (pre : List Atom)
    (hw : wfA pre = true) (hn : (ids pre).Nodup) (o o' : Atom) (h : xorX PW pre o = some o')
    (μ : ℕ → ℤ) : aval V (aext V pre μ) o' = aval V (aext V pre μ) o := by
  set E := aext V pre μ
  have hfix : ∀ a ∈ pre, E a.id = aval V E a := aext_fix V pre hw hn μ
  have hbit : ∀ y, (findAt pre y).any isBit = true → E y = 0 ∨ E y = 1 := by
    intro y hy
    cases hb : findAt pre y with
    | none => simp [hb] at hy
    | some b =>
    rw [hb] at hy
    have hbb := hy
    simp only [Option.any_some] at hbb
    obtain ⟨hbm, hid⟩ := findAt_spec pre y b hb
    rw [← hid, hfix b hbm]
    unfold isBit at hbb
    simp only [Bool.and_eq_true, beq_iff_eq] at hbb
    obtain ⟨hf, hb2⟩ := hbb
    split at hb2
    · next q M hargs =>
      simp only [beq_iff_eq] at hb2
      subst hb2
      simp only [aval, hf, show (2 : ℕ) < 100 by norm_num, if_true, bfn, hargs, List.map_cons,
        List.map_nil, argV, List.getD_cons_zero]
      have : (DMon.den V.ρ.dv ⟨2, []⟩ : ℕ) = 2 := by simp [DMon.den, npow]
      rw [this]
      exact Int.emod_two_eq_zero_or_one _
    · simp at hb2
  have hpw : ∀ y, (findAt pre y).any isPw2 = true → ∃ m : ℕ, E y = ((2 ^ m : ℕ) : ℤ) := by
    intro y hy
    cases hb : findAt pre y with
    | none => simp [hb] at hy
    | some b =>
    rw [hb] at hy
    have hbb := hy
    simp only [Option.any_some] at hbb
    obtain ⟨hbm, hid⟩ := findAt_spec pre y b hb
    rw [← hid, hfix b hbm]
    unfold isPw2 at hbb
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hbb
    obtain ⟨⟨hf, -⟩, hdp⟩ := hbb
    refine ⟨((b.args.map (argV V.ρ.dv E)).getD 0 0).toNat, ?_⟩
    simp only [aval, hf, show (7 : ℕ) < 100 by norm_num, if_true, bfn]
    rcases hdp with hdp | hdp <;> simp [hdp, DMon.den, npow]
  unfold xorX at h
  split at h
  · next A M1 Bq M2 hf hargs =>
    split at h
    · next w u v =>
      split at h
      · next wa hwa =>
        split at h
        · next a Ma C1 Mb hwf hwargs =>
          split_ifs at h with hm h1 h2
          · simp only [Option.some.injEq] at h
            subst h
            obtain ⟨hMa, hMb, hM2, hpw2⟩ := hm
            rw [hMa, hMb] at hwargs
            rw [hM2] at hargs
            obtain ⟨hu, hv, hC⟩ := h1
            obtain ⟨-, k, hk⟩ := hPW _ hpw2
            have h2 : DMon.den V.ρ.dv ⟨2, []⟩ = 2 := by simp [DMon.den, npow]
            have hk' : M1.den V.ρ.dv = 2 ^ k := by rw [← h2]; exact hk
            obtain ⟨hwm, hwid⟩ := findAt_spec pre w wa hwa
            have hEw : E w = aval V E wa := by rw [← hwid, hfix wa hwm]
            obtain ⟨m, hm⟩ := hpw v hv
            have hc := hbit u hu
            simp only [aval, hf, show (1 : ℕ) < 100 by norm_num, if_true, bfn, hargs,
              List.map_cons, List.map_nil, argV, List.getD_cons_zero, List.getD_cons_succ]
            have ew : ipDen E [([w], 1)] = E w := by simp [ipDen, imDen]
            have euv : ipDen E [([u, v], 1)] = E u * E v := by simp [ipDen, imDen] <;> ring
            rw [ew, euv, hEw]
            simp only [aval, hwf, show (1 : ℕ) < 100 by norm_num, if_true, bfn, hwargs,
              List.map_cons, List.map_nil, argV, List.getD_cons_zero, List.getD_cons_succ]
            simp only [hC, ipDen_sub, ipDen_mul, ipDen_V, ipDen_smul, hk', hm]
            exact (xor_step _ _ _ _ k m rfl rfl hc).symm
          · simp only [Option.some.injEq] at h
            subst h
            obtain ⟨hMa, hMb, hM2, hpw2⟩ := hm
            rw [hMa, hMb] at hwargs
            rw [hM2] at hargs
            obtain ⟨hv, hu, hC⟩ := h2
            obtain ⟨-, k, hk⟩ := hPW _ hpw2
            have h2 : DMon.den V.ρ.dv ⟨2, []⟩ = 2 := by simp [DMon.den, npow]
            have hk' : M1.den V.ρ.dv = 2 ^ k := by rw [← h2]; exact hk
            obtain ⟨hwm, hwid⟩ := findAt_spec pre w wa hwa
            have hEw : E w = aval V E wa := by rw [← hwid, hfix wa hwm]
            obtain ⟨m, hm⟩ := hpw u hu
            have hc := hbit v hv
            simp only [aval, hf, show (1 : ℕ) < 100 by norm_num, if_true, bfn, hargs,
              List.map_cons, List.map_nil, argV, List.getD_cons_zero, List.getD_cons_succ]
            have ew : ipDen E [([w], 1)] = E w := by simp [ipDen, imDen]
            have euv : ipDen E [([u, v], 1)] = E v * E u := by simp [ipDen, imDen] <;> ring
            rw [ew, euv, hEw]
            simp only [aval, hwf, show (1 : ℕ) < 100 by norm_num, if_true, bfn, hwargs,
              List.map_cons, List.map_nil, argV, List.getD_cons_zero, List.getD_cons_succ]
            simp only [hC, ipDen_sub, ipDen_mul, ipDen_V, ipDen_smul, hk', hm]
            exact (xor_step _ _ _ _ k m rfl rfl hc).symm
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- `(P - 1) xor P` as `mod(2 P - 1, N)`, `P` a power of two, `N` a power of two. -/
def xorP (PW : List (DMon × DMon)) (pre : List Atom) (o : Atom) : Option Atom :=
  match o.f, o.args with
  | 1, [(A, M1), (Bq, M2)] =>
    match Bq with
    | [([z], 1)] =>
      if M2 = M1 ∧ (⟨2, []⟩, M1) ∈ PW ∧ (findAt pre z).any isPw2 ∧ A = ipSub (ipV z) (ipC 1) then
        some { o with f := 2, args := [(ipSub (ipSmul 2 (ipV z)) (ipC 1), M1)] }
      else none
    | _ => none
  | _, _ => none

theorem xorP_ok (V : LV) (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (pre : List Atom)
    (hw : wfA pre = true) (hn : (ids pre).Nodup) (o o' : Atom) (h : xorP PW pre o = some o')
    (μ : ℕ → ℤ) : aval V (aext V pre μ) o' = aval V (aext V pre μ) o := by
  set E := aext V pre μ
  have hfix : ∀ a ∈ pre, E a.id = aval V E a := aext_fix V pre hw hn μ
  unfold xorP at h
  split at h
  · next A M1 Bq M2 hf hargs =>
    split at h
    · next z =>
      split_ifs at h with hc
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hM, hpw, hz, hA⟩ := hc
      rw [hM, hA] at hargs
      obtain ⟨-, k, hk⟩ := hPW _ hpw
      have h2 : DMon.den V.ρ.dv ⟨2, []⟩ = 2 := by simp [DMon.den, npow]
      rw [h2] at hk
      have hm : ∃ m : ℕ, E z = ((2 ^ m : ℕ) : ℤ) := by
        cases hb : findAt pre z with
        | none => simp [hb] at hz
        | some b =>
        rw [hb] at hz
        simp only [Option.any_some] at hz
        obtain ⟨hbm, hid⟩ := findAt_spec pre z b hb
        rw [← hid, hfix b hbm]
        unfold isPw2 at hz
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hz
        obtain ⟨⟨hf7, -⟩, hdp⟩ := hz
        refine ⟨((b.args.map (argV V.ρ.dv E)).getD 0 0).toNat, ?_⟩
        simp only [aval, hf7, show (7 : ℕ) < 100 by norm_num, if_true, bfn]
        rcases hdp with hdp | hdp <;> simp [hdp, DMon.den, npow]
      obtain ⟨m, hm⟩ := hm
      have hmp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have hB : ipDen E [([z], 1)] = E z := by simp [ipDen, imDen]
      simp only [aval, hf, hargs, show (1 : ℕ) < 100 by norm_num, show (2 : ℕ) < 100 by norm_num,
        if_true, bfn, List.map_cons, List.map_nil, argV, List.getD_cons_zero, List.getD_cons_succ,
        ipDen_sub, ipDen_smul, ipDen_V, ipDen_C, hB, hm, hk]
      have hz1 : ((2 ^ m : ℕ) : ℤ) - 1 = ((2 ^ m - 1 : ℕ) : ℤ) := by push_cast [hmp]; ring
      have hz2 : 2 * ((2 ^ m : ℕ) : ℤ) - 1 = ((2 ^ (m + 1) - 1 : ℕ) : ℤ) := by
        have : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
        push_cast [this]; ring
      rw [hz1, hz2, toNat_mod_pow, toNat_mod_pow, xor_mod_pow, pow_xor_pow, Int.natCast_mod]
    · simp at h
  · simp at h

/-- The exclusive or of bit patterns at the split `sp` combined. -/
def xorAt (PW : List (DMon × DMon)) (t : ATm) (sp : List Atom × Atom × List Atom) : Option ATm :=
  match xorX PW sp.1 sp.2.1 with
  | some o' =>
    if wfA t.ats && (ids t.ats).Nodup then some ⟨t.c, t.sums, sp.1 ++ o' :: sp.2.2, t.dels, t.phs, t.aps⟩
    else none
  | none =>
    match xorP PW sp.1 sp.2.1 with
    | some o' =>
      if wfA t.ats && (ids t.ats).Nodup then some ⟨t.c, t.sums, sp.1 ++ o' :: sp.2.2, t.dels, t.phs, t.aps⟩
      else none
    | none => none

theorem xorAt_ok (V : LV) (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (t t' : ATm)
    (p : List Atom × Atom × List Atom) (hsp : t.ats = p.1 ++ p.2.1 :: p.2.2)
    (he : xorAt PW t p = some t') : PWEq V t t' := by
  unfold xorAt at he
  split at he
  · next o' ho =>
    split_ifs at he with hc
    simp only [Option.some.injEq] at he; subst he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [hsp] at hc
    have hw : wfA p.1 = true := wfA_append _ _ hc.1
    have hn : (ids p.1).Nodup := (List.nodup_append.1 (by simpa [ids] using hc.2)).1
    have hid : o'.id = p.2.1.id := by
      unfold xorX at ho
      repeat' (first | split at ho | split_ifs at ho)
      all_goals first | (simp only [Option.some.injEq] at ho; rw [← ho]) | simp at ho
    exact swap_pw V t p hsp o' hid fun μ => xorX_ok V PW hPW p.1 hw hn _ _ ho μ
  · split at he
    · next o' ho =>
      split_ifs at he with hc
      simp only [Option.some.injEq] at he; subst he
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rw [hsp] at hc
      have hw : wfA p.1 = true := wfA_append _ _ hc.1
      have hn : (ids p.1).Nodup := (List.nodup_append.1 (by simpa [ids] using hc.2)).1
      have hid : o'.id = p.2.1.id := by
        unfold xorP at ho
        repeat' (first | split at ho | split_ifs at ho)
        all_goals first | (simp only [Option.some.injEq] at ho; rw [← ho]) | simp at ho
      exact swap_pw V t p hsp o' hid fun μ => xorP_ok V PW hPW p.1 hw hn _ _ ho μ
    · simp at he

/-- An in-place atom rule at the split `sp`. -/
def swapAt (g : Atom → Option Atom) (t : ATm) (sp : List Atom × Atom × List Atom) : Option ATm :=
  match g sp.2.1 with
  | some a' => some ⟨t.c, t.sums, sp.1 ++ a' :: sp.2.2, t.dels, t.phs, t.aps⟩
  | none => none

/-- An atom read by later atoms, read as an earlier atom computing the same value. -/
def dedupA (t : ATm) (sp : List Atom × Atom × List Atom) : Option ATm :=
  match sp.1.find? (fun a => a.id != sp.2.1.id && sameAt a sp.2.1) with
  | some a =>
    if (ids t.ats).Nodup && sp.2.1.args.all (fun p => plainP t.ats p.1) &&
        (argVs sp.2.2).contains sp.2.1.id then
      some ⟨t.c, t.sums, sp.1 ++ sp.2.2.map (atSub sp.2.1.id (ipV a.id)),
        t.dels.map (facSub sp.2.1.id (ipV a.id)), t.phs.map (facSub sp.2.1.id (ipV a.id)), t.aps⟩
    else none
  | none => none

theorem dedupA_ok (V : LV) (t t' : ATm) (sp : List Atom × Atom × List Atom)
    (hsp : t.ats = sp.1 ++ sp.2.1 :: sp.2.2) (h : dedupA t sp = some t') : PWEq V t t' := by
  unfold dedupA at h
  split at h
  · next a ha =>
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hnd, hpl⟩, -⟩ := hc
    obtain ⟨ha1, ha2⟩ := List.find?_some ha |> fun h' => (⟨h', List.mem_of_find?_eq_some ha⟩ :
      _ ∧ a ∈ sp.1)
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, sameAt, beq_iff_eq] at ha1
    obtain ⟨hid, ⟨⟨⟨hf, hks⟩, hdp⟩, hargs⟩⟩ := ha1
    have hids : ids t.ats = ids sp.1 ++ ids (sp.2.1 :: sp.2.2) := by rw [hsp]; simp [ids]
    have hnd2 := hnd
    rw [hids] at hnd2
    obtain ⟨hpre, hrest, hdisj⟩ := List.nodup_append.1 hnd2
    have hbpost : sp.2.1.id ∉ ids sp.2.2 := (List.nodup_cons.1 (by simpa [ids] using hrest)).1
    have hain : a.id ∈ ids sp.1 := by simp only [ids]; exact List.mem_map_of_mem ha2
    have hapost : a.id ∉ ids sp.2.2 := fun h' =>
      hdisj a.id hain a.id (by simp only [ids, List.map_cons, List.mem_cons] at h' ⊢; exact Or.inr h') rfl
    refine ⟨rfl, rfl, fun μ => ?_⟩
    unfold abody
    simp only
    rw [hsp, aext_append, aext_append]
    simp only [aext]
    obtain ⟨μa, ha3, ha4⟩ := aext_find V sp.1 a.id a hpre (find_id _ hpre _ ha2) μ
    set P := aext V sp.1 μ
    have hval : aval V P sp.2.1 = P a.id := by
      rw [ha3]
      have : aval V P sp.2.1 = aval V μa sp.2.1 := by
        refine aval_reads V _ _ _ fun y hy => ?_
        simp only [atVs, List.mem_flatMap] at hy
        obtain ⟨p, hp, hy⟩ := hy
        have := hpl p hp
        simp only [plainP, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
          decide_eq_false_iff_not] at this
        have hy1 : y ∉ ids sp.1 := fun h' => this y hy (by rw [hids]; exact List.mem_append_left _ h')
        exact (aext_off V sp.1 μ y hy1).trans (ha4 y hy1).symm
      rw [this]
      unfold aval
      rw [hf, hks, hdp, hargs]
    rw [hval]
    have hv : P a.id = ipDen P (ipV a.id) := by rw [ipDen_V]
    have hpv : plainP sp.2.2 (ipV a.id) = true := by
      simp only [plainP, ipVs, ipV, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.all_cons, List.all_nil, Bool.and_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not]
      exact hapost
    have hhs : ipHas sp.2.1.id (ipV a.id) = false := by
      simp [ipHas, ipV, Ne.symm hid]
    have hapost' : a.id ∉ ids (sp.2.2.map (atSub sp.2.1.id (ipV a.id))) := by
      simpa [ids, atSub, List.map_map, Function.comp_def] using hapost
    rw [hv, aext_sub V sp.2.2 sp.2.1.id hbpost _ hpv hhs P, bodyOf_sub, ipDen_V, ipDen_V,
      aext_off V _ _ _ hapost']
  · simp at h

/-- In a table in dependency order, an atom read as an earlier atom computing the same value in the
factors. -/
def dedupW (t : ATm) (sp : List Atom × Atom × List Atom) : Option ATm :=
  match sp.1.find? (fun a => a.id != sp.2.1.id && sameAt a sp.2.1) with
  | some a =>
    if wfA t.ats && (ids t.ats).Nodup && (fvs t).contains sp.2.1.id then
      some ⟨t.c, t.sums, t.ats, t.dels.map (facSub sp.2.1.id (ipV a.id)),
        t.phs.map (facSub sp.2.1.id (ipV a.id)), t.aps⟩
    else none
  | none => none

theorem dedupW_ok (V : LV) (t t' : ATm) (sp : List Atom × Atom × List Atom)
    (hsp : t.ats = sp.1 ++ sp.2.1 :: sp.2.2) (h : dedupW t sp = some t') : PWEq V t t' := by
  unfold dedupW at h
  split at h
  · next a ha =>
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hw, hnd⟩, -⟩ := hc
    obtain ⟨ha1, ha2⟩ := List.find?_some ha |> fun h' => (⟨h', List.mem_of_find?_eq_some ha⟩ :
      _ ∧ a ∈ sp.1)
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, sameAt, beq_iff_eq] at ha1
    obtain ⟨-, ⟨⟨⟨hf, hks⟩, hdp⟩, hargs⟩⟩ := ha1
    refine ⟨rfl, rfl, fun μ => ?_⟩
    unfold abody
    simp only
    have hfix := aext_fix V t.ats hw hnd μ
    have hbm : sp.2.1 ∈ t.ats := by rw [hsp]; simp
    have ham : a ∈ t.ats := by rw [hsp]; exact List.mem_append_left _ ha2
    have hval : aext V t.ats μ sp.2.1.id = aext V t.ats μ a.id := by
      rw [hfix _ hbm, hfix _ ham]
      unfold aval
      rw [hf, hks, hdp, hargs]
    rw [bodyOf_sub, ipDen_V, ← hval, Function.update_eq_self]
  · simp at h

/-- Under a delta `[M ∣ s o + B]`, `s = ±1`, the atom at the split `sp` read with `o` set to `-s B`,
its arguments reading `o` reduced modulo divisors of `M`. -/
def dsubAt (t : ATm) (sp : List Atom × Atom × List Atom) : Option ATm :=
  match firstSome (fun o : ℕ =>
      firstSome (fun f : Fac =>
        match ipLin o f.2 with
        | some (A, B) =>
          match ipConst A with
          | some s =>
            if (s == 1 || s == -1) && f.1.c != 0 && !(ids t.ats).contains o &&
                (ipVs B).all (fun y => !(ids (sp.2.1 :: sp.2.2)).contains y) &&
                sp.2.1.args.all (fun p => !ipHas o p.1 || p.2.dvd f.1) then
              some ⟨t.c, t.sums, sp.1 ++ atSub o (pinVal s B) sp.2.1 :: sp.2.2, t.dels, t.phs, t.aps⟩
            else none
          | none => none
        | none => none) t.dels) (atVs sp.2.1) with
  | some t' => if wfA t.ats && (ids t.ats).Nodup then some t' else none
  | none => none

theorem dsubAt_ok (V : LV) (hρ : V.ρ.OK) (t t' : ATm) (sp : List Atom × Atom × List Atom)
    (hsp : t.ats = sp.1 ++ sp.2.1 :: sp.2.2) (h : dsubAt t sp = some t') : PWEq V t t' := by
  unfold dsubAt at h
  split at h
  swap
  · simp at h
  rename_i t'' hfs
  split_ifs at h with hwn
  simp only [Option.some.injEq] at h
  subst h
  have h := hfs
  obtain ⟨o, -, h⟩ := firstSome_spec _ _ _ h
  obtain ⟨f, hf, h⟩ := firstSome_spec _ _ _ h
  split at h
  · next A B hlin =>
    split at h
    · next s hs =>
      split_ifs at h with hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
        Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, List.all_eq_true] at hc
      obtain ⟨⟨⟨⟨hs1, hc0⟩, hoi⟩, hB⟩, hargs⟩ := hc
      obtain ⟨-, -, hp⟩ := ipLin_spec o f.2 A B hlin
      have hsv : ∀ ν, ipDen ν A = s := fun ν => ipConst_spec A s hs ν
      have hpos : 0 < f.1.den V.ρ.dv := DMon.den_pos _ hρ.dpos _ (Nat.pos_of_ne_zero hc0)
      have hoi' : o ∉ ids (sp.2.1 :: sp.2.2) := fun h' => hoi (by
        rw [hsp]; simp only [ids, List.map_append, List.mem_append] at h' ⊢; exact Or.inr h')
      refine ⟨rfl, rfl, fun μ => ?_⟩
      unfold abody
      simp only
      rw [hsp, aext_append, aext_append]
      simp only [aext]
      set P := aext V sp.1 μ
      set v := pinVal s B
      have hread : ∀ w : ℤ, ipDen (aext V sp.2.2 (Function.update P sp.2.1.id w)) f.2 =
          s * P o + ipDen P B := by
        intro w
        rw [hp, hsv]
        have h1 : aext V sp.2.2 (Function.update P sp.2.1.id w) o = P o := by
          simp only [ids, List.map_cons, List.mem_cons, not_or] at hoi'
          rw [aext_off V _ _ _ hoi'.2, Function.update_of_ne hoi'.1]
        have h2 : ipDen (aext V sp.2.2 (Function.update P sp.2.1.id w)) B = ipDen P B := by
          refine ipDen_reads B _ _ fun y hy => ?_
          have := hB y hy
          simp only [ids, List.map_cons, List.mem_cons, not_or] at this
          rw [aext_off V _ _ _ this.2, Function.update_of_ne this.1]
        rw [h1, h2]
      by_cases hd : ((f.1.den V.ρ.dv : ℕ) : ℤ) ∣ s * P o + ipDen P B
      · have hd' : ((f.1.den V.ρ.dv : ℕ) : ℤ) ∣ ipDen P v - P o := by
          have := (pin_dvd s hs1 _ (P o) (ipDen P B)).1 hd
          rw [show ipDen P v = -s * ipDen P B by simp [v, pinVal, ipDen_smul]]
          exact (dvd_neg.2 this).trans (by ring_nf; exact dvd_refl _)
        have hval : aval V P (atSub o v sp.2.1) = aval V P sp.2.1 := by
          have : (atSub o v sp.2.1).args.map (argV V.ρ.dv P) = sp.2.1.args.map (argV V.ρ.dv P) := by
            simp only [atSub, List.map_map]
            refine List.map_congr_left fun p hpm => ?_
            simp only [Function.comp_apply, argV, ipDen_subst]
            have := argV_congr V.ρ.dv hρ.dpos o f.1 p (by simpa using hargs p hpm) P _ _ hd'
            simp only [argV, Function.update_eq_self] at this
            exact this
          unfold aval; rw [this]; rfl
        simp only [atSub] at hval ⊢
        rw [hval]
      · have hz : ∀ w : ℤ, bodyOf V.ρ.dv t.dels t.phs
            (aext V sp.2.2 (Function.update P sp.2.1.id w)) = 0 := by
          intro w
          unfold bodyOf
          rw [List.prod_eq_zero (List.mem_map.2 ⟨f, hf, by unfold delV; rw [hread w, if_neg hd]⟩),
            zero_mul]
        simp only [atSub]
        rw [hz, hz]
    · simp at h
  · simp at h

/-! ## Digit products of exclusive ors modulo two -/

theorem atVsMk (id f : ℕ) (ks : List ℤ) (dp : List DMon) (args : List (IPoly × DMon)) :
    atVs ⟨id, f, ks, dp, args⟩ = args.flatMap fun p => ipVs p.1 := rfl

theorem dig2_xor (i x y : ℕ) : (x ^^^ y) / 2 ^ i % 2 = (x / 2 ^ i % 2 + y / 2 ^ i % 2) % 2 := by
  have key : ∀ m : ℕ, m / 2 ^ i % 2 = if m.testBit i then 1 else 0 := by
    intro m
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have := Nat.mod_two_eq_zero_or_one (m / 2 ^ i)
    rcases this with h | h <;> simp [h]
  rw [key, key x, key y, Nat.testBit_xor]
  cases x.testBit i <;> cases y.testBit i <;> simp

theorem ddot2_xor (S : Finset ℕ) (x y c : ℕ) :
    (2 : ℤ) ∣ (∑ i ∈ S, dig 2 i ((x ^^^ y : ℕ) : ℤ) * dig 2 i (c : ℤ)) -
      ((∑ i ∈ S, dig 2 i (x : ℤ) * dig 2 i (c : ℤ)) + ∑ i ∈ S, dig 2 i (y : ℤ) * dig 2 i (c : ℤ)) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun i _ => ?_
  simp only [dig_nat, dig2_xor]
  set a := x / 2 ^ i % 2
  set b := y / 2 ^ i % 2
  set c' := c / 2 ^ i % 2
  have h' : (((a + b) % 2 : ℕ) : ℤ) = (a : ℤ) + b - 2 * (((a + b) / 2 : ℕ) : ℤ) := by omega
  rw [h']
  exact ⟨-(((a + b) / 2 : ℕ) : ℤ) * c', by ring⟩

/-- The operands `(u, v)` of an exclusive or `X = w`, both reduced modulo `N`, `w` an atom of
`pre`. -/
def xorOf (pre : List Atom) (X : IPoly) (N : DMon) : Option (IPoly × IPoly) :=
  match X with
  | [([w], 1)] =>
    match findAt pre w with
    | some wa =>
      match wa.f, wa.args with
      | 1, [(u, Mu), (v, Mv)] => if Mu = N ∧ Mv = N then some (u, v) else none
      | _, _ => none
    | none => none
  | _ => none

/-- `ddot_{2,N}(u xor v, c)` as the atoms `ddot(u, c)` and `ddot(v, c)` from `B`, either argument
an exclusive or. -/
def dotXor (PW : List (DMon × DMon)) (pre : List Atom) (a : Atom) (B : ℕ) : Option (Atom × Atom) :=
  match a.f, a.dp, a.args with
  | 0, [d, N], [(X, M1), (Cp, M2)] =>
    if d = ⟨2, []⟩ ∧ M1 = N ∧ M2 = N ∧ (⟨2, []⟩, N) ∈ PW then
      match xorOf pre X N with
      | some (u, v) => some (⟨B, 0, a.ks, [d, N], [(u, N), (Cp, N)]⟩,
          ⟨B + 1, 0, a.ks, [d, N], [(v, N), (Cp, N)]⟩)
      | none =>
        match xorOf pre Cp N with
        | some (u, v) => some (⟨B, 0, a.ks, [d, N], [(X, N), (u, N)]⟩,
            ⟨B + 1, 0, a.ks, [d, N], [(X, N), (v, N)]⟩)
        | none => none
    else none
  | _, _, _ => none

theorem xorOf_spec (V : LV) (pre : List Atom) (hw : wfA pre = true) (hn : (ids pre).Nodup)
    (X : IPoly) (N : DMon) (u v : IPoly) (h : xorOf pre X N = some (u, v)) (μ : ℕ → ℤ) :
    ipDen (aext V pre μ) X = (((argV V.ρ.dv (aext V pre μ) (u, N)).toNat ^^^
      (argV V.ρ.dv (aext V pre μ) (v, N)).toNat : ℕ) : ℤ) ∧
      ∀ y ∈ ipVs u ++ ipVs v, y ∈ argVs pre := by
  unfold xorOf at h
  split at h
  · next w =>
    split at h
    · next wa hwa =>
      split at h
      · next u' Mu v' Mv hf hargs =>
        split_ifs at h with hM
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨rfl, rfl⟩ := hM
        obtain ⟨hwm, hwid⟩ := findAt_spec pre w wa hwa
        refine ⟨?_, fun y hy => List.mem_flatMap.2 ⟨wa, hwm, ?_⟩⟩
        · have : ipDen (aext V pre μ) [([w], 1)] = aext V pre μ w := by simp [ipDen, imDen]
          rw [this, ← hwid, aext_fix V pre hw hn μ wa hwm]
          simp only [aval, hf, show (1 : ℕ) < 100 by norm_num, if_true, bfn, hargs, List.map_cons,
            List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
        · simp only [atVs, hargs, List.flatMap_cons, List.flatMap_nil, List.append_nil]
          exact hy
      · simp at h
    · simp at h
  · simp at h

theorem dotXor_ok (V : LV) (hPW : PowOK PW V.ρ) (pre : List Atom) (hw : wfA pre = true)
    (hn : (ids pre).Nodup) (a b1 b2 : Atom) (B : ℕ) (h : dotXor PW pre a B = some (b1, b2))
    (μ : ℕ → ℤ) :
    b1.id = B ∧ b2.id = B + 1 ∧ (∀ y ∈ atVs b1 ++ atVs b2, y ∈ atVs a ∨ y ∈ argVs pre) ∧
      (2 : ℤ) ∣ aval V (aext V pre μ) a -
        (aval V (aext V pre μ) b1 + aval V (aext V pre μ) b2) := by
  unfold dotXor at h
  split at h
  · next d N X M1 Cp M2 hf hdp hargs =>
    split_ifs at h with hc
    obtain ⟨hd, hN, hM2, hpw⟩ := hc
    subst hd
    rw [hN, hM2] at hargs
    obtain ⟨-, k, hk⟩ := hPW _ hpw
    have h2 : DMon.den V.ρ.dv ⟨2, []⟩ = 2 := by simp [DMon.den, npow]
    rw [h2] at hk
    set E := aext V pre μ
    have hlt : ∀ z : ℤ, (z % ((N.den V.ρ.dv : ℕ) : ℤ)).toNat < 2 ^ k := by
      intro z
      have hpos : (0 : ℤ) < ((N.den V.ρ.dv : ℕ) : ℤ) := by rw [hk]; positivity
      have := Int.emod_lt_of_pos z hpos
      have h0 := Int.emod_nonneg z hpos.ne'
      rw [hk] at this h0 ⊢
      omega
    have hnn : ∀ z : ℤ, z % ((N.den V.ρ.dv : ℕ) : ℤ) =
        (((z % ((N.den V.ρ.dv : ℕ) : ℤ)).toNat : ℕ) : ℤ) := fun z =>
      (Int.toNat_of_nonneg (Int.emod_nonneg z (by rw [hk]; positivity))).symm
    have hxor : ∀ x y : ℕ, x < 2 ^ k → y < 2 ^ k →
        (((x ^^^ y : ℕ) : ℤ) % ((N.den V.ρ.dv : ℕ) : ℤ)) = ((x ^^^ y : ℕ) : ℤ) := fun x y hx hy =>
      Int.emod_eq_of_lt (by positivity) (by rw [hk]; exact_mod_cast Nat.xor_lt_two_pow hx hy)
    split at h
    · next u v huv =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hX, hvars⟩ := xorOf_spec V pre hw hn X N u v huv μ
      refine ⟨rfl, rfl, fun y hy => ?_, ?_⟩
      · simp only [atVsMk, List.mem_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil] at hy
        rcases hy with (hy | hy) | (hy | hy)
        · exact Or.inr (hvars y (List.mem_append_left _ hy))
        · exact Or.inl (by simp [atVs, hargs, hy])
        · exact Or.inr (hvars y (List.mem_append_right _ hy))
        · exact Or.inl (by simp [atVs, hargs, hy])
      · simp only [aval, hf, hdp, hargs, show (0 : ℕ) < 100 by norm_num, if_true, bfn,
          List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ, h2]
        simp only [argV] at hX ⊢
        rw [hX, hxor _ _ (hlt _) (hlt _), hnn (ipDen E u), hnn (ipDen E v), hnn (ipDen E Cp)]
        simp only [Int.toNat_natCast]
        exact ddot2_xor _ _ _ _
    · next hnone =>
      split at h
      · next u v huv =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hC, hvars⟩ := xorOf_spec V pre hw hn Cp N u v huv μ
        refine ⟨rfl, rfl, fun y hy => ?_, ?_⟩
        · simp only [atVsMk, List.mem_append, List.flatMap_cons, List.flatMap_nil,
            List.append_nil] at hy
          rcases hy with (hy | hy) | (hy | hy)
          · exact Or.inl (by simp [atVs, hargs, hy])
          · exact Or.inr (hvars y (List.mem_append_left _ hy))
          · exact Or.inl (by simp [atVs, hargs, hy])
          · exact Or.inr (hvars y (List.mem_append_right _ hy))
        · simp only [aval, hf, hdp, hargs, show (0 : ℕ) < 100 by norm_num, if_true, bfn,
            List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ, h2]
          simp only [argV] at hC ⊢
          rw [hC, hxor _ _ (hlt _) (hlt _), hnn (ipDen E u), hnn (ipDen E v), hnn (ipDen E X)]
          simp only [Int.toNat_natCast]
          have := ddot2_xor (pos 2 (N.den V.ρ.dv)) ((ipDen E u % ((N.den V.ρ.dv : ℕ) : ℤ)).toNat)
            ((ipDen E v % ((N.den V.ρ.dv : ℕ) : ℤ)).toNat)
            ((ipDen E X % ((N.den V.ρ.dv : ℕ) : ℤ)).toNat)
          simpa only [mul_comm] using this
      · simp at h
  · simp at h

/-- The digit product at the split `sp` of an exclusive or, read only by roots of unity of order
`2`, as the sum of two digit products. -/
def dotXorAt (PW : List (DMon × DMon)) (t : ATm) (sp : List Atom × Atom × List Atom) :
    Option ATm :=
  match dotXor PW sp.1 sp.2.1 (maxV t + 1) with
  | some (b1, b2) =>
    if wfA t.ats && (ids t.ats).Nodup && !(argVs t.ats).contains sp.2.1.id &&
        t.dels.all (fun g => !facHas sp.2.1.id g) &&
        t.phs.all (fun g => !facHas sp.2.1.id g || g.1 == ⟨2, []⟩) &&
        (fvs t).contains sp.2.1.id then
      some ⟨t.c, t.sums, sp.1 ++ b1 :: b2 :: sp.2.1 :: sp.2.2,
        t.dels.map (facSub sp.2.1.id (ipAdd (ipV (maxV t + 1)) (ipV (maxV t + 2)))),
        t.phs.map (facSub sp.2.1.id (ipAdd (ipV (maxV t + 1)) (ipV (maxV t + 2)))), t.aps⟩
    else none
  | none => none

theorem dotXorAt_ok (V : LV) (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (t t' : ATm)
    (sp : List Atom × Atom × List Atom) (hsp : t.ats = sp.1 ++ sp.2.1 :: sp.2.2)
    (h : dotXorAt PW t sp = some t') : PWEq V t t' := by
  unfold dotXorAt at h
  split at h
  · next b1 b2 hb =>
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
      List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨hw, hnd⟩, hna⟩, hds⟩, hps⟩, -⟩ := hc
    set B := maxV t + 1
    have hlt : ∀ v ∈ allV t, v < B := fun v hv => Nat.lt_succ_of_le (le_foldr_max _ v hv)
    have hall : ∀ v, v ∈ fvs t ∨ v ∈ argVs t.ats ∨ v ∈ ids t.ats → v < B := fun v hv =>
      hlt v (by simp only [allV, rvs, List.mem_append]; tauto)
    rw [hsp] at hw hnd
    have hwp : wfA sp.1 = true := wfA_append _ _ hw
    have hnp : (ids sp.1).Nodup := (List.nodup_append.1 (by simpa [ids] using hnd)).1
    have hid : ∀ v ∈ ids (sp.1 ++ sp.2.1 :: sp.2.2), v < B := fun v hv =>
      hall v (Or.inr (Or.inr (by rw [hsp]; exact hv)))
    have harg : ∀ v ∈ argVs (sp.1 ++ sp.2.1 :: sp.2.2), v < B := fun v hv =>
      hall v (Or.inr (Or.inl (by rw [hsp]; exact hv)))
    have haid : sp.2.1.id < B := hid _ (by simp [ids])
    refine ⟨rfl, rfl, fun μ => ?_⟩
    obtain ⟨hb1, hb2, hrd, hdv⟩ := dotXor_ok V hPW sp.1 hwp hnp sp.2.1 b1 b2 B hb μ
    unfold abody
    simp only
    rw [hsp, aext_append, aext_append]
    simp only [aext]
    set E0 := aext V sp.1 μ
    have hrdB : ∀ y ∈ atVs b1 ++ atVs b2, y < B := fun y hy => by
      rcases hrd y hy with h1 | h1
      · exact harg y (by simp only [argVs, List.flatMap_append, List.flatMap_cons, List.mem_append]; tauto)
      · exact harg y (by simp only [argVs, List.flatMap_append, List.mem_append] at h1 ⊢; tauto)
    have haB : ∀ y ∈ atVs sp.2.1, y < B := fun y hy =>
      harg y (by simp only [argVs, List.flatMap_append, List.flatMap_cons, List.mem_append]; tauto)
    have e1 : aval V (Function.update E0 b1.id (aval V E0 b1)) b2 = aval V E0 b2 :=
      aval_reads V b2 _ _ fun y hy => Function.update_of_ne (by
        have := hrdB y (List.mem_append_right _ hy); omega) _ _
    rw [e1]
    set E2 := Function.update (Function.update E0 b1.id (aval V E0 b1)) b2.id (aval V E0 b2)
    have e2 : aval V E2 sp.2.1 = aval V E0 sp.2.1 :=
      aval_reads V _ _ _ fun y hy => by
        have := haB y hy
        simp only [E2]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    rw [e2]
    set F' := aext V sp.2.2 (Function.update E2 sp.2.1.id (aval V E0 sp.2.1))
    set F := aext V sp.2.2 (Function.update E0 sp.2.1.id (aval V E0 sp.2.1))
    have hFF : ∀ v ∈ allV t, F' v = F v := by
      refine aext_agree V sp.2.2 (allV t) (fun v hv => ?_) _ _ (fun v hv => ?_)
      · rcases List.mem_append.1 hv with hv | hv
        · simp only [allV, rvs, List.mem_append]; left; left; right
          rw [hsp]; simp only [argVs, List.flatMap_append, List.flatMap_cons, List.mem_append]; tauto
        · simp only [allV, rvs, List.mem_append]; left; right
          rw [hsp]; simp only [ids, List.map_append, List.map_cons, List.mem_append, List.mem_cons]; tauto
      · have := hlt v hv
        by_cases e : v = sp.2.1.id
        · subst e; simp
        · simp only [E2]
          rw [Function.update_of_ne e, Function.update_of_ne e, Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
    have hpost : ∀ v ∈ ids sp.2.2, v < B := fun v hv => hid v (by
      simp only [ids, List.map_append, List.map_cons, List.mem_append, List.mem_cons] at hv ⊢; tauto)
    have hFB : F' B = aval V E0 b1 := by
      have h1 : F' B = E2 B := by
        simp only [F']
        rw [aext_off V _ _ _ (fun h' => by have := hpost B h'; omega), Function.update_of_ne (by omega)]
      rw [h1]
      simp only [E2]
      rw [Function.update_of_ne (by rw [hb2]; omega), hb1, Function.update_self]
    have hFB1 : F' (B + 1) = aval V E0 b2 := by
      have h1 : F' (B + 1) = E2 (B + 1) := by
        simp only [F']
        rw [aext_off V _ _ _ (fun h' => by have := hpost (B + 1) h'; omega),
          Function.update_of_ne (by omega)]
      rw [h1]
      simp only [E2]
      rw [hb2, Function.update_self]
    have hFa : F' sp.2.1.id = aval V E0 sp.2.1 := by
      simp only [F']
      rw [aext_off V _ _ _ (fun h' => by
        have := (List.nodup_append.1 (by simpa [ids] using hnd)).2.1
        simp only [ids, List.map_cons, List.nodup_cons] at this
        exact this.1 h'), Function.update_self]
    rw [bodyOf_sub, ipDen_add, ipDen_V, ipDen_V, hFB, show maxV t + 2 = B + 1 by rfl, hFB1]
    have hfv : ∀ g ∈ t.dels ++ t.phs, ∀ y ∈ facVars g, y < B := fun g hg y hy =>
      hall y (Or.inl (fvs_fac (List.mem_flatMap.2 ⟨g, hg, hy⟩)))
    have hgF : ∀ g ∈ t.dels ++ t.phs, ipDen F' g.2 = ipDen F g.2 := fun g hg =>
      ipDen_reads _ _ _ fun y hy => hFF y (by
        simp only [allV, rvs, List.mem_append]; left; left; left
        exact fvs_fac (List.mem_flatMap.2 ⟨g, hg, hy⟩))
    have hs2 : (2 : ℤ) ∣ (aval V E0 b1 + aval V E0 b2) - F' sp.2.1.id := by
      rw [hFa, ← neg_sub]; exact dvd_neg.2 hdv
    congr 1
    unfold bodyOf
    congr 1
    · congr 1; refine List.map_congr_left fun g hg => ?_
      have hn : ipHas sp.2.1.id g.2 = false := by simpa [facHas] using hds g hg
      unfold delV; rw [ipDen_upd_of _ _ _ _ hn, hgF g (List.mem_append_left _ hg)]
    · congr 1; refine List.map_congr_left fun g hg => ?_
      unfold phV
      rcases hps g hg with hn | h2g
      · have hn' : ipHas sp.2.1.id g.2 = false := by simpa [facHas] using hn
        rw [ipDen_upd_of _ _ _ _ hn', hgF g (List.mem_append_right _ hg)]
      · rw [← hgF g (List.mem_append_right _ hg), h2g]
        have hd2 : DMon.den V.ρ.dv ⟨2, []⟩ = 2 := by simp [DMon.den, npow]
        rw [hd2]
        apply om_zpow_congr 2 (by norm_num)
        have := hs2.trans (ipDen_upd_dvd F' sp.2.1.id _ (F' sp.2.1.id) g.2)
        rw [Function.update_eq_self] at this
        exact_mod_cast this
  · simp at h

/-! ## Remainders modulo a dimension less one -/

/-- Whether `z` is a remainder modulo `N - 1` of the table `l`. -/
def isM1 (l : List Atom) (z : ℕ) (N : DMon) : Bool :=
  (findAt l z).any fun b => b.f == 13 && b.dp == [N] && b.args.length == 1

/-- Whether `w` is the value of `N` in the table `l`. -/
def isDim (l : List Atom) (w : ℕ) (N : DMon) : Bool :=
  (findAt l w).any fun b => b.f == 8 && b.dp == [N] && b.args.isEmpty

theorem m1_val (V : LV) (pre : List Atom) (hw : wfA pre = true) (hn : (ids pre).Nodup)
    (z : ℕ) (N : DMon) (h : isM1 pre z N = true) (μ : ℕ → ℤ) :
    ∃ X : ℤ, aext V pre μ z = X % ((N.den V.ρ.dv : ℤ) - 1) := by
  unfold isM1 at h
  cases hb : findAt pre z with
  | none => simp [hb] at h
  | some b =>
    rw [hb] at h
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hf, hdp⟩, -⟩ := h
    obtain ⟨hbm, hid⟩ := findAt_spec pre z b hb
    rw [← hid, aext_fix V pre hw hn μ b hbm]
    refine ⟨((b.args.map (argV V.ρ.dv (aext V pre μ))).getD 0 0), ?_⟩
    simp [aval, hf, hdp, bfn]

theorem dim_val (V : LV) (pre : List Atom) (hw : wfA pre = true) (hn : (ids pre).Nodup)
    (w : ℕ) (N : DMon) (h : isDim pre w N = true) (μ : ℕ → ℤ) :
    aext V pre μ w = (N.den V.ρ.dv : ℤ) := by
  unfold isDim at h
  cases hb : findAt pre w with
  | none => simp [hb] at h
  | some b =>
    rw [hb] at h
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
    obtain ⟨⟨hf, hdp⟩, ha⟩ := h
    obtain ⟨hbm, hid⟩ := findAt_spec pre w b hb
    rw [← hid, aext_fix V pre hw hn μ b hbm]
    simp [aval, hf, hdp, ha, bfn]

/-- Whether `u` is `mod(-1, N)` in the table `l`. -/
def isNeg1 (l : List Atom) (u : ℕ) (N : DMon) : Bool :=
  (findAt l u).any fun b => b.f == 2 && b.args == [(ipC (-1), N)]

theorem neg1_val (V : LV) (pre : List Atom) (hw : wfA pre = true) (hn : (ids pre).Nodup)
    (u : ℕ) (N : DMon) (h : isNeg1 pre u N = true) (μ : ℕ → ℤ) :
    ((N.den V.ρ.dv : ℤ) - 1) ∣ aext V pre μ u := by
  unfold isNeg1 at h
  cases hb : findAt pre u with
  | none => simp [hb] at h
  | some b =>
    rw [hb] at h
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hf, ha⟩ := h
    obtain ⟨hbm, hid⟩ := findAt_spec pre u b hb
    rw [← hid, aext_fix V pre hw hn μ b hbm]
    simp only [aval, hf, ha, show (2 : ℕ) < 100 by norm_num, if_true, bfn, List.map_cons,
      List.map_nil, List.getD_cons_zero, argV, ipDen_C]
    rcases Nat.eq_zero_or_pos (N.den V.ρ.dv) with h0 | h0
    · rw [h0]; exact ⟨-(-1 % ((0 : ℕ) : ℤ)), by ring⟩
    · have : (-1 : ℤ) % ((N.den V.ρ.dv : ℕ) : ℤ) = (N.den V.ρ.dv : ℤ) - 1 := by
        rw [show (-1 : ℤ) = ((N.den V.ρ.dv : ℤ) - 1) + (-1) * (N.den V.ρ.dv : ℤ) by ring,
          Int.add_mul_emod_self_right]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      rw [this]

/-- Inside a remainder modulo `N - 1`, a remainder modulo `N - 1` read as its argument, the
value of `N` read as `1` and `mod(-1, N)` read as `0`. -/
def m1Arg (pre : List Atom) (a : Atom) : Option Atom :=
  match a.f, a.dp, a.args with
  | 13, [N], [(P, Z)] =>
    if Z = ZM then
      match (ipVs P).find? (fun z => isM1 pre z N) with
      | some z =>
        match findAt pre z with
        | some b =>
          match b.args with
          | [(q, Zb)] => if Zb = ZM then some { a with args := [(ipSubst z q P, ZM)] } else none
          | _ => none
        | none => none
      | none =>
        match (ipVs P).find? (fun w => isDim pre w N) with
        | some w => some { a with args := [(ipSubst w (ipC 1) P, ZM)] }
        | none =>
          match (ipVs P).find? (fun u => isNeg1 pre u N) with
          | some u => some { a with args := [(ipSubst u (ipC 0) P, ZM)] }
          | none => none
    else none
  | _, _, _ => none

theorem emod_congr_sub (m a b c : ℤ) (h : m ∣ a - b) (hc : m ∣ c - b) : a % m = c % m :=
  ((Int.modEq_iff_dvd.2 h).symm.trans (Int.modEq_iff_dvd.2 hc))

theorem m1Arg_ok (V : LV) (pre : List Atom) (hw : wfA pre = true) (hn : (ids pre).Nodup)
    (a a' : Atom) (h : m1Arg pre a = some a') (μ : ℕ → ℤ) :
    aval V (aext V pre μ) a' = aval V (aext V pre μ) a := by
  set E := aext V pre μ
  unfold m1Arg at h
  split at h
  · next N P Z hf hdp hargs =>
    split_ifs at h with hZ
    subst hZ
    split at h
    · next z hz =>
      have hzm := List.find?_some hz
      split at h
      · next b hb =>
        split at h
        · next q Zb hbargs =>
          split_ifs at h with hZb
          subst hZb
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨hbm, hid⟩ := findAt_spec pre z b hb
          have hEz : E z = ipDen E q % ((N.den V.ρ.dv : ℤ) - 1) := by
            rw [← hid]
            show aext V pre μ b.id = _
            rw [aext_fix V pre hw hn μ b hbm]
            have hb13 : b.f = 13 ∧ b.dp = [N] := by
              unfold isM1 at hzm; rw [hb] at hzm
              simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hzm
              exact hzm.1
            simp [aval, hb13.1, hb13.2, hbargs, bfn, argV_zm]
            rfl
          simp only [aval, hf, hdp, hargs, show (13 : ℕ) < 100 by norm_num, if_true, bfn,
            List.map_cons, List.map_nil, List.getD_cons_zero, argV_zm]
          rw [ipDen_subst]
          refine emod_congr_sub _ _ (ipDen (Function.update E z (E z)) P) _ ?_ ?_
          · have := ipDen_upd_dvd E z (ipDen E q) (E z) P
            refine (dvd_trans ?_ this)
            rw [hEz, Int.emod_def]; exact ⟨ipDen E q / ((N.den V.ρ.dv : ℤ) - 1), by ring⟩
          · rw [Function.update_eq_self]; simp
        · simp at h
      · simp at h
    · next hz =>
      split at h
      · next w hwf =>
        have hwm := List.find?_some hwf
        simp only [Option.some.injEq] at h
        subst h
        have hEw : E w = (N.den V.ρ.dv : ℤ) := dim_val V pre hw hn w N hwm μ
        simp only [aval, hf, hdp, hargs, show (13 : ℕ) < 100 by norm_num, if_true, bfn,
          List.map_cons, List.map_nil, List.getD_cons_zero, argV_zm]
        rw [ipDen_subst, ipDen_C]
        refine emod_congr_sub _ _ (ipDen (Function.update E w (E w)) P) _ ?_ ?_
        · have := ipDen_upd_dvd E w 1 (E w) P
          refine dvd_trans ?_ this
          rw [hEw]; exact ⟨-1, by ring⟩
        · rw [Function.update_eq_self]; simp
      · split at h
        · next u huf =>
          have hum := List.find?_some huf
          simp only [Option.some.injEq] at h
          subst h
          have hEu := neg1_val V pre hw hn u N hum μ
          simp only [aval, hf, hdp, hargs, show (13 : ℕ) < 100 by norm_num, if_true, bfn,
            List.map_cons, List.map_nil, List.getD_cons_zero, argV_zm]
          rw [ipDen_subst, ipDen_C]
          refine emod_congr_sub _ _ (ipDen (Function.update E u (E u)) P) _ ?_ ?_
          · have := ipDen_upd_dvd E u 0 (E u) P
            refine dvd_trans ?_ this
            simpa using hEu
          · rw [Function.update_eq_self]; simp
        · simp at h
  · simp at h

/-- The argument of the remainder modulo `N - 1` at the split `sp` simplified. -/
def m1At (t : ATm) (sp : List Atom × Atom × List Atom) : Option ATm :=
  match m1Arg sp.1 sp.2.1 with
  | some a' =>
    if wfA t.ats && (ids t.ats).Nodup then some ⟨t.c, t.sums, sp.1 ++ a' :: sp.2.2, t.dels, t.phs, t.aps⟩
    else none
  | none => none

theorem m1At_ok (V : LV) (t t' : ATm) (sp : List Atom × Atom × List Atom)
    (hsp : t.ats = sp.1 ++ sp.2.1 :: sp.2.2) (h : m1At t sp = some t') : PWEq V t t' := by
  unfold m1At at h
  split at h
  · next a' ha =>
    split_ifs at h with hc
    simp only [Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [hsp] at hc
    have hw : wfA sp.1 = true := wfA_append _ _ hc.1
    have hn : (ids sp.1).Nodup := (List.nodup_append.1 (by simpa [ids] using hc.2)).1
    have hid : a'.id = sp.2.1.id := by
      unfold m1Arg at ha
      repeat' (first | split at ha | split_ifs at ha)
      all_goals first | (simp only [Option.some.injEq] at ha; rw [← ha]) | simp at ha
    exact swap_pw V t sp hsp a' hid fun μ => m1Arg_ok V sp.1 hw hn _ _ ha μ
  · simp at h

/-- A reduced argument `mod(z, N)` of a remainder `z` modulo `N - 1`, `2 ≤ N`, read as `z`. -/
def aliasAt (fl : List ℕ) (t : ATm) (sp : List Atom × Atom × List Atom) : Option ATm :=
  match sp.2.1.f, sp.2.1.args with
  | 2, [([([z], 1)], N)] =>
    if isM1 sp.1 z N && decide (2 ≤ N.den (flv fl)) && wfA t.ats && (ids t.ats).Nodup then
      some ⟨t.c, t.sums, sp.1 ++ sp.2.2.map (atSub sp.2.1.id (ipV z)),
        t.dels.map (facSub sp.2.1.id (ipV z)), t.phs.map (facSub sp.2.1.id (ipV z)), t.aps⟩
    else none
  | _, _ => none

theorem aliasAt_ok (V : LV) (fl : List ℕ) (hfl : FloorOK fl V.ρ) (t t' : ATm)
    (sp : List Atom × Atom × List Atom) (hsp : t.ats = sp.1 ++ sp.2.1 :: sp.2.2)
    (h : aliasAt fl t sp = some t') : PWEq V t t' := by
  unfold aliasAt at h
  split at h
  · next z N hf hargs =>
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hm, h2⟩, hw0⟩, hn0⟩ := hc
    have hN2 : 2 ≤ N.den V.ρ.dv := h2.trans (DMon.den_mono _ _ hfl N)
    rw [hsp] at hw0 hn0
    have hw : wfA sp.1 = true := wfA_append _ _ hw0
    have hnd := List.nodup_append.1 (by simpa [ids] using hn0)
    have hn : (ids sp.1).Nodup := hnd.1
    have hzpre : z ∈ ids sp.1 := by
      unfold isM1 at hm
      cases hb : findAt sp.1 z with
      | none => simp [hb] at hm
      | some b =>
        obtain ⟨hbm, hid⟩ := findAt_spec sp.1 z b hb
        rw [← hid]; exact List.mem_map_of_mem hbm
    have hzpost : z ∉ ids (sp.2.1 :: sp.2.2) := fun h' => hnd.2.2 z hzpre z h' rfl
    simp only [ids, List.map_cons, List.mem_cons, not_or] at hzpost
    have hapost : sp.2.1.id ∉ ids sp.2.2 := by
      have := hnd.2.1; simp only [ids, List.map_cons, List.nodup_cons] at this; exact this.1
    refine ⟨rfl, rfl, fun μ => ?_⟩
    unfold abody
    simp only
    rw [hsp, aext_append, aext_append]
    simp only [aext]
    obtain ⟨X, hX⟩ := m1_val V sp.1 hw hn z N hm μ
    set P := aext V sp.1 μ
    have hval : aval V P sp.2.1 = ipDen P (ipV z) := by
      have hpos : (0 : ℤ) < (N.den V.ρ.dv : ℤ) - 1 := by omega
      simp only [aval, hf, hargs, show (2 : ℕ) < 100 by norm_num, if_true, bfn, List.map_cons,
        List.map_nil, argV, List.getD_cons_zero, ipDen_V]
      have hV : ipDen P [([z], 1)] = P z := by simp [ipDen, imDen]
      rw [hV, hX]
      have h0 := Int.emod_nonneg X hpos.ne'
      have h1 := Int.emod_lt_of_pos X hpos
      exact Int.emod_eq_of_lt h0 (by omega)
    have hpv : plainP sp.2.2 (ipV z) = true := by
      simp only [plainP, ipVs, ipV, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.all_cons, List.all_nil, Bool.and_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not]
      exact hzpost.2
    have hhs : ipHas sp.2.1.id (ipV z) = false := by simp [ipHas, ipV, Ne.symm hzpost.1]
    rw [hval, aext_sub V sp.2.2 sp.2.1.id hapost _ hpv hhs P, bodyOf_sub, ipDen_V, ipDen_V,
      aext_off V _ _ _ (by simpa [ids, atSub, List.map_map, Function.comp_def] using hzpost.2)]
  · simp at h

/-- A delta `[N ∣ z - N + 1]` of a remainder `z` modulo `N - 1`, `2 ≤ N`, read as `[N ∣ 1]`. -/
def falseDel (fl : List ℕ) (ats : List Atom) (f : Fac) : Option Fac :=
  match f.2 with
  | [([], c), ([z], cz), ([w], cw)] =>
    if (c = 1 ∧ cz = 1 ∧ cw = -1 ∨ c = -1 ∧ cz = -1 ∧ cw = 1) ∧ isM1 ats z f.1 = true ∧
        isDim ats w f.1 = true ∧ 2 ≤ f.1.den (flv fl) then some (f.1, ipC 1) else none
  | [([], c), ([z], cz)] =>
    if (c = 1 ∧ cz = 1 ∨ c = -1 ∧ cz = -1) ∧ isM1 ats z f.1 = true ∧ 2 ≤ f.1.den (flv fl) then
      some (f.1, ipC 1) else none
  | _ => none

theorem falseDel_ok (V : LV) (fl : List ℕ) (hfl : FloorOK fl V.ρ) (ats : List Atom)
    (hw : wfA ats = true) (hn : (ids ats).Nodup) (f f' : Fac) (h : falseDel fl ats f = some f')
    (μ : ℕ → ℤ) : delV V.ρ.dv (aext V ats μ) f' = delV V.ρ.dv (aext V ats μ) f := by
  unfold falseDel at h
  split at h
  · next c z cz w cw hp =>
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hs, hm, hd, h2⟩ := hc
    have hN2 : 2 ≤ f.1.den V.ρ.dv := h2.trans (DMon.den_mono _ _ hfl f.1)
    obtain ⟨X, hX⟩ := m1_val V ats hw hn z f.1 hm μ
    have hW := dim_val V ats hw hn w f.1 hd μ
    have hpos : (0 : ℤ) < (f.1.den V.ρ.dv : ℤ) - 1 := by omega
    have h0 := Int.emod_nonneg X hpos.ne'
    have h1 := Int.emod_lt_of_pos X hpos
    have hl : delV V.ρ.dv (aext V ats μ) (f.1, ipC 1) = 0 := by
      unfold delV
      simp only [ipDen_C]
      rw [if_neg]
      intro hd1; have := Int.le_of_dvd one_pos hd1; omega
    have hr : delV V.ρ.dv (aext V ats μ) f = 0 := by
      unfold delV
      rw [hp, if_neg]
      simp only [ipDen, imDen, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        List.sum_cons, List.sum_nil, mul_one, add_zero, hX, hW]
      intro hd2
      rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd2 (by omega)
        omega
      · have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd2 (by omega)
        omega
    rw [hl, hr]
  · next c z cz hp =>
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hs, hm, h2⟩ := hc
    have hN2 : 2 ≤ f.1.den V.ρ.dv := h2.trans (DMon.den_mono _ _ hfl f.1)
    obtain ⟨X, hX⟩ := m1_val V ats hw hn z f.1 hm μ
    have hpos : (0 : ℤ) < (f.1.den V.ρ.dv : ℤ) - 1 := by omega
    have h0 := Int.emod_nonneg X hpos.ne'
    have h1 := Int.emod_lt_of_pos X hpos
    have hl : delV V.ρ.dv (aext V ats μ) (f.1, ipC 1) = 0 := by
      unfold delV
      simp only [ipDen_C]
      rw [if_neg]
      intro hd1; have := Int.le_of_dvd one_pos hd1; omega
    have hr : delV V.ρ.dv (aext V ats μ) f = 0 := by
      unfold delV
      rw [hp, if_neg]
      simp only [ipDen, imDen, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        List.sum_cons, List.sum_nil, mul_one, add_zero, hX]
      intro hd2
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd2 (by omega)
        omega
      · have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd2 (by omega)
        omega
    rw [hl, hr]
  · simp at h

/-- A delta of a remainder modulo `N - 1` that never holds read as `[N ∣ 1]`. -/
def falseAt (fl : List ℕ) (t : ATm) (sp : List Fac × Fac × List Fac) : Option ATm :=
  match falseDel fl t.ats sp.2.1 with
  | some f' =>
    if wfA t.ats && (ids t.ats).Nodup then some ⟨t.c, t.sums, t.ats, sp.1 ++ f' :: sp.2.2, t.phs, t.aps⟩
    else none
  | none => none

theorem falseAt_ok (V : LV) (fl : List ℕ) (hfl : FloorOK fl V.ρ) (t t' : ATm)
    (sp : List Fac × Fac × List Fac) (hsp : t.dels = sp.1 ++ sp.2.1 :: sp.2.2)
    (h : falseAt fl t sp = some t') : PWEq V t t' := by
  unfold falseAt at h
  split at h
  · next f' hf =>
    split_ifs at h with hc
    simp only [Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    refine ⟨rfl, rfl, fun μ => ?_⟩
    unfold abody bodyOf
    simp only
    rw [hsp]
    simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
    rw [falseDel_ok V fl hfl t.ats hc.1 hc.2 _ _ hf μ]
  · simp at h

/-- Whether `u` is a reduced argument `mod(y, N)` of the table `l`. -/
def isRed (l : List Atom) (u : ℕ) (N : DMon) : Bool :=
  (findAt l u).any fun c => c.f == 2 && match c.args with
    | [(_, M)] => M == N
    | _ => false

theorem red_val (V : LV) (pre : List Atom) (hw : wfA pre = true) (hn : (ids pre).Nodup)
    (u : ℕ) (N : DMon) (h : isRed pre u N = true) (μ : ℕ → ℤ) :
    ∃ Y : ℤ, aext V pre μ u = Y % (N.den V.ρ.dv : ℤ) := by
  unfold isRed at h
  cases hb : findAt pre u with
  | none => simp [hb] at h
  | some b =>
    rw [hb] at h
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hf, ha⟩ := h
    obtain ⟨hbm, hid⟩ := findAt_spec pre u b hb
    rw [← hid, aext_fix V pre hw hn μ b hbm]
    split at ha
    · next q M hargs =>
      simp only [beq_iff_eq] at ha
      subst ha
      exact ⟨ipDen (aext V pre μ) q, by simp [aval, hf, hargs, bfn, argV]⟩
    · simp at ha

/-- Inside a remainder modulo `N - 1`, `u = mod(y, N)` under the delta `[N ∣ 1 + u]` of `ds`
read as `0`. -/
def redArg (ds : List Fac) (pre : List Atom) (a : Atom) : Option (ℕ × Atom) :=
  match a.f, a.dp, a.args with
  | 13, [N], [(P, Z)] =>
    if Z = ZM then
      match (ipVs P).find? (fun u => isRed pre u N && ds.contains (N, [([], 1), ([u], 1)])) with
      | some u => some (u, { a with args := [(ipSubst u (ipC 0) P, ZM)] })
      | none => none
    else none
  | _, _, _ => none

theorem redArg_spec (ds : List Fac) (pre : List Atom) (a : Atom) (u : ℕ) (a' : Atom)
    (h : redArg ds pre a = some (u, a')) :
    a'.id = a.id ∧ isRed pre u (a.dp.getD 0 ZM) = true ∧
      (a.dp.getD 0 ZM, [([], 1), ([u], 1)]) ∈ ds ∧
      ∀ (V : LV) (E : ℕ → ℤ), ((a.dp.getD 0 ZM).den V.ρ.dv : ℤ) - 1 ∣ E u →
        aval V E a' = aval V E a := by
  unfold redArg at h
  split at h
  · next N P Z hf hdp hargs =>
    split_ifs at h with hZ
    subst hZ
    split at h
    · next u0 hu =>
      have hum := List.find?_some hu
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hum
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [hdp, List.getD_cons_zero]
      refine ⟨trivial, hum.1, hum.2, fun V E hE => ?_⟩
      simp only [aval, hf, hdp, hargs, show (13 : ℕ) < 100 by norm_num, if_true, bfn,
        List.map_cons, List.map_nil, List.getD_cons_zero, argV_zm]
      rw [ipDen_subst, ipDen_C]
      refine emod_congr_sub _ _ (ipDen (Function.update E u0 (E u0)) P) _ ?_ ?_
      · have := ipDen_upd_dvd E u0 0 (E u0) P
        refine dvd_trans ?_ this
        simpa using hE
      · rw [Function.update_eq_self]; simp
    · simp at h
  · simp at h

/-- The remainder modulo `N - 1` at the split `sp` simplified under a delta of the term. -/
def redAt (t : ATm) (sp : List Atom × Atom × List Atom) : Option ATm :=
  match redArg t.dels sp.1 sp.2.1 with
  | some (_, a') =>
    if wfA t.ats && (ids t.ats).Nodup then some ⟨t.c, t.sums, sp.1 ++ a' :: sp.2.2, t.dels, t.phs, t.aps⟩
    else none
  | none => none

theorem redAt_ok (V : LV) (t t' : ATm) (sp : List Atom × Atom × List Atom)
    (hsp : t.ats = sp.1 ++ sp.2.1 :: sp.2.2) (h : redAt t sp = some t') : PWEq V t t' := by
  unfold redAt at h
  split at h
  · next u a' ha =>
    split_ifs at h with hc
    simp only [Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hid, hred, hdel, hv⟩ := redArg_spec _ _ _ _ _ ha
    rw [hsp] at hc
    have hw : wfA sp.1 = true := wfA_append _ _ hc.1
    have hnd : (ids (sp.1 ++ sp.2.1 :: sp.2.2)).Nodup := hc.2
    have hn : (ids sp.1).Nodup := (List.nodup_append.1 (by simpa [ids] using hnd)).1
    set N := sp.2.1.dp.getD 0 ZM
    have hu_in : u ∈ ids sp.1 := by
      unfold isRed at hred
      cases hb : findAt sp.1 u with
      | none => simp [hb] at hred
      | some b =>
        obtain ⟨hbm, hbid⟩ := findAt_spec sp.1 u b hb
        exact hbid ▸ List.mem_map_of_mem hbm
    have hu_out : u ∉ ids (sp.2.1 :: sp.2.2) := by
      intro hm
      have := List.disjoint_of_nodup_append (by simpa [ids] using hnd)
      exact this hu_in (by simpa [ids] using hm)
    have hu_out' : u ∉ ids (a' :: sp.2.2) := by simpa [ids, hid] using hu_out
    refine ⟨rfl, rfl, fun μ => ?_⟩
    unfold abody
    simp only
    rw [hsp, aext_append, aext_append]
    set E0 := aext V sp.1 μ
    have hF : aext V (sp.2.1 :: sp.2.2) E0 u = E0 u := aext_off V _ E0 u hu_out
    have hF' : aext V (a' :: sp.2.2) E0 u = E0 u := aext_off V _ E0 u hu_out'
    by_cases hd : ((N.den V.ρ.dv : ℕ) : ℤ) ∣ 1 + E0 u
    · have hE : (N.den V.ρ.dv : ℤ) - 1 ∣ E0 u := by
        obtain ⟨Y, hY⟩ := red_val V sp.1 hw hn u N hred μ
        rcases Nat.eq_zero_or_pos (N.den V.ρ.dv) with h0 | h0
        · rw [h0]; exact ⟨-E0 u, by ring⟩
        · have hY0 := Int.emod_nonneg Y (by omega : ((N.den V.ρ.dv : ℕ) : ℤ) ≠ 0)
          have hY1 := Int.emod_lt_of_pos Y (by omega : (0 : ℤ) < (N.den V.ρ.dv : ℕ))
          obtain ⟨k, hk⟩ := hd
          have : k = 1 := by
            rcases lt_trichotomy k 1 with hk1 | hk1 | hk1
            · have : k ≤ 0 := by omega
              nlinarith
            · exact hk1
            · have : 2 ≤ k := by omega
              nlinarith
          subst this
          rw [show E0 u = (N.den V.ρ.dv : ℤ) - 1 by omega]
      simp only [aext]
      rw [hid, hv V E0 hE]
    · have hz : ∀ F : ℕ → ℤ, F u = E0 u → (t.dels.map (delV V.ρ.dv F)).prod = 0 := by
        intro F hFu
        apply List.prod_eq_zero
        refine List.mem_map.2 ⟨_, hdel, ?_⟩
        unfold delV
        rw [if_neg]
        simpa [ipDen, imDen, hFu] using hd
      unfold bodyOf
      rw [hz _ hF, hz _ hF']
      simp
  · simp at h

/-- `(u, w)` when `f = [D ∣ s a + c b]` equates the reduced atoms `a`, `b` modulo a constant `D`,
`s = ±1`, `D ∣ s + c`; `u` the one of lesser key. -/
def eqDelOf (ats : List Atom) (f : Fac) : Option (ℕ × ℕ) :=
  match f.2 with
  | [([a], ca), ([b], cb)] =>
    if f.1.isConst = true ∧ f.1.c ≠ 0 ∧ (ca = 1 ∨ ca = -1) ∧ (ca + cb) % (f.1.c : ℤ) = 0 ∧
        isRed ats a f.1 = true ∧ isRed ats b f.1 = true ∧ a ≠ b then
      match findAt ats a, findAt ats b with
      | some A, some B => if zLt (atKey B) (atKey A) then some (b, a) else some (a, b)
      | _, _ => none
    else none
  | _ => none

theorem eqDelOf_spec (V : LV) (ats : List Atom) (hw : wfA ats = true) (hn : (ids ats).Nodup)
    (f : Fac) (u w : ℕ) (h : eqDelOf ats f = some (u, w)) (μ : ℕ → ℤ)
    (hd : delV V.ρ.dv (aext V ats μ) f ≠ 0) : aext V ats μ u = aext V ats μ w := by
  unfold eqDelOf at h
  split at h
  · next a ca b cb hp =>
    split_ifs at h with hc
    obtain ⟨hD, hD0, hs, hsc, ha, hb, -⟩ := hc
    set F := aext V ats μ
    have hden : f.1.den V.ρ.dv = f.1.c := DMon.den_isConst _ _ hD
    have hpos : (0 : ℤ) < (f.1.c : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hD0
    have hab : F a = F b := by
      obtain ⟨Ya, hYa⟩ := red_val V ats hw hn a f.1 ha μ
      obtain ⟨Yb, hYb⟩ := red_val V ats hw hn b f.1 hb μ
      rw [hden] at hYa hYb
      have hYa' : F a = Ya % (f.1.c : ℤ) := hYa
      have hYb' : F b = Yb % (f.1.c : ℤ) := hYb
      have hdv : ((f.1.den V.ρ.dv : ℕ) : ℤ) ∣ ipDen F f.2 := by
        unfold delV at hd; by_contra hc'; exact hd (if_neg hc')
      rw [hp, hden] at hdv
      simp only [ipDen, imDen, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one, List.sum_cons, List.sum_nil, add_zero] at hdv
      have hdc : (f.1.c : ℤ) ∣ ca + cb := Int.dvd_of_emod_eq_zero hsc
      have h2 : (f.1.c : ℤ) ∣ ca * (ca * F a + cb * F b) - ca * ((ca + cb) * F b) :=
        dvd_sub (dvd_mul_of_dvd_right hdv _) (dvd_mul_of_dvd_right (Dvd.dvd.mul_right hdc _) _)
      have e2 : ca * (ca * F a + cb * F b) - ca * ((ca + cb) * F b) = F a - F b := by
        rcases hs with rfl | rfl <;> ring
      rw [e2] at h2
      have ha0 := Int.emod_nonneg Ya hpos.ne'
      have ha1 := Int.emod_lt_of_pos Ya hpos
      have hb0 := Int.emod_nonneg Yb hpos.ne'
      have hb1 := Int.emod_lt_of_pos Yb hpos
      rw [hYa', hYb'] at h2 ⊢
      obtain ⟨k, hk⟩ := h2
      have : k = 0 := by
        rcases lt_trichotomy k 0 with h' | h' | h'
        · nlinarith
        · exact h'
        · nlinarith
      subst this
      omega
    split at h
    · next A B _ _ =>
      split_ifs at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
        obtain ⟨rfl, rfl⟩ := h
      · exact hab.symm
      · exact hab
    · simp at h
  · simp at h

/-- The atom of greater key read as the lesser one in the other factors, under the delta at the
split `sp` equating them. -/
def eqAt (t : ATm) (sp : List Fac × Fac × List Fac) : Option ATm :=
  match eqDelOf t.ats sp.2.1 with
  | some (u, w) =>
    if wfA t.ats && (ids t.ats).Nodup &&
        ((sp.1 ++ sp.2.2).any (facHas w) || t.phs.any (facHas w)) then
      some ⟨t.c, t.sums, t.ats, sp.1.map (facSub w (ipV u)) ++ sp.2.1 ::
        sp.2.2.map (facSub w (ipV u)), t.phs.map (facSub w (ipV u)), t.aps⟩
    else none
  | none => none

theorem eqAt_ok (V : LV) (t t' : ATm) (sp : List Fac × Fac × List Fac)
    (hsp : t.dels = sp.1 ++ sp.2.1 :: sp.2.2) (h : eqAt t sp = some t') : PWEq V t t' := by
  unfold eqAt at h
  split at h
  · next u w ho =>
    split_ifs at h with hc
    simp only [Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    refine ⟨rfl, rfl, fun μ => ?_⟩
    unfold abody bodyOf
    simp only
    rw [hsp]
    set F := aext V t.ats μ
    simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
    by_cases hd : delV V.ρ.dv F sp.2.1 = 0
    · rw [hd]; ring
    · have he : F u = F w := eqDelOf_spec V t.ats hc.1.1 hc.1.2 sp.2.1 u w ho μ hd
      have hF : Function.update F w (ipDen F (ipV u)) = F := by
        rw [show ipDen F (ipV u) = F u by simp [ipDen, ipV, imDen], he, Function.update_eq_self]
      have hD : ∀ g : Fac, delV V.ρ.dv F (facSub w (ipV u) g) = delV V.ρ.dv F g := fun g => by
        unfold delV facSub; rw [ipDen_subst, hF]
      have hP : ∀ g : Fac, phV V.ρ.dv F (facSub w (ipV u) g) = phV V.ρ.dv F g := fun g => by
        unfold phV facSub; rw [ipDen_subst, hF]
      simp only [List.map_map, Function.comp_def, hD, hP]
  · simp at h

/-- One rule for constants, exclusive or and shared atoms, the first that applies. -/
def pRule1 (fl : List ℕ) (PW : List (DMon × DMon)) (t : ATm) : Option ATm :=
  match firstSome (cstAt t) (splits t.ats) with
  | some t' => some t'
  | none =>
    match firstSome (swapAt xorZ t) (splits t.ats) with
    | some t' => some t'
    | none =>
      match firstSome (swapAt modC t) (splits t.ats) with
      | some t' => some t'
      | none =>
      match firstSome (swapAt ddotSwap t) (splits t.ats) with
      | some t' => some t'
      | none =>
        match firstSome (xorAt PW t) (splits t.ats) with
        | some t' => some t'
        | none =>
          match firstSome (dedupA t) (splits t.ats) with
          | some t' => some t'
          | none =>
            match firstSome (dedupW t) (splits t.ats) with
            | some t' => some t'
            | none =>
              match firstSome (dsubAt t) (splits t.ats) with
              | some t' => some t'
              | none =>
                match firstSome (dotXorAt PW t) (splits t.ats) with
                | some t' => some t'
                | none =>
                  match firstSome (m1At t) (splits t.ats) with
                  | some t' => some t'
                  | none =>
                    match firstSome (aliasAt fl t) (splits t.ats) with
                    | some t' => some t'
                    | none =>
                      match firstSome (redAt t) (splits t.ats) with
                      | some t' => some t'
                      | none =>
                        match firstSome (eqAt t) (splits t.dels) with
                        | some t' => some t'
                        | none => firstSome (falseAt fl t) (splits t.dels)

theorem swapAt_ok (V : LV) (g : Atom → Option Atom) (hg : ∀ a a', g a = some a' →
    a'.id = a.id ∧ ∀ μ, aval V μ a' = aval V μ a) (t t' : ATm) (sp : List Atom × Atom × List Atom)
    (hsp : t.ats = sp.1 ++ sp.2.1 :: sp.2.2) (h : swapAt g t sp = some t') : PWEq V t t' := by
  unfold swapAt at h
  split at h
  · next a' ha =>
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hid, hv⟩ := hg _ _ ha
    exact swap_pw V t sp hsp a' hid fun μ => hv _
  · simp at h

theorem pRule1_ok (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ)
    (t t' : ATm) (h : pRule1 fl PW t = some t') : PWEq V t t' := by
  unfold pRule1 at h
  split at h
  · next t'' h' =>
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h'
    exact cstAt_ok V t _ p (splits_spec _ p hp) he
  · split at h
    · next t'' h' =>
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h'
      refine swapAt_ok V xorZ (fun a a' ha => ⟨?_, xorZ_ok V hρ a a' ha⟩) t _ p (splits_spec _ p hp) he
      unfold xorZ at ha; split at ha
      · split_ifs at ha <;> simp only [Option.some.injEq] at ha <;> rw [← ha]
      · simp at ha
    · split at h
      · next t'' h' =>
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h'
        refine swapAt_ok V modC (fun a a' ha => ⟨?_, modC_ok V a a' ha⟩) t _ p (splits_spec _ p hp) he
        unfold modC at ha; split at ha
        · split_ifs at ha; simp only [Option.some.injEq] at ha; rw [← ha]
        · simp at ha
      · split at h
        · next t'' h' =>
          simp only [Option.some.injEq] at h; subst h
          obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h'
          refine swapAt_ok V ddotSwap (fun a a' ha => ⟨?_, ddotSwap_ok V a a' ha⟩) t _ p
            (splits_spec _ p hp) he
          unfold ddotSwap at ha; split at ha
          · split_ifs at ha; simp only [Option.some.injEq] at ha; rw [← ha]
          · simp at ha
        · split at h
          · next t'' h' =>
            simp only [Option.some.injEq] at h; subst h
            obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h'
            exact xorAt_ok V PW hPW t _ p (splits_spec _ p hp) he
          · split at h
            · next t'' h' =>
              simp only [Option.some.injEq] at h; subst h
              obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h'
              exact dedupA_ok V t _ p (splits_spec _ p hp) he
            · split at h
              · next t'' h' =>
                simp only [Option.some.injEq] at h; subst h
                obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h'
                exact dedupW_ok V t _ p (splits_spec _ p hp) he
              · split at h
                · next t'' h' =>
                  simp only [Option.some.injEq] at h; subst h
                  obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h'
                  exact dsubAt_ok V hρ t _ p (splits_spec _ p hp) he
                · split at h
                  · next t'' h' =>
                    simp only [Option.some.injEq] at h; subst h
                    obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h'
                    exact dotXorAt_ok V PW hPW t _ p (splits_spec _ p hp) he
                  · split at h
                    · next t'' h' =>
                      simp only [Option.some.injEq] at h; subst h
                      obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h'
                      exact m1At_ok V t _ p (splits_spec _ p hp) he
                    · split at h
                      · next t'' h' =>
                        simp only [Option.some.injEq] at h; subst h
                        obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h'
                        exact aliasAt_ok V fl hfl t _ p (splits_spec _ p hp) he
                      · split at h
                        · next t'' h' =>
                          simp only [Option.some.injEq] at h; subst h
                          obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h'
                          exact redAt_ok V t _ p (splits_spec _ p hp) he
                        · split at h
                          · next t'' h' =>
                            simp only [Option.some.injEq] at h; subst h
                            obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h'
                            exact eqAt_ok V t _ p (splits_spec _ p hp) he
                          · obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h
                            exact falseAt_ok V fl hfl t _ p (splits_spec _ p hp) he

/-- The rules for constants, exclusive or and shared atoms repeated, at most `n` of them. -/
def pRules (fl : List ℕ) (PW : List (DMon × DMon)) : ℕ → ATm → ATm
  | 0, t => t
  | n + 1, t => match pRule1 fl PW t with
    | some t' => pRules fl PW n t'
    | none => t

theorem pRules_ok (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ)
    (n : ℕ) (t : ATm) : PWEq V t (pRules fl PW n t) := by
  induction n generalizing t with
  | zero => exact ⟨rfl, rfl, fun _ => rfl⟩
  | succ n ih =>
    simp only [pRules]
    split
    · next t' h => exact (pRule1_ok V hρ fl hfl PW hPW t t' h).trans (ih t')
    · exact ⟨rfl, rfl, fun _ => rfl⟩

/-- Atom rules around the reduced-argument and digit-condition steps. -/
@[irreducible] def preA (fl : List ℕ) (PW : List (DMon × DMon)) (t : ATm) : ATm :=
  aRules ((dzStep PW (modRules fl PW (t.ats.length + 1)
      (pRules fl PW (t.ats.length + 1) (aRules (t.ats.length + 1) t)))).ats.length + 1)
    (dzStep PW (modRules fl PW (t.ats.length + 1)
      (pRules fl PW (t.ats.length + 1) (aRules (t.ats.length + 1) t))))

theorem preA_ok (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (t : ATm) : PWEq V t (preA fl PW t) := by
  unfold preA
  exact ((((aRules_ok V _ t).trans (pRules_ok V hρ fl hfl PW hPW _ _)).trans
    (modRules_ok V hρ fl hfl PW hPW _ _)).trans (dzStep_ok V PW hPW _)).trans (aRules_ok V _ _)

/-- Atom rules, digit conditions read as deltas, factor canonicalisation, canonical names and
sorted sums; `none` when the term vanishes. -/
def canonCore (fl : List ℕ) (t : ATm) : Option ATm :=
  match canonF fl t.dels t.phs with
  | none => none
  | some (k, ds, ps) => some (sortSums (sortTab (canonRen ⟨CMon.mul t.c k, t.sums, t.ats, ds, ps, t.aps⟩)))

/-- Atom rules, digit conditions read as deltas, factor canonicalisation, canonical names and
sorted sums; `none` when the term vanishes. -/
@[irreducible] def canonA (fl : List ℕ) (PW : List (DMon × DMon)) (t : ATm) : Option ATm :=
  canonCore fl (preA fl PW t)

theorem canonA_ok (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (t : ATm) : ARes V t (canonA fl PW t) := by
  have h13 := preA_ok V hρ fl hfl PW hPW t
  unfold canonA
  generalize preA fl PW t = t3 at h13 ⊢
  unfold canonCore
  split
  · next hn =>
    intro ν
    rw [← h13.den ν]
    exact den_zero_of_pw V t3 (fun μ => by
      unfold abody; rw [canonF_none V.ρ hρ fl hfl _ _ hn _, zero_mul]) ν
  · next k ds ps hk =>
    intro ν
    rw [sortSums_ok, sortTab_ok, canonRen_ok, ← h13.den ν]
    refine den_of_pw V t3 ⟨CMon.mul t3.c k, t3.sums, t3.ats, ds, ps, t3.aps⟩ rfl (fun μ => ?_) ν
    unfold abody
    simp only
    rw [CMon.den_mul V.ρ hρ, ← canonF_some V.ρ hρ fl hfl _ _ k ds ps hk]
    ring

/-- A term with its powers merged by `apsCanon`. -/
def tCanonAps (t : ATm) : ATm := ⟨t.c, t.sums, t.ats, t.dels, t.phs, apsCanon t.aps⟩

theorem tCanonAps_den (V : LV) (hρ : V.ρ.OK) (t : ATm) (ν : ℕ → ℤ) :
    (tCanonAps t).den V ν = t.den V ν := by
  unfold ATm.den abody tCanonAps
  simp only [apsV_canon V hρ]

/-- Eliminations and canonicalisation, alternated `r` times, the powers merged after each. -/
def normA (fl : List ℕ) (PW : List (DMon × DMon)) : ℕ → ATm → Option ATm
  | 0, t => some t
  | r + 1, t =>
    match canonA fl PW (aElimAll PW (t.sums.length + 1) t) with
    | none => none
    | some t' => normA fl PW r (tCanonAps t')

theorem normA_ok (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (r : ℕ) (t : ATm) :
    ARes V t (normA fl PW r t) := by
  induction r generalizing t with
  | zero => intro ν; rfl
  | succ r ih =>
    have hc := canonA_ok V hρ fl hfl PW hPW (aElimAll PW (t.sums.length + 1) t)
    have he := aElimAll_ok V hρ PW hPW (t.sums.length + 1) t
    simp only [normA]
    split
    · next h => rw [h] at hc; intro ν; rw [← he ν, hc ν]
    · next t' h =>
      rw [h] at hc
      have := ih (tCanonAps t')
      revert this
      cases normA fl PW r (tCanonAps t') with
      | none => intro h' ν; rw [← he ν, ← hc ν, ← tCanonAps_den V hρ t' ν, h' ν]
      | some t'' => intro h' ν; rw [h' ν, tCanonAps_den V hρ t' ν, hc ν, he ν]

/-- The term without its rational coefficient. -/
def ashape (t : ATm) : ATm := { t with c := { t.c with q := 0 } }

/-- A term with rational coefficient `q`. -/
def awithQ (t : ATm) (q : ℚ) : ATm := { t with c := { t.c with q := q } }

/-- A term added to an expression, merged with one of the same shape. -/
def taAdd (t : ATm) : List ATm → List ATm
  | [] => if t.c.q = 0 then [] else [t]
  | u :: l =>
    if ashape u = ashape t then
      (if qAdd u.c.q t.c.q = 0 then l else awithQ u (qAdd u.c.q t.c.q) :: l)
    else u :: taAdd t l

theorem aden_withQ (V : LV) (ν : ℕ → ℤ) (t : ATm) (q : ℚ) :
    (awithQ t q).den V ν = (q : ℂ) * (awithQ t 1).den V ν := by
  unfold ATm.den
  rw [show abody V (awithQ t q) = abody V t from rfl,
    show abody V (awithQ t 1) = abody V t from rfl]
  simp only [awithQ, CMon.den]; push_cast; ring

theorem aden_self (V : LV) (ν : ℕ → ℤ) (t : ATm) :
    t.den V ν = (t.c.q : ℂ) * (awithQ t 1).den V ν := by
  rw [← aden_withQ]; rfl

theorem awithQ_shape (t u : ATm) (h : ashape u = ashape t) (q : ℚ) : awithQ u q = awithQ t q := by
  obtain ⟨⟨_, r, sq, rc, am, gc⟩, s, at', d, p, ap⟩ := u
  obtain ⟨⟨_, r', sq', rc', am', gc'⟩, s', at'', d', p', ap'⟩ := t
  simp only [ashape, ATm.mk.injEq, CMon.mk.injEq] at h
  obtain ⟨⟨-, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

theorem taAdd_ok (V : LV) (ν : ℕ → ℤ) (t : ATm) (l : List ATm) :
    axDen V ν (taAdd t l) = t.den V ν + axDen V ν l := by
  induction l with
  | nil =>
    simp only [taAdd]
    split_ifs with h
    · simp [axDen, aden_self V ν t, h]
    · simp [axDen]
  | cons u l ih =>
    simp only [taAdd, qAdd_eq]
    split_ifs with h1 h2
    · have e := awithQ_shape t u h1 1
      have hq : ((u.c.q + t.c.q : ℚ) : ℂ) = 0 := by rw [h2]; simp
      simp only [axDen, List.map_cons, List.sum_cons]
      rw [aden_self V ν t, aden_self V ν u, e]
      push_cast at hq
      linear_combination -(awithQ t 1).den V ν * hq
    · have e := awithQ_shape t u h1 1
      simp only [axDen, List.map_cons, List.sum_cons]
      rw [aden_withQ, aden_self V ν t, aden_self V ν u, e]
      push_cast; ring
    · simp only [axDen, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]; ring

/-- Rounds of eliminations per term. -/
def AROUNDS : ℕ := 8

/-- Every term normalised, terms of one shape merged. -/
def nfA (fl : List ℕ) (PW : List (DMon × DMon)) (e : List ATm) : List ATm :=
  (e.filterMap (normA fl PW AROUNDS)).foldl (fun acc t => taAdd t acc) []

theorem nfA_den (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (e : List ATm) (ν : ℕ → ℤ) :
    axDen V ν (nfA fl PW e) = axDen V ν e := by
  have h1 : ∀ (l : List ATm) (acc : List ATm),
      axDen V ν (l.foldl (fun acc t => taAdd t acc) acc) = axDen V ν acc + axDen V ν l := by
    intro l
    induction l with
    | nil => intro acc; simp [axDen]
    | cons t l ih =>
      intro acc
      rw [List.foldl_cons, ih, taAdd_ok]; simp only [axDen, List.map_cons, List.sum_cons]; ring
  have h2 : ∀ l : List ATm, axDen V ν (l.filterMap (normA fl PW AROUNDS)) = axDen V ν l := by
    intro l
    induction l with
    | nil => rfl
    | cons t l ih =>
      have := normA_ok V hρ fl hfl PW hPW AROUNDS t
      simp only [List.filterMap_cons]
      revert this
      cases normA fl PW AROUNDS t with
      | none => intro h; simp only [axDen, List.map_cons, List.sum_cons] at ih ⊢; rw [ih, h]; ring
      | some t' =>
        intro h
        simp only [axDen, List.map_cons, List.sum_cons] at ih ⊢; rw [ih, h]
  unfold nfA
  rw [h1, h2]; simp [axDen]

theorem nfA_zero (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (e : List ATm) (h : nfA fl PW e = [])
    (ν : ℕ → ℤ) : axDen V ν e = 0 := by
  rw [← nfA_den V hρ fl hfl PW hPW e ν, h]; rfl

/-- Every term negated. -/
def axNeg (e : List ATm) : List ATm := e.map fun t => awithQ t (-t.c.q)

theorem axDen_neg (V : LV) (ν : ℕ → ℤ) (e : List ATm) : axDen V ν (axNeg e) = -axDen V ν e := by
  induction e with
  | nil => simp [axDen, axNeg]
  | cons t e ih =>
    simp only [axNeg, List.map_cons, axDen, List.sum_cons] at ih ⊢
    rw [ih, aden_withQ, aden_self V ν t]; push_cast; ring

end DiracULA.LSym