/-
Copyright 2026 Arkhip A. Dmitriev
Licensed under the Apache License, Version 2.0.
-/
import DiracULA.LCanon

/-!
# Atoms rewritten under facts about free variables

A context lists free variables known to be nonnegative (a loop variable `J` at an iteration) and
width links `(v, d, N)` with `N = d^(ν v)` (a loop count equal to a width). Under it, `xpass`
rewrites the atoms

  `d^(J + 1) = d · d^J`, `x mod d^(J + 1) = x mod d^J + d^J · digit J of x`,
  `d^v = N`, `x mod d^v = x mod N`,

each as a polynomial in new atoms (`xOne`), and keeps the value of every term at each valuation
the context holds for (`axDen_xpass`).
-/

namespace DiracULA.LSym

open DiracULA.Sym Complex Finset

/-- Free variables known nonnegative (`nn`), width links `(v, d, N)`, `N = d^(ν v)` (`wl`), and
divisibilities `(D1, D2)`, `D1 ∣ D2` (`dv`). -/
structure Ctx where
  nn : List ℕ
  wl : List (ℕ × DMon × DMon)
  dv : List (DMon × DMon)

/-- The variables a context reads. -/
def Ctx.vs (C : Ctx) : List ℕ := C.nn ++ C.wl.map (·.1)

/-- The context holds at `ν`. -/
def CtxOK (V : LV) (C : Ctx) (ν : ℕ → ℤ) : Prop :=
  (∀ j ∈ C.nn, 0 ≤ ν j) ∧
    (∀ w ∈ C.wl, 0 ≤ ν w.1 ∧ w.2.2.den V.ρ.dv = w.2.1.den V.ρ.dv ^ (ν w.1).toNat) ∧
    ∀ w ∈ C.dv, 0 < w.1.den V.ρ.dv ∧ 0 < w.2.den V.ρ.dv ∧ w.1.den V.ρ.dv ∣ w.2.den V.ρ.dv

theorem CtxOK.congr {V : LV} {C : Ctx} {ν μ : ℕ → ℤ} (h : CtxOK V C ν)
    (he : ∀ v ∈ C.vs, μ v = ν v) : CtxOK V C μ := by
  refine ⟨fun j hj => ?_, fun w hw => ?_, h.2.2⟩
  · rw [he j (List.mem_append_left _ hj)]; exact h.1 j hj
  · rw [he w.1 (List.mem_append_right _ (List.mem_map_of_mem hw))]; exact h.2.1 w hw

/-- An atom's value as a polynomial in new atoms from variable `B`, under the context. -/
def xOne (C : Ctx) (B : ℕ) (a : Atom) : Option (List Atom × IPoly) :=
  match a.f, a.dp, a.args with
  | 10, [d], [(x, M), (p, Z)] =>
    if Z = ZM then
      match C.nn.find? (fun j => p == ipAdd (ipV j) (ipC 1) && M.c != 0 && d.c != 0) with
      | some j =>
        some ([⟨B + 1, 7, [], [d], [(ipV j, ZM)]⟩, ⟨B + 2, 9, [], [d], [(x, M), (ipV j, ZM)]⟩,
          ⟨B, 10, [], [d], [(x, M), (ipV j, ZM)]⟩], ipAdd (ipV B) (ipMul (ipV (B + 1)) (ipV (B + 2))))
      | none =>
        match C.wl.find? (fun w => p == ipV w.1 && d == w.2.1 && M == w.2.2) with
        | some w => some ([⟨B, 2, [], [], [(x, w.2.2)]⟩], ipV B)
        | none => none
    else none
  | 7, _, [(p, Z)] =>
    if Z = ZM then
      match C.nn.find? (fun j => p == ipAdd (ipV j) (ipC 1)) with
      | some j =>
        if (a.dp.headD ⟨2, []⟩).isConst then
          some ([⟨B, 7, [], a.dp, [(ipV j, ZM)]⟩], ipSmul (a.dp.headD ⟨2, []⟩).c (ipV B))
        else
          some ([⟨B, 7, [], a.dp, [(ipV j, ZM)]⟩, ⟨B + 1, 8, [], [a.dp.headD ⟨2, []⟩], []⟩],
            ipMul (ipV (B + 1)) (ipV B))
      | none =>
        match C.wl.find? (fun w => p == ipV w.1 && a.dp.headD ⟨2, []⟩ == w.2.1) with
        | some w => some ([⟨B, 8, [], [w.2.2], []⟩], ipV B)
        | none => none
    else none
  | _, _, _ => none

/-! ## The values of the new atoms -/

theorem base_den (dv : ℕ → ℕ) (dp : List DMon) :
    (dp.map (·.den dv)).getD 0 2 = (dp.headD ⟨2, []⟩).den dv := by
  cases dp with
  | nil => simp [DMon.den, npow]
  | cons d dp => simp

/-- What `xOne` gives: new atoms from `B` reading the atom's variables, and the polynomial of its
value. -/
structure XOK (V : LV) (C : Ctx) (B : ℕ) (a : Atom) (nw : List Atom) (P : IPoly) : Prop where
  ids_ge : ∀ b ∈ nw, B ≤ b.id
  val : ∀ E, CtxOK V C E → (∀ y ∈ atVs a, y < B) → aval V E a = ipDen (aext V nw E) P

theorem atVs_mk (id f : ℕ) (ks : List ℤ) (dp : List DMon) (args : List (IPoly × DMon)) :
    atVs ⟨id, f, ks, dp, args⟩ = args.flatMap fun p => ipVs p.1 := rfl

theorem ipVs_V (x : ℕ) : ipVs (ipV x) = [x] := by simp [ipVs, ipV]

theorem ipVs_succ (j : ℕ) : j ∈ ipVs (ipAdd (ipV j) (ipC 1)) := by
  simp only [ipVs, List.mem_flatMap]
  refine ⟨([j], 1), ?_, List.mem_singleton_self _⟩
  simp [ipAdd, ipC, ipIns, ipV, lexLt]

theorem xOne_ok (V : LV) (hρ : V.ρ.OK) (C : Ctx) (B : ℕ) (a : Atom) (nw : List Atom) (P : IPoly)
    (h : xOne C B a = some (nw, P)) : XOK V C B a nw P := by
  unfold xOne at h
  split at h
  · next d x M p Z hf hdp hargs =>
    split_ifs at h with hZ
    subst hZ
    have hav : atVs a = ipVs x ++ ipVs p := by simp [atVs, hargs]
    split at h
    · next j hj =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hj' := List.find?_some hj
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hj'
      obtain ⟨⟨hp, hM⟩, hd⟩ := hj'
      have hjm := List.mem_of_find?_eq_some hj
      refine ⟨by simp, fun E hE hB => ?_⟩
      have hJ : 0 ≤ E j := hE.1 j hjm
      have hjB : j < B := hB j (by rw [hav, hp]; exact List.mem_append_right _ (ipVs_succ j))
      have hxB : ∀ y ∈ ipVs x, y < B := fun y hy => hB y (by rw [hav]; exact List.mem_append_left _ hy)
      have hnew := aext_new V B [⟨B + 1, 7, [], [d], [(ipV j, ZM)]⟩,
          ⟨B + 2, 9, [], [d], [(x, M), (ipV j, ZM)]⟩, ⟨B, 10, [], [d], [(x, M), (ipV j, ZM)]⟩]
        (by simp) (by
          intro b hb y hy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl | rfl
          · simp [atVs_mk, ipVs_V] at hy; omega
          · simp [atVs_mk, ipVs_V] at hy
            rcases hy with hy | hy
            · exact hxB y hy
            · omega
          · simp [atVs_mk, ipVs_V] at hy
            rcases hy with hy | hy
            · exact hxB y hy
            · omega) (by simp [ids]) E
      have e1 := hnew ⟨B + 1, 7, [], [d], [(ipV j, ZM)]⟩ (by simp)
      have e2 := hnew ⟨B + 2, 9, [], [d], [(x, M), (ipV j, ZM)]⟩ (by simp)
      have e3 := hnew ⟨B, 10, [], [d], [(x, M), (ipV j, ZM)]⟩ (by simp)
      simp only at e1 e2 e3
      rw [ipDen_add, ipDen_mul, ipDen_V, ipDen_V, ipDen_V, e1, e2, e3]
      simp only [aval, hf, hdp, hargs, show (10 : ℕ) < 100 by norm_num,
        show (9 : ℕ) < 100 by norm_num, show (7 : ℕ) < 100 by norm_num, if_true, bfn,
        List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ, argV_zm, hp,
        ipDen_add, ipDen_V, ipDen_C, dig]
      have hpos : 0 < M.den V.ρ.dv := DMon.den_pos _ hρ.dpos _ (Nat.pos_of_ne_zero hM)
      have hx0 : 0 ≤ argV V.ρ.dv E (x, M) := Int.emod_nonneg _ (by simp only; omega)
      have hm : (E j + 1).toNat = (E j).toNat + 1 := by omega
      rw [hm]
      obtain ⟨n, hn⟩ : ∃ n : ℕ, argV V.ρ.dv E (x, M) = n :=
        ⟨_, (Int.toNat_of_nonneg hx0).symm⟩
      rw [hn]
      have := (Nat.mod_mul (x := n) (a := d.den V.ρ.dv ^ (E j).toNat) (b := d.den V.ρ.dv))
      rw [← pow_succ] at this
      exact_mod_cast this
    · next hj =>
      split at h
      · next w hw =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hw' := List.find?_some hw
        simp only [Bool.and_eq_true, beq_iff_eq] at hw'
        obtain ⟨⟨hp, hdw⟩, hMw⟩ := hw'
        have hwm := List.mem_of_find?_eq_some hw
        refine ⟨by simp, fun E hE hB => ?_⟩
        have hnew := aext_new V B [⟨B, 2, [], [], [(x, w.2.2)]⟩] (by simp) (by
          intro b hb y hy
          simp only [List.mem_singleton] at hb
          subst hb
          simp [atVs_mk] at hy
          exact hB y (by rw [hav]; exact List.mem_append_left _ hy)) (by simp [ids]) E
          ⟨B, 2, [], [], [(x, w.2.2)]⟩ (by simp)
        simp only at hnew
        rw [ipDen_V, hnew]
        obtain ⟨-, hN⟩ := hE.2.1 w hwm
        simp only [aval, hf, hdp, hargs, show (10 : ℕ) < 100 by norm_num,
          show (2 : ℕ) < 100 by norm_num, if_true, bfn, List.map_cons, List.map_nil,
          List.getD_cons_zero, List.getD_cons_succ, argV_zm, hp, ipDen_V]
        rw [hdw, ← Nat.cast_pow, ← hN, hMw]
        simp only [argV]
        exact Int.emod_emod_of_dvd _ (dvd_refl _)
      · simp at h
  · next p Z hf hargs =>
    by_cases hZ : Z = ZM
    swap
    · rw [if_neg hZ] at h; simp at h
    rw [if_pos hZ] at h
    subst hZ
    have hav : atVs a = ipVs p := by simp [atVs, hargs]
    split at h
    · next j hj =>
      have hj' := List.find?_some hj
      simp only [beq_iff_eq] at hj'
      have hjm := List.mem_of_find?_eq_some hj
      have hbase : ∀ E, 0 ≤ E j →
          aval V E a = ((a.dp.headD ⟨2, []⟩).den V.ρ.dv : ℤ) ^ ((E j).toNat + 1) := by
        intro E hJ
        simp only [aval, hf, show (7 : ℕ) < 100 by norm_num, if_true, bfn, hargs, List.map_cons,
          List.map_nil, List.getD_cons_zero, argV_zm, hj', ipDen_add, ipDen_V, ipDen_C,
          base_den]
        congr 1; omega
      split_ifs at h with hc
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by simp, fun E hE hB => ?_⟩
        have hjB : j < B := hB j (by rw [hav, hj']; exact ipVs_succ j)
        have hnew := aext_new V B [⟨B, 7, [], a.dp, [(ipV j, ZM)]⟩] (by simp) (by
          intro b hb y hy
          simp only [List.mem_singleton] at hb
          subst hb
          simp [atVs_mk, ipVs_V] at hy
          omega) (by simp [ids]) E ⟨B, 7, [], a.dp, [(ipV j, ZM)]⟩ (by simp)
        simp only at hnew
        rw [ipDen_smul, ipDen_V, hnew, hbase E (hE.1 j hjm)]
        simp only [aval, show (7 : ℕ) < 100 by norm_num, if_true, bfn, List.map_cons,
          List.map_nil, List.getD_cons_zero, argV_zm, ipDen_V, base_den]
        rw [DMon.den_isConst _ _ hc, pow_succ]; ring
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by simp, fun E hE hB => ?_⟩
        have hjB : j < B := hB j (by rw [hav, hj']; exact ipVs_succ j)
        have hnew := aext_new V B [⟨B, 7, [], a.dp, [(ipV j, ZM)]⟩,
            ⟨B + 1, 8, [], [a.dp.headD ⟨2, []⟩], []⟩] (by simp) (by
              intro b hb y hy
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
              rcases hb with rfl | rfl
              · simp [atVs_mk, ipVs_V] at hy; omega
              · simp [atVs_mk] at hy) (by simp [ids]) E
        have e1 := hnew ⟨B, 7, [], a.dp, [(ipV j, ZM)]⟩ (by simp)
        have e2 := hnew ⟨B + 1, 8, [], [a.dp.headD ⟨2, []⟩], []⟩ (by simp)
        simp only at e1 e2
        rw [ipDen_mul, ipDen_V, ipDen_V, e1, e2, hbase E (hE.1 j hjm)]
        simp only [aval, show (7 : ℕ) < 100 by norm_num, show (8 : ℕ) < 100 by norm_num,
          if_true, bfn, List.map_cons, List.map_nil, List.getD_cons_zero, argV_zm, ipDen_V,
          base_den]
        rw [pow_succ]; ring
    · next hj =>
      split at h
      · next w hw =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hw' := List.find?_some hw
        simp only [Bool.and_eq_true, beq_iff_eq] at hw'
        obtain ⟨hp, hdw⟩ := hw'
        have hwm := List.mem_of_find?_eq_some hw
        refine ⟨by simp, fun E hE hB => ?_⟩
        have hnew := aext_new V B [⟨B, 8, [], [w.2.2], []⟩] (by simp) (by
          intro b hb y hy
          simp only [List.mem_singleton] at hb
          subst hb
          simp [atVs_mk] at hy) (by simp [ids]) E ⟨B, 8, [], [w.2.2], []⟩ (by simp)
        simp only at hnew
        rw [ipDen_V, hnew]
        obtain ⟨-, hN⟩ := hE.2.1 w hwm
        simp only [aval, hf, hargs, show (7 : ℕ) < 100 by norm_num, show (8 : ℕ) < 100 by norm_num,
          if_true, bfn, List.map_cons, List.map_nil, List.getD_cons_zero, argV_zm, hp, ipDen_V,
          base_den]
        rw [hdw, hN]
        push_cast; rfl
      · simp at h
  · simp at h

/-! ## The pass -/

/-- The atom at the split `sp` rewritten as its polynomial in new atoms. -/
def xAt (C : Ctx) (t : ATm) (sp : List Atom × Atom × List Atom) : Option ATm :=
  match xOne C (maxV t + 1) sp.2.1 with
  | some (nw, P) =>
    if C.vs.all (fun v => !(abvs t).contains v && !(ids t.ats).contains v) &&
        !(ids sp.2.2).contains sp.2.1.id && wfA t.ats && plainP sp.2.2 P &&
        !ipHas sp.2.1.id P then
      some ⟨t.c, t.sums, sp.1 ++ nw ++ sp.2.2.map (atSub sp.2.1.id P),
        t.dels.map (facSub sp.2.1.id P), t.phs.map (facSub sp.2.1.id P)⟩
    else none
  | none => none

theorem sumsV_congr_off (dv : ℕ → ℕ) (s : List (ℕ × DMon)) (S : List ℕ) (f g : (ℕ → ℤ) → ℂ)
    (hS : ∀ p ∈ s, p.1 ∉ S) (ν : ℕ → ℤ) (h : ∀ μ, (∀ v ∈ S, μ v = ν v) → f μ = g μ) :
    sumsV dv s f ν = sumsV dv s g ν := by
  induction s generalizing ν with
  | nil => exact h ν fun _ _ => rfl
  | cons p s ih =>
    simp only [sumsV]
    refine Finset.sum_congr rfl fun j _ => ih (fun q hq => hS q (List.mem_cons_of_mem _ hq)) _
      fun μ hμ => h μ fun v hv => ?_
    rw [hμ v hv, Function.update_of_ne (fun e : v = p.1 => hS p List.mem_cons_self (e ▸ hv))]

theorem xAt_ok (V : LV) (hρ : V.ρ.OK) (C : Ctx) (t t' : ATm) (sp : List Atom × Atom × List Atom)
    (hsp : t.ats = sp.1 ++ sp.2.1 :: sp.2.2) (h : xAt C t sp = some t') (ν : ℕ → ℤ)
    (hC : CtxOK V C ν) : t'.den V ν = t.den V ν := by
  unfold xAt at h
  split at h
  · next nw P hx =>
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hc
    obtain ⟨⟨⟨⟨hcv, hz⟩, hw⟩, hPpost⟩, hPz⟩ := hc
    set B := maxV t + 1
    have hok := xOne_ok V hρ C B sp.2.1 nw P hx
    have hlt : ∀ v ∈ allV t, v < B := fun v hv => Nat.lt_succ_of_le (le_foldr_max _ v hv)
    have hids : ∀ v ∈ ids t.ats, v ∈ allV t := fun v hv => by
      simp only [allV, rvs, List.mem_append]; tauto
    have hargs : ∀ v ∈ argVs t.ats, v ∈ allV t := fun v hv => by
      simp only [allV, rvs, List.mem_append]; tauto
    have haV : ∀ y ∈ atVs sp.2.1, y < B := fun y hy => hlt y (hargs y (by
      rw [hsp]; simp only [argVs, List.flatMap_append, List.flatMap_cons, List.mem_append]
      tauto))
    have hzB : sp.2.1.id < B := hlt _ (hids _ (by rw [hsp]; simp [ids]))
    have hnwB : ∀ y ∈ ids nw, B ≤ y := fun y hy => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy; exact hok.ids_ge b hb
    unfold ATm.den
    simp only
    congr 1
    refine sumsV_congr_off _ _ C.vs _ _ (fun p hp hv => (hcv _ hv).1 (List.mem_map_of_mem hp)) ν
      fun μ hμ => ?_
    unfold abody
    simp only
    rw [hsp, aext_append, aext_append, aext_append]
    simp only [aext]
    set E := aext V sp.1 μ
    have hvpre : ∀ v ∈ C.vs, v ∉ ids sp.1 := fun v hv h' => (hcv v hv).2 (by
      rw [hsp]; simp only [ids, List.map_append, List.mem_append] at h' ⊢; exact Or.inl h')
    have hE : CtxOK V C E := hC.congr fun v hv =>
      (aext_off V sp.1 μ v (hvpre v hv)).trans (hμ v hv)
    set F := aext V nw E
    have hval := hok.val E hE haV
    have hPF : ipDen (aext V (sp.2.2.map (atSub sp.2.1.id P)) F) P = ipDen F P :=
      ipDen_aext V _ P (by simpa [plainP, ids, atSub, List.map_map, Function.comp_def] using hPpost) F
    rw [bodyOf_sub, hPF, ← aext_sub V sp.2.2 sp.2.1.id hz P hPpost hPz F, ← hval]
    refine bodyOf_reads _ _ _ _ _ fun y hy => ?_
    have hS : ∀ v ∈ argVs sp.2.2 ++ ids sp.2.2, v ∈ allV t := by
      intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact hargs v (by rw [hsp]; simp only [argVs, List.flatMap_append, List.flatMap_cons,
          List.mem_append]; exact Or.inr (Or.inr hv))
      · exact hids v (by rw [hsp]; simp only [ids, List.map_append, List.map_cons,
          List.mem_append, List.mem_cons]; exact Or.inr (Or.inr hv))
    refine aext_agree V sp.2.2 (allV t) hS _ _ (fun v hv => ?_) y (by
      simp only [allV, rvs, fvs, List.mem_append]; left; left; left; exact hy)
    by_cases e : v = sp.2.1.id
    · subst e; simp
    · rw [Function.update_of_ne e, Function.update_of_ne e]
      exact aext_off V nw E v fun h' => by have := hnwB v h'; have := hlt v hv; omega
  · simp at h

/-- A root of unity of order `D1`, `D1 ∣ D2`, read as one of order `D2`: `ω_{D1}^p = ω_{D2}^(q p)`,
`q` the quotient atom. -/
def xPh (C : Ctx) (t : ATm) : Option ATm :=
  firstSome (fun sp : List Fac × Fac × List Fac =>
    match C.dv.find? (fun w => sp.2.1.1 == w.1 && w.1 != w.2) with
    | some w => some ⟨t.c, t.sums, ⟨maxV t + 1, 12, [], [w.2, w.1], []⟩ :: t.ats, t.dels,
        sp.1 ++ (w.2, ipMul (ipV (maxV t + 1)) sp.2.1.2) :: sp.2.2⟩
    | none => none) (splits t.phs)

theorem om_div (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b) (k : ℤ) :
    om b ^ (((b / a : ℕ) : ℤ) * k) = om a ^ k := by
  obtain ⟨q, rfl⟩ := hab
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hb
    · exact h
  rw [Nat.mul_div_cancel_left _ ha, zpow_mul]
  congr 1
  simp only [om, zpow_natCast, ← Complex.exp_nat_mul]
  congr 1
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  push_cast
  field_simp

theorem xPh_ok (V : LV) (C : Ctx) (t t' : ATm) (h : xPh C t = some t') (ν : ℕ → ℤ)
    (hC : CtxOK V C ν) : t'.den V ν = t.den V ν := by
  obtain ⟨sp, hsp, he⟩ := firstSome_spec _ _ _ h
  have hs := splits_spec _ sp hsp
  split at he
  · next w hw =>
    simp only [Option.some.injEq] at he
    subst he
    have hw' := List.find?_some hw
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hw'
    obtain ⟨hf, -⟩ := hw'
    obtain ⟨hpos, hpos2, hdvd⟩ := hC.2.2 w (List.mem_of_find?_eq_some hw)
    set B := maxV t + 1
    have hlt : ∀ v ∈ allV t, v < B := fun v hv => Nat.lt_succ_of_le (le_foldr_max _ v hv)
    unfold ATm.den
    simp only
    congr 1
    refine sumsV_congr _ _ _ _ (fun μ => ?_) ν
    unfold abody
    simp only [aext]
    have hBt : B ∉ argVs t.ats ++ ids t.ats := fun h' => by
      have := hlt B (by simp only [allV, rvs, List.mem_append] at h' ⊢; tauto); omega
    rw [aext_upd V t.ats B hBt]
    set E := aext V t.ats μ
    have hq : aval V μ ⟨B, 12, [], [w.2, w.1], []⟩ = ((w.2.den V.ρ.dv / w.1.den V.ρ.dv : ℕ) : ℤ) := by
      simp [aval, bfn]
    rw [hq]
    have hfac : ∀ g ∈ t.dels ++ t.phs, ∀ y ∈ facVars g, y ≠ B := fun g hg y hy e => by
      have hy' : y ∈ fvs t := List.mem_flatMap.2 ⟨g, hg, hy⟩
      have := hlt y (by simp only [allV, rvs, List.mem_append]; exact Or.inl (Or.inl (Or.inl hy')))
      omega
    have hrd : ∀ g ∈ t.dels ++ t.phs, ∀ v : ℤ,
        ipDen (Function.update E B v) g.2 = ipDen E g.2 := fun g hg v =>
      ipDen_reads _ _ _ fun y hy => Function.update_of_ne (hfac g hg y hy) _ _
    simp only [bodyOf]
    rw [hs] at hrd ⊢
    simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
    congr 1
    · congr 1; exact List.map_congr_left fun g hg => by
        unfold delV; rw [hrd g (List.mem_append_left _ hg)]
    · have e1 : ∀ l : List Fac, (∀ g ∈ l, g ∈ t.dels ++ (sp.1 ++ sp.2.1 :: sp.2.2)) →
          (l.map (phV V.ρ.dv (Function.update E B ((w.2.den V.ρ.dv / w.1.den V.ρ.dv : ℕ) : ℤ)))).prod =
            (l.map (phV V.ρ.dv E)).prod := fun l hl => congrArg _ (List.map_congr_left fun g hg => by
              unfold phV; rw [hrd g (hl g hg)])
      rw [e1 sp.1 (fun g hg => by simp [hg]), e1 sp.2.2 (fun g hg => by simp [hg])]
      congr 2
      unfold phV
      simp only [ipDen_mul, ipDen_V, Function.update_self]
      rw [hrd _ (by simp), hf]
      exact om_div _ _ hpos hpos2 hdvd _
  · simp at he

/-- A delta `[D2 ∣ q p]`, `q` the table's quotient atom `D2 / D1` and `D1 ∣ D2`, read as
`[D1 ∣ p]`. -/
def xDel (C : Ctx) (t : ATm) : Option ATm :=
  if (ids t.ats).Nodup then
    firstSome (fun sp : List Fac × Fac × List Fac =>
      firstSome (fun w : DMon × DMon =>
        match t.ats.find? (fun b => b.f == 12 && b.dp == [w.2, w.1] && b.args.isEmpty) with
        | some z =>
          if sp.2.1.1 = w.2 then
            match ipLin z.id sp.2.1.2 with
            | some (P', R) =>
              if R = [] ∧ ipHas z.id P' = false then
                some ⟨t.c, t.sums, t.ats, sp.1 ++ (w.1, P') :: sp.2.2, t.phs⟩
              else none
            | none => none
          else none
        | none => none) C.dv) (splits t.dels)
  else none

theorem xDel_ok (V : LV) (C : Ctx) (t t' : ATm) (h : xDel C t = some t') (ν : ℕ → ℤ)
    (hC : CtxOK V C ν) : t'.den V ν = t.den V ν := by
  unfold xDel at h
  split_ifs at h with hnd
  obtain ⟨sp, hsp, he⟩ := firstSome_spec _ _ _ h
  have hs := splits_spec _ sp hsp
  obtain ⟨w, hw, he⟩ := firstSome_spec _ _ _ he
  split at he
  · next z hz =>
    split_ifs at he with hD
    split at he
    · next P' R hlin =>
      split_ifs at he with hR
      simp only [Option.some.injEq] at he
      subst he
      obtain ⟨hR0, -⟩ := hR
      subst hR0
      have hz' := List.find?_some hz
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hz'
      obtain ⟨⟨hf, hdp⟩, hargs⟩ := hz'
      have hzm := List.mem_of_find?_eq_some hz
      obtain ⟨hpos, hpos2, hdvd⟩ := hC.2.2 w hw
      obtain ⟨-, -, hp⟩ := ipLin_spec _ _ _ _ hlin
      refine den_of_pw V t ⟨t.c, t.sums, t.ats, sp.1 ++ (w.1, P') :: sp.2.2, t.phs⟩ rfl
        (fun μ => ?_) ν
      simp only
      congr 1
      unfold abody
      simp only
      obtain ⟨μ', hv, -⟩ := aext_find V t.ats z.id z hnd (find_id _ hnd _ hzm) μ
      have hq : aext V t.ats μ z.id = ((w.2.den V.ρ.dv / w.1.den V.ρ.dv : ℕ) : ℤ) := by
        rw [hv]; simp [aval, hf, hdp, hargs, bfn]
      obtain ⟨q, hq2⟩ := hdvd
      have hqpos : 0 < q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · rw [h0] at hq2; omega
        · exact h0
      have hqv : w.2.den V.ρ.dv / w.1.den V.ρ.dv = q := by
        rw [hq2, Nat.mul_div_cancel_left _ hpos]
      simp only [bodyOf]
      rw [hs]
      simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
      congr 2
      unfold delV
      rw [hp, hq, hqv, ipDen_nil, add_zero, hD, hq2]
      simp only [Nat.cast_mul]
      rw [mul_comm ((w.1.den V.ρ.dv : ℕ) : ℤ) (q : ℤ), mul_comm _ (q : ℤ)]
      have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hqpos.ne'
      simp only [mul_dvd_mul_iff_left hq0]
    · simp at he
  · simp at he

/-- The atoms, roots of unity and deltas rewritten under the context, at most `n` times. -/
def xRules (C : Ctx) : ℕ → ATm → ATm
  | 0, t => t
  | n + 1, t => match firstSome (xAt C t) (splits t.ats) with
    | some t' => xRules C n t'
    | none => match xPh C t with
      | some t' => xRules C n t'
      | none => match xDel C t with
        | some t' => xRules C n t'
        | none => t

theorem xRules_ok (V : LV) (hρ : V.ρ.OK) (C : Ctx) (n : ℕ) (t : ATm) (ν : ℕ → ℤ)
    (hC : CtxOK V C ν) : (xRules C n t).den V ν = t.den V ν := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [xRules]
    split
    · next t' h =>
      obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h
      rw [ih, xAt_ok V hρ C t t' p (splits_spec _ p hp) he ν hC]
    · split
      · next t' h => rw [ih, xPh_ok V C t t' h ν hC]
      · split
        · next t' h => rw [ih, xDel_ok V C t t' h ν hC]
        · rfl

/-! ## Splitting a remainder by its one exceptional value -/

/-- A delta `[M ∣ s z + R]`, `z = mod(u, N - 1)` of the table, `u = mod(y, N)`, as the three terms
`[M ∣ s u + R] - [N ∣ u + 1] [M ∣ s u + R] + [N ∣ u + 1] [M ∣ R]`. -/
def splitOf (t : ATm) (sp : List Fac × Fac × List Fac) : Option (List ATm) :=
  firstSome (fun z =>
    match findAt t.ats z with
    | some b =>
      match b.f, b.dp, b.args with
      | 13, [N], [([([u], 1)], Z)] =>
        if Z = ZM ∧ isRed t.ats u N = true ∧ N.c ≠ 0 then
          match ipLin z sp.2.1.2 with
          | some (A, R) =>
            match ipConst A with
            | some s =>
              if (s == 1 || s == -1) && wfA t.ats && (ids t.ats).Nodup then
                some [⟨t.c, t.sums, t.ats, sp.1 ++ (sp.2.1.1, ipAdd (ipSmul s (ipV u)) R) :: sp.2.2,
                    t.phs⟩,
                  ⟨{ t.c with q := -t.c.q }, t.sums, t.ats,
                    sp.1 ++ (sp.2.1.1, ipAdd (ipSmul s (ipV u)) R) :: (N, ipAdd (ipV u) (ipC 1)) ::
                      sp.2.2, t.phs⟩,
                  ⟨t.c, t.sums, t.ats, sp.1 ++ (sp.2.1.1, R) :: (N, ipAdd (ipV u) (ipC 1)) :: sp.2.2,
                    t.phs⟩]
              else none
            | none => none
          | none => none
        else none
      | _, _, _ => none
    | none => none) (facVars sp.2.1)

theorem sumsV_sub_add (dv : ℕ → ℕ) (s : List (ℕ × DMon)) (f g k : (ℕ → ℤ) → ℂ) (ν : ℕ → ℤ) :
    sumsV dv s (fun μ => f μ - g μ + k μ) ν = sumsV dv s f ν - sumsV dv s g ν + sumsV dv s k ν := by
  induction s generalizing ν with
  | nil => rfl
  | cons p s ih =>
    simp only [sumsV, ih, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem den_negq (V : LV) (c : CMon) (sums : List (ℕ × DMon)) (ats : List Atom)
    (dels phs : List Fac) (ν : ℕ → ℤ) :
    ATm.den V ν ⟨{ c with q := -c.q }, sums, ats, dels, phs⟩ =
      -ATm.den V ν ⟨c, sums, ats, dels, phs⟩ := by
  unfold ATm.den abody
  simp only [CMon.den]
  push_cast; ring

theorem splitOf_ok (V : LV) (hρ : V.ρ.OK) (t : ATm) (ts : List ATm)
    (sp : List Fac × Fac × List Fac) (hsp : t.dels = sp.1 ++ sp.2.1 :: sp.2.2)
    (h : splitOf t sp = some ts) (ν : ℕ → ℤ) : axDen V ν ts = t.den V ν := by
  obtain ⟨z, -, h⟩ := firstSome_spec _ _ _ h
  split at h
  · next b hb =>
    split at h
    · next N u Z hf hdp hargs =>
      split_ifs at h with hc
      obtain ⟨hZ, hred, hN0⟩ := hc
      subst hZ
      split at h
      · next A R hlin =>
        split at h
        · next s hs =>
          split_ifs at h with hc2
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc2
          obtain ⟨⟨hs1, hw⟩, hn⟩ := hc2
          obtain ⟨-, -, hp⟩ := ipLin_spec z _ A R hlin
          have hsv : ∀ μ, ipDen μ A = s := fun μ => ipConst_spec A s hs μ
          have hNpos : 0 < N.den V.ρ.dv := DMon.den_pos _ hρ.dpos _ (Nat.pos_of_ne_zero hN0)
          rw [axDen_cons, axDen_cons, axDen_cons, axDen_nil, add_zero]
          have key : ∀ μ, bodyOf V.ρ.dv (sp.1 ++ (sp.2.1.1, ipAdd (ipSmul s (ipV u)) R) :: sp.2.2)
              t.phs (aext V t.ats μ) - bodyOf V.ρ.dv (sp.1 ++ (sp.2.1.1, ipAdd (ipSmul s (ipV u)) R) ::
              (N, ipAdd (ipV u) (ipC 1)) :: sp.2.2) t.phs (aext V t.ats μ) +
              bodyOf V.ρ.dv (sp.1 ++ (sp.2.1.1, R) :: (N, ipAdd (ipV u) (ipC 1)) :: sp.2.2) t.phs
              (aext V t.ats μ) = bodyOf V.ρ.dv t.dels t.phs (aext V t.ats μ) := by
            intro μ
            set E := aext V t.ats μ
            obtain ⟨hbm, hbid⟩ := findAt_spec _ _ _ hb
            have hEz : E z = E u % ((N.den V.ρ.dv : ℤ) - 1) := by
              rw [← hbid]
              show aext V t.ats μ b.id = _
              rw [aext_fix V t.ats hw hn μ b hbm]
              simp [aval, hf, hdp, hargs, bfn, argV_zm, ipDen, imDen]
              rfl
            have hEu : 0 ≤ E u ∧ E u < N.den V.ρ.dv := by
              unfold isRed at hred
              cases hc : findAt t.ats u with
              | none => simp [hc] at hred
              | some c =>
                rw [hc] at hred
                simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hred
                obtain ⟨hcf, hca⟩ := hred
                obtain ⟨hcm, hcid⟩ := findAt_spec _ _ _ hc
                show 0 ≤ aext V t.ats μ u ∧ aext V t.ats μ u < _
                rw [← hcid, aext_fix V t.ats hw hn μ c hcm]
                split at hca
                · next y M hcargs =>
                  simp only [beq_iff_eq] at hca
                  subst hca
                  simp only [aval, hcf, hcargs, show (2 : ℕ) < 100 by norm_num, if_true, bfn,
                    List.map_cons, List.map_nil, argV, List.getD_cons_zero]
                  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
                · simp at hca
            unfold bodyOf
            rw [hsp]
            simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
            unfold delV
            simp only [hp, hsv, ipDen_add, ipDen_smul, ipDen_V, ipDen_C, hEz]
            by_cases hcase : ((N.den V.ρ.dv : ℕ) : ℤ) ∣ E u + 1
            · have hv : E u = N.den V.ρ.dv - 1 := by
                obtain ⟨k, hk⟩ := hcase
                rcases lt_trichotomy k 1 with hk1 | rfl | hk1
                · have : k ≤ 0 := by omega
                  nlinarith [hEu.1]
                · omega
                · nlinarith [hEu.2]
              rw [if_pos hcase, hv, Int.emod_self]
              simp only [mul_zero, zero_add]
              ring
            · have hlt : E u < (N.den V.ρ.dv : ℤ) - 1 := by
                rcases lt_or_eq_of_le (show E u ≤ (N.den V.ρ.dv : ℤ) - 1 by omega) with h1 | h1
                · exact h1
                · exact absurd ⟨1, by omega⟩ hcase
              rw [if_neg hcase, Int.emod_eq_of_lt hEu.1 hlt]
              ring
          rw [den_negq]
          unfold ATm.den abody
          simp only
          rw [show ∀ a b c d : ℂ, a * b + (-(a * c) + a * d) = a * (b - c + d) from
            fun a b c d => by ring, ← sumsV_sub_add]
          congr 1
          exact sumsV_congr _ _ _ _ (fun μ => key μ) ν
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- Every term's atoms and roots of unity rewritten under the context, and remainders split. -/
def xpass (C : Ctx) (e : List ATm) : List ATm :=
  (e.map fun t => xRules C (t.ats.length + t.phs.length + t.dels.length + 1) t).flatMap fun t =>
    match firstSome (splitOf t) (splits t.dels) with
    | some ts => ts
    | none => [t]

theorem axDen_flatMap (V : LV) (ν : ℕ → ℤ) (e : List ATm) (g : ATm → List ATm)
    (h : ∀ t ∈ e, axDen V ν (g t) = t.den V ν) : axDen V ν (e.flatMap g) = axDen V ν e := by
  induction e with
  | nil => rfl
  | cons t e ih =>
    rw [List.flatMap_cons, axDen_append, h t List.mem_cons_self, axDen_cons,
      ih fun t' ht' => h t' (List.mem_cons_of_mem _ ht')]

theorem axDen_xpass (V : LV) (hρ : V.ρ.OK) (C : Ctx) (e : List ATm) (ν : ℕ → ℤ)
    (hC : CtxOK V C ν) : axDen V ν (xpass C e) = axDen V ν e := by
  unfold xpass
  rw [axDen_flatMap]
  · unfold axDen
    rw [List.map_map]
    congr 1
    exact List.map_congr_left fun t _ => xRules_ok V hρ C _ t ν hC
  · intro t _
    split
    · next ts hts =>
      obtain ⟨sp, hsp, he⟩ := firstSome_spec _ _ _ hts
      exact splitOf_ok V hρ t ts sp (splits_spec _ sp hsp) he ν
    · rw [axDen_cons, axDen_nil, add_zero]

/-- The difference normalised after the pass, and once more when terms are left. -/
def close2 (fl : List ℕ) (PW : List (DMon × DMon)) (C : Ctx) (e : List ATm) : Bool :=
  (nfA fl PW (xpass C e)).isEmpty || (nfA fl PW (xpass C (nfA fl PW (xpass C e)))).isEmpty

theorem close2_ok (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (C : Ctx) (e : List ATm)
    (h : close2 fl PW C e = true) (ν : ℕ → ℤ) (hC : CtxOK V C ν) : axDen V ν e = 0 := by
  unfold close2 at h
  simp only [Bool.or_eq_true, List.isEmpty_iff] at h
  rcases h with h | h
  · rw [← axDen_xpass V hρ C e ν hC]; exact nfA_zero V hρ fl hfl PW hPW _ h ν
  · rw [← axDen_xpass V hρ C e ν hC, ← nfA_den V hρ fl hfl PW hPW _ ν,
      ← axDen_xpass V hρ C _ ν hC]
    exact nfA_zero V hρ fl hfl PW hPW _ h ν

/-! ## Free variables in their ranges -/

/-- `v` read through a new atom `mod(v, D)` in every factor and atom of `t`. -/
def rgOne (v : ℕ) (D : DMon) (t : ATm) : ATm :=
  if (fvs t ++ argVs t.ats).contains v && !(abvs t).contains v && !(ids t.ats).contains v then
    ⟨t.c, t.sums, ⟨maxV t + 1, 2, [], [], [(ipV v, D)]⟩ :: t.ats.map (atSub v (ipV (maxV t + 1))),
      t.dels.map (facSub v (ipV (maxV t + 1))), t.phs.map (facSub v (ipV (maxV t + 1)))⟩
  else t

/-- `rgOne` for each variable and range of `rg`. -/
def rgT (rg : List (ℕ × DMon)) (t : ATm) : ATm := rg.foldl (fun t p => rgOne p.1 p.2 t) t

/-- Every variable of `rg` lies in its range at `ν`. -/
def RgOK (V : LV) (rg : List (ℕ × DMon)) (ν : ℕ → ℤ) : Prop :=
  ∀ p ∈ rg, 0 ≤ ν p.1 ∧ ν p.1 < (p.2.den V.ρ.dv : ℤ)

theorem rgOne_ok (V : LV) (v : ℕ) (D : DMon) (t : ATm) (ν : ℕ → ℤ) (h0 : 0 ≤ ν v)
    (h1 : ν v < (D.den V.ρ.dv : ℤ)) : (rgOne v D t).den V ν = t.den V ν := by
  unfold rgOne
  split_ifs with hc
  · simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_true_eq,
      decide_eq_false_iff_not] at hc
    obtain ⟨⟨hr, hb⟩, hi⟩ := hc
    set B := maxV t + 1
    have hlt : ∀ w ∈ allV t, w < B := fun w hw => Nat.lt_succ_of_le (le_foldr_max _ w hw)
    have hBi : B ∉ ids t.ats := fun h => by
      have := hlt B (by simp only [allV, rvs, List.mem_append]; tauto); omega
    have hBa : B ∉ argVs t.ats := fun h => by
      have := hlt B (by simp only [allV, rvs, List.mem_append]; tauto); omega
    have hBf : B ∉ fvs t := fun h => by
      have := hlt B (by simp only [allV, rvs, List.mem_append]; tauto); omega
    have hvB : v ≠ B := by
      intro e
      have := hlt v (by
        simp only [List.mem_append] at hr
        simp only [allV, rvs, List.mem_append]; tauto)
      omega
    unfold ATm.den
    simp only
    congr 1
    refine sumsV_congr_off _ _ [v] _ _ (fun p hp hv => ?_) ν fun μ hμ => ?_
    · simp only [List.mem_singleton] at hv
      exact hb (by rw [← hv]; exact List.mem_map_of_mem hp)
    · have hμv : μ v = ν v := hμ v (by simp)
      unfold abody
      simp only [aext]
      have hav : aval V μ ⟨B, 2, [], [], [(ipV v, D)]⟩ = μ v := by
        simp only [aval, show (2 : ℕ) < 100 by norm_num, if_true, bfn, List.map_cons,
          List.map_nil, List.getD_cons_zero, argV, ipDen_V]
        rw [hμv]
        exact Int.emod_eq_of_lt h0 h1
      rw [hav]
      set μ' := Function.update μ B (μ v)
      have hpl : plainP t.ats (ipV B) = true := by
        simp only [plainP, ipVs_V, List.all_cons, List.all_nil, Bool.and_true, Bool.not_eq_true',
          List.contains_eq_mem, decide_eq_false_iff_not]
        exact hBi
      have hhs : ipHas v (ipV B) = false := by
        simp only [ipHas, ipV, List.any_cons, List.any_nil, Bool.or_false, List.contains_cons,
          List.contains_nil, Bool.or_false, beq_eq_false_iff_ne, ne_eq]
        simp [hvB]
      have e1 := aext_sub V t.ats v hi (ipV B) hpl hhs μ'
      have hμ'B : μ' B = μ v := Function.update_self _ _ _
      have hμ'v : Function.update μ' v (μ v) = μ' := by
        rw [show μ v = μ' v from (Function.update_of_ne hvB _ _).symm, Function.update_eq_self]
      rw [ipDen_V, hμ'B, hμ'v] at e1
      have hBi' : B ∉ ids (t.ats.map (atSub v (ipV B))) := by
        simpa [ids, atSub, List.map_map, Function.comp_def] using hBi
      rw [bodyOf_sub, ipDen_V, aext_off V _ μ' B hBi', hμ'B, ← e1]
      have hup : aext V t.ats μ' = Function.update (aext V t.ats μ) B (μ v) :=
        aext_upd V t.ats B (by simp only [List.mem_append, not_or]; exact ⟨hBa, hBi⟩) μ (μ v)
      rw [hup]
      refine bodyOf_reads _ _ _ _ _ fun y hy => ?_
      have hyB : y ≠ B := fun e => hBf (by rw [← e]; simpa [fvs] using hy)
      exact Function.update_of_ne hyB _ _
  · rfl

theorem rgT_ok (V : LV) (rg : List (ℕ × DMon)) (ν : ℕ → ℤ) (h : RgOK V rg ν) (t : ATm) :
    (rgT rg t).den V ν = t.den V ν := by
  unfold rgT
  induction rg generalizing t with
  | nil => rfl
  | cons p rg ih =>
    simp only [List.foldl_cons]
    rw [ih (fun q hq => h q (List.mem_cons_of_mem _ hq)),
      rgOne_ok V p.1 p.2 t ν (h p List.mem_cons_self).1 (h p List.mem_cons_self).2]

theorem axDen_rg (V : LV) (rg : List (ℕ × DMon)) (e : List ATm) (ν : ℕ → ℤ) (h : RgOK V rg ν) :
    axDen V ν (e.map (rgT rg)) = axDen V ν e := by
  simp only [axDen, List.map_map, Function.comp_def, rgT_ok V rg ν h]

end DiracULA.LSym
