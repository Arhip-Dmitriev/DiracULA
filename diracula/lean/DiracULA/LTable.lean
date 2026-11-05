/-
Copyright 2026 Arkhip A. Dmitriev
Licensed under the Apache License, Version 2.0.
-/
import DiracULA.LDigit

/-!
# Atom tables in any dependency order

A table whose atoms read only atoms before them (`wfA`), with distinct variables, has its values
fixed by the atoms' equations (`aext_fix`, `aext_unique`); every such ordering of the same atoms
gives the same values (`aext_perm`). `sortTab` orders a table canonically; `elimPinC` pins a
variable to a constant of its own range; `elimPinA` pins a variable to a value read from atoms,
the atoms not reading the variable moved first.
-/

namespace DiracULA.LSym

open DiracULA.Sym Complex Finset

/-- Each atom's arguments read no atom of its own or a later position. -/
def wfA : List Atom → Bool
  | [] => true
  | a :: l => (atVs a).all (fun v => !(ids (a :: l)).contains v) && wfA l

theorem wfA_cons (a : Atom) (l : List Atom) (h : wfA (a :: l) = true) :
    (∀ v ∈ atVs a, v ∉ ids (a :: l)) ∧ wfA l = true := by
  simp only [wfA, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at h
  exact h

/-- The modulus of an unreduced argument. -/
def ZM : DMon := ⟨0, []⟩

theorem argV_zm (dv : ℕ → ℕ) (ν : ℕ → ℤ) (p : IPoly) : argV dv ν (p, ZM) = ipDen ν p := by
  simp [argV, ZM, DMon.den]

/-! ## Values fixed by the equations -/

theorem aext_fix (V : LV) (l : List Atom) (hw : wfA l = true) (hn : (ids l).Nodup)
    (μ : ℕ → ℤ) : ∀ a ∈ l, aext V l μ a.id = aval V (aext V l μ) a := by
  induction l generalizing μ with
  | nil => intro a ha; simp at ha
  | cons b l ih =>
    obtain ⟨hb, hw'⟩ := wfA_cons b l hw
    simp only [ids, List.map_cons, List.nodup_cons] at hn
    intro a ha
    simp only [aext]
    rcases List.mem_cons.1 ha with rfl | ha'
    · rw [aext_off V l _ _ hn.1, Function.update_self]
      refine aval_reads V a _ _ fun y hy => ?_
      have hy' := hb y hy
      simp only [ids, List.map_cons, List.mem_cons, not_or] at hy'
      rw [aext_off V l _ _ hy'.2, Function.update_of_ne hy'.1]
    · exact ih hw' hn.2 _ a ha'

theorem aext_unique (V : LV) (l : List Atom) (hw : wfA l = true) (μ F : ℕ → ℤ)
    (hoff : ∀ y, y ∉ ids l → F y = μ y) (hfix : ∀ a ∈ l, F a.id = aval V F a) :
    aext V l μ = F := by
  induction l generalizing μ with
  | nil => funext y; exact (hoff y (by simp [ids])).symm
  | cons b l ih =>
    obtain ⟨hb, hw'⟩ := wfA_cons b l hw
    simp only [aext]
    refine ih hw' _ (fun y hy => ?_) (fun a ha => hfix a (List.mem_cons_of_mem _ ha))
    by_cases e : y = b.id
    · subst e
      rw [Function.update_self, hfix b List.mem_cons_self]
      refine aval_reads V b _ _ fun z hz => hoff z (hb z hz)
    · rw [Function.update_of_ne e]
      exact hoff y (by simp only [ids, List.map_cons, List.mem_cons, not_or]; exact ⟨e, hy⟩)

theorem ids_perm {l l' : List Atom} (h : l'.Perm l) : (ids l').Perm (ids l) := h.map _

/-- Two dependency orders of the same atoms give the same values. -/
theorem aext_perm (V : LV) (l l' : List Atom) (h : l'.Perm l) (hw : wfA l = true)
    (hw' : wfA l' = true) (hn : (ids l).Nodup) (μ : ℕ → ℤ) : aext V l μ = aext V l' μ := by
  have hn' : (ids l').Nodup := (ids_perm h).nodup_iff.2 hn
  refine aext_unique V l hw μ _ (fun y hy => aext_off V l' μ y fun hy' => hy ((ids_perm h).mem_iff.1 hy'))
    (fun a ha => aext_fix V l' hw' hn' μ a (h.mem_iff.2 ha))

/-- New atoms reading only variables below `B`, with variables from `B` on, take their values
at `E`. -/
theorem aext_new (V : LV) (B : ℕ) (nw : List Atom) (hid : ∀ b ∈ nw, B ≤ b.id)
    (hrd : ∀ b ∈ nw, ∀ y ∈ atVs b, y < B) (hn : (ids nw).Nodup) (E : ℕ → ℤ) :
    ∀ b ∈ nw, aext V nw E b.id = aval V E b := by
  have hw : wfA nw = true := by
    clear hn
    induction nw with
    | nil => rfl
    | cons b l ih =>
      simp only [wfA, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not]
      refine ⟨fun y hy hy' => ?_, ih (fun c hc => hid c (List.mem_cons_of_mem _ hc))
        (fun c hc => hrd c (List.mem_cons_of_mem _ hc))⟩
      have h1 := hrd b List.mem_cons_self y hy
      simp only [ids, List.mem_map] at hy'
      obtain ⟨c, hc, rfl⟩ := hy'
      have := hid c hc
      omega
  intro b hb
  rw [aext_fix V nw hw hn E b hb]
  refine aval_reads V b _ _ fun y hy => aext_off V nw E y fun hy' => ?_
  simp only [ids, List.mem_map] at hy'
  obtain ⟨c, hc, rfl⟩ := hy'
  have := hid c hc
  have := hrd b hb _ hy
  omega

/-- The greatest variable a term names. -/
def maxV (t : ATm) : ℕ := (allV t).foldr max 0

theorem le_foldr_max (l : List ℕ) (v : ℕ) (h : v ∈ l) : v ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h'
    · exact le_max_left _ _
    · exact (ih h').trans (le_max_right _ _)

/-! ## The canonical order -/

/-- A dimension monomial as integers. -/
def dmKey (m : DMon) : List ℤ := (m.c : ℤ) :: (m.e.length : ℤ) :: m.e.map (fun x : ℕ => (x : ℤ))

/-- A polynomial as integers. -/
def ipKey (p : IPoly) : List ℤ :=
  (p.length : ℤ) :: p.flatMap fun t => (t.1.length : ℤ) :: t.1.map (fun x : ℕ => (x : ℤ)) ++ [t.2]

/-- An atom without its variable as integers, the function first and negated. -/
def atKey (a : Atom) : List ℤ :=
  -(a.f : ℤ) :: (a.ks.length : ℤ) :: a.ks ++ (a.dp.length : ℤ) :: a.dp.flatMap dmKey ++
    (a.args.length : ℤ) :: a.args.flatMap fun p => ipKey p.1 ++ dmKey p.2

/-- Lexicographic order on integer lists. -/
def zLt : List ℤ → List ℤ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: a, y :: b => if x = y then zLt a b else decide (x < y)

/-- The atom of least key among those reading no atom of `rest`, the first on ties. -/
def pickMin (rest : List Atom) : Option Atom :=
  (rest.filter fun a => (atVs a).all fun v => !(ids rest).contains v).foldl
    (fun acc a => match acc with
      | none => some a
      | some b => if zLt (atKey a) (atKey b) then some a else some b) none

/-- The atoms of `rest` after `acc`, each step the atom `pickMin` gives. -/
def topo : ℕ → List Atom → List Atom → Option (List Atom)
  | _, acc, [] => some acc
  | 0, _, _ :: _ => none
  | n + 1, acc, a :: rest =>
    match pickMin (a :: rest) with
    | some b => topo n (acc ++ [b]) ((a :: rest).erase b)
    | none => none

/-- The table in canonical order, when that order is a dependency order of the same atoms. -/
def sortTab (t : ATm) : ATm :=
  match topo (t.ats.length + 1) [] t.ats with
  | some l =>
    if wfA t.ats && (ids t.ats).Nodup && wfA l && l.isPerm t.ats then
      ⟨t.c, t.sums, l, t.dels, t.phs⟩
    else t
  | none => t

theorem sortTab_ok (V : LV) (t : ATm) (ν : ℕ → ℤ) : (sortTab t).den V ν = t.den V ν := by
  unfold sortTab
  split
  · next l _ =>
    split_ifs with hc
    · simp only [Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hc
      obtain ⟨⟨⟨hw, hn⟩, hw'⟩, hp⟩ := hc
      unfold ATm.den abody
      simp only
      congr 1
      refine sumsV_congr _ _ _ _ (fun μ => ?_) ν
      rw [aext_perm V t.ats l hp hw hw' hn μ]
    · rfl
  · rfl

/-! ## Pinning to a constant of the variable's range -/

/-- `x` pinned by `[D ∣ s x + c]`, `D` the constant range of `x`, `s = ±1`, `c` constant: `x`
set to `(-s c) mod D`. -/
def elimPinC1 (x : ℕ) (D : DMon) (ats : List Atom) (pre : List Fac) (f : Fac) (post ps : List Fac) :
    Option AElim :=
  match ipLin x f.2 with
  | some (a, b) =>
    match ipConst a, ipConst b with
    | some s, some c =>
      if (s == 1 || s == -1) && D.isConst && D.c != 0 && f.1 == D && !(ids ats).contains x then
        some ⟨CMon.ofQ 1, ats.map (atSub x (ipC ((-s * c) % (D.c : ℤ)))),
          (pre ++ post).map (facSub x (ipC ((-s * c) % (D.c : ℤ)))),
          ps.map (facSub x (ipC ((-s * c) % (D.c : ℤ))))⟩
      else none
    | _, _ => none
  | none => none

theorem sum_pin_exact (D : ℕ) (hD : 0 < D) (v : ℤ) (g : ℤ → ℂ) :
    ∑ j ∈ range D, (if (D : ℤ) ∣ (j : ℤ) - v then g j else 0) = g (v % D) := by
  have hv0 : 0 ≤ v % (D : ℤ) := Int.emod_nonneg _ (by omega)
  have hv1 : v % (D : ℤ) < D := Int.emod_lt_of_pos _ (by omega)
  have key : ∀ j ∈ range D, ((D : ℤ) ∣ (j : ℤ) - v ↔ j = (v % (D : ℤ)).toNat) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [← Int.modEq_iff_dvd]
    unfold Int.ModEq
    rw [Int.emod_eq_of_lt (show (0 : ℤ) ≤ j by positivity) (show (j : ℤ) < D by exact_mod_cast hj')]
    omega
  rw [Finset.sum_congr rfl fun j hj => if_congr (key j hj) rfl rfl,
    Finset.sum_ite_eq' (range D) _ (fun j : ℕ => g j), if_pos (Finset.mem_range.2 (by omega)),
    Int.toNat_of_nonneg hv0]

theorem elimPinC1_ok (V : LV) (x : ℕ) (D : DMon) (ats : List Atom) (pre : List Fac)
    (f : Fac) (post ps : List Fac) (e : AElim) (h : elimPinC1 x D ats pre f post ps = some e) :
    AElimOK V x D ats (pre ++ f :: post) ps e := by
  unfold elimPinC1 at h
  split at h
  · next a b hlin =>
    split at h
    · next s c hs hc =>
      split_ifs at h with hcc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
        Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hcc
      obtain ⟨⟨⟨⟨hs1, hD⟩, hD0⟩, hf⟩, hx⟩ := hcc
      obtain ⟨-, hb, hp⟩ := ipLin_spec x f.2 a b hlin
      intro ν
      have hden : D.den V.ρ.dv = D.c := DMon.den_isConst _ _ hD
      set v : ℤ := (-s * c) % (D.c : ℤ)
      set g : ℤ → ℂ := fun j => bodyOf V.ρ.dv (pre ++ post) ps (aext V ats (Function.update ν x j))
      have hsplit : ∀ j : ℤ, bodyOf V.ρ.dv (pre ++ f :: post) ps (aext V ats (Function.update ν x j)) =
          (if (D.c : ℤ) ∣ j - (-s * c) then g j else 0) := by
        intro j
        have hd : delV V.ρ.dv (aext V ats (Function.update ν x j)) f =
            if (D.c : ℤ) ∣ j - (-s * c) then 1 else 0 := by
          unfold delV
          rw [hp, ipConst_spec a s hs, ipConst_spec b c hc, aext_off V ats _ x hx,
            Function.update_self, hf, hden]
          simp only [pin_dvd s hs1]
        simp only [g, bodyOf, List.map_append, List.map_cons, List.prod_append, List.prod_cons, hd]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl fun (j : ℕ) _ => hsplit (j : ℤ), hden,
        sum_pin_exact D.c (Nat.pos_of_ne_zero hD0) (-s * c) g, ofQ_den, Rat.cast_one, one_mul,
        bodyOf_sub, ipDen_C]
      have hpl : plainP ats (ipC v) = true := by
        unfold plainP ipVs ipC ipIns; split_ifs <;> simp
      have hhs : ipHas x (ipC v) = false := by
        unfold ipHas ipC ipIns; split_ifs <;> simp
      have e := aext_sub V ats x hx (ipC v) hpl hhs ν
      rw [ipDen_C] at e
      simp only [g]
      rw [e]
    · simp at h
  · simp at h

/-- `x` pinned by the first delta of its constant range that pins it to a constant. -/
def elimPinC (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac) : Option AElim :=
  firstSome (fun p => elimPinC1 x D ats p.1 p.2.1 p.2.2 ps) (splits ds)

theorem elimPinC_ok (V : LV) (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac)
    (e : AElim) (h : elimPinC x D ats ds ps = some e) : AElimOK V x D ats ds ps e := by
  obtain ⟨p, hp, he⟩ := firstSome_spec _ _ _ h
  rw [splits_spec ds p hp]
  exact elimPinC1_ok V x D ats _ _ _ _ e he

/-! ## Pinning to a value read from atoms -/

/-- `elimPin` on the atoms reading `x`, those not reading it moved before them. -/
def elimPinA (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac) : Option AElim :=
  match elimPin x D (ats.filter (atReads x)) ds ps with
  | some e =>
    if !(ids ats).contains x && wfA ats && (ids ats).Nodup &&
        wfA (ats.filter (fun a => !atReads x a) ++ ats.filter (atReads x)) then
      some ⟨e.k, ats.filter (fun a => !atReads x a) ++ e.ats, e.ds, e.ps⟩
    else none
  | none => none

theorem elimPinA_ok (V : LV) (hρ : V.ρ.OK) (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac)
    (e : AElim) (h : elimPinA x D ats ds ps = some e) : AElimOK V x D ats ds ps e := by
  unfold elimPinA at h
  split at h
  · next e' he =>
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hc
    obtain ⟨⟨⟨hx, hw⟩, hn⟩, hw'⟩ := hc
    set A := ats.filter (fun a => !atReads x a)
    set B := ats.filter (atReads x)
    have hp : (A ++ B).Perm ats := by
      have := List.filter_append_perm (fun a => !atReads x a) ats
      simpa [A, B, Bool.not_not] using this
    have hok := elimPin_ok V hρ x D B ds ps e' he
    have hxA : x ∉ argVs A ++ ids A := by
      simp only [List.mem_append, not_or]
      constructor
      · simp only [argVs, List.mem_flatMap, not_exists, not_and]
        intro a ha hxa
        simp only [A, List.mem_filter, Bool.not_eq_true'] at ha
        simp [atReads, hxa] at ha
      · intro hxi
        apply hx
        simp only [ids] at hxi ⊢
        exact (List.filter_sublist.map _).subset hxi
    intro ν
    have hrw : ∀ j : ℤ, aext V ats (Function.update ν x j) =
        aext V B (Function.update (aext V A ν) x j) := by
      intro j
      rw [aext_perm V ats (A ++ B) hp hw hw' hn, aext_append, aext_upd V A x hxA]
    simp only [hrw]
    rw [hok (aext V A ν), aext_append]
  · simp at h

theorem wfA_append (l1 l2 : List Atom) (h : wfA (l1 ++ l2) = true) : wfA l1 = true := by
  induction l1 with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨ha, hw⟩ := wfA_cons a (l ++ l2) h
    simp only [wfA, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not]
    refine ⟨fun v hv hv' => ha v hv ?_, ih hw⟩
    simp only [ids, List.map_cons, List.mem_cons, List.map_append, List.mem_append] at hv' ⊢
    tauto

/-! ## Pinning to a reduced atom of the same range -/

/-- The reduced atom `u = mod(q, D)` of `A` that the delta `f` equates with `x` modulo `D`:
`f = [D ∣ s x + c u]`, `s = ±1`, `D ∣ s + c`. -/
def pinROf (x : ℕ) (D : DMon) (A : List Atom) (f : Fac) : Option ℕ :=
  if f.1 = D ∧ D.isConst = true ∧ D.c ≠ 0 then
    match ipLin x f.2 with
    | some (a, b) =>
      match ipConst a, b with
      | some s, [([u], c)] =>
        if (s = 1 ∨ s = -1) ∧ (s + c) % (D.c : ℤ) = 0 ∧
            ((A.find? fun b => b.id == u).any fun b => b.f == 2 && b.args.length == 1 &&
              (b.args.headD ([], ZM)).2 == D) = true then some u else none
      | _, _ => none
    | none => none
  else none

/-- `x` of constant range `D` pinned to a reduced atom `u = mod(q, D)` by a delta equating them
modulo `D`. -/
def elimPinR (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac) : Option AElim :=
  if (ids ats).contains x then none else
    match firstSome (fun p => (pinROf x D (ats.filter fun a => !atReads x a) p.2.1).map
        fun u => (p, u)) (splits ds) with
    | some (p, u) =>
      if wfA ats && (ids ats).Nodup &&
          wfA (ats.filter (fun a => !atReads x a) ++ ats.filter (atReads x)) then
        some ⟨CMon.ofQ 1, ats.filter (fun a => !atReads x a) ++
          (ats.filter (atReads x)).map (atSub x (ipV u)),
          (p.1 ++ p.2.2).map (facSub x (ipV u)), ps.map (facSub x (ipV u))⟩
      else none
    | none => none

theorem pinROf_spec (x : ℕ) (D : DMon) (A : List Atom) (f : Fac) (u : ℕ)
    (h : pinROf x D A f = some u) :
    f.1 = D ∧ D.isConst = true ∧ D.c ≠ 0 ∧ ∃ s c : ℤ, (s = 1 ∨ s = -1) ∧ (s + c) % (D.c : ℤ) = 0 ∧
      (∀ ν, ipDen ν f.2 = s * ν x + c * ν u) ∧ ∃ b ∈ A, b.id = u ∧ b.f = 2 ∧
        ∃ q, b.args = [(q, D)] := by
  unfold pinROf at h
  split_ifs at h with h1
  split at h
  · next a b hlin =>
    split at h
    · next s u' c hs =>
      split_ifs at h with h2
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hsr, hsc, hb⟩ := h2
      obtain ⟨-, -, hp⟩ := ipLin_spec x f.2 a _ hlin
      refine ⟨h1.1, h1.2.1, h1.2.2, s, c, hsr, hsc, fun ν => ?_, ?_⟩
      · rw [hp, ipConst_spec a s hs]; simp [ipDen, imDen]; try ring
      · cases hf : A.find? (fun b => b.id == u') with
        | none => simp [hf] at hb
        | some b =>
          rw [hf] at hb
          simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hb
          obtain ⟨⟨hb2, hbl⟩, hbD⟩ := hb
          refine ⟨b, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, hb2, ?_⟩
          match hba : b.args, hbl with
          | [(q, M)], _ => exact ⟨q, by rw [hba] at hbD; simp at hbD; rw [hbD]⟩
    · simp at h
  · simp at h

theorem elimPinR_ok (V : LV) (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac) (e : AElim)
    (h : elimPinR x D ats ds ps = some e) : AElimOK V x D ats ds ps e := by
  unfold elimPinR at h
  by_cases hx0 : (ids ats).contains x = true
  · rw [if_pos hx0] at h; simp at h
  rw [if_neg hx0] at h
  split at h
  · next p u hfs =>
    by_cases hc : (wfA ats && decide (ids ats).Nodup &&
        wfA (ats.filter (fun a => !atReads x a) ++ ats.filter (atReads x))) = true
    swap
    · rw [if_neg hc] at h; simp at h
    rw [if_pos hc] at h
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hw, hn⟩, hw'⟩ := hc
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hx0
    obtain ⟨sp, hsp, hpu⟩ := firstSome_spec _ _ _ hfs
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hpu
    obtain ⟨u', hu', rfl, rfl⟩ := hpu
    set A := ats.filter (fun a => !atReads x a)
    set B := ats.filter (atReads x)
    obtain ⟨hfD, hDc, hD0, s, c, hs, hsc, hval, b, hbA, hbid, hbf, q, hbq⟩ :=
      pinROf_spec x D A _ u' hu'
    have hds := splits_spec ds sp hsp
    have hp : (A ++ B).Perm ats := by
      have := List.filter_append_perm (fun a => !atReads x a) ats
      simpa [A, B, Bool.not_not] using this
    have hnAB : (ids (A ++ B)).Nodup := by
      simpa [ids] using (hp.map Atom.id).nodup_iff.2 (by simpa [ids] using hn)
    have hwA : wfA A = true := wfA_append A B hw'
    have hnA : (ids A).Nodup := (List.nodup_append.1 (by simpa [ids] using hnAB)).1
    have huA : u' ∈ ids A := hbid ▸ List.mem_map_of_mem hbA
    have huB : u' ∉ ids B := fun h' => by
      have := List.disjoint_of_nodup_append (by simpa [ids] using hnAB)
      exact this huA (by simpa [ids] using h')
    have hxA : x ∉ argVs A ++ ids A := by
      simp only [List.mem_append, not_or]
      constructor
      · simp only [argVs, List.mem_flatMap, not_exists, not_and]
        intro a ha hxa
        simp only [A, List.mem_filter, Bool.not_eq_true'] at ha
        simp [atReads, hxa] at ha
      · intro hxi
        apply hx0
        simp only [ids] at hxi ⊢
        exact (List.filter_sublist.map _).subset hxi
    have hxB : x ∉ ids B := fun hxi => hx0 (by
      simp only [ids] at hxi ⊢; exact (List.filter_sublist.map _).subset hxi)
    have hxu : x ≠ u' := fun e => hxA (List.mem_append_right _ (e ▸ huA))
    intro ν
    have hrw : ∀ j : ℤ, aext V ats (Function.update ν x j) =
        aext V B (Function.update (aext V A ν) x j) := by
      intro j
      rw [aext_perm V ats (A ++ B) hp hw hw' hn, aext_append, aext_upd V A x hxA]
    set E := aext V A ν
    have hden : D.den V.ρ.dv = D.c := DMon.den_isConst _ _ hDc
    have hEu : 0 ≤ E u' ∧ E u' < (D.c : ℤ) := by
      have hfix := aext_fix V A hwA hnA ν b hbA
      rw [hbid] at hfix
      rw [show E u' = _ from hfix]
      simp only [aval, hbf, show (2 : ℕ) < 100 by norm_num, if_true, bfn, hbq, List.map_cons,
        List.map_nil, List.getD_cons_zero, argV, hden]
      exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
    set g : ℤ → ℂ := fun j =>
      bodyOf V.ρ.dv (sp.1 ++ sp.2.2) ps (aext V B (Function.update E x j))
    have hsplit : ∀ j : ℤ, bodyOf V.ρ.dv ds ps (aext V ats (Function.update ν x j)) =
        (if (D.c : ℤ) ∣ j - E u' then g j else 0) := by
      intro j
      rw [hrw j]
      have hF : ∀ y ∉ ids B, aext V B (Function.update E x j) y = Function.update E x j y :=
        fun y hy => aext_off V B _ y hy
      have hd : delV V.ρ.dv (aext V B (Function.update E x j)) sp.2.1 =
          if (D.c : ℤ) ∣ j - E u' then 1 else 0 := by
        unfold delV
        rw [hval, hF x hxB, hF u' huB, Function.update_self, Function.update_of_ne hxu.symm, hfD,
          hden]
        have hiff : (D.c : ℤ) ∣ s * j + c * E u' ↔ (D.c : ℤ) ∣ j - E u' := by
          have hdc : (D.c : ℤ) ∣ s + c := Int.dvd_of_emod_eq_zero hsc
          constructor
          · intro h1
            have h2 : (D.c : ℤ) ∣ s * (s * j + c * E u') - s * ((s + c) * E u') :=
              dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right (Dvd.dvd.mul_right hdc _) _)
            have e2 : s * (s * j + c * E u') - s * ((s + c) * E u') = j - E u' := by
              rcases hs with rfl | rfl <;> ring
            rwa [e2] at h2
          · intro h1
            rw [show s * j + c * E u' = s * (j - E u') + (s + c) * E u' by ring]
            exact dvd_add (dvd_mul_of_dvd_right h1 _) (Dvd.dvd.mul_right hdc _)
        simp only [hiff]
      rw [hds]
      simp only [g, bodyOf, List.map_append, List.map_cons, List.prod_append, List.prod_cons, hd]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun (j : ℕ) _ => hsplit (j : ℤ), hden,
      sum_pin_exact D.c (Nat.pos_of_ne_zero hD0) (E u') g, Int.emod_eq_of_lt hEu.1 hEu.2,
      ofQ_den, Rat.cast_one, one_mul, aext_append]
    have hpl : plainP B (ipV u') = true := by
      simp only [plainP, ipVs, ipV, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.all_cons, List.all_nil, Bool.and_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not]
      exact huB
    have hhs : ipHas x (ipV u') = false := by
      simp [ipHas, ipV, hxu]
    have e1 := aext_sub V B x hxB (ipV u') hpl hhs E
    have hEu' : ipDen E (ipV u') = E u' := by simp [ipDen, ipV, imDen]
    rw [hEu'] at e1
    simp only [g]
    rw [e1, bodyOf_sub]
    have hB'u : aext V (B.map (atSub x (ipV u'))) E u' = E u' :=
      aext_off V _ E u' (by simpa [ids, atSub, List.map_map, Function.comp_def] using huB)
    simp only [ipDen, ipV, imDen, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, List.sum_cons, List.sum_nil, add_zero, one_mul] at hB'u ⊢
    rw [hB'u]
  · simp at h

/-! ## Roots of unity of a smaller order -/

theorem sum_om_pow (d k : ℕ) (hd : 2 ≤ d) (A B : ℤ) :
    ∑ j ∈ range (d ^ k), om d ^ ((j : ℤ) * A + B) =
      om d ^ B * ((d ^ k : ℕ) : ℂ) * (if (((d ^ k : ℕ) : ℤ) ∣ A % d) then 1 else 0) := by
  have hd0 : 0 < d := by omega
  rcases k with _ | m
  · simp
  · have hper : ∀ v y : ℕ, om d ^ (((v + d * y : ℕ) : ℤ) * A + B) = om d ^ ((v : ℤ) * A + B) := by
      intro v y
      apply om_zpow_congr d hd0
      exact ⟨y * A, by push_cast; ring⟩
    rw [pow_succ', sum_range_mul, Finset.sum_congr rfl fun v _ =>
      Finset.sum_congr rfl fun y _ => hper v y]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← Finset.mul_sum, sum_om_lin d hd0]
    have hlt : A % d < ((d * d ^ m : ℕ) : ℤ) := by
      have h1 := Int.emod_lt_of_pos A (by omega : (0 : ℤ) < d)
      have h2 : (d : ℤ) ≤ ((d * d ^ m : ℕ) : ℤ) := by
        push_cast; nlinarith [pow_pos (show (0 : ℤ) < d by omega) m]
      omega
    have h0 : 0 ≤ A % d := Int.emod_nonneg A (by omega)
    have hiff : (((d * d ^ m : ℕ) : ℤ) ∣ A % d) ↔ (d : ℤ) ∣ A := by
      rw [Int.dvd_iff_emod_eq_zero (a := (d : ℤ))]
      constructor
      · intro h; exact Int.eq_zero_of_dvd_of_nonneg_of_lt h0 hlt h
      · intro h; rw [h]; exact dvd_zero _
    by_cases h : (d : ℤ) ∣ A
    · rw [if_pos h, if_pos (hiff.2 h)]; push_cast; ring
    · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]; ring

/-- `x` read only through roots of unity of a constant order `d`, `x` below `D = d^k`, linearly
with a constant coefficient `A`: `Σ_x ω_d^(A x + R) = D [D ∣ A mod d] ω_d^R`. -/
def elimLinC (PW : List (DMon × DMon)) (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac) :
    Option AElim :=
  match ps.filter (facHas x) with
  | [] => none
  | f0 :: _ =>
    match ipLin x (psum (ps.filter (facHas x))) with
    | some (Ap, R) =>
      match ipConst Ap with
      | some A =>
        if (f0.1, D) ∈ PW ∧ f0.1.isConst = true ∧ f0.1.c ≠ 0 ∧
            (ps.filter (facHas x)).all (fun f => f.1 == f0.1) = true ∧
            (argVs ats ++ ids ats).contains x = false ∧ ds.all (fun f => !facHas x f) = true then
          some ⟨CMon.rtD D 2, ats, ds ++ [(D, ipC (A % (f0.1.c : ℤ)))],
            ps.filter (fun f => !facHas x f) ++ [(f0.1, R)]⟩
        else none
      | none => none
    | none => none

theorem elimLinC_ok (V : LV) (hρ : V.ρ.OK) (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ)
    (x : ℕ) (D : DMon) (ats : List Atom) (ds ps : List Fac) (e : AElim)
    (h : elimLinC PW x D ats ds ps = some e) : AElimOK V x D ats ds ps e := by
  unfold elimLinC at h
  split at h
  · simp at h
  · next f0 rest hsel =>
    split at h
    · next Ap R hlin =>
      split at h
      · next A hA =>
        split_ifs at h with hc
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hpw, hcon, hc0, hall, hx, hds⟩ := hc
        obtain ⟨hd2, k, hk⟩ := hPW _ hpw
        obtain ⟨-, hR, hp⟩ := ipLin_spec x _ Ap R hlin
        set d := f0.1
        have hdden : d.den V.ρ.dv = d.c := DMon.den_isConst _ _ hcon
        have hd2' : 2 ≤ d.c := by rw [← hdden]; exact hd2
        have hk' : D.den V.ρ.dv = d.c ^ k := by rw [hk, hdden]
        have hDc : 0 < D.c := by
          have hpos : 0 < D.den V.ρ.dv := by rw [hk']; positivity
          unfold DMon.den at hpos
          exact Nat.pos_of_mul_pos_right hpos
        have hx' : x ∉ argVs ats ++ ids ats := by simpa using hx
        intro ν
        set E := aext V ats ν
        have hall' : ∀ f ∈ ps.filter (facHas x), f.1 = d := by
          simp only [List.all_eq_true, beq_iff_eq] at hall; exact hall
        have hdsx : ∀ f ∈ ds, facHas x f = false := by
          simp only [List.all_eq_true, Bool.not_eq_true'] at hds; exact hds
        have hterm : ∀ j : ℕ, bodyOf V.ρ.dv ds ps (aext V ats (Function.update ν x j)) =
            (ds.map (delV V.ρ.dv E)).prod * ((ps.filter fun f => !facHas x f).map (phV V.ρ.dv E)).prod *
              om d.c ^ ((j : ℤ) * A + ipDen E R) := by
          intro j
          rw [aext_upd V ats x hx' ν]
          unfold bodyOf
          rw [prod_filter_split ps (facHas x) (phV V.ρ.dv _), psum_om V.ρ.dv d (by omega) _ hall',
            hp, ipConst_spec Ap A hA, Function.update_self, ipDen_upd_of _ _ _ _ hR, hdden]
          have e1 : (ds.map (delV V.ρ.dv (Function.update E x j))).prod = (ds.map (delV V.ρ.dv E)).prod :=
            congrArg _ (List.map_congr_left fun f hf => by
              unfold delV; rw [ipDen_upd_of _ _ _ _ (hdsx f hf)])
          have e2 : ((ps.filter fun f => !facHas x f).map (phV V.ρ.dv (Function.update E x j))).prod =
              ((ps.filter fun f => !facHas x f).map (phV V.ρ.dv E)).prod :=
            congrArg _ (List.map_congr_left fun f hf => by
              simp only [List.mem_filter, Bool.not_eq_true'] at hf
              unfold phV; rw [ipDen_upd_of _ _ _ _ hf.2])
          rw [e1, e2, mul_comm (A : ℤ) _]; ring
        rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum, hk', sum_om_pow _ _ hd2',
          rtD_two V.ρ D hDc]
        simp only [bodyOf, List.map_append, List.map_cons, List.map_nil, List.prod_append,
          List.prod_cons, List.prod_nil, mul_one]
        unfold delV phV
        rw [ipDen_C, hk', hdden]
        push_cast
        ring
      · simp at h
    · simp at h

end DiracULA.LSym
