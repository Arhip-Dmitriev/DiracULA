/-
Copyright 2026 Arkhip A. Dmitriev
Licensed under the Apache License, Version 2.0.
-/
import DiracULA.LPass

/-!
# The meaning of .ula programs

A program value is a complex function of the index variables (`Fn`): output register `i` is
variable `i`, input register `i` of an operator is variable `IN + i`, and every other variable
is a parameter, a summation index or an atom. `Prog` is a program's structure over leaf
expressions; `Prog.sem` is its meaning as sums and products over ℂ, `Prog.sym` its translation
into one symbolic sum with atoms, and `Prog.sym_ok` proves the two agree. `certify` proves a
program equal to an expression when the normal form of their difference is empty.
-/

namespace DiracULA.Lang

open DiracULA.Sym DiracULA.LSym Complex Finset

/-- Complex functions of the index variables. -/
abbrev Fn := (ℕ → ℤ) → ℂ

/-- The variable of input register `0`. -/
def IN : ℕ := 1000

/-- `ν` with the variables `b, b + 1, …` set to `js`. -/
def setL (ν : ℕ → ℤ) (b : ℕ) : List ℤ → ℕ → ℤ
  | [] => ν
  | j :: js => setL (Function.update ν b j) (b + 1) js

/-- The sum over every tuple below the levels `L`. -/
noncomputable def sumT : List ℕ → (List ℤ → ℂ) → ℂ
  | [], f => f []
  | N :: L, f => ∑ j ∈ range N, sumT L (fun js => f ((j : ℤ) :: js))

/-- Output and input registers moved up by `k`. -/
def shiftN (k v : ℕ) : ℕ := if v < 2 * IN then v + k else v

/-- A program's structure. -/
inductive Prog where
  /-- An expression: a state, a gate's kernel or a scalar. -/
  | leaf (e : List ATm)
  /-- `a` applied to `b` over registers of levels `L`: `Σ_y a(o, y) b(y, x)`. -/
  | app (L : List DMon) (a b : Prog)
  /-- `a ⊗ b`, `a` on the first `k` registers. -/
  | ten (k : ℕ) (a b : Prog)
  /-- The pointwise product. -/
  | mul (a b : Prog)
  /-- The sum. -/
  | add (a b : Prog)
  /-- The inner product `⟨a|b⟩` over registers of levels `L`. -/
  | inn (L : List DMon) (a b : Prog)
  /-- The complex conjugate. -/
  | cnj (a : Prog)
  /-- `step` applied `cnt` times to `init` over registers of levels `L`, iteration `i` reading
  `J = lo + i`; `inv` is the closed form after the iterations before `J`; `k0`, `k1` are the
  relation cofactors of its two checks. -/
  | loop (L : List DMon) (J : ℕ) (lo : ℤ) (cnt : IPoly) (step init : Prog) (inv : List ATm)
      (k0 k1 : List (ATm × ℕ × ℕ))
  /-- `Σ_{x < D} body`. -/
  | sum (D : DMon) (x : ℕ) (body : Prog)
  /-- `a` with variable `v` read as variable `w` for each pair `(v, w)` of `m`. -/
  | ren (m : List (ℕ × ℕ)) (a : Prog)
  /-- `a` with variable `x` read as the value of `v`. -/
  | sub (x : ℕ) (v : IPoly) (a : Prog)

/-- Variable `v` renamed by the pairs `m`: the first `w` with `(v, w)` in `m`, else `v`. -/
def rmap (m : List (ℕ × ℕ)) (v : ℕ) : ℕ := (m.lookup v).getD v

/-- `k` iterations of `u` from `s`, iteration `i` reading `J = lo + i`. -/
noncomputable def loopSem (dv : ℕ → ℕ) (L : List DMon) (J : ℕ) (lo : ℤ) (u s : Fn) : ℕ → Fn
  | 0 => s
  | i + 1 => fun ν => sumT (L.map (·.den dv)) fun js =>
      u (Function.update (setL ν IN js) J (lo + i)) * loopSem dv L J lo u s i (setL ν 0 js)

/-- The meaning of a program. -/
noncomputable def Prog.sem (V : LV) : Prog → Fn
  | .leaf e => fun ν => axDen V ν e
  | .app L a b => fun ν => sumT (L.map (·.den V.ρ.dv)) fun js =>
      a.sem V (setL ν IN js) * b.sem V (setL ν 0 js)
  | .ten k a b => fun ν => a.sem V ν * b.sem V (ν ∘ shiftN k)
  | .mul a b => fun ν => a.sem V ν * b.sem V ν
  | .add a b => fun ν => a.sem V ν + b.sem V ν
  | .inn L a b => fun ν => sumT (L.map (·.den V.ρ.dv)) fun js =>
      starRingEnd ℂ (a.sem V (setL ν 0 js)) * b.sem V (setL ν 0 js)
  | .cnj a => fun ν => starRingEnd ℂ (a.sem V ν)
  | .loop L J lo cnt step init _ _ _ => fun ν =>
      loopSem V.ρ.dv L J lo (step.sem V) (init.sem V) (ipDen ν cnt).toNat ν
  | .sum D x b => fun ν => ∑ j ∈ range (D.den V.ρ.dv), b.sem V (Function.update ν x j)
  | .ren m a => fun ν => a.sem V (ν ∘ rmap m)
  | .sub x v a => fun ν => a.sem V (Function.update ν x (ipDen ν v))

/-- The iteration counts of a program's loops. -/
def Prog.counts : Prog → List IPoly
  | .leaf _ => []
  | .app _ a b => a.counts ++ b.counts
  | .ten _ a b => a.counts ++ b.counts
  | .mul a b => a.counts ++ b.counts
  | .add a b => a.counts ++ b.counts
  | .inn _ a b => a.counts ++ b.counts
  | .cnj a => a.counts
  | .loop _ _ _ c s i _ _ _ => c :: (s.counts ++ i.counts)
  | .sum _ _ b => b.counts
  | .ren _ a => a.counts
  | .sub _ _ a => a.counts

/-! ## Tuples -/

theorem setL_apply (ν : ℕ → ℤ) (b : ℕ) (js : List ℤ) (v : ℕ) :
    setL ν b js v = if b ≤ v ∧ v < b + js.length then js.getD (v - b) 0 else ν v := by
  induction js generalizing ν b with
  | nil => simp [setL]
  | cons j js ih =>
    simp only [setL, ih, List.length_cons]
    by_cases h1 : v = b
    · subst h1; simp
    · rw [Function.update_of_ne h1]
      by_cases h2 : b + 1 ≤ v ∧ v < b + 1 + js.length
      · have e : v - b = (v - (b + 1)) + 1 := by omega
        rw [ite_eq_left_of_eq_true _ _ (eq_true h2),
          ite_eq_left_of_eq_true _ _ (eq_true (by omega)), e, List.getD_cons_succ]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h2),
          ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem sumT_congr (L : List ℕ) (f g : List ℤ → ℂ)
    (h : ∀ js : List ℤ, js.length = L.length → f js = g js) : sumT L f = sumT L g := by
  induction L generalizing f g with
  | nil => exact h [] rfl
  | cons N L ih =>
    simp only [sumT]
    exact Finset.sum_congr rfl fun j _ =>
      ih _ _ fun js hjs => h _ (by simp [hjs])

/-- The variables `T, T + 1, …` over the levels `L`. -/
def blk (T : ℕ) : List DMon → List (ℕ × DMon)
  | [] => []
  | D :: L => (T, D) :: blk (T + 1) L

theorem sumsV_blk (dv : ℕ → ℕ) (T : ℕ) (L : List DMon) (f : (ℕ → ℤ) → ℂ) (ν : ℕ → ℤ) :
    sumsV dv (blk T L) f ν = sumT (L.map (·.den dv)) fun js => f (setL ν T js) := by
  induction L generalizing T ν with
  | nil => rfl
  | cons D L ih => simp only [blk, sumsV, List.map_cons, sumT, ih, setL]

/-! ## Expressions -/

/-- An expression renamed. -/
def axRen (m : ℕ → ℕ) (e : List ATm) : List ATm := e.map (tRen m)

/-- `m` is injective on every term's variables. -/
def renOKA (m : ℕ → ℕ) (e : List ATm) : Bool := e.all fun t => injOn m (allV t)

theorem axDen_ren (V : LV) (m : ℕ → ℕ) (e : List ATm) (h : renOKA m e = true) (ν : ℕ → ℤ) :
    axDen V ν (axRen m e) = axDen V (ν ∘ m) e := by
  simp only [renOKA, List.all_eq_true] at h
  unfold axDen axRen
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun t ht => tRen_den V m t (h t ht) ν

/-- Every term summed over `S` first. -/
def axSums (S : List (ℕ × DMon)) (e : List ATm) : List ATm :=
  e.map fun t => { t with sums := S ++ t.sums }

theorem axDen_sums (V : LV) (S : List (ℕ × DMon)) (e : List ATm) (ν : ℕ → ℤ) :
    axDen V ν (axSums S e) = sumsV V.ρ.dv S (fun ν' => axDen V ν' e) ν := by
  have h1 : ∀ t : ATm, ATm.den V ν { t with sums := S ++ t.sums } =
      sumsV V.ρ.dv S (fun ν' => t.den V ν') ν := by
    intro t
    unfold ATm.den
    rw [show abody V { t with sums := S ++ t.sums } = abody V t from rfl, sumsV_append,
      ← sumsV_mul_left]
  unfold axDen axSums
  rw [List.map_map]
  simp only [Function.comp_def, h1]
  have := sumsV_lsum V.ρ.dv S (e.map fun t => fun ν' => t.den V ν') ν
  simp only [List.map_map, Function.comp_def] at this
  rw [← this]

/-- The greatest variable an expression names. -/
def maxVar (e : List ATm) : ℕ := (e.flatMap allV).foldr max 0

/-- The first variable of a block free in `a` and `b`. -/
def fresh (a b : List ATm) : ℕ := max (3 * IN) (max (maxVar a) (maxVar b) + 1)

/-- Bound variables renamed `B, B + 1, …` and then the atoms. -/
def bmap (B : ℕ) (bl al : List ℕ) (v : ℕ) : ℕ :=
  if bl.contains v then B + bl.idxOf v
  else if al.contains v then B + bl.length + al.idxOf v else v

/-- A term's bound variables and atoms renamed from `B`, when the renaming is injective. -/
def tApart (B : ℕ) (t : ATm) : ATm :=
  if injOn (bmap B (abvs t) ((ids t.ats).filter fun v => !(abvs t).contains v)) (allV t) &&
      wfA t.ats && (t.aps.flatMap apVs).all (fun v => !(ids t.ats).contains v) then
    tRen (bmap B (abvs t) ((ids t.ats).filter fun v => !(abvs t).contains v)) t
  else t

theorem tApart_ok (V : LV) (B : ℕ) (t : ATm) (ν : ℕ → ℤ) : (tApart B t).den V ν = t.den V ν := by
  unfold tApart
  split_ifs with hc
  · simp only [Bool.and_eq_true] at hc
    rw [tRen_den V _ t hc.1.1]
    refine den_reads_free V t hc.1.2 _ _ fun v hv => ?_
    have hv' : v ∉ ids t.ats ∧ v ∉ abvs t := by
      simp only [freeV, List.mem_append, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
        List.contains_eq_mem, decide_eq_false_iff_not] at hv
      rcases hv with hv | hv
      · exact hv.2
      · refine ⟨fun hi => ?_, hv.2⟩
        have := List.all_eq_true.1 hc.2 v hv.1
        simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at this
        exact this hi
    simp only [Function.comp_apply, bmap, List.contains_eq_mem, List.mem_filter,
      decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    rw [if_neg hv'.2, if_neg (fun h' => hv'.1 h'.1)]
  · rfl

/-- Every term's bound variables and atoms renamed from `B`. -/
def apart (B : ℕ) (e : List ATm) : List ATm := e.map (tApart B)

theorem axDen_apart (V : LV) (B : ℕ) (e : List ATm) (ν : ℕ → ℤ) :
    axDen V ν (apart B e) = axDen V ν e := by
  unfold axDen apart
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun t _ => tApart_ok V B t ν

/-! ## Application -/

/-- Input register `i` renamed `T + i`, for `i < k`. -/
def inMap (T k v : ℕ) : ℕ := if IN ≤ v ∧ v < IN + k then T + (v - IN) else v

/-- Output register `i` renamed `T + i`, for `i < k`. -/
def outMap (T k v : ℕ) : ℕ := if v < k then T + v else v

/-- No variable of `e` in the block `T, …, T + k - 1`. -/
def avoids (T k : ℕ) (e : List ATm) : Bool := (axVs e).all fun v => !(decide (T ≤ v ∧ v < T + k))

/-- `Σ_y a(o, y) b(y, x)` as one expression, the intermediate registers summed over the block
from `fresh a b`. -/
def appSym (L : List DMon) (a b : List ATm) : Option (List ATm) :=
  if decide (L.length < IN) && decide (3 * IN ≤ fresh a b) &&
      avoids (fresh a b) L.length a && avoids (fresh a b) L.length b &&
      renOKA (inMap (fresh a b) L.length) a && renOKA (outMap (fresh a b) L.length) b &&
      axMulOK (axRen (inMap (fresh a b) L.length) a) (axRen (outMap (fresh a b) L.length) b) then
    some (axSums (blk (fresh a b) L)
      (axMul (axRen (inMap (fresh a b) L.length) a) (axRen (outMap (fresh a b) L.length) b)))
  else none

theorem appSym_ok (V : LV) (hρ : V.ρ.OK) (L : List DMon) (a b e : List ATm)
    (h : appSym L a b = some e) (ν : ℕ → ℤ) :
    axDen V ν e = sumT (L.map (·.den V.ρ.dv)) fun js =>
      axDen V (setL ν IN js) a * axDen V (setL ν 0 js) b := by
  unfold appSym at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hk, hT⟩, haA⟩, haB⟩, hrA⟩, hrB⟩, hm⟩ := hc
  generalize fresh a b = T at *
  rw [axDen_sums, sumsV_blk]
  refine sumT_congr _ _ _ fun js hjs => ?_
  simp only [List.length_map] at hjs
  rw [axDen_mul V hρ _ _ hm, axDen_ren V _ _ hrA, axDen_ren V _ _ hrB]
  simp only [avoids, List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at haA haB
  congr 1
  · refine axDen_reads V a _ _ fun v hv => ?_
    have hv' := haA v hv
    simp only [Function.comp_apply, inMap, setL_apply, hjs]
    by_cases hc : IN ≤ v ∧ v < IN + L.length
    · have h1 : T ≤ T + (v - IN) ∧ T + (v - IN) < T + L.length := by omega
      simp only [hc, h1, and_self, ite_true]
      rw [Nat.add_sub_cancel_left]
    · simp only [hc, hv', ite_false]
  · refine axDen_reads V b _ _ fun v hv => ?_
    have hv' := haB v hv
    simp only [Function.comp_apply, outMap, setL_apply, hjs]
    by_cases hc : v < L.length
    · have h1 : T ≤ T + v ∧ T + v < T + L.length := by omega
      have h2 : 0 ≤ v ∧ v < 0 + L.length := by omega
      simp only [hc, h1, h2, and_self, ite_true]
      rw [Nat.add_sub_cancel_left, Nat.sub_zero]
    · have h2 : ¬(0 ≤ v ∧ v < 0 + L.length) := by omega
      simp only [hc, hv', h2, ite_false]

/-! ## Tensor products -/

/-- `a ⊗ b` as one expression, `a` on the first `k` registers. -/
def tenSym (k : ℕ) (a b : List ATm) : Option (List ATm) :=
  if renOKA (shiftN k) b && axMulOK a (axRen (shiftN k) b) then
    some (axMul a (axRen (shiftN k) b)) else none

theorem tenSym_ok (V : LV) (hρ : V.ρ.OK) (k : ℕ) (a b e : List ATm) (h : tenSym k a b = some e)
    (ν : ℕ → ℤ) : axDen V ν e = axDen V ν a * axDen V (ν ∘ shiftN k) b := by
  unfold tenSym at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  simp only [Bool.and_eq_true] at hc
  rw [axDen_mul V hρ _ _ hc.2, axDen_ren V _ _ hc.1]

/-! ## Conjugates -/

/-- Exponents of atoms `2 j` and `2 j + 1` exchanged. -/
def pswap : List ℤ → List ℤ
  | [] => []
  | [a] => [0, a]
  | a :: b :: l => b :: a :: pswap l

def cConj (c : CMon) : CMon :=
  ⟨(CMon.rnorm c.q (-c.r)).1, (CMon.rnorm c.q (-c.r)).2, c.sq, c.rc, pswap c.am, c.gc⟩

theorem conj_zpw_pair (ρ : Val) (hρ : ρ.OK) (l : List ℤ) (j : ℕ) :
    starRingEnd ℂ (zpw ρ.atom (2 * j) l) = zpw ρ.atom (2 * j) (pswap l) := by
  have h1 : ∀ j, starRingEnd ℂ (ρ.atom (2 * j)) = ρ.atom (2 * j + 1) := fun j => (hρ.aconj j).symm
  have h2 : ∀ j, starRingEnd ℂ (ρ.atom (2 * j + 1)) = ρ.atom (2 * j) := fun j => by
    rw [hρ.aconj j, Complex.conj_conj]
  induction l using pswap.induct generalizing j with
  | case1 => simp [zpw, pswap]
  | case2 a => simp [zpw, pswap, map_zpow₀, h1]
  | case3 a b l ih =>
    simp only [zpw, pswap, map_mul, map_zpow₀, h1, h2]
    have := ih (j + 1)
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring] at this
    rw [this]; ring

theorem conj_ex (r : ℝ) : starRingEnd ℂ (ex r) = ex (-r) := by
  simp only [ex, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

theorem conj_zpw (f : ℕ → ℂ) (hf : ∀ i, starRingEnd ℂ (f i) = f i) (k : ℕ) (l : List ℤ) :
    starRingEnd ℂ (zpw f k l) = zpw f k l := by
  induction l generalizing k with
  | nil => simp [zpw]
  | cons a l ih => simp only [zpw, map_mul, map_zpow₀, hf, ih]

theorem conj_cden (ρ : Val) (hρ : ρ.OK) (c : CMon) :
    starRingEnd ℂ (c.den ρ) = (cConj c).den ρ := by
  have hr := rnorm_den c.q (-c.r)
  have hrt : ∀ x : ℕ, starRingEnd ℂ (rt x) = rt x := fun x => Complex.conj_ofReal _
  have e1 : starRingEnd ℂ (c.rc.map rt).prod = (c.rc.map rt).prod := by
    rw [map_list_prod]; simp [List.map_map, Function.comp_def, hrt]
  have e2 : starRingEnd ℂ (c.gc.map (gcdV ρ.dv)).prod = (c.gc.map (gcdV ρ.dv)).prod := by
    rw [map_list_prod, List.map_map]
    exact congrArg _ (List.map_congr_left fun g _ => by simp [gcdV])
  have e3 : starRingEnd ℂ (zpw (rtv ρ.dv) 0 c.sq) = zpw (rtv ρ.dv) 0 c.sq :=
    conj_zpw _ (fun i => hrt _) _ _
  have e4 : starRingEnd ℂ (zpw ρ.atom 0 c.am) = zpw ρ.atom 0 (pswap c.am) := by
    simpa using conj_zpw_pair ρ hρ c.am 0
  simp only [CMon.den, cConj, map_mul, map_ratCast, conj_ex, e1, e2, e3, e4]
  have hr' : ((CMon.rnorm c.q (-c.r)).1 : ℂ) * ex ((CMon.rnorm c.q (-c.r)).2 : ℝ) =
      (c.q : ℂ) * ex (-(c.r : ℝ)) := by rw [hr]; push_cast; rfl
  rw [← hr']

/-- The conjugate coefficient atom's index. -/
def aswap (k : ℕ) : ℕ := if k % 2 = 0 then k + 1 else k - 1

theorem conj_atom (ρ : Val) (hρ : ρ.OK) (k : ℕ) :
    starRingEnd ℂ (ρ.atom k) = ρ.atom (aswap k) := by
  unfold aswap
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [if_pos (by omega), hρ.aconj]
  · rw [if_neg (by omega), show 2 * j + 1 - 1 = 2 * j by omega, hρ.aconj, Complex.conj_conj]

theorem conj_apF (V : LV) (hρ : V.ρ.OK) (k : ℕ) (z : ℤ) :
    starRingEnd ℂ (apF V k z) = apF V (aswap k) z := by
  have hF : FB = 1000000 := rfl
  have hG : GB = 2000000 := rfl
  unfold apF
  by_cases hk : k < FB
  · have hk' : aswap k < FB := by unfold aswap; split_ifs <;> omega
    rw [if_pos hk, if_pos hk', map_zpow₀, conj_atom V.ρ hρ]
  · have hk' : ¬ aswap k < FB := by unfold aswap; split_ifs <;> omega
    rw [if_neg hk, if_neg hk']
    by_cases hg : k < GB
    · have hg' : aswap k < GB := by unfold aswap; split_ifs <;> omega
      rw [if_pos hg, if_pos hg']
      have hq : (aswap k - FB) / 2 = (k - FB) / 2 := by unfold aswap; split_ifs <;> omega
      rw [hq]
      by_cases hp : (k - FB) % 2 = 0
      · have hp' : ¬ (aswap k - FB) % 2 = 0 := by unfold aswap; split_ifs <;> omega
        rw [if_pos hp, if_neg hp']
      · have hp' : (aswap k - FB) % 2 = 0 := by unfold aswap; split_ifs <;> omega
        rw [if_neg hp, if_pos hp', Complex.conj_conj]
    · have hg' : ¬ aswap k < GB := by unfold aswap; split_ifs <;> omega
      rw [if_neg hg, if_neg hg']
      have hq : (aswap k - GB) / 2 = (k - GB) / 2 := by unfold aswap; split_ifs <;> omega
      have hq4 : (aswap k - GB) / 4 = (k - GB) / 4 := by unfold aswap; split_ifs <;> omega
      rw [hq, hq4]
      by_cases hp : (k - GB) % 2 = 0
      · have hp' : ¬ (aswap k - GB) % 2 = 0 := by unfold aswap; split_ifs <;> omega
        rw [if_pos hp, if_neg hp', map_zpow₀]
      · have hp' : (aswap k - GB) % 2 = 0 := by unfold aswap; split_ifs <;> omega
        rw [if_neg hp, if_pos hp', map_zpow₀, Complex.conj_conj]

/-- The conjugate term. -/
def tConj (t : ATm) : ATm :=
  ⟨cConj t.c, t.sums, t.ats, t.dels, t.phs.map fun f => (f.1, ipSmul (-1) f.2),
    t.aps.map fun a => (aswap a.1, a.2)⟩

theorem aps_swap_vs (l : List APw) :
    (l.map fun a => (aswap a.1, a.2)).flatMap apVs = l.flatMap apVs := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.flatMap_cons, ih, apVs]

theorem conj_sumsV (dv : ℕ → ℕ) (s : List (ℕ × DMon)) (f g : (ℕ → ℤ) → ℂ)
    (h : ∀ μ, starRingEnd ℂ (f μ) = g μ) (ν : ℕ → ℤ) :
    starRingEnd ℂ (sumsV dv s f ν) = sumsV dv s g ν := by
  induction s generalizing ν with
  | nil => exact h ν
  | cons p s ih => simp only [sumsV, map_sum, ih]

theorem conj_body (V : LV) (hρ : V.ρ.OK) (t : ATm) (μ : ℕ → ℤ) :
    starRingEnd ℂ (abody V t μ) = abody V (tConj t) μ := by
  unfold abody bodyOf apsV
  simp only [tConj, map_mul, map_list_prod, List.map_map]
  congr 1
  · congr 1
    · congr 1; refine List.map_congr_left fun f _ => ?_
      simp only [Function.comp_apply, delV]; split_ifs <;> simp
    · congr 1; refine List.map_congr_left fun f _ => ?_
      simp only [Function.comp_apply, phV, map_zpow₀, conj_om, ipDen_smul, inv_zpow', neg_one_mul]
  · congr 1; refine List.map_congr_left fun a _ => ?_
    simp only [Function.comp_apply, conj_apF V hρ]

theorem conj_den (V : LV) (hρ : V.ρ.OK) (t : ATm) (ν : ℕ → ℤ) :
    starRingEnd ℂ (t.den V ν) = (tConj t).den V ν := by
  unfold ATm.den
  rw [map_mul, conj_cden V.ρ hρ t.c, conj_sumsV _ _ _ _ (conj_body V hρ t)]
  rfl

theorem axDen_conj (V : LV) (hρ : V.ρ.OK) (e : List ATm) (ν : ℕ → ℤ) :
    starRingEnd ℂ (axDen V ν e) = axDen V ν (e.map tConj) := by
  unfold axDen
  rw [map_list_sum, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun t _ => conj_den V hρ t ν

/-! ## Inner products -/

/-- Output register `i` renamed input register `i`, for `i < k`. -/
def toIn (k v : ℕ) : ℕ := if v < k then IN + v else v

/-- `⟨a|b⟩` as one expression: the conjugate of `a` read on input registers, applied to `b`. -/
def innSym (L : List DMon) (a b : List ATm) : Option (List ATm) :=
  if renOKA (toIn L.length) (a.map tConj) && avoids IN L.length a then
    appSym L (axRen (toIn L.length) (a.map tConj)) b
  else none

theorem innSym_ok (V : LV) (hρ : V.ρ.OK) (L : List DMon) (a b e : List ATm)
    (h : innSym L a b = some e) (ν : ℕ → ℤ) :
    axDen V ν e = sumT (L.map (·.den V.ρ.dv)) fun js =>
      starRingEnd ℂ (axDen V (setL ν 0 js) a) * axDen V (setL ν 0 js) b := by
  unfold innSym at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hc2, hc3⟩ := hc
  rw [appSym_ok V hρ L _ b e h]
  refine sumT_congr _ _ _ fun js hjs => ?_
  simp only [List.length_map] at hjs
  rw [axDen_ren V _ _ hc2, axDen_conj V hρ a]
  congr 1
  have hv : ∀ v ∈ axVs (a.map tConj), (setL ν IN js ∘ toIn L.length) v = setL ν 0 js v := by
    intro v hv
    have hva : v ∈ axVs a := by
      simp only [axVs, List.mem_flatMap, List.mem_map] at hv ⊢
      obtain ⟨_, ⟨t, ht, rfl⟩, hv⟩ := hv
      exact ⟨t, ht, by simpa [rvs, fvs, tConj, facVars, ipSmul, ipVs, aps_swap_vs] using hv⟩
    simp only [avoids, List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hc3
    have := hc3 v hva
    simp only [Function.comp_apply, toIn, setL_apply, hjs]
    by_cases hc : v < L.length
    · have h1 : IN ≤ IN + v ∧ IN + v < IN + L.length := by omega
      have h2 : 0 ≤ v ∧ v < 0 + L.length := by omega
      simp only [hc, h1, h2, and_self, ite_true]
      rw [Nat.add_sub_cancel_left, Nat.sub_zero]
    · have h2 : ¬(0 ≤ v ∧ v < 0 + L.length) := by omega
      simp only [hc, this, h2, ite_false]
  exact axDen_reads V _ _ _ hv

/-! ## Substituting a free variable -/

theorem aext_sub' (V : LV) (l : List Atom) (x : ℕ) (hx : x ∉ ids l) (v : IPoly)
    (hv : plainP l v = true) (μ : ℕ → ℤ) :
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

/-- `x` substituted by `v` in a power without atoms of its own. -/
def apSubT (x : ℕ) (v : IPoly) (a : APw) : APw :=
  if a.2.2 = [] then (a.1, ipSubst x v a.2.1, []) else a

/-- Whether a power is `1`: no atoms of its own, a zero exponent and an index of `apMerge`. -/
def apOne (a : APw) : Bool := a.2.2.isEmpty && a.2.1.isEmpty && apMerge a.1

/-- The variables the powers with atoms of their own read. -/
def tabVs (l : List APw) : List ℕ := (l.filter fun a => !a.2.2.isEmpty).flatMap apVs

theorem apsV_drop (V : LV) (l : List APw) (μ : ℕ → ℤ) :
    apsV V (l.filter fun a => !apOne a) μ = apsV V l μ := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filter_cons]
    split_ifs with h
    · simp only [apsV, List.map_cons, List.prod_cons] at ih ⊢
      rw [ih]
    · simp only [apOne, Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true,
        List.isEmpty_iff] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      simp only [apsV, List.map_cons, List.prod_cons] at ih ⊢
      rw [ih, h1, h2]
      simp only [aext, ipDen, List.map_nil, List.sum_nil, apF_zero V a.1 h3, one_mul]

theorem apsV_sub (V : LV) (x : ℕ) (v : IPoly) (l : List APw) (h : x ∉ tabVs l) (μ : ℕ → ℤ) :
    apsV V (l.map (apSubT x v)) μ = apsV V l (Function.update μ x (ipDen μ v)) := by
  unfold apsV
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun a ha => ?_
  simp only [Function.comp_apply]
  by_cases he : a.2.2 = []
  · have e : apSubT x v a = (a.1, ipSubst x v a.2.1, []) := if_pos he
    rw [e, he]
    show apF V a.1 (ipDen μ (ipSubst x v a.2.1)) =
      apF V a.1 (ipDen (Function.update μ x (ipDen μ v)) a.2.1)
    rw [ipDen_subst]
  · have e : apSubT x v a = a := if_neg he
    rw [e]
    have hx : x ∉ apVs a := fun hx => h (List.mem_flatMap.2
      ⟨a, List.mem_filter.2 ⟨ha, by simpa [List.isEmpty_iff] using he⟩, hx⟩)
    have := apsV_reads V [a] μ (Function.update μ x (ipDen μ v)) (fun y hy => by
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hy
      have : y ≠ x := fun e => hx (e ▸ hy)
      rw [Function.update_of_ne this])
    simpa [apsV] using this

/-- `x` substituted by `v` in a term's factors, atom arguments and powers. -/
def tSub (x : ℕ) (v : IPoly) (t : ATm) : ATm :=
  ⟨t.c, t.sums, t.ats.map (atSub x v), t.dels.map (facSub x v), t.phs.map (facSub x v),
    (t.aps.map (apSubT x v)).filter fun a => !apOne a⟩

/-- `x` is free in `t` and `v` reads no bound variable or atom of `t`. -/
def subOK (x : ℕ) (v : IPoly) (t : ATm) : Bool :=
  !(abvs t).contains x && !(ids t.ats).contains x && plainP t.ats v &&
    (ipVs v).all (fun y => !(abvs t).contains y) && !(tabVs t.aps).contains x

theorem tSub_den (V : LV) (x : ℕ) (v : IPoly) (t : ATm) (h : subOK x v t = true) (ν : ℕ → ℤ) :
    (tSub x v t).den V ν = t.den V (Function.update ν x (ipDen ν v)) := by
  simp only [subOK, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hb, hi⟩, hp⟩, hvb⟩, hxa⟩ := h
  have hbody : ∀ μ, abody V (tSub x v t) μ = abody V t (Function.update μ x (ipDen μ v)) := by
    intro μ
    unfold abody
    simp only [tSub]
    rw [aext_sub' V t.ats x hi v hp μ, bodyOf_sub, ipDen_aext V _ v (by
      simpa [plainP, ids, atSub] using hp), apsV_drop, apsV_sub V x v t.aps hxa]
  unfold ATm.den
  show t.c.den V.ρ * sumsV V.ρ.dv t.sums (abody V (tSub x v t)) ν = _
  congr 1
  rw [sumsV_congr _ _ _ _ hbody]
  have key : ∀ (s : List (ℕ × DMon)), (∀ p ∈ s, p.1 ∈ abvs t) → ∀ μ : ℕ → ℤ,
      sumsV V.ρ.dv s (fun μ => abody V t (Function.update μ x (ipDen μ v))) μ =
        sumsV V.ρ.dv s (abody V t) (Function.update μ x (ipDen μ v)) := by
    intro s
    induction s with
    | nil => intro _ μ; rfl
    | cons p s ih =>
      intro hs μ
      simp only [sumsV]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hp := hs p List.mem_cons_self
      have hpx : p.1 ≠ x := fun e => hb (e ▸ hp)
      rw [ih (fun q hq => hs q (List.mem_cons_of_mem _ hq)),
        ipDen_upd_of _ _ _ _ (ipHas_false_of _ _ fun hy => hvb _ hy hp),
        Function.update_comm hpx]
  exact key t.sums (fun p hp => List.mem_map_of_mem hp) ν

theorem axDen_tSub (V : LV) (x : ℕ) (v : IPoly) (e : List ATm) (h : e.all (subOK x v) = true)
    (ν : ℕ → ℤ) : axDen V ν (e.map (tSub x v)) = axDen V (Function.update ν x (ipDen ν v)) e := by
  simp only [List.all_eq_true] at h
  unfold axDen
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun t ht => tSub_den V x v t (h t ht) ν

/-- The invariant after one more iteration with its atoms at `J + 1` rewritten, for `0 ≤ lo`. -/
def jPass (lo : ℤ) (J : ℕ) (e : List ATm) : List ATm := if 0 ≤ lo then xpass ⟨[J], [], []⟩ e else e

theorem axDen_jPass (V : LV) (hρ : V.ρ.OK) (lo : ℤ) (J : ℕ) (e : List ATm) (ν : ℕ → ℤ)
    (h : lo ≤ ν J) : axDen V ν (jPass lo J e) = axDen V ν e := by
  unfold jPass
  split_ifs with h0
  · refine axDen_xpass V hρ _ e ν ⟨fun j hj => ?_, fun w hw => by simp at hw, fun w hw => by simp at hw⟩
    simp only [List.mem_singleton] at hj
    subst hj; omega
  · rfl

/-! ## Relations of the built-in values -/

theorem apsV_foldr (V : LV) (hρ : V.ρ.OK) (es : List (ℕ × ℤ)) (h : es.all (fun e => apMerge e.1))
    (l : List APw) (μ : ℕ → ℤ) :
    apsV V (es.foldr (fun e acc => apIns (e.1, ipC e.2) acc) l) μ =
      (es.map fun e => apF V e.1 e.2).prod * apsV V l μ := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [apsV_apIns V hρ (e.1, ipC e.2) h.1, ih h.2, ipDen_C]; ring

/-- `√(dv i)` as a coefficient. -/
def cmRt (q : ℚ) (i : ℕ) : CMon := ⟨q, 0, List.replicate i 0 ++ [1], [], [], []⟩

theorem cmRt_den (ρ : Val) (q : ℚ) (i : ℕ) : (cmRt q i).den ρ = q * rt (ρ.dv i) := by
  simp only [cmRt, CMon.den]
  suffices h : ∀ k, zpw (rtv ρ.dv) k (List.replicate i 0 ++ [1]) = rtv ρ.dv (k + i) by
    simp [h, zpw, ex_zero, rtv]
  intro k
  induction i generalizing k with
  | zero => simp [zpw]
  | succ j ih => simp [zpw, List.replicate_succ, ih, Nat.add_assoc, Nat.add_comm 1 j]

theorem ex_quarter : ex (1 / 4) = Complex.I := by
  simp only [ex]
  have : 2 * (Real.pi : ℂ) * Complex.I * ((1 / 4 : ℝ) : ℂ) = (Real.pi / 2 : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_pi_div_two_mul_I]

/-- Relation `r` of dimension `i`: `0` is `√N u - √N u⁻¹ - 2 i = 0`, `1` is `q u + q u⁻¹ - 1 = 0`,
for `u = u_N`, `q = q_N` and `N = dv i`; each monomial a coefficient and constant powers. -/
def relM (r i : ℕ) : List (CMon × List (ℕ × ℤ)) :=
  if r = 0 then
    [(cmRt 1 i, [(GB + 4 * i, 1)]), (cmRt (-1) i, [(GB + 4 * i, -1)]),
      (⟨-2, 1 / 4, [], [], [], []⟩, [])]
  else
    [(CMon.ofQ 1, [(GB + 4 * i + 2, 1), (GB + 4 * i, 1)]),
      (CMon.ofQ 1, [(GB + 4 * i + 2, 1), (GB + 4 * i, -1)]), (CMon.ofQ (-1), [])]

theorem apF_g (V : LV) (i f : ℕ) (hf : f < 2) (z : ℤ) :
    apF V (GB + 4 * i + 2 * f) z = gfn f (V.ρ.dv i) ^ z := by
  have hF : FB = 1000000 := rfl
  have hG : GB = 2000000 := rfl
  unfold apF
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show (GB + 4 * i + 2 * f - GB) / 2 % 2 = f by omega,
    show (GB + 4 * i + 2 * f - GB) / 4 = i by omega]

theorem relM_zero (V : LV) (r i : ℕ) (hr : r ≤ 1) (hN : 2 ≤ V.ρ.dv i) :
    ((relM r i).map fun m => m.1.den V.ρ * (m.2.map fun e => apF V e.1 e.2).prod).sum = 0 := by
  have g0 := apF_g V i 0 (by norm_num)
  have g1 := apF_g V i 1 (by norm_num)
  simp only [mul_zero, add_zero, mul_one] at g0 g1
  unfold relM
  split_ifs with h0
  · have hc : (⟨-2, 1 / 4, [], [], [], []⟩ : CMon).den V.ρ = -2 * ex (1 / 4) := by
      simp [CMon.den, zpw]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.sum_cons,
      List.sum_nil, cmRt_den, g0, zpow_one, zpow_neg, hc, mul_one]
    have := gfn_rel1 (V.ρ.dv i) hN
    rw [ex_quarter]
    simp only [rt] at this ⊢
    push_cast
    linear_combination this
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.sum_cons,
      List.sum_nil, ofQ_den, g0, g1, zpow_one, zpow_neg, mul_one]
    have := gfn_rel2 (V.ρ.dv i) hN
    push_cast
    linear_combination this

/-- The terms `p · relation r of dimension i` of each cofactor `(p, r, i)`. -/
def relX (ks : List (ATm × ℕ × ℕ)) : List ATm :=
  ks.flatMap fun k => (relM k.2.1 k.2.2).map fun m =>
    ⟨k.1.c.mul m.1, k.1.sums, k.1.ats, k.1.dels, k.1.phs,
      m.2.foldr (fun e acc => apIns (e.1, ipC e.2) acc) k.1.aps⟩

/-- Every cofactor names a relation of a dimension at least `2`. -/
def relOK (fl : List ℕ) (ks : List (ATm × ℕ × ℕ)) : Bool :=
  ks.all fun k => decide (2 ≤ flv fl k.2.2) && decide (k.2.1 ≤ 1)

theorem relM_merge (r i : ℕ) : ∀ m ∈ relM r i, m.2.all (fun e => apMerge e.1) = true := by
  have hG : GB = 2000000 := rfl
  intro m hm
  unfold relM at hm
  split_ifs at hm <;>
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp [apMerge] <;> omega

theorem axDen_relX (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (ks : List (ATm × ℕ × ℕ)) (h : relOK fl ks = true) (ν : ℕ → ℤ) : axDen V ν (relX ks) = 0 := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [relOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hN, hr⟩, hks⟩ := h
    have ih' := ih (by simpa [relOK] using hks)
    simp only [relX, List.flatMap_cons] at ih' ⊢
    rw [axDen_append, ih', add_zero]
    unfold axDen
    have hN' : 2 ≤ V.ρ.dv k.2.2 := le_trans hN (hfl k.2.2)
    have hterm : ∀ m ∈ relM k.2.1 k.2.2, ATm.den V ν ⟨k.1.c.mul m.1, k.1.sums, k.1.ats, k.1.dels,
        k.1.phs, m.2.foldr (fun e acc => apIns (e.1, ipC e.2) acc) k.1.aps⟩ =
        (m.1.den V.ρ * (m.2.map fun e => apF V e.1 e.2).prod) * k.1.den V ν := by
      intro m hm
      unfold ATm.den abody
      simp only
      rw [CMon.den_mul V.ρ hρ]
      have hs : ∀ μ, bodyOf V.ρ.dv k.1.dels k.1.phs (aext V k.1.ats μ) *
          apsV V (m.2.foldr (fun e acc => apIns (e.1, ipC e.2) acc) k.1.aps) μ =
          (m.2.map fun e => apF V e.1 e.2).prod *
            (bodyOf V.ρ.dv k.1.dels k.1.phs (aext V k.1.ats μ) * apsV V k.1.aps μ) := by
        intro μ
        rw [apsV_foldr V hρ m.2 (relM_merge _ _ m hm)]; ring
      rw [sumsV_congr _ _ _ _ hs, sumsV_mul_left]
      ring
    rw [List.map_map]
    rw [List.map_congr_left (fun m hm => by simpa using hterm m hm)]
    rw [List.sum_map_mul_right, relM_zero V k.2.1 k.2.2 hr hN', zero_mul]

/-- The checks of a loop: the invariant at `J = lo` is the initial state and one step takes
the invariant at `J` to the invariant at `J + 1`, each up to the relations of the cofactors. -/
def loopChk (fl : List ℕ) (PW : List (DMon × DMon)) (L : List DMon) (J : ℕ) (lo : ℤ)
    (s i0 inv : List ATm) (k0 k1 : List (ATm × ℕ × ℕ)) : Bool :=
  decide (2 * IN ≤ J) && inv.all (subOK J (ipC lo)) &&
    inv.all (subOK J (ipAdd (ipV J) (ipC 1))) && relOK fl k0 && relOK fl k1 &&
    close2 fl PW ⟨[], [], []⟩ (i0 ++ axNeg (inv.map (tSub J (ipC lo))) ++ relX k0) &&
    (match appSym L (apart (fresh s inv) s) inv with
     | some e1 =>
       close2 fl PW ⟨[], [], []⟩
         (e1 ++ axNeg (jPass lo J (inv.map (tSub J (ipAdd (ipV J) (ipC 1))))) ++ relX k1)
     | none => false)

theorem setL_update (ν : ℕ → ℤ) (b : ℕ) (js : List ℤ) (J : ℕ) (hJ : b + js.length ≤ J)
    (v : ℤ) : setL (Function.update ν J v) b js = Function.update (setL ν b js) J v := by
  funext y
  rw [setL_apply]
  by_cases hy : y = J
  · subst hy; simp only [Function.update_self]; rw [if_neg (by omega)]
  · rw [Function.update_of_ne hy, Function.update_of_ne hy, setL_apply]

theorem loop_inv (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (L : List DMon) (J : ℕ) (lo : ℤ)
    (s i0 inv : List ATm) (k0 k1 : List (ATm × ℕ × ℕ)) (u w : Fn) (hu : ∀ μ, u μ = axDen V μ s)
    (hw : ∀ μ, w μ = axDen V μ i0) (hL : L.length < IN)
    (h : loopChk fl PW L J lo s i0 inv k0 k1 = true) (k : ℕ) (ν : ℕ → ℤ) :
    loopSem V.ρ.dv L J lo u w k ν = axDen V (Function.update ν J (lo + k)) inv := by
  unfold loopChk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hJ, hs0⟩, hs1⟩, hr0⟩, hr1⟩, h0⟩, h1⟩ := h
  have hC0 : ∀ μ, CtxOK V ⟨[], [], []⟩ μ := fun μ =>
    ⟨fun j hj => by simp at hj, fun w hw => by simp at hw, fun w hw => by simp at hw⟩
  induction k generalizing ν with
  | zero =>
    have hz := close2_ok V hρ fl hfl PW hPW _ _ h0 ν (hC0 ν)
    rw [axDen_append, axDen_append, axDen_neg, axDen_tSub V J _ inv hs0,
      axDen_relX V hρ fl hfl k0 hr0, add_zero] at hz
    simp only [loopSem, hw, Nat.cast_zero, add_zero]
    rw [show (lo : ℤ) = ipDen ν (ipC lo) from (ipDen_C ν lo).symm]
    linear_combination hz
  | succ k ih =>
    split at h1
    · next e1 he1 =>
      set μ := Function.update ν J (lo + k)
      have hz := close2_ok V hρ fl hfl PW hPW _ _ h1 μ (hC0 μ)
      rw [axDen_append, axDen_append, axDen_neg, axDen_jPass V hρ lo J _ μ (by simp [μ]),
        axDen_tSub V J _ inv hs1, appSym_ok V hρ L _ inv e1 he1, axDen_relX V hρ fl hfl k1 hr1,
        add_zero] at hz
      have e2 : ipDen μ (ipAdd (ipV J) (ipC 1)) = lo + (k + 1 : ℕ) := by
        simp only [ipDen_add, ipDen_V, ipDen_C, μ, Function.update_self]; push_cast; ring
      rw [e2, Function.update_idem] at hz
      simp only [loopSem]
      rw [← sub_eq_zero.1 hz]
      refine sumT_congr _ _ _ fun js hjs => ?_
      simp only [List.length_map] at hjs
      rw [hu, axDen_apart, ih (setL ν 0 js),
        ← setL_update ν IN js J (by simp only [IN] at hL hJ ⊢; omega),
        ← setL_update ν 0 js J (by simp only [IN] at hL hJ ⊢; omega)]
    · simp at h1

/-! ## Programs -/

/-- A program as one expression. -/
def Prog.sym (fl : List ℕ) (PW : List (DMon × DMon)) : Prog → Option (List ATm)
  | .leaf e => some e
  | .app L a b =>
    match a.sym fl PW, b.sym fl PW with
    | some x, some y => appSym L (apart (fresh x y) x) y
    | _, _ => none
  | .ten k a b =>
    match a.sym fl PW, b.sym fl PW with
    | some x, some y => tenSym k x (apart (fresh x y) y)
    | _, _ => none
  | .mul a b =>
    match a.sym fl PW, b.sym fl PW with
    | some x, some y =>
      if axMulOK x (apart (fresh x y) y) then some (axMul x (apart (fresh x y) y)) else none
    | _, _ => none
  | .add a b =>
    match a.sym fl PW, b.sym fl PW with
    | some x, some y => some (x ++ y)
    | _, _ => none
  | .inn L a b =>
    match a.sym fl PW, b.sym fl PW with
    | some x, some y => innSym L (apart (fresh x y) x) y
    | _, _ => none
  | .cnj a =>
    match a.sym fl PW with
    | some x => some (x.map tConj)
    | none => none
  | .loop L J lo cnt step init inv k0 k1 =>
    match step.sym fl PW, init.sym fl PW with
    | some x, some y =>
      if step.counts = [] ∧ init.counts = [] ∧ L.length < IN ∧
          (ipVs cnt).all (fun v => decide (2 * IN ≤ v)) = true ∧
          inv.all (subOK J (ipAdd (ipC lo) cnt)) = true ∧
          loopChk fl PW L J lo x y inv k0 k1 = true then
        some (inv.map (tSub J (ipAdd (ipC lo) cnt)))
      else none
    | _, _ => none
  | .sum D x b =>
    match b.sym fl PW with
    | some e => if b.counts = [] then some (axSums [(x, D)] e) else none
    | none => none
  | .ren m a =>
    match a.sym fl PW with
    | some e => if a.counts = [] ∧ renOKA (rmap m) e = true then some (axRen (rmap m) e) else none
    | none => none
  | .sub x v a =>
    match a.sym fl PW with
    | some e => if a.counts = [] ∧ e.all (subOK x v) = true then some (e.map (tSub x v)) else none
    | none => none

/-- Every loop count of `p` is nonnegative at each valuation agreeing with `ν` from `2 IN` on. -/
def HiOK (p : Prog) (ν : ℕ → ℤ) : Prop :=
  ∀ c ∈ p.counts, ∀ μ : ℕ → ℤ, (∀ v, 2 * IN ≤ v → μ v = ν v) → 0 ≤ ipDen μ c

theorem HiOK.sub {p q : Prog} {ν : ℕ → ℤ} (h : HiOK p ν) (hsub : ∀ c ∈ q.counts, c ∈ p.counts)
    (μ0 : ℕ → ℤ) (hμ0 : ∀ v, 2 * IN ≤ v → μ0 v = ν v) : HiOK q μ0 :=
  fun c hc μ hμ => h c (hsub c hc) μ fun v hv => (hμ v hv).trans (hμ0 v hv)

theorem setL_hi (ν : ℕ → ℤ) (b : ℕ) (js : List ℤ) (hb : b + js.length ≤ 2 * IN) :
    ∀ v, 2 * IN ≤ v → setL ν b js v = ν v := by
  intro v hv; rw [setL_apply, if_neg (by omega)]

theorem shift_hi (ν : ℕ → ℤ) (k : ℕ) : ∀ v, 2 * IN ≤ v → (ν ∘ shiftN k) v = ν v := by
  intro v hv; simp [shiftN, show ¬ v < 2 * IN by omega]

theorem Prog.sym_ok (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (p : Prog) (e : List ATm)
    (h : p.sym fl PW = some e) (ν : ℕ → ℤ) (hc : HiOK p ν) : p.sem V ν = axDen V ν e := by
  induction p generalizing e ν with
  | leaf e' => simp only [Prog.sym, Option.some.injEq] at h; subst h; rfl
  | app L a b iha ihb =>
    simp only [Prog.sym] at h
    split at h
    · next x y hx hy =>
      have hL : L.length < IN := by
        unfold appSym at h; split_ifs at h with hcc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcc; exact hcc.1.1.1.1.1.1
      rw [appSym_ok V hρ L _ y e h]
      simp only [Prog.sem]
      refine sumT_congr _ _ _ fun js hjs => ?_
      simp only [List.length_map] at hjs
      rw [axDen_apart, iha x hx _ (hc.sub (fun c h' => by simp [Prog.counts, h']) _
        (setL_hi ν IN js (by simp only [IN] at hL ⊢; omega))),
        ihb y hy _ (hc.sub (fun c h' => by simp [Prog.counts, h']) _
        (setL_hi ν 0 js (by simp only [IN] at hL ⊢; omega)))]
    · simp at h
  | ten k a b iha ihb =>
    simp only [Prog.sym] at h
    split at h
    · next x y hx hy =>
      rw [tenSym_ok V hρ k x _ e h]
      simp only [Prog.sem]
      rw [axDen_apart, iha x hx _ (hc.sub (fun c h' => by simp [Prog.counts, h']) _
        fun _ _ => rfl), ihb y hy _ (hc.sub (fun c h' => by simp [Prog.counts, h']) _
        (shift_hi ν k))]
    · simp at h
  | mul a b iha ihb =>
    simp only [Prog.sym] at h
    split at h
    · next x y hx hy =>
      split_ifs at h with hm
      simp only [Option.some.injEq] at h
      subst h
      simp only [Prog.sem]
      rw [axDen_mul V hρ _ _ hm, axDen_apart,
        iha x hx _ (hc.sub (fun c h' => by simp [Prog.counts, h']) _ fun _ _ => rfl),
        ihb y hy _ (hc.sub (fun c h' => by simp [Prog.counts, h']) _ fun _ _ => rfl)]
    · simp at h
  | add a b iha ihb =>
    simp only [Prog.sym] at h
    split at h
    · next x y hx hy =>
      simp only [Option.some.injEq] at h
      subst h
      simp only [Prog.sem]
      rw [axDen_append, iha x hx _ (hc.sub (fun c h' => by simp [Prog.counts, h']) _
        fun _ _ => rfl), ihb y hy _ (hc.sub (fun c h' => by simp [Prog.counts, h']) _
        fun _ _ => rfl)]
    · simp at h
  | inn L a b iha ihb =>
    simp only [Prog.sym] at h
    split at h
    · next x y hx hy =>
      have hL : L.length < IN := by
        unfold innSym at h; split_ifs at h
        unfold appSym at h; split_ifs at h with hcc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcc; exact hcc.1.1.1.1.1.1
      rw [innSym_ok V hρ L _ y e h]
      simp only [Prog.sem]
      refine sumT_congr _ _ _ fun js hjs => ?_
      simp only [List.length_map] at hjs
      rw [axDen_apart, iha x hx _ (hc.sub (fun c h' => by simp [Prog.counts, h']) _
        (setL_hi ν 0 js (by simp only [IN] at hL ⊢; omega))),
        ihb y hy _ (hc.sub (fun c h' => by simp [Prog.counts, h']) _
        (setL_hi ν 0 js (by simp only [IN] at hL ⊢; omega)))]
    · simp at h
  | cnj a iha =>
    simp only [Prog.sym] at h
    split at h
    · next x hx =>
      simp only [Option.some.injEq] at h
      subst h
      simp only [Prog.sem]
      rw [iha x hx _ (hc.sub (fun c h' => by simp [Prog.counts, h']) _ fun _ _ => rfl),
        axDen_conj V hρ x]
    · simp at h
  | loop L J lo cnt step init inv k0 k1 ihs ihi =>
    simp only [Prog.sym] at h
    split at h
    · next x y hx hy =>
      split_ifs at h with hcc
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hsc, hic, hL, hcv, hsub, hchk⟩ := hcc
      have hu : ∀ μ, step.sem V μ = axDen V μ x := fun μ =>
        ihs x hx μ fun c h' => by simp [hsc] at h'
      have hw : ∀ μ, init.sem V μ = axDen V μ y := fun μ =>
        ihi y hy μ fun c h' => by simp [hic] at h'
      have h0 : 0 ≤ ipDen ν cnt := hc cnt (by simp [Prog.counts]) ν fun _ _ => rfl
      simp only [Prog.sem]
      rw [loop_inv V hρ fl hfl PW hPW L J lo x y inv k0 k1 _ _ hu hw hL hchk,
        axDen_tSub V J _ inv hsub,
        ipDen_add, ipDen_C, Int.toNat_of_nonneg h0]
    · simp at h
  | sum D x b ih =>
    simp only [Prog.sym] at h
    split at h
    · next e' he =>
      split_ifs at h with hcb
      simp only [Option.some.injEq] at h
      subst h
      simp only [Prog.sem]
      rw [axDen_sums]
      simp only [sumsV]
      exact Finset.sum_congr rfl fun j _ => ih e' he _ fun c h' => by simp [hcb] at h'
    · simp at h
  | ren m a ih =>
    simp only [Prog.sym] at h
    split at h
    · next e' he =>
      split_ifs at h with hcb
      simp only [Option.some.injEq] at h
      subst h
      simp only [Prog.sem]
      rw [axDen_ren V _ _ hcb.2]
      exact ih e' he _ fun c h' => by simp [hcb.1] at h'
    · simp at h
  | sub x v a ih =>
    simp only [Prog.sym] at h
    split at h
    · next e' he =>
      split_ifs at h with hcb
      simp only [Option.some.injEq] at h
      subst h
      simp only [Prog.sem]
      rw [axDen_tSub V x v e' hcb.2]
      exact ih e' he _ fun c h' => by simp [hcb.1] at h'
    · simp at h

/-! ## Certificates -/

theorem pow_floor (a b n : ℕ) (h : a = b ^ n) (hb : 2 ≤ b) (hn : 1 ≤ n) : 2 ≤ a := by
  subst h
  calc 2 ≤ b := hb
    _ = b ^ 1 := (pow_one b).symm
    _ ≤ b ^ n := Nat.pow_le_pow_right (by omega) hn

end DiracULA.Lang

namespace DiracULA.Lang

open DiracULA.Sym DiracULA.LSym

theorem nfA_of_lit (fl : List ℕ) (PW : List (DMon × DMon)) (e : List ATm) (ns : List (Option ATm))
    (hn : e.map (normA fl PW AROUNDS) = ns) :
    nfA fl PW e = (ns.filterMap id).foldl (fun acc t => taAdd t acc) [] := by
  unfold nfA
  rw [← hn, List.filterMap_map]
  rfl

theorem hi_of (p : Prog) (hv : ∀ c ∈ p.counts, ∀ v ∈ ipVs c, 2 * IN ≤ v) (ν : ℕ → ℤ)
    (h : ∀ c ∈ p.counts, 0 ≤ ipDen ν c) : HiOK p ν := by
  intro c hc μ hμ
  rw [ipDen_reads c μ ν fun v hv' => hμ v (hv c hc v hv')]
  exact h c hc

/-- `p` equals `r` at every valuation where its loop counts are nonnegative, given the
translation and every term's normal form. -/
theorem certify_lit_c (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (p : Prog) (r e : List ATm)
    (ns : List (Option ATm)) (he : p.sym fl PW = some e)
    (hn : (e ++ axNeg r).map (normA fl PW AROUNDS) = ns)
    (hz : (ns.filterMap id).foldl (fun acc t => taAdd t acc) [] = [])
    (hv : ∀ c ∈ p.counts, ∀ v ∈ ipVs c, 2 * IN ≤ v) :
    ∀ ν, (∀ c ∈ p.counts, 0 ≤ ipDen ν c) → p.sem V ν = axDen V ν r := by
  intro ν hc
  have hz' := nfA_zero V hρ fl hfl PW hPW _ (by rw [nfA_of_lit fl PW _ ns hn, hz]) ν
  rw [axDen_append, axDen_neg] at hz'
  rw [Prog.sym_ok V hρ fl hfl PW hPW p e he ν (hi_of p hv ν hc)]
  linear_combination hz'

/-- `certify_lit_c` with the program's expression rewritten under the context `C`, at every
valuation where it holds. -/
theorem certify_w_c (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (C : Ctx) (p : Prog)
    (r e : List ATm) (ns : List (Option ATm)) (he : p.sym fl PW = some e)
    (hn : (xpass C e ++ axNeg r).map (normA fl PW AROUNDS) = ns)
    (hz : (ns.filterMap id).foldl (fun acc t => taAdd t acc) [] = [])
    (hv : ∀ c ∈ p.counts, ∀ v ∈ ipVs c, 2 * IN ≤ v) :
    ∀ ν, CtxOK V C ν → (∀ c ∈ p.counts, 0 ≤ ipDen ν c) → p.sem V ν = axDen V ν r := by
  intro ν hW hc
  have hz' := nfA_zero V hρ fl hfl PW hPW _ (by rw [nfA_of_lit fl PW _ ns hn, hz]) ν
  rw [axDen_append, axDen_neg, axDen_xpass V hρ _ e ν hW] at hz'
  rw [Prog.sym_ok V hρ fl hfl PW hPW p e he ν (hi_of p hv ν hc)]
  linear_combination hz'

/-- `certify_w_c` with a second round: the normal form of the difference passed under the context
again and normalised. -/
theorem certify_w2_c (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (C : Ctx) (p : Prog)
    (r e : List ATm) (ns ns2 : List (Option ATm)) (he : p.sym fl PW = some e)
    (hn : (xpass C e ++ axNeg r).map (normA fl PW AROUNDS) = ns)
    (hn2 : (xpass C ((ns.filterMap id).foldl (fun acc t => taAdd t acc) [])).map
      (normA fl PW AROUNDS) = ns2)
    (hz : (ns2.filterMap id).foldl (fun acc t => taAdd t acc) [] = [])
    (hv : ∀ c ∈ p.counts, ∀ v ∈ ipVs c, 2 * IN ≤ v) :
    ∀ ν, CtxOK V C ν → (∀ c ∈ p.counts, 0 ≤ ipDen ν c) → p.sem V ν = axDen V ν r := by
  intro ν hW hc
  have h1 := nfA_den V hρ fl hfl PW hPW (xpass C e ++ axNeg r) ν
  rw [nfA_of_lit fl PW _ ns hn] at h1
  have hz' := nfA_zero V hρ fl hfl PW hPW _ (by rw [nfA_of_lit fl PW _ ns2 hn2, hz]) ν
  rw [axDen_xpass V hρ C _ ν hW, h1, axDen_append, axDen_neg, axDen_xpass V hρ _ e ν hW] at hz'
  rw [Prog.sym_ok V hρ fl hfl PW hPW p e he ν (hi_of p hv ν hc)]
  linear_combination hz'

/-- `certify_eq_w_c` with a second round. -/
theorem certify_eq_w2_c (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (C : Ctx) (p q : Prog)
    (e r : List ATm) (ns ns2 : List (Option ATm)) (he : p.sym fl PW = some e)
    (hr : q.sym fl PW = some r)
    (hn : (xpass C e ++ axNeg r).map (normA fl PW AROUNDS) = ns)
    (hn2 : (xpass C ((ns.filterMap id).foldl (fun acc t => taAdd t acc) [])).map
      (normA fl PW AROUNDS) = ns2)
    (hz : (ns2.filterMap id).foldl (fun acc t => taAdd t acc) [] = [])
    (hvp : ∀ c ∈ p.counts, ∀ v ∈ ipVs c, 2 * IN ≤ v)
    (hvq : ∀ c ∈ q.counts, ∀ v ∈ ipVs c, 2 * IN ≤ v) :
    ∀ ν, CtxOK V C ν → (∀ c ∈ p.counts ++ q.counts, 0 ≤ ipDen ν c) →
      p.sem V ν = q.sem V ν := by
  intro ν hW hc
  rw [certify_w2_c V hρ fl hfl PW hPW C p r e ns ns2 he hn hn2 hz hvp ν hW
    (fun c h' => hc c (List.mem_append_left _ h')),
    Prog.sym_ok V hρ fl hfl PW hPW q r hr ν (hi_of q hvq ν fun c h' => hc c
      (List.mem_append_right _ h'))]

/-- `certify_lit_c` for a program without loops. -/
theorem certify_lit (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (p : Prog) (r e : List ATm)
    (ns : List (Option ATm)) (hc : p.counts = []) (he : p.sym fl PW = some e)
    (hn : (e ++ axNeg r).map (normA fl PW AROUNDS) = ns)
    (hz : (ns.filterMap id).foldl (fun acc t => taAdd t acc) [] = []) :
    p.sem V = fun ν => axDen V ν r := by
  funext ν
  exact certify_lit_c V hρ fl hfl PW hPW p r e ns he hn hz (by simp [hc]) ν (by simp [hc])

/-- Two programs equal at every valuation where their loop counts are nonnegative. -/
theorem certify_eq_lit_c (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (p q : Prog) (e r : List ATm)
    (ns : List (Option ATm)) (he : p.sym fl PW = some e) (hr : q.sym fl PW = some r)
    (hn : (e ++ axNeg r).map (normA fl PW AROUNDS) = ns)
    (hz : (ns.filterMap id).foldl (fun acc t => taAdd t acc) [] = [])
    (hvp : ∀ c ∈ p.counts, ∀ v ∈ ipVs c, 2 * IN ≤ v)
    (hvq : ∀ c ∈ q.counts, ∀ v ∈ ipVs c, 2 * IN ≤ v) :
    ∀ ν, (∀ c ∈ p.counts ++ q.counts, 0 ≤ ipDen ν c) → p.sem V ν = q.sem V ν := by
  intro ν hc
  rw [certify_lit_c V hρ fl hfl PW hPW p r e ns he hn hz hvp ν
    (fun c h' => hc c (List.mem_append_left _ h')),
    Prog.sym_ok V hρ fl hfl PW hPW q r hr ν (hi_of q hvq ν fun c h' => hc c
      (List.mem_append_right _ h'))]

/-- `certify_eq_lit_c` with the left program's expression rewritten under the context `C`. -/
theorem certify_eq_w_c (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (C : Ctx) (p q : Prog)
    (e r : List ATm) (ns : List (Option ATm)) (he : p.sym fl PW = some e)
    (hr : q.sym fl PW = some r)
    (hn : (xpass C e ++ axNeg r).map (normA fl PW AROUNDS) = ns)
    (hz : (ns.filterMap id).foldl (fun acc t => taAdd t acc) [] = [])
    (hvp : ∀ c ∈ p.counts, ∀ v ∈ ipVs c, 2 * IN ≤ v)
    (hvq : ∀ c ∈ q.counts, ∀ v ∈ ipVs c, 2 * IN ≤ v) :
    ∀ ν, CtxOK V C ν → (∀ c ∈ p.counts ++ q.counts, 0 ≤ ipDen ν c) →
      p.sem V ν = q.sem V ν := by
  intro ν hW hc
  rw [certify_w_c V hρ fl hfl PW hPW C p r e ns he hn hz hvp ν hW
    (fun c h' => hc c (List.mem_append_left _ h')),
    Prog.sym_ok V hρ fl hfl PW hPW q r hr ν (hi_of q hvq ν fun c h' => hc c
      (List.mem_append_right _ h'))]

/-- `certify_eq_lit_c` for programs without loops. -/
theorem certify_eq_lit (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (p q : Prog) (e r : List ATm)
    (ns : List (Option ATm)) (hcp : p.counts = []) (hcq : q.counts = [])
    (he : p.sym fl PW = some e) (hr : q.sym fl PW = some r)
    (hn : (e ++ axNeg r).map (normA fl PW AROUNDS) = ns)
    (hz : (ns.filterMap id).foldl (fun acc t => taAdd t acc) [] = []) :
    p.sem V = q.sem V := by
  funext ν
  exact certify_eq_lit_c V hρ fl hfl PW hPW p q e r ns he hr hn hz (by simp [hcp])
    (by simp [hcq]) ν (by simp [hcp, hcq])

/-! ## Normalisation -/

/-- Whether a term is a coefficient alone whose value is a positive real. -/
def posC (t : ATm) : Bool :=
  t.sums.isEmpty && t.ats.isEmpty && t.dels.isEmpty && t.phs.isEmpty && t.c.r == 0 &&
    t.c.am.isEmpty && t.c.gc.isEmpty && decide (0 < t.c.q) && t.c.rc.all (0 < ·) && t.aps.isEmpty

theorem zpw_rtv_pos (dv : ℕ → ℕ) (hd : ∀ i, 0 < dv i) :
    ∀ (k : ℕ) (l : List ℤ), ∃ x : ℝ, 0 < x ∧ zpw (rtv dv) k l = x
  | _, [] => ⟨1, one_pos, by simp [zpw]⟩
  | k, a :: v => by
    obtain ⟨x, hx, hxe⟩ := zpw_rtv_pos dv hd (k + 1) v
    have hs : 0 < Real.sqrt (dv k) := Real.sqrt_pos.2 (by exact_mod_cast hd k)
    refine ⟨Real.sqrt (dv k) ^ a * x, mul_pos (zpow_pos hs a) hx, ?_⟩
    simp only [zpw, hxe, rtv, rt]
    push_cast; ring

theorem rc_pos (l : List ℕ) (h : l.all (0 < ·) = true) : ∃ x : ℝ, 0 < x ∧ (l.map rt).prod = x := by
  induction l with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons c l ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨x, hx, hxe⟩ := ih h.2
    refine ⟨Real.sqrt c * x, mul_pos (Real.sqrt_pos.2 (by exact_mod_cast h.1)) hx, ?_⟩
    simp only [List.map_cons, List.prod_cons, hxe, rt]
    push_cast; ring

theorem posC_val (V : LV) (hρ : V.ρ.OK) (t : ATm) (h : posC t = true) (ν : ℕ → ℤ) :
    ∃ x : ℝ, 0 < x ∧ axDen V ν [t] = x := by
  obtain ⟨c, sums, ats, dels, phs, aps⟩ := t
  simp only [posC, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, ha⟩, hd⟩, hp⟩, hr⟩, ham⟩, hgc⟩, hq⟩, hrc⟩, hap⟩ := h
  subst hs ha hd hp hap
  obtain ⟨x, hx, hxe⟩ := zpw_rtv_pos V.ρ.dv hρ.dpos 0 c.sq
  obtain ⟨y, hy, hye⟩ := rc_pos c.rc hrc
  refine ⟨(c.q : ℝ) * x * y, mul_pos (mul_pos (by exact_mod_cast hq) hx) hy, ?_⟩
  simp only [axDen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ATm.den,
    CMon.den, hr, ham, hgc, hxe, hye, zpw, List.map_nil, List.prod_nil]
  simp [sumsV, abody, bodyOf, apsV, ex_zero]

theorem nrm_of (x : ℝ) (hx : 0 < x) (z w : ℂ) (hz : (x : ℂ) * x * z = 1) :
    (x : ℂ) * w = ((Real.sqrt z.re : ℝ) : ℂ)⁻¹ * w := by
  have hz' : z = (((x * x)⁻¹ : ℝ) : ℂ) := by
    push_cast
    exact eq_inv_of_mul_eq_one_right hz
  rw [hz', Complex.ofReal_re, Real.sqrt_inv, Real.sqrt_mul_self hx.le, Complex.ofReal_inv, inv_inv]

/-- `k p` is `p` over the root of `⟨p|p⟩` when `k² ⟨p|p⟩ = 1` for a positive real coefficient
`k`. -/
theorem nrm_scale (V : LV) (hρ : V.ρ.OK) (L : List DMon) (p : Prog) (k : ATm)
    (hk : posC k = true) (ν : ℕ → ℤ)
    (hB : (Prog.mul (.mul (.leaf [k]) (.leaf [k])) (.inn L p p)).sem V ν =
      axDen V ν [⟨CMon.ofQ 1, [], [], [], [], []⟩]) :
    (Prog.mul (.leaf [k]) p).sem V ν =
      ((Real.sqrt ((Prog.inn L p p).sem V ν).re : ℝ) : ℂ)⁻¹ * p.sem V ν := by
  obtain ⟨x, hx, hxe⟩ := posC_val V hρ k hk ν
  have h1 : axDen V ν [⟨CMon.ofQ 1, [], [], [], [], []⟩] = 1 := by
    simp [axDen, ATm.den, CMon.den, CMon.ofQ, ex_zero, zpw, sumsV, abody, bodyOf, apsV]
  simp only [Prog.sem, hxe] at hB ⊢
  rw [h1] at hB
  exact nrm_of x hx _ _ hB

/-- `r` is `p` over the root of `⟨p|p⟩` when `k p = r` and `k² ⟨p|p⟩ = 1` for a positive real
coefficient `k`. -/
theorem nrm_cert (V : LV) (hρ : V.ρ.OK) (L : List DMon) (p : Prog) (r : List ATm) (k : ATm)
    (hk : posC k = true) (ν : ℕ → ℤ)
    (hA : (Prog.mul (.leaf [k]) p).sem V ν = axDen V ν r)
    (hB : (Prog.mul (.mul (.leaf [k]) (.leaf [k])) (.inn L p p)).sem V ν =
      axDen V ν [⟨CMon.ofQ 1, [], [], [], [], []⟩]) :
    axDen V ν r = ((Real.sqrt ((Prog.inn L p p).sem V ν).re : ℝ) : ℂ)⁻¹ * p.sem V ν := by
  obtain ⟨x, hx, hxe⟩ := posC_val V hρ k hk ν
  have h1 : axDen V ν [⟨CMon.ofQ 1, [], [], [], [], []⟩] = 1 := by
    simp [axDen, ATm.den, CMon.den, CMon.ofQ, ex_zero, zpw, sumsV, abody, bodyOf, apsV]
  simp only [Prog.sem, hxe] at hA hB
  rw [h1] at hB
  rw [← hA]
  exact nrm_of x hx _ _ hB

/-! ## Real coefficient atoms -/

theorem zpw_set (f : ℕ → ℂ) : ∀ (k i : ℕ) (l : List ℤ),
    zpw f k l = zpw f k (l.set i 0) * f (k + i) ^ (l.getD i 0)
  | k, i, [] => by simp [zpw]
  | k, 0, a :: l => by simp [zpw]; ring
  | k, i + 1, a :: l => by
    simp only [zpw, List.set_cons_succ, List.getD_cons_succ]
    rw [zpw_set f (k + 1) i l, show k + (i + 1) = k + 1 + i by omega]
    ring

/-- `m` with the exponent of atom `2 j + 1` moved to atom `2 j`. -/
def realC (j : ℕ) (m : CMon) : CMon :=
  CMon.mul { m with am := m.am.set (2 * j + 1) 0 } (CMon.atomP (2 * j) (m.am.getD (2 * j + 1) 0))

theorem realC_den (ρ : Val) (hρ : ρ.OK) (j : ℕ) (h : ρ.atom (2 * j + 1) = ρ.atom (2 * j))
    (m : CMon) : (realC j m).den ρ = m.den ρ := by
  unfold realC
  rw [CMon.den_mul ρ hρ, atomP_den, ← h]
  conv_rhs => simp only [CMon.den]; rw [zpw_set ρ.atom 0 (2 * j + 1) m.am]
  simp only [CMon.den, zero_add]
  ring

/-- A term with the atoms `2 j`, `j ∈ rs`, read as real. -/
def realT (rs : List ℕ) (t : ATm) : ATm :=
  ⟨rs.foldl (fun m j => realC j m) t.c, t.sums, t.ats, t.dels, t.phs, t.aps⟩

theorem realT_den (V : LV) (hρ : V.ρ.OK) (rs : List ℕ)
    (h : ∀ j ∈ rs, V.ρ.atom (2 * j + 1) = V.ρ.atom (2 * j)) (t : ATm) (ν : ℕ → ℤ) :
    (realT rs t).den V ν = t.den V ν := by
  have hf : ∀ (l : List ℕ) (m : CMon), (∀ j ∈ l, V.ρ.atom (2 * j + 1) = V.ρ.atom (2 * j)) →
      (l.foldl (fun m j => realC j m) m).den V.ρ = m.den V.ρ := by
    intro l
    induction l with
    | nil => intro m _; rfl
    | cons j l ih =>
      intro m hl
      simp only [List.foldl_cons]
      rw [ih _ (fun j hj => hl j (List.mem_cons_of_mem _ hj)),
        realC_den V.ρ hρ j (hl j List.mem_cons_self) m]
  simp only [ATm.den, realT]
  rw [hf rs t.c h]
  rfl

theorem axDen_real (V : LV) (hρ : V.ρ.OK) (rs : List ℕ)
    (h : ∀ j ∈ rs, V.ρ.atom (2 * j + 1) = V.ρ.atom (2 * j)) (e : List ATm) (ν : ℕ → ℤ) :
    axDen V ν (e.map (realT rs)) = axDen V ν e := by
  simp only [axDen, List.map_map, Function.comp_def, realT_den V hρ rs h]

/-- `certify_lit_c` with the atoms `2 j`, `j ∈ rs`, real. -/
theorem certify_real_c (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (rs : List ℕ)
    (hr : ∀ j ∈ rs, starRingEnd ℂ (V.ρ.atom (2 * j)) = V.ρ.atom (2 * j)) (p : Prog)
    (r e : List ATm) (ns : List (Option ATm)) (he : p.sym fl PW = some e)
    (hn : ((e ++ axNeg r).map (realT rs)).map (normA fl PW AROUNDS) = ns)
    (hz : (ns.filterMap id).foldl (fun acc t => taAdd t acc) [] = [])
    (hv : ∀ c ∈ p.counts, ∀ v ∈ ipVs c, 2 * IN ≤ v) :
    ∀ ν, (∀ c ∈ p.counts, 0 ≤ ipDen ν c) → p.sem V ν = axDen V ν r := by
  intro ν hc
  have h' : ∀ j ∈ rs, V.ρ.atom (2 * j + 1) = V.ρ.atom (2 * j) := fun j hj => by
    rw [hρ.aconj, hr j hj]
  have hz' := nfA_zero V hρ fl hfl PW hPW _ (by rw [nfA_of_lit fl PW _ ns hn, hz]) ν
  rw [axDen_real V hρ rs h', axDen_append, axDen_neg] at hz'
  rw [Prog.sym_ok V hρ fl hfl PW hPW p e he ν (hi_of p hv ν hc)]
  linear_combination hz'

/-- `certify_eq_lit_c` with the atoms `2 j`, `j ∈ rs`, real. -/
theorem certify_eq_real_c (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (rs : List ℕ)
    (hr : ∀ j ∈ rs, starRingEnd ℂ (V.ρ.atom (2 * j)) = V.ρ.atom (2 * j)) (p q : Prog)
    (e r : List ATm) (ns : List (Option ATm)) (he : p.sym fl PW = some e)
    (hq : q.sym fl PW = some r)
    (hn : ((e ++ axNeg r).map (realT rs)).map (normA fl PW AROUNDS) = ns)
    (hz : (ns.filterMap id).foldl (fun acc t => taAdd t acc) [] = [])
    (hvp : ∀ c ∈ p.counts, ∀ v ∈ ipVs c, 2 * IN ≤ v)
    (hvq : ∀ c ∈ q.counts, ∀ v ∈ ipVs c, 2 * IN ≤ v) :
    ∀ ν, (∀ c ∈ p.counts ++ q.counts, 0 ≤ ipDen ν c) → p.sem V ν = q.sem V ν := by
  intro ν hc
  rw [certify_real_c V hρ fl hfl PW hPW rs hr p r e ns he hn hz hvp ν
    (fun c h' => hc c (List.mem_append_left _ h')),
    Prog.sym_ok V hρ fl hfl PW hPW q r hq ν (hi_of q hvq ν fun c h' => hc c
      (List.mem_append_right _ h'))]

/-! ## Unit coefficient atoms -/

/-- `m` with the exponent of atom `2 j + 1` moved, negated, to atom `2 j`. -/
def unitC (j : ℕ) (m : CMon) : CMon :=
  CMon.mul { m with am := m.am.set (2 * j + 1) 0 } (CMon.atomP (2 * j) (-(m.am.getD (2 * j + 1) 0)))

theorem unitC_den (ρ : Val) (hρ : ρ.OK) (j : ℕ) (h : ρ.atom (2 * j + 1) = (ρ.atom (2 * j))⁻¹)
    (m : CMon) : (unitC j m).den ρ = m.den ρ := by
  unfold unitC
  rw [CMon.den_mul ρ hρ, atomP_den]
  conv_rhs => simp only [CMon.den]; rw [zpw_set ρ.atom 0 (2 * j + 1) m.am]
  simp only [CMon.den, zero_add, h, inv_zpow', zpow_neg]
  ring

/-- A term with the atoms `2 j`, `j ∈ us`, read as of modulus 1. -/
def unitT (us : List ℕ) (t : ATm) : ATm :=
  ⟨us.foldl (fun m j => unitC j m) t.c, t.sums, t.ats, t.dels, t.phs, t.aps⟩

theorem unitT_den (V : LV) (hρ : V.ρ.OK) (us : List ℕ)
    (h : ∀ j ∈ us, V.ρ.atom (2 * j + 1) = (V.ρ.atom (2 * j))⁻¹) (t : ATm) (ν : ℕ → ℤ) :
    (unitT us t).den V ν = t.den V ν := by
  have hf : ∀ (l : List ℕ) (m : CMon), (∀ j ∈ l, V.ρ.atom (2 * j + 1) = (V.ρ.atom (2 * j))⁻¹) →
      (l.foldl (fun m j => unitC j m) m).den V.ρ = m.den V.ρ := by
    intro l
    induction l with
    | nil => intro m _; rfl
    | cons j l ih =>
      intro m hl
      simp only [List.foldl_cons]
      rw [ih _ (fun j hj => hl j (List.mem_cons_of_mem _ hj)),
        unitC_den V.ρ hρ j (hl j List.mem_cons_self) m]
  simp only [ATm.den, unitT]
  rw [hf us t.c h]
  rfl

theorem axDen_unit (V : LV) (hρ : V.ρ.OK) (us : List ℕ)
    (h : ∀ j ∈ us, V.ρ.atom (2 * j + 1) = (V.ρ.atom (2 * j))⁻¹) (e : List ATm) (ν : ℕ → ℤ) :
    axDen V ν (e.map (unitT us)) = axDen V ν e := by
  simp only [axDen, List.map_map, Function.comp_def, unitT_den V hρ us h]

theorem unit_inv (V : LV) (hρ : V.ρ.OK) (j : ℕ)
    (h : V.ρ.atom (2 * j) * starRingEnd ℂ (V.ρ.atom (2 * j)) = 1) :
    V.ρ.atom (2 * j + 1) = (V.ρ.atom (2 * j))⁻¹ := by
  rw [hρ.aconj]
  exact (eq_inv_of_mul_eq_one_right h)

/-- `certify_lit_c` with the atoms `2 j`, `j ∈ us`, of modulus 1. -/
theorem certify_unit_c (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (us : List ℕ)
    (hu : ∀ j ∈ us, V.ρ.atom (2 * j) * starRingEnd ℂ (V.ρ.atom (2 * j)) = 1) (p : Prog)
    (r e : List ATm) (ns : List (Option ATm)) (he : p.sym fl PW = some e)
    (hn : ((e ++ axNeg r).map (unitT us)).map (normA fl PW AROUNDS) = ns)
    (hz : (ns.filterMap id).foldl (fun acc t => taAdd t acc) [] = [])
    (hv : ∀ c ∈ p.counts, ∀ v ∈ ipVs c, 2 * IN ≤ v) :
    ∀ ν, (∀ c ∈ p.counts, 0 ≤ ipDen ν c) → p.sem V ν = axDen V ν r := by
  intro ν hc
  have h' : ∀ j ∈ us, V.ρ.atom (2 * j + 1) = (V.ρ.atom (2 * j))⁻¹ := fun j hj =>
    unit_inv V hρ j (hu j hj)
  have hz' := nfA_zero V hρ fl hfl PW hPW _ (by rw [nfA_of_lit fl PW _ ns hn, hz]) ν
  rw [axDen_unit V hρ us h', axDen_append, axDen_neg] at hz'
  rw [Prog.sym_ok V hρ fl hfl PW hPW p e he ν (hi_of p hv ν hc)]
  linear_combination hz'

/-- `certify_eq_lit_c` with the atoms `2 j`, `j ∈ us`, of modulus 1. -/
theorem certify_eq_unit_c (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (us : List ℕ)
    (hu : ∀ j ∈ us, V.ρ.atom (2 * j) * starRingEnd ℂ (V.ρ.atom (2 * j)) = 1) (p q : Prog)
    (e r : List ATm) (ns : List (Option ATm)) (he : p.sym fl PW = some e)
    (hq : q.sym fl PW = some r)
    (hn : ((e ++ axNeg r).map (unitT us)).map (normA fl PW AROUNDS) = ns)
    (hz : (ns.filterMap id).foldl (fun acc t => taAdd t acc) [] = [])
    (hvp : ∀ c ∈ p.counts, ∀ v ∈ ipVs c, 2 * IN ≤ v)
    (hvq : ∀ c ∈ q.counts, ∀ v ∈ ipVs c, 2 * IN ≤ v) :
    ∀ ν, (∀ c ∈ p.counts ++ q.counts, 0 ≤ ipDen ν c) → p.sem V ν = q.sem V ν := by
  intro ν hc
  rw [certify_unit_c V hρ fl hfl PW hPW us hu p r e ns he hn hz hvp ν
    (fun c h' => hc c (List.mem_append_left _ h')),
    Prog.sym_ok V hρ fl hfl PW hPW q r hq ν (hi_of q hvq ν fun c h' => hc c
      (List.mem_append_right _ h'))]

/-! ## Operators on inputs in range -/

/-- `certify_lit` at every valuation whose variables of `rg` lie in their ranges. -/
theorem certify_rg (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (rg : List (ℕ × DMon)) (p : Prog)
    (r e : List ATm) (ns : List (Option ATm)) (hc : p.counts = []) (he : p.sym fl PW = some e)
    (hn : ((e ++ axNeg r).map (rgT rg)).map (normA fl PW AROUNDS) = ns)
    (hz : (ns.filterMap id).foldl (fun acc t => taAdd t acc) [] = []) :
    ∀ ν, RgOK V rg ν → p.sem V ν = axDen V ν r := by
  intro ν hR
  have hz' := nfA_zero V hρ fl hfl PW hPW _ (by rw [nfA_of_lit fl PW _ ns hn, hz]) ν
  rw [axDen_rg V rg _ ν hR, axDen_append, axDen_neg] at hz'
  rw [Prog.sym_ok V hρ fl hfl PW hPW p e he ν (hi_of p (by simp [hc]) ν (by simp [hc]))]
  linear_combination hz'

/-- `certify_eq_lit` at every valuation whose variables of `rg` lie in their ranges. -/
theorem certify_eq_rg (V : LV) (hρ : V.ρ.OK) (fl : List ℕ) (hfl : FloorOK fl V.ρ)
    (PW : List (DMon × DMon)) (hPW : PowOK PW V.ρ) (rg : List (ℕ × DMon)) (p q : Prog)
    (e r : List ATm) (ns : List (Option ATm)) (hcp : p.counts = []) (hcq : q.counts = [])
    (he : p.sym fl PW = some e) (hq : q.sym fl PW = some r)
    (hn : ((e ++ axNeg r).map (rgT rg)).map (normA fl PW AROUNDS) = ns)
    (hz : (ns.filterMap id).foldl (fun acc t => taAdd t acc) [] = []) :
    ∀ ν, RgOK V rg ν → p.sem V ν = q.sem V ν := by
  intro ν hR
  rw [certify_rg V hρ fl hfl PW hPW rg p r e ns hcp he hn hz ν hR,
    Prog.sym_ok V hρ fl hfl PW hPW q r hq ν (hi_of q (by simp [hcq]) ν (by simp [hcq]))]

end DiracULA.Lang
