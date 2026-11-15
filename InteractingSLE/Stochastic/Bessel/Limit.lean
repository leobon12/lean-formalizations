/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Stochastic.Bessel.Estimate

/-!
# The monotone limit of regularized Bessel solutions (pathwise part)

Packet PROVE-BESSEL. Fix `c > 0`, `x`, a continuous path `w : ℝ → ℝ` and a positive antitone
sequence `e n → 0`. The regularized solutions `U n = regSol c (e n) x w` (`seqSol`) increase in `n`
(`regSol_le_regSol`); `X = ⨆ n, U n` (`limSol`) and `A_t = X_t - x - w_t` (the increasing limit of
`A n t = ∫₀ᵗ c / max (U n s) (e n) ds`, `seqA`). On the event that `(U n N)_n` is bounded, for
`0 ≤ a ≤ b ≤ N`:

* `U n t → X t` (`tendsto_seqSol`);
* `{s ∈ [0, N] : X s ≤ 0}` is Lebesgue-null (`volume_limSol_nonpos`): there `U n ≤ 0 < e n`, so the
  drift equals `c / e n` and `(c / e n) · Leb ≤ A n N ≤ A_N`;
* `A_b - A_a ≥ ∫ₐᵇ c / max (X s) 0 ds`, and `s ↦ c / max (X s) 0` is integrable on `[0, N]`
  (`integral_le_limA_sub`): split the drift as `cut η (U) · b + qfun η (U)` with the continuous
  bounded `qfun η y = (1 - cut η y) c / max y η` (`≤ c / max y 0`, increasing to it as `η ↓ 0`),
  pass to the limit in `n` by dominated convergence and in `η` by monotone convergence;
* `A_N - ∫₀ᴺ qfun η (X) = lim_n J n η` with `J n η = ∫₀ᴺ cut η (U n) · b` (`tendsto_seqJ`).
-/

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

noncomputable section

namespace InteractingSLE

namespace Bessel

/-! ### The sequence of regularized solutions and its supremum -/

/-- The `n`-th regularized solution `regSol c (e n) x w`, on `ℝ≥0`. -/
def seqSol (c x : ℝ) (e : ℕ → ℝ) (w : ℝ → ℝ) (n : ℕ) (t : ℝ≥0) : ℝ := regSol c (e n) x w t

/-- The drift integral of the `n`-th regularized solution. -/
def seqA (c x : ℝ) (e : ℕ → ℝ) (w : ℝ → ℝ) (n : ℕ) (t : ℝ≥0) : ℝ :=
  ∫ s in (0 : ℝ)..t, regDrift c (e n) (seqSol c x e w n s.toNNReal)

/-- The pathwise Bessel candidate `⨆ n, seqSol c x e w n t`. -/
def limSol (c x : ℝ) (e : ℕ → ℝ) (w : ℝ → ℝ) (t : ℝ≥0) : ℝ := ⨆ n, seqSol c x e w n t

variable {c x : ℝ} {e : ℕ → ℝ} {w : ℝ → ℝ}

theorem seqSol_eq (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n) (n : ℕ) (t : ℝ≥0) :
    seqSol c x e w n t = x + w t + seqA c x e w n t := by
  rw [seqSol, regSol_eq hw hc (he n) x t.coe_nonneg, seqA]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le t.coe_nonneg] at hr
  simp only [seqSol, Real.coe_toNNReal r hr.1]

theorem continuous_seqSol (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n) (n : ℕ) :
    Continuous (seqSol c x e w n) := by
  have h := continuousOn_regSol_Ici hw hc (he n) x
  exact h.comp_continuous NNReal.continuous_coe fun t => t.coe_nonneg

theorem continuous_seqSol_real (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n) (n : ℕ) :
    Continuous fun s : ℝ => seqSol c x e w n s.toNNReal :=
  (continuous_seqSol hw hc he n).comp continuous_real_toNNReal

theorem seqA_nonneg (hc : 0 ≤ c) (he : ∀ n, 0 < e n) (n : ℕ) (t : ℝ≥0) :
    0 ≤ seqA c x e w n t :=
  intervalIntegral.integral_nonneg t.coe_nonneg fun _ _ => regDrift_nonneg hc (he n) _

theorem seqSol_mono (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n) (hanti : Antitone e)
    (t : ℝ≥0) : Monotone fun n => seqSol c x e w n t := fun _ m hnm =>
  regSol_le_regSol hw hc le_rfl (he m) (hanti hnm) le_rfl t.coe_nonneg

theorem seqA_mono (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n) (hanti : Antitone e)
    (t : ℝ≥0) : Monotone fun n => seqA c x e w n t := fun n m hnm => by
  have h := seqSol_mono (x := x) hw hc he hanti t hnm
  simp only [seqSol_eq hw hc he] at h
  linarith

theorem intervalIntegrable_regDrift_seqSol (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n)
    (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => regDrift c (e n) (seqSol c x e w n s.toNNReal)) volume a b :=
  ((continuous_regDrift hc (he n)).comp (continuous_seqSol_real hw hc he n)).intervalIntegrable a b

/-- Increments of the drift integral. -/
theorem seqA_sub (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n) (n : ℕ) (a b : ℝ≥0) :
    seqA c x e w n b - seqA c x e w n a
      = ∫ s in (a : ℝ)..b, regDrift c (e n) (seqSol c x e w n s.toNNReal) :=
  intervalIntegral.integral_interval_sub_left (intervalIntegrable_regDrift_seqSol hw hc he n _ _)
    (intervalIntegrable_regDrift_seqSol hw hc he n _ _)

theorem seqA_mono_time (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n) (n : ℕ) {a b : ℝ≥0}
    (hab : a ≤ b) : seqA c x e w n a ≤ seqA c x e w n b := by
  have h := seqA_sub (x := x) hw hc he n a b
  have : 0 ≤ ∫ s in (a : ℝ)..b, regDrift c (e n) (seqSol c x e w n s.toNNReal) :=
    intervalIntegral.integral_nonneg (by exact_mod_cast hab) fun _ _ => regDrift_nonneg hc (he n) _
  linarith

/-- Boundedness at a time `N` propagates to earlier times. -/
theorem bddAbove_seqSol_of_le (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n) {N t : ℝ≥0}
    (hN : BddAbove (range fun n => seqSol c x e w n N)) (ht : t ≤ N) :
    BddAbove (range fun n => seqSol c x e w n t) := by
  obtain ⟨M, hM⟩ := hN
  refine ⟨M - w N + w t, ?_⟩
  rintro _ ⟨n, rfl⟩
  have h1 := hM ⟨n, rfl⟩
  have h2 := seqA_mono_time (x := x) hw hc he n ht
  simp only [seqSol_eq hw hc he] at h1 ⊢
  linarith

theorem tendsto_seqSol (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n) (hanti : Antitone e)
    {t : ℝ≥0} (hb : BddAbove (range fun n => seqSol c x e w n t)) :
    Tendsto (fun n => seqSol c x e w n t) atTop (𝓝 (limSol c x e w t)) :=
  tendsto_atTop_ciSup (seqSol_mono hw hc he hanti t) hb

theorem seqSol_le_limSol {t : ℝ≥0} (hb : BddAbove (range fun n => seqSol c x e w n t)) (n : ℕ) :
    seqSol c x e w n t ≤ limSol c x e w t :=
  le_ciSup hb n

theorem measurable_limSol_real (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n) :
    Measurable fun s : ℝ => limSol c x e w s.toNNReal :=
  Measurable.iSup fun n => (continuous_seqSol_real hw hc he n).measurable

/-- The limit drift `A_t = X_t - x - w_t` is the limit of `seqA n t`. -/
theorem tendsto_seqA (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n) (hanti : Antitone e)
    {t : ℝ≥0} (hb : BddAbove (range fun n => seqSol c x e w n t)) :
    Tendsto (fun n => seqA c x e w n t) atTop (𝓝 (limSol c x e w t - x - w t)) := by
  have h := ((tendsto_seqSol hw hc he hanti hb).sub_const x).sub_const (w t)
  refine h.congr fun n => ?_
  rw [seqSol_eq hw hc he]; ring

theorem seqA_le_limA (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n) {t : ℝ≥0}
    (hb : BddAbove (range fun n => seqSol c x e w n t)) (n : ℕ) :
    seqA c x e w n t ≤ limSol c x e w t - x - w t := by
  have := seqSol_le_limSol hb n
  rw [seqSol_eq hw hc he] at this
  linarith

/-! ### The set where the limit is nonpositive is Lebesgue-null -/

/-- On a bounded path, `{s ∈ [0, N] : X s ≤ 0}` is Lebesgue-null. -/
theorem volume_limSol_nonpos (hw : Continuous w) (hc : 0 < c) (he : ∀ n, 0 < e n)
    (hlim : Tendsto e atTop (𝓝 0)) {N : ℝ≥0}
    (hN : BddAbove (range fun n => seqSol c x e w n N)) :
    volume {s : ℝ | s ∈ Icc (0 : ℝ) N ∧ limSol c x e w s.toNNReal ≤ 0} = 0 := by
  set S : Set ℝ := {s | s ∈ Ioc (0 : ℝ) N ∧ limSol c x e w s.toNNReal ≤ 0} with hSdef
  have hS : MeasurableSet S :=
    measurableSet_Ioc.inter (measurableSet_le (measurable_limSol_real hw hc.le he) measurable_const)
  set L := limSol c x e w N - x - w N
  have hSfin : volume S < ∞ :=
    (measure_mono fun s hs => hs.1).trans_lt (by simp [Real.volume_Ioc])
  have hbound : ∀ n, (volume S).toReal ≤ L * e n / c := by
    intro n
    have hint1 : IntervalIntegrable (S.indicator fun _ => c / e n) volume 0 N := by
      have h := intervalIntegrable_const (μ := volume) (a := (0 : ℝ)) (b := N) (c := c / e n)
      exact ⟨h.1.indicator hS, h.2.indicator hS⟩
    have hmono := intervalIntegral.integral_mono_on N.coe_nonneg hint1
      (intervalIntegrable_regDrift_seqSol hw hc.le he n 0 N) fun s hs => by
        by_cases hsS : s ∈ S
        · rw [indicator_of_mem hsS]
          have hbd := bddAbove_seqSol_of_le (x := x) hw hc.le he hN
            (t := s.toNNReal) (Real.toNNReal_le_iff_le_coe.2 hs.2)
          have hle : seqSol c x e w n s.toNNReal ≤ e n :=
            ((seqSol_le_limSol hbd n).trans hsS.2).trans (he n).le
          rw [regDrift_of_le' hle]
        · rw [indicator_of_notMem hsS]; exact regDrift_nonneg hc.le (he n) _
    have hval : ∫ s in (0 : ℝ)..N, S.indicator (fun _ => c / e n) s = (volume S).toReal * (c / e n) := by
      rw [intervalIntegral.integral_of_le N.coe_nonneg, integral_indicator_const _ hS,
        measureReal_def, Measure.restrict_apply hS, inter_eq_left.2 (fun s hs => hs.1), smul_eq_mul]
    have hA : seqA c x e w n N ≤ L := seqA_le_limA hw hc.le he hN n
    rw [hval] at hmono
    have h2 : (volume S).toReal * (c / e n) ≤ L := hmono.trans hA
    rw [le_div_iff₀ hc]
    have hen := he n
    calc (volume S).toReal * c = (volume S).toReal * (c / e n) * e n := by field_simp
      _ ≤ L * e n := mul_le_mul_of_nonneg_right h2 hen.le
  have htend : Tendsto (fun n => L * e n / c) atTop (𝓝 0) := by
    have := (hlim.const_mul L).div_const c
    simpa using this
  have h0 : (volume S).toReal ≤ 0 := ge_of_tendsto' htend hbound
  have hS0 : volume S = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm h0 ENNReal.toReal_nonneg) with h | h
    · exact h
    · exact absurd h hSfin.ne
  refine measure_mono_null (t := S ∪ {0}) ?_ (measure_union_null hS0 (Real.volume_singleton))
  intro s hs
  rcases eq_or_lt_of_le hs.1.1 with h | h
  · exact Or.inr h.symm
  · exact Or.inl ⟨⟨h, hs.1.2⟩, hs.2⟩

/-! ### The cut-off drift `qfun` -/

/-- The cut-off drift `(1 - cut η y) · c / max y η`; it vanishes for `y ≤ η` and is `≤ c / max y 0`. -/
def qfun (c η y : ℝ) : ℝ := (1 - cut η y) * regDrift c η y

theorem one_sub_cut_nonneg (η y : ℝ) : 0 ≤ 1 - cut η y := by linarith [cut_le_one η y]

theorem qfun_nonneg (hc : 0 ≤ c) {η : ℝ} (hη : 0 < η) (y : ℝ) : 0 ≤ qfun c η y :=
  mul_nonneg (one_sub_cut_nonneg η y) (regDrift_nonneg hc hη y)

theorem qfun_le (hc : 0 ≤ c) {η : ℝ} (hη : 0 < η) (y : ℝ) : qfun c η y ≤ c / η := by
  have h1 : 1 - cut η y ≤ 1 := by linarith [cut_nonneg η y]
  calc qfun c η y ≤ 1 * regDrift c η y :=
        mul_le_mul_of_nonneg_right h1 (regDrift_nonneg hc hη y)
    _ ≤ c / η := by rw [one_mul]; exact regDrift_le hc hη y

theorem continuous_qfun (hc : 0 ≤ c) {η : ℝ} (hη : 0 < η) : Continuous (qfun c η) :=
  (continuous_const.sub (continuous_cut η)).mul (continuous_regDrift hc hη)

theorem qfun_of_le {η y : ℝ} (hη : 0 < η) (hy : y ≤ η) : qfun c η y = 0 := by
  rw [qfun, cut_eq_one hη hy, sub_self, zero_mul]

/-- `regDrift c ε = cut η · regDrift c ε + qfun c η` for `ε ≤ η`. -/
theorem regDrift_eq_cut_add_qfun (hε : 0 < ε) {η : ℝ} (hεη : ε ≤ η) (y : ℝ) :
    regDrift c ε y = cut η y * regDrift c ε y + qfun c η y := by
  have hη : 0 < η := hε.trans_le hεη
  rcases le_total y η with hy | hy
  · rw [qfun_of_le hη hy, cut_eq_one hη hy]; ring
  · rw [qfun, regDrift_of_le (hεη.trans hy), regDrift_of_le hy]; ring

/-- `qfun c η y ≤ c / max y 0 = regDrift c 0 y`. -/
theorem qfun_le_regDrift_zero (hc : 0 ≤ c) {η : ℝ} (hη : 0 < η) (y : ℝ) :
    qfun c η y ≤ regDrift c 0 y := by
  have h0 : 0 ≤ regDrift c 0 y := div_nonneg hc (le_max_right _ _)
  rcases le_total y η with hy | hy
  · rw [qfun_of_le hη hy]; exact h0
  · have h1 : 1 - cut η y ≤ 1 := by linarith [cut_nonneg η y]
    have hy0 : 0 ≤ y := hη.le.trans hy
    have : regDrift c η y = regDrift c 0 y := by
      rw [regDrift_of_le hy, regDrift_of_le hy0]
    calc qfun c η y ≤ 1 * regDrift c η y :=
          mul_le_mul_of_nonneg_right h1 (regDrift_nonneg hc hη y)
      _ = regDrift c 0 y := by rw [one_mul, this]

theorem cut_anti {η η' : ℝ} (hη' : 0 < η') (hηη : η' ≤ η) (y : ℝ) : cut η' y ≤ cut η y := by
  have hη : 0 < η := hη'.trans_le hηη
  rcases le_total y η' with hy | hy
  · rw [cut_eq_one hη' hy, cut_eq_one hη (hy.trans hηη)]
  · have hy0 : 0 ≤ y := hη'.le.trans hy
    have : y / η ≤ y / η' := div_le_div_of_nonneg_left hy0 hη' hηη
    unfold cut
    exact min_le_min le_rfl (max_le_max le_rfl (by linarith))

/-- `qfun c η y` increases as `η` decreases. -/
theorem qfun_anti (hc : 0 ≤ c) {η η' : ℝ} (hη' : 0 < η') (hηη : η' ≤ η) (y : ℝ) :
    qfun c η y ≤ qfun c η' y := by
  have hη : 0 < η := hη'.trans_le hηη
  have h1 : 1 - cut η y ≤ 1 - cut η' y := by linarith [cut_anti hη' hηη y]
  exact mul_le_mul h1 (regDrift_le_of_le hc hη' hηη y) (regDrift_nonneg hc hη y)
    (one_sub_cut_nonneg η' y)

/-- The levels `ηₖ = 1 / (k + 1)`. -/
def levelSeq (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem levelSeq_pos (k : ℕ) : 0 < levelSeq k := by unfold levelSeq; positivity

theorem levelSeq_anti : Antitone levelSeq := fun k l hkl => by
  unfold levelSeq
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hkl 1)

theorem tendsto_levelSeq : Tendsto levelSeq atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

/-- `qfun c ηₖ y → c / max y 0` (the sequence is eventually constant). -/
theorem tendsto_qfun_levelSeq (y : ℝ) :
    Tendsto (fun k => qfun c (levelSeq k) y) atTop (𝓝 (regDrift c 0 y)) := by
  rcases le_or_gt y 0 with hy | hy
  · have : ∀ k, qfun c (levelSeq k) y = regDrift c 0 y := fun k => by
      rw [qfun_of_le (levelSeq_pos k) (hy.trans (levelSeq_pos k).le), regDrift,
        max_eq_right hy, div_zero]
    simp only [this]; exact tendsto_const_nhds
  · have hev : ∀ᶠ k in atTop, 2 * levelSeq k ≤ y := by
      have h := (tendsto_levelSeq.const_mul 2).eventually_lt_const (u := y) (by linarith)
      exact h.mono fun k hk => hk.le
    refine tendsto_const_nhds.congr' (hev.mono fun k hk => ?_)
    have hl := levelSeq_pos k
    show regDrift c 0 y = (1 - cut (levelSeq k) y) * regDrift c (levelSeq k) y
    rw [cut_eq_zero hl hk, regDrift_of_le (show levelSeq k ≤ y by linarith),
      regDrift_of_le (show (0 : ℝ) ≤ y from hy.le)]
    ring

/-! ### Limits of the cut-off drift integrals -/

/-- `∫ₐᵇ qfun c η (U n s) ds → ∫ₐᵇ qfun c η (X s) ds` on a bounded path. -/
theorem tendsto_integral_qfun_seqSol (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n)
    (hanti : Antitone e) {η : ℝ} (hη : 0 < η) {N a b : ℝ≥0}
    (hN : BddAbove (range fun n => seqSol c x e w n N)) (hab : a ≤ b) (hbN : b ≤ N) :
    Tendsto (fun n => ∫ s in (a : ℝ)..b, qfun c η (seqSol c x e w n s.toNNReal)) atTop
      (𝓝 (∫ s in (a : ℝ)..b, qfun c η (limSol c x e w s.toNNReal))) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => c / η)
    (Eventually.of_forall fun n =>
      ((continuous_qfun hc hη).comp (continuous_seqSol_real hw hc he n)).aestronglyMeasurable)
    (Eventually.of_forall fun n => ae_of_all _ fun s _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (qfun_nonneg hc hη _)]; exact qfun_le hc hη _)
    intervalIntegrable_const (ae_of_all _ fun s hs => ?_)
  rw [uIoc_of_le (by exact_mod_cast hab)] at hs
  have hsN : s.toNNReal ≤ N := Real.toNNReal_le_iff_le_coe.2 (hs.2.trans (by exact_mod_cast hbN))
  have hbd := bddAbove_seqSol_of_le (x := x) hw hc he hN hsN
  exact ((continuous_qfun hc hη).tendsto _).comp (tendsto_seqSol hw hc he hanti hbd)

/-- Eventually (`e n ≤ η`) the cut-off drift integral is below the drift increment. -/
theorem integral_qfun_seqSol_le (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n) {η : ℝ}
    {n : ℕ} (hn : e n ≤ η) {a b : ℝ≥0} (hab : a ≤ b) :
    ∫ s in (a : ℝ)..b, qfun c η (seqSol c x e w n s.toNNReal)
      ≤ seqA c x e w n b - seqA c x e w n a := by
  have hη : 0 < η := (he n).trans_le hn
  rw [seqA_sub hw hc he n a b]
  refine intervalIntegral.integral_mono_on (by exact_mod_cast hab)
    (((continuous_qfun hc hη).comp (continuous_seqSol_real hw hc he n)).intervalIntegrable _ _)
    (intervalIntegrable_regDrift_seqSol hw hc he n _ _) fun s _ => ?_
  rw [regDrift_eq_cut_add_qfun (he n) hn (seqSol c x e w n s.toNNReal)]
  have := mul_nonneg (cut_nonneg η (seqSol c x e w n s.toNNReal))
    (regDrift_nonneg hc (he n) (seqSol c x e w n s.toNNReal))
  linarith

/-- `∫ₐᵇ qfun c η (X s) ds ≤ A_b - A_a`. -/
theorem integral_qfun_limSol_le (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n)
    (hanti : Antitone e) (hlim : Tendsto e atTop (𝓝 0)) {η : ℝ} (hη : 0 < η) {N a b : ℝ≥0}
    (hN : BddAbove (range fun n => seqSol c x e w n N)) (hab : a ≤ b) (hbN : b ≤ N) :
    ∫ s in (a : ℝ)..b, qfun c η (limSol c x e w s.toNNReal)
      ≤ (limSol c x e w b - x - w b) - (limSol c x e w a - x - w a) := by
  have hbdb := bddAbove_seqSol_of_le (x := x) hw hc he hN hbN
  have hbda := bddAbove_seqSol_of_le (x := x) hw hc he hN (hab.trans hbN)
  have hA := (tendsto_seqA hw hc he hanti hbdb).sub (tendsto_seqA hw hc he hanti hbda)
  have hG := tendsto_integral_qfun_seqSol (x := x) hw hc he hanti hη hN hab hbN
  have hev : ∀ᶠ n in atTop, e n ≤ η := hlim.eventually (ge_mem_nhds hη) |>.mono fun n h => h
  exact le_of_tendsto_of_tendsto hG hA (hev.mono fun n hn => integral_qfun_seqSol_le hw hc he hn hab)

theorem measurable_regDrift_zero (c : ℝ) : Measurable (regDrift c 0) := by
  unfold regDrift
  exact measurable_const.div (measurable_id.max measurable_const)

/-- **Integrability of the reciprocal** and `∫ₐᵇ c / max (X s) 0 ds ≤ A_b - A_a`. -/
theorem integral_regDrift_zero_limSol_le (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n)
    (hanti : Antitone e) (hlim : Tendsto e atTop (𝓝 0)) {N a b : ℝ≥0}
    (hN : BddAbove (range fun n => seqSol c x e w n N)) (hab : a ≤ b) (hbN : b ≤ N) :
    IntervalIntegrable (fun s : ℝ => regDrift c 0 (limSol c x e w s.toNNReal)) volume a b ∧
      ∫ s in (a : ℝ)..b, regDrift c 0 (limSol c x e w s.toNNReal)
        ≤ (limSol c x e w b - x - w b) - (limSol c x e w a - x - w a) := by
  set D := (limSol c x e w b - x - w b) - (limSol c x e w a - x - w a)
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  set μ := volume.restrict (Ioc (a : ℝ) b)
  have hXm := measurable_limSol_real (x := x) hw hc he
  set f : ℕ → ℝ → ℝ := fun k s => qfun c (levelSeq k) (limSol c x e w s.toNNReal)
  set F : ℝ → ℝ := fun s => regDrift c 0 (limSol c x e w s.toNNReal)
  have hFm : Measurable F := (measurable_regDrift_zero c).comp hXm
  have hfi : ∀ k, Integrable (f k) μ := fun k =>
    Integrable.of_bound (((continuous_qfun hc (levelSeq_pos k)).measurable.comp
      hXm).aestronglyMeasurable) (c / levelSeq k) (ae_of_all _ fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (qfun_nonneg hc (levelSeq_pos k) _)]
        exact qfun_le hc (levelSeq_pos k) _)
  have hmono : ∀ s, Monotone fun k => f k s := fun s k l hkl =>
    qfun_anti hc (levelSeq_pos l) (levelSeq_anti hkl) _
  have htend : ∀ s, Tendsto (fun k => f k s) atTop (𝓝 (F s)) := fun s =>
    tendsto_qfun_levelSeq _
  have hfD : ∀ k, ∫ s, f k s ∂μ ≤ D := fun k => by
    have := integral_qfun_limSol_le (x := x) hw hc he hanti hlim (levelSeq_pos k) hN hab hbN
    rwa [intervalIntegral.integral_of_le habR] at this
  have hF0 : ∀ s, 0 ≤ F s := fun s => div_nonneg hc (le_max_right _ _)
  have hf0 : ∀ k s, 0 ≤ f k s := fun k s => qfun_nonneg hc (levelSeq_pos k) _
  -- the lintegral of `F` is finite
  have hlin : Tendsto (fun k => ∫⁻ s, ENNReal.ofReal (f k s) ∂μ) atTop
      (𝓝 (∫⁻ s, ENNReal.ofReal (F s) ∂μ)) :=
    lintegral_tendsto_of_tendsto_of_monotone (fun k => (hfi k).aemeasurable.ennreal_ofReal)
      (ae_of_all _ fun s k l hkl => ENNReal.ofReal_le_ofReal (hmono s hkl))
      (ae_of_all _ fun s => (ENNReal.continuous_ofReal.tendsto _).comp (htend s))
  have hlinD : ∫⁻ s, ENNReal.ofReal (F s) ∂μ ≤ ENNReal.ofReal D := by
    refine le_of_tendsto' hlin fun k => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi k) (ae_of_all _ (hf0 k))]
    exact ENNReal.ofReal_le_ofReal (hfD k)
  have hFi : Integrable F μ :=
    ⟨hFm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hF0)).2
      (hlinD.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le habR).2 hFi, ?_⟩
  rw [intervalIntegral.integral_of_le habR]
  have hT := integral_tendsto_of_tendsto_of_monotone hfi hFi (ae_of_all _ hmono)
    (ae_of_all _ htend)
  exact le_of_tendsto' hT hfD

/-- The localized drift integrals converge: `∫₀ᴺ cut η (U n) · b → A_N - ∫₀ᴺ qfun c η (X)`. -/
theorem tendsto_integral_cut_seqSol (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n)
    (hanti : Antitone e) (hlim : Tendsto e atTop (𝓝 0)) {η : ℝ} (hη : 0 < η) {N : ℝ≥0}
    (hN : BddAbove (range fun n => seqSol c x e w n N)) :
    Tendsto (fun n => ∫ s in (0 : ℝ)..N,
        cut η (seqSol c x e w n s.toNNReal) * regDrift c (e n) (seqSol c x e w n s.toNNReal))
      atTop (𝓝 ((limSol c x e w N - x - w N)
        - ∫ s in (0 : ℝ)..N, qfun c η (limSol c x e w s.toNNReal))) := by
  have hA := tendsto_seqA hw hc he hanti hN
  have hG := tendsto_integral_qfun_seqSol (x := x) hw hc he hanti hη hN (by simp : (0 : ℝ≥0) ≤ N) le_rfl
  simp only [NNReal.coe_zero] at hG
  refine (hA.sub hG).congr' ?_
  have hev : ∀ᶠ n in atTop, e n ≤ η := hlim.eventually (ge_mem_nhds hη) |>.mono fun n h => h
  refine hev.mono fun n hn => ?_
  have hsplit : seqA c x e w n N = ∫ s in (0 : ℝ)..N,
      (cut η (seqSol c x e w n s.toNNReal) * regDrift c (e n) (seqSol c x e w n s.toNNReal)
        + qfun c η (seqSol c x e w n s.toNNReal)) := by
    rw [seqA]
    refine intervalIntegral.integral_congr fun s _ => ?_
    exact regDrift_eq_cut_add_qfun (he n) hn _
  have hi1 : IntervalIntegrable (fun s : ℝ =>
      cut η (seqSol c x e w n s.toNNReal) * regDrift c (e n) (seqSol c x e w n s.toNNReal))
      volume 0 N :=
    (((continuous_cut η).comp (continuous_seqSol_real hw hc he n)).mul
      ((continuous_regDrift hc (he n)).comp (continuous_seqSol_real hw hc he n))).intervalIntegrable
      _ _
  have hi2 : IntervalIntegrable (fun s : ℝ => qfun c η (seqSol c x e w n s.toNNReal)) volume 0 N :=
    ((continuous_qfun hc hη).comp (continuous_seqSol_real hw hc he n)).intervalIntegrable _ _
  dsimp only
  rw [hsplit, intervalIntegral.integral_add hi1 hi2]
  ring

end Bessel

end InteractingSLE
