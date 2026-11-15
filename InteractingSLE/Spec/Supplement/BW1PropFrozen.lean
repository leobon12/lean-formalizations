/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1PropTip
import InteractingSLE.Spec.Supplement.Q3KernelNoReturn
import InteractingSLE.Foundations.Loewner.TraceClose

/-!
# Proposition BW1: the piece frozen at its lifetime, and BW1's retained chart

Packet PROVE-BW1-PROP. Proposition BW1 retains the *whole completed* piece `A = α[0, σ]` up to its lifetime `σ`, where
the trace ends on `ℝ` at `q` (supplement p. 614: "Work with the first contact with the whole completed set `A`"). The
landed GB6 machinery (`Q3Rel`, `Q3Kernel`, `GB6Glue`) works with a globally continuous driver `U` with a global Loewner
trace, obtained there by freezing the flow driver strictly after the stop (`IsLoewnerTraceLT.isLoewnerTrace_ext` needs a
horizon beyond the freezing time). At a threshold the stop is the horizon itself, so the extension must be closed at
the horizon:

* **`isLoewnerTrace_ext_close`**: a Loewner trace before `σ` that is continuous on `[0, σ]` (driver continuous on `ℝ`)
  extends, with the driver frozen at `σ` and the trace continued by the image of the vertical slit, to a global
  continuous Loewner trace (the trace closure at the horizon, `TraceClose`, replaces the horizon `T > σ` of the open
  version; the proof is the one of `YuanCorollary13Finite` with these inputs);
* **`exists_frozen_trace_close`**: in the staged form — a generating trace of a piece on `[0, σ]`, with the driver
  continuous on `[0, σ]`, gives a global Loewner trace of the driver stopped at `σ`, equal to the piece's trace on
  `[0, σ]`;
* **`isRetainedChartOff_close`**: BW1's retained chart — for such a piece not returning to `0` on `(0, σ]`,
  `(relMap U σ, relInv U σ, relLog U σ)` is an `IsRetainedChartOff` of `invHull U σ` (the piece in the counterflow's
  frame `w = −1/z`) landing off `relBad U σ` (`Q3Rel.isRetainedChartOff_relMap`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.BW1Prop

open YuanCorollary13

/-! ### The slit extension closed at the horizon -/

section Close

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {σ : ℝ}

/-- The slit extension at the horizon is continuous on `[0, ∞)`. -/
theorem continuousOn_extTrace_close (hη : IsLoewnerTraceLT W σ η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hσ : 0 < σ) (hησ : ContinuousOn η (Icc 0 σ)) : ContinuousOn (extTrace W η σ) (Ici 0) := by
  have hFbc : ContinuousOn (extendFrom H (fwdMapInv W σ)) Hbar :=
    (TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη hW hW0 hσ hησ).continuousOn
  have hFb0 := TraceClose.extendFrom_zero_eq hη hW hW0 hσ hησ
  have hg : Continuous fun t : ℝ =>
      extendFrom H (fwdMapInv W σ) (((2 * Real.sqrt (t - σ) : ℝ) : ℂ) * I) := by
    refine hFbc.comp_continuous (by fun_prop) fun t => ?_
    show 0 ≤ (((2 * Real.sqrt (t - σ) : ℝ) : ℂ) * I).im
    simp [Real.sqrt_nonneg]
  refine ContinuousOn.if (fun t ht => ?_) ?_ hg.continuousOn
  · have hfr : frontier {t : ℝ | t ≤ σ} = {σ} := by
      rw [show {t : ℝ | t ≤ σ} = Iic σ from rfl, frontier_Iic]
    rw [hfr] at ht
    rw [mem_singleton_iff.1 ht.2, sub_self, Real.sqrt_zero, mul_zero, ofReal_zero, zero_mul, hFb0]
  · refine hησ.mono ?_
    rintro t ⟨ht0, ht⟩
    rw [show {t : ℝ | t ≤ σ} = Iic σ from rfl, closure_Iic] at ht
    exact ⟨ht0, ht⟩

/-- Hulls of the extension up to and including the horizon. -/
theorem fwdHull_extDrive_of_le_close (hη : IsLoewnerTraceLT W σ η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hσ : 0 < σ) (hησ : ContinuousOn η (Icc 0 σ)) {t : ℝ} (ht : 0 ≤ t) (htσ : t ≤ σ) :
    fwdHull (extDrive W σ) t = fillH (extTrace W η σ '' Icc 0 t) := by
  have hK : fwdHull W t = fillH (η '' Icc 0 t) := by
    rcases htσ.lt_or_eq with hlt | heq
    · exact hη.2.2 t ht hlt
    · rw [heq]
      exact TraceClose.fwdHull_eq_fillH_of_isLoewnerTraceLT hη hW hW0 hσ hησ
  rw [fwdHull_eq_of_eqOn_Icc (continuous_extDrive hW) hW ht fun r hr => extDrive_eq (hr.2.trans htσ), hK]
  congr 1
  exact (Set.EqOn.image_eq fun r hr => extTrace_eq (hr.2.trans htσ)).symm

theorem fillH_extTrace_add_close (hη : IsLoewnerTraceLT W σ η)
    (hW : Continuous W) (hW0 : W 0 = 0) (hσ : 0 < σ) (hησ : ContinuousOn η (Icc 0 σ)) {u : ℝ} (hu : 0 ≤ u) :
    fillH (extTrace W η σ '' Icc 0 (σ + u)) = fwdHull W σ ∪ fwdMapInv W σ '' slitSet u := by
  set P := extTrace W η σ '' Icc 0 (σ + u) with hP
  set A := η '' Icc 0 σ with hA
  set F := fwdMapInv W σ with hF
  set K := fwdHull W σ with hKdef
  have hKA : K = fillH A := TraceClose.fwdHull_eq_fillH_of_isLoewnerTraceLT hη hW hW0 hσ hησ
  have hFb0 := TraceClose.extendFrom_zero_eq hη hW hW0 hσ hησ
  have hcb := isConformalBijection_fwdMapInv hW hW0 hσ.le
  have hFeq : ∀ w ∈ H, extendFrom H F w = F w := fun w hw =>
    extendFrom_H_eq hcb.1.continuousOn hw
  have hPc : IsCompact P := isCompact_Icc.image_of_continuousOn
    ((continuousOn_extTrace_close hη hW hW0 hσ hησ).mono fun t ht => ht.1)
  have hAP : A ⊆ P := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ⟨ht.1, by linarith [ht.2]⟩, extTrace_eq ht.2⟩
  have hSP : F '' slitSet u ⊆ P := by
    rintro _ ⟨w, hw, rfl⟩
    have hw0 : 0 < w.im := hw.1
    have hwI : w = ((w.im : ℝ) : ℂ) * I := Complex.ext (by simp [hw.2.1]) (by simp)
    have hle : w.im ^ 2 / 4 ≤ u := by
      have h1 : w.im ^ 2 ≤ (2 * Real.sqrt u) ^ 2 := pow_le_pow_left₀ hw0.le hw.2.2 2
      rw [mul_pow, Real.sq_sqrt hu] at h1
      linarith
    refine ⟨σ + w.im ^ 2 / 4, ⟨by positivity, by linarith⟩, ?_⟩
    have hgt : ¬ (σ + w.im ^ 2 / 4 ≤ σ) := by
      have : 0 < w.im ^ 2 / 4 := by positivity
      linarith
    simp only [extTrace, hgt, ite_false, add_sub_cancel_left]
    have hsq : 2 * Real.sqrt (w.im ^ 2 / 4) = w.im := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_sq hw0.le,
        show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      ring
    rw [hsq, ← hwI]
    exact hFeq w hw.1
  -- the points of `P`
  have hPsub : ∀ v ∈ P, v ∈ A ∨ ∃ y : ℝ, 0 ≤ y ∧ y ≤ 2 * Real.sqrt u ∧
      v = extendFrom H F ((y : ℂ) * I) := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases htσ : t ≤ σ
    · exact Or.inl ⟨t, ⟨ht.1, htσ⟩, (extTrace_eq htσ).symm⟩
    · refine Or.inr ⟨2 * Real.sqrt (t - σ), by positivity, ?_, ?_⟩
      · gcongr; linarith [ht.2]
      · simp only [extTrace, htσ, ite_false]
        rfl
  -- `P` is disjoint from `F(ℍ \ S_u)`
  have hAK : ∀ v ∈ A, v ∈ H → v ∈ K := fun v hv hvH => by
    rw [hKA]; exact ⟨hvH, Or.inl (subset_closure hv)⟩
  have hdisj : F '' (H \ slitSet u) ⊆ H \ closure P := by
    rintro _ ⟨w, hw, rfl⟩
    have hFw := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hσ.le hw.1
    refine ⟨hFw.1, fun hcl => ?_⟩
    rw [hPc.isClosed.closure_eq] at hcl
    rcases hPsub _ hcl with hA' | ⟨y, hy0, hyu, hyv⟩
    · exact hFw.2 (hAK _ hA' hFw.1)
    · rcases hy0.eq_or_lt with hy | hy
      · rw [← hy, ofReal_zero, zero_mul, hFb0] at hyv
        have hmemA : F w ∈ A := by rw [hyv]; exact ⟨σ, ⟨hσ.le, le_rfl⟩, rfl⟩
        exact hFw.2 (hAK _ hmemA hFw.1)
      · have hyH : (y : ℂ) * I ∈ H := show 0 < ((y : ℂ) * I).im by simpa using hy
        rw [hFeq _ hyH] at hyv
        have := hcb.2.injOn hw.1 hyH hyv
        exact hw.2 (this ▸ ⟨hyH, by simp, by simpa using hyu⟩)
  -- `F(ℍ \ S_u)` is preconnected and unbounded
  have hEc : IsPreconnected (F '' (H \ slitSet u)) :=
    (isPreconnected_H_diff_slitSet u).image _ (hcb.1.continuousOn.mono sdiff_subset)
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hσ.le
  have hEb : ¬ Bornology.IsBounded (F '' (H \ slitSet u)) := by
    intro hb
    obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    set y : ℝ := 2 * Real.sqrt u + |R| + |C| + 1 with hy
    have hy0 : 0 < y := by positivity
    have hyH : (y : ℂ) * I ∈ H := show 0 < ((y : ℂ) * I).im by simpa using hy0
    have hyS : (y : ℂ) * I ∉ slitSet u := fun h => by
      have := h.2.2
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at this
      linarith [abs_nonneg R, abs_nonneg C]
    have h1 := hR ⟨_, ⟨hyH, hyS⟩, rfl⟩
    rw [mem_closedBall, dist_zero_right] at h1
    have h2 : ‖F ((y : ℂ) * I) - (y : ℂ) * I‖ ≤ C := hC _ hyH
    have h3 : ‖(y : ℂ) * I‖ = y := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
    have h4 := norm_le_norm_add_norm_sub' ((y : ℂ) * I) (F ((y : ℂ) * I))
    rw [norm_sub_rev] at h4
    rw [h3] at h4
    linarith [le_abs_self R, le_abs_self C, Real.sqrt_nonneg u]
  have hEsub := subset_H_diff_fillH_of_isPreconnected hPc.isBounded hEc hdisj hEb
  apply Subset.antisymm
  · intro z hz
    by_contra hcon
    have hzH : z ∈ H := hz.1
    have hzK : z ∉ K := fun h => hcon (Or.inl h)
    have hzD : z ∈ H \ K := ⟨hzH, hzK⟩
    have hGz := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hσ.le hzD
    have hFG : F (fwdMap W σ z) = z := QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hσ.le hzD
    by_cases hS : fwdMap W σ z ∈ slitSet u
    · exact hcon (Or.inr ⟨_, hS, hFG⟩)
    · exact (hEsub ⟨_, ⟨hGz, hS⟩, hFG⟩).2 hz
  · rintro z (hz | hz)
    · rw [hKA] at hz
      exact fillH_mono hAP hz
    · obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨(QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hσ.le hw.1).1,
        Or.inl (subset_closure (hSP ⟨w, hw, rfl⟩))⟩


/-- **The slit extension at the horizon is a continuous Loewner trace** of the driver frozen at the horizon. -/
theorem isLoewnerTrace_ext_close (hη : IsLoewnerTraceLT W σ η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hσ : 0 < σ) (hησ : ContinuousOn η (Icc 0 σ)) :
    IsLoewnerTrace (extDrive W σ) (extTrace W η σ) := by
  refine ⟨by rw [extTrace_eq hσ.le, hη.1], continuousOn_extTrace_close hη hW hW0 hσ hησ, fun t ht => ?_⟩
  by_cases htσ : t ≤ σ
  · exact fwdHull_extDrive_of_le_close hη hW hW0 hσ hησ ht htσ
  · have hu : 0 ≤ t - σ := by linarith [not_le.1 htσ]
    have ht' : t = σ + (t - σ) := by ring
    rw [ht', fwdHull_extDrive_add hW hW0 hσ.le hu, fillH_extTrace_add_close hη hW hW0 hσ hησ hu]

end Close

/-! ### The piece frozen at its lifetime -/

section Staged

variable {w : ℝ≥0 → ℝ} {S : ℝ≥0} {α : ℝ≥0 → ℂ}

/-- The driver stopped at `S`, read on `ℝ`, is frozen after `S`. -/
theorem extDrive_stopped (r : ℝ) :
    extDrive (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) S r =
      w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal := by
  simp only [extDrive]
  by_cases hr : r ≤ S
  · rw [min_eq_left hr]
  · push Not at hr
    have hS : (S : ℝ≥0∞) ≤ ((r.toNNReal : ℝ≥0) : ℝ≥0∞) :=
      ENNReal.coe_le_coe.2 (Real.le_toNNReal_iff_coe_le (S.2.trans hr.le) |>.2 hr.le)
    rw [min_eq_right hr.le, Real.toNNReal_coe, min_self, min_eq_right hS]

/-- **A finite piece frozen at its stop has a global Loewner trace**: a generating trace on `[0, S]` (`S > 0`) of a
driver continuous on `[0, S]` from `0` gives a continuous Loewner trace on `[0, ∞)` of the driver stopped at `S`, equal
to the piece's trace on `[0, S]`. -/
theorem exists_frozen_trace_close (hα : IsGeneratingTrace w S α) (hw : ContinuousOn w {t | (t : ℝ≥0∞) ≤ S})
    (hw0 : w 0 = 0) (hS : 0 < S) :
    ∃ αr : ℝ → ℂ, IsLoewnerTrace (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) αr ∧
      ∀ r ∈ Icc (0 : ℝ) S, αr r = α r.toNNReal := by
  set U : ℝ → ℝ := fun r => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal with hUdef
  have hUc : Continuous U := (CounterflowRange.continuous_stopped hw).comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by
    show w (min (((0 : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal = 0
    rw [Real.toNNReal_zero, CounterflowRange.stopped_eq_of_lt (W := w) (t := 0) (by simp)]
    exact hw0
  have hη := CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace (CounterflowRange.isGeneratingTrace_stopped hα)
  have hησ : ContinuousOn (fun s : ℝ => α s.toNNReal) (Icc 0 (S : ℝ)) :=
    hα.2.1.comp continuous_real_toNNReal.continuousOn fun s hs =>
      ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
  have hext := isLoewnerTrace_ext_close hη hUc hU0 (NNReal.coe_pos.2 hS) hησ
  have hUe : extDrive U S = U := funext extDrive_stopped
  rw [hUe] at hext
  exact ⟨_, hext, fun r hr => extTrace_eq hr.2⟩

/-- **BW1's retained chart.** For a finite piece (generating trace on `[0, S]`, driver continuous on `[0, S]` from
`0`, `S > 0`) whose trace does not return to `0` on `(0, S]`, the driver `U` stopped at `S` has a global Loewner
trace agreeing with the piece on `[0, S]`, and GB6's relative chart of the completed piece in the counterflow's frame,
`(relMap U S, relInv U S, relLog U S)` on `invHull U S`, is a retained chart landing off `relBad U S`. -/
theorem isRetainedChartOff_close (hα : IsGeneratingTrace w S α) (hw : ContinuousOn w {t | (t : ℝ≥0∞) ≤ S})
    (hw0 : w 0 = 0) (hS : 0 < S) (hNR : ∀ v : ℝ≥0, 0 < v → v ≤ S → α v ≠ 0) :
    ∃ αr : ℝ → ℂ, IsLoewnerTrace (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) αr ∧
      (∀ r ∈ Icc (0 : ℝ) S, αr r = α r.toNNReal) ∧
      Supp8.Q3Rel.IsRetainedChartOff
        (Supp8.Q3Rel.invHull (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) S)
        (Supp8.GB6.relMap (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) S)
        (Supp8.GB6.relInv (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) S)
        (Supp8.Q3Rel.relLog (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) S)
        (Supp8.Q3Rel.relBad (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) S) := by
  obtain ⟨αr, hαr, hαeq⟩ := exists_frozen_trace_close hα hw hw0 hS
  have hUc : Continuous fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal :=
    (CounterflowRange.continuous_stopped hw).comp continuous_real_toNNReal
  have hU0 : (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) 0 = 0 := by
    show w (min (((0 : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal = 0
    rw [Real.toNNReal_zero, CounterflowRange.stopped_eq_of_lt (W := w) (t := 0) (by simp)]
    exact hw0
  have hNR' : ∀ v ∈ Ioc (0 : ℝ) S, αr v ≠ 0 := fun v hv => by
    rw [hαeq v ⟨hv.1.le, hv.2⟩]
    refine hNR v.toNNReal (Real.toNNReal_pos.2 hv.1) ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hv.1.le]
    exact hv.2
  exact ⟨αr, hαr, hαeq, Supp8.Q3Rel.isRetainedChartOff_relMap hUc hU0 hαr (by exact_mod_cast hS) hNR'⟩

end Staged

end InteractingSLE.Theorem14.BW1Prop
