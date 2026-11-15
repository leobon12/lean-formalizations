/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketTraversalErase
import InteractingSLE.Spec.Sec6.DrivingUnconditional
import InteractingSLE.Foundations.Loewner.YuanCorollary13Finite
import InteractingSLE.Foundations.Loewner.Concat

/-!
# SB2's relative chain: the Loewner chain of a lifted simple curve up to a stop

Packet PROVE-T14-SB2FIN. Lemma SB2 (supplement pp. 630–633, `source/spec/p625-671.md` L113–L150): "the later tail lies
in `closure D_A` with the unique lift selected by its free one-sided collar. In the first assertion this is the
injective, proper lift of the witness […] On every ordinary piece the strict angle comparison excludes a common open
arc with the other history […] An original-real open arc cannot belong to an ordinary flow. Consequently the relative
capacity is continuous and strictly increasing on each retained ordinary piece."

Lemma S2's lift (`SB.s2LiftStatement`) is a proper continuous injective curve `γ` in `closure ℍ` from `0`. If its
real-boundary times have empty interior on `(0, S)` (no open real arc before `S`; the source's no-common-arc and
no-real-arc facts), then:

* `exists_localDriver_of_lt`: on every `[0, S']`, `S' ≤ S`, the capacity clock `capClock γ` is the continuous strictly
  increasing clock of a continuous driver whose hulls are the filled prefixes (Proposition 6.12 for simple paths;
  criterion (b) needs the real times only before `S'`);
* `isDrivenCurve_relCurve_of_lt`: the reparametrization `relCurve γ S` of `γ` on `[0, S)` is a driven curve;
* **`exists_relChain`**: for every stop `S₀ < S` there are a globally continuous driver `Wr` from `0` and a global
  continuous Loewner trace `ηr` of it (the canonical driver, frozen after the relative stop `capClock γ S₀`, with its
  slit continuation) such that, at the relative capacity times `capClock γ s`, `s ≤ S₀`, the trace is at `γ s` and the
  Loewner hull is the filled prefix `fill γ([0, s])`. The relative clock `capClock γ` is `0` at `0`, continuous and
  strictly increasing on `[0, S₀]`.

These are the fields `hWr`, `hWr0`, `hηr` of `SB.Union.IsRelConfigJ` and the hull identity used for `hullIn`/`hullFr`
(`SB2FinHull`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.SB.FinRel

open Sec7.Lemma71C Sec7.PocketTraversal

variable {γ : ℝ → ℂ}

/-! ### Local drivers before the first open real arc -/

/-- **Local drivers of a simple proper curve before `S`** (Proposition 6.12 for simple paths): if `γ` is continuous,
injective, in `closure ℍ` on `[0, ∞)`, starts at `0`, tends to `∞`, and its real-boundary times in `(0, S)` have
empty interior, then on every `[0, S']`, `0 < S' ≤ S`, the capacity clock is the clock of a continuous driver. -/
theorem exists_localDriver_of_lt (hc : ContinuousOn γ (Ici 0)) (hinj : InjOn γ (Ici 0)) (hH : MapsTo γ (Ici 0) Hbar)
    (h0 : γ 0 = 0) (hinf : Tendsto (fun t => ‖γ t‖) atTop atTop) {S : ℝ}
    (hR : interior {u ∈ Ioo (0 : ℝ) S | (γ u).im = 0} = ∅) {S' : ℝ} (hS' : 0 < S') (hS'S : S' ≤ S) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ capClock γ 0 = 0 ∧ StrictMonoOn (capClock γ) (Icc 0 S') ∧
      ContinuousOn (capClock γ) (Icc 0 S') ∧
      ∀ t ∈ Icc 0 S', 0 ≤ capClock γ t ∧ fwdHull W (capClock γ t) = fillH (γ '' Icc 0 t) := by
  have hsub : Icc 0 S' ⊆ Ici (0 : ℝ) := Icc_subset_Ici_self
  have hA := Sec6.drivingCriterionA_of_injOn ordConnected_Ici hc hinj hH self_mem_Ici
    (Sec7.Lemma71.not_isBounded_image_Ici hinf) hsub
  have hB := Sec6.drivingCriterionB_of_injOn (S := S') (hinj.mono hsub) (subset_empty_iff.1 (hR ▸ interior_mono
    (fun u hu => ⟨⟨hu.1.1, lt_of_lt_of_le hu.1.2 hS'S⟩, hu.2⟩)))
  have hS := Sec6.hasSimpleApproxOn_of_injOn hS' (hc.mono hsub) (hinj.mono hsub) h0 (hH.mono_left hsub)
  obtain ⟨W, hW, hW0, σ, hσ0, hσm, hσc, hσ⟩ := Sec6.exists_driver_of_drivingCriteria hS' (hc.mono hsub) h0 hS hA hB
  have heq : EqOn σ (capClock γ) (Icc 0 S') := fun t ht => by
    obtain ⟨hσt, hK, -⟩ := hσ t ht
    have := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hW hW0 hσt hK
    simp only [capClock, this]
    ring
  refine ⟨W, hW, hW0, ?_, hσm.congr heq, hσc.congr heq.symm, fun t ht => ?_⟩
  · rw [← heq ⟨le_rfl, hS'.le⟩, hσ0]
  · rw [← heq ht]
    exact ⟨(hσ t ht).1, (hσ t ht).2.1⟩

/-- **The reparametrized curve on `[0, S)` is driven.** -/
theorem isDrivenCurve_relCurve_of_lt (hc : ContinuousOn γ (Ici 0)) (hinj : InjOn γ (Ici 0))
    (hH : MapsTo γ (Ici 0) Hbar) (h0 : γ 0 = 0) (hinf : Tendsto (fun t => ‖γ t‖) atTop atTop) {S : ℝ} (hS : 0 < S)
    (hR : interior {u ∈ Ioo (0 : ℝ) S | (γ u).im = 0} = ∅) : IsDrivenCurve (relCurve γ S) := by
  refine isDrivenCurve_relCurve hS (hc.mono Ico_subset_Ici_self) h0 fun S' hS' hS'S => ?_
  obtain ⟨W, hW, hW0, hc0, hm, hcc, hK⟩ := exists_localDriver_of_lt hc hinj hH h0 hinf hR hS' hS'S.le
  exact ⟨W, hW, hW0, capClock γ, hc0, hm, hcc, fun t ht => (hK t ht).2⟩

/-- The capacity clock of the reparametrized curve is the capacity clock of `γ` at the reparametrized time. -/
theorem capClock_relCurve {S : ℝ} (hS : 0 < S) {u : ℝ} (hu : 0 ≤ u) :
    capClock (relCurve γ S) u = capClock γ (clockOf S u) := by
  simp only [capClock, image_relCurve_Icc γ hS hu]

/-- The reparametrization hits every time of `[0, S)`. -/
theorem clockOf_inv {S s : ℝ} (hs : s ∈ Ico 0 S) : clockOf S (s / (S - s)) = s := by
  have hLv : 0 < S - s := by linarith [hs.2]
  have hS0 : S ≠ 0 := (show (0 : ℝ) < S by linarith [hs.1, hs.2]).ne'
  simp only [clockOf]
  have h1 : 1 + s / (S - s) = S / (S - s) := by field_simp; ring
  rw [h1]
  field_simp

theorem inv_clockOf_nonneg {S s : ℝ} (hs : s ∈ Ico 0 S) : 0 ≤ s / (S - s) :=
  div_nonneg hs.1 (by linarith [hs.2])

/-! ### The frozen relative chain -/

/-- A driver continuous on `(−∞, T]` frozen after `T` is continuous. -/
theorem continuous_extDrive_of_continuousOn {W : ℝ → ℝ} {T : ℝ} (hW : ContinuousOn W (Iic T)) :
    Continuous (YuanCorollary13.extDrive W T) :=
  hW.comp_continuous (continuous_id.min continuous_const) fun t => min_le_right t T

/-- The canonical driver of a driven curve, read on real times, is continuous below the terminal capacity time. -/
theorem continuousOn_rpath_segDriver {ζ : ℝ → ℂ} (hζ : IsDrivenCurve ζ) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < capLife ζ) :
    ContinuousOn (Ito.rpath (segDriver ζ)) (Iic (T : ℝ)) := by
  have hc := hζ.segDriver_spec.2.1
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < capLife ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  intro t ht
  have hlt : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < capLife ζ :=
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 ht)) hT
  have hca : ContinuousAt (segDriver ζ) t.toNNReal := (hc _ hlt).continuousAt (hopen.mem_nhds hlt)
  exact (hca.comp continuous_real_toNNReal.continuousAt).continuousWithinAt

/-- **SB2's relative chain** (Lemma SB2, p. 631: "the relative capacity is continuous and strictly increasing on each
retained ordinary piece"): let `γ` be a simple proper curve in `closure ℍ` from `0` (S2's lift, read on real times)
whose real-boundary times have empty interior on `(0, S)`. For every stop `S₀ < S` there are a continuous driver
`Wr` from `0` and a continuous Loewner trace `ηr` of it on `[0, ∞)` such that, at every relative capacity time
`capClock γ s`, `0 ≤ s ≤ S₀`, the trace is at `γ s` and the hull is the filled prefix `fill γ([0, s])`; the relative
clock `capClock γ` starts at `0` and is continuous and strictly increasing on `[0, S₀]`. -/
theorem exists_relChain (hc : ContinuousOn γ (Ici 0)) (hinj : InjOn γ (Ici 0)) (hH : MapsTo γ (Ici 0) Hbar)
    (h0 : γ 0 = 0) (hinf : Tendsto (fun t => ‖γ t‖) atTop atTop) {S : ℝ} (hS : 0 < S)
    (hR : interior {u ∈ Ioo (0 : ℝ) S | (γ u).im = 0} = ∅) {S₀ : ℝ} (hS₀ : 0 ≤ S₀) (hS₀S : S₀ < S) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
      capClock γ 0 = 0 ∧ StrictMonoOn (capClock γ) (Icc 0 S₀) ∧ ContinuousOn (capClock γ) (Icc 0 S₀) ∧
      ∀ s ∈ Icc 0 S₀, 0 ≤ capClock γ s ∧ ηr (capClock γ s) = γ s ∧
        fwdHull Wr (capClock γ s) = fillH (γ '' Icc 0 s) := by
  obtain ⟨W₁, -, -, hc0, hcm, hcc, hcK⟩ := exists_localDriver_of_lt hc hinj hH h0 hinf hR hS le_rfl
  have hsub : Icc 0 S₀ ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS₀S.le
  set γr := relCurve γ S with hγrdef
  have hγr : IsDrivenCurve γr := isDrivenCurve_relCurve_of_lt hc hinj hH h0 hinf hS hR
  -- the relative times of the lift parameters
  have hrel : ∀ s ∈ Icc 0 S₀, capClock γ s = capClock γr (s / (S - s)) ∧ 0 ≤ s / (S - s) ∧
      clockOf S (s / (S - s)) = s := fun s hs => by
    have hsI : s ∈ Ico 0 S := ⟨hs.1, lt_of_le_of_lt hs.2 hS₀S⟩
    refine ⟨?_, inv_clockOf_nonneg hsI, clockOf_inv hsI⟩
    rw [hγrdef, capClock_relCurve hS (inv_clockOf_nonneg hsI), clockOf_inv hsI]
  obtain ⟨hT₀e, hu₀, -⟩ := hrel S₀ ⟨hS₀, le_rfl⟩
  set u₀ := S₀ / (S - S₀)
  set T₀ := capClock γ S₀ with hT₀def
  have hT₀0 : 0 ≤ T₀ := (hcK S₀ ⟨hS₀, hS₀S.le⟩).1
  -- a horizon beyond the stop, below the terminal capacity time
  set T₁ : ℝ≥0 := (capClock γr (u₀ + 1)).toNNReal with hT₁def
  have hT₁r : (T₁ : ℝ) = capClock γr (u₀ + 1) := Real.coe_toNNReal _ (hγr.capClock_nonneg (by linarith))
  have hT₁ : (T₁ : ℝ≥0∞) < capLife γr := hγr.ofReal_capClock_lt (by linarith)
  have hT₀T₁ : T₀ < T₁ := by
    rw [hT₁r, hT₀e]
    exact hγr.strictMonoOn_capClock hu₀ (show (0 : ℝ) ≤ u₀ + 1 by linarith) (by linarith)
  have hgen := hγr.isGeneratingTrace hT₁
  have hLT := LoewnerConcat.isLoewnerTraceLT_prefix hgen
  -- freeze the driver at the horizon
  set W' := YuanCorollary13.extDrive (Ito.rpath (segDriver γr)) T₁ with hW'def
  have hW'c : Continuous W' := continuous_extDrive_of_continuousOn (continuousOn_rpath_segDriver hγr hT₁)
  have hW'0 : W' 0 = 0 := by
    rw [hW'def, YuanCorollary13.extDrive_eq (NNReal.coe_nonneg T₁)]
    simp only [Ito.rpath, Real.toNNReal_zero]
    exact hγr.segDriver_spec.1
  set η := fun t : ℝ => capTrace γr t.toNNReal with hηdef
  have hLT' : IsLoewnerTraceLT W' T₁ η := by
    refine ⟨hLT.1, hLT.2.1, fun t ht htT => ?_⟩
    rw [← hLT.2.2 t ht htT]
    exact fwdHull_eq_of_eqOn ht htT fun r hr => YuanCorollary13.extDrive_eq hr.2
  have hext := hLT'.isLoewnerTrace_ext hW'c hW'0 hT₀0 hT₀T₁
  refine ⟨YuanCorollary13.extDrive W' T₀, YuanCorollary13.extTrace W' η T₀, YuanCorollary13.continuous_extDrive hW'c,
    YuanCorollary13.extDrive_zero hW'0 hT₀0, hext, hc0, hcm.mono hsub, hcc.mono hsub, fun s hs => ?_⟩
  obtain ⟨hse, hu, hcl⟩ := hrel s hs
  have ha0 : 0 ≤ capClock γ s := (hcK s (hsub hs)).1
  have haT₀ : capClock γ s ≤ T₀ := hcm.monotoneOn (hsub hs) ⟨hS₀, hS₀S.le⟩ hs.2
  have hlife : ((capClock γ s).toNNReal : ℝ≥0∞) < capLife γr := by
    rw [hse]
    exact hγr.ofReal_capClock_lt hu
  have hinv : capInv γr (capClock γ s) = s / (S - s) := by rw [hse, hγr.capInv_eq hu]
  have himg : YuanCorollary13.extTrace W' η T₀ '' Icc 0 (capClock γ s) = γ '' Icc 0 s := by
    rw [(Set.EqOn.image_eq fun r hr => YuanCorollary13.extTrace_eq (hr.2.trans haT₀)), hηdef,
      image_toNNReal_Icc (capTrace γr) ha0, hγr.image_capTrace hlife, Real.coe_toNNReal _ ha0, hinv, hγrdef,
      image_relCurve_Icc γ hS hu, hcl]
  refine ⟨ha0, ?_, by rw [hext.2.2 _ ha0, himg]⟩
  rw [YuanCorollary13.extTrace_eq haT₀]
  show capTrace γr (capClock γ s).toNNReal = γ s
  rw [capTrace, Real.coe_toNNReal _ ha0, hinv]
  show γ (clockOf S (s / (S - s))) = γ s
  rw [hcl]

/-! ### The physical chain through a time before the lifetime -/

/-- **A global Loewner trace through a time before the lifetime** (the fields `hw`, `hw0`, `hη` of
`SB.Union.IsRelConfigJ` for the physical flow): if `η` is a continuous generating trace of `w` on `[0, T]` (the frozen
`IsGeneratingTrace`, e.g. `η - x` for a flow line from `x`) and `w` is continuous before `T`, then for every `t ≥ 0`
with `t < T` there are a continuous driver `W` from `0` and a continuous Loewner trace `η'` of it on `[0, ∞)` that
agree with `w`, `η` on `[0, t]`; the hull at `t` is the filled prefix `fill η([0, t])`. -/
theorem exists_globalTrace_of_isGeneratingTrace {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w T η) (hw : ContinuousOn w {s : ℝ≥0 | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) (htT : ENNReal.ofReal t < T) :
    ∃ (W : ℝ → ℝ) (η' : ℝ → ℂ), Continuous W ∧ W 0 = 0 ∧ IsLoewnerTrace W η' ∧
      (∀ r ∈ Icc (0 : ℝ) t, W r = w r.toNNReal ∧ η' r = η r.toNNReal) ∧
      fwdHull W t = fillH (η '' Icc 0 t.toNNReal) := by
  obtain ⟨r, hr0, htr, hrT⟩ := ENNReal.lt_iff_exists_real_btwn.1 htT
  have htr' : t < r := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).1 htr
  have hLT := hη.isLoewnerTraceLT hrT
  have hWc : Continuous (frozenDrive w r) := continuous_frozenDrive (hw.mono fun s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) (by rwa [ENNReal.ofReal] at hrT))
  have hW0 : frozenDrive w r 0 = 0 := by rw [frozenDrive_zero hr0, hw0]
  have hext := hLT.isLoewnerTrace_ext hWc hW0 ht htr'
  refine ⟨YuanCorollary13.extDrive (frozenDrive w r) t, YuanCorollary13.extTrace (frozenDrive w r)
    (fun s : ℝ => η s.toNNReal) t, YuanCorollary13.continuous_extDrive hWc,
    YuanCorollary13.extDrive_zero hW0 ht, hext, fun r' hr' => ⟨?_, YuanCorollary13.extTrace_eq hr'.2⟩, ?_⟩
  · rw [YuanCorollary13.extDrive_eq hr'.2, frozenDrive_eq ⟨hr'.1, hr'.2.trans htr'.le⟩]
  · rw [hext.2.2 t ht, Set.EqOn.image_eq fun r' hr' => YuanCorollary13.extTrace_eq hr'.2,
      image_toNNReal_Icc η ht]

end InteractingSLE.Theorem14.SB.FinRel
