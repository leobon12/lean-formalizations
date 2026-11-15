/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowLocalityGenSetting

/-!
# Flow locality with a general agreement set: the regularized clock

Packet PROVE-G7A-LOC. The positive clock of the general setting. Its source side (measurable exit, frozen driver,
announcements, path data) is the proved clock of the trivial comparison `GSetting.toFake`
(`FlowStopIdentCMI.cmiVPositiveClockStatement`); the reference side (threshold bound and reference
announcements of the `bR` word) is re-proved here — the CMI proofs use the interval only through the geometric
images of the source marks, which `stopPathData_det` gives for the trivial interval of the fake setting.

* `GSetting.threshold_of_agree`, `GSetting.exists_reference_announce`;
* `GClock`, **`GSetting.exists_clock`** (no input);
* `GClock.driving_le`, `GClock.ae_pos`, `GClock.seed_mem`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowLocalityGen
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open Sec7.PocketTraversal
open FlowStopIdentCMI FlowStopIdentLL StoppedExtend

namespace GSetting
variable {S : Type u} [MeasurableSpace S] (D : GSetting S)

/-- A continuous driver agreeing before the exit cannot meet the reference
word's continuation threshold earlier. This discharges the clock's threshold field. -/
theorem threshold_of_agree {e : S → ℝ≥0∞} {W : ℝ≥0 → S → ℝ}
    (he : e =ᵐ[D.Q₀] fun ω => RLC.exitTime D.V (D.Γ ω) (D.U ω))
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous (W · ω))
    (hag : ∀ᵐ ω ∂D.Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W t ω = D.W₀ t ω) :
    ∀ᵐ ω ∂D.Q₀, e ω ≤ MartChar.thresholdTime
      (flowLineRhoL D.κ D.bR D.JR D.y D.θ) (flowLineRhoR D.κ D.bR D.JR D.y D.θ) (W · ω)
      (fun i t => geomLW W (fun _ => flowLineXL D.bR D.JR D.y) i t ω)
      (fun j t => geomRW W (fun _ => flowLineXR D.bR D.JR D.y) j t ω) := by
  classical
  filter_upwards [he, hag, D.coupling.1.ae_isIntegratedSLEPath, D.trace] with ω heω hagω hp hg
  have hag' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < RLC.exitTime D.V (D.Γ ω) (D.U ω) →
      W t ω = D.W₀ t ω := fun t ht => hagω t (heω ▸ ht)
  have hnot : ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω →
      ¬ ForceWord.ThresholdCondition (flowLineRhoL D.κ D.bR D.JR D.y D.θ)
        (flowLineRhoR D.κ D.bR D.JR D.y D.θ) (W t ω)
        (fun i => geomLW W (fun _ => flowLineXL D.bR D.JR D.y) i t ω)
        (fun j => geomRW W (fun _ => flowLineXR D.bR D.JR D.y) j t ω) := by
    intro t ht
    have htexit : (t : ℝ≥0∞) < RLC.exitTime D.V (D.Γ ω) (D.U ω) := heω ▸ ht
    have htU := htexit.trans_le (min_le_left _ _)
    have hmem := FlowStopIdentG.mem_of_lt_exitTime htexit
    have hreal : (D.Γ ω t - D.y).im = 0 → D.y + (D.Γ ω t - D.y).re ∈ D.O := by
      intro hr
      have h := D.N_real (D.Γ ω t) (D.closureV_subset (subset_closure hmem))
        (by simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hr)
      simpa only [Complex.sub_re, Complex.ofReal_re, add_sub_cancel] using h
    by_cases ht0 : t = 0
    · subst t
      have hy : D.y ∈ D.O := by
        have hz : D.Γ ω 0 = D.y := sub_eq_zero.1 hg.1
        have h := hreal (by rw [hz, sub_self]; rfl)
        simpa only [hz, sub_self, Complex.zero_re, add_zero] using h
      have hcuts := hasCommonCollisionCuts_initial (b := D.b) (J := D.J)
        (bR := D.bR) (JR := D.JR) D.O_open hy
      have hn := hp.isForcePath.not_threshold htU
      rw [hp.isForcePath.w_zero, funext hp.isForcePath.vL_zero, funext hp.isForcePath.vR_zero] at hn
      have hnR := (thresholdCondition_iff_of_commonCollisionCuts D.κ_pos D.b_pc D.bR_pc
        D.boundary_eq hcuts).not.mp hn
      have hzL : (fun i => geomLW W (fun _ => flowLineXL D.bR D.JR D.y) i 0 ω) =
          flowLineXL D.bR D.JR D.y := funext fun i => geomLW_zero hWc hW0
            (xL := fun _ => flowLineXL D.bR D.JR D.y) (flowLineXL_nonpos_seed D.bR D.JR D.y i)
      have hzR : (fun i => geomRW W (fun _ => flowLineXR D.bR D.JR D.y) i 0 ω) =
          flowLineXR D.bR D.JR D.y := funext fun i => geomRW_zero hWc hW0
            (xR := fun _ => flowLineXR D.bR D.JR D.y) (flowLineXR_nonneg_seed D.bR D.JR D.y i)
      simpa only [hW0, hzL, hzR] using hnR
    · have htpos : 0 < t := pos_iff_ne_zero.2 ht0
      have hwzero : Ito.rpath (W · ω) 0 = 0 := by
        simpa only [Ito.rpath, Real.toNNReal_zero] using hW0 ω
      have hagT : ∀ s : ℝ≥0, s < t → Ito.rpath (W · ω) s = D.W₀ s ω := by
        intro s hs
        simpa only [Ito.rpath, Real.toNNReal_coe] using hagω s ((ENNReal.coe_lt_coe.2 hs).trans ht)
      have hcuts := hasCommonCollisionCuts_terminal_images (b := D.b) (J := D.J)
        (bR := D.bR) (JR := D.JR) (D := Ito.rpath (W · ω)) D.O_open hg htpos htU.le
        ((hWc ω).comp continuous_real_toNNReal) hwzero hagT hreal
      obtain ⟨-, -, hL, hR, -, -⟩ :=
        stopPathData_det D.V_bounded D.closureV_real_radius (subset_univ _)
        hp hg (hWc ω) hag' htexit
      have hVL : (fun i => D.VL₀ i t ω) =
          (fun i => geomLW W (fun _ => flowLineXL D.b D.J D.y) i t ω) := by
        funext i
        apply sub_left_inj.mp
        simpa only [geomL_rpath_eq_geomLW_sub, hagω t ht] using hL i
      have hVR : (fun i => D.VR₀ i t ω) =
          (fun i => geomRW W (fun _ => flowLineXR D.b D.J D.y) i t ω) := by
        funext i
        apply sub_left_inj.mp
        simpa only [geomR_rpath_eq_geomRW_sub, hagω t ht] using hR i
      have hr : Bessel.realPath W ω = Ito.rpath (W · ω) := rfl
      have hl : Bessel.realPath (fun t ω => -W t ω) ω = (fun s => -Ito.rpath (W · ω) s) := rfl
      have hcuts' : HasCommonCollisionCuts D.b D.J D.bR D.JR D.y D.O (W t ω)
        (fun i => geomLW W (fun _ => flowLineXL D.b D.J D.y) i t ω)
        (fun j => geomRW W (fun _ => flowLineXR D.b D.J D.y) j t ω) (W t ω)
        (fun i => geomLW W (fun _ => flowLineXL D.bR D.JR D.y) i t ω)
        (fun j => geomRW W (fun _ => flowLineXR D.bR D.JR D.y) j t ω) := by
        simpa only [geomLW, geomRW, hr, hl, Ito.rpath, Real.toNNReal_coe] using hcuts
      rw [← hVL, ← hVR, hagω t ht] at hcuts'
      have hn := (thresholdCondition_iff_of_commonCollisionCuts D.κ_pos D.b_pc D.bR_pc
        D.boundary_eq hcuts').not.mp (hp.isForcePath.not_threshold htU)
      simpa only [hagω t ht] using hn
  by_contra hle
  have hlt := lt_of_not_ge hle
  have hne := ne_top_of_lt hlt
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hne
  have hte : (t : ℝ≥0∞) = MartChar.thresholdTime
      (flowLineRhoL D.κ D.bR D.JR D.y D.θ) (flowLineRhoR D.κ D.bR D.JR D.y D.θ) (W · ω)
      (fun i t => geomLW W (fun _ => flowLineXL D.bR D.JR D.y) i t ω)
      (fun j t => geomRW W (fun _ => flowLineXR D.bR D.JR D.y) j t ω) := ht
  have hmem := MartChar.thresholdTime_mem_thresholdSet (hWc ω)
    (fun i => (isForcePath_geomLW hWc (fun _ => flowLineXL D.bR D.JR D.y) ω i).1)
    (fun j => (isForcePath_geomRW hWc (fun _ => flowLineXR D.bR D.JR D.y) ω j).1)
    (fun i j s t hst => geomLW_merge hWc (fun _ => flowLineXL D.bR D.JR D.y) ω i j s t hst)
    (fun i j s t hst => geomRW_merge hWc (fun _ => flowLineXR D.bR D.JR D.y) ω i j s t hst) ht.symm
  exact hnot t (by rw [hte]; exact hlt) hmem

/-- The reference exit announcement (`FlowStopIdentCMI.cmiWReferenceAnnounceStatement`'s proof, the source-side
inputs taken from the trivial comparison `D.toFake`). -/
theorem exists_reference_announce (e : S → ℝ≥0∞) (W : ℝ≥0 → S → ℝ)
    (he : e =ᵐ[D.Q₀] fun ω => RLC.exitTime D.V (D.Γ ω) (D.U ω))
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous (W · ω))
    (hag : ∀ᵐ ω ∂D.Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W t ω = D.W₀ t ω)
    (hpos : ∀ᵐ ω ∂D.Q₀, 0 < e ω)
    (hX : IsMeasurableKilledDriving W (geomLW W fun _ => flowLineXL D.bR D.JR D.y)
      (geomRW W fun _ => flowLineXR D.bR D.JR D.y) e) :
    ∃ σ : ℕ → S → WithTop ℝ≥0,
      (∀ n, IsStoppingTime (drivingFiltration D.Q₀ hX) (σ n)) ∧
      (∀ ω, Monotone fun n => σ n ω) ∧
      (∀ᵐ ω ∂D.Q₀, ∀ n, (σ n ω : ℝ≥0∞) < e ω) ∧
      ∀ᵐ ω ∂D.Q₀, Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (e ω)) := by
  let _ := D.Q₀_prob
  let 𝓖 := drivingFiltration D.Q₀ hX
  have : 𝓖.IsRightContinuous := by unfold 𝓖 drivingFiltration; infer_instance
  have hseed : ¬ FlowStopIdentG.SeedStop D.κ D.b D.J D.y D.θ D.V := by
    intro hseed
    obtain ⟨ω, hp, hz⟩ := (hpos.and (he.trans (D.toFake.ae_exit_zero hseed))).exists
    exact (ne_of_gt hp) hz
  obtain ⟨e₀, -, he₀, -, T, hT⟩ := cmiWSourceAnnounceStatement D.toFake hseed
  have he₀e : e₀ =ᵐ[D.Q₀] e := he₀.trans he.symm
  have haW : AdaptedBefore 𝓖 e W := Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _)
    (Coupling.adaptedBefore_killedDriving_W hX)
  obtain ⟨W', hW'0, hW'c, hW'a, hW'ag⟩ := RetAux79.exists_continuous_adapted_stopped hWc hW0 haW
  have hag' : ∀ᵐ ω ∂D.Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W' t ω = D.W₀ t ω := by
    filter_upwards [hag] with ω hω t ht
    exact (hW'ag ω t ht).trans (hω t ht)
  have hgeom := D.toFake.ae_original_geom_of_agree he hW'c hag'
  let f : S → ℝ≥0∞ := fun ω => min (e ω) (D.U ω)
  have hem : Measurable e := FlowStopIdentLift.measurable_lifetime hX
  have hfm : Measurable f := hem.min (FlowStopIdentLift.measurable_lifetime D.killed)
  have hfe : f =ᵐ[D.Q₀] e := he.mono fun ω hω =>
    min_eq_left (hω ▸ min_le_left _ _)
  have hXf : IsMeasurableKilledDriving D.W₀ D.VL₀ D.VR₀ f := by
    intro r A hA
    have hs : {ω | (r : ℝ≥0∞) < f ω ∧
        (D.W₀ r ω, fun i => D.VL₀ i r ω, fun j => D.VR₀ j r ω) ∈ A} =
        {ω | (r : ℝ≥0∞) < f ω} ∩ {ω | (r : ℝ≥0∞) < D.U ω ∧
        (D.W₀ r ω, fun i => D.VL₀ i r ω, fun j => D.VR₀ j r ω) ∈ A} := by
      ext ω
      constructor
      · rintro ⟨hr, hAω⟩
        exact ⟨hr, hr.trans_le (min_le_right _ _), hAω⟩
      · rintro ⟨hr, -, hAω⟩
        exact ⟨hr, hAω⟩
    rw [hs]
    exact (measurableSet_lt measurable_const hfm).inter (D.killed r A hA)
  have hes : IsStoppingTime 𝓖 (fun ω => (e ω : WithTop ℝ≥0)) := Ito.isStoppingTime_lifetime haW
  have hWL := fun i => stronglyAdapted_geomLW hW'a hW'c
    (xL := fun _ => flowLineXL D.b D.J D.y) measurable_const i
  have hWR := fun j => stronglyAdapted_geomRW hW'a hW'c
    (xR := fun _ => flowLineXR D.b D.J D.y) measurable_const j
  have hXg := Coupling.isMeasurableKilledDriving_of_adaptedBefore
    (MartChar.adaptedBefore_of_stronglyAdapted hes hW'a)
    (fun i => MartChar.adaptedBefore_of_stronglyAdapted hes (hWL i))
    (fun j => MartChar.adaptedBefore_of_stronglyAdapted hes (hWR j))
  have hraw := Ito.killedDrivingFiltration_le
    (MartChar.adaptedBefore_of_stronglyAdapted hes hW'a)
    (fun i => MartChar.adaptedBefore_of_stronglyAdapted hes (hWL i))
    (fun j => MartChar.adaptedBefore_of_stronglyAdapted hes (hWR j)) hXg
  have hid : usualAugmentation 𝓖 D.Q₀ = 𝓖 := by
    rw [Ito.usualAugmentation_eq_rightCont]
    have hn : Ito.nullAugmented 𝓖 D.Q₀ = 𝓖 :=
      Ito.nullAugmented_usualAugmentation (killedDrivingFiltration hX) D.Q₀
    rw [hn]
    exact Filtration.rightCont_self _
  have hle : drivingFiltration D.Q₀ hXf ≤ 𝓖 := by
    have hcong : drivingFiltration D.Q₀ hXf = drivingFiltration D.Q₀ hXg := by
      apply Exist.drivingFiltration_congr_ae
      filter_upwards [hfe, hgeom] with ω hf hg
      refine ⟨hf.symm, fun t ht => ?_⟩
      obtain ⟨hw, hl, hr⟩ := hg t (hf ▸ ht)
      exact ⟨hw.symm, fun i => (hl i).symm, fun j => (hr j).symm⟩
    rw [hcong]
    exact (Ito.usualAugmentation_mono hraw D.Q₀).trans hid.le
  have hTf : ∀ n, ∀ᵐ ω ∂D.Q₀, (T n ω : ℝ≥0∞) < f ω := fun n => by
    filter_upwards [hT.2.2.1 n, he₀e, hfe] with ω ht heq hf
    rwa [hf, ← heq]
  have hTs : ∀ n, IsStoppingTime 𝓖 fun ω => (T n ω : WithTop ℝ≥0) := by
    intro n
    have hs := WFS.isStoppingTime_drivingFiltration_of_lt D.killed hXf
      (fun _ => min_le_right _ _) (hT.1 n) (hTf n)
    exact fun t => hle t _ (hs t)
  refine ⟨fun n ω => (T n ω : WithTop ℝ≥0), hTs,
    fun ω n m hnm => WithTop.coe_le_coe.2 (hT.2.1 ω hnm), ?_, ?_⟩
  · filter_upwards [ae_all_iff.2 hTf, hfe] with ω ht hf n
    exact hf ▸ ht n
  · filter_upwards [RetAux79.ae_tendsto_of_isAnnouncingSeq hT, he₀e] with ω ht heq
    exact heq ▸ ht

end GSetting

/-! ### The clock -/

/-- **A regularized positive clock of the general setting**: the source-side clock of the trivial comparison
(`base`: measurable exit version `e`, the frozen continuous adapted driver `W`, announcements in the original
driving filtration, path data), with the reference word's threshold bound, killed measurability and reference
announcements. -/
structure GClock {S : Type u} [MeasurableSpace S] (D : GSetting S) where
  base : CMIVClock D.toFake
  threshold : ∀ᵐ ω ∂D.Q₀, base.e ω ≤ MartChar.thresholdTime
    (flowLineRhoL D.κ D.bR D.JR D.y D.θ) (flowLineRhoR D.κ D.bR D.JR D.y D.θ) (base.W · ω)
    (fun i t => geomLW base.W (fun _ => flowLineXL D.bR D.JR D.y) i t ω)
    (fun j t => geomRW base.W (fun _ => flowLineXR D.bR D.JR D.y) j t ω)
  killed : IsMeasurableKilledDriving base.W (geomLW base.W fun _ => flowLineXL D.bR D.JR D.y)
    (geomRW base.W fun _ => flowLineXR D.bR D.JR D.y) base.e
  σ : ℕ → S → WithTop ℝ≥0
  σ_stopping : ∀ n, IsStoppingTime (drivingFiltration D.Q₀ killed) (σ n)
  σ_monotone : ∀ ω, Monotone fun n => σ n ω
  σ_lt : ∀ᵐ ω ∂D.Q₀, ∀ n, (σ n ω : ℝ≥0∞) < base.e ω
  σ_limit : ∀ᵐ ω ∂D.Q₀, Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (base.e ω))

namespace GSetting
variable {S : Type u} [MeasurableSpace S] (D : GSetting S)

/-- **The positive clock exists** (no input): the source clock of the trivial comparison, the threshold bound and
the reference announcements. -/
theorem exists_clock (hseed : ¬ FlowStopIdentG.SeedStop D.κ D.b D.J D.y D.θ D.V) : Nonempty (GClock D) := by
  obtain ⟨C⟩ := cmiVPositiveClockStatement D.toFake hseed
  have hag : ∀ᵐ ω ∂D.Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < C.e ω → C.W t ω = D.W₀ t ω := C.ae_agree_before
  have hXP : IsMeasurableKilledDriving C.W (geomLW C.W fun _ => flowLineXL D.bR D.JR D.y)
      (geomRW C.W fun _ => flowLineXR D.bR D.JR D.y) C.e := Coupling.isMeasurableKilledDriving_of_adaptedBefore
    (MartChar.adaptedBefore_of_stronglyAdapted C.stopping C.adapted)
    (fun i => MartChar.adaptedBefore_of_stronglyAdapted C.stopping
      (stronglyAdapted_geomLW C.adapted C.continuous measurable_const i))
    (fun j => MartChar.adaptedBefore_of_stronglyAdapted C.stopping
      (stronglyAdapted_geomRW C.adapted C.continuous measurable_const j))
  obtain ⟨σ, hσ, hσm, hσlt, hσlim⟩ :=
    D.exists_reference_announce C.e C.W C.ae_exit C.zero C.continuous hag C.ae_pos hXP
  exact ⟨{
    base := C
    threshold := D.threshold_of_agree C.ae_exit C.zero C.continuous hag
    killed := hXP
    σ := σ
    σ_stopping := hσ
    σ_monotone := hσm
    σ_lt := hσlt
    σ_limit := hσlim }⟩

end GSetting

namespace GClock
variable {S : Type u} [MeasurableSpace S] {D : GSetting S} (C : GClock D)

/-- The reference driving filtration is contained in the original driving filtration. -/
theorem driving_le : drivingFiltration D.Q₀ C.killed ≤ D.driving := by
  have hraw := Ito.killedDrivingFiltration_le
    (MartChar.adaptedBefore_of_stronglyAdapted C.base.stopping C.base.adapted)
    (fun i => MartChar.adaptedBefore_of_stronglyAdapted C.base.stopping
      (stronglyAdapted_geomLW C.base.adapted C.base.continuous measurable_const i))
    (fun j => MartChar.adaptedBefore_of_stronglyAdapted C.base.stopping
      (stronglyAdapted_geomRW C.base.adapted C.base.continuous measurable_const j)) C.killed
  have hid : usualAugmentation D.driving D.Q₀ = D.driving := by
    rw [Ito.usualAugmentation_eq_rightCont]
    have hn : Ito.nullAugmented D.driving D.Q₀ = D.driving :=
      Ito.nullAugmented_usualAugmentation (killedDrivingFiltration D.killed) D.Q₀
    rw [hn]
    exact Filtration.rightCont_self _
  exact (Ito.usualAugmentation_mono hraw D.Q₀).trans hid.le

include C in
/-- A positive clock forces the seed into the cutoff buffer. -/
theorem seed_mem : (D.y : ℂ) ∈ D.N := by
  let _ := D.toFake.Q₀_prob
  obtain ⟨ω, hpos, he, hg⟩ := ((CMIVClock.ae_pos C.base).and ((C.base.ae_exit).and D.trace)).exists
  have hzero : D.Γ ω 0 = D.y := sub_eq_zero.1 hg.1
  have hyV : (D.y : ℂ) ∈ D.V := by
    by_contra hnot
    have hex := RLC.exitTime_eq_zero (V := D.V) (γ := D.Γ ω) (D.U ω) (by rwa [hzero])
    exact hpos.ne' (he.trans hex)
  exact D.closureV_subset (subset_closure hyV)

end GClock

end InteractingSLE.Restart.FlowLocalityGen
