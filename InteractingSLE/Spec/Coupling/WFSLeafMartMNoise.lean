/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafMartMSpace
import InteractingSLE.Spec.Coupling.WholeField5Life
import InteractingSLE.Spec.Coupling.WholeField7Label
import InteractingSLE.Spec.Sec2.GirsanovDensity

/-!
# The stopped-noise exponential martingales in the driving filtration

Noise recovery and the landed lifetime announcing sequence give continuous
martingales in the actual full driving filtration. No strong-solution or
Brownian natural-filtration assertion is used.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open WholeField LawUnique Coupling

/-- A martingale adapted to a smaller filtration stays a martingale there. -/
theorem martingale_of_le_of_stronglyAdapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓓 𝓔 : Filtration ℝ≥0 mΩ} (hle : 𝓓 ≤ 𝓔)
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓔 P) (ha : StronglyAdapted 𝓓 M) :
    Martingale M 𝓓 P := by
  refine ⟨ha, fun s t hst => ?_⟩
  exact (condExp_condExp_of_le (hle s) (𝓔.le s)).symm.trans
    ((condExp_congr_ae (hM.condExp_ae_eq hst)).trans
      (EventuallyEq.of_eq (condExp_of_stronglyMeasurable (𝓓.le s) (ha s) (hM.integrable s))))

/-- Along a lifetime announcing sequence, the recovered stopped-noise
exponentials have continuous paths and are full-driving martingales. -/
theorem exists_stoppedNoise_exponentials
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ)
    {σ : ℕ → Ω → ℝ≥0} (hσ : IsAnnouncingSeq (drivingFiltration P hX) P ζ σ) :
    ∃ Bv : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (Bv t)) ∧
      (∀ ω, Continuous (fun t => Bv t ω)) ∧ (∀ ω, Bv 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, Bv t ω = B t ω) ∧
      ∀ m (a : ℝ), Martingale (fun t ω => Real.exp (a * Bv (min t (σ m ω)) ω -
        a ^ 2 * ((min t (σ m ω) : ℝ≥0) : ℝ) / 2)) (drivingFiltration P hX) P := by
  let 𝓓 := drivingFiltration P hX
  let 𝓔 := usualAugmentation 𝓕 P
  have hDE : 𝓓 ≤ 𝓔 := Ito.drivingFiltration_le_usualAugmentation hE hX
  have hnull (t : ℝ≥0) (A : Set Ω) (hA : MeasurableSet A) (h0 : P A = 0) :
      MeasurableSet[𝓓 t] A := Ito.measurableSet_usualAugmentation_of_null hA h0 t
  obtain ⟨Bv, hBvm, hBvc, hBv0, _, hBve⟩ := QuantumZipper.RS.exists_good_version0 hE.1.1
  have hBa : StronglyAdapted 𝓔 Bv := by
    intro t
    apply Measurable.stronglyMeasurable
    exact Sec2.Restart.measurable_of_ae_eq_of_null (𝓔.le t)
      (fun A hA h0 => Ito.measurableSet_usualAugmentation_of_null hA h0 t)
      ((Ito.isFilteredBrownianReal_usualAugmentation hE.1).2.1 t)
      (hBvm t) (hBve.mono fun ω hω => (hω t).symm)
  have hFB := Girsanov.isFilteredPreBrownian_of_isFilteredBrownianReal
    (Ito.isFilteredBrownianReal_usualAugmentation hE.1)
  have hBm (a : ℝ) : Martingale (fun t ω => Real.exp
      (a * Bv t ω - a ^ 2 * (t : ℝ) / 2)) 𝓔 P := by
    have := hFB.waldExponential_isMartingale a
    apply this.congr (fun t => ?_) (fun t => ?_)
    · exact (Real.measurable_exp.comp (((hBa t).measurable.const_mul a).sub_const _)).stronglyMeasurable
    · exact hBve.mono fun ω hω => by
        change Real.exp (a * B t ω - a ^ 2 * (t : ℝ) / 2) =
          Real.exp (a * Bv t ω - a ^ 2 * (t : ℝ) / 2)
        rw [hω t]
  have hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath κ xL xR ρL ρR (W · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) (Bv · ω) (ζ ω) := by
    filter_upwards [hE.2.2.2.2, hBve] with ω hp he
    exact Sec2.Assembly.isIntegratedSLEPath_congr hp rfl (fun _ => rfl) (fun _ => rfl)
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun t _ => he t)
  let good : Ω → Prop := fun ω => IsIntegratedSLEPath κ xL xR ρL ρR (W · ω)
    (fun i t => VL i t ω) (fun j t => VR j t ω) (Bv · ω) (ζ ω) ∧
    ∀ m, (σ m ω : ℝ≥0∞) < ζ ω
  have hg : ∀ᵐ ω ∂P, good ω := hpath.and (ae_all_iff.2 hσ.2.2.1)
  let G := (toMeasurable P {ω | ¬ good ω})ᶜ
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hG0 : P Gᶜ = 0 := by
    rw [show Gᶜ = toMeasurable P {ω | ¬ good ω} from compl_compl _]
    rw [measure_toMeasurable]
    exact ae_iff.1 hg
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hG0
  have hGgood : ∀ ω ∈ G, good ω := fun ω hω => by
    by_contra hn
    exact hω (subset_toMeasurable _ _ hn)
  have hGD : MeasurableSet[𝓓 0] G := by
    have := (hnull 0 Gᶜ hGm.compl hG0).compl
    simpa only [compl_compl] using this
  have hWa := Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P)
    (Coupling.adaptedBefore_killedDriving_W hX)
  have hVLa := fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P)
    (Coupling.adaptedBefore_killedDriving_VL hX i)
  have hVRa := fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P)
    (Coupling.adaptedBefore_killedDriving_VR hX i)
  have hBvj : Measurable (Function.uncurry Bv) :=
    measurable_uncurry_of_continuous_of_measurable hBvc hBvm
  refine ⟨Bv, hBvm, hBvc, hBv0, hBve, fun m a => ?_⟩
  have hsm (t : ℝ≥0) : Measurable[𝓓 t] (fun ω => min t (σ m ω)) := by
    have hm := (WithTop.measurable_untopD (0 : ℝ≥0)).comp ((hσ.1 m).min_const t).measurable
    have hl := ((hσ.1 m).min_const t).measurableSpace_le_of_le_const fun _ => min_le_right _ _
    simpa only [Function.comp_def, ← WithTop.coe_min, WithTop.untopD_coe, min_comm]
      using hm.mono hl le_rfl
  have hNa (t : ℝ≥0) : Measurable[𝓓 t] (fun ω => Bv (min t (σ m ω)) ω) := by
    have hr := measurable_stoppedNoise hκ hWa hVLa hVRa hGD
      (fun ω hω => ⟨(hGgood ω hω).1, hBvc ω⟩)
      (fun ω hω => (hGgood ω hω).2 m) t ((hσ.1 m).min_const t)
    have hl := ((hσ.1 m).min_const t).measurableSpace_le_of_le_const fun _ => min_le_right _ _
    apply Sec2.Restart.measurable_of_ae_eq_of_null (𝓓.le t) (hnull t) (hr.mono hl le_rfl)
      (hBvj.comp (((hsm t).mono (𝓓.le t) le_rfl).prodMk measurable_id))
    filter_upwards [hGae] with ω hω
    simp only [WholeField.stoppedProcess_coe_apply, noiseOn, hω, ↓reduceIte,
      Function.comp_def, Function.uncurry_apply_pair, id_eq]
  have hsE : IsStoppingTime 𝓔 fun ω => (σ m ω : WithTop ℝ≥0) :=
    fun t => hDE t _ (hσ.1 m t)
  have hstop := InteractingSLE.Martingale.stoppedProcess_of_rightContinuous (hBm a)
    (fun ω _ => ((Real.continuous_exp.comp
      (((hBvc ω).const_mul a).sub ((NNReal.continuous_coe.const_mul _).div_const _)))).continuousWithinAt)
    hsE
  have had : StronglyAdapted 𝓓 (fun t ω => Real.exp (a * Bv (min t (σ m ω)) ω -
      a ^ 2 * ((min t (σ m ω) : ℝ≥0) : ℝ) / 2)) := fun t =>
    (Real.measurable_exp.comp (((hNa t).const_mul a).sub
      (((measurable_coe_nnreal_real.comp (hsm t)).const_mul _).div_const _))).stronglyMeasurable
  apply martingale_of_le_of_stronglyAdapted hDE _ had
  convert hstop using 1
  funext t ω
  rw [WholeField.stoppedProcess_coe_apply]

end InteractingSLE.WFS
