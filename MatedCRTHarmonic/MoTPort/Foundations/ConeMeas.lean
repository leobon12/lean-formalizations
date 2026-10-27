/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import MatedCRTHarmonic.MoTPort.Foundations.Cone
import QuantumZipper.Proofs.LQG.Measurability
import QuantumZipper.Proofs.LQG.GoodSample

/-!
# C.meas (part 1): a.e.-measurability of `qAreaC` and `scaleC` given the vague limit

For the measurability predicate `ConeRefMeas` from `Cone.lean`, consider an
a.e.-measurable random field `Y : Ω → Field` whose whole-plane area approximations a.s. converge
vaguely (the conclusion of node C.area-exist), the area of every open bounded set
(`aemeasurable_qAreaC_open`) and the plane-like scale `scaleC γ (Y ·)` (`aemeasurable_scaleC`) are
a.e.-measurable.

Proof: a.e. version of QuantumZipper's `LQGMeas.measurable_qAreaMeasure_open` /
`measurable_scaleParam_good` (QZ/Proofs/LQG/Measurability.lean): `μ(U) = sup_n ∫ bump_n dμ`
(`LQGMeas.measure_open_eq_iSup`), each `∫ bump_n dqAreaC` is the a.s. limit of
`∫ bump_n dareaApproxC_k`, measurable in the field (`ConeArea.measurable_areaApproxC`, mathlib
`Measure.measurable_lintegral`), and `scaleC` is an infimum over rationals
(`LQGMeas.measurable_sInf_upClosed`). Same scheme as `WedgeMeasC.aemeasurable_scaleParam`
(WedgeMeas.lean). Own bookkeeping only.

Still missing for C.meas: C.area-exist itself, measurability of the cone field
`ω ↦ coneField (lateralPartC (X ω)) (A · ω) Q`, and joint measurability of
`(s, h) ↦ affineComp s 0 h` and `(θ, h) ↦ rotateField θ h` (Carathéodory, LQGMetric
`continuous_testFamK` template).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace MatedCRTHarmonic.MoTPort

open QuantumZipper LQGMetric

namespace ConeMeas

variable {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `h ↦ ∫ f d(areaApproxC γ h k)` is measurable for continuous `f ≥ 0` -/
theorem measurable_integral_areaApproxC (γ : ℝ) (k : ℕ) {f : ℂ → ℝ} (hf : Continuous f)
    (hf0 : ∀ z, 0 ≤ f z) : Measurable fun h : Field => ∫ z, f z ∂areaApproxC γ h k := by
  have e : (fun h : Field => ∫ z, f z ∂areaApproxC γ h k) =
      fun h => (∫⁻ z, ENNReal.ofReal (f z) ∂areaApproxC γ h k).toReal := by
    funext h
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hf.aestronglyMeasurable
  rw [e]
  exact ((Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hf.measurable)).comp
    (ConeArea.measurable_areaApproxC γ k)).ennreal_toReal

/-- **the `qAreaC`-area of an open bounded set is a.e.-measurable**, given an a.e.-measurable
field with a.s. a vague area limit -/
theorem aemeasurable_qAreaC_open {Y : Ω → Field} (hY : AEMeasurable Y P)
    (hv : ∀ᵐ ω ∂P, ∃ μ, QuantumZipper.IsVagueLimitOn univ (areaApproxC γ (Y ω)) μ)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    AEMeasurable (fun ω => qAreaC γ (Y ω) U) P := by
  have hUc : Uᶜ.Nonempty := by
    obtain ⟨R, hR⟩ := hUb.subset_closedBall (0 : ℂ)
    refine ⟨((|R| + 1 : ℝ) : ℂ), fun h => ?_⟩
    have := hR h
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)] at this
    linarith [le_abs_self R]
  have hv' : ∀ᵐ ω ∂P, QuantumZipper.IsVagueLimitOn univ (areaApproxC γ (Y ω)) (qAreaC γ (Y ω)) :=
    hv.mono fun ω h => ConeArea.isVagueLimitOn_qAreaC h
  have hn : ∀ n : ℕ, AEMeasurable
      (fun ω => ∫ z, LQGMeas.openBump U n z ∂qAreaC γ (Y ω)) P := by
    intro n
    refine aemeasurable_of_tendsto_metrizable_ae atTop
      (f := fun k ω => ∫ z, LQGMeas.openBump U n z ∂areaApproxC γ (Y ω) k) (fun k => ?_) ?_
    · exact (measurable_integral_areaApproxC γ k (LQGMeas.continuous_openBump U n)
        (LQGMeas.openBump_nonneg U n)).comp_aemeasurable hY
    · filter_upwards [hv'] with ω h
      exact h.2.2 _ (LQGMeas.continuous_openBump U n) (LQGMeas.hasCompactSupport_openBump hUb n)
        (subset_univ _)
  have key : ∀ ω, qAreaC γ (Y ω) U =
      ⨆ n : ℕ, ENNReal.ofReal (∫ z, LQGMeas.openBump U n z ∂qAreaC γ (Y ω)) := by
    intro ω
    rw [LQGMeas.measure_open_eq_iSup _ hU hUc]
    congr 1
    funext n
    rw [ofReal_integral_eq_lintegral_ofReal (GoodSample.integrable_of_tsupport
      (U := univ) (fun K hK _ => ConeArea.qAreaC_compact_lt_top γ (Y ω) hK)
      (LQGMeas.continuous_openBump U n) (LQGMeas.hasCompactSupport_openBump hUb n)
      (subset_univ _)) (ae_of_all _ fun z => LQGMeas.openBump_nonneg U n z)]
  simp_rw [key]
  exact AEMeasurable.iSup fun n => ENNReal.measurable_ofReal.comp_aemeasurable (hn n)

/-- **`scaleC` is a.e.-measurable**, given an a.e.-measurable field with a.s. a vague area limit -/
theorem aemeasurable_scaleC {Y : Ω → Field} (hY : AEMeasurable Y P)
    (hv : ∀ᵐ ω ∂P, ∃ μ, QuantumZipper.IsVagueLimitOn univ (areaApproxC γ (Y ω)) μ) :
    AEMeasurable (fun ω => scaleC γ (Y ω)) P := by
  classical
  have hq : ∀ q : ℚ, AEMeasurable (fun ω => qAreaC γ (Y ω) (ball 0 (q : ℝ))) P :=
    fun q => aemeasurable_qAreaC_open hY hv isOpen_ball isBounded_ball
  set m : ℚ → Ω → ℝ≥0∞ := fun q => (hq q).mk _ with hmdef
  have hmm : ∀ q, Measurable (m q) := fun q => (hq q).measurable_mk
  have hm : ∀ᵐ ω ∂P, ∀ q : ℚ, qAreaC γ (Y ω) (ball 0 (q : ℝ)) = m q ω :=
    ae_all_iff.2 fun q => (hq q).ae_eq_mk
  set N : Set Ω := toMeasurable P {ω | ¬ ∀ q : ℚ, qAreaC γ (Y ω) (ball 0 (q : ℝ)) = m q ω}
  have hN0 : P N = 0 := by rw [measure_toMeasurable]; exact ae_iff.1 hm
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hgood : ∀ ω ∉ N, ∀ q : ℚ, qAreaC γ (Y ω) (ball 0 (q : ℝ)) = m q ω := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  let T : Ω → Set ℝ := fun ω => {a : ℝ | 0 < a ∧ 1 ≤ qAreaC γ (Y ω) (ball 0 a)}
  let S : Ω → Set ℝ := fun ω => if ω ∈ N then Ioi 0 else T ω
  have hS : ∀ q : ℚ, MeasurableSet {ω | (q : ℝ) ∈ S ω} := by
    intro q
    have e : {ω | (q : ℝ) ∈ S ω} =
        (N ∩ {_ω | (0 : ℝ) < q}) ∪ (Nᶜ ∩ ({_ω | (0 : ℝ) < q} ∩ {ω | 1 ≤ m q ω})) := by
      ext ω
      by_cases hω : ω ∈ N
      · simp [S, hω]
      · simp only [S, T, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff,
          not_false_eq_true, true_and, false_and, false_or, hgood ω hω q]
    rw [e]
    exact (hNm.inter (MeasurableSet.const _)).union
      (hNm.compl.inter ((MeasurableSet.const _).inter (measurableSet_le measurable_const (hmm q))))
  have hup : ∀ ω a b, a ∈ S ω → a ≤ b → b ∈ S ω := by
    intro ω a b ha hab
    by_cases hω : ω ∈ N
    · simp only [S, hω, ↓reduceIte, mem_Ioi] at ha ⊢; linarith
    · simp only [S, T, hω, ↓reduceIte, mem_ofPred_eq] at ha ⊢
      exact ⟨ha.1.trans_le hab, ha.2.trans (measure_mono (ball_subset_ball hab))⟩
  have hpos : ∀ ω a, a ∈ S ω → 0 < a := by
    intro ω a ha
    by_cases hω : ω ∈ N
    · simpa [S, hω] using ha
    · simp only [S, T, hω, ↓reduceIte, mem_ofPred_eq] at ha; exact ha.1
  have hmeas := LQGMeas.measurable_sInf_upClosed S hS hup hpos
  refine hmeas.aemeasurable.congr ?_
  have hNc : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  filter_upwards [hNc] with ω hω
  simp only [S, hω, ↓reduceIte, T, scaleC]

end ConeMeas

end MatedCRTHarmonic.MoTPort
