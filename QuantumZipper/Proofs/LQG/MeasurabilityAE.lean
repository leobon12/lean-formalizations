import QuantumZipper.Proofs.LQG.Measurability
import QuantumZipper.Proofs.LQG.BoundaryExistenceAS
import QuantumZipper.Proofs.LQG.AreaExistenceAS

/-!
# AE-MEAS: almost-sure measurability of the LQG measures as random measures

If `X : Ω → FieldSample` has measurable coordinates and, almost surely, the approximations of
`X ω` converge vaguely to `qBoundaryMeasure γ (X ω)` (resp. to `qAreaMeasure γ (X ω)` on `ℍ`),
then `ω ↦ qBoundaryMeasure γ (X ω)` (resp. `qAreaMeasure`) is `AEMeasurable` into the Giry
`σ`-algebra. The measurable modification is the measure on a measurable full-measure subset of
the good event, and `0` elsewhere.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace LQGMeasAE

open LQGMeas

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- A measurable full-measure subset of an almost-sure event. -/
theorem exists_measurableSet_subset_ae {p : Ω → Prop} (hp : ∀ᵐ ω ∂P, p ω) :
    ∃ S : Set Ω, MeasurableSet S ∧ (∀ ω ∈ S, p ω) ∧ P Sᶜ = 0 := by
  refine ⟨(toMeasurable P {ω | ¬ p ω})ᶜ, (measurableSet_toMeasurable _ _).compl,
    fun ω hω => ?_, ?_⟩
  · by_contra h
    exact hω (subset_toMeasurable _ _ h)
  · rw [compl_compl, measure_toMeasurable]
    exact ae_iff.1 hp

theorem measurable_bdryFun_comp (hXm : ∀ μ, Measurable fun ω => X ω μ) (γ : ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) : Measurable fun ω => bdryFun γ f (X ω) :=
  (measurable_bdryFun γ hf).comp (measurable_pi_iff.2 hXm)

theorem measurable_areaFun_comp (hXm : ∀ μ, Measurable fun ω => X ω μ) (γ : ℝ) {f : ℂ → ℝ}
    (hf : Measurable f) : Measurable fun ω => areaFun γ f (X ω) :=
  (measurable_areaFun γ hf).comp (measurable_pi_iff.2 hXm)

/-! ## Boundary -/

theorem aemeasurable_qBoundaryMeasure_of_ae (hXm : ∀ μ, Measurable fun ω => X ω μ) {γ : ℝ}
    (hae : ∀ᵐ ω ∂P, IsVagueLimitR (bdryApprox γ (X ω)) (qBoundaryMeasure γ (X ω))) :
    AEMeasurable (fun ω => qBoundaryMeasure γ (X ω)) P := by
  classical
  obtain ⟨S, hSm, hSp, hS0⟩ := exists_measurableSet_subset_ae hae
  let M : Ω → Measure ℝ := fun ω => if ω ∈ S then qBoundaryMeasure γ (X ω) else 0
  refine ⟨M, ?_, ?_⟩
  · refine measurable_measure_of_open M (fun N => Ioo (-(N : ℝ)) N) (fun N => measurableSet_Ioo)
      (fun m n hmn => Ioo_subset_Ioo (by simpa using hmn) (by exact_mod_cast hmn))
      (fun ω => ?_) (fun ω N => ?_) (fun U N hU => ?_)
    · have : (⋃ N : ℕ, Ioo (-(N : ℝ)) N) = univ := by
        refine eq_univ_of_forall fun t => mem_iUnion.2 ?_
        obtain ⟨N, hN⟩ := exists_nat_gt |t|
        exact ⟨N, abs_lt.1 hN⟩
      rw [this, compl_univ, measure_empty]
    · by_cases hω : ω ∈ S
      · have := (hSp ω hω).1
        simp only [M, hω, ite_true]
        exact measure_Ioo_lt_top.ne
      · simp [M, hω]
    · set W := U ∩ Ioo (-(N : ℝ)) N
      have hW : IsOpen W := hU.inter isOpen_Ioo
      have hWb : Bornology.IsBounded W := Metric.isBounded_Ioo _ _ |>.subset inter_subset_right
      have hWc : Wᶜ.Nonempty := ⟨N, fun h => lt_irrefl _ h.2.2⟩
      have key : ∀ ω, M ω W = S.indicator
          (fun ω => ⨆ n : ℕ, ENNReal.ofReal (bdryFun γ (openBump W n) (X ω))) ω := by
        intro ω
        by_cases hω : ω ∈ S
        · simp only [M, hω, ite_true, indicator_of_mem hω]
          have hv := hSp ω hω
          have := hv.1
          rw [measure_open_eq_iSup _ hW hWc]
          congr 1
          funext n
          have hc := continuous_openBump W n
          have hcs := hasCompactSupport_openBump hWb n
          rw [show bdryFun γ (openBump W n) (X ω) = ∫ t, openBump W n t ∂qBoundaryMeasure γ (X ω)
              from (hv.2 _ hc hcs).liminf_eq,
            ofReal_integral_eq_lintegral_ofReal (hc.integrable_of_hasCompactSupport hcs)
              (ae_of_all _ fun z => openBump_nonneg W n z)]
        · simp [M, hω]
      simp_rw [key]
      exact (Measurable.iSup fun n => ENNReal.measurable_ofReal.comp
        (measurable_bdryFun_comp hXm γ (continuous_openBump W n).measurable)).indicator hSm
  · refine measure_mono_null (fun ω hω => ?_) hS0
    by_contra h
    exact hω (by simp [M, show ω ∈ S from not_not.1 h])

/-! ## Area -/

theorem aemeasurable_qAreaMeasure_of_ae (hXm : ∀ μ, Measurable fun ω => X ω μ) {γ : ℝ}
    (hae : ∀ᵐ ω ∂P, IsVagueLimitOn H (areaApprox γ (X ω)) (qAreaMeasure γ (X ω))) :
    AEMeasurable (fun ω => qAreaMeasure γ (X ω)) P := by
  classical
  obtain ⟨S, hSm, hSp, hS0⟩ := exists_measurableSet_subset_ae hae
  let M : Ω → Measure ℂ := fun ω => if ω ∈ S then qAreaMeasure γ (X ω) else 0
  refine ⟨M, ?_, ?_⟩
  · refine measurable_measure_of_open M hExh (fun N => (isOpen_hExh N).measurableSet) hExh_mono
      (fun ω => ?_) (fun ω N => ?_) (fun U N hU => ?_)
    · by_cases hω : ω ∈ S
      · simp only [M, hω, ite_true]
        exact measure_mono_null (compl_subset_compl.2 H_subset_iUnion_hExh) (hSp ω hω).1
      · simp [M, hω]
    · by_cases hω : ω ∈ S
      · simp only [M, hω, ite_true]
        exact (lt_of_le_of_lt (measure_mono (hExh_subset_compact N))
          ((hSp ω hω).2.1 _ (isCompact_hExhK N) (hExhK_subset_H N))).ne
      · simp [M, hω]
    · set W := U ∩ hExh N
      have hW : IsOpen W := hU.inter (isOpen_hExh N)
      have hWH : W ⊆ H :=
        inter_subset_right.trans ((hExh_subset_compact N).trans (hExhK_subset_H N))
      have hWb : Bornology.IsBounded W :=
        (isCompact_hExhK N).isBounded.subset (inter_subset_right.trans (hExh_subset_compact N))
      have hWc : Wᶜ.Nonempty := ⟨0, fun h => by simpa [H] using hWH h⟩
      have key : ∀ ω, M ω W = S.indicator
          (fun ω => ⨆ n : ℕ, ENNReal.ofReal (areaFun γ (openBump W n) (X ω))) ω := by
        intro ω
        by_cases hω : ω ∈ S
        · simp only [M, hω, ite_true, indicator_of_mem hω]
          have hv := hSp ω hω
          rw [measure_open_eq_iSup _ hW hWc]
          congr 1
          funext n
          have hc := continuous_openBump W n
          have hcs := hasCompactSupport_openBump hWb n
          have hsupp := (tsupport_openBump_subset W n).trans hWH
          rw [show areaFun γ (openBump W n) (X ω) = ∫ z, openBump W n z ∂qAreaMeasure γ (X ω)
              from (hv.2.2 _ hc hcs hsupp).liminf_eq,
            ofReal_integral_eq_lintegral_ofReal
              (GoodSample.integrable_of_tsupport hv.2.1 hc hcs hsupp)
              (ae_of_all _ fun z => openBump_nonneg W n z)]
        · simp [M, hω]
      simp_rw [key]
      exact (Measurable.iSup fun n => ENNReal.measurable_ofReal.comp
        (measurable_areaFun_comp hXm γ (continuous_openBump W n).measurable)).indicator hSm
  · refine measure_mono_null (fun ω hω => ?_) hS0
    by_contra h
    exact hω (by simp [M, show ω ∈ S from not_not.1 h])

theorem aemeasurable_qAreaMeasure_apply_of_ae (hXm : ∀ μ, Measurable fun ω => X ω μ)
    {γ : ℝ} (hae : ∀ᵐ ω ∂P, IsVagueLimitOn H (areaApprox γ (X ω)) (qAreaMeasure γ (X ω)))
    {s : Set ℂ} (hs : MeasurableSet s) :
    AEMeasurable (fun ω => qAreaMeasure γ (X ω) s) P :=
  (Measure.measurable_coe hs).comp_aemeasurable (aemeasurable_qAreaMeasure_of_ae hXm hae)

/-! ## Free-field corollaries -/

end LQGMeasAE

end QuantumZipper
