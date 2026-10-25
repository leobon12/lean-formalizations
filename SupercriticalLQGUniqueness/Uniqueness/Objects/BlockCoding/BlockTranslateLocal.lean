import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.BlockQuotLocal
import LQGMetric.Papers.CONF.S3L35B5




set_option autoImplicit false
noncomputable section
open MeasureTheory Set LQGMetric.Blueprint
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

open LQGMetric (DistC)

 

theorem fieldSigma0On_normTranslate_le (z : ℂ) (V : Set ℂ) :
    fieldSigma0On (Objects.Producer.normTranslate z : DistC → DistC) V ≤
      fieldSigma0On (id : DistC → DistC) {y | y - z ∈ V} := by
  change fieldSigma0On
    (fun g : DistC => LQGMetric.addConst (translateDist z g)
      (-LQGMetric.circleAvg g 1 z)) V ≤ _
  rw [LQGMetric.CONF.fieldSigma0On_addConst]
  rw [show translateDist z =
      (fun g : DistC => LQGMetric.affineComp 1 z g) from by
        funext g; exact translateDist_eq_affineComp_one z g]
  let _ : MeasurableSpace DistC :=
    fieldSigma0On (id : DistC → DistC) {y | y - z ∈ V}
  apply (measurable_iff_comap_le).mp
  refine measurable_pi_iff.mpr fun ψ => ?_
  let φ : {φ : LQGMetric.TestC0 //
      tsupport (φ.1 : ℂ → ℝ) ⊆ {y | y - z ∈ V}} :=
    ⟨⟨LQGMetric.CONF.affPush 1 z ψ.1.1, by
      rw [LQGMetric.CONF.integral_affPush one_pos z, ψ.1.2]⟩,
      by
        intro y hy
        have hs := LQGMetric.CONF.tsupport_affPush_subset one_pos z ψ.1.1 ψ.2 hy
        simpa using hs⟩
  have hgen : Measurable
      (fun g : DistC => fun φ : {φ : LQGMetric.TestC0 //
        tsupport (φ.1 : ℂ → ℝ) ⊆ {y | y - z ∈ V}} => g φ.1.1) :=
    Measurable.of_comap_le le_rfl
  convert (measurable_pi_apply φ).comp hgen using 1
  funext g
  change LQGMetric.affineComp 1 z g ψ.1.1 =
    g (LQGMetric.CONF.affPush 1 z ψ.1.1)
  exact LQGMetric.CONF.affineComp_apply_eq_affPush 1 z g ψ.1.1

 

theorem aeEventIn_normTranslate_preimage
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (z : ℂ) (V : TopologicalSpace.Opens ℂ) (B : Set DistC)
    (hB : AEEventIn μ (fieldSigma0On id V) B) :
    AEEventIn μ (fieldSigma0On id {y | y - z ∈ V})
      (Objects.Producer.normTranslate z ⁻¹' B) := by
  obtain ⟨R, hRm, hBR⟩ := hB
  have hsig : fieldSigma0On (Objects.Producer.normTranslate z : DistC → DistC) V =
      MeasurableSpace.comap (Objects.Producer.normTranslate z)
        (fieldSigma0On (id : DistC → DistC) V) := by
    unfold fieldSigma0On
    rw [MeasurableSpace.comap_comp]
    rfl
  have hpre : MeasurableSet[fieldSigma0On
      (Objects.Producer.normTranslate z : DistC → DistC) V]
      (Objects.Producer.normTranslate z ⁻¹' R) := by
    rw [hsig]
    exact hRm.preimage (Measurable.of_comap_le le_rfl)
  have hmap : μ.map (Objects.Producer.normTranslate z) = μ := by
    calc
      μ.map (Objects.Producer.normTranslate z) = μ.map
          (fun g => LQGMetric.addConst (translateDist z g)
            (-LQGMetric.circleAvg g 1 z)) := rfl
      _ = μ.map id := map_normalized_translate_sub_circleAvg hμ z
      _ = μ := by simp
  have hae : ∀ᵐ g ∂μ,
      (Objects.Producer.normTranslate z g ∈ B) = (Objects.Producer.normTranslate z g ∈ R) := by
    have heq : ∀ᵐ y ∂μ.map (Objects.Producer.normTranslate z), (y ∈ B) = (y ∈ R) := by
      rw [hmap]
      exact hBR
    exact ae_of_ae_map (measurable_normTranslate z).aemeasurable heq
  exact ⟨Objects.Producer.normTranslate z ⁻¹' R,
    (fieldSigma0On_normTranslate_le z V) _ hpre, hae⟩

 

theorem aeEventIn_blockEvent_modConst
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    (Cp Ci : ℝ) (hCp : 0 < Cp) (hCi : 0 < Ci)
    (hCmp : ∀ᵐ g ∂μ, (∀ p : ℂ × ℂ,
      E g p ≤ ENNReal.ofReal Cp * D g p) ∧
      (∀ p : ℂ × ℂ, D g p ≤ ENNReal.ofReal Ci * E g p))
    (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (Cmid0 : ℝ)
    (hR : 0 < T.rho * T.r) (hn : ‖T.orientation‖ = 1)
    (hRad : 0 ≤ T.blockRadius)
    (hLam : C.lamConst < 1)
    (hRatio : ENNReal.ofReal Cp * ENNReal.ofReal C.lamConst *
      ENNReal.ofReal Ci < 1)
    (U : TopologicalSpace.Opens ℂ) (hUne : (U : Set ℂ).Nonempty)
    (hW : ∀ k ∈ Finset.Icc 1 Ksh,
      Metric.ball (0 : ℂ) (3 * (3 * 8 ^ (Ksh - k) * (T.rho * T.r))) ⊆ U)
    (hWin : ∀ k ∈ Finset.Icc 1 Ksh,
      (Objects.ShieldLocality.shieldWindow (3 * 8 ^ (Ksh - k) * (T.rho * T.r)) : Set ℂ) ⊆ U)
    (hKW : closure (Objects.Excursions.blockShape T) ⊆ U)
    (hCU : Metric.closedBall (Objects.Excursions.cU T) T.blockRadius ⊆ U)
    (hCV : Metric.closedBall (Objects.Excursions.cV T) T.blockRadius ⊆ U)
    (z : ℂ) :
    AEEventIn μ (fieldSigma0On id {y | y - z ∈ U})
      {g | Objects.Excursions.blockEvent C T Ksh Cmid0 D E z g} := by
  change AEEventIn μ (fieldSigma0On id {y | y - z ∈ U})
    (Objects.Producer.normTranslate z ⁻¹'
      {g | Objects.Excursions.blockRaw C T Ksh Cmid0 D E g})
  exact aeEventIn_normTranslate_preimage μ hμ z U _
    (aeEventIn_blockRaw_modConst μ hμ ξ Q D E hD hE Cp Ci hCp hCi
      hCmp C T Ksh Cmid0 hR hn hRad hLam hRatio U hUne
      hW hWin hKW hCU hCV)

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
