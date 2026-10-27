import MatedCRTHarmonic.GMCUpper.ZeroConeMass
import MatedCRTHarmonic.GMS4.Prop410Rooting
import MatedCRTHarmonic.GMCFacts.BallMoment
import MatedCRTHarmonic.GMCUpper.TranslatedMoment
import MatedCRTHarmonic.CellScaling.JointScalingOPath

/-! The whole-plane area record of Proposition 4.8 identifies the same canonical GMC. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric LQGMetric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMCUpper

open MatedCRTHarmonic.GMSLemma27

/-- The defining GMC limit in the Proposition 4.8 area record uniquely identifies
its area with the canonical area of its whole-plane GFF. -/
theorem ae_prop48_areaMeasure_eq_wholePlaneArea
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → DistC} {γ : ℝ}
    (hY : IsNormalizedWPGFF Y P) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (A : MatedCRTHarmonic.GMS4.GMSA.WholePlaneGMCUnitDiskArea Ω γ Y P)
    (hHm : ∀ r z, Measurable (A.circleAverage r z)) :
    ∀ᵐ ω ∂P, A.areaMeasure ω = wholePlaneArea γ Y ω := by
  letI : IsProbabilityMeasure P := hY.1.gaussian.isProbabilityMeasure
  have happ : ∀ᵐ ω ∂P, ∀ k,
      MatedCRTHarmonic.GMSLemma27.lqgApprox γ A.circleAverage k ω =
        MatedCRTHarmonic.MoTPort.areaApproxC γ (Y ω) k := by
    rw [ae_all_iff]
    intro k
    let r : ℝ := QuantumZipper.radius k
    have hr : 0 < r := QuantumZipper.radius_pos k
    have hS : MeasurableSet {p : Ω × ℂ |
        A.circleAverage r p.2 p.1 = circleAvg (Y p.1) r p.2} := by
      refine measurableSet_eq_fun ?_ ?_
      · exact (MatedCRTHarmonic.GMCFacts.measurable_uncurry_coord
          A.circleAverage_isGFF hHm hr).comp
            (measurable_snd.prodMk measurable_fst)
      · exact measurable_circleAvg.comp (f := fun p : Ω × ℂ => (Y p.1, r, p.2))
          ((hY.1.measurable.comp measurable_fst).prodMk
            (measurable_const.prodMk measurable_snd))
    have hcoord : ∀ᵐ ω ∂P, ∀ᵐ z ∂(volume : Measure ℂ),
        A.circleAverage r z ω = circleAvg (Y ω) r z := by
      rw [Measure.ae_ae_comm hS]
      exact Eventually.of_forall fun z => A.circleAverage_eq_field r hr z
    filter_upwards [hcoord] with ω hω
    exact MatedCRTHarmonic.GMCFacts.lqgApprox_eq_areaApproxC γ k hω
  have hv := MatedCRTHarmonic.LQGCoord.ae_exists_isVagueLimitC_wp
    hY.1 hγ.1 hγ.2
  filter_upwards [A.isLQGAreaOf, happ, hv] with ω hAω hωapp hωv
  haveI : IsLocallyFiniteMeasure (A.areaMeasure ω) := hAω.1
  have hA : QuantumZipper.IsVagueLimitOn univ
      (MatedCRTHarmonic.MoTPort.areaApproxC γ (Y ω))
      (A.areaMeasure ω) := by
    refine ⟨by simp, fun K hK _ => by simpa using hK.measure_lt_top,
      fun f hf hfs _ => ?_⟩
    simpa only [← hωapp] using hAω.2 f hf hfs
  have hC : QuantumZipper.IsVagueLimitOn univ
      (MatedCRTHarmonic.MoTPort.areaApproxC γ (Y ω))
      (wholePlaneArea γ Y ω) := by
    have hc := MatedCRTHarmonic.CellScaling.JointScalingO.isVagueLimitC_lqgArea_of_exists hωv
    exact MatedCRTHarmonic.LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mp hc
  have heq := QuantumZipper.isVagueLimitOn_unique isOpen_univ hA hC
  exact heq

/-- An almost-sure identification of a cell model's area transfers the upper
mass event without requiring equality on null samples. -/
theorem upperMassBound_of_ae_area
    {γ : ℝ} (M : CellModel γ) (μ : M.Ω → Measure ℂ)
    (harea : ∀ᵐ ω ∂M.P, M.area ω = μ ω)
    (hbound : ∃ ξ β : ℝ, 0 < ξ ∧ 0 < β ∧
      ∀ ρ ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
        M.P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
          ENNReal.ofReal (δ ^ ξ) < μ ω (ball z δ)} ≤
          ENNReal.ofReal (C * δ ^ β)) :
    MatedCRTHarmonic.GMS4b.UpperMassBound M := by
  obtain ⟨ξ, β, hξ, hβ, hb⟩ := hbound
  refine ⟨ξ, β, hξ, hβ, ?_⟩
  intro ρ hρ
  obtain ⟨C, hC⟩ := hb ρ hρ
  refine ⟨C, fun δ hδ => ?_⟩
  have hevent : {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (δ ^ ξ) < M.area ω (ball z δ)} =ᵐ[M.P]
      {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (δ ^ ξ) < μ ω (ball z δ)} := by
    filter_upwards [harea] with ω hω
    simp only [hω]
  exact (measure_congr hevent).le.trans (hC δ hδ)

/-- G4b's upper-mass input for a cell model whose area is the canonical
normalized whole-plane GMC, up to a null set. -/
theorem upperMassBoundWholePlane_toCellModel
    {γ : ℝ} (M : CellModel γ) {Y : M.Ω → DistC}
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hY : IsNormalizedWPGFF Y M.P)
    (harea : ∀ᵐ ω ∂M.P, M.area ω = wholePlaneArea γ Y ω) :
    MatedCRTHarmonic.GMS4b.UpperMassBound M :=
  upperMassBound_of_ae_area M (wholePlaneArea γ Y) harea
    (upperMassBoundWholePlaneModel_holds hγ hY)

/-- The actual Proposition 4.8 area record satisfies the same grid-level
upper-mass estimate. -/
theorem upperMassBoundProp48AreaRecord_holds
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → DistC} {γ : ℝ}
    (hY : IsNormalizedWPGFF Y P) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (A : MatedCRTHarmonic.GMS4.GMSA.WholePlaneGMCUnitDiskArea Ω γ Y P)
    (hHm : ∀ r z, Measurable (A.circleAverage r z)) :
    ∃ ξ β : ℝ, 0 < ξ ∧ 0 < β ∧
      ∀ ρ ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
        P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
          ENNReal.ofReal (δ ^ ξ) < A.areaMeasure ω (ball z δ)} ≤
          ENNReal.ofReal (C * δ ^ β) := by
  obtain ⟨ξ, β, hξ, hβ, hb⟩ := upperMassBoundWholePlaneModel_holds hγ hY
  refine ⟨ξ, β, hξ, hβ, ?_⟩
  intro ρ hρ
  obtain ⟨C, hC⟩ := hb ρ hρ
  refine ⟨C, fun δ hδ => ?_⟩
  have hevent : {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (δ ^ ξ) < A.areaMeasure ω (ball z δ)} =ᵐ[P]
      {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (δ ^ ξ) < wholePlaneArea γ Y ω (ball z δ)} := by
    filter_upwards [ae_prop48_areaMeasure_eq_wholePlaneArea hY hγ A hHm]
      with ω hω
    simp only [hω]
  exact (measure_congr hevent).le.trans (hC δ hδ)

/-- The translated-ball moment available for the Proposition 4.8 area record.
The auxiliary exponent `p > q` records the Hölder loss; the exact exponent
requested by `Prop48UpperMassMomentInput` is a separate sharp-moment theorem. -/
theorem exists_prop48_record_translated_ball_moment_loss
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → DistC} {γ : ℝ}
    (hY : IsNormalizedWPGFF Y P) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (A : MatedCRTHarmonic.GMS4.GMSA.WholePlaneGMCUnitDiskArea Ω γ Y P)
    (hHm : ∀ r z, Measurable (A.circleAverage r z))
    {q p : ℝ} (hq : 0 < q) (hqp : q < p) (hp : p < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (z : ℂ), ‖z‖ ≤ 1 →
      ∀ R : ℝ, 0 < R → R ≤ 1 / 64 →
        ∫⁻ ω, A.areaMeasure ω (ball z R) ^ q ∂P ≤
          C * ENNReal.ofReal
            (R ^ (q * (2 + γ ^ 2 / 2) - p * q * γ ^ 2 / 2)) := by
  obtain ⟨C, hCtop, hC⟩ :=
    exists_uniform_translated_ball_moment hY hγ.1 hγ.2 hq hqp hp
  refine ⟨C, hCtop, fun z hz R hR hR64 => ?_⟩
  have heq : (fun ω => A.areaMeasure ω (ball z R) ^ q) =ᵐ[P]
      fun ω => wholePlaneArea γ Y ω (ball z R) ^ q := by
    filter_upwards [ae_prop48_areaMeasure_eq_wholePlaneArea hY hγ A hHm]
      with ω hω
    rw [hω]
  rw [lintegral_congr_ae heq]
  exact hC z hz R hR hR64

/-- G4b's upper-mass input for a cell model whose area is the frozen
coupling's zero-cone GMC, up to a null set. -/
theorem upperMassBoundZeroCone_toCellModel
    {γ : ℝ} (M : CellModel γ)
    {X X₀ hIG₀ : M.Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → M.Ω → ℝ} {U : M.Ω → ℝ}
    {ηL η η₀ : M.Ω → C(ℝ, ℂ)} {bm : M.Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (D : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling
      γ M.P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (harea : ∀ᵐ ω ∂M.P, M.area ω = zeroConeArea γ X₀ B₀ B₀' ω) :
    MatedCRTHarmonic.GMS4b.UpperMassBound M :=
  upperMassBound_of_ae_area M (zeroConeArea γ X₀ B₀ B₀') harea
    (upperMassBoundZeroConeModel_holds hγ D)

/-- The Proposition 4.8 area record supplies G4b's upper-mass input after
identifying the cell model's area with that record. -/
theorem upperMassBoundProp48Record_toCellModel
    {γ : ℝ} (M : CellModel γ) {Y : M.Ω → DistC}
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (hY : IsNormalizedWPGFF Y M.P)
    (A : MatedCRTHarmonic.GMS4.GMSA.WholePlaneGMCUnitDiskArea
      M.Ω γ Y M.P)
    (hHm : ∀ r z, Measurable (A.circleAverage r z))
    (harea : ∀ᵐ ω ∂M.P, M.area ω = A.areaMeasure ω) :
    MatedCRTHarmonic.GMS4b.UpperMassBound M := by
  have hcanon := ae_prop48_areaMeasure_eq_wholePlaneArea hY hγ A hHm
  have harea' : ∀ᵐ ω ∂M.P, M.area ω = wholePlaneArea γ Y ω := by
    filter_upwards [harea, hcanon] with ω hω hω'
    exact hω.trans hω'
  exact upperMassBoundWholePlane_toCellModel M hγ hY harea'

end MatedCRTHarmonic.GMCUpper

