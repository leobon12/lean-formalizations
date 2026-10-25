import SupercriticalLQGUniqueness.B2.PfeWeyl.S3Reference
import SupercriticalLQGUniqueness.B2.PfeWeyl.InputsS1
import SupercriticalLQGUniqueness.B2.PfeAxioms.AnalyticImageTransfer
import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedLaw
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf

 



















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.Final

 


def DG20Interfaces : Prop :=
  DG20Section4 ∧ DG20PercEstimate' ∧ DG20QuantileRatio ∧ DG20ExponentRelation ∧
    DG20ExponentPositive ∧ LscTop

 

structure DG20CouplingData (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (h' : Ω' → DistC)
    (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric) : Prop where
  exponent : IsLFPPExponent ξ Q
  normalizer : ∀ δ, IsLFPPNormalizer ξ δ (m δ)
  scale_tendsto : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0)
  ratio : ∀ r : ℚ, ∀ hr : 0 < r,
    Tendsto (fun n => (r : ℝ) *
      (m ⟨(e n : ℝ) / (r : ℝ),
        Set.mem_Ioi.mpr (div_pos (e n).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
      (m (e n) : ℝ)) atTop
      (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))
  ratio_bound : ∃ Λ : ℝ, 1 < Λ ∧
    ∀ δ : Set.Ioo (0 : ℝ) 1, ∀ r : ℚ, ∀ hr : 0 < r,
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ)
  heat_measurable : ∀ δ, Measurable (V δ)
  heat_ae : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z
  limit_field : IsNormalizedWholePlaneGFF h' P'
  field_measurable : ∀ n, Measurable (hN n)
  field_law : ∀ n, P'.map (hN n) = normGFFLaw
  field_tendsto : ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω) atTop (𝓝 (h' ω))
  limit_measurable : Measurable L
  metric_tendsto : ∀ᵐ ω ∂P', Tendsto (fun n =>
    PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n)) (V (e n) (hN n ω))) atTop (𝓝 (L ω))
  rational_tendsto : ∀ᵐ ω ∂P', ∀ u v : ℂ, IsRationalPoint u → IsRationalPoint v →
    Tendsto (fun n => rescaledLFPP (ξ : ℝ) (m (e n)) (V (e n) (hN n ω)) (u, v)) atTop
      (𝓝 ((L ω).toLSCFun.1 (u, v)))
  geometry : ∀ᵐ ω ∂P', (L ω).IsLengthSpace ∧
    (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, (L ω).1 (u, v) < ENNReal.ofReal η → dist u v < δ) ∧
    (∀ u v : ℂ, (L ω).1 (u, v) < ∞ →
      ∃ (γ : ℝ → ℂ) (a b : ℝ),
        (L ω).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧ (L ω).len γ a b = (L ω).1 (u, v))

 


def CoupledSmallAnnuli (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (hN : ℕ → Ω' → DistC)
    (L : Ω' → LSCMetric) : Prop :=
  ∀ k : ℕ, ∀ᵐ ω ∂P', PfeWeyl.SmallAnnulusCosts
    (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n)) (V (e n) (hN n ω)))
    (L ω) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1))

 

def CoupledAcrossTails {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (L : Ω' → LSCMetric) : Prop :=
  ∀ k : ℕ, PfeWeyl.AcrossTailInput P' L ((k : ℝ) + 1) (Nat.cast_add_one_pos k)

section Reindex

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
  {e : ℕ → Set.Ioi (0 : ℝ)} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
  {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {h' : Ω' → DistC}
  {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}

 
theorem DG20CouplingData.comp (hB : DG20CouplingData ξ Q m e c V P' h' hN L)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    DG20CouplingData ξ Q m (fun n => e (ψ n)) c V P' h' (fun n => hN (ψ n)) L where
  exponent := hB.exponent
  normalizer := hB.normalizer
  scale_tendsto := hB.scale_tendsto.comp hψ.tendsto_atTop
  ratio := fun r hr => (hB.ratio r hr).comp hψ.tendsto_atTop
  ratio_bound := hB.ratio_bound
  heat_measurable := hB.heat_measurable
  heat_ae := hB.heat_ae
  limit_field := hB.limit_field
  field_measurable := fun n => hB.field_measurable (ψ n)
  field_law := fun n => hB.field_law (ψ n)
  field_tendsto := hB.field_tendsto.mono fun _ hω => hω.comp hψ.tendsto_atTop
  limit_measurable := hB.limit_measurable
  metric_tendsto := hB.metric_tendsto.mono fun _ hω => hω.comp hψ.tendsto_atTop
  rational_tendsto := hB.rational_tendsto.mono fun _ hω u v hu hv =>
    (hω u v hu hv).comp hψ.tendsto_atTop
  geometry := hB.geometry

 
theorem smallAnnulusCosts_comp {G : ℕ → LSCMetric} {D : LSCMetric} {K' K'' : Set ℂ}
    (h : PfeWeyl.SmallAnnulusCosts G D K' K'') {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    PfeWeyl.SmallAnnulusCosts (fun n => G (ψ n)) D K' K'' := by
  intro z hz hns δ hδ ρ hρ
  obtain ⟨A, h1, h2, h3, h4, h5⟩ := h z hz hns δ hδ ρ hρ
  exact ⟨A, h1, h2, h3, h4, hψ.tendsto_atTop.eventually h5⟩

 
theorem CoupledSmallAnnuli.comp (h : CoupledSmallAnnuli ξ m e V P' hN L)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    CoupledSmallAnnuli ξ m (fun n => e (ψ n)) V P' (fun n => hN (ψ n)) L := fun k =>
  (h k).mono fun _ hω => smallAnnulusCosts_comp hω hψ

end Reindex

section Transfer

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
  {e : ℕ → Set.Ioi (0 : ℝ)} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
  {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {h' : Ω' → DistC}
  {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}

 


theorem normalizedLimitGeometry_of_coupling [StandardBorelSpace Ω'] [IsProbabilityMeasure P']
    (hB : DG20CouplingData ξ Q m e c V P' h' hN L) (Φ : DistC → LSCMetric)
    (hII : ∀ᵐ ω ∂P', L ω = Φ (h' ω)) : PfeWeyl.NormalizedLimitGeometry Φ := by
  intro Ω _ P _ h hh
  have hLaw : P.map h = P'.map h' :=
    (PfeAxioms.normGFFLaw_eq_of_normalized P h hh).symm.trans
      (PfeAxioms.normGFFLaw_eq_of_normalized P' h' hB.limit_field)
  have hTarget : ∀ᵐ ω ∂P', (Φ (h' ω)).IsLengthSpace ∧
      (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, (Φ (h' ω)).1 (u, v) < ENNReal.ofReal η → dist u v < δ) := by
    filter_upwards [hB.geometry, hII] with ω hG hEq
    rw [← hEq]
    exact ⟨hG.1, hG.2.1⟩
  have key := PfeAxioms.ae_field_property_of_standardBorel_coupling P P' h h'
    hh.1.measurable hB.limit_field.1.measurable hLaw
    (fun g => (Φ g).IsLengthSpace ∧
      (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, (Φ g).1 (u, v) < ENNReal.ofReal η → dist u v < δ)) hTarget
  exact ⟨key.mono fun _ hω => hω.1, key.mono fun _ hω => hω.2⟩

 

theorem measure_acrossDist_le_eq_of_coupling [IsProbabilityMeasure P']
    (hB : DG20CouplingData ξ Q m e c V P' h' hN L) {Φ : DistC → LSCMetric} (hΦ : Measurable Φ)
    (hII : ∀ᵐ ω ∂P', L ω = Φ (h' ω))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) (A : EuclideanAnnulus) (T : ℝ≥0∞) :
    P {ω | acrossDist (Φ (h ω)) A ≤ T} = P' {ω | acrossDist (L ω) A ≤ T} := by
  have hS : MeasurableSet {g : DistC | acrossDist (Φ g) A ≤ T} :=
    measurableSet_le
      ((SupercriticalLQGUniqueness.measurable_acrossDist A).comp hΦ)
      measurable_const
  have h1 : P {ω | acrossDist (Φ (h ω)) A ≤ T} = normGFFLaw {g | acrossDist (Φ g) A ≤ T} := by
    rw [PfeAxioms.normGFFLaw_eq_of_normalized P h hh, Measure.map_apply hh.1.measurable hS]
    rfl
  have h2 : P' {ω | acrossDist (Φ (h' ω)) A ≤ T} = normGFFLaw {g | acrossDist (Φ g) A ≤ T} := by
    rw [PfeAxioms.normGFFLaw_eq_of_normalized P' h' hB.limit_field,
      Measure.map_apply hB.limit_field.1.measurable hS]
    rfl
  have h3 : P' {ω | acrossDist (L ω) A ≤ T} = P' {ω | acrossDist (Φ (h' ω)) A ≤ T} := by
    apply measure_congr
    filter_upwards [hII] with ω hω
    simp only [hω]
  rw [h1, h3, h2]

 

theorem normalizedAcrossTails_of_coupling [IsProbabilityMeasure P']
    (hB : DG20CouplingData ξ Q m e c V P' h' hN L) {Φ : DistC → LSCMetric} (hΦ : Measurable Φ)
    (hII : ∀ᵐ ω ∂P', L ω = Φ (h' ω)) (hAT : CoupledAcrossTails P' L) :
    PfeWeyl.NormalizedAcrossTails Φ := by
  intro Ω _ P _ h hh k T hT η hη
  filter_upwards [hAT k T hT η hη] with R hR
  rw [measure_acrossDist_le_eq_of_coupling hB hΦ hII P h hh]
  exact hR

end Transfer

end SupercriticalLQGUniqueness.B2.Final
