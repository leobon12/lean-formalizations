import SupercriticalLQGUniqueness.B2.PfeLocal.Inputs
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.ClosedEventToolkit
import SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes.SetGeoRegular

 





set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 

theorem lscInternalFam_measurable_bounded
    {Ω : Type} [MeasurableSpace Ω] {D : Ω → LSCMetric}
    (hD : Measurable D) (V : TopologicalSpace.Opens ℂ)
    (hVb : Bornology.IsBounded (V : Set ℂ)) :
    Measurable (fun ω => lscInternalFam D ω (V : Set ℂ)) := by
  classical
  refine measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v => ?_
  by_cases hu : u ∈ (V : Set ℂ)
  · by_cases hv : v ∈ (V : Set ℂ)
    · have hm := (Uniqueness.Toolkit.CountableBase.internalBoundedOpen_borel
        V.isOpen hVb (⟨u, hu⟩ : V) (⟨v, hv⟩ : V)).comp hD
      simpa only [Function.comp_def, lscInternalFam,
        Uniqueness.TwoScale.S36.internal_eq_intExt] using hm
    · have heq : (fun ω => lscInternalFam D ω (V : Set ℂ) u v) =
          fun _ => (∞ : ℝ≥0∞) := by
        funext ω
        exact Uniqueness.TwoScale.S36.intExt_eq_top_of_not_mem_right
          (D := D ω) (Y := (V : Set ℂ)) u hv
      rw [heq]
      exact measurable_const
  · have heq : (fun ω => lscInternalFam D ω (V : Set ℂ) u v) =
        fun _ => (∞ : ℝ≥0∞) := by
      funext ω
      exact Uniqueness.TwoScale.S36.intExt_eq_top_of_not_mem_left
        (D := D ω) (Y := (V : Set ℂ)) v hu
    rw [heq]
    exact measurable_const

 

theorem lscNormIntFam_measurable_bounded
    {Ω : Type} [MeasurableSpace Ω]
    {h : Ω → LQGMetric.DistC} {D : Ω → LSCMetric}
    (hh : Measurable h) (hD : Measurable D)
    (ξ : ℝ) (z : ℂ) (r : ℝ)
    (V : TopologicalSpace.Opens ℂ)
    (hVb : Bornology.IsBounded (V : Set ℂ)) :
    Measurable (fun ω => lscNormIntFam ξ h D z r ω (V : Set ℂ)) := by
  have hca : Measurable (fun ω => LQGMetric.circleAvg (h ω) r z) :=
    (LQGMetric.measurable_circleAvg_left r z).comp hh
  have hfac : Measurable (fun ω =>
      ENNReal.ofReal (Real.exp (-ξ * LQGMetric.circleAvg (h ω) r z))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (hca.const_mul (-ξ)))
  have hI := lscInternalFam_measurable_bounded hD V hVb
  exact measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v =>
    hfac.mul ((measurable_pi_apply v).comp
      ((measurable_pi_apply u).comp hI))

theorem lscNormIntFam_sigma_le_bounded
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {h : Ω → LQGMetric.DistC} {D : Ω → LSCMetric}
    (hh : Measurable h) (hD : Measurable D)
    (ξ : ℝ) (z : ℂ) (r : ℝ)
    (V : TopologicalSpace.Opens ℂ)
    (hVb : Bornology.IsBounded (V : Set ℂ)) :
    LQGMetric.Blueprint.famSigma (lscNormIntFam ξ h D z r) V ≤ mΩ :=
  (lscNormIntFam_measurable_bounded hh hD ξ z r V hVb).comap_le

 

theorem continuous_euclidForget_of_small_metric (D : LSCMetric)
    (hsmall : ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, D.1 (u, v) < ENNReal.ofReal η → dist u v < δ) :
    Continuous (Uniqueness.Measurability.SetGeodesicCodes.euclidForget D) := by
  rw [continuous_iff_continuousAt]
  intro x
  change Tendsto (Uniqueness.Measurability.SetGeodesicCodes.euclidForget D)
    (𝓝 x) (𝓝 (Uniqueness.Measurability.SetGeodesicCodes.euclidForget D x))
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨η, hη, hclose⟩ := hsmall x δ hδ
  have hD : Tendsto (fun y : D.Space => D.1 (x, y)) (𝓝 x) (𝓝 0) := by
    have hD' := (tendsto_iff_edist_tendsto_0).mp
      (tendsto_id : Tendsto (fun y : D.Space => y) (𝓝 x) (𝓝 x))
    change Tendsto (fun y : D.Space => D.1 (y, x)) (𝓝 x) (𝓝 0) at hD'
    convert hD' using 1
    funext y
    exact D.isExtMetric.2.2.1 x y
  have hev : ∀ᶠ y : D.Space in 𝓝 x,
      D.1 (x, y) < ENNReal.ofReal η :=
    hD.eventually (isOpen_Iio.mem_nhds (ENNReal.ofReal_pos.mpr hη))
  exact hev.mono fun y hy => by
    simpa only [Uniqueness.Measurability.SetGeodesicCodes.euclidForget,
      id_eq, @dist_comm ℂ (inferInstance : PseudoMetricSpace ℂ) y x] using hclose y hy

 

theorem internal_eq_iInf_compactPathInf_of_forget
    (D : LSCMetric)
    (hforget : Continuous
      (Uniqueness.Measurability.SetGeodesicCodes.euclidForget D))
    {U : Set ℂ} (H : CompactExhaustion U) (x y : U) :
    D.internal U (x, y) =
      ⨅ n : ℕ, Uniqueness.Toolkit.CompactPathInfimum.compactPathInf D
        ((H n).image Subtype.val) {(x : ℂ)} {(y : ℂ)} := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun n => ?_
    unfold Uniqueness.Toolkit.CompactPathInfimum.compactPathInf
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun hK => le_iInf fun hE => le_iInf fun hF => ?_
    have hU : ∀ t ∈ Icc a b, P t ∈ U := by
      intro t ht
      obtain ⟨u, -, hu⟩ := hK t ht
      exact hu ▸ u.2
    have hx : P a = (x : ℂ) := Set.mem_singleton_iff.mp hE
    have hy : P b = (y : ℂ) := Set.mem_singleton_iff.mp hF
    unfold LSCMetric.internal
    exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
      iInf_le_of_le hP <| iInf_le_of_le hU <|
      iInf_le_of_le hx <| iInf_le_of_le hy le_rfl
  · unfold LSCMetric.internal
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun hU => le_iInf fun hx => le_iInf fun hy => ?_
    have hcont : ContinuousOn P (Icc a b) := by
      have hc := hforget.comp_continuousOn hP.2
      change ContinuousOn P (Icc a b) at hc
      exact hc
    let g : Icc a b → U := fun t => ⟨P t, hU t t.2⟩
    have hg : Continuous g :=
      (continuousOn_iff_continuous_domRestrict.mp hcont).subtype_mk _
    obtain ⟨n, hn⟩ := H.exists_superset_of_isCompact (isCompact_univ.image hg)
    have hK : ∀ t ∈ Icc a b, P t ∈ (H n).image Subtype.val := by
      intro t ht
      exact ⟨g ⟨t, ht⟩, hn (Set.mem_image_of_mem g (Set.mem_univ _)), rfl⟩
    refine (iInf_le (fun n : ℕ =>
      Uniqueness.Toolkit.CompactPathInfimum.compactPathInf D
        ((H n).image Subtype.val) {(x : ℂ)} {(y : ℂ)}) n).trans ?_
    unfold Uniqueness.Toolkit.CompactPathInfimum.compactPathInf
    exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
      iInf_le_of_le hP <| iInf_le_of_le hK <|
      iInf_le_of_le (Set.mem_singleton_iff.mpr hx) <|
      iInf_le_of_le (Set.mem_singleton_iff.mpr hy) le_rfl

 
def compactExhaustIntExt (U : Set ℂ) (H : CompactExhaustion U)
    (D : LSCMetric) (u v : ℂ) : ℝ≥0∞ := by
  classical
  exact if u ∈ U ∧ v ∈ U then
    ⨅ n : ℕ, Uniqueness.Toolkit.CompactPathInfimum.compactPathInf D
      ((H n).image Subtype.val) {u} {v}
    else ∞

theorem compactExhaustIntExt_measurable (U : Set ℂ)
    (H : CompactExhaustion U) :
    Measurable (fun D : LSCMetric => compactExhaustIntExt U H D) := by
  classical
  refine measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v => ?_
  by_cases huv : u ∈ U ∧ v ∈ U
  · simp only [compactExhaustIntExt, if_pos huv]
    exact Measurable.iInf fun n =>
      Uniqueness.Toolkit.CompactPathInfimum.compactPathInf_measurable
        ((H.isCompact n).image continuous_subtype_val)
        isCompact_singleton isCompact_singleton
  · simp only [compactExhaustIntExt, if_neg huv]
    exact measurable_const

theorem compactExhaustIntExt_eq_intExt (D : LSCMetric)
    (hforget : Continuous
      (Uniqueness.Measurability.SetGeodesicCodes.euclidForget D))
    {U : Set ℂ} (H : CompactExhaustion U) :
    compactExhaustIntExt U H D = Uniqueness.TwoScale.S36.intExt D U := by
  classical
  funext u v
  by_cases hu : u ∈ U
  · by_cases hv : v ∈ U
    · have h := internal_eq_iInf_compactPathInf_of_forget D hforget H
        (⟨u, hu⟩ : U) (⟨v, hv⟩ : U)
      simpa only [compactExhaustIntExt, hu, hv, and_self,
        ↓reduceIte, Uniqueness.TwoScale.S36.internal_eq_intExt] using h.symm
    · rw [show compactExhaustIntExt U H D u v = ∞ by
        simp [compactExhaustIntExt, hv]]
      exact (Uniqueness.TwoScale.S36.intExt_eq_top_of_not_mem_right
        (D := D) (Y := U) u hv).symm
  · rw [show compactExhaustIntExt U H D u v = ∞ by
      simp [compactExhaustIntExt, hu]]
    exact (Uniqueness.TwoScale.S36.intExt_eq_top_of_not_mem_left
      (D := D) (Y := U) v hu).symm

 


theorem lscInternalFam_ae_borel_version_open
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → LSCMetric} (hD : Measurable D)
    (hsmall : ∀ᵐ ω ∂P, ∀ u : ℂ, ∀ δ : ℝ, 0 < δ →
      ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, (D ω).1 (u, v) < ENNReal.ofReal η → dist u v < δ)
    (V : TopologicalSpace.Opens ℂ) :
    ∃ F : Ω → ℂ → ℂ → ℝ≥0∞, Measurable F ∧
      ∀ᵐ ω ∂P, F ω = lscInternalFam D ω (V : Set ℂ) := by
  letI : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  let H : CompactExhaustion V := CompactExhaustion.choice V
  refine ⟨fun ω => compactExhaustIntExt V H (D ω),
    (compactExhaustIntExt_measurable V H).comp hD, ?_⟩
  filter_upwards [hsmall] with ω hω
  exact compactExhaustIntExt_eq_intExt (D ω)
    (continuous_euclidForget_of_small_metric (D ω) hω) H

end SupercriticalLQGUniqueness.B2.PfeLocal
