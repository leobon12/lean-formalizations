import HigherDimLQGMetric.Limits.BoundedWeylCompare
import HigherDimLQGMetric.Sec10.Basic
import HigherDimLQGMetric.Field.Measurable

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Topology Filter
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Remark 3.8(b), conditional only on the Weyl identity for the limiting
assignment. The identity is the A21(4) input, proved later in the assembly. -/
theorem l6c_remark38_bounded_of_weyl {d : ℕ}
    (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 ≤ ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (g : Ω → C(Rd d, ℝ)) (hg : Measurable g)
    (hgb : ∀ᵐ ω ∂P, ∃ G : ℝ, ∀ x, |g ω x| ≤ G)
    (D Dg : Ω → ContMetric d) (hDg : Measurable Dg)
    (hLen : ∀ᵐ ω ∂P, (D ω).IsLength)
    (hW : ∀ᵐ ω ∂P, IsWeylOf ξ (g ω) (D ω) (Dg ω))
    (c : ℝ → ℝ) (hc : ∀ r, 0 < r → 0 < c r)
    (hPure : TightFamily P
      (fun r ω => normalizedAtScale ξ (fun _ => D ω) c (h ω) r) (Ioi 0)) :
    TightFamily P
      (fun r ω => normalizedAtScale ξ (fun _ => Dg ω) c
        (addFun (h ω) (g ω)) r) (Ioi 0) := by
  let A : ℝ → Ω → C(Rd d × Rd d, ℝ) :=
    fun r ω => normalizedAtScale ξ (fun _ => D ω) c (h ω) r
  let B : ℝ → Ω → C(Rd d × Rd d, ℝ) :=
    fun r ω => normalizedAtScale ξ (fun _ => Dg ω) c (addFun (h ω) (g ω)) r
  let M : Ω → ℝ := fun ω => ξ * (2 * s8a_supAbs (g ω))
  have hMm : Measurable M :=
    measurable_const.mul (measurable_const.mul (s8a_measurable_supAbs hg))
  have hpmeas : Measurable (fun ω => addFun (h ω) (g ω)) :=
    measurable_addFun.comp (hh.1.measurable.prodMk hg)
  have hBm : ∀ r ∈ Ioi (0 : ℝ), AEMeasurable (B r) P := by
    intro r _
    have hs : Measurable (fun ω =>
        (c r)⁻¹ * Real.exp (-ξ * sphereAvg (addFun (h ω) (g ω)) r 0)) :=
      measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul ((measurable_sphereAvg_left r 0).comp hpmeas)))
    exact (hs.smul ((ContinuousMap.continuous_precomp _).measurable.comp
      (measurable_subtype_coe.comp hDg))).aemeasurable
  have hAalg : ∀ r ∈ Ioi (0 : ℝ), ∀ᵐ ω ∂P, A r ω ∈ metricAlgSet_select := by
    intro r hr
    exact ae_of_all _ fun ω =>
      let hm := s8a_normalizedAtScale_isContinuousMetric ξ (fun _ => D ω) c
        (h ω) hr (hc r hr)
      ⟨hm.self_eq_zero, hm.symm, hm.triangle⟩
  have hBalg : ∀ r ∈ Ioi (0 : ℝ), ∀ᵐ ω ∂P, B r ω ∈ metricAlgSet_select := by
    intro r hr
    exact ae_of_all _ fun ω =>
      let hm := s8a_normalizedAtScale_isContinuousMetric ξ (fun _ => Dg ω) c
        (addFun (h ω) (g ω)) hr (hc r hr)
      ⟨hm.self_eq_zero, hm.symm, hm.triangle⟩
  have hcmp : ∀ r ∈ Ioi (0 : ℝ), ∀ᵐ ω ∂P, ∀ p : Rd d × Rd d,
      Real.exp (-M ω) * A r ω p ≤ B r ω p ∧
      B r ω p ≤ Real.exp (M ω) * A r ω p := by
    intro r hr
    filter_upwards [hLen, hW, hgb,
      hh.1.ae_exists_tendsto_sphereAvgSeq hd hr 0] with ω hL hWω ⟨G, hG⟩ ⟨a, ha⟩ p
    have hG' : ∀ x, |g ω x| ≤ s8a_supAbs (g ω) :=
      s8a_abs_le_supAbs hG
    have hseq : Tendsto (sphereAvgSeq (h ω) r 0) atTop
        (𝓝 (sphereAvg (h ω) r 0)) := tendsto_sphereAvgSeq_sphereAvg ⟨a, ha⟩
    simpa only [A, B, M, normalizedAtScale, ContinuousMap.smul_apply,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk, smul_eq_mul, neg_mul] using
      l6c_normalized_weyl_bdd_compare (by omega : 1 ≤ d) hξ
        (h ω) (g ω) (D ω) (Dg ω) hL hWω r (c r)
        (s8a_supAbs (g ω)) hr (hc r hr) hseq hG' p.1 p.2
  exact l6c_tightFamily_of_randomCompare P A B (Ioi 0) hPure hBm
    hAalg hBalg M hMm hcmp

end HigherDimLQGMetric
