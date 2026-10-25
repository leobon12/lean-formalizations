import SupercriticalLQGUniqueness.B2.PfeAxioms.RecenteredLocalitySB
import SupercriticalLQGUniqueness.B2.DG20Lim.GeometryTransferC
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalityNormalizedSkC
import SupercriticalLQGUniqueness.B2.PfeAxioms.RecenteredGeometrySB
import SupercriticalLQGUniqueness.B2.PfeAxioms.RecenteredAnnulusSB
import SupercriticalLQGUniqueness.B2.PfeAxioms.W3MeasurableShiftSkC

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set LQGMetric
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem xiAdditiveLocality_of_dg20LimitSkC_w3
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hSkSB : B2.DG20Lim.DG20LimitSkC)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (hgeo : ∀ k : ℕ, PfeWeyl.AcrossTailInput P (fun ω => D (h ω))
      ((k : ℝ) + 1) (Nat.cast_add_one_pos k))
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P,
      PfeWeyl.SmallAnnulusCosts
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (D (h ω)) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)))
    (hAnn : ∀ K V : Set ℂ,
      IsCompact K → IsOpen V → IsCompact (closure V) → K ⊆ V →
      ∀ᵐ ω ∂P, PfeWeyl.SmallAnnulusCosts
        (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m (ε k)) (X (ε k) ω)) (D (h ω)) K V) :
    B2.PfeLocal.Inputs.LscXiAdditiveLocality (ξ : ℝ) P h
      (fun ω => D (h ω)) := by
  refine ⟨jointlyLocal_internal_of_dg20LimitSkC hSkSB
    ξ Q hQ m hm ε hε D hD P h hh X hX hAnn, ?_⟩
  intro z r hr
  let g : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) r z)
  have hg : IsGFFPlusBddCont g P := isGFFPlusBddCont_recentered hh r z
  let Y : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ) := fun δ =>
    Classical.choose (exists_heatVersion_bdd hg δ)
  have hY : ∀ δ, IsHeatSmoothing P g δ (Y δ) := fun δ =>
    (Classical.choose_spec (exists_heatVersion_bdd hg δ)).2
  have hc : Measurable (fun ω => -circleAvg (h ω) r z) :=
    ((LQGMetric.measurable_circleAvg_left r z).comp hh.1.measurable).neg
  have hScale := ae_addConst_eq_scale_of_dg20LimitSkC_w3 hSkSB
    ξ Q hQ m hm ε hε D hD P h hh X hX hgeo hsmall
    (fun ω => -circleAvg (h ω) r z) hc
  have hBase := B2.DG20Lim.limitEuclideanControl0_of_dg20LimitSkC hSkSB
    ξ Q hQ m ε D hm hε hD P h hh
  have hGeom : ∀ᵐ ω ∂P,
      ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ,
          D (g ω) (u, v) < ENNReal.ofReal η → dist u v < δ := by
    filter_upwards [hBase, hScale] with ω hBω hSω
    exact euclideanControl_of_positive_scale (D (h ω)) (D (g ω))
      (Real.exp ((ξ : ℝ) * -circleAvg (h ω) r z))
      (Real.exp_pos _) hSω hBω
  have hAnnG : ∀ K V : Set ℂ,
      IsCompact K → IsOpen V → IsCompact (closure V) → K ⊆ V →
      ∀ᵐ ω ∂P, PfeWeyl.SmallAnnulusCosts
        (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m (ε k)) (Y (ε k) ω)) (D (g ω)) K V := by
    intro K V hK hV hVc hKV
    have hFinite := ae_recentered_finiteLFPP_scale
      (ξ : ℝ) m ε P h hh X Y hX r z hY
    filter_upwards [hAnn K V hK hV hVc hKV, hScale, hFinite] with ω hA hDω hFω
    apply smallAnnulusCosts_of_positive_scale
      (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
        (m (ε k)) (X (ε k) ω))
      (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
        (m (ε k)) (Y (ε k) ω))
      (D (h ω)) (D (g ω))
      (Real.exp ((ξ : ℝ) * -circleAvg (h ω) r z))
      (Real.exp_pos _) hDω ?_ K V hA
    exact Filter.Eventually.of_forall (fun k p => hFω k p)
  have hLocal := jointlyLocal_internal_bdd_of_geometry_annulus
    ξ m ε hε D hD P g hg Y hY hGeom hAnnG
  apply LQGMetric.GM.Bilip.isJointlyLocalFam_congr hLocal
  · filter_upwards [hScale] with ω hω
    intro V hV
    funext u v
    let k : ℝ≥0∞ := ENNReal.ofReal
      (Real.exp ((ξ : ℝ) * -circleAvg (h ω) r z))
    have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have hkt : k ≠ ⊤ := ENNReal.ofReal_ne_top
    change B2.PfeLocal.lscNormIntFam (ξ : ℝ) h
      (fun ω => D (h ω)) z r ω V u v =
      B2.PfeLocal.lscInternalFam (fun ω => D (g ω)) ω V u v
    simp only [B2.PfeLocal.lscNormIntFam, B2.PfeLocal.lscInternalFam]
    convert (intExt_eq_mul_of_dist_scale (D (h ω)) (D (g ω))
      k hk0 hkt hω V u v).symm using 1
    · simp only [k, mul_neg]
      congr 2
      ring
  · filter_upwards [hScale] with ω hω
    intro V hV
    funext u v
    let k : ℝ≥0∞ := ENNReal.ofReal
      (Real.exp ((ξ : ℝ) * -circleAvg (h ω) r z))
    have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have hkt : k ≠ ⊤ := ENNReal.ofReal_ne_top
    change B2.PfeLocal.lscNormIntFam (ξ : ℝ) h
      (fun ω => D (h ω)) z r ω V u v =
      B2.PfeLocal.lscInternalFam (fun ω => D (g ω)) ω V u v
    simp only [B2.PfeLocal.lscNormIntFam, B2.PfeLocal.lscInternalFam]
    convert (intExt_eq_mul_of_dist_scale (D (h ω)) (D (g ω))
      k hk0 hkt hω V u v).symm using 1
    · simp only [k, mul_neg]
      congr 2
      ring

end SupercriticalLQGUniqueness.B2.PfeAxioms
