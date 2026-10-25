import SupercriticalLQGUniqueness.B2.PfeAxioms.RecenteredAnnulusSB
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalityBddSB

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem intExt_eq_mul_of_dist_scale
    (D E : LSCMetric) (k : ℝ≥0∞) (hk0 : k ≠ 0) (hkt : k ≠ ⊤)
    (hd : ∀ p : ℂ × ℂ, E p = k * D p)
    (V : Set ℂ) (u v : ℂ) :
    Uniqueness.TwoScale.S36.intExt E V u v =
      k * Uniqueness.TwoScale.S36.intExt D V u v := by
  unfold Uniqueness.TwoScale.S36.intExt
  simp only [Uniqueness.Positivity.Witnesses.isCurve_iff_of_dist_scale
    D E k hk0 hkt (fun x y => hd (x, y)),
    Uniqueness.Positivity.Witnesses.len_eq_mul_of_dist_scale
      D E k (fun x y => hd (x, y))]
  simp only [ENNReal.mul_iInf_of_ne hk0 hkt]

 


theorem xiAdditiveLocality_of_dg20LimitStrongSB_and_w3
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hStrong : Inputs.DG20LimitStrongSB)
    (hW3 : Inputs.BoundedWeylOnBaseEvent)
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
    (hAnn : ∀ K V : Set ℂ,
      IsCompact K → IsOpen V → IsCompact (closure V) → K ⊆ V →
      ∀ᵐ ω ∂P, PfeWeyl.SmallAnnulusCosts
        (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m (ε k)) (X (ε k) ω)) (D (h ω)) K V) :
    B2.PfeLocal.Inputs.LscXiAdditiveLocality (ξ : ℝ) P h
      (fun ω => D (h ω)) := by
  refine ⟨jointlyLocal_internal_of_dg20LimitStrongSB hStrong
    ξ Q hQ m hm ε hε D hD P h hh X hX hAnn, ?_⟩
  intro z r hr
  let g : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) r z)
  have hg : IsGFFPlusBddCont g P := isGFFPlusBddCont_recentered hh r z
  let Y : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ) := fun δ =>
    Classical.choose (exists_heatVersion_bdd hg δ)
  have hY : ∀ δ, IsHeatSmoothing P g δ (Y δ) := fun δ =>
    (Classical.choose_spec (exists_heatVersion_bdd hg δ)).2
  have hGeom := ae_euclideanControl_recentered_of_dg20LimitStrongSB
    hStrong hW3 ξ Q hQ m hm ε hε D hD P h hh r z
  have hAnnG : ∀ K V : Set ℂ,
      IsCompact K → IsOpen V → IsCompact (closure V) → K ⊆ V →
      ∀ᵐ ω ∂P, PfeWeyl.SmallAnnulusCosts
        (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m (ε k)) (Y (ε k) ω)) (D (g ω)) K V := by
    intro K V hK hV hVc hKV
    exact ae_smallAnnulusCosts_recentered_of_dg20LimitStrongSB
      hStrong hW3 ξ Q hQ m hm ε hε D hD P h hh X Y hX r z hY
      K V (hAnn K V hK hV hVc hKV)
  have hLocal := jointlyLocal_internal_bdd_of_geometry_annulus
    ξ m ε hε D hD P g hg Y hY hGeom hAnnG
  have hScale := ae_addConst_eq_scale_of_dg20LimitStrongSB hStrong hW3
    ξ Q hQ m hm ε hε D hD P h hh
    (fun ω => -circleAvg (h ω) r z)
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
