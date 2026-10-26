import SupercriticalLFPPAS.ContractionStep.GoodDisk
import SupercriticalLFPPAS.Iteration.Recursion

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric.MetricGeometry
open SupercriticalLFPPAS.Core
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.Polylog

namespace SupercriticalLFPPAS.ContractionStep

/-- Restricting and shifting a unit-speed geodesic preserves the `IsGeodIn` data. -/
theorem shift_isGeodIn {d : LSCMetric} {P : ℝ → ℂ} {T R s t : ℝ}
    (hgeo : IsGeodIn d P T R) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    IsGeodIn d (fun u => P (s + u)) (t - s) R := by
  have hL : 0 ≤ t - s := sub_nonneg.mpr hst
  have hdist : ∀ u ∈ Icc 0 (t - s), ∀ v ∈ Icc 0 (t - s),
      edist ((d.pt ∘ fun u => P (s + u)) u) ((d.pt ∘ fun u => P (s + u)) v) = edist u v := by
    intro u hu v hv
    have hu' : s + u ∈ Icc 0 T := by
      constructor
      · linarith [hu.1]
      · calc s + u ≤ s + (t - s) := add_le_add_right hu.2 s
          _ = t := by ring
          _ ≤ T := ht
    have hv' : s + v ∈ Icc 0 T := by
      constructor
      · linarith [hv.1]
      · calc s + v ≤ s + (t - s) := add_le_add_right hv.2 s
          _ = t := by ring
          _ ≤ T := ht
    rcases le_total u v with huv | hvu
    · have he := hgeo.1.edist_eq_of_hasUnitSpeedOn hgeo.2.1 hu' hv' (by linarith)
      simpa [Function.comp_apply, edist_dist, dist_eq_norm, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr huv)] using he
    · have he := hgeo.1.edist_eq_of_hasUnitSpeedOn hgeo.2.1 hv' hu' (by linarith)
      rw [edist_comm] at he
      simpa [Function.comp_apply, edist_dist, dist_eq_norm, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hvu)] using he
  have hgeoQ := isGeodesicCurve_of_edist_eq hL hdist
  have hcont : ContinuousOn (fun u => P (s + u)) (Icc 0 (t - s)) := by
    exact hgeo.2.2.1.comp (continuousOn_const.add continuousOn_id) (by
      intro u hu
      constructor
      · linarith [hs, hu.1]
      · nlinarith [hu.2])
  refine ⟨hgeoQ.1, hgeoQ.2, hcont, ?_⟩
  intro u hu
  apply hgeo.2.2.2 (s + u)
  constructor <;> nlinarith [hs, ht, hu.1, hu.2]

/-- Pointwise good root scales along every geodesic imply the one-step contraction for all
subsegments, by restricting to each subsegment before applying Lemma 4.1. -/
theorem compIn_contract_of_goodScales
    (h41 : Lemma41Stmt) (d d' : LSCMetric) (R C d₀ η A K rmin rmax ρold : ℝ)
    (hC : 0 ≤ C)
    (hη : 0 < η) (hηsmall : 2 * Real.sqrt η < 1 / 10) (hd₀ : 0 ≤ d₀)
    (hA : 1 ≤ A) (hK : 0 ≤ K) (hrmin : 0 < rmin) (hrange : rmin ≤ rmax)
    (hscale : 513 * rmax ≤ 1) (hρ : 0 < ρold) (hρsmall : ρold < η * rmin / 4)
    (hGS : ∀ (P : ℝ → ℂ) (T : ℝ), IsGeodIn d P T R → ∀ u ∈ Icc 0 T,
      ∃ c r, ∃ hr : 0 < r, dist c (P u) < rmin / 10 ∧ r ∈ Icc rmin rmax ∧
        GoodScale d d' c r hr η d₀ A K)
    (hprior : CompIn d d' (ball 0 (R + 2)) R C ρold) :
    CompIn d d' (ball 0 (R + 2)) R
      (Iteration.contractionFactor C K (1 / (5 * A)) d₀) (513 * rmax) := by
  intro P T hgeo s t hs hst ht
  let Q : ℝ → ℂ := fun u => P (s + u)
  have hQgeo : IsGeodIn d Q (t - s) R := by
    simpa [Q] using shift_isGeodIn hgeo hs hst ht
  have hQgood : ∀ u ∈ Icc 0 (t - s),
      ∃ c r, dist c (Q u) < rmin / 10 ∧ r ∈ Icc rmin rmax ∧
        GoodDiskIn d d' (ball 0 (R + 2)) Q (t - s) η d₀ A K c r := by
    intro u hu
    obtain ⟨c, r, hrpos, hclose, hr, hgood⟩ := hGS Q (t - s) hQgeo u hu
    have hcNorm : ‖c‖ < R + rmin / 10 := by
      have hPu := hQgeo.2.2.2 u hu
      have hdist : dist (Q u) c < rmin / 10 := by simpa [dist_comm] using hclose
      have htriangle : ‖c‖ ≤ ‖Q u‖ + dist (Q u) c := by
        calc
          ‖c‖ = ‖(c - Q u) + Q u‖ := by congr 1; abel
          _ ≤ ‖c - Q u‖ + ‖Q u‖ := norm_add_le _ _
          _ = dist (Q u) c + ‖Q u‖ := by rw [dist_eq_norm, norm_sub_rev]
          _ = ‖Q u‖ + dist (Q u) c := by ring
      have hPuNorm : ‖Q u‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hPu
      exact lt_of_le_of_lt htriangle (add_lt_add hPuNorm hdist)
    have hV : closedAnn c (r / 8) (16 * r) ⊆ ball (0 : ℂ) (R + 2) := by
      intro x hx
      have hx' : dist (x : ℂ) c ≤ 16 * r := by
        change r / 8 ≤ ‖(x : ℂ) - c‖ ∧ ‖(x : ℂ) - c‖ ≤ 16 * r at hx
        simpa [dist_eq_norm] using hx.2
      have hxtri : ‖(x : ℂ)‖ ≤ dist (x : ℂ) c + ‖c‖ := by
        calc
          ‖(x : ℂ)‖ = ‖((x : ℂ) - c) + c‖ := by congr 1; abel
          _ ≤ ‖(x : ℂ) - c‖ + ‖c‖ := norm_add_le _ _
          _ = dist (x : ℂ) c + ‖c‖ := by rw [dist_eq_norm]
      have hrmax : r ≤ rmax := hr.2
      have hrminmax : rmin ≤ rmax := hrange
      have hbound' : 16 * r + rmin / 10 ≤ (161 / 10 : ℝ) * rmax := by nlinarith
      have hrmaxpos : 0 < rmax := lt_of_lt_of_le hrmin hrange
      have hfac : (161 / 10 : ℝ) < 513 := by norm_num
      have hfac' : (161 / 10 : ℝ) * rmax < 513 * rmax :=
        mul_lt_mul_of_pos_right hfac hrmaxpos
      have hbound : 16 * r + rmin / 10 < 1 :=
        (hbound'.trans_lt hfac').trans_le hscale
      have : ‖(x : ℂ)‖ < R + 2 := by
        calc
          ‖(x : ℂ)‖ ≤ dist (x : ℂ) c + ‖c‖ := hxtri
          _ ≤ 16 * r + ‖c‖ := by simpa [add_comm] using add_le_add_right hx' ‖c‖
          _ < 16 * r + (R + rmin / 10) := by linarith [hcNorm]
          _ < R + 2 := by nlinarith [hbound]
      simpa [Metric.mem_ball, dist_eq_norm] using this
    have hLocal : ∀ p ∈ Q '' Icc 0 (t - s), ball p (r / 10) ⊆ ball (0 : ℂ) (R + 2) := by
      intro p hp y hy
      rcases hp with ⟨u, hu, rfl⟩
      have huR := hQgeo.2.2.2 u hu
      have hydist : dist y (Q u) < r / 10 := by simpa [Metric.mem_ball] using hy
      have htri : ‖y‖ ≤ dist y (Q u) + ‖Q u‖ := by
        calc
          ‖y‖ = ‖(y - Q u) + Q u‖ := by congr 1; abel
          _ ≤ ‖y - Q u‖ + ‖Q u‖ := norm_add_le _ _
          _ = dist y (Q u) + ‖Q u‖ := by rw [dist_eq_norm]
      have hrlt : r / 10 < 1 := by nlinarith [hr.2, hscale]
      have huNorm : ‖Q u‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using huR
      have hyR : ‖y‖ < R + 2 := by nlinarith [htri, hydist, huNorm, hrlt]
      simpa [Metric.mem_ball, dist_eq_norm] using hyR
    exact ⟨c, r, hclose, hr, goodScale_to_goodDiskIn d d' (ball 0 (R + 2)) R Q (t - s)
      η d₀ A K c r hrpos hQgeo hgood hV hLocal hηsmall hd₀ hK⟩
  have hpriorQ : ∀ u v, 0 ≤ u → u ≤ v → v ≤ t - s →
      d'.internalSetDist (ball 0 (R + 2))
        {y | (y : ℂ) ∈ ball (Q u) ρold} {y | (y : ℂ) ∈ ball (Q v) ρold} ≤
          ENNReal.ofReal (C * (v - u)) := by
    intro u v hu huv hv
    have hsub := hprior P T hgeo (s + u) (s + v) (by linarith)
      (by linarith) (by linarith [hv])
    simpa [Q] using hsub
  have hbounded : Bornology.IsBounded (ball (0 : ℂ) (R + 2)) := Metric.isBounded_ball
  have hconvex : Convex ℝ (ball (0 : ℂ) (R + 2)) := convex_ball _ _
  have hsubset : ball (0 : ℂ) (R + 1) ⊆ ball (0 : ℂ) (R + 2) := by
    intro z hz
    have hz' : ‖z‖ < R + 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hz'' : ‖z‖ < R + 2 := lt_trans hz' (by linarith)
    simpa [Metric.mem_ball, dist_eq_norm] using hz''
  have h41result := h41 d d' (ball 0 (R + 2)) R hbounded hconvex hsubset Q (t - s) hQgeo
    η d₀ A K C rmin rmax ρold hη hηsmall hd₀ hA hK hC hrmin hrange hscale hρ hρsmall
    hQgood hpriorQ
  simpa [Q, Iteration.contractionFactor] using h41result

end SupercriticalLFPPAS.ContractionStep
