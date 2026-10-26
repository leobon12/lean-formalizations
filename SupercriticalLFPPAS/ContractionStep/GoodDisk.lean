import SupercriticalLFPPAS.Core.Interfaces
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MetricLemmas
import LQGMetric.Metric.Geodesic

/-! Local adapters used by the §4.2 contraction step. -/

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric.MetricGeometry
open SupercriticalLQGUniqueness.B2.Polylog

namespace SupercriticalLFPPAS.ContractionStep

open SupercriticalLFPPAS.Core
open SupercriticalLQGUniqueness

/-- The good-scale bounds are monotone in the comparison factor. -/
theorem goodScale_mono_K
    {d d' : LSCMetric} {c : ℂ} {r : ℝ} (hr : 0 < r) {η d₀ A K₀ K₁ : ℝ}
    (hd₀ : 0 ≤ d₀) (hK : K₀ ≤ K₁)
    (h : GoodScale d d' c r hr η d₀ A K₀) :
    GoodScale d d' c r hr η d₀ A K₁ := by
  have hfac : (1 + d₀ / 10) * K₀ ≤ (1 + d₀ / 10) * K₁ :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  have hfac' : ENNReal.ofReal ((1 + d₀ / 10) * K₀) ≤
      ENNReal.ofReal ((1 + d₀ / 10) * K₁) := ENNReal.ofReal_le_ofReal hfac
  have hb : d₀ / 10 * K₀ ≤ d₀ / 10 * K₁ :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  have hb' : ENNReal.ofReal (d₀ / 10 * K₀) ≤ ENNReal.ofReal (d₀ / 10 * K₁) :=
    ENNReal.ofReal_le_ofReal hb
  refine ⟨h.ratio, ?_, ?_⟩
  · intro u v hu hv htime
    exact (h.cross u v hu hv htime).trans
      (mul_le_mul_of_nonneg_right hfac' bot_le)
  · intro P α β hgeo hcont p hp hmem hleft hright
    rcases h.surround P α β hgeo hcont p hp hmem hleft hright with
      ⟨σ, a', b', hcurve, hcurveCont, hsmall, hpNot, hball, hbounded, hlen⟩
    refine ⟨σ, a', b', hcurve, hcurveCont, hsmall, hpNot, hball, hbounded, ?_⟩
    exact hlen.trans (mul_le_mul_of_nonneg_right hb' bot_le)

/-- Enlarging the carrier of an internal set distance can only decrease it. -/
theorem internalSetDist_mono_domain (d : LSCMetric) {U V : Set ℂ} (hUV : U ⊆ V)
    (K₁ K₂ : Set ℂ) :
    d.internalSetDist V (Subtype.val ⁻¹' K₁) (Subtype.val ⁻¹' K₂) ≤
      d.internalSetDist U (Subtype.val ⁻¹' K₁) (Subtype.val ⁻¹' K₂) := by
  classical
  unfold LSCMetric.internalSetDist
  apply le_iInf
  intro x
  apply le_iInf
  intro hx
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  let xV : V := ⟨(x : ℂ), hUV x.property⟩
  let yV : V := ⟨(y : ℂ), hUV y.property⟩
  have hInt : d.internal V (xV, yV) ≤ d.internal U (x, y) := by
    unfold LSCMetric.internal
    apply le_iInf
    intro P
    apply le_iInf
    intro a
    apply le_iInf
    intro b
    apply le_iInf
    intro hP
    apply le_iInf
    intro hY
    apply le_iInf
    intro ha
    apply le_iInf
    intro hb
    apply iInf_le_of_le P
    apply iInf_le_of_le a
    apply iInf_le_of_le b
    apply iInf_le_of_le hP
    apply iInf_le_of_le (fun t ht => hUV (hY t ht))
    apply iInf_le_of_le ha
    apply iInf_le_of_le hb
    exact le_rfl
  apply iInf_le_of_le xV (iInf_le_of_le hx (iInf_le_of_le yV (iInf_le_of_le hy hInt)))

/-- A geodesic-independent good scale gives the geodesic-relative data needed by Lemma 4.1. -/
theorem goodScale_to_goodDiskIn
    (d d' : LSCMetric) (W : Set ℂ) (R : ℝ) (P : ℝ → ℂ) (L : ℝ)
    (η d₀ A Kf : ℝ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hgeo : IsGeodIn d P L R)
    (hGS : GoodScale d d' c r hr η d₀ A Kf)
    (hV : closedAnn c (r / 8) (16 * r) ⊆ W)
    (hLocal : ∀ p ∈ P '' Icc 0 L, ball p (r / 10) ⊆ W)
    (hEta : 2 * Real.sqrt η < 1 / 10)
    (hd₀ : 0 ≤ d₀) (hK : 0 ≤ Kf) :
    GoodDiskIn d d' W P L η d₀ A Kf c r := by
  classical
  refine ⟨hr, hGS.ratio, ?_, ?_⟩
  · intro s t hs hst ht hps hpt hPath hTime
    let u : closedAnn c (r / 2) (3 * r) :=
      ⟨P s, by
        change r / 2 ≤ ‖P s - c‖ ∧ ‖P s - c‖ ≤ 3 * r
        have hps' : ‖P s - c‖ = r := by simpa [dist_eq_norm] using hps
        rw [hps']
        constructor <;> linarith⟩
    let v : closedAnn c (r / 2) (3 * r) :=
      ⟨P t, by
        change r / 2 ≤ ‖P t - c‖ ∧ ‖P t - c‖ ≤ 3 * r
        have hpt' : ‖P t - c‖ = 2 * r := by simpa [dist_eq_norm] using hpt
        rw [hpt']
        constructor <;> linarith⟩
    have hCurve : d.IsCurve P s t := by
      refine ⟨hst, ?_⟩
      apply hgeo.1.2.1.mono
      exact Icc_subset_Icc (show 0 ≤ s from hs) ht
    have hInside : ∀ u ∈ Icc s t, P u ∈ closedAnn c (r / 2) (3 * r) := by
      intro u' hu'
      have hu := hPath u' hu'
      change r ≤ ‖P u' - c‖ ∧ ‖P u' - c‖ ≤ 2 * r at hu
      change r / 2 ≤ ‖P u' - c‖ ∧ ‖P u' - c‖ ≤ 3 * r
      exact ⟨by linarith, by linarith⟩
    have hInternal : d.internal (closedAnn c (r / 2) (3 * r)) (u, v) ≤ ENNReal.ofReal (t - s) := by
      calc
        d.internal (closedAnn c (r / 2) (3 * r)) (u, v) ≤ d.len P s t := by
          simpa [u, v] using d.internal_le_len (closedAnn c (r / 2) (3 * r)) P s t hCurve hInside
        _ = ENNReal.ofReal (t - s) := by
          change LQGMetric.MetricGeometry.curveLength (d.pt ∘ P) s t = _
          exact LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn hgeo.2.1
            ⟨hs, hst.trans ht⟩ ⟨hs.trans hst, ht⟩
    have hcross := hGS.cross u v hps hpt (hInternal.trans hTime)
    have hcoef : 0 ≤ (1 + d₀ / 10) * Kf := by positivity
    have hmul := mul_le_mul_of_nonneg_left hInternal
      (show (0 : ENNReal) ≤ ENNReal.ofReal ((1 + d₀ / 10) * Kf) by positivity)
    have hscaled : ENNReal.ofReal ((1 + d₀ / 10) * Kf) * ENNReal.ofReal (t - s) =
        ENNReal.ofReal ((1 + d₀ / 10) * Kf * (t - s)) :=
      (ENNReal.ofReal_mul hcoef).symm
    calc
      d'.internalSetDist W {x | (x : ℂ) ∈ ball (P s) (η * r / 2)}
          {x | (x : ℂ) ∈ ball (P t) (η * r / 2)}
          ≤ d'.internalSetDist (closedAnn c (r / 8) (16 * r))
          {x | (x : ℂ) ∈ ball (P s) (η * r / 2)} {x | (x : ℂ) ∈ ball (P t) (η * r / 2)} := by
            apply internalSetDist_mono_domain d' hV
      _ ≤ ENNReal.ofReal ((1 + d₀ / 10) * Kf) * d.internal (closedAnn c (r / 2) (3 * r)) (u, v) := hcross
      _ ≤ ENNReal.ofReal ((1 + d₀ / 10) * Kf) * ENNReal.ofReal (t - s) := hmul
      _ = ENNReal.ofReal ((1 + d₀ / 10) * Kf * (t - s)) := hscaled
  · intro α β p hα hαβ hβ hp hHit hleft hright
    have hGeoSub : LQGMetric.MetricGeometry.IsGeodesicCurve (d.pt ∘ P) α β := by
      have hfin : edist ((d.pt ∘ P) 0) ((d.pt ∘ P) L) ≠ ⊤ := by
        rw [← hgeo.1.2.2]
        rw [LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn hgeo.2.1
          ⟨le_rfl, hgeo.1.1⟩ ⟨hgeo.1.1, le_rfl⟩]
        exact ENNReal.ofReal_ne_top
      refine ⟨hαβ, hgeo.1.2.1.mono (Icc_subset_Icc hα hβ), ?_⟩
      exact LQGMetric.MetricGeometry.curveLength_eq_edist_of_subinterval
        hgeo.1.2.2 hfin hα hαβ hβ
    have hPcont : ContinuousOn P (Icc α β) := hgeo.2.2.1.mono (Icc_subset_Icc hα hβ)
    have hSphere : p ∈ sphere c r ∪ sphere c (2 * r) := by
      rcases hHit with hpR | hp2R
      · exact Or.inl (by change dist p c = r; simpa [dist_comm] using hpR)
      · exact Or.inr (by change dist p c = 2 * r; simpa [dist_comm] using hp2R)
    obtain ⟨σ, a', b', hCurve', hCont', hSmall, hpNot, hBallComp, hBounded, hLen⟩ :=
      hGS.surround P α β hGeoSub hPcont p hSphere hp hleft hright
    have hSmall' : σ '' Icc a' b' ⊆ ball p (r / 10) := by
      apply Set.Subset.trans hSmall
      apply Metric.ball_subset_ball
      nlinarith [hEta, Real.sqrt_nonneg η]
    have hpGlobal : p ∈ P '' Icc 0 L := by
      rcases hp with ⟨u, hu, rfl⟩
      exact ⟨u, ⟨hα.trans hu.1, hu.2.trans hβ⟩, rfl⟩
    have hWcurve : σ '' Icc a' b' ⊆ W := hSmall'.trans (hLocal p hpGlobal)
    have hLen' : d'.len σ a' b' ≤ ENNReal.ofReal (d₀ / 10 * Kf * (β - α)) := by
      have hlenP : d.len P α β = ENNReal.ofReal (β - α) := by
        change LQGMetric.MetricGeometry.curveLength (d.pt ∘ P) α β = _
        exact LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn hgeo.2.1
          ⟨hα, hαβ.trans hβ⟩ ⟨hα.trans hαβ, hβ⟩
      have hcoef : 0 ≤ d₀ / 10 * Kf := by positivity
      calc
        d'.len σ a' b' ≤ ENNReal.ofReal (d₀ / 10 * Kf) * d.len P α β := hLen
        _ = ENNReal.ofReal (d₀ / 10 * Kf) * ENNReal.ofReal (β - α) := by rw [hlenP]
        _ = ENNReal.ofReal (d₀ / 10 * Kf * (β - α)) := (ENNReal.ofReal_mul hcoef).symm
    exact ⟨σ, a', b', hCurve', hCont', hSmall', hWcurve, hpNot, hBallComp, hBounded, hLen'⟩

end SupercriticalLFPPAS.ContractionStep
