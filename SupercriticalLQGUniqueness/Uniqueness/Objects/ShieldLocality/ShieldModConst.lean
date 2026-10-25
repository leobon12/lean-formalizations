import SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality.ShieldRawLocal
import SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality.ShieldScale
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.BarrierScale
import LQGMetric.Field.GermSplitA




 







set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory
open LQGMetric.Blueprint
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality

def shieldWindow (t : ℝ) : TopologicalSpace.Opens ℂ :=
  annulus 0 ((22 / 25) * t) ((88 / 25) * t)

private theorem shieldWindow_nonempty (t : ℝ) (ht : 0 < t) :
    (shieldWindow t : Set ℂ).Nonempty := by
  refine ⟨(t : ℂ), ?_⟩
  change (22 / 25) * t < ‖(t : ℂ) - 0‖ ∧
    ‖(t : ℂ) - 0‖ < (88 / 25) * t
  simp only [sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  constructor <;> nlinarith only [ht]

theorem shieldClosed_subset_window (t : ℝ) (ht : 0 < t) :
    BiLipschitz.Barrier.closedAnn 0 (2 * t) (3 * t) ⊆ (shieldWindow t : Set ℂ) := by
  intro x hx
  change 2 * t ≤ ‖x - 0‖ ∧ ‖x - 0‖ ≤ 3 * t at hx
  change (22 / 25) * t < ‖x - 0‖ ∧ ‖x - 0‖ < (88 / 25) * t
  constructor <;> nlinarith only [ht, hx.1, hx.2]

theorem shieldAnn_subset_window (t : ℝ) (ht : 0 < t) :
    EuclideanAnnulus.toSet
      (⟨(0, t, 2 * t), ht, by linarith⟩ : EuclideanAnnulus) ⊆
        (shieldWindow t : Set ℂ) := by
  intro x hx
  change x ∈ ball 0 (2 * t) \ closure (ball 0 t) at hx
  rw [closure_ball 0 ht.ne'] at hx
  simp only [mem_sdiff, mem_ball, mem_closedBall, not_le, dist_eq_norm] at hx
  change (22 / 25) * t < ‖x - 0‖ ∧ ‖x - 0‖ < (88 / 25) * t
  constructor <;> nlinarith only [ht, hx.1, hx.2]

 
theorem aeEventIn_shieldAt_modConst_open
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants)
    (t : ℝ) (ht : 0 < t) :
    AEEventIn μ (fieldSigma0On id (shieldWindow t))
      {g | Objects.Excursions.shieldAt C (D g) t} := by
  let U := shieldWindow t
  obtain ⟨ψ, hψU, hψ1⟩ :=
    LQGMetric.GermSplit.exists_test_unit (shieldWindow_nonempty t ht)
  have hwhole : LQGMetric.IsGFFPlusCont
      (id : LQGMetric.DistC → LQGMetric.DistC) μ :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hμ.1
  let G := LQGMetric.CONF.normIn (id : LQGMetric.DistC → LQGMetric.DistC) ψ
  have hG : LQGMetric.IsGFFPlusCont G μ :=
    Toolkit.LocalEvents.isGFFPlusCont_normIn hwhole ψ
  have hQ : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  have hB := BiLipschitz.Barrier.ae_barrier hD hQ μ id hμ
  have hscale := Positivity.Witnesses.ae_addConst_eq_mul μ id hwhole ξ Q D hD
    (fun g => -(g ψ))
  have hBG : ∀ᵐ g ∂μ, BiLipschitz.Barrier.Barrier (D (G g)) := by
    filter_upwards [hB, hscale] with g hb hc
    let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ)))
    exact Objects.ProbabilityS3.barrier_of_dist_scale (D g) (D (G g)) e
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
      ENNReal.ofReal_ne_top (fun x y => hc (x, y)) hb
  have hLocal := aeEventIn_shieldAt_open_of_barrier μ G hG ξ Q D hD hBG
    C t ht U (shieldClosed_subset_window t ht) (shieldAnn_subset_window t ht)
  have hLocal0 := Toolkit.LocalEvents.aeEventIn_fieldSigma0On_of_normIn
    (id : LQGMetric.DistC → LQGMetric.DistC) ψ hψ1 U hψU hLocal
  have hEq := ae_shieldAt_addConst_iff μ hμ ξ Q D hD C t
    (fun g => -(g ψ))
  obtain ⟨R, hRm, hGR⟩ := hLocal0
  refine ⟨R, hRm, ?_⟩
  filter_upwards [hEq, hGR] with g he hR
  exact propext (he.symm.trans (Iff.of_eq hR))

end SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality
