import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.ModConstOpen




 


set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric
open LQGMetric.Blueprint
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

private theorem inner_annulus_nonempty (w : ℂ) (s : ℝ) (hs : 0 < s) :
    (annulus w s (2*s) : Set ℂ).Nonempty := by
  refine ⟨w + ((3*s/2 : ℝ) : ℂ), ?_⟩
  change s < ‖w + ((3*s/2 : ℝ) : ℂ) - w‖ ∧
    ‖w + ((3*s/2 : ℝ) : ℂ) - w‖ < 2*s
  simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
  have hthree : 0 < 3*s/2 := by positivity
  rw [abs_of_pos hthree]
  constructor <;> nlinarith only [hs]

private theorem inner_annulus_subset_closed (w : ℂ) (s : ℝ) :
    (annulus w s (2*s) : Set ℂ) ⊆ BiLipschitz.Barrier.closedAnn w s (2*s) := by
  intro x hx
  exact ⟨hx.1.le, hx.2.le⟩

theorem aeEventIn_regGood_closed0
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants)
    (w : ℂ) (s : ℝ) (hs : 0 < s) :
    AEEventIn μ (fieldSigmaClosed0 id (BiLipschitz.Barrier.closedAnn w s (2*s)))
      {g | Objects.CorrectedEvent.regGood C (D g) s w} := by
  let K := BiLipschitz.Barrier.closedAnn w s (2*s)
  let V := annulus w s (2*s)
  obtain ⟨ψ, hψV, hψ1⟩ :=
    LQGMetric.GermSplit.exists_test_unit (inner_annulus_nonempty w s hs)
  have hψK : tsupport (ψ : ℂ → ℝ) ⊆ K :=
    hψV.trans (inner_annulus_subset_closed w s)
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
    exact barrier_of_dist_scale (D g) (D (G g)) e
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
      ENNReal.ofReal_ne_top (fun x y => hc (x,y)) hb
  have hLocal (n : ℕ) : AEEventIn μ
      (fieldSigma G (nbhdO (1 / ((n : ℝ) + 1)) K))
      {g | Objects.CorrectedEvent.regGood C (D (G g)) s w} := by
    let U := nbhdO (1 / ((n : ℝ) + 1)) K
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hKU : K ⊆ (U : Set ℂ) := Metric.self_subset_thickening hε K
    have hAU : EuclideanAnnulus.toSet
        (⟨(w, s, 2*s), hs, by linarith⟩ : EuclideanAnnulus) ⊆ (U : Set ℂ) := by
      intro x hx
      apply hKU
      change x ∈ ball w (2*s) \ closure (ball w s) at hx
      rw [closure_ball w hs.ne'] at hx
      simp only [mem_sdiff, mem_ball, mem_closedBall, not_le, dist_eq_norm] at hx
      exact ⟨hx.2.le, hx.1.le⟩
    exact aeEventIn_regGood_open_of_barrier μ G hG ξ Q D hD hBG
      C w s hs U hKU hAU
  have hLocal0 := Toolkit.LocalEvents.aeEventIn_fieldSigmaClosed0_of_normIn
    (id : LQGMetric.DistC → LQGMetric.DistC) ψ hψ1 K hψK hLocal
  have hEq := ae_regGood_addConst_iff μ hμ ξ Q D hD C w s
    (fun g => -(g ψ))
  obtain ⟨R, hRm, hGR⟩ := hLocal0
  refine ⟨R, hRm, ?_⟩
  filter_upwards [hEq, hGR] with g he hR
  exact propext (he.symm.trans (Iff.of_eq hR))

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
