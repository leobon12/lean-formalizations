import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.DGZ.FunctionalsMeas
import HigherDimLQGMetric.DGZ.FunctionalsBounds
import HigherDimLFPP.Paths.Measurable

/-!
# Rational envelopes for convolution LFPP

The supremum is indexed by rational centres and radii. The endpoint supremum is
written as the equivalent internal diameter of the smaller ball; continuity of
the internal metric identifies this with the rational endpoint supremum.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

namespace HigherDimLQGContinuity

open HigherDimLFPP (Rd)

/-- The countable set of admissible centre-radius pairs in the envelope. -/
def convEnvIndex (d : ℕ) (R : ℝ) : Set ((Fin d → ℚ) × ℚ) :=
  {i | HigherDimLFPP.ratPt i.1 ∈ closedBall (0 : Rd d) (R + 1) ∧
    0 < (i.2 : ℝ) ∧ (i.2 : ℝ) ≤ 2}

/-- Rational-centre envelope for an LFPP field. -/
def ratEnvelope {d : ℕ} (ξ σ R : ℝ) (φ : C(Rd d, ℝ)) : ℝ≥0∞ :=
  ⨆ i : convEnvIndex d R,
    ENNReal.ofReal (((i.1.2 : ℝ) ^ (-σ)) *
      HigherDimLQGMetric.DGZ.lfppDiam ξ φ
        (ball (HigherDimLFPP.ratPt i.1.1) (i.1.2 : ℝ))
        (ball (HigherDimLFPP.ratPt i.1.1) (29 / 20 * (i.1.2 : ℝ))))

/-- The rational envelope is a Borel functional of the continuous field. -/
theorem measurable_ratEnvelope {d : ℕ} (ξ σ R : ℝ) :
    Measurable (ratEnvelope (d := d) ξ σ R) := by
  unfold ratEnvelope
  apply Measurable.iSup
  intro i
  have ht : (0 : ℝ) < (i.1.2 : ℝ) := i.2.2.1
  have hsub : ball (HigherDimLFPP.ratPt i.1.1) (i.1.2 : ℝ) ⊆
      ball (HigherDimLFPP.ratPt i.1.1) (29 / 20 * (i.1.2 : ℝ)) := by
    apply ball_subset_ball
    nlinarith
  exact (ENNReal.measurable_ofReal.comp
    ((HigherDimLQGMetric.DGZ.measurable_lfppDiam_continuousMap
      isOpen_ball (convex_ball _ _).isPreconnected hsub ξ).const_mul _))

/-- A rational centre and radius with both buffers required by the envelope. -/
theorem convEnvIndex_exists {d : ℕ} {R s : ℝ} {z : Rd d}
    (hz : z ∈ closedBall (0 : Rd d) R)
    (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ i : convEnvIndex d R,
      (i.1.2 : ℝ) < 102 / 100 * s ∧
      ball z s ⊆ ball (HigherDimLFPP.ratPt i.1.1) (i.1.2 : ℝ) ∧
      ball (HigherDimLFPP.ratPt i.1.1) (29 / 20 * (i.1.2 : ℝ)) ⊆
        ball z (3 / 2 * s) := by
  obtain ⟨w, hw⟩ := (HigherDimLFPP.denseRange_ratPt (d := d)).exists_dist_lt z
    (show 0 < s / 100 by positivity)
  obtain ⟨t, htlo, hthi⟩ := exists_rat_btwn
    (show (101 / 100 : ℝ) * s < (102 / 100 : ℝ) * s by nlinarith)
  have ht0 : (0 : ℝ) < t := by nlinarith
  have ht2 : (t : ℝ) ≤ 2 := by nlinarith
  have hwR : HigherDimLFPP.ratPt w ∈ closedBall (0 : Rd d) (R + 1) := by
    apply Metric.mem_closedBall.mpr
    have htri := dist_triangle (HigherDimLFPP.ratPt w) z (0 : Rd d)
    have hzR : dist z (0 : Rd d) ≤ R := by simpa only [Metric.mem_closedBall] using hz
    rw [dist_comm z (HigherDimLFPP.ratPt w)] at hw
    linarith
  let i : convEnvIndex d R := ⟨(w, t), hwR, ht0, ht2⟩
  refine ⟨i, hthi, ?_, ?_⟩
  · intro x hx
    have hxs : dist x z < s := Metric.mem_ball.mp hx
    have htri := dist_triangle x z (HigherDimLFPP.ratPt w)
    exact Metric.mem_ball.mpr (by change dist x (HigherDimLFPP.ratPt w) < (t : ℝ); linarith)
  · intro x hx
    have hxt : dist x (HigherDimLFPP.ratPt w) < 29 / 20 * (t : ℝ) :=
      Metric.mem_ball.mp hx
    have htri := dist_triangle x (HigherDimLFPP.ratPt w) z
    have hw' : dist (HigherDimLFPP.ratPt w) z < s / 100 := by
      simpa only [dist_comm] using hw
    change dist x z < 3 / 2 * s
    linarith

/-- The envelope controls every buffered local distance. -/
theorem lfppDistOn_le_ratEnvelope {d : ℕ} {ξ σ R s : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    {z x y : Rd d} (hz : z ∈ closedBall (0 : Rd d) R)
    (hs : s ∈ Ioc (0 : ℝ) 1) (hx : x ∈ ball z s) (hy : y ∈ ball z s)
    (φ : C(Rd d, ℝ)) :
    ENNReal.ofReal (HigherDimLFPP.lfppDistOn ξ φ (ball z (3 / 2 * s)) x y) ≤
      ENNReal.ofReal 2 * ratEnvelope ξ σ R φ * ENNReal.ofReal (s ^ σ) := by
  obtain ⟨i, htupper, hxy, hbuf⟩ := convEnvIndex_exists hz hs.1 hs.2
  let w : Rd d := HigherDimLFPP.ratPt i.1.1
  let t : ℝ := i.1.2
  have ht0 : 0 < t := i.2.2.1
  have htw : t ≤ 2 * s := by linarith
  have hdiam : HigherDimLFPP.lfppDistOn ξ φ (ball z (3 / 2 * s)) x y ≤
      HigherDimLQGMetric.DGZ.lfppDiam ξ φ (ball w t) (ball w (29 / 20 * t)) := by
    have hUV : ball w t ⊆ ball w (29 / 20 * t) :=
      ball_subset_ball (by nlinarith)
    have hK : closedBall w t ⊆ ball w (29 / 20 * t) :=
      closedBall_subset_ball (by nlinarith)
    have hbdd := HigherDimLQGMetric.DGZ.bddAbove_lfppDiam_of_isCompact
      isOpen_ball (convex_ball _ _).isPreconnected φ.continuous ξ
      (isCompact_closedBall w t) hK ball_subset_closedBall
    exact (HigherDimLQGMetric.DGZ.lfppDistOn_mono_of_isPreconnected
      isOpen_ball (convex_ball _ _).isPreconnected hbuf (hUV (hxy hx)) (hUV (hxy hy))).trans
      (HigherDimLQGMetric.DGZ.lfppDistOn_le_lfppDiam hbdd (hxy hx) (hxy hy))
  have htpow : t ^ σ ≤ 2 * s ^ σ := by
    have h2 : (2 : ℝ) ^ σ ≤ 2 := by
      simpa using (Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
        (y := σ) (z := 1) (by norm_num) hσ1)
    calc
      t ^ σ ≤ (2 * s) ^ σ := Real.rpow_le_rpow ht0.le htw hσ
      _ = 2 ^ σ * s ^ σ := Real.mul_rpow (by norm_num) hs.1.le
      _ ≤ 2 * s ^ σ :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hs.1.le σ)
  have hterm : ENNReal.ofReal (t ^ (-σ) *
      HigherDimLQGMetric.DGZ.lfppDiam ξ φ (ball w t) (ball w (29 / 20 * t))) ≤
      ratEnvelope ξ σ R φ := by
    have hi := le_iSup (fun j : convEnvIndex d R =>
      ENNReal.ofReal (((j.1.2 : ℝ) ^ (-σ)) *
        HigherDimLQGMetric.DGZ.lfppDiam ξ φ
          (ball (HigherDimLFPP.ratPt j.1.1) (j.1.2 : ℝ))
          (ball (HigherDimLFPP.ratPt j.1.1) (29 / 20 * (j.1.2 : ℝ))))) i
    simpa only [w, t, ratEnvelope] using hi
  have hp : t ^ (-σ) * t ^ σ = 1 := by
    rw [Real.rpow_neg ht0.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos ht0 σ).ne']
  have hrepr : HigherDimLQGMetric.DGZ.lfppDiam ξ φ (ball w t) (ball w (29 / 20 * t)) =
      (t ^ (-σ) * HigherDimLQGMetric.DGZ.lfppDiam ξ φ
        (ball w t) (ball w (29 / 20 * t))) * t ^ σ := by
    calc
      _ = (t ^ (-σ) * t ^ σ) *
          HigherDimLQGMetric.DGZ.lfppDiam ξ φ (ball w t) (ball w (29 / 20 * t)) := by rw [hp]; ring
      _ = _ := by ring
  have hn : 0 ≤ t ^ (-σ) *
      HigherDimLQGMetric.DGZ.lfppDiam ξ φ (ball w t) (ball w (29 / 20 * t)) :=
    mul_nonneg (Real.rpow_nonneg ht0.le _) (HigherDimLQGMetric.DGZ.lfppDiam_nonneg _ _ _ _)
  have hreprE : ENNReal.ofReal (HigherDimLQGMetric.DGZ.lfppDiam ξ φ
      (ball w t) (ball w (29 / 20 * t))) =
      ENNReal.ofReal (t ^ (-σ) * HigherDimLQGMetric.DGZ.lfppDiam ξ φ
        (ball w t) (ball w (29 / 20 * t))) * ENNReal.ofReal (t ^ σ) := by
    rw [← ENNReal.ofReal_mul hn, ← hrepr]
  calc
    ENNReal.ofReal (HigherDimLFPP.lfppDistOn ξ φ (ball z (3 / 2 * s)) x y) ≤
        ENNReal.ofReal (HigherDimLQGMetric.DGZ.lfppDiam ξ φ
          (ball w t) (ball w (29 / 20 * t))) := ENNReal.ofReal_le_ofReal hdiam
    _ = ENNReal.ofReal (t ^ (-σ) * HigherDimLQGMetric.DGZ.lfppDiam ξ φ
        (ball w t) (ball w (29 / 20 * t))) * ENNReal.ofReal (t ^ σ) := hreprE
    _ ≤ ratEnvelope ξ σ R φ * ENNReal.ofReal (t ^ σ) := by gcongr
    _ ≤ ratEnvelope ξ σ R φ * ENNReal.ofReal (2 * s ^ σ) := by gcongr
    _ = ENNReal.ofReal 2 * ratEnvelope ξ σ R φ * ENNReal.ofReal (s ^ σ) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ac_rfl

/-- Internal LFPP diameters scale exactly under a constant field shift. -/
theorem convEnv_lfppDiam_add_const {d : ℕ} (ξ c : ℝ)
    (φ : Rd d → ℝ) (U V : Set (Rd d)) :
    HigherDimLQGMetric.DGZ.lfppDiam ξ (fun z => φ z + c) U V =
      Real.exp (ξ * c) * HigherDimLQGMetric.DGZ.lfppDiam ξ φ U V := by
  unfold HigherDimLQGMetric.DGZ.lfppDiam
  simp_rw [HigherDimLFPP.lfppDistOn_add_const]
  rw [show (fun p : Rd d × Rd d => Real.exp (ξ * c) *
      HigherDimLFPP.lfppDistOn ξ φ V p.1 p.2) '' (U ×ˢ U) =
      Real.exp (ξ * c) • ((fun p : Rd d × Rd d =>
        HigherDimLFPP.lfppDistOn ξ φ V p.1 p.2) '' (U ×ˢ U)) by
        ext a
        simp only [Set.mem_image, Set.mem_smul_set]
        constructor
        · rintro ⟨p, hp, rfl⟩
          exact ⟨_, ⟨p, hp, rfl⟩, by simp only [smul_eq_mul]⟩
        · rintro ⟨b, ⟨p, hp, rfl⟩, rfl⟩
          exact ⟨p, hp, by simp only [smul_eq_mul]⟩]
  simpa only [smul_eq_mul] using
    (Real.sSup_smul_of_nonneg (Real.exp_pos (ξ * c)).le
      ((fun p : Rd d × Rd d => HigherDimLFPP.lfppDistOn ξ φ V p.1 p.2) '' (U ×ˢ U)))

/-- A constant field shift multiplies the rational envelope by its Weyl factor. -/
theorem ratEnvelope_add_const {d : ℕ} (ξ σ R c : ℝ) (φ : C(Rd d, ℝ)) :
    ratEnvelope ξ σ R (φ + ContinuousMap.const (Rd d) c) =
      ENNReal.ofReal (Real.exp (ξ * c)) * ratEnvelope ξ σ R φ := by
  unfold ratEnvelope
  have hterm (i : convEnvIndex d R) :
      ENNReal.ofReal (((i.1.2 : ℝ) ^ (-σ)) *
        HigherDimLQGMetric.DGZ.lfppDiam ξ (φ + ContinuousMap.const (Rd d) c)
          (ball (HigherDimLFPP.ratPt i.1.1) (i.1.2 : ℝ))
          (ball (HigherDimLFPP.ratPt i.1.1) (29 / 20 * (i.1.2 : ℝ)))) =
      ENNReal.ofReal (Real.exp (ξ * c)) *
        ENNReal.ofReal (((i.1.2 : ℝ) ^ (-σ)) *
          HigherDimLQGMetric.DGZ.lfppDiam ξ φ
            (ball (HigherDimLFPP.ratPt i.1.1) (i.1.2 : ℝ))
            (ball (HigherDimLFPP.ratPt i.1.1) (29 / 20 * (i.1.2 : ℝ)))) := by
    have hfield : (⇑(φ + ContinuousMap.const (Rd d) c) : Rd d → ℝ) =
        fun z => φ z + c := by
      funext z
      rfl
    rw [hfield, convEnv_lfppDiam_add_const]
    rw [show (i.1.2 : ℝ) ^ (-σ) *
        (Real.exp (ξ * c) * HigherDimLQGMetric.DGZ.lfppDiam ξ φ
          (ball (HigherDimLFPP.ratPt i.1.1) (i.1.2 : ℝ))
          (ball (HigherDimLFPP.ratPt i.1.1) (29 / 20 * (i.1.2 : ℝ)))) =
        Real.exp (ξ * c) * ((i.1.2 : ℝ) ^ (-σ) *
          HigherDimLQGMetric.DGZ.lfppDiam ξ φ
            (ball (HigherDimLFPP.ratPt i.1.1) (i.1.2 : ℝ))
            (ball (HigherDimLFPP.ratPt i.1.1) (29 / 20 * (i.1.2 : ℝ)))) by ring]
    exact ENNReal.ofReal_mul (Real.exp_pos _).le
  simp_rw [hterm]
  exact (ENNReal.mul_iSup (ENNReal.ofReal (Real.exp (ξ * c))) _).symm

/-- A field perturbation bounded on the observation ball controls the envelope. -/
theorem ratEnvelope_le_of_abs_le {d : ℕ} (ξ σ R M : ℝ)
    (φ ψ : C(Rd d, ℝ))
    (hM : ∀ z ∈ closedBall (0 : Rd d) (R + 5), |ψ z| ≤ M) :
    ratEnvelope ξ σ R (φ + ψ) ≤
      ENNReal.ofReal (Real.exp (|ξ| * M)) * ratEnvelope ξ σ R φ := by
  unfold ratEnvelope
  apply iSup_le
  intro i
  let w : Rd d := HigherDimLFPP.ratPt i.1.1
  let t : ℝ := i.1.2
  have ht0 : 0 < t := i.2.2.1
  have ht2 : t ≤ 2 := i.2.2.2
  have hwR : w ∈ closedBall (0 : Rd d) (R + 1) := i.2.1
  have hV : ball w (29 / 20 * t) ⊆ closedBall (0 : Rd d) (R + 5) := by
    intro z hz
    apply Metric.mem_closedBall.mpr
    have hzt : dist z w < 29 / 20 * t := Metric.mem_ball.mp hz
    have hw := Metric.mem_closedBall.mp hwR
    have htri := dist_triangle z w (0 : Rd d)
    linarith
  have hbdd : BddAbove ((fun p : Rd d × Rd d =>
      HigherDimLFPP.lfppDistOn ξ φ (ball w (29 / 20 * t)) p.1 p.2) ''
      (ball w t ×ˢ ball w t)) := by
    have hK : closedBall w t ⊆ ball w (29 / 20 * t) :=
      closedBall_subset_ball (by nlinarith)
    exact HigherDimLQGMetric.DGZ.bddAbove_lfppDiam_of_isCompact
      isOpen_ball (convex_ball _ _).isPreconnected φ.continuous ξ
      (isCompact_closedBall w t) hK ball_subset_closedBall
  have hcmp : HigherDimLQGMetric.DGZ.lfppDiam ξ (φ + ψ)
      (ball w t) (ball w (29 / 20 * t)) ≤
      Real.exp (|ξ| * M) * HigherDimLQGMetric.DGZ.lfppDiam ξ φ
        (ball w t) (ball w (29 / 20 * t)) := by
    have hfield : (⇑(φ + ψ) : Rd d → ℝ) = fun z => φ z + ψ z := by
      funext z
      rfl
    rw [hfield]
    exact HigherDimLQGMetric.DGZ.lfppDiam_le_exp_mul
      (φ.continuous.add ψ.continuous) φ.continuous
      (by
        intro z hz
        change |φ z + ψ z - φ z| ≤ M
        simpa only [add_sub_cancel_left] using hM z (hV hz)) hbdd
  have hpow : 0 ≤ t ^ (-σ) := Real.rpow_nonneg ht0.le _
  have hnonneg : 0 ≤ t ^ (-σ) * HigherDimLQGMetric.DGZ.lfppDiam ξ φ
      (ball w t) (ball w (29 / 20 * t)) :=
    mul_nonneg hpow (HigherDimLQGMetric.DGZ.lfppDiam_nonneg _ _ _ _)
  have hi := le_iSup (fun j : convEnvIndex d R =>
      ENNReal.ofReal (((j.1.2 : ℝ) ^ (-σ)) *
        HigherDimLQGMetric.DGZ.lfppDiam ξ φ
          (ball (HigherDimLFPP.ratPt j.1.1) (j.1.2 : ℝ))
          (ball (HigherDimLFPP.ratPt j.1.1) (29 / 20 * (j.1.2 : ℝ))))) i
  calc
    ENNReal.ofReal (((i.1.2 : ℝ) ^ (-σ)) *
        HigherDimLQGMetric.DGZ.lfppDiam ξ (φ + ψ)
          (ball w t) (ball w (29 / 20 * t))) ≤
      ENNReal.ofReal (t ^ (-σ) * (Real.exp (|ξ| * M) *
        HigherDimLQGMetric.DGZ.lfppDiam ξ φ
          (ball w t) (ball w (29 / 20 * t)))) := by
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcmp hpow)
    _ = ENNReal.ofReal (Real.exp (|ξ| * M)) *
        ENNReal.ofReal (t ^ (-σ) * HigherDimLQGMetric.DGZ.lfppDiam ξ φ
          (ball w t) (ball w (29 / 20 * t))) := by
          rw [show t ^ (-σ) * (Real.exp (|ξ| * M) *
              HigherDimLQGMetric.DGZ.lfppDiam ξ φ (ball w t) (ball w (29 / 20 * t))) =
              Real.exp (|ξ| * M) * (t ^ (-σ) *
                HigherDimLQGMetric.DGZ.lfppDiam ξ φ (ball w t) (ball w (29 / 20 * t))) by ring]
          exact ENNReal.ofReal_mul (Real.exp_pos _).le
    _ ≤ ENNReal.ofReal (Real.exp (|ξ| * M)) *
        ⨆ j : convEnvIndex d R,
          ENNReal.ofReal (((j.1.2 : ℝ) ^ (-σ)) *
            HigherDimLQGMetric.DGZ.lfppDiam ξ φ
              (ball (HigherDimLFPP.ratPt j.1.1) (j.1.2 : ℝ))
              (ball (HigherDimLFPP.ratPt j.1.1) (29 / 20 * (j.1.2 : ℝ)))) := by
                exact mul_le_mul_of_nonneg_left (by simpa only [w, t] using hi) bot_le

/-- The companion lower comparison for a bounded field perturbation. -/
theorem ratEnvelope_ge_of_abs_le {d : ℕ} (ξ σ R M : ℝ)
    (φ ψ : C(Rd d, ℝ))
    (hM : ∀ z ∈ closedBall (0 : Rd d) (R + 5), |ψ z| ≤ M) :
    ratEnvelope ξ σ R φ ≤
      ENNReal.ofReal (Real.exp (|ξ| * M)) * ratEnvelope ξ σ R (φ + ψ) := by
  have hcancel : (φ + ψ) + -ψ = φ := by
    ext z
    simp only [add_neg_cancel_right]
  have hneg : ∀ z ∈ closedBall (0 : Rd d) (R + 5), |(-ψ) z| ≤ M := by
    intro z hz
    simpa only [ContinuousMap.neg_apply, abs_neg] using hM z hz
  simpa only [hcancel] using ratEnvelope_le_of_abs_le ξ σ R M (φ + ψ) (-ψ) hneg

end HigherDimLQGContinuity
