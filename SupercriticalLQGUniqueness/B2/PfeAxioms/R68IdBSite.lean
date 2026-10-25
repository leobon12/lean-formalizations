import SupercriticalLQGUniqueness.B2.PfeAxioms.R68IdBSample
import SupercriticalLQGUniqueness.B2.PfeAxioms.R68IdSelfSmall
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2NormalizedPatch
import SupercriticalLQGUniqueness.B2.Final.OpenInputs5

 

















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DFGPS.L217
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
theorem fixedFieldPatchIdentification_of_weyl
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (Φ : DistC → LSCMetric)
    (hgeo : PfeWeyl.NormalizedLimitGeometry Φ)
    (htail : PfeWeyl.NormalizedAcrossTails Φ)
    (hSSA : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ᵐ ω ∂P, SelfSmallAnnuli (Φ (h ω)) univ)
    (hW : FixedFieldWeylAllBounded ξ m ε Φ) :
    Final.FixedFieldPatchIdentification ξ m ε Φ := by
  intro Ω _ P _ h hh
  have hb := LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hh.1
  choose X _ hX using fun t : Set.Ioi (0 : ℝ) => exists_heatVersion_bdd hb t
  obtain ⟨hlen, hctrl⟩ := hgeo P h hh
  have hacr := PfeWeyl.ae_acrossUnbounded_of_acrossTail P (fun ω => Φ (h ω)) (htail P h hh)
  have hW3 := hW P h hh X hX
  have hXeq := ae_heat_smoothing_sequence_eq P h hh ε X hX
  have hloc : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ δ : ℝ, 0 < δ → ∀ᶠ e in 𝓝[>] (0 : ℝ), ∀ he : 0 < e,
      ∀ z ∈ closure (Metric.ball (0 : ℂ) ((j : ℝ) + 2)),
        |heatMollify e (h ω) z - locMollify e he (h ω) z| ≤ δ :=
    ae_all_iff.2 fun j => (B2.DG20Pt.dg20_gff_localized_approx hh Metric.isBounded_ball
      (ξ : ℝ)).mono fun ω hω => hω.2.1
  filter_upwards [hlen, hctrl, hacr, hSSA P h hh, hW3, hXeq, hloc] with ω hlω hctω hacω
    hSSAω hW3ω hXω hlocω
  intro F
  have hforget : Continuous (PfeWeyl.euclidForget (Φ (h ω))) :=
    B2.PfeLocal.continuous_euclidForget_of_small_metric _ hctω
  
  choose M0 hM0 using fun k : ℕ =>
    (isCompact_closedBall (0 : ℂ) ((k : ℝ) + 3)).exists_bound_of_continuousOn
      F.continuous.continuousOn
  set Mk : ℕ → ℝ := fun k => max (M0 k) 0
  set Fk : ℕ → C(ℂ, ℝ) := fun k => clampContinuous (Mk k) F
  have hFkM : ∀ k z, |Fk k z| ≤ Mk k := fun k z =>
    clampContinuous_bound (le_max_right _ _) F z
  have hFk : ∀ k, EqOn F (Fk k) (Metric.closedBall 0 ((k : ℝ) + 3)) := by
    intro k z hz
    have h1 : |F z| ≤ Mk k := by
      have := hM0 k z hz
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    exact (clampContinuous_eq_of_bound F h1).symm
  
  have hεw : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε, Eventually.of_forall fun n => (ε n).property⟩
  have hclosek : ∀ k, ∀ θ : ℝ, 0 < θ → ∀ᶠ n in atTop, ∀ z ∈ patchBall k,
      |locMollifyC (ε n : ℝ) (ε n).property (addFun (h ω) F) z -
        (X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' (Fk k) (Mk k)
          (hFkM k)) z| ≤ θ := by
    intro k θ hθ
    have h1 := hεw.eventually (hlocω k (θ / 2) (half_pos hθ))
    have h2 : ∀ᶠ n in atTop, Mk k * (2 * Real.exp (-(1 / (8 * (ε n : ℝ))))) ≤ θ / 2 := by
      have ht : Tendsto (fun n => Mk k * (2 * Real.exp (-(1 / (8 * (ε n : ℝ)))))) atTop
          (𝓝 (Mk k * (2 * 0))) :=
        ((LQGMetric.DFGPS.tendsto_exp_neg_inv_eight.comp hεw).const_mul 2).const_mul (Mk k)
      simp only [mul_zero] at ht
      exact ht.eventually (ge_mem_nhds (half_pos hθ))
    have h3 : ∀ᶠ n in atTop, Real.sqrt (ε n : ℝ) < 1 := by
      have hs : Tendsto (fun n => Real.sqrt (ε n : ℝ)) atTop (𝓝 0) := by
        have := (Real.continuous_sqrt.tendsto 0).comp hε
        rw [Real.sqrt_zero] at this
        exact this
      exact hs.eventually (gt_mem_nhds one_pos)
    filter_upwards [h1, h2, h3] with n hn1 hn2 hn3
    intro z hz
    have hzb : ‖z‖ < (k : ℝ) + 1 := by
      have := Metric.mem_ball.1 hz; rwa [dist_zero_right] at this
    have hball : EqOn F (Fk k) (Metric.closedBall z (Real.sqrt (ε n : ℝ))) := by
      intro w hw
      apply hFk k
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [Metric.mem_closedBall] at hw
      have := norm_le_norm_add_norm_sub' w z
      rw [← dist_eq_norm] at this
      linarith
    have hzc : z ∈ closure (Metric.ball (0 : ℂ) ((k : ℝ) + 2)) :=
      subset_closure (Metric.ball_subset_ball (by linarith) hz)
    have hpos : 0 < (ε n : ℝ) := (ε n).property
    have hA := hn1 hpos z hzc
    have hB := LQGMetric.DFGPS.abs_heatMollify_sub_locMollify_ofCont_le (Fk k) (Mk k) (hFkM k)
      (ε n : ℝ) hpos z
    have hexpand : locMollifyC (ε n : ℝ) (ε n).property (addFun (h ω) F) z -
        (X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' (Fk k) (Mk k)
          (hFkM k)) z =
        (locMollify (ε n : ℝ) hpos (h ω) z - heatMollify (ε n : ℝ) (h ω) z) +
          (locMollify (ε n : ℝ) hpos (ofCont (Fk k)) z -
            heatMollify (ε n : ℝ) (ofCont (Fk k)) z) := by
      show locMollify (ε n : ℝ) hpos (addFun (h ω) F) z -
        (X (ε n) ω z + heatMollify (ε n : ℝ) (ofCont (Fk k)) z) = _
      rw [locMollify_addFun, locMollify_ofCont_congr _ hpos hball, hXω n z]
      ring
    rw [hexpand]
    calc |(locMollify (ε n : ℝ) hpos (h ω) z - heatMollify (ε n : ℝ) (h ω) z) +
          (locMollify (ε n : ℝ) hpos (ofCont (Fk k)) z -
            heatMollify (ε n : ℝ) (ofCont (Fk k)) z)|
        ≤ |heatMollify (ε n : ℝ) (h ω) z - locMollify (ε n : ℝ) hpos (h ω) z| +
          |heatMollify (ε n : ℝ) (ofCont (Fk k)) z -
            locMollify (ε n : ℝ) hpos (ofCont (Fk k)) z| := by
          rw [abs_sub_comm (heatMollify _ (h ω) z), abs_sub_comm (heatMollify _ (ofCont _) z)]
          exact abs_add_le _ _
      _ ≤ θ / 2 + θ / 2 := add_le_add hA (hB.trans hn2)
      _ = θ := by ring
  exact tendsto_patchApprox_of_fixedFieldWeyl ξ m ε (Φ (h ω)) hlω hforget hacω hSSAω
    (addFun (h ω) F) F Fk Mk hFkM hFk (fun n => X (ε n) ω) hW3ω hclosek

 

theorem s2IdentificationSite_proved : Final.S2IdentificationSite := by
  intro _hI ξ Q m e c V Ω' _ _ P' _ h' hN L hB hSA hAT _hR Φ hΦm hII _hlsc hW
  refine ⟨id, strictMono_id, ?_⟩
  exact fixedFieldPatchIdentification_of_weyl ξ m e hB.scale_tendsto Φ
    (Final.normalizedLimitGeometry_of_coupling hB Φ hII)
    (Final.normalizedAcrossTails_of_coupling hB hΦm hII hAT)
    (fun P _ h hh => ae_selfSmallAnnuli_of_coupling hB hSA hII P h hh) hW

end SupercriticalLQGUniqueness.B2.PfeAxioms
