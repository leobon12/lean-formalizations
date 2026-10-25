import SupercriticalLQGUniqueness.B2.PfeAxioms.S2NormalizedPatch

 









set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DFGPS.L217

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
theorem ae_patch_local_data_of_normalized
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (Φ : DistC → LSCMetric)
    (hlsc : PfeWeyl.NormalizedLscLimit ξ m ε Φ)
    (hgeo : PfeWeyl.NormalizedLimitGeometry Φ)
    (htail : PfeWeyl.NormalizedAcrossTails Φ)
    (hsmall : PfeWeyl.NormalizedSmallAnnuli ξ m ε Φ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, (Φ (h ω)).IsLengthSpace ∧ Continuous (PfeWeyl.euclidForget (Φ (h ω))) ∧
      PfeWeyl.AcrossUnbounded (Φ (h ω)) ∧ SelfSmallAnnuli (Φ (h ω)) univ ∧
      ∀ F : C(ℂ, ℝ), ∃ (Fk : ℕ → C(ℂ, ℝ)) (Mk : ℕ → ℝ) (ψ : ℕ → ℕ → C(ℂ, ℝ))
        (E : ℕ → LSCMetric),
        (∀ k z, |Fk k z| ≤ Mk k) ∧
        (∀ k, EqOn F (Fk k) (Metric.closedBall 0 ((k : ℝ) + 3))) ∧
        (∀ k p, E k p = weylScale (ξ : ℝ) (Fk k) (Φ (h ω)) p) ∧
        (∀ k, Tendsto (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n))
          atTop (𝓝 (E k))) ∧
        (∀ k, PfeWeyl.SmallAnnulusCosts
          (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n)) (E k)
          (Metric.closedBall 0 ((k : ℝ) + 1 / 2)) (patchBall k)) ∧
        (∀ k, ∀ θ : ℝ, 0 < θ → ∀ᶠ n in atTop, ∀ z ∈ patchBall k,
          |locMollifyC (ε n : ℝ) (ε n).property (addFun (h ω) F) z - ψ k n z| ≤ θ) := by
  have hξ0 : (0 : ℝ) ≤ ξ := ξ.property.le
  have hb := LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hh.1
  choose X _ hX using fun t : Set.Ioi (0 : ℝ) => exists_heatVersion_bdd hb t
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n))
      (X (ε n) ω)) atTop (𝓝 (Φ (h ω))) := by
    filter_upwards [hlsc P h hh X hX] with ω hω
    exact (PfeWeyl.tendsto_normalizedLFPP_iff_lscTendsto _ _ _ _).2 hω
  obtain ⟨hlen, hctrl⟩ := hgeo P h hh
  have hacr := PfeWeyl.ae_acrossUnbounded_of_acrossTail P (fun ω => Φ (h ω)) (htail P h hh)
  have hsm : ∀ᵐ ω ∂P, ∀ j : ℕ, PfeWeyl.SmallAnnulusCosts
      (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
      (Φ (h ω)) (Metric.closedBall 0 j) (Metric.ball 0 ((j : ℝ) + 1)) :=
    ae_all_iff.2 (hsmall P h hh X hX)
  have hW3 := PfeWeyl.ae_weyl_scaling_all_bounded_of_tendsto ξ m ε hε P (fun ω => Φ (h ω)) X
    hconv hlen hctrl (htail P h hh) (hsmall P h hh X hX)
  have hXeq := ae_heat_smoothing_sequence_eq P h hh ε X hX
  have hloc : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ δ : ℝ, 0 < δ → ∀ᶠ e in 𝓝[>] (0 : ℝ), ∀ he : 0 < e,
      ∀ z ∈ closure (Metric.ball (0 : ℂ) ((j : ℝ) + 2)),
        |heatMollify e (h ω) z - locMollify e he (h ω) z| ≤ δ :=
    ae_all_iff.2 fun j => (B2.DG20Pt.dg20_gff_localized_approx hh Metric.isBounded_ball
      (ξ : ℝ)).mono fun ω hω => hω.2.1
  filter_upwards [hconv, hlen, hctrl, hacr, hsm, hW3, hXeq, hloc] with ω hcω hlω hctω hacω
    hsmω hW3ω hXω hlocω
  have hforget : Continuous (PfeWeyl.euclidForget (Φ (h ω))) :=
    B2.PfeLocal.continuous_euclidForget_of_small_metric _ hctω
  have hSSA : SelfSmallAnnuli (Φ (h ω)) univ := by
    intro z _ hns δ hδ ρ hρ
    obtain ⟨j, hj⟩ := exists_nat_gt ‖z‖
    exact selfSmallAnnuli_of_smallAnnulusCosts hcω (hsmω j) z
      (by rw [Metric.mem_closedBall, dist_zero_right]; exact hj.le) hns δ hδ ρ hρ
  refine ⟨hlω, hforget, hacω, hSSA, fun F => ?_⟩
  
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
  choose E hE hEconv using fun k => hW3ω (Fk k) (Mk k) (hFkM k)
  set ψ : ℕ → ℕ → C(ℂ, ℝ) := fun k n =>
    X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' (Fk k) (Mk k) (hFkM k)
  
  have hsmallk : ∀ k, PfeWeyl.SmallAnnulusCosts
      (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n)) (E k)
      (Metric.closedBall 0 ((k : ℝ) + 1 / 2)) (patchBall k) := by
    intro k
    have hbase : PfeWeyl.SmallAnnulusCosts
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω)) (Φ (h ω))
        (Metric.closedBall 0 ((k : ℝ) + 1 / 2)) (patchBall k) := by
      have h1 := hsmω (k + 1)
      refine smallAnnulusCosts_restrict h1 (Metric.closedBall_subset_closedBall
        (by push_cast; linarith)) (by norm_num : (0 : ℝ) < 1 / 2) ?_
      intro z hz w hw
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [Metric.mem_ball] at hw
      change w ∈ Metric.ball (0 : ℂ) ((k : ℝ) + 1)
      rw [Metric.mem_ball, dist_zero_right]
      have := norm_le_norm_add_norm_sub' w z
      rw [← dist_eq_norm] at this
      linarith
    exact smallAnnulusCosts_of_bounded_weyl (ξ : ℝ) hξ0
      (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
      (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n))
      (Φ (h ω)) (E k) (Fk k)
      (fun n => LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' (Fk k) (Mk k) (hFkM k))
      hforget (hE k)
      (fun n p => PfeWeyl.normalizedLFPPMetric_add_eq_weylScale _ _ _ _ p) (Mk k)
      (fun z => (abs_le.1 (hFkM k z)).1)
      (fun n z _ => (abs_le.1 (PfeWeyl.abs_mollCont_le _ _ _ _ z)).2) hbase
  
  have hεw : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε, Eventually.of_forall fun n => (ε n).property⟩
  have hclosek : ∀ k, ∀ θ : ℝ, 0 < θ → ∀ᶠ n in atTop, ∀ z ∈ patchBall k,
      |locMollifyC (ε n : ℝ) (ε n).property (addFun (h ω) F) z - ψ k n z| ≤ θ := by
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
    have hexpand : locMollifyC (ε n : ℝ) (ε n).property (addFun (h ω) F) z - ψ k n z =
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
  exact ⟨Fk, Mk, ψ, E, hFkM, hFk, hE, hEconv, hsmallk, hclosek⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
