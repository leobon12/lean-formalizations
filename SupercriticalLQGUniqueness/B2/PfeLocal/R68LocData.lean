import SupercriticalLQGUniqueness.B2.PfeLocal.R68LocTransfer
import SupercriticalLQGUniqueness.B2.Iface.FixedFieldWeyl

 






























set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DFGPS.L217

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open Uniqueness.Toolkit.CompactPathInfimum

 
theorem r68_liminf_le_mul {a x : ℕ → ℝ≥0∞} {κ : ℝ≥0∞} (hκ : κ ≠ ∞)
    (h : ∀ᶠ n in atTop, a n ≤ κ * x n) : liminf a atTop ≤ κ * liminf x atTop := by
  refine (liminf_le_liminf h).trans (le_of_eq ?_)
  exact ((Monotone.map_liminf_of_continuousAt (f := fun t => κ * t)
    (fun s t hst => l6_mul_le_mul_left hst) x (ENNReal.continuous_const_mul hκ).continuousAt)).symm

 
theorem r68_le_of_forall_exp_mul {a b : ℝ≥0∞} {ξ : ℝ}
    (h : ∀ θ : ℚ, 0 < θ → a ≤ ENNReal.ofReal (Real.exp (ξ * θ)) * b) : a ≤ b := by
  by_cases hb : b = ∞
  · rw [hb]; exact le_top
  set t : ℕ → ℚ := fun k => 1 / ((k : ℚ) + 1)
  have ht0 : ∀ k, 0 < t k := fun k => by positivity
  have htt : Tendsto (fun k => ((t k : ℚ) : ℝ)) atTop (𝓝 0) := by
    refine tendsto_one_div_add_atTop_nhds_zero_nat.congr fun k => ?_
    simp only [t]; push_cast; ring
  have hcont : Continuous fun x : ℝ => ENNReal.ofReal (Real.exp (ξ * x)) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have h1 : Tendsto (fun k => ENNReal.ofReal (Real.exp (ξ * (t k : ℝ)))) atTop (𝓝 1) :=
    (hcont.tendsto' 0 1 (by simp)).comp htt
  have h2 : Tendsto (fun k => ENNReal.ofReal (Real.exp (ξ * (t k : ℝ))) * b) atTop (𝓝 b) := by
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hb)
  exact ge_of_tendsto' h2 fun k => h (t k) (ht0 k)

 
theorem r68_abs_clamp_sub_le {C : ℝ} (f : C(ℂ, ℝ)) (z : ℂ) {g : ℝ} (hg : |g| ≤ C) :
    |PfeAxioms.clampContinuous C f z - g| ≤ |f z - g| := by
  show |max (-C) (min C (f z)) - g| ≤ |f z - g|
  have hg' := abs_le.1 hg
  have hC : 0 ≤ C := (abs_nonneg g).trans hg
  rcases le_total (f z) C with h1 | h1
  · rw [min_eq_right h1]
    rcases le_total (-C) (f z) with h2 | h2
    · rw [max_eq_right h2]
    · rw [max_eq_left h2, abs_sub_comm, abs_sub_comm (f z),
        abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  · rw [min_eq_left h1, max_eq_right (by linarith), abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith

 
def r68Fam (i : ℕ × ℕ × ℕ) : C(ℂ, ℝ) :=
  PfeAxioms.clampContinuous (i.2.2 : ℝ) (l6W (i.1 : ℝ) i.2.1)

theorem r68Fam_bound (i : ℕ × ℕ × ℕ) (z : ℂ) : |r68Fam i z| ≤ (i.2.2 : ℝ) :=
  PfeAxioms.clampContinuous_bound (Nat.cast_nonneg _) _ z

 
def r68Q (U : Set ℂ) (j l : ℕ) : Set ℂ := closure (l6Exh (PfeAxioms.exhW U j) l)

theorem isCompact_r68Q (U : Set ℂ) (j l : ℕ) : IsCompact (r68Q U j l) :=
  isCompact_closure_l6Exh _ _

 

theorem r68_ae_patch_local_data {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {ε : ℕ → Set.Ioi (0 : ℝ)}
    {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m ε c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m ε V P' hN L) (hAT : Final.CoupledAcrossTails P' L)
    {Φ : DistC → LSCMetric} (hII : ∀ᵐ ω ∂P', L ω = Φ (h' ω)) (hpatch : R68PatchWeyl ξ m ε Φ)
    (hFFW : Iface.FixedFieldWeylAllBounded ξ m ε Φ) (hgeo : PfeWeyl.NormalizedLimitGeometry Φ)
    (U : Set ℂ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, (Φ (h ω)).IsLengthSpace ∧ Continuous (PfeWeyl.euclidForget (Φ (h ω))) ∧
      ∀ F : C(ℂ, ℝ), ∃ (Fk : ℕ → C(ℂ, ℝ)) (Mk : ℕ → ℝ) (ψ : ℕ → ℕ → C(ℂ, ℝ))
        (E : ℕ → LSCMetric),
        (∀ k z, |Fk k z| ≤ Mk k) ∧
        (∀ k, EqOn F (Fk k) (Metric.closedBall 0 ((k : ℝ) + 3))) ∧
        (∀ k p, E k p = weylScale (ξ : ℝ) (Fk k) (Φ (h ω)) p) ∧
        (∀ k, Tendsto (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n))
          atTop (𝓝 (E k))) ∧
        (∀ (k j l : ℕ) (b₁ b₂ : ℚ × ℚ × ℚ) (η : ℚ), 0 < η →
          liminf (fun n => r68Y (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n))
            (r68Q U j l) b₁ b₂ η) atTop ≤ r68Z (E k) (r68Q U j l) b₁ b₂) ∧
        (∀ k, ∀ θ : ℝ, 0 < θ → ∀ᶠ n in atTop, ∀ z ∈ PfeAxioms.patchBall k,
          |locMollifyC (ε n : ℝ) (ε n).property (addFun (h ω) F) z - ψ k n z| ≤ θ) := by
  have hξ0 : (0 : ℝ) < ξ := ξ.property
  have hε := hB.scale_tendsto
  have hb := LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hh.1
  choose X _ hX using fun t : Set.Ioi (0 : ℝ) => PfeAxioms.exists_heatVersion_bdd hb t
  obtain ⟨hlen, hctrl⟩ := hgeo P h hh
  have hW3 := hFFW P h hh X hX
  have hXeq := PfeAxioms.ae_heat_smoothing_sequence_eq P h hh ε X hX
  have hVeq : ∀ᵐ ω ∂P, ∀ n z, V (ε n) (h ω) z = heatMollify (ε n : ℝ) (h ω) z := by
    have hlaw : normGFFLaw = P.map h := PfeAxioms.normGFFLaw_eq_of_normalized P h hh
    refine ae_all_iff.2 fun n => ?_
    have := hB.heat_ae (ε n)
    rw [hlaw] at this
    exact ae_of_ae_map hh.1.measurable.aemeasurable this
  have hloc : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ δ : ℝ, 0 < δ → ∀ᶠ e in 𝓝[>] (0 : ℝ), ∀ he : 0 < e,
      ∀ z ∈ closure (Metric.ball (0 : ℂ) ((j : ℝ) + 2)),
        |heatMollify e (h ω) z - locMollify e he (h ω) z| ≤ δ :=
    ae_all_iff.2 fun j => (B2.DG20Pt.dg20_gff_localized_approx hh Metric.isBounded_ball
      (ξ : ℝ)).mono fun ω hω => hω.2.1
  
  have hT : ∀ᵐ ω ∂P, ∀ (i : ℕ × ℕ × ℕ) (j l : ℕ) (b₁ b₂ : ℚ × ℚ × ℚ) (η : ℚ), 0 < η →
      liminf (fun n => r68Y (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n))
        (r68Wt V (ε n) (r68Fam i) (i.2.2 : ℝ) (r68Fam_bound i) (h ω))) (r68Q U j l) b₁ b₂ η)
        atTop ≤ r68Z (PfeAxioms.patchWitness ξ m ε (addFun (h ω) (r68Fam i))) (r68Q U j l) b₁ b₂ := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ae_all_iff.2 fun l => ae_all_iff.2 fun b₁ =>
      ae_all_iff.2 fun b₂ => ae_all_iff.2 fun η => ?_
    by_cases hη : (0 : ℚ) < η
    · filter_upwards [r68_fixedField_liminf_le hB hSA hAT hII hpatch (r68Fam i) _ (r68Fam_bound i)
        (isCompact_r68Q U j l) b₁ b₂ (η := (η : ℝ)) (by exact_mod_cast hη) P h hh] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h0 => absurd h0 hη
  filter_upwards [hlen, hctrl, hW3, hXeq, hVeq, hloc, hT, hpatch P h hh] with ω hlω hctω hW3ω
    hXω hVω hlocω hTω hpω
  have hforget : Continuous (PfeWeyl.euclidForget (Φ (h ω))) :=
    continuous_euclidForget_of_small_metric _ hctω
  have hXV : ∀ n, X (ε n) ω = V (ε n) (h ω) := fun n =>
    ContinuousMap.ext fun z => by rw [hXω n z, hVω n z]
  refine ⟨hlω, hforget, fun F => ?_⟩
  
  choose M0 hM0 using fun k : ℕ =>
    (isCompact_closedBall (0 : ℂ) ((k : ℝ) + 3)).exists_bound_of_continuousOn
      F.continuous.continuousOn
  set Mk : ℕ → ℝ := fun k => max (M0 k) 0
  set Fk : ℕ → C(ℂ, ℝ) := fun k => PfeAxioms.clampContinuous (Mk k) F
  have hFkM : ∀ k z, |Fk k z| ≤ Mk k := fun k z =>
    PfeAxioms.clampContinuous_bound (le_max_right _ _) F z
  have hFk : ∀ k, EqOn F (Fk k) (Metric.closedBall 0 ((k : ℝ) + 3)) := by
    intro k z hz
    have h1 : |F z| ≤ Mk k := by
      have := hM0 k z hz
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    exact (PfeAxioms.clampContinuous_eq_of_bound F h1).symm
  choose E hE hEconv using fun k => hW3ω (Fk k) (Mk k) (hFkM k)
  set ψ : ℕ → ℕ → C(ℂ, ℝ) := fun k n =>
    X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' (Fk k) (Mk k) (hFkM k)
  
  have hupper : ∀ (k j l : ℕ) (b₁ b₂ : ℚ × ℚ × ℚ) (η : ℚ), 0 < η →
      liminf (fun n => r68Y (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n))
        (r68Q U j l) b₁ b₂ η) atTop ≤ r68Z (E k) (r68Q U j l) b₁ b₂ := by
    intro k j l b₁ b₂ η hη
    set Qs := r68Q U j l with hQs
    have hQc : IsCompact Qs := isCompact_r68Q U j l
    obtain ⟨R₀, hR₀⟩ := (hQc.cthickening (r := (η : ℝ))).isBounded.subset_closedBall 0
    obtain ⟨R, hR⟩ := exists_nat_gt (max R₀ 0 + 1)
    have hRpos : (0 : ℝ) < R := lt_of_le_of_lt (by positivity) hR
    have hQ'O : cthickening (η : ℝ) Qs ⊆ ball (0 : ℂ) R := fun z hz => by
      have := hR₀ hz
      rw [mem_closedBall, dist_zero_right] at this
      rw [mem_ball, dist_zero_right]
      linarith [le_max_left R₀ 0]
    have hQsO : Qs ⊆ ball (0 : ℂ) R :=
      (self_subset_cthickening Qs).trans hQ'O
    refine r68_le_of_forall_exp_mul (ξ := 3 * (ξ : ℝ)) fun θ hθ => ?_
    have hθr : (0 : ℝ) < θ := by exact_mod_cast hθ
    
    obtain ⟨jw, hjw⟩ := l6_exists_weight (R : ℝ) (l6Res (R : ℝ) (Fk k)) hθr
    obtain ⟨Mn, hMn⟩ := exists_nat_ge (Mk k)
    set i : ℕ × ℕ × ℕ := (R, jw, Mn) with hi
    have hclose : ∀ z ∈ closedBall (0 : ℂ) R, |r68Fam i z - Fk k z| ≤ θ := by
      intro z hz
      have h1 : |l6W (R : ℝ) jw z - Fk k z| ≤ θ := by
        have := l6_abs_le_norm_res (R := (R : ℝ)) (l6W (R : ℝ) jw - Fk k) hz
        simp only [ContinuousMap.sub_apply] at this
        refine this.trans ?_
        have e : l6Res (R : ℝ) (l6W (R : ℝ) jw - Fk k) = l6Res (R : ℝ) (l6W (R : ℝ) jw) -
            l6Res (R : ℝ) (Fk k) := rfl
        rw [e]; exact hjw.le
      exact (r68_abs_clamp_sub_le _ z ((hFkM k z).trans hMn)).trans h1
    
    have hmoll := r68_eventually_mollCont_close (εn := fun n => (ε n : ℝ))
      (fun n => (ε n).property) hε (Fk k) (r68Fam i) (hFkM k) (r68Fam_bound i) hRpos hθr
      (fun z hz => by rw [abs_sub_comm]; exact hclose z hz)
    have ha : ∀ᶠ n in atTop, r68Y (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n))
        Qs b₁ b₂ η ≤ ENNReal.ofReal (Real.exp ((ξ : ℝ) * (2 * θ))) *
          r68Y (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n))
            (r68Wt V (ε n) (r68Fam i) (i.2.2 : ℝ) (r68Fam_bound i) (h ω))) Qs b₁ b₂ η := by
      filter_upwards [hmoll] with n hn
      unfold r68Y
      have := l6_compactPathInf_lfpp_le (ξ : ℝ) (m (ε n)) isOpen_ball (δ := 2 * θ)
        (φ := r68Wt V (ε n) (r68Fam i) (i.2.2 : ℝ) (r68Fam_bound i) (h ω)) (φ' := ψ k n)
        (fun z hz => by
          simp only [ψ, r68Wt, ContinuousMap.add_apply, hXV n]
          have := hn z (ball_subset_closedBall hz)
          rw [show V (ε n) (h ω) z + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne'
              (Fk k) (Mk k) (hFkM k) z - (V (ε n) (h ω) z + LQGMetric.LFPP.mollCont (ε n : ℝ)
                (ε n).property.ne' (r68Fam i) (i.2.2 : ℝ) (r68Fam_bound i) z) =
              LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' (Fk k) (Mk k) (hFkM k) z -
                LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' (r68Fam i) (i.2.2 : ℝ)
                  (r68Fam_bound i) z by ring]
          exact this) hQ'O (E := cthickening (η : ℝ) (l5Ball b₁))
        (F := cthickening (η : ℝ) (l5Ball b₂))
      rwa [abs_of_pos hξ0] at this
    
    have hb' := hTω i j l b₁ b₂ η hη
    
    have hc : r68Z (PfeAxioms.patchWitness ξ m ε (addFun (h ω) (r68Fam i))) Qs b₁ b₂ ≤
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * θ)) * r68Z (E k) Qs b₁ b₂ := by
      unfold r68Z
      refine r68_compactPathInf_weyl_le_local (Φ (h ω)) _ (E k) hξ0 (r68Fam i) (Fk k) hforget hlω
        (fun p => (hpω (r68Fam i)).2 p) (hE k) (-(i.2.2 : ℝ)) (i.2.2 : ℝ)
        (fun z => abs_le.1 (r68Fam_bound i z)) (N := ball (0 : ℂ) R) (fun x hx => ?_) hQsO
      have := hclose x (ball_subset_closedBall hx)
      have h2 := (abs_le.1 this).2
      nlinarith [hξ0]
    calc liminf (fun n => r68Y (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n))
          Qs b₁ b₂ η) atTop
        ≤ ENNReal.ofReal (Real.exp ((ξ : ℝ) * (2 * θ))) *
            liminf (fun n => r68Y (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n))
              (r68Wt V (ε n) (r68Fam i) (i.2.2 : ℝ) (r68Fam_bound i) (h ω))) Qs b₁ b₂ η) atTop :=
          r68_liminf_le_mul ENNReal.ofReal_ne_top ha
      _ ≤ ENNReal.ofReal (Real.exp ((ξ : ℝ) * (2 * θ))) *
            (ENNReal.ofReal (Real.exp ((ξ : ℝ) * θ)) * r68Z (E k) Qs b₁ b₂) := by
          gcongr; exact hb'.trans hc
      _ = ENNReal.ofReal (Real.exp (3 * (ξ : ℝ) * θ)) * r68Z (E k) Qs b₁ b₂ := by
          rw [← mul_assoc, l6_ofReal_exp_mul]; congr 3; ring
  
  have hεw : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε, Eventually.of_forall fun n => (ε n).property⟩
  have hclosek : ∀ k, ∀ θ : ℝ, 0 < θ → ∀ᶠ n in atTop, ∀ z ∈ PfeAxioms.patchBall k,
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
    have hB' := LQGMetric.DFGPS.abs_heatMollify_sub_locMollify_ofCont_le (Fk k) (Mk k) (hFkM k)
      (ε n : ℝ) hpos z
    have hexpand : locMollifyC (ε n : ℝ) (ε n).property (addFun (h ω) F) z - ψ k n z =
        (locMollify (ε n : ℝ) hpos (h ω) z - heatMollify (ε n : ℝ) (h ω) z) +
          (locMollify (ε n : ℝ) hpos (ofCont (Fk k)) z -
            heatMollify (ε n : ℝ) (ofCont (Fk k)) z) := by
      show locMollify (ε n : ℝ) hpos (addFun (h ω) F) z -
        (X (ε n) ω z + heatMollify (ε n : ℝ) (ofCont (Fk k)) z) = _
      rw [PfeAxioms.locMollify_addFun, PfeAxioms.locMollify_ofCont_congr _ hpos hball, hXω n z]
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
      _ ≤ θ / 2 + θ / 2 := add_le_add hA (hB'.trans hn2)
      _ = θ := by ring
  exact ⟨Fk, Mk, ψ, E, hFkM, hFk, hE, hEconv, hupper, hclosek⟩

end SupercriticalLQGUniqueness.B2.PfeLocal
