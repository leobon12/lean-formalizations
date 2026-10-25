import SupercriticalLQGUniqueness.B2.PfeAxioms.S2LocalCompare
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2WeylLscMain
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteGeometry

 
















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.DFGPS.L217

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
theorem exists_weylScale_lscMetric (Φ : LSCMetric) (hlen : Φ.IsLengthSpace)
    (hforget : Continuous (PfeWeyl.euclidForget Φ))
    (hacross : PfeWeyl.AcrossUnbounded Φ) (hSSA : SelfSmallAnnuli Φ univ)
    (ξ : ℝ) (hξ : 0 ≤ ξ) (F : C(ℂ, ℝ)) :
    ∃ W : LSCMetric, ∀ p, W p = weylScale ξ F Φ p :=
  ⟨⟨fun p => weylScale ξ F Φ p,
    Uniqueness.Toolkit.WeylLength.weylScale_isExtMetric Φ ξ F hforget,
    lowerSemicontinuous_weylScale Φ hlen hforget hacross hSSA ξ hξ F⟩, fun _ => rfl⟩

theorem tendsto_patchApprox_of_local_data
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (Φ : LSCMetric) (hlen : Φ.IsLengthSpace)
    (hforget : Continuous (PfeWeyl.euclidForget Φ))
    (hacross : PfeWeyl.AcrossUnbounded Φ) (hSSA : SelfSmallAnnuli Φ univ)
    (g : DistC) (F : C(ℂ, ℝ))
    (Fk : ℕ → C(ℂ, ℝ)) (Mk : ℕ → ℝ) (hFkM : ∀ k z, |Fk k z| ≤ Mk k)
    (hFk : ∀ k, EqOn F (Fk k) (Metric.closedBall 0 ((k : ℝ) + 3)))
    (ψ : ℕ → ℕ → C(ℂ, ℝ)) (E : ℕ → LSCMetric)
    (hE : ∀ k p, E k p = weylScale (ξ : ℝ) (Fk k) Φ p)
    (hconv : ∀ k, Tendsto (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n))
      atTop (𝓝 (E k)))
    (hsmall : ∀ k, PfeWeyl.SmallAnnulusCosts
      (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n)) (E k)
      (Metric.closedBall 0 ((k : ℝ) + 1 / 2)) (patchBall k))
    (hclose : ∀ k, ∀ θ : ℝ, 0 < θ → ∀ᶠ n in atTop, ∀ z ∈ patchBall k,
      |locMollifyC (ε n : ℝ) (ε n).property g z - ψ k n z| ≤ θ) :
    ∃ W : LSCMetric, (∀ p, W p = weylScale (ξ : ℝ) F Φ p) ∧
      Tendsto (fun k => patchApprox ξ m ε k g) atTop (𝓝 W.toLSCFun) := by
  have hξ0 : (0 : ℝ) ≤ ξ := ξ.property.le
  obtain ⟨W, hW⟩ := exists_weylScale_lscMetric Φ hlen hforget hacross hSSA (ξ : ℝ) hξ0 F
  refine ⟨W, hW, ?_⟩
  
  have hsand : ∀ (k : ℕ) (x y : Metric.ball (0 : ℂ) (k : ℝ)),
      (E k).internal (Metric.ball 0 ((k : ℝ) + 2))
          (⟨(x : ℂ), by
            have := Metric.mem_ball.1 x.property
            exact Metric.mem_ball.2 (by linarith)⟩,
           ⟨(y : ℂ), by
            have := Metric.mem_ball.1 y.property
            exact Metric.mem_ball.2 (by linarith)⟩) ≤
        lowerNeighborhoodObservable
          (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n)) (patchBall k)
          ⟨(x : ℂ), Metric.ball_subset_ball (by linarith) x.property⟩
          ⟨(y : ℂ), Metric.ball_subset_ball (by linarith) y.property⟩ ∧
      lowerNeighborhoodObservable
          (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n)) (patchBall k)
          ⟨(x : ℂ), Metric.ball_subset_ball (by linarith) x.property⟩
          ⟨(y : ℂ), Metric.ball_subset_ball (by linarith) y.property⟩ ≤
        (E k).internal (Metric.ball 0 (k : ℝ)) (x, y) := by
    intro k x y
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hfront : frontier (patchBall k) = Metric.sphere 0 ((k : ℝ) + 1) :=
      frontier_ball 0 (by positivity)
    exact buffered_neighborhood_observable_sandwich (hconv k)
      (fun n => PfeWeyl.isLengthSpace_normalizedLFPPMetric _ _ _)
      (fun n => finitePathsEuclideanContinuous_normalizedLFPPMetric _ _ _)
      (fun n => continuous_euclidForget_normalizedLFPPMetric _ _ _)
      (W := Metric.ball 0 (k : ℝ)) (V := patchBall k)
      (K := Metric.closedBall 0 ((k : ℝ) + 1 / 2)) (Kout := Metric.closedBall 0 ((k : ℝ) + 1))
      (U := Metric.ball 0 ((k : ℝ) + 2))
      (Metric.ball_subset_ball (by linarith))
      ((Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_interior_closedBall)
      Metric.ball_subset_closedBall (isCompact_closedBall _ _)
      (Metric.closedBall_subset_ball (by linarith)) (isOpen_patchBall k)
      (isCompact_closedBall _ _)
      (by rw [hfront]; exact isCompact_sphere _ _)
      (by rw [hfront]; exact NormedSpace.sphere_nonempty.2 (by positivity))
      (by
        rw [hfront]
        rw [Set.disjoint_left]
        intro z hz hz'
        rw [Metric.mem_closedBall] at hz
        rw [Metric.mem_sphere] at hz'
        linarith)
      (hsmall k) x y
  
  have hval : ∀ (k : ℕ) {x y : ℂ} (hx : x ∈ Metric.ball (0 : ℂ) (k : ℝ))
      (hy : y ∈ Metric.ball (0 : ℂ) (k : ℝ)),
      (patchApprox ξ m ε k g).1 (x, y) =
        ((lowerNeighborhoodObservable
          (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n)) (patchBall k)
          ⟨x, Metric.ball_subset_ball (by linarith) hx⟩
          ⟨y, Metric.ball_subset_ball (by linarith) hy⟩ : ℝ≥0∞) : EReal) := by
    intro k x y hx hy
    rw [patchApprox_apply_of_mem ξ m ε k g (Metric.ball_subset_ball (by linarith) hx)
      (Metric.ball_subset_ball (by linarith) hy)]
    have heq := lowerNbhdObs_eq_of_weight_close ξ (fun n => m (ε n))
      (fun n => locMollifyC (ε n : ℝ) (ε n).property g) (ψ k) (isOpen_patchBall k)
      (hclose k) ⟨x, Metric.ball_subset_ball (by linarith) hx⟩
      ⟨y, Metric.ball_subset_ball (by linarith) hy⟩
    exact congrArg (fun t : ℝ≥0∞ => (t : EReal)) heq
  apply tendsto_lscFun_of_sandwich _ W (fun k => (k : ℝ)) tendsto_natCast_atTop_atTop
  · 
    rintro k ⟨x, y⟩ hp1 hp2
    have hx : x ∈ Metric.ball (0 : ℂ) (k : ℝ) := by rwa [Metric.mem_ball, dist_zero_right]
    have hy : y ∈ Metric.ball (0 : ℂ) (k : ℝ) := by rwa [Metric.mem_ball, dist_zero_right]
    rw [hval k hx hy]
    apply EReal.coe_ennreal_le_coe_ennreal_iff.2
    refine le_trans ?_ (hsand k ⟨x, hx⟩ ⟨y, hy⟩).1
    rw [hW (x, y)]
    have hUR : EqOn F (Fk k) (Metric.ball 0 ((k : ℝ) + 2)) := fun z hz =>
      hFk k (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall
        (by linarith)) hz)
    have hxU : x ∈ Metric.ball (0 : ℂ) ((k : ℝ) + 2) := Metric.ball_subset_ball (by linarith) hx
    have hyU : y ∈ Metric.ball (0 : ℂ) ((k : ℝ) + 2) := Metric.ball_subset_ball (by linarith) hy
    exact weylScale_le_internal_of_eqOn Φ (E k) (ξ : ℝ) hξ0 F (Fk k) hforget (hE k)
      (-Mk k) (fun z => (abs_le.1 (hFkM k z)).1) hUR ⟨x, hxU⟩ ⟨y, hyU⟩
  · 
    rintro ⟨x₀, y₀⟩
    set p : ℂ × ℂ := (x₀, y₀) with hpdef
    by_cases htop : W p = ⊤
    · rw [htop]; simp
    apply le_of_forall_gt_imp_ge_of_dense
    intro c hc
    have hc0 : (0 : EReal) ≤ c := le_trans (EReal.coe_ennreal_nonneg _) hc.le
    by_cases hctop : c = ⊤
    · rw [hctop]; exact le_top
    have hcc : (W p : ℝ≥0∞) < c.toENNReal := by
      have := EReal.toENNReal_lt_toENNReal (EReal.coe_ennreal_nonneg _) hc
      rwa [EReal.toENNReal_coe] at this
    obtain ⟨η, hη, hηlt⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hcc
    
    have hlt : weylScale (ξ : ℝ) F Φ p < W p + η := by
      rw [← hW p]; exact ENNReal.lt_add_right htop (by exact_mod_cast hη.ne')
    obtain ⟨P, hP, hP0, hP1, hPlen⟩ := exists_curve_of_weylScale_lt Φ (ξ : ℝ) F hforget hlt
    have hPc := continuousOn_of_isCurve_forget Φ hforget hP
    obtain ⟨R, hR⟩ := ((isCompact_Icc.image_of_continuousOn hPc).isBounded).subset_closedBall 0
    obtain ⟨K₀, hK₀⟩ := exists_nat_gt R
    have hev : ∀ᶠ k in atTop, (patchApprox ξ m ε k g).1 p ≤ (c : EReal) := by
      filter_upwards [eventually_ge_atTop K₀] with k hk
      have hRk : R < (k : ℝ) := lt_of_lt_of_le hK₀ (by exact_mod_cast hk)
      have htr : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ Metric.ball (0 : ℂ) (k : ℝ) := fun t ht =>
        Metric.closedBall_subset_ball hRk (hR ⟨t, ht, rfl⟩)
      have hx : p.1 ∈ Metric.ball (0 : ℂ) (k : ℝ) := by
        have h0 := htr 0 ⟨le_rfl, zero_le_one⟩; rw [hP0] at h0; exact h0
      have hy : p.2 ∈ Metric.ball (0 : ℂ) (k : ℝ) := by
        have h1 := htr 1 ⟨zero_le_one, le_rfl⟩; rw [hP1] at h1; exact h1
      rw [hval k hx hy]
      have hEc : (E k).IsCurve P 0 1 :=
        isCurve_weyl_of_bounded Φ (E k) (ξ : ℝ) hξ0 (Fk k) hforget (hE k) (-Mk k) (Mk k)
          (fun z => abs_le.1 (hFkM k z)) hlen hP
      have hint := internal_trace_pair_le_len (E k) hEc htr
        (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc 0 1) (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Icc 0 1)
      have hlenE : (E k).len P 0 1 = weylWL Φ (ξ : ℝ) F P 0 1 :=
        len_eq_weylWL_of_eqOn Φ (E k) (ξ : ℝ) F (Fk k) hforget (hE k) hP
          (fun t ht => hFk k (Metric.ball_subset_closedBall.trans
            (Metric.closedBall_subset_closedBall (by linarith)) (htr t ht)))
      have hpt : (⟨P 0, htr 0 ⟨le_rfl, zero_le_one⟩⟩ : Metric.ball (0 : ℂ) (k : ℝ)) = ⟨p.1, hx⟩ :=
        Subtype.ext hP0
      have hpt' : (⟨P 1, htr 1 ⟨zero_le_one, le_rfl⟩⟩ : Metric.ball (0 : ℂ) (k : ℝ)) = ⟨p.2, hy⟩ :=
        Subtype.ext hP1
      rw [hpt, hpt'] at hint
      have hchain : lowerNeighborhoodObservable
          (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n)) (patchBall k)
          ⟨p.1, Metric.ball_subset_ball (by linarith) hx⟩
          ⟨p.2, Metric.ball_subset_ball (by linarith) hy⟩ ≤ c.toENNReal := by
        refine ((hsand k ⟨p.1, hx⟩ ⟨p.2, hy⟩).2.trans hint).trans ?_
        rw [hlenE]
        exact hPlen.le.trans hηlt.le
      calc (((lowerNeighborhoodObservable
          (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n)) (patchBall k)
          ⟨p.1, Metric.ball_subset_ball (by linarith) hx⟩
          ⟨p.2, Metric.ball_subset_ball (by linarith) hy⟩ : ℝ≥0∞)) : EReal)
          ≤ ((c.toENNReal : ℝ≥0∞) : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.2 hchain
        _ = c := EReal.coe_toENNReal hc0
    exact limsup_le_of_le (by isBoundedDefault) hev

end SupercriticalLQGUniqueness.B2.PfeAxioms
