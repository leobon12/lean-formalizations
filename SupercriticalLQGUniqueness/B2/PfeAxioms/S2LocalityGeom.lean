import SupercriticalLQGUniqueness.B2.PfeAxioms.S2WeylAlgebra
import SupercriticalLQGUniqueness.B2.PfeLocal.Length

 















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric.MetricGeometry

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem internal_mono (D : LSCMetric) {S S' : Set ℂ} (hSS : S ⊆ S') (x y : S) :
    D.internal S' (⟨x, hSS x.2⟩, ⟨y, hSS y.2⟩) ≤ D.internal S (x, y) := by
  unfold LSCMetric.internal
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun hPS => le_iInf fun ha => le_iInf fun hb => ?_
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <| iInf_le_of_le hP <|
    iInf_le_of_le (fun t ht => hSS (hPS t ht)) <| iInf_le_of_le ha <| iInf_le_of_le hb le_rfl

 
theorem internal_eq_iInf_of_exhaustion (D : LSCMetric)
    (hforget : Continuous (PfeWeyl.euclidForget D)) {U : Set ℂ} (W : ℕ → Set ℂ)
    (hWo : ∀ j, IsOpen (W j)) (hWm : Monotone W) (hWU : ∀ j, W j ⊆ U)
    (hUW : U ⊆ ⋃ j, W j) (x y : U) :
    D.internal U (x, y) = ⨅ (j : ℕ) (hx : (x : ℂ) ∈ W j) (hy : (y : ℂ) ∈ W j),
      D.internal (W j) (⟨x, hx⟩, ⟨y, hy⟩) := by
  apply le_antisymm
  · refine le_iInf fun j => le_iInf fun hx => le_iInf fun hy => ?_
    exact internal_mono D (hWU j) ⟨x, hx⟩ ⟨y, hy⟩
  · conv_rhs => unfold LSCMetric.internal
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun hPU => le_iInf fun ha => le_iInf fun hb => ?_
    have hc := isCompact_Icc.image_of_continuousOn (continuousOn_of_isCurve_forget D hforget hP)
    obtain ⟨j, hj⟩ := hc.elim_directed_cover W hWo
      (by rintro z ⟨t, ht, rfl⟩; exact hUW (hPU t ht)) hWm.directed_le
    have hPW : ∀ t ∈ Icc a b, P t ∈ W j := fun t ht => hj ⟨t, ht, rfl⟩
    have hx : (x : ℂ) ∈ W j := by
      have h0 := hPW a ⟨le_rfl, hP.1⟩; rw [ha] at h0; exact h0
    have hy : (y : ℂ) ∈ W j := by
      have h1 := hPW b ⟨hP.1, le_rfl⟩; rw [hb] at h1; exact h1
    refine (iInf_le_of_le j <| iInf_le_of_le hx <| iInf_le_of_le hy le_rfl).trans ?_
    unfold LSCMetric.internal
    exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <| iInf_le_of_le hP <|
      iInf_le_of_le hPW <| iInf_le_of_le ha <| iInf_le_of_le hb le_rfl

 

 

theorem weylScale_local_le (Φ D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ) (F F' : C(ℂ, ℝ))
    (hforget : Continuous (PfeWeyl.euclidForget Φ))
    (hD : ∀ p, D p = weylScale ξ F Φ p) (hE : ∀ p, E p = weylScale ξ F' Φ p)
    {N : Set ℂ} (hN : IsOpen N) (hFF : EqOn F F' N) {u : ℂ} (hu : u ∈ N) :
    ∃ η : ℝ≥0∞, 0 < η ∧ ∀ v : ℂ, E (u, v) < η → D (u, v) ≤ E (u, v) := by
  have hEforget : Continuous (PfeWeyl.euclidForget E) :=
    Uniqueness.Toolkit.WeylShift.continuous_forget_of_weyl Φ E ξ hξ F' hforget hE
  have hElen : E.IsLengthSpace := isLengthSpace_weylScale Φ hforget ξ hξ F' E hE
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hN u hu
  obtain ⟨η, hη, hηδ⟩ := EMetric.continuousAt_iff.1 (hEforget.continuousAt (x := E.pt u))
    (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
  refine ⟨η, hη, fun v hv => ?_⟩
  refine ENNReal.le_of_forall_pos_le_add fun θ hθ hfin => ?_
  obtain ⟨r, hr, hrη⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hv
  set ε' : ℝ := min (r : ℝ) (θ : ℝ) with hε'
  have hε'0 : 0 < ε' := lt_min (by exact_mod_cast hr) (by exact_mod_cast hθ)
  obtain ⟨Q, a, b, hQ, hQa, hQb, hQlen⟩ := hElen u v hfin ε' hε'0
  have hε'r : ENNReal.ofReal ε' ≤ (r : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have hε'θ : ENNReal.ofReal ε' ≤ (θ : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
  have hQη : E.len Q a b < η :=
    lt_of_le_of_lt (hQlen.trans (add_le_add le_rfl hε'r)) hrη
  have hQN : ∀ t ∈ Icc a b, Q t ∈ N := by
    intro t ht
    apply hball
    have h1 : E (Q a, Q t) ≤ E.len Q a b :=
      (PfeLocal.edist_le_len E Q ht.1).trans (PfeWeyl.len_mono_Icc E Q le_rfl ht.2)
    have h2 : E (Q t, u) < η := by
      rw [E.isExtMetric.2.2.1, ← hQa]; exact lt_of_le_of_lt h1 hQη
    have h3 := hηδ (x := E.pt (Q t)) h2
    rw [Metric.mem_ball]
    have h4 : edist (Q t) u < ENNReal.ofReal δ := h3
    rwa [edist_dist, ENNReal.ofReal_lt_ofReal_iff hδ] at h4
  have hQΦ : Φ.IsCurve Q a b :=
    Uniqueness.Toolkit.WeylShift.curve_back_all_continuous Φ E ξ hξ F' hforget hE hQ
  calc D (u, v) = weylScale ξ F Φ (Q a, Q b) := by rw [hD, hQa, hQb]
    _ ≤ weylWL Φ ξ F Q a b := weylScale_le_weylWL Φ ξ F hforget hQΦ
    _ = E.len Q a b :=
        (len_eq_weylWL_of_eqOn Φ E ξ F F' hforget hE hQΦ fun t ht => hFF (hQN t ht)).symm
    _ ≤ E (u, v) + θ := hQlen.trans (add_le_add le_rfl hε'θ)

 
theorem isCurve_weylScale_of_local (Φ D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ) (F F' : C(ℂ, ℝ))
    (hforget : Continuous (PfeWeyl.euclidForget Φ))
    (hD : ∀ p, D p = weylScale ξ F Φ p) (hE : ∀ p, E p = weylScale ξ F' Φ p)
    {N : Set ℂ} (hN : IsOpen N) (hFF : EqOn F F' N)
    {P : ℝ → ℂ} {a b : ℝ} (hP : E.IsCurve P a b) (hPN : ∀ t ∈ Icc a b, P t ∈ N) :
    D.IsCurve P a b := by
  refine ⟨hP.1, fun t ht => ?_⟩
  obtain ⟨η, hη, hle⟩ := weylScale_local_le Φ D E ξ hξ F F' hforget hD hE hN hFF (hPN t ht)
  have hEc := EMetric.continuousWithinAt_iff'.1 (hP.2 t ht)
  refine EMetric.continuousWithinAt_iff'.2 fun ε hε => ?_
  filter_upwards [hEc (min ε η) (lt_min hε hη)] with s hs
  have hs' : E (P s, P t) < min ε η := hs
  have h1 : E (P t, P s) < η := by
    rw [E.isExtMetric.2.2.1]; exact lt_of_lt_of_le hs' (min_le_right _ _)
  have h2 : D (P t, P s) < ε := by
    refine lt_of_le_of_lt (hle (P s) h1) ?_
    rw [E.isExtMetric.2.2.1]; exact lt_of_lt_of_le hs' (min_le_left _ _)
  show D (P s, P t) < ε
  rw [D.isExtMetric.2.2.1]; exact h2

 
theorem internal_weylScale_congr (Φ D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ) (F F' : C(ℂ, ℝ))
    (hforget : Continuous (PfeWeyl.euclidForget Φ)) (hlen : Φ.IsLengthSpace)
    (hD : ∀ p, D p = weylScale ξ F Φ p) (hE : ∀ p, E p = weylScale ξ F' Φ p)
    (m M : ℝ) (hb : ∀ z, m ≤ F' z ∧ F' z ≤ M)
    {N : Set ℂ} (hN : IsOpen N) (hFF : EqOn F F' N) {S : Set ℂ} (hSN : S ⊆ N) (p : S × S) :
    D.internal S p = E.internal S p := by
  apply le_antisymm
  · unfold LSCMetric.internal
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun hPS => le_iInf fun ha => le_iInf fun hb' => ?_
    have hPΦ := Uniqueness.Toolkit.WeylShift.curve_back_all_continuous Φ E ξ hξ F' hforget hE hP
    have hPD := isCurve_weylScale_of_local Φ D E ξ hξ F F' hforget hD hE hN hFF hP
      (fun t ht => hSN (hPS t ht))
    refine iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <| iInf_le_of_le hPD <|
      iInf_le_of_le hPS <| iInf_le_of_le ha <| iInf_le_of_le hb' (le_of_eq ?_)
    rw [len_eq_weylWL_of_eqOn Φ D ξ F F hforget hD hPΦ (fun _ _ => rfl),
      len_eq_weylWL_of_eqOn Φ E ξ F F' hforget hE hPΦ (fun t ht => hFF (hSN (hPS t ht)))]
  · unfold LSCMetric.internal
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun hPS => le_iInf fun ha => le_iInf fun hb' => ?_
    have hPΦ := Uniqueness.Toolkit.WeylShift.curve_back_all_continuous Φ D ξ hξ F hforget hD hP
    have hPE := isCurve_weyl_of_bounded Φ E ξ hξ F' hforget hE m M hb hlen hPΦ
    refine iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <| iInf_le_of_le hPE <|
      iInf_le_of_le hPS <| iInf_le_of_le ha <| iInf_le_of_le hb' (le_of_eq ?_)
    rw [len_eq_weylWL_of_eqOn Φ D ξ F F hforget hD hPΦ (fun _ _ => rfl),
      len_eq_weylWL_of_eqOn Φ E ξ F F' hforget hE hPΦ (fun t ht => hFF (hSN (hPS t ht)))]

 

 
def exhA (j : ℕ) : ℝ := ((j : ℝ) + 1)⁻¹

def exhW (U : Set ℂ) (j : ℕ) : Set ℂ :=
  Metric.ball 0 (j : ℝ) \ Metric.cthickening (4 * exhA j) Uᶜ

def exhK (U : Set ℂ) (j : ℕ) : Set ℂ :=
  Metric.closedBall 0 ((j : ℝ) + 1 / 2) \ Metric.thickening (7 / 2 * exhA j) Uᶜ

def exhV (U : Set ℂ) (j : ℕ) : Set ℂ :=
  Metric.ball 0 ((j : ℝ) + 1) \ Metric.cthickening (3 * exhA j) Uᶜ

def exhKout (U : Set ℂ) (j : ℕ) : Set ℂ :=
  Metric.closedBall 0 ((j : ℝ) + 1) \ Metric.thickening (3 * exhA j) Uᶜ

def exhU (U : Set ℂ) (j : ℕ) : Set ℂ :=
  Metric.ball 0 ((j : ℝ) + 2) \ Metric.cthickening (2 * exhA j) Uᶜ

theorem exhA_pos (j : ℕ) : 0 < exhA j := inv_pos.2 (by positivity)

theorem exhA_anti {j j' : ℕ} (h : j ≤ j') : exhA j' ≤ exhA j := by
  unfold exhA
  exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)

theorem isOpen_exhW (U : Set ℂ) (j : ℕ) : IsOpen (exhW U j) :=
  Metric.isOpen_ball.sdiff Metric.isClosed_cthickening

theorem isOpen_exhV (U : Set ℂ) (j : ℕ) : IsOpen (exhV U j) :=
  Metric.isOpen_ball.sdiff Metric.isClosed_cthickening

theorem isOpen_exhU (U : Set ℂ) (j : ℕ) : IsOpen (exhU U j) :=
  Metric.isOpen_ball.sdiff Metric.isClosed_cthickening

theorem isCompact_exhK (U : Set ℂ) (j : ℕ) : IsCompact (exhK U j) :=
  (isCompact_closedBall _ _).diff Metric.isOpen_thickening

theorem isCompact_exhKout (U : Set ℂ) (j : ℕ) : IsCompact (exhKout U j) :=
  (isCompact_closedBall _ _).diff Metric.isOpen_thickening

theorem exhW_subset_interior_exhK (U : Set ℂ) (j : ℕ) : exhW U j ⊆ interior (exhK U j) := by
  have ha := exhA_pos j
  refine Subset.trans ?_ (interior_maximal (t := Metric.ball 0 ((j : ℝ) + 1 / 2) \
    Metric.cthickening (7 / 2 * exhA j) Uᶜ) ?_ (Metric.isOpen_ball.sdiff
      Metric.isClosed_cthickening))
  · rintro z ⟨hz1, hz2⟩
    refine ⟨Metric.ball_subset_ball (by linarith) hz1, fun hz => hz2 ?_⟩
    exact Metric.cthickening_mono (by linarith) _ hz
  · rintro z ⟨hz1, hz2⟩
    exact ⟨Metric.ball_subset_closedBall hz1,
      fun hz => hz2 (Metric.thickening_subset_cthickening _ _ hz)⟩

theorem exhK_subset_exhV (U : Set ℂ) (j : ℕ) : exhK U j ⊆ exhV U j := by
  have ha := exhA_pos j
  rintro z ⟨hz1, hz2⟩
  refine ⟨Metric.closedBall_subset_ball (by linarith) hz1, fun hz => hz2 ?_⟩
  exact Metric.cthickening_subset_thickening' (by positivity) (by linarith) _ hz

theorem exhW_subset_exhV (U : Set ℂ) (j : ℕ) : exhW U j ⊆ exhV U j :=
  (exhW_subset_interior_exhK U j).trans (interior_subset.trans (exhK_subset_exhV U j))

theorem exhV_subset_exhKout (U : Set ℂ) (j : ℕ) : exhV U j ⊆ exhKout U j := by
  rintro z ⟨hz1, hz2⟩
  exact ⟨Metric.ball_subset_closedBall hz1,
    fun hz => hz2 (Metric.thickening_subset_cthickening _ _ hz)⟩

theorem exhKout_subset_exhU (U : Set ℂ) (j : ℕ) : exhKout U j ⊆ exhU U j := by
  have ha := exhA_pos j
  rintro z ⟨hz1, hz2⟩
  refine ⟨Metric.closedBall_subset_ball (by linarith) hz1, fun hz => hz2 ?_⟩
  exact Metric.cthickening_subset_thickening' (by positivity) (by linarith) _ hz

theorem exhU_subset (U : Set ℂ) (j : ℕ) : exhU U j ⊆ U := by
  rintro z ⟨-, hz2⟩
  by_contra hz
  exact hz2 (Metric.self_subset_cthickening _ hz)

theorem exhW_subset (U : Set ℂ) (j : ℕ) : exhW U j ⊆ U :=
  (exhW_subset_exhV U j).trans ((exhV_subset_exhKout U j).trans
    ((exhKout_subset_exhU U j).trans (exhU_subset U j)))

theorem exhU_subset_ball (U : Set ℂ) (j : ℕ) : exhU U j ⊆ Metric.ball 0 ((j : ℝ) + 2) :=
  sdiff_subset

theorem exhV_subset_ball (U : Set ℂ) (j : ℕ) : exhV U j ⊆ Metric.ball 0 ((j : ℝ) + 1) :=
  sdiff_subset

theorem exhW_subset_ball (U : Set ℂ) (j : ℕ) : exhW U j ⊆ Metric.ball 0 (j : ℝ) :=
  sdiff_subset

theorem exhK_subset_closedBall (U : Set ℂ) (j : ℕ) :
    exhK U j ⊆ Metric.closedBall 0 ((j : ℝ) + 1 / 2) :=
  sdiff_subset

 
theorem ball_subset_exhV_of_mem_exhK (U : Set ℂ) (j : ℕ) {z : ℂ} (hz : z ∈ exhK U j) :
    Metric.ball z (min (1 / 2) (exhA j / 2)) ⊆ exhV U j := by
  have ha := exhA_pos j
  obtain ⟨hz1, hz2⟩ := hz
  intro w hw
  rw [Metric.mem_ball] at hw
  have hw1 : dist w z < 1 / 2 := lt_of_lt_of_le hw (min_le_left _ _)
  have hw2 : dist w z < exhA j / 2 := lt_of_lt_of_le hw (min_le_right _ _)
  refine ⟨?_, fun hwc => hz2 ?_⟩
  · rw [Metric.mem_closedBall] at hz1
    rw [Metric.mem_ball]
    have := dist_triangle w z 0
    linarith
  · have h1 : z ∈ Metric.thickening (exhA j / 2) (Metric.cthickening (3 * exhA j) Uᶜ) :=
      Metric.mem_thickening_iff.2 ⟨w, hwc, by rw [dist_comm]; exact hw2⟩
    have h2 := Metric.thickening_cthickening_subset (exhA j / 2) (by positivity : (0 : ℝ) ≤
      3 * exhA j) Uᶜ h1
    exact Metric.thickening_mono (by linarith) _ h2

theorem closure_exhV_subset_exhKout (U : Set ℂ) (j : ℕ) : closure (exhV U j) ⊆ exhKout U j :=
  closure_minimal (exhV_subset_exhKout U j) (isCompact_exhKout U j).isClosed

theorem isCompact_closure_exhV (U : Set ℂ) (j : ℕ) : IsCompact (closure (exhV U j)) :=
  (isCompact_exhKout U j).of_isClosed_subset isClosed_closure (closure_exhV_subset_exhKout U j)

theorem closure_exhV_subset (U : Set ℂ) (j : ℕ) : closure (exhV U j) ⊆ U :=
  (closure_exhV_subset_exhKout U j).trans ((exhKout_subset_exhU U j).trans (exhU_subset U j))

theorem isCompact_frontier_exhV (U : Set ℂ) (j : ℕ) : IsCompact (frontier (exhV U j)) :=
  (isCompact_closure_exhV U j).of_isClosed_subset isClosed_frontier frontier_subset_closure

theorem frontier_exhV_nonempty (U : Set ℂ) (j : ℕ) (hne : (exhV U j).Nonempty) :
    (frontier (exhV U j)).Nonempty := by
  refine nonempty_frontier_iff.2 ⟨hne, fun huniv => ?_⟩
  have h : ((((j : ℝ) + 2 : ℝ)) : ℂ) ∈ exhV U j := by rw [huniv]; trivial
  have h2 := exhV_subset_ball U j h
  rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)] at h2
  linarith

theorem disjoint_exhK_frontier_exhV (U : Set ℂ) (j : ℕ) :
    Disjoint (exhK U j) (frontier (exhV U j)) := by
  rw [Set.disjoint_left]
  intro z hzK hzF
  exact hzF.2 ((isOpen_exhV U j).interior_eq.symm ▸ exhK_subset_exhV U j hzK)

theorem monotone_exhW (U : Set ℂ) : Monotone (exhW U) := by
  intro j j' hjj z ⟨hz1, hz2⟩
  refine ⟨Metric.ball_subset_ball (by exact_mod_cast hjj) hz1, fun hz => hz2 ?_⟩
  exact Metric.cthickening_mono (by linarith [exhA_anti hjj]) _ hz

theorem subset_iUnion_exhW {U : Set ℂ} (hU : IsOpen U) : U ⊆ ⋃ j, exhW U j := by
  intro z hz
  have hpos : 0 < Metric.infEDist z Uᶜ := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have := Metric.mem_closure_iff_infEDist_zero.2 h0
    rw [hU.isClosed_compl.closure_eq] at this
    exact this hz
  have ht : Tendsto (fun j : ℕ => ENNReal.ofReal (4 * exhA j)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => 4 * exhA j) atTop (𝓝 (4 * 0)) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4 : ℝ)
      simpa only [exhA, one_div] using this
    rw [mul_zero] at h1
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h1
  obtain ⟨j, hj1, hj2⟩ := ((ht.eventually (gt_mem_nhds hpos)).and
    (tendsto_natCast_atTop_atTop.eventually_gt_atTop ‖z‖)).exists
  refine mem_iUnion.2 ⟨j, ?_, fun hzc => ?_⟩
  · rw [Metric.mem_ball, dist_zero_right]; exact hj2
  · exact (not_le.2 hj1) (Metric.mem_cthickening_iff.1 hzc)

end SupercriticalLQGUniqueness.B2.PfeAxioms
