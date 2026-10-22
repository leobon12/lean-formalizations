import HigherDimLQGMetric.Determ.PathResample
import LQGMetric.Papers.LM.T1_7N1

/-! A local modulus for the internal metric in every Euclidean dimension. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {d : ℕ}

theorem determ_local_modulus {D : ContMetric d} (hD : D.IsLength) {R R' : ℝ} (hRR' : R < R')
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ r > 0, ∀ a b : (Rd d), ‖a‖ ≤ R → ‖a - b‖ < r →
      D.internal (Metric.ball 0 R') a b ≤ ENNReal.ofReal κ := by
  by_cases hR : R < 0
  · exact ⟨1, one_pos, fun a b ha _ => absurd (ha.trans_lt hR) (not_lt.2 (norm_nonneg a))⟩
  have hne : (Metric.closedBall (0 : (Rd d)) R).Nonempty := ⟨0, Metric.mem_closedBall_self (not_lt.1 hR)⟩
  -- positive `D`-distance from `cl B_R` to the complement of `B_{R'}`
  set Z : Set D.Space := (D.pt '' Metric.ball (0 : (Rd d)) R')ᶜ with hZ
  have hZc : IsClosed Z := (D.isOpen_image_pt Metric.isOpen_ball).isClosed_compl
  have hpos : ∀ a ∈ Metric.closedBall (0 : (Rd d)) R, 0 < Metric.infEDist (D.pt a) Z := by
    intro a ha
    rw [Metric.infEDist_pos_iff_notMem_closure, hZc.closure_eq, hZ, notMem_compl_iff]
    exact D.mem_image_pt.2 (Metric.mem_ball.2 (by
      simpa using (Metric.mem_closedBall.1 ha).trans_lt hRR'))
  have hcont : ContinuousOn (fun a => Metric.infEDist (D.pt a) Z) (Metric.closedBall 0 R) :=
    (Metric.continuous_infEDist.comp D.continuous_pt).continuousOn
  obtain ⟨a₀, ha₀, hmin⟩ := (isCompact_closedBall (0 : (Rd d)) R).exists_isMinOn hne hcont
  obtain ⟨ρ, -, hρ0, hρ⟩ := ENNReal.lt_iff_exists_real_btwn.1 (hpos a₀ ha₀)
  have hρpos : 0 < ρ := ENNReal.ofReal_pos.1 hρ0
  -- uniform continuity of `D` on `cl B_{R'} × cl B_{R'}`
  have huc := ((isCompact_closedBall (0 : (Rd d)) R').prod
    (isCompact_closedBall (0 : (Rd d)) R')).uniformContinuousOn_of_continuous D.1.continuous.continuousOn
  obtain ⟨δ, hδ, hδd⟩ := Metric.uniformContinuousOn_iff.1 huc (min κ ρ) (lt_min hκ hρpos)
  refine ⟨min δ (R' - R), lt_min hδ (by linarith), fun a b ha hab => ?_⟩
  have hab' : ‖a - b‖ < R' - R := hab.trans_le (min_le_right _ _)
  have haR : ‖a‖ ≤ R' := by linarith
  have hbR : ‖b‖ ≤ R' := by
    have := norm_sub_norm_le b a
    rw [norm_sub_rev] at this
    linarith
  have hdab : D.1 (a, b) < min κ ρ := by
    have h := hδd (a, a) ⟨by simpa using haR, by simpa using haR⟩ (a, b)
      ⟨by simpa using haR, by simpa using hbR⟩ (by
        rw [Prod.dist_eq, dist_self, dist_eq_norm]
        exact (max_eq_right (norm_nonneg _)).trans_lt (hab.trans_le (min_le_left _ _)))
    rwa [D.2.self_eq_zero a, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg (ContMetric.nonneg D a b)] at h
  have hball : Metric.eball (D.pt a) (ENNReal.ofReal ρ) ⊆ D.pt '' Metric.ball 0 R' := by
    intro x hx
    by_contra hxn
    have h1 : Metric.infEDist (D.pt a) Z ≤ edist (D.pt a) x := Metric.infEDist_le_edist_of_mem hxn
    have h2 : Metric.infEDist (D.pt a₀) Z ≤ Metric.infEDist (D.pt a) Z :=
      hmin (Metric.mem_closedBall.2 (by simpa using ha))
    have h3 : edist x (D.pt a) < ENNReal.ofReal ρ := Metric.mem_eball.1 hx
    rw [edist_comm] at h3
    exact absurd (hρ.trans_le (h2.trans h1)) (not_lt.2 h3.le)
  have hxy : edist (D.pt a) (D.pt b) < ENNReal.ofReal ρ := by
    rw [ContMetric.edist_pt]
    exact (ENNReal.ofReal_lt_ofReal_iff hρpos).2 (hdab.trans_le (min_le_right _ _))
  unfold ContMetric.internal
  rw [internalEDist_eq_edist_of_ball_subset hD hball hxy, ContMetric.edist_pt]
  exact ENNReal.ofReal_le_ofReal (hdab.le.trans (min_le_left _ _))


theorem determ_near_bound {D : ContMetric d} (hD : D.IsLength) {R R' : ℝ} (hRR' : R < R') {κ : ℝ}
    (hκ : 0 < κ) :
    ∃ r > 0, ∀ (a b : ℝ) (P : ℝ → (Rd d)), ContinuousOn P (Icc a b) →
      MapsTo P (Icc a b) (Metric.closedBall 0 R) →
      ∀ ε' : ℝ≥0∞, D.len P a b ≤ D.internal (Metric.ball 0 R) (P a) (P b) + ε' →
      ∀ s u : ℝ, a ≤ s → s ≤ u → u ≤ b → ‖P s - P u‖ < r →
        D.len P s u + D.internal (Metric.ball 0 R') (P a) (P b) ≤
          D.internal (Metric.ball 0 R) (P a) (P b) + ε' + ENNReal.ofReal κ := by
  obtain ⟨r, hr, hmod⟩ := determ_local_modulus hD hRR' hκ
  refine ⟨r, hr, fun a b P hP hPm ε' hnear s u hs hsu hu hsu' => ?_⟩
  have hY : MapsTo (D.pt ∘ P) (Icc a b) (D.pt '' Metric.ball 0 R') := fun t ht =>
    ⟨P t, Metric.mem_ball.2 ((Metric.mem_closedBall.1 (hPm ht)).trans_lt hRR'), rfl⟩
  have h := LQGMetric.LM.t17_replace (X := D.Space) (P := D.pt ∘ P) (D.continuous_pt.comp_continuousOn hP) hY
    hs hsu hu
  have hPs : ‖P s‖ ≤ R := by simpa using Metric.mem_closedBall.1 (hPm ⟨hs, hsu.trans hu⟩)
  have hm := hmod (P s) (P u) hPs hsu'
  calc D.len P s u + D.internal (Metric.ball 0 R') (P a) (P b)
      ≤ D.len P a b + D.internal (Metric.ball 0 R') (P s) (P u) := h
    _ ≤ D.internal (Metric.ball 0 R) (P a) (P b) + ε' + ENNReal.ofReal κ := add_le_add hnear hm

/-- first and last hits of a closed set `K` by a curve on `[0,1]` -/
theorem determ_first_last_hit {P : ℝ → (Rd d)} {a b : ℝ} (hP : ContinuousOn P (Icc a b)) {K : Set (Rd d)}
    (hK : IsClosed K) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (hPt₀ : P t₀ ∈ K) :
    ∃ s u : ℝ, a ≤ s ∧ s ≤ u ∧ u ≤ b ∧ P s ∈ K ∧ P u ∈ K ∧
      ∀ t ∈ Icc a b, P t ∈ K → s ≤ t ∧ t ≤ u := by
  have hT : IsClosed (Icc a b ∩ P ⁻¹' K) := hP.preimage_isClosed_of_isClosed isClosed_Icc hK
  have hc : IsCompact (Icc a b ∩ P ⁻¹' K) := isCompact_Icc.of_isClosed_subset hT
    inter_subset_left
  have hn : (Icc a b ∩ P ⁻¹' K).Nonempty := ⟨t₀, ht₀, hPt₀⟩
  obtain ⟨hs1, hs2⟩ := hc.sInf_mem hn
  obtain ⟨hu1, hu2⟩ := hc.sSup_mem hn
  refine ⟨_, _, hs1.1, csInf_le_csSup hn hc.bddBelow hc.bddAbove, hu1.2, hs2, hu2,
    fun t ht hPt => ⟨csInf_le hc.bddBelow ⟨ht, hPt⟩, le_csSup hc.bddAbove ⟨ht, hPt⟩⟩⟩

/-- Diameter of a closed translated cube. -/
theorem determ_closure_cube_norm {ε : ℝ} (hε : 0 ≤ ε)
    {θ : Fin d → ℝ} {k : Fin d → ℤ} {x y : Rd d}
    (hx : x ∈ closure (determCube ε θ k))
    (hy : y ∈ closure (determCube ε θ k)) :
    ‖x - y‖ ≤ Real.sqrt d * ε := by
  have hx' := determ_closure_cube_bounds ε θ k hx
  have hy' := determ_closure_cube_bounds ε θ k hy
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Fin d, ‖(x - y).ofLp i‖ ^ 2 ≤ d * ε ^ 2 := by
    calc ∑ i : Fin d, ‖(x - y).ofLp i‖ ^ 2 ≤ ∑ _i : Fin d, ε ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := hx' i
          have h2 := hy' i
          have e : (x - y).ofLp i = x i - y i := rfl
          rw [e, Real.norm_eq_abs, sq_abs]
          nlinarith
      _ = d * ε ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ i : Fin d, ‖(x - y).ofLp i‖ ^ 2) ≤ Real.sqrt (d * ε ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * ε := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hε]

end HigherDimLQGMetric
