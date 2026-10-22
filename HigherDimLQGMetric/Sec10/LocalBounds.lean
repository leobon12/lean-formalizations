import HigherDimLQGMetric.Sec10.BoundedCase
import HigherDimLQGMetric.Metric.WeylCompose

/-!
# Local first-exit bounds for Weyl perturbations

The lower bound protects distances from shortcuts through regions where the perturbation is
unbounded. The upper bound uses internal metrics for sufficiently close pairs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ} {ξ : ℝ} {f : C(Rd d, ℝ)} {D : ContMetric d}
  {V : Set (Rd d)} {x y : Rd d}

/-- A lower weight bound on an open set protects the distance by the first-exit cost. -/
theorem s8a_weylScale_lower_local (hD : D.IsLength) (hV : IsOpen V) (hx : x ∈ V) {a : ℝ}
    (ha : ∀ z ∈ V, a ≤ ξ * f z) :
    ENNReal.ofReal (Real.exp a) *
      min (edist (D.pt x) (D.pt y))
        (Metric.infEDist (D.pt x) (D.pt '' frontier V)) ≤
      weylScale ξ f D x y := by
  refine le_weylScale fun L P hL hc hu h0 h1 => ?_
  by_cases hexit : ∃ t ∈ Icc 0 L, P t ∉ V
  · have hcost := le_weylCost_of_exit hL hc hu hV ha hexit
    rw [h0] at hcost
    rw [D.image_pt_compl, infEDist_compl_eq_infEDist_frontier hD
      (D.isOpen_image_pt hV) ⟨x, hx, rfl⟩, ← D.image_pt_frontier] at hcost
    exact (mul_le_mul' le_rfl (min_le_right _ _)).trans hcost
  · have hstay : ∀ t ∈ Icc 0 L, P t ∈ V := by
      intro t ht
      by_contra hnot
      exact hexit ⟨t, ht, hnot⟩
    have hlen : edist (D.pt x) (D.pt y) ≤ ENNReal.ofReal L := by
      rw [← h0, ← h1]
      calc edist (D.pt (P 0)) (D.pt (P L))
          ≤ curveLength (D.pt ∘ P) 0 L := edist_le_curveLength _ hL
        _ = ENNReal.ofReal L := by
          rw [curveLength_of_hasUnitSpeedOn hu ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩,
            sub_zero]
    calc ENNReal.ofReal (Real.exp a) *
          min (edist (D.pt x) (D.pt y))
            (Metric.infEDist (D.pt x) (D.pt '' frontier V))
        ≤ ENNReal.ofReal (Real.exp a) * ENNReal.ofReal L :=
          mul_le_mul' le_rfl ((min_le_left _ _).trans hlen)
      _ = ∫⁻ _t in Icc 0 L, ENNReal.ofReal (Real.exp a) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero]
      _ ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) :=
        setLIntegral_mono' measurableSet_Icc fun t ht =>
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (ha _ (hstay t ht)))

/-- For pairs closer than the base-metric distance to the boundary, internal comparison
gives a local upper bound. -/
theorem s8a_weylScale_upper_local (hD : D.IsLength) (hV : IsOpen V) (hx : x ∈ V)
    {b : ℝ} (hb : ∀ z ∈ V, ξ * f z ≤ b)
    (hxy : edist (D.pt x) (D.pt y) <
      Metric.infEDist (D.pt x) (D.pt '' frontier V)) :
    weylScale ξ f D x y ≤
      ENNReal.ofReal (Real.exp b) * edist (D.pt x) (D.pt y) := by
  obtain ⟨_, hint⟩ := D.internal_eq_of_lt_infEDist_frontier hD hV hx hxy
  calc weylScale ξ f D x y ≤ weylScaleOn ξ f D V x y :=
      weylScale_le_weylScaleOn
    _ ≤ ENNReal.ofReal (Real.exp b) * D.internal V x y :=
      weylScaleOn_le_of_le hb
    _ = ENNReal.ofReal (Real.exp b) * edist (D.pt x) (D.pt y) := by rw [hint]

/-- Compact families of continuous metrics are uniformly separated between a closed ball and
a larger Euclidean sphere. -/
theorem s8a_exists_uniform_sphere_gap
    {K : Set C(Rd d × Rd d, ℝ)} (hK : IsCompact K)
    (hKm : K ⊆ {M | IsContinuousMetric M}) (n : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ M ∈ K,
      ∀ x ∈ closedBall (0 : Rd d) n,
      ∀ z ∈ sphere (0 : Rd d) (n + 2), ρ ≤ M (x, z) := by
  let T : Set ((C(Rd d × Rd d, ℝ) × Rd d) × Rd d) :=
    (K ×ˢ closedBall (0 : Rd d) n) ×ˢ sphere (0 : Rd d) (n + 2)
  have hT : IsCompact T :=
    (hK.prod (isCompact_closedBall _ _)).prod (isCompact_sphere _ _)
  let F : ((C(Rd d × Rd d, ℝ) × Rd d) × Rd d) → ℝ :=
    fun q => q.1.1 (q.1.2, q.2)
  have hFc : Continuous F :=
    continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  have hpos : ∀ q ∈ T, 0 < F q := by
    rintro ⟨⟨M, x⟩, z⟩ ⟨⟨hM, hx⟩, hz⟩
    have hMx : IsContinuousMetric M := hKm hM
    have hxz : x ≠ z := by
      intro heq
      subst z
      have hxN : ‖x‖ ≤ (n : ℝ) := by simpa only [mem_closedBall, dist_zero_right] using hx
      have hzN : ‖x‖ = (n : ℝ) + 2 := by
        simpa only [mem_sphere, dist_zero_right, Nat.cast_add, Nat.cast_ofNat] using hz
      linarith
    have hnn := s8a_metricFn_nonneg hMx x z
    have hne : M (x, z) ≠ 0 := fun h0 => hxz (hMx.eq_of_eq_zero x z h0)
    exact lt_of_le_of_ne hnn (Ne.symm hne)
  by_cases hTn : T.Nonempty
  · obtain ⟨q, hq, hmin⟩ := hT.exists_isMinOn hTn hFc.continuousOn
    refine ⟨F q, hpos q hq, fun M hM x hx z hz => ?_⟩
    change F q ≤ F ((M, x), z)
    exact hmin ⟨⟨hM, hx⟩, hz⟩
  · refine ⟨1, one_pos, fun M hM x hx z hz => ?_⟩
    have ht : ((M, x), z) ∈ T := ⟨⟨hM, hx⟩, hz⟩
    exact False.elim (hTn ⟨((M, x), z), ht⟩)

/-- The uniform sphere gap bounds the base-metric distance to the frontier of the open ball. -/
theorem s8a_uniform_frontier_gap
    {K : Set C(Rd d × Rd d, ℝ)}
    {n : ℕ} {ρ : ℝ}
    (hgap : ∀ M ∈ K, ∀ x ∈ closedBall (0 : Rd d) n,
      ∀ z ∈ sphere (0 : Rd d) (n + 2), ρ ≤ M (x, z))
    {M : C(Rd d × Rd d, ℝ)} (hM : M ∈ K) (hMm : IsContinuousMetric M)
    {x : Rd d} (hx : x ∈ closedBall (0 : Rd d) n) :
    ENNReal.ofReal ρ ≤
      Metric.infEDist (ContMetric.pt (⟨M, hMm⟩ : ContMetric d) x)
        (ContMetric.pt (⟨M, hMm⟩ : ContMetric d) '' frontier (ball (0 : Rd d) (n + 2))) := by
  apply Metric.le_infEDist.mpr
  rintro w ⟨z, hz, rfl⟩
  have hzs : z ∈ sphere (0 : Rd d) (n + 2) := frontier_ball_subset_sphere hz
  rw [ContMetric.edist_pt]
  exact ENNReal.ofReal_le_ofReal (hgap M hM x hx z hzs)

/-- The pointwise supremum of a compact family of metrics has a uniform near-diagonal modulus
on every Euclidean ball. -/
theorem s8a_exists_supEnvelope_modulus
    {K : Set C(Rd d × Rd d, ℝ)} (hK : IsCompact K)
    (hKn : K.Nonempty) (hKm : K ⊆ {M | IsContinuousMetric M})
    (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ closedBall (0 : Rd d) n,
      ∀ y ∈ closedBall (0 : Rd d) n,
        ‖x - y‖ ≤ δ → s8a_supEnvelope K (x, y) < η := by
  have hBall : IsCompact (closedBall (0 : Rd d) n) := isCompact_closedBall _ _
  have hUC : UniformContinuousOn (s8a_supEnvelope K)
      (closedBall (0 : Rd d) n ×ˢ closedBall (0 : Rd d) n) :=
    (hBall.prod hBall).uniformContinuousOn_of_continuous
      (s8a_continuous_supEnvelope K hK).continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hUC η hη
  refine ⟨δ / 2, half_pos hδ, fun x hx y hy hxy => ?_⟩
  have hp : (x, y) ∈ closedBall (0 : Rd d) n ×ˢ closedBall (0 : Rd d) n := ⟨hx, hy⟩
  have hq : (x, x) ∈ closedBall (0 : Rd d) n ×ˢ closedBall (0 : Rd d) n := ⟨hx, hx⟩
  have hdist : dist (x, y) (x, x) < δ := by
    rw [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg), dist_eq_norm,
      norm_sub_rev]
    exact lt_of_le_of_lt hxy (half_lt_self hδ)
  have hv := hmod (x, y) hp (x, x) hq hdist
  rw [s8a_supEnvelope_diag hKn hKm x, Real.dist_eq, sub_zero, abs_lt] at hv
  exact hv.2

/-- Uniform positive distance on a compact family of metrics and compact off-diagonal set. -/
theorem s8a_exists_uniform_offdiag_gap
    {K : Set C(Rd d × Rd d, ℝ)} (hK : IsCompact K)
    (hKm : K ⊆ {M | IsContinuousMetric M})
    {J : Set (Rd d × Rd d)} (hJ : IsCompact J)
    (hJdiag : ∀ p ∈ J, p.1 ≠ p.2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ M ∈ K, ∀ p ∈ J, ρ ≤ M p := by
  let T : Set (C(Rd d × Rd d, ℝ) × (Rd d × Rd d)) := K ×ˢ J
  have hT : IsCompact T := hK.prod hJ
  let F : C(Rd d × Rd d, ℝ) × (Rd d × Rd d) → ℝ := fun q => q.1 q.2
  have hFc : Continuous F := continuous_eval
  have hpos : ∀ q ∈ T, 0 < F q := by
    rintro ⟨M, p⟩ ⟨hM, hp⟩
    have hMm := hKm hM
    have hnn := s8a_metricFn_nonneg hMm p.1 p.2
    have hne : M p ≠ 0 := fun h0 => hJdiag p hp (hMm.eq_of_eq_zero p.1 p.2 h0)
    exact lt_of_le_of_ne hnn (Ne.symm hne)
  by_cases hTn : T.Nonempty
  · obtain ⟨q, hq, hmin⟩ := hT.exists_isMinOn hTn hFc.continuousOn
    refine ⟨F q, hpos q hq, fun M hM p hp => ?_⟩
    change F q ≤ F (M, p)
    exact hmin ⟨hM, hp⟩
  · refine ⟨1, one_pos, fun M hM p hp => ?_⟩
    have ht : (M, p) ∈ T := ⟨hM, hp⟩
    exact False.elim (hTn ⟨(M, p), ht⟩)

end HigherDimLQGMetric
