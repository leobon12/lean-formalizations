import HigherDimLQGMetric.Sec10.LocalCompact

/-! Uniform local control of Weyl perturbations over compact families. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Topology Metric Filter
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Compactness of the perturbation family bounds all scaled Weyl weights on a fixed ball,
uniformly over a bounded interval of scales. -/
theorem s8a_uniform_abs_scaledWeight (hd : 1 ≤ d)
    {F : Set C(Rd d, ℝ)} (hF : IsCompact F) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f ∈ F, ∀ r ∈ Icc 0 R,
      ∀ x ∈ closedBall (0 : Rd d) (n + 2),
        |s8a_scaledWeight f r x| ≤ C := by
  let T : Set (C(Rd d, ℝ) × (ℝ × Rd d)) :=
    F ×ˢ (Icc 0 R ×ˢ closedBall (0 : Rd d) (n + 2))
  have hT : IsCompact T :=
    hF.prod ((isCompact_Icc).prod (isCompact_closedBall _ _))
  let G : C(Rd d, ℝ) × (ℝ × Rd d) → ℝ :=
    fun q => |q.1 (q.2.1 • q.2.2)|
  have hGc : Continuous G := by
    unfold G
    fun_prop
  obtain ⟨B, hB⟩ := hT.bddAbove_image hGc.continuousOn
  have hpoint : ∀ f ∈ F, ∀ r ∈ Icc 0 R,
      ∀ x ∈ closedBall (0 : Rd d) (n + 2), |f (r • x)| ≤ max B 0 := by
    intro f hf r hr x hx
    exact (hB ⟨(f, (r, x)), ⟨hf, hr, hx⟩, rfl⟩).trans (le_max_left _ _)
  refine ⟨2 * max B 0, by positivity, fun f hf r hr x hx => ?_⟩
  have hs : ∀ᵐ u ∂(unitSphereProb d), |f (r • u)| ≤ max B 0 := by
    filter_upwards [ae_unitSphereProb_norm_eq_one d] with u hu
    apply hpoint f hf r hr u
    rw [mem_closedBall, dist_zero_right, hu]
    exact_mod_cast (by omega : 1 ≤ n + 2)
  exact s8a_abs_scaledWeight_le_of_ae hd f r (max B 0) x
    (hpoint f hf r hr x hx) hs

/-- Uniform separation of a compact metric family on two bounded balls. -/
theorem s8a_exists_ball_offdiag_gap
    {K : Set C(Rd d × Rd d, ℝ)} (hK : IsCompact K)
    (hKm : K ⊆ {M | IsContinuousMetric M}) (n m : ℕ) :
    ∃ lmb : ℝ, 0 < lmb ∧ ∀ M ∈ K,
      ∀ x ∈ closedBall (0 : Rd d) n,
      ∀ y ∈ closedBall (0 : Rd d) (n + 2),
        1 / ((m : ℝ) + 1) ≤ ‖y - x‖ → lmb ≤ M (x, y) := by
  let J : Set (Rd d × Rd d) :=
    (closedBall (0 : Rd d) n ×ˢ closedBall (0 : Rd d) (n + 2)) ∩
      {p | 1 / ((m : ℝ) + 1) ≤ ‖p.2 - p.1‖}
  have hJc : IsClosed {p : Rd d × Rd d |
      1 / ((m : ℝ) + 1) ≤ ‖p.2 - p.1‖} := by
    exact isClosed_le continuous_const (by fun_prop)
  have hJ : IsCompact J :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).inter_right hJc
  have hJdiag : ∀ p ∈ J, p.1 ≠ p.2 := by
    intro p hp heq
    have hsep := hp.2
    change 1 / ((m : ℝ) + 1) ≤ ‖p.2 - p.1‖ at hsep
    rw [heq, sub_self, norm_zero] at hsep
    have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  obtain ⟨lmb, hlmb, hgap⟩ := s8a_exists_uniform_offdiag_gap hK hKm hJ hJdiag
  refine ⟨lmb, hlmb, fun M hM x hx y hy hxy => hgap M hM (x, y) ?_⟩
  exact ⟨⟨hx, hy⟩, hxy⟩

/-- The first-exit lower bound controls separated pairs, including pairs whose second point
lies outside the region where the weight is bounded. -/
theorem s8a_weylScale_sep_lower
    {K : Set C(Rd d × Rd d, ℝ)} {M : ContMetric d} (hM : M.1 ∈ K)
    (hMl : M.IsLength) {n m : ℕ} {ρ lmb C : ℝ}
    (hsphere : ∀ M' ∈ K, ∀ x ∈ closedBall (0 : Rd d) n,
      ∀ z ∈ sphere (0 : Rd d) (n + 2), ρ ≤ M' (x, z))
    (hoffdiag : ∀ M' ∈ K, ∀ x ∈ closedBall (0 : Rd d) n,
      ∀ y ∈ closedBall (0 : Rd d) (n + 2),
        1 / ((m : ℝ) + 1) ≤ ‖y - x‖ → lmb ≤ M' (x, y))
    {ξ : ℝ} {f : C(Rd d, ℝ)}
    (hweight : ∀ z ∈ ball (0 : Rd d) (n + 2), -C ≤ ξ * f z)
    {x y : Rd d} (hx : x ∈ closedBall (0 : Rd d) n)
    (hxy : 1 / ((m : ℝ) + 1) ≤ ‖y - x‖) :
    ENNReal.ofReal (Real.exp (-C) * min lmb ρ) ≤ weylScale ξ f M x y := by
  let V : Set (Rd d) := ball 0 (n + 2)
  have hxV : x ∈ V := by
    have hxn : ‖x‖ ≤ (n : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right] using hx
    change dist x 0 < (n : ℝ) + 2
    rw [dist_zero_right]
    linarith
  have hfront : ENNReal.ofReal ρ ≤
      Metric.infEDist (M.pt x) (M.pt '' frontier V) :=
    s8a_uniform_frontier_gap hsphere hM M.2 hx
  have hbase : ENNReal.ofReal (min lmb ρ) ≤
      min (edist (M.pt x) (M.pt y))
        (Metric.infEDist (M.pt x) (M.pt '' frontier V)) := by
    apply le_min
    · rw [M.edist_pt]
      by_cases hy : y ∈ closedBall (0 : Rd d) (n + 2)
      · exact ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans
          (hoffdiag M.1 hM x hx y hy hxy))
      · have hnot : y ∉ V := by
          intro hV
          exact hy (ball_subset_closedBall hV)
        have hnotlt : ¬ edist (M.pt x) (M.pt y) <
            Metric.infEDist (M.pt x) (M.pt '' frontier V) := by
          intro hlt
          exact hnot (M.internal_eq_of_lt_infEDist_frontier hMl isOpen_ball hxV hlt).1
        have hle := (ENNReal.ofReal_le_ofReal (min_le_right lmb ρ)).trans
          (hfront.trans (le_of_not_gt hnotlt))
        simpa only [M.edist_pt] using hle
    · exact (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans hfront
  have hlow := s8a_weylScale_lower_local (y := y) hMl isOpen_ball hxV hweight
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact (mul_le_mul' le_rfl hbase).trans hlow

/-- A pair closer in the base metric than the first-exit radius admits the local Weyl upper
bound through the internal metric. -/
theorem s8a_weylScale_upper_of_ball
    {K : Set C(Rd d × Rd d, ℝ)} {M : ContMetric d} (hM : M.1 ∈ K)
    (hMl : M.IsLength) {n : ℕ} {ρ C : ℝ} (hρ : 0 < ρ)
    (hsphere : ∀ M' ∈ K, ∀ x ∈ closedBall (0 : Rd d) n,
      ∀ z ∈ sphere (0 : Rd d) (n + 2), ρ ≤ M' (x, z))
    {ξ : ℝ} {f : C(Rd d, ℝ)}
    (hweight : ∀ z ∈ ball (0 : Rd d) (n + 2), ξ * f z ≤ C)
    {x y : Rd d} (hx : x ∈ closedBall (0 : Rd d) n)
    (hxy : M.1 (x, y) < ρ) :
    weylScale ξ f M x y ≤ ENNReal.ofReal (Real.exp C * M.1 (x, y)) := by
  let V : Set (Rd d) := ball 0 (n + 2)
  have hxV : x ∈ V := by
    have hxn : ‖x‖ ≤ (n : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right] using hx
    change dist x 0 < (n : ℝ) + 2
    rw [dist_zero_right]
    linarith
  have hfront : ENNReal.ofReal ρ ≤
      Metric.infEDist (M.pt x) (M.pt '' frontier V) :=
    s8a_uniform_frontier_gap hsphere hM M.2 hx
  have hlt : edist (M.pt x) (M.pt y) <
      Metric.infEDist (M.pt x) (M.pt '' frontier V) := by
    rw [M.edist_pt]
    exact ((ENNReal.ofReal_lt_ofReal_iff hρ).2 hxy).trans_le hfront
  have hup := s8a_weylScale_upper_local (y := y) hMl isOpen_ball hxV hweight hlt
  rw [M.edist_pt, ← ENNReal.ofReal_mul (Real.exp_pos _).le] at hup
  exact hup

end HigherDimLQGMetric
