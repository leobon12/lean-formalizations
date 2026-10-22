import HigherDimLQGContinuity.Grid.InterpBound
import HigherDimLQGContinuity.Grid.Borel

/-! Uniform Cauchy estimates and the positive-window profile limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The geometric tail estimate for the interpolants on one good spatial ball. -/
theorem supd_interpProfile_tail_le (d : ℕ) {lo hi R : ℝ} (h : lo < hi)
    {g : DistRd d} {J : ℕ}
    (hg : ∀ j ≥ J, g ∉ posBad d lo hi R j) :
    ∀ j ≥ J, ∀ i ≥ j, ∀ ξ : ℝ,
      supDistLU d R (interpProfile d lo hi i ξ g) (interpProfile d lo hi j ξ g) ≤
        ENNReal.ofReal (endA (j + 5) - endA (i + 5)) := by
  intro j hj i hij
  induction i, hij using Nat.le_induction with
  | base =>
    intro ξ
    simp [supDistLU]
  | succ i hij ih =>
    intro ξ
    have hiJ : J ≤ i := hj.trans hij
    have hstep := supd_interpProfile_succ_le d h i ξ (hg i hiJ)
    have hprev := ih ξ
    have htail : 0 ≤ endA (j + 5) - endA (i + 5) :=
      sub_nonneg.2 (endA_anti (by omega))
    have hδ : 0 ≤ posDelta i := (posDelta_pos i).le
    calc
      supDistLU d R (interpProfile d lo hi (i + 1) ξ g)
          (interpProfile d lo hi j ξ g) ≤
          supDistLU d R (interpProfile d lo hi (i + 1) ξ g)
            (interpProfile d lo hi i ξ g) +
          supDistLU d R (interpProfile d lo hi i ξ g)
            (interpProfile d lo hi j ξ g) := endpt_supDistLU_triangle
      _ ≤ ENNReal.ofReal (posDelta i) +
          ENNReal.ofReal (endA (j + 5) - endA (i + 5)) := add_le_add hstep hprev
      _ = ENNReal.ofReal (endA (j + 5) - endA (i + 1 + 5)) := by
        rw [← ENNReal.ofReal_add hδ htail]
        congr 1
        change endA (i + 6) + (endA (j + 5) - endA (i + 5)) =
          endA (j + 5) - endA (i + 1 + 5)
        rw [show i + 6 = i + 5 + 1 by omega,
          show i + 1 + 5 = i + 5 + 1 by omega, endA_succ]
        ring

theorem supd_interpProfile_tail_bound (d : ℕ) {lo hi R : ℝ} (h : lo < hi)
    {g : DistRd d} {J : ℕ}
    (hg : ∀ j ≥ J, g ∉ posBad d lo hi R j)
    {j i : ℕ} (hj : J ≤ j) (hij : j ≤ i) (ξ : ℝ) :
    supDistLU d R (interpProfile d lo hi i ξ g) (interpProfile d lo hi j ξ g) ≤
      ENNReal.ofReal (endA (j + 5)) := by
  calc
    _ ≤ ENNReal.ofReal (endA (j + 5) - endA (i + 5)) :=
      supd_interpProfile_tail_le d h hg j hj i hij ξ
    _ ≤ ENNReal.ofReal (endA (j + 5)) :=
      ENNReal.ofReal_le_ofReal (by linarith [(endA_pos (i + 5)).le])

theorem cauchySeq_interpProfile (d : ℕ) {lo hi : ℝ} (h : lo < hi)
    {g : DistRd d} (hg : g ∈ posGood d lo hi) (ξ : ℝ) :
    CauchySeq (fun j : ℕ => interpProfile d lo hi j ξ g) := by
  rw [ContinuousMap.hasBasis_compactConvergenceUniformity.cauchySeq_iff]
  intro ⟨K, V⟩ ⟨hK, hV⟩
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.mp hV
  obtain ⟨r, hKr⟩ := hK.isBounded.subset_closedBall (0 : Rd d × Rd d)
  obtain ⟨R, hR⟩ := exists_nat_ge r
  have hgoodR : ∃ J : ℕ, ∀ j ≥ J, g ∉ posBad d lo hi (R + 1) j := by
    have h := (Set.mem_iInter.mp hg) R
    rcases Set.mem_iUnion.mp h with ⟨J, hJ⟩
    refine ⟨J, fun j hj => ?_⟩
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hJ j) hj
  obtain ⟨J, hJ⟩ := hgoodR
  have htail0 : Tendsto (fun j : ℕ => endA (j + 5)) atTop (𝓝 0) :=
    tendsto_endA.comp (tendsto_add_atTop_nat 5)
  obtain ⟨N, hN, hNJ⟩ :=
    ((htail0.eventually (Iio_mem_nhds hε)).and (eventually_ge_atTop J)).exists
  refine ⟨N, fun m hm n hn p hp => ?_⟩
  have hRp : p ∈ closedBall (0 : Rd d) (R + 1) ×ˢ
      closedBall (0 : Rd d) (R + 1) := by
    have hp0 := hKr hp
    have hpnorm : ‖p‖ ≤ r := by
      rwa [mem_closedBall, dist_zero_right] at hp0
    constructor
    · rw [mem_closedBall, dist_zero_right]
      have hR' : r ≤ (R : ℝ) := hR
      linarith [norm_fst_le p]
    · rw [mem_closedBall, dist_zero_right]
      have hR' : r ≤ (R : ℝ) := hR
      linarith [norm_snd_le p]
  have hbound : supDistLU d (R + 1) (interpProfile d lo hi m ξ g)
      (interpProfile d lo hi n ξ g) ≤ ENNReal.ofReal (endA (N + 5)) := by
    rcases le_total m n with hmn | hnm
    · have h1 := supd_interpProfile_tail_bound d h hJ (hNJ.trans hm) hmn ξ
      rw [endpt_supDistLU_comm]
      exact h1.trans (ENNReal.ofReal_le_ofReal (endA_anti (by omega)))
    · have h1 := supd_interpProfile_tail_bound d h hJ (hNJ.trans hn) hnm ξ
      exact h1.trans (ENNReal.ofReal_le_ofReal (endA_anti (by omega)))
  have habs := endpt_abs_sub_le_of_supDistLU_le (endA_pos _).le hbound hRp
  apply hεV
  rw [Real.dist_eq]
  exact habs.trans_lt hN

/-- The compact-open limit of logarithmic profiles on the good event. -/
def limitProfile (d : ℕ) (lo hi : ℝ) (ξ : ℝ) (g : DistRd d) : C(Rd d × Rd d, ℝ) :=
  by
    classical
    exact if g ∈ posGood d lo hi then
      limUnder atTop (fun j : ℕ => interpProfile d lo hi j ξ g)
    else 0

theorem tendsto_interpProfile_limit (d : ℕ) {lo hi : ℝ} (h : lo < hi)
    {g : DistRd d} (hg : g ∈ posGood d lo hi) (ξ : ℝ) :
    Tendsto (fun j : ℕ => interpProfile d lo hi j ξ g) atTop
      (𝓝 (limitProfile d lo hi ξ g)) := by
  simpa [limitProfile, hg] using
    (cauchySeq_interpProfile d h hg ξ).tendsto_limUnder

theorem supd_limitProfile_interp_le (d : ℕ) {lo hi R : ℝ} (h : lo < hi)
    {g : DistRd d} (hg : g ∈ posGood d lo hi) {J : ℕ}
    (hJ : ∀ j ≥ J, g ∉ posBad d lo hi R j)
    {j : ℕ} (hj : J ≤ j) (ξ : ℝ) :
    supDistLU d R (limitProfile d lo hi ξ g) (interpProfile d lo hi j ξ g) ≤
      ENNReal.ofReal (endA (j + 5)) := by
  apply endpt_supDistLU_le_iff.2
  intro p hp
  have hlim : Tendsto (fun i : ℕ => interpProfile d lo hi i ξ g p) atTop
      (𝓝 (limitProfile d lo hi ξ g p)) :=
    (continuous_eval_const p).tendsto _ |>.comp
      (tendsto_interpProfile_limit d h hg ξ)
  have habs : |limitProfile d lo hi ξ g p - interpProfile d lo hi j ξ g p| ≤
      endA (j + 5) := by
    apply le_of_tendsto (hlim.sub_const _).abs
    filter_upwards [eventually_ge_atTop j] with i hi
    exact endpt_abs_sub_le_of_supDistLU_le (endA_pos _).le
      (supd_interpProfile_tail_bound d h hJ hj hi ξ) hp
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal habs

/-- On the good event the profile limit is continuous on the whole parameter line. -/
theorem continuous_limitProfile (d : ℕ) {lo hi : ℝ} (h : lo < hi)
    {g : DistRd d} (hg : g ∈ posGood d lo hi) :
    Continuous (fun ξ => limitProfile d lo hi ξ g) := by
  apply continuous_of_uniform_approx_of_continuous
  intro U hU
  obtain ⟨K, V, hK, hV, hKU⟩ :=
    ContinuousMap.mem_compactConvergence_entourage_iff U |>.mp hU
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.mp hV
  obtain ⟨r, hKr⟩ := hK.isBounded.subset_closedBall (0 : Rd d × Rd d)
  obtain ⟨R, hR⟩ := exists_nat_ge r
  have hgoodR : ∃ J : ℕ, ∀ j ≥ J, g ∉ posBad d lo hi (R + 1) j := by
    have h := (Set.mem_iInter.mp hg) R
    rcases Set.mem_iUnion.mp h with ⟨J, hJ⟩
    exact ⟨J, fun j hj => Set.mem_iInter.mp (Set.mem_iInter.mp hJ j) hj⟩
  obtain ⟨J, hJ⟩ := hgoodR
  have htail0 : Tendsto (fun j : ℕ => endA (j + 5)) atTop (𝓝 0) :=
    tendsto_endA.comp (tendsto_add_atTop_nat 5)
  obtain ⟨N, hN, hNJ⟩ :=
    ((htail0.eventually (Iio_mem_nhds hε)).and (eventually_ge_atTop J)).exists
  refine ⟨fun ξ => interpProfile d lo hi N ξ g,
    continuous_interpProfile d lo hi N g, fun ξ => hKU ?_⟩
  intro p hp
  have hRp : p ∈ closedBall (0 : Rd d) (R + 1) ×ˢ
      closedBall (0 : Rd d) (R + 1) := by
    have hp0 := hKr hp
    have hpnorm : ‖p‖ ≤ r := by
      rwa [mem_closedBall, dist_zero_right] at hp0
    constructor
    · rw [mem_closedBall, dist_zero_right]
      have hR' : r ≤ (R : ℝ) := hR
      linarith [norm_fst_le p]
    · rw [mem_closedBall, dist_zero_right]
      have hR' : r ≤ (R : ℝ) := hR
      linarith [norm_snd_le p]
  have hbound := supd_limitProfile_interp_le d h hg hJ hNJ ξ
  have habs := endpt_abs_sub_le_of_supDistLU_le (endA_pos _).le hbound hRp
  apply hεV
  rw [Real.dist_eq]
  exact habs.trans_lt hN

theorem limitProfile_nonneg (d : ℕ) {lo hi : ℝ} (h : lo < hi)
    (ξ : ℝ) (g : DistRd d) : 0 ≤ limitProfile d lo hi ξ g := by
  classical
  by_cases hg : g ∈ posGood d lo hi
  · intro p
    have hlim : Tendsto (fun j : ℕ => interpProfile d lo hi j ξ g p) atTop
        (𝓝 (limitProfile d lo hi ξ g p)) :=
      (continuous_eval_const p).tendsto _ |>.comp
        (tendsto_interpProfile_limit d h hg ξ)
    exact ge_of_tendsto hlim (Eventually.of_forall fun j =>
      interpProfile_nonneg d lo hi j ξ g p)
  · simp [limitProfile, hg]

/-- The good-event patched approximants converge pointwise in the continuous-map space
on the full parameter-field product. -/
def approxProfile (d : ℕ) (lo hi : ℝ) (j : ℕ)
    (z : ℝ × DistRd d) : C(Rd d × Rd d, ℝ) := by
  classical
  exact if z.2 ∈ posGood d lo hi then interpProfile d lo hi j z.1 z.2 else 0

theorem measurable_approxProfile (d : ℕ) (hd : 3 ≤ d)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hhi : 0 < hi ∧ Real.sqrt (2 * d) < distExp d hi) (j : ℕ) :
    Measurable (approxProfile d lo hi j) := by
  have hset : MeasurableSet {z : ℝ × DistRd d | z.2 ∈ posGood d lo hi} :=
    (measurable_posGood hd hlo hlohi hhi).preimage measurable_snd
  exact Measurable.ite hset (measurable_interpProfile d hd hlo hlohi hhi j) measurable_const

theorem measurable_limitProfile (d : ℕ) (hd : 3 ≤ d)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hhi : 0 < hi ∧ Real.sqrt (2 * d) < distExp d hi) :
    Measurable (Function.uncurry (limitProfile d lo hi)) := by
  apply measurable_of_tendsto_metrizable
    (fun j => measurable_approxProfile d hd hlo hlohi hhi j)
  rw [tendsto_pi_nhds]
  intro z
  change Tendsto (fun j : ℕ => approxProfile d lo hi j z) atTop
    (𝓝 (limitProfile d lo hi z.1 z.2))
  classical
  by_cases hg : z.2 ∈ posGood d lo hi
  · simpa [approxProfile, limitProfile, hg] using
      (tendsto_interpProfile_limit d hlohi hg z.1)
  · simp [approxProfile, limitProfile, hg]

theorem limitProfile_node (d : ℕ) {lo hi : ℝ} (h : lo < hi)
    {g : DistRd d} (hg : g ∈ posGood d lo hi)
    (j : ℕ) {m : ℕ} (hm : m ≤ 2 ^ posLevel j) :
    limitProfile d lo hi (posNode lo hi j m) g =
      gridProfile d (posNode lo hi j m) g := by
  have hlim := tendsto_interpProfile_limit d h hg (posNode lo hi j m)
  have hconst : Tendsto
      (fun i : ℕ => interpProfile d lo hi i (posNode lo hi j m) g) atTop
      (𝓝 (gridProfile d (posNode lo hi j m) g)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop j] with i hi
    exact (interpProfile_node_refined d h hi hm g).symm
  exact tendsto_nhds_unique hlim hconst

end HigherDimLQGContinuity
