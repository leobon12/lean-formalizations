import QuantumZipper.Proofs.Thm18.G1ZA2Area

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-A2, part 5: the small-mass node from the goodness node

`g1A2SmallTopStmt_of : G1Z2SideGoodStmt → G1A2SmallTopStmt`.

The clause "mass `< 1` near every real point, infinite total mass" of an area limit `μ` is
turned into countably many conditions (rational centres `q`, radii `1/(m+1)`, balls `B(0,n)`) by
a Lebesgue-number argument on the compact `[-n, n]` (`small_iff`, `top_iff`), each of which is the
value at a bounded open set of a measurable formula
`μ(U) = ⨆ₖ ofReal (areaFun γ (openBump U k) x)` (`measure_eq_iSup_areaFun`, as in
`LQGMeas.measurable_qAreaMeasure_open`, but for a regular sample with an area limit only, not a
globally good sample). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZA2

open D3Plus Factorization LQGMeas

/-- The measure of a bounded open subset of `ℍ` from the area approximations. -/
theorem measure_eq_iSup_areaFun {γ : ℝ} {x : FieldSample} {μ : Measure ℂ}
    (hL : IsVagueLimitOn H (areaApprox γ x) μ) {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUH : U ⊆ H) :
    μ U = ⨆ n : ℕ, ENNReal.ofReal (areaFun γ (openBump U n) x) := by
  have hUc : Uᶜ.Nonempty := ⟨0, fun h => by simpa [H] using hUH h⟩
  rw [measure_open_eq_iSup _ hU hUc]
  congr 1
  funext n
  have hsupp := (tsupport_openBump_subset U n).trans hUH
  rw [areaFun, (hL.2.2 _ (continuous_openBump U n) (hasCompactSupport_openBump hUb n)
      hsupp).liminf_eq,
    ofReal_integral_eq_lintegral_ofReal _ (ae_of_all _ fun z => openBump_nonneg U n z)]
  exact GoodSample.integrable_of_tsupport hL.2.1 (continuous_openBump U n)
    (hasCompactSupport_openBump hUb n) hsupp

theorem small_iff (μ : Measure ℂ) :
    (∀ p : ℝ, ∃ a : ℝ, 0 < a ∧ μ (Metric.ball (p : ℂ) a ∩ H) < 1) ↔
      ∀ n : ℕ, ∃ m : ℕ, ∀ q : ℚ, |(q : ℝ)| ≤ n →
        μ (Metric.ball ((q : ℝ) : ℂ) (1 / ((m : ℝ) + 1)) ∩ H) < 1 := by
  constructor
  · intro h n
    choose a ha hμ using h
    have hK : IsCompact (((↑) : ℝ → ℂ) '' Icc (-(n : ℝ)) n) :=
      isCompact_Icc.image Complex.continuous_ofReal
    obtain ⟨δ, hδ, hδc⟩ := lebesgue_number_lemma_of_metric hK
      (c := fun p : ℝ => Metric.ball (p : ℂ) (a p)) (fun p => Metric.isOpen_ball)
      (fun z hz => by
        obtain ⟨p, -, rfl⟩ := hz
        exact mem_iUnion.2 ⟨p, Metric.mem_ball_self (ha p)⟩)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine ⟨m, fun q hq => ?_⟩
    obtain ⟨p, hp⟩ := hδc ((q : ℝ) : ℂ) ⟨(q : ℝ), by simpa [abs_le] using hq, rfl⟩
    exact lt_of_le_of_lt (measure_mono (inter_subset_inter_left _
      ((Metric.ball_subset_ball hm.le).trans hp))) (hμ p)
  · intro h p
    obtain ⟨n, hn⟩ := exists_nat_ge (|p| + 1)
    obtain ⟨m, hm⟩ := h n
    have hpos : (0 : ℝ) < 1 / (2 * ((m : ℝ) + 1)) := by positivity
    have hle : 1 / (2 * ((m : ℝ) + 1)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show p - 1 / (2 * ((m : ℝ) + 1)) < p +
      1 / (2 * ((m : ℝ) + 1)) by linarith)
    have hqp : |(q : ℝ) - p| < 1 / (2 * ((m : ℝ) + 1)) := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    have hqn : |(q : ℝ)| ≤ n := by
      have := abs_sub_abs_le_abs_sub (q : ℝ) p
      linarith
    refine ⟨1 / (2 * ((m : ℝ) + 1)), hpos, lt_of_le_of_lt (measure_mono (inter_subset_inter_left _
      (Metric.ball_subset_ball' ?_))) (hm q hqn)⟩
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    have : 1 / ((m : ℝ) + 1) = 1 / (2 * ((m : ℝ) + 1)) + 1 / (2 * ((m : ℝ) + 1)) := by
      field_simp; ring
    linarith

theorem top_iff (μ : Measure ℂ) :
    μ H = ⊤ ↔ ∀ M : ℕ, ∃ n : ℕ, (M : ℝ≥0∞) ≤ μ (Metric.ball (0 : ℂ) n ∩ H) := by
  constructor
  · intro htop M
    set s : ℕ → Set ℂ := fun n => Metric.ball (0 : ℂ) n ∩ H with hs
    have hmono : Monotone s := fun m n hmn => inter_subset_inter_left _
      (Metric.ball_subset_ball (by exact_mod_cast hmn))
    have hU : (⋃ n, s n) = H := by
      refine subset_antisymm (iUnion_subset fun n => inter_subset_right) fun z hz => ?_
      obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
      exact mem_iUnion.2 ⟨n, by simpa using hn, hz⟩
    have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hU, htop] at ht
    obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds (ENNReal.natCast_lt_top M))).exists
    exact ⟨n, hn.le⟩
  · intro h
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    obtain ⟨M, hM⟩ := exists_nat_ge (r : ℝ)
    obtain ⟨n, hn⟩ := h M
    refine le_trans ?_ (hn.trans (measure_mono inter_subset_right))
    have : (r : ℝ≥0∞) ≤ (M : ℝ≥0∞) := by
      rw [← ENNReal.coe_natCast]
      exact_mod_cast (by exact_mod_cast hM : r ≤ (M : ℝ≥0))
    exact this

end G1ZA2
end Thm18Asm
end QuantumZipper
