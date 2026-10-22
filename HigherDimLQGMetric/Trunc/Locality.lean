import HigherDimLQGMetric.Trunc.Basic
import HigherDimLQGMetric.Trunc.Param
import HigherDimLQGMetric.Markov.Defs
import HigherDimLQGMetric.Field.Basic

/-!
# Locality of the truncated test

Its topological support lies in the closed ball of truncation radius.  Hence
the pairing is measurable from the restriction to any open set containing
that closed ball.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace Filter
open scoped Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem l2c_truncTest_tsupport_subset_closedBall (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (z : Rd d) :
    tsupport (⇑(truncTest κ ε z)) ⊆ closedBall z (Real.sqrt ε) := by
  rw [tsupport]
  apply closure_minimal _ isClosed_closedBall
  intro w hw
  by_contra hn
  have hdist : Real.sqrt ε ≤ dist w z := le_of_lt (lt_of_not_ge hn)
  have hb : Real.sqrt ε / 2 < Real.sqrt ε := by
    have hs := Real.sqrt_pos.2 hε
    linarith
  have hzero : radBump (Real.sqrt ε / 2) (Real.sqrt ε) (z - w) = 0 := by
    apply l2c_radBump_eq_zero (by positivity) hb
    simpa only [dist_eq_norm, norm_sub_rev] using hdist
  have hwzero : truncTest κ ε z w = 0 := by
    rw [l2c_truncTest_apply hd hκ hε, hzero, mul_zero]
  exact hw hwzero

theorem l2c_truncTest_tsupport_subset_open (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (z : Rd d) (U : Opens (Rd d))
    (hU : closedBall z (Real.sqrt ε) ⊆ U) :
    tsupport (⇑(truncTest κ ε z)) ⊆ U :=
  (l2c_truncTest_tsupport_subset_closedBall hd hκ hε z).trans hU

theorem l2c_truncMollify_eq_of_restrictTo (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (z : Rd d) (U : Opens (Rd d))
    (hU : closedBall z (Real.sqrt ε) ⊆ U)
    {h k : DistRd d} (heq : restrictTo U h = restrictTo U k) :
    truncMollify κ ε h z = truncMollify κ ε k z := by
  exact (restrictTo_eq_restrictTo_iff U).1 heq _
    (l2c_truncTest_tsupport_subset_open hd hκ hε z U hU)

theorem l2c_measurable_truncMollify_fieldSigmaRd (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (z : Rd d) (U : Opens (Rd d))
    (hU : closedBall z (Real.sqrt ε) ⊆ U)
    {Ω : Type*} [MeasurableSpace Ω] (h : Ω → DistRd d) :
    Measurable[fieldSigmaRd h U] (fun ω => truncMollify κ ε (h ω) z) := by
  let φ := testOnOf U (truncTest κ ε z)
    (l2c_truncTest_tsupport_subset_open hd hκ hε z U hU)
  have hm : Measurable[fieldSigmaRd h U] (fun ω => restrictTo U (h ω)) :=
    comap_measurable _
  have heq : (fun ω => truncMollify κ ε (h ω) z) =
      (fun k : DistOn U => k φ) ∘ (fun ω => restrictTo U (h ω)) := by
    funext ω
    exact (restrictTo_testOnOf U (h ω) (truncTest κ ε z)
      (l2c_truncTest_tsupport_subset_open hd hκ hε z U hU)).symm
  rw [heq]
  exact (measurable_distOn_apply φ).comp hm

theorem l2c_measurable_truncMollify_enlargedBall (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (z : Rd d)
    {Ω : Type*} [MeasurableSpace Ω] (h : Ω → DistRd d) :
    Measurable[fieldSigmaRd h ⟨ball z (Real.sqrt ε + δ), isOpen_ball⟩]
      (fun ω => truncMollify κ ε (h ω) z) := by
  apply l2c_measurable_truncMollify_fieldSigmaRd hd hκ hε z
  intro w hw
  exact lt_of_le_of_lt hw (lt_add_of_pos_right _ hδ)

private def l2c_innerScale (ε : ℝ) (n : ℕ) : ℝ :=
  ε * (1 - (1 / 2 : ℝ) ^ (n + 1))

private theorem l2c_innerScale_pos_lt {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    0 < l2c_innerScale ε n ∧ l2c_innerScale ε n < ε := by
  have hp : 0 < (1 / 2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
  have hp1 : (1 / 2 : ℝ) ^ (n + 1) < 1 := by
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  dsimp [l2c_innerScale]
  constructor
  · exact mul_pos hε (sub_pos.mpr hp1)
  · nlinarith [mul_pos hε hp]

private theorem l2c_innerScale_tendsto {ε : ℝ} :
    Tendsto (l2c_innerScale ε) atTop (𝓝 ε) := by
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)).comp
      ((tendsto_add_atTop_iff_nat 1).2 tendsto_id)
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := (h1.sub hp).const_mul ε
  change Tendsto (fun n : ℕ => ε * (1 - (1 / 2 : ℝ) ^ (n + 1))) atTop (𝓝 ε)
  simpa only [sub_zero, mul_one] using h

private theorem l2c_tendsto_truncMollify_innerScale (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (h : DistRd d) (z : Rd d) :
    Tendsto (fun n => truncMollify κ (l2c_innerScale ε n) h z) atTop
      (𝓝 (truncMollify κ ε h z)) := by
  have hc : ContinuousAt (fun q : ℝ × Rd d => truncMollify κ q.1 h q.2) (ε, z) :=
    (map_continuous h).continuousAt.comp (l2c_continuousAt_truncTest hd hκ hε)
  have hs : Tendsto (fun n => (l2c_innerScale ε n, z)) atTop (𝓝 (ε, z)) :=
    l2c_innerScale_tendsto.prodMk_nhds tendsto_const_nhds
  exact hc.tendsto.comp hs

theorem l2c_truncMollify_eq_of_restrictTo_openBall (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (z : Rd d) {h k : DistRd d}
    (heq : restrictTo ⟨ball z (Real.sqrt ε), isOpen_ball⟩ h =
      restrictTo ⟨ball z (Real.sqrt ε), isOpen_ball⟩ k) :
    truncMollify κ ε h z = truncMollify κ ε k z := by
  have hn : ∀ n : ℕ, truncMollify κ (l2c_innerScale ε n) h z =
      truncMollify κ (l2c_innerScale ε n) k z := by
    intro n
    obtain ⟨hpos, hlt⟩ := l2c_innerScale_pos_lt hε n
    apply l2c_truncMollify_eq_of_restrictTo hd hκ hpos z
      ⟨ball z (Real.sqrt ε), isOpen_ball⟩ ?_ heq
    intro w hw
    exact lt_of_le_of_lt hw (Real.sqrt_lt_sqrt hpos.le hlt)
  exact tendsto_nhds_unique_of_forall
    (l2c_tendsto_truncMollify_innerScale hd hκ hε h z)
    (l2c_tendsto_truncMollify_innerScale hd hκ hε k z) hn

set_option linter.style.haveILetI false in
theorem l2c_measurable_truncMollify_openBall (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (z : Rd d) {Ω : Type*} [MeasurableSpace Ω] (h : Ω → DistRd d) :
    Measurable[fieldSigmaRd h ⟨ball z (Real.sqrt ε), isOpen_ball⟩]
      (fun ω => truncMollify κ ε (h ω) z) := by
  letI : MeasurableSpace Ω := fieldSigmaRd h ⟨ball z (Real.sqrt ε), isOpen_ball⟩
  change Measurable (fun ω => truncMollify κ ε (h ω) z)
  refine measurable_of_tendsto_metrizable
    (f := fun n ω => truncMollify κ (l2c_innerScale ε n) (h ω) z) ?_ ?_
  · intro n
    obtain ⟨hpos, hlt⟩ := l2c_innerScale_pos_lt hε n
    apply l2c_measurable_truncMollify_fieldSigmaRd hd hκ hpos z
    intro w hw
    exact lt_of_le_of_lt hw (Real.sqrt_lt_sqrt hpos.le hlt)
  · exact tendsto_pi_nhds.mpr (fun ω =>
      l2c_tendsto_truncMollify_innerScale hd hκ hε (h ω) z)

end HigherDimLQGMetric
