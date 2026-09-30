import QuantumZipper.Proofs.Thm18.RTMeas2CGlue

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-MEAS2, part 6: the window certificate for local area limits

On a window `B(c_n, r_n)` with `B̄(c_n, 2r_n) ⊆ U ⊆ ℍ`, the approximations weighted by the cut-off
`wt n` (`= 1` on `B̄(c_n, r_n)`, `= 0` off `B(c_n, 2r_n)`) are eventually finite; their convergence
against the countable dense family `GoodMeas.denseFam` gives a vague limit on `ℍ` (Riesz–Markov,
`VagueH.exists_isVagueLimitOn_of_family`), whose restriction to the window is the local limit of
the unweighted approximations. With `exists_isVagueLimitOn_of_winC` this gives the local limit on
`U` from the countable certificate `WinCertC`.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18
namespace RTMeas

/-- The cut-off of the `n`-th window. -/
def wt (n : ℕ) (z : ℂ) : ℝ := max 0 (min 1 (2 - dist z (cC n) / rC n))

theorem continuous_wt (n : ℕ) : Continuous (wt n) :=
  continuous_const.max (continuous_const.min (continuous_const.sub
    ((continuous_id.dist continuous_const).div_const _)))

theorem wt_nonneg (n : ℕ) (z : ℂ) : 0 ≤ wt n z := le_max_left _ _

theorem wt_le_one (n : ℕ) (z : ℂ) : wt n z ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem wt_eq_one {n : ℕ} (hr : 0 < rC n) {z : ℂ} (hz : z ∈ closedBall (cC n) (rC n)) :
    wt n z = 1 := by
  have h : dist z (cC n) / rC n ≤ 1 := (div_le_one hr).2 (mem_closedBall.1 hz)
  unfold wt
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem wt_eq_zero {n : ℕ} (hr : 0 < rC n) {z : ℂ} (hz : z ∉ closedBall (cC n) (2 * rC n)) :
    wt n z = 0 := by
  have h : 2 ≤ dist z (cC n) / rC n := by
    rw [le_div_iff₀ hr]; rw [mem_closedBall, not_le] at hz; linarith
  unfold wt
  rw [max_eq_left (min_le_of_right_le (by linarith))]

/-- The certificate on the windows of `U`. -/
def WinCertC (μs : ℕ → Measure ℂ) (U : Set ℂ) : Prop :=
  ∀ n, WinOKC U n → (∃ K : ℕ, ∀ k, K ≤ k → μs k (closedBall (cC n) (2 * rC n)) < ⊤) ∧
    ∀ f ∈ GoodMeas.denseFam, ∃ l, Tendsto (fun k => ∫ z, f z * wt n z ∂μs k) atTop (𝓝 l)

theorem exists_lim_winC {μs : ℕ → Measure ℂ} {U : Set ℂ} (hUH : U ⊆ H) {n : ℕ}
    (hok : WinOKC U n) (hfin : ∃ K : ℕ, ∀ k, K ≤ k → μs k (closedBall (cC n) (2 * rC n)) < ⊤)
    (hconv : ∀ f ∈ GoodMeas.denseFam, ∃ l,
      Tendsto (fun k => ∫ z, f z * wt n z ∂μs k) atTop (𝓝 l)) :
    ∃ ν, IsVagueLimitOn (winC U n) μs ν := by
  have hr := hok.1
  set μw : ℕ → Measure ℂ := fun k => (μs k).withDensity fun z => ENNReal.ofReal (wt n z)
    with hμw
  have hwm : Measurable (wt n) := (continuous_wt n).measurable
  have hI : ∀ k (g : ℂ → ℝ), ∫ z, g z ∂μw k = ∫ z, g z * wt n z ∂μs k := fun k g => by
    rw [hμw]
    simp only
    rw [GoodSample.integral_withDensity_ofReal hwm (wt_nonneg n) g]
    simp_rw [mul_comm]
  have hle : ∀ k, μw k univ ≤ μs k (closedBall (cC n) (2 * rC n)) := fun k => by
    rw [hμw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← lintegral_indicator_one measurableSet_closedBall]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ closedBall (cC n) (2 * rC n)
    · rw [indicator_of_mem hz]
      exact ENNReal.ofReal_le_one.2 (wt_le_one n z)
    · rw [indicator_of_notMem hz, wt_eq_zero hr hz, ENNReal.ofReal_zero]
  obtain ⟨K₀, hK₀⟩ := hfin
  have hfinw : ∀ K, IsCompact K → K ⊆ H → ∀ᶠ k in atTop, μw k K < ∞ := fun K _ _ => by
    filter_upwards [eventually_ge_atTop K₀] with k hk
    exact (measure_mono (subset_univ K)).trans_lt ((hle k).trans_lt (hK₀ k hk))
  obtain ⟨μW, hW⟩ := VagueH.exists_isVagueLimitOn_of_family hfinw GoodMeas.denseFam_dense
    fun f hf => by
      obtain ⟨l, hl⟩ := hconv f hf
      exact ⟨l, by simp_rw [hI]; exact hl⟩
  have hwin : winC U n = ball (cC n) (rC n) := by unfold winC; rw [if_pos hok]
  have hbH : ball (cC n) (rC n) ⊆ H := fun z hz =>
    hUH (hok.2 (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith)) hz))
  rw [hwin]
  refine ⟨μW.restrict (ball (cC n) (rC n)), ?_, fun K hK hKb => ?_, fun f hf hfc hfb => ?_⟩
  · rw [Measure.restrict_apply' isOpen_ball.measurableSet]; simp
  · exact (Measure.restrict_apply_le _ _).trans_lt (hW.2.1 K hK (hKb.trans hbH))
  · have e1 : ∀ k, ∫ z, f z ∂μs k = ∫ z, f z ∂μw k := fun k => by
      rw [hI]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      show f z = f z * wt n z
      by_cases hz : z ∈ tsupport f
      · rw [wt_eq_one hr (ball_subset_closedBall (hfb hz)), mul_one]
      · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
    have e2 : ∫ z, f z ∂μW.restrict (ball (cC n) (rC n)) = ∫ z, f z ∂μW :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
        image_eq_zero_of_notMem_tsupport fun h => hz (hfb h)
    simp_rw [e1, e2]
    exact hW.2.2 f hf hfc (hfb.trans hbH)

theorem exists_lim_of_winCertC {μs : ℕ → Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H)
    (hc : WinCertC μs U) : ∃ ν, IsVagueLimitOn U μs ν := by
  classical
  refine exists_isVagueLimitOn_of_winC hU (fun C hC hCU => ?_) fun n => ?_
  · obtain ⟨s, hs⟩ := hC.elim_finite_subcover (winC U) (isOpen_winC U)
      (by rw [iUnion_winC hU]; exact hCU)
    have hall : ∀ᶠ k in atTop, ∀ n ∈ s, μs k (winC U n) < ⊤ := by
      refine (s.eventually_all).2 fun n _ => ?_
      by_cases hok : WinOKC U n
      · obtain ⟨K, hK⟩ := (hc n hok).1
        filter_upwards [eventually_ge_atTop K] with k hk
        have hwin : winC U n = ball (cC n) (rC n) := by unfold winC; rw [if_pos hok]
        rw [hwin]
        exact (measure_mono (ball_subset_closedBall.trans
          (closedBall_subset_closedBall (by linarith [hok.1])))).trans_lt (hK k hk)
      · have hwin : winC U n = ∅ := by unfold winC; rw [if_neg hok]
        exact Eventually.of_forall fun k => by rw [hwin]; simp
    filter_upwards [hall] with k hk
    exact (measure_mono hs).trans_lt (measure_biUnion_lt_top s.finite_toSet hk)
  · by_cases hok : WinOKC U n
    · exact exists_lim_winC hUH hok (hc n hok).1 (hc n hok).2
    · have hwin : winC U n = ∅ := by unfold winC; rw [if_neg hok]
      rw [hwin]
      refine ⟨0, by simp, fun K _ _ => by simp, fun f _ _ hfS => ?_⟩
      rw [subset_empty_iff, tsupport_eq_empty_iff] at hfS
      subst hfS
      simp

end RTMeas
end R18
end QuantumZipper
