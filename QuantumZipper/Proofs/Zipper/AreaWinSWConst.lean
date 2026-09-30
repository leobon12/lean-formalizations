import QuantumZipper.Proofs.Zipper.AreaWinSWDoob
import QuantumZipper.Proofs.Zipper.AreaWinSWReduce
import QuantumZipper.Proofs.Zipper.AreaWinDense
import QuantumZipper.Proofs.Zipper.AreaWinWedge
import QuantumZipper.Proofs.Probability.BMExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-WINSPLIT (4): SW's constants `C(N)`, `C̲(N)` and `WedgeWindowStmt` from the Markov structure

Source: S. Sheffield, M. Wang, arXiv:1605.06171, proof of Theorem 1.1, p. 9:
`C(N) := (E sup_{t ∈ [0, log 2/N]} e^{-γ² t/2} e^{γ B_t})^{-1}`, `C̲(N)` with `inf`, and "the
monotone convergence theorem implies that both `C(N)` and `C̲(N)` converge to 1". Our windows
have two lattice steps (`AreaVarWin.lean`), so the time interval is `[0, 2 log 2 / N]`.

* `swC γ N`, `swC' γ N`: these constants for the standard Brownian motion `swBM` on `stdP`
  (`BMExist.exists_isBrownianReal_stdP`), with the supremum/infimum over the rational times of
  the interval (for continuous paths this is the supremum over the interval).
* `tendsto_swC`, `tendsto_swC'`: both tend to `1`. Instead of SW's monotone-convergence remark
  we use the quantitative Doob bound `E sup |e^{γB_t − γ²t/2} − 1| ≤ 2 √(e^{γ² s} − 1)`
  (`AreaWinSWDoob.lean`), together with `sup ≥ value at 0 = 1 ≥ inf`.
* `wedgeWindowStmt_of_markov`: `WedgeWindowStmt` from `SWWinMarkovStmt` with these constants.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Real
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

open LQGDimension.ExistAsm

/-- The standard Brownian motion used to define SW's constants. -/
def swBM : ℝ≥0 → (ℕ → ℝ) → ℝ := Classical.choose BMExist.exists_isBrownianReal_stdP

theorem isBrownianReal_swBM : IsBrownianReal swBM stdP :=
  Classical.choose_spec BMExist.exists_isBrownianReal_stdP

/-- Length `2 log 2 / N` of the window in the Brownian time `t = log (2^{-j/N}/ρ)`. -/
def swWinLen (N : ℕ) : ℝ≥0 := Real.toNNReal (2 * Real.log 2 / N)

/-- Rational times of the window. -/
def swWinSet (N : ℕ) : Set ℝ≥0 := {t | t ≤ swWinLen N ∧ ∃ q : ℚ, (q : ℝ) = t}

theorem swWinSet_countable (N : ℕ) : (swWinSet N).Countable :=
  (Set.countable_range fun q : ℚ => Real.toNNReal q).mono fun t ht => by
    obtain ⟨-, q, hq⟩ := ht
    exact ⟨q, by simp only; rw [hq]; exact Real.toNNReal_coe⟩

theorem zero_mem_swWinSet (N : ℕ) : (0 : ℝ≥0) ∈ swWinSet N :=
  ⟨zero_le, 0, by simp⟩

/-- `E sup_{t ∈ window} e^{γ B_t − γ² t/2}` (SW's `C(N)^{-1}`). -/
def swWinMean (γ : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ⨆ t ∈ swWinSet N, ENNReal.ofReal (rexp (γ * swBM t ω - γ ^ 2 / 2 * t)) ∂stdP

/-- `E inf_{t ∈ window} e^{γ B_t − γ² t/2}` (SW's `C̲(N)^{-1}`). -/
def swWinMeanInf (γ : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ⨅ t ∈ swWinSet N, ENNReal.ofReal (rexp (γ * swBM t ω - γ ^ 2 / 2 * t)) ∂stdP

/-- SW's `C(N)`. -/
def swC (γ : ℝ) (N : ℕ) : ℝ := (swWinMean γ N).toReal⁻¹

/-- SW's `C̲(N)`. -/
def swC' (γ : ℝ) (N : ℕ) : ℝ := (swWinMeanInf γ N).toReal⁻¹

/-- The value at time `0` integrates to `1`. -/
theorem lintegral_swBM_zero (γ : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (rexp (γ * swBM 0 ω - γ ^ 2 / 2 * ((0 : ℝ≥0) : ℝ))) ∂stdP = 1 := by
  have h0 := isBrownianReal_swBM.toIsPreBrownianReal.eval_zero_ae_eq_zero
  rw [lintegral_congr_ae (h0.mono fun ω hω => by
    show ENNReal.ofReal (rexp (γ * swBM 0 ω - γ ^ 2 / 2 * ((0 : ℝ≥0) : ℝ))) = 1
    rw [hω]; simp)]
  simp

theorem one_le_swWinMean (γ : ℝ) (N : ℕ) : 1 ≤ swWinMean γ N := by
  rw [← lintegral_swBM_zero γ]
  exact lintegral_mono fun ω => le_iSup₂_of_le (0 : ℝ≥0) (zero_mem_swWinSet N) le_rfl

theorem swWinMeanInf_le_one (γ : ℝ) (N : ℕ) : swWinMeanInf γ N ≤ 1 := by
  rw [← lintegral_swBM_zero γ]
  exact lintegral_mono fun ω => iInf₂_le_of_le (0 : ℝ≥0) (zero_mem_swWinSet N) le_rfl

/-- The Doob error `ε_N = 2 √(e^{γ² · 2 log 2 / N} − 1)`. -/
def swWinErr (γ : ℝ) (N : ℕ) : ℝ := 2 * √(rexp (γ ^ 2 * (swWinLen N : ℝ)) - 1)

theorem tendsto_swWinErr (γ : ℝ) : Tendsto (swWinErr γ) atTop (𝓝 0) := by
  have hlen : Tendsto (fun N : ℕ => (swWinLen N : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (2 * Real.log 2)
    have h' : Tendsto (fun N : ℕ => Real.toNNReal (2 * Real.log 2 / N)) atTop
        (𝓝 (Real.toNNReal 0)) := (continuous_real_toNNReal.tendsto 0).comp h
    rw [Real.toNNReal_zero] at h'
    have h3 := (NNReal.continuous_coe.tendsto 0).comp h'
    rw [NNReal.coe_zero] at h3
    exact h3
  have h1 : Tendsto (fun N : ℕ => rexp (γ ^ 2 * (swWinLen N : ℝ)) - 1) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => γ ^ 2 * (swWinLen N : ℝ)) atTop (𝓝 0) := by
      simpa using hlen.const_mul (γ ^ 2)
    have := ((Real.continuous_exp.tendsto 0).comp h0).sub_const 1
    simpa using this
  have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
  rw [Real.sqrt_zero] at h2
  have h3 := h2.const_mul 2
  rw [mul_zero] at h3
  exact h3

theorem swWinMean_le (γ : ℝ) (N : ℕ) :
    swWinMean γ N ≤ ENNReal.ofReal (1 + swWinErr γ N) := by
  have h := lintegral_iSup_expMart_le isBrownianReal_swBM.toIsPreBrownianReal γ (swWinLen N)
    (swWinSet_countable N) (fun t ht => ht.1)
  refine h.trans (le_of_eq ?_)
  rw [swWinErr, ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]

theorem swWinMeanInf_ge (γ : ℝ) (N : ℕ) :
    1 - swWinErr γ N ≤ (swWinMeanInf γ N).toReal := by
  have h := lintegral_iInf_expMart_ge isBrownianReal_swBM.toIsPreBrownianReal γ (swWinLen N)
    (swWinSet_countable N) (fun t ht => ht.1)
  have hfin : swWinMeanInf γ N ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (swWinMeanInf_le_one γ N)
  have h' : 1 ≤ swWinMeanInf γ N + ENNReal.ofReal (swWinErr γ N) := by
    rw [swWinErr, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
    exact tsub_le_iff_right.1 h
  have h'' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.ofReal_ne_top⟩) h'
  rw [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top, ENNReal.toReal_one,
    ENNReal.toReal_ofReal (by unfold swWinErr; positivity)] at h''
  linarith

/-- **SW p. 9: `C(N) → 1`.** -/
theorem tendsto_swC (γ : ℝ) : Tendsto (swC γ) atTop (𝓝 1) := by
  have hm : Tendsto (fun N => (swWinMean γ N).toReal) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using (tendsto_swWinErr γ).const_add 1) (fun N => ?_) (fun N => ?_)
    · have := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (swWinMean_le γ N)) (one_le_swWinMean γ N)
      simpa using this
    · have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (swWinMean_le γ N)
      rwa [ENNReal.toReal_ofReal (by unfold swWinErr; positivity)] at this
  have h3 := hm.inv₀ one_ne_zero
  rw [inv_one] at h3
  exact h3

/-- **SW p. 9: `C̲(N) → 1`.** -/
theorem tendsto_swC' (γ : ℝ) : Tendsto (swC' γ) atTop (𝓝 1) := by
  have hm : Tendsto (fun N => (swWinMeanInf γ N).toReal) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using (tendsto_swWinErr γ).const_sub 1) tendsto_const_nhds
      (fun N => swWinMeanInf_ge γ N) (fun N => ?_)
    have := ENNReal.toReal_mono ENNReal.one_ne_top (swWinMeanInf_le_one γ N)
    simpa using this
  have h3 := hm.inv₀ one_ne_zero
  rw [inv_one] at h3
  exact h3

end QuantumZipper.E6
