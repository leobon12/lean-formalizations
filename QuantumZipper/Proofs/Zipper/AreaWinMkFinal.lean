import QuantumZipper.Proofs.Zipper.AreaWinMkMain
import QuantumZipper.Proofs.Zipper.SWCoreDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-WINMARKOV (A3): SW's window split with the normalization at a large circle

Source: S. Sheffield, M. Wang, arXiv:1605.06171, proof of Theorem 1.1, p. 9, with the window
estimate of the proof of Lemma 3.1 (pp. 7–8) (`E6.winSplit_of_markovData`), and the Markov
structure `E6.mkWinMarkovData` (SW p. 9; B. Duplantier, S. Sheffield 2011, §3.1).

* `mkF_swBM_true`, `mkF_swBM_false`: SW's constants `C(N)^{-1}`, `C̲(N)^{-1}` in the form used by
  `mkWinMarkovData`.
* `swWinMeanInf_pos`: `E inf_{t ∈ window} e^{γ B_t − γ² t/2} > 0` (own elementary argument:
  `inf ≥ e^{-γ² s} / sup e^{-γ B_t − γ² t/2}` and the Doob bound makes the supremum a.s. finite).
* `swWindowSplitStmtR_holds`: **`SWCore.SWWindowSplitStmtR γ (swC γ) (swC' γ)`** for
  `0 < γ < 2`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Real
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

open LQGDimension.ExistAsm

theorem mkF_swBM_true (γ : ℝ) (N : ℕ) :
    ∫⁻ ω, mkF γ N true (fun q : swWinSet N => swBM q ω) ∂stdP = swWinMean γ N := by
  unfold swWinMean
  refine lintegral_congr fun ω => ?_
  simp only [mkF, if_true, mkE]
  exact iSup_subtype'' (swWinSet N) fun t => ENNReal.ofReal (rexp (γ * swBM t ω - γ ^ 2 / 2 * t))

theorem mkF_swBM_false (γ : ℝ) (N : ℕ) :
    ∫⁻ ω, mkF γ N false (fun q : swWinSet N => swBM q ω) ∂stdP = swWinMeanInf γ N := by
  unfold swWinMeanInf
  refine lintegral_congr fun ω => ?_
  simp only [mkF, Bool.false_eq_true, if_false, mkE]
  exact iInf_subtype'' (swWinSet N) fun t => ENNReal.ofReal (rexp (γ * swBM t ω - γ ^ 2 / 2 * t))

theorem mkF_false_le_true (γ : ℝ) (N : ℕ) (v : swWinSet N → ℝ) :
    mkF γ N false v ≤ mkF γ N true v := by
  have : Nonempty (swWinSet N) := ⟨⟨0, zero_mem_swWinSet N⟩⟩
  simp only [mkF, Bool.false_eq_true, if_false, if_true]
  exact iInf_le_iSup

theorem swWinMean_ne_top (γ : ℝ) (N : ℕ) : swWinMean γ N ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (swWinMean_le γ N)

theorem mkF_true_sq_ne_top (γ : ℝ) (N : ℕ) :
    ∫⁻ ω, mkF γ N true (fun q : swWinSet N => swBM q ω) ^ 2 ∂stdP ≠ ∞ := by
  have h := lintegral_sup_pow_preBM_le isBrownianReal_swBM.toIsPreBrownianReal γ (swWinLen N)
    (swWinSet_countable N) (fun t ht => ht.1) 2
  refine ne_top_of_le_ne_top ?_ (le_trans (le_of_eq ?_) h)
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
        ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top⟩)
  · refine lintegral_congr fun ω => ?_
    simp only [mkF, if_true, mkE]
    rw [iSup_subtype'' (swWinSet N) fun t => ENNReal.ofReal (rexp (γ * swBM t ω - γ ^ 2 / 2 * t))]

theorem mkF_false_sq_ne_top (γ : ℝ) (N : ℕ) :
    ∫⁻ ω, mkF γ N false (fun q : swWinSet N => swBM q ω) ^ 2 ∂stdP ≠ ∞ :=
  ne_top_of_le_ne_top (mkF_true_sq_ne_top γ N)
    (lintegral_mono fun ω => pow_le_pow_left₀ zero_le (mkF_false_le_true γ N _) 2)

/-- `E inf_{t ∈ window} e^{γ B_t − γ² t/2} > 0` (own elementary argument). -/
theorem swWinMeanInf_pos (γ : ℝ) (N : ℕ) : 0 < swWinMeanInf γ N := by
  have hB := isBrownianReal_swBM.toIsPreBrownianReal
  set s : ℝ≥0 := swWinLen N
  set M : (ℕ → ℝ) → ℝ≥0∞ := fun ω =>
    ⨆ t ∈ swWinSet N, ENNReal.ofReal (rexp ((-γ) * swBM t ω - (-γ) ^ 2 / 2 * t)) with hM
  have hMm : AEMeasurable M stdP :=
    AEMeasurable.biSup _ (swWinSet_countable N) fun t _ =>
      ENNReal.measurable_ofReal.comp_aemeasurable (Real.measurable_exp.comp_aemeasurable
        (((hB.aemeasurable t).const_mul _).sub aemeasurable_const))
  have hMfin : ∫⁻ ω, M ω ∂stdP ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
        ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top⟩)
      (lintegral_iSup_expMart_le hB (-γ) s (swWinSet_countable N) fun t ht => ht.1)
  have hMlt := ae_lt_top' hMm hMfin
  set e : ℝ≥0∞ := ENNReal.ofReal (rexp (-(γ ^ 2 * s)))
  have he : e ≠ 0 := by simp [e, Real.exp_pos]
  have hpt : ∀ ω, e / M ω ≤
      ⨅ t ∈ swWinSet N, ENNReal.ofReal (rexp (γ * swBM t ω - γ ^ 2 / 2 * t)) := by
    intro ω
    refine le_iInf₂ fun t ht => ?_
    have hts : (t : ℝ) ≤ s := NNReal.coe_le_coe.2 ht.1
    have h1 : e / M ω ≤ e / ENNReal.ofReal (rexp ((-γ) * swBM t ω - (-γ) ^ 2 / 2 * t)) :=
      ENNReal.div_le_div_left (le_iSup₂_of_le t ht le_rfl) e
    refine h1.trans ?_
    rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    nlinarith [sq_nonneg γ, NNReal.coe_nonneg t]
  have hgm : AEMeasurable (fun ω => e / M ω) stdP := hMm.const_div e
  rw [swWinMeanInf, pos_iff_ne_zero]
  intro h0
  have h0' : ∫⁻ ω, e / M ω ∂stdP = 0 := le_antisymm (h0 ▸ lintegral_mono hpt) zero_le
  rw [lintegral_eq_zero_iff' hgm] at h0'
  obtain ⟨ω, hω1, hω2⟩ := (hMlt.and h0').exists
  exact (ENNReal.div_pos he hω1.ne) |>.ne' hω2

theorem swWinMeanInf_ne_top (γ : ℝ) (N : ℕ) : swWinMeanInf γ N ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (swWinMeanInf_le_one γ N)

end QuantumZipper.E6

namespace QuantumZipper.SWCore

open E6 VagueH LQGDimension.ExistAsm MeasureTheory Metric

/-- **SW-WINMARKOV: SW's window split (proof of Thm 1.1, p. 9) for the free field normalized at a
large circle.** -/
theorem swWindowSplitStmtR_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    SWWindowSplitStmtR γ (swC γ) (swC' γ) := by
  intro Ω _ P _ X hX R hR h0 N hN φ hφ hφ0 hsupp
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
  have hSR : ∀ z ∈ tsupport φ, ‖z‖ + 1 ≤ (R : ℝ) := fun z hz => by
    have := hsupp hz
    rw [mem_ball_zero_iff] at this
    linarith
  have hS := hφ.2.1
  have hSH := hφ.2.2
  -- the sup windows
  have hc1 : swC γ N * (∫⁻ ω, mkF γ N true (fun q : swWinSet N => swBM q ω) ∂stdP).toReal = 1 := by
    rw [mkF_swBM_true, swC]
    refine inv_mul_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨?_, swWinMean_ne_top γ N⟩)
    exact (lt_of_lt_of_le zero_lt_one (one_le_swWinMean γ N)).ne'
  have hc2 : swC' γ N * (∫⁻ ω, mkF γ N false (fun q : swWinSet N => swBM q ω) ∂stdP).toReal =
      1 := by
    rw [mkF_swBM_false, swC']
    exact inv_mul_cancel₀ (ENNReal.toReal_ne_zero.2
      ⟨(swWinMeanInf_pos γ N).ne', swWinMeanInf_ne_top γ N⟩)
  have hD1 := mkWinMarkovData hX hR1 h0 γ (swC γ N) (inv_nonneg.2 ENNReal.toReal_nonneg) hN true
    (by rw [mkF_swBM_true]; exact swWinMean_ne_top γ N) hc1 (mkF_true_sq_ne_top γ N) hS hSH hSR
  have hD2 := mkWinMarkovData hX hR1 h0 γ (swC' γ N) (inv_nonneg.2 ENNReal.toReal_nonneg) hN
    false (by rw [mkF_swBM_false]; exact swWinMeanInf_ne_top γ N) hc2 (mkF_false_sq_ne_top γ N)
    hS hSH hSR
  have e1 : (fun x j w => mkWin γ N true x j w) = fun x j w => supWin γ x N j w := by
    funext x j w; simp [mkWin]
  have e2 : (fun x j w => mkWin γ N false x j w) = fun x j w => infWin γ x N j w := by
    funext x j w; simp [mkWin]
  rw [e1] at hD1
  rw [e2] at hD2
  exact ⟨winSplit_of_markovData hγ hγ2 hN hφ hφ0 hD1, winSplit_of_markovData hγ hγ2 hN hφ hφ0 hD2⟩

end QuantumZipper.SWCore
