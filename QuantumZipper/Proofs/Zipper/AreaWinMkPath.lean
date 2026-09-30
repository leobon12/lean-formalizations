import QuantumZipper.Proofs.Zipper.AreaWinMkBM

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-WINMARKOV (P1): the pathwise window identity

Source: S. Sheffield, M. Wang, arXiv:1605.06171, proof of Theorem 1.1, p. 9: with
`r = 2^{-j/N}` and `ρ = r e^{-t}`,
`ρ^{γ²/2} e^{γ h_ρ(w)} = r^{γ²/2} e^{γ h_r(w)} · e^{γ (h_ρ(w) − h_r(w)) − γ² t/2}`, so the window
supremum (infimum) of the area densities is `areaDens_r · sup (inf)` of SW's exponential
martingale over the window `t ∈ [0, 2 log 2 / N]`. On a regular sample
(`RegSample.ae_isRegularSample`) the circle averages are continuous in the radius, so the
supremum (infimum) over the window equals the one over its rational times, and is finite.

* `mkWin_eq_of_regular`: the identity, for every `w ∈ Hbar`, on a regular sample.
-/

noncomputable section

open MeasureTheory Filter Set Function Real
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

theorem winLo_eq_mkRad (N j : ℕ) : winLo N j = mkRad N j (swWinLen N) := by
  have hlen : ((swWinLen N : ℝ≥0) : ℝ) = 2 * Real.log 2 / N :=
    Real.coe_toNNReal _ (by positivity)
  rw [mkRad, hlen, winLo, winHi, Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos two_pos,
    ← Real.exp_add]
  congr 1
  ring

theorem image_mkRad_Iic (N j : ℕ) :
    mkRad N j '' Iic (swWinLen N) = Icc (winLo N j) (winHi N j) := by
  ext ρ
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨winLo_eq_mkRad N j ▸ mkRad_anti N j ht, mkRad_le N j t⟩
  · rintro ⟨h1, h2⟩
    have hr := winHi_pos N j
    have hρ : 0 < ρ := (winLo_pos N j).trans_le h1
    have hl : 0 ≤ Real.log (winHi N j / ρ) :=
      Real.log_nonneg ((one_le_div hρ).2 h2)
    refine ⟨Real.toNNReal (Real.log (winHi N j / ρ)), ?_, ?_⟩
    · rw [winLo_eq_mkRad] at h1
      have hlen : ((swWinLen N : ℝ≥0) : ℝ) = 2 * Real.log 2 / N :=
        Real.coe_toNNReal _ (by positivity)
      unfold mkRad at h1
      show Real.toNNReal _ ≤ swWinLen N
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hl]
      rw [Real.log_le_iff_le_exp (div_pos hr hρ), div_le_iff₀ hρ]
      have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos ((swWinLen N : ℝ))).le
      rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at this
      linarith
    · rw [mkRad, Real.coe_toNNReal _ hl, Real.exp_neg, Real.exp_log (div_pos hr hρ)]
      field_simp

/-- SW's factorization of the area density at radius `r e^{-t}`. -/
theorem areaDens_mkRad (γ : ℝ) (x : FieldSample) (N j : ℕ) (w : ℂ) (t : ℝ≥0) :
    areaDens γ x (mkRad N j t) w = areaDens γ x (winHi N j) w *
      rexp (γ * (evalReg x (foldedCircle w (mkRad N j t)) -
        evalReg x (foldedCircle w (winHi N j))) - γ ^ 2 / 2 * t) := by
  unfold areaDens
  rw [mkRad, Real.mul_rpow (winHi_pos N j).le (Real.exp_pos _).le, ← Real.exp_mul]
  rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

/-- Continuous `g`: the supremum over `[0, L]` equals the one over the rational points. -/
theorem iSup_Iic_eq_rat {g : ℝ≥0 → ℝ≥0∞} (hg : Continuous g) (N : ℕ) :
    (⨆ t ∈ Iic (swWinLen N), g t) = ⨆ q : swWinSet N, g q := by
  apply le_antisymm
  · refine iSup₂_le fun t ht => ?_
    have hC : IsClosed {s : ℝ≥0 | g s ≤ ⨆ q : swWinSet N, g q} :=
      isClosed_le hg continuous_const
    have hD : ∀ s ∈ swWinSet N, s ∈ {s : ℝ≥0 | g s ≤ ⨆ q : swWinSet N, g q} :=
      fun s hs => le_iSup (fun q : swWinSet N => g q) ⟨s, hs⟩
    refine hC.closure_subset_iff.2 hD ?_
    rw [Metric.mem_closure_iff]
    intro ε hε
    rcases eq_or_ne t 0 with rfl | ht0
    · exact ⟨0, zero_mem_swWinSet N, by simp [hε]⟩
    · have htpos : (0 : ℝ) < t := by positivity
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt htpos (by linarith : (t : ℝ) - ε < t))
      have hq0 : (0 : ℝ) < q := (le_max_left _ _).trans_lt hq1
      refine ⟨Real.toNNReal q, ⟨?_, q, (Real.coe_toNNReal _ hq0.le).symm⟩, ?_⟩
      · exact (Real.toNNReal_le_iff_le_coe.2 hq2.le).trans ht
      · rw [NNReal.dist_eq, Real.coe_toNNReal _ hq0.le, abs_of_pos (by linarith)]
        linarith [le_max_right (0 : ℝ) (t - ε)]
  · exact iSup_le fun q => le_iSup₂_of_le (q : ℝ≥0) q.2.1 le_rfl

/-- Continuous `g`: the infimum over `[0, L]` equals the one over the rational points. -/
theorem iInf_Iic_eq_rat {g : ℝ≥0 → ℝ≥0∞} (hg : Continuous g) (N : ℕ) :
    (⨅ t ∈ Iic (swWinLen N), g t) = ⨅ q : swWinSet N, g q := by
  apply le_antisymm
  · exact le_iInf fun q => iInf₂_le_of_le (q : ℝ≥0) q.2.1 le_rfl
  · refine le_iInf₂ fun t ht => ?_
    have hC : IsClosed {s : ℝ≥0 | (⨅ q : swWinSet N, g q) ≤ g s} :=
      isClosed_le continuous_const hg
    have hD : ∀ s ∈ swWinSet N, s ∈ {s : ℝ≥0 | (⨅ q : swWinSet N, g q) ≤ g s} :=
      fun s hs => iInf_le (fun q : swWinSet N => g q) ⟨s, hs⟩
    refine hC.closure_subset_iff.2 hD ?_
    rw [Metric.mem_closure_iff]
    intro ε hε
    rcases eq_or_ne t 0 with rfl | ht0
    · exact ⟨0, zero_mem_swWinSet N, by simp [hε]⟩
    · have htpos : (0 : ℝ) < t := by positivity
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt htpos (by linarith : (t : ℝ) - ε < t))
      have hq0 : (0 : ℝ) < q := (le_max_left _ _).trans_lt hq1
      refine ⟨Real.toNNReal q, ⟨?_, q, (Real.coe_toNNReal _ hq0.le).symm⟩, ?_⟩
      · exact (Real.toNNReal_le_iff_le_coe.2 hq2.le).trans ht
      · rw [NNReal.dist_eq, Real.coe_toNNReal _ hq0.le, abs_of_pos (by linarith)]
        linarith [le_max_right (0 : ℝ) (t - ε)]

/-- The regularized increment path. -/
def mkPath (x : FieldSample) (N j : ℕ) (w : ℂ) (t : ℝ≥0) : ℝ :=
  evalReg x (foldedCircle w (mkRad N j t)) - evalReg x (foldedCircle w (winHi N j))

theorem continuous_mkRad (N j : ℕ) : Continuous (mkRad N j) := by
  unfold mkRad; fun_prop

theorem continuous_mkPath_of_regular {x : FieldSample} (hx : IsRegularSample x) (N j : ℕ)
    {w : ℂ} (hw : w ∈ Hbar) : Continuous (mkPath x N j w) := by
  obtain ⟨F, hF⟩ := hx
  have e : mkPath x N j w = fun t => F (w, mkRad N j t) - F (w, winHi N j) := by
    funext t
    rw [mkPath, hF.evalReg_fc_of_mem hw (mkRad_pos N j t),
      hF.evalReg_fc_of_mem hw (winHi_pos N j)]
  rw [e]
  refine Continuous.sub ?_ continuous_const
  refine hF.1.comp_continuous (continuous_const.prodMk (continuous_mkRad N j)) fun t => ?_
  exact ⟨hw, mkRad_pos N j t⟩

/-- **The pathwise window identity** (SW p. 9) on a regular sample. -/
theorem mkWin_eq_of_regular {x : FieldSample} (hx : IsRegularSample x) (γ : ℝ) (N : ℕ)
    (b : Bool) (j : ℕ) {w : ℂ} (hw : w ∈ Hbar) :
    mkWin γ N b x j w = ENNReal.ofReal (areaDens γ x (winHi N j) w) *
        mkF γ N b (fun q => mkPath x N j w q) ∧
      mkF γ N b (fun q => mkPath x N j w q) ≠ ∞ := by
  set g : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (rexp (γ * mkPath x N j w t - γ ^ 2 / 2 * t))
    with hg
  have hgc : Continuous g := by
    refine ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp ?_)
    exact (continuous_const.mul (continuous_mkPath_of_regular hx N j hw)).sub
      (continuous_const.mul NNReal.continuous_coe)
  have hA : 0 ≤ areaDens γ x (winHi N j) w := by
    unfold areaDens; exact mul_nonneg (Real.rpow_nonneg (winHi_pos N j).le _) (Real.exp_pos _).le
  have hApos : 0 < areaDens γ x (winHi N j) w := by
    unfold areaDens; exact mul_pos (Real.rpow_pos_of_pos (winHi_pos N j) _) (Real.exp_pos _)
  have hpt : ∀ t, ENNReal.ofReal (areaDens γ x (mkRad N j t) w) =
      ENNReal.ofReal (areaDens γ x (winHi N j) w) * g t := by
    intro t
    rw [areaDens_mkRad, ENNReal.ofReal_mul hA]
    rfl
  have : Nonempty (swWinSet N) := ⟨⟨0, zero_mem_swWinSet N⟩⟩
  have hmkE : (fun q : swWinSet N => mkE γ N (fun q => mkPath x N j w q) q) =
      fun q : swWinSet N => g (q : ℝ≥0) := rfl
  -- finiteness of the sup over the compact window
  have hfin : (⨆ q : swWinSet N, g q) ≠ ∞ := by
    obtain ⟨t₀, -, ht₀⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := swWinLen N)).exists_isMaxOn
      ⟨0, le_rfl, zero_le⟩ hgc.continuousOn
    exact ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := rexp (γ * mkPath x N j w t₀ -
      γ ^ 2 / 2 * t₀))) (iSup_le fun q => ht₀ ⟨zero_le, q.2.1⟩)
  cases b
  · have hfin' : (⨅ q : swWinSet N, g q) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (iInf_le_iSup)
    refine ⟨?_, by simp only [mkF, Bool.false_eq_true, if_false]; exact hfin'⟩
    simp only [mkWin, mkF, Bool.false_eq_true, if_false, infWin]
    rw [← image_mkRad_Iic, iInf_image]
    simp_rw [hpt]
    rw [hmkE, ← iInf_Iic_eq_rat hgc N, ENNReal.mul_iInf_of_ne (by simpa using hApos)
      ENNReal.ofReal_ne_top]
    refine iInf_congr fun t => ?_
    rw [ENNReal.mul_iInf_of_ne (by simpa using hApos) ENNReal.ofReal_ne_top]
  · refine ⟨?_, by simp only [mkF, if_true]; exact hfin⟩
    simp only [mkWin, mkF, if_true, supWin]
    rw [← image_mkRad_Iic, iSup_image]
    simp_rw [hpt]
    rw [hmkE, ← iSup_Iic_eq_rat hgc N, ENNReal.mul_iSup]
    refine iSup_congr fun t => ?_
    rw [ENNReal.mul_iSup]

end QuantumZipper.E6
