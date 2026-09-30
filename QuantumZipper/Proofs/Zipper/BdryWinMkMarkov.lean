import QuantumZipper.Proofs.Zipper.BdryWinMkDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-W1 (M): the boundary window Markov structure for the free field normalized at `fc(0,R)`

Source: S. Sheffield, M. Wang, arXiv:1605.06171, proof of Theorem 4.2, pp. 18–19 (as the proof
of Theorem 1.1, p. 9); B. Duplantier, S. Sheffield (2011), §6: for `x ∈ ℝ`, the semicircle
averages satisfy `Var(h_{r e^{-s}}(x) − h_r(x)) = 2 s`, so `B_s = (h_{r e^{-s}}(x) − h_r(x))/√2`
is a standard Brownian motion (`isPreBrownianReal_bIncr`, from `kernelCov_fc_real_sameCenter`),
and `ρ^{γ²/4} e^{(γ/2) h_ρ} = r^{γ²/4} e^{(γ/2) h_r} · e^{γ' B_s − γ'² s/2}` with `γ' = γ/√2`.
So SW's boundary constants are `C(N)` for `γ/√2`.

* `isPreBrownianReal_bIncr`, `bWin_eq_of_regular` (pathwise identity), `bWinHypB`,
  `bWinMarkovData`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Real
open scoped Topology NNReal ENNReal

namespace QuantumZipper.F1

open E6 GaussTK LQGDimension.ExistAsm

/-- The normalized boundary increment `(X(fc(t, r e^{-s})) − X(fc(t, r)))/√2`. -/
def bIncr {Ω : Type} (X : Ω → FieldSample) (N j : ℕ) (t : ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  (√2)⁻¹ * mkIncr X N j (t : ℂ) s ω

theorem winHi_le_one (N j : ℕ) : winHi N j ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos one_le_two
    (div_nonpos_of_nonpos_of_nonneg (by simp) (Nat.cast_nonneg N))

theorem isPreBrownianReal_bIncr {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) (N j : ℕ) (t : ℝ) :
    IsPreBrownianReal (bIncr X N j t) P := by
  have hr := winHi_pos N j
  have hgood : ∀ s : ℝ≥0, FcIdx.Good ((t : ℂ), mkRad N j s, (t : ℂ), winHi N j) :=
    fun s => good_real (mkRad_pos N j s) hr
  let f : ℝ≥0 → {p : FcIdx // p.Good} := fun s => ⟨_, hgood s⟩
  have hG := ((isGaussianProcess_fcPair hX).comp_right f).smul (fun _ => (√2)⁻¹)
  refine IsGaussianProcess.isPreBrownianReal_of_covariance hG (fun s => ?_) (fun s u hsu => ?_)
  · show ∫ ω, (√2)⁻¹ • fcPairVal X _ ω ∂P = 0
    rw [integral_smul, integral_fcPairVal hX (hgood s), smul_zero]
  · show cov[fun ω => (√2)⁻¹ • fcPairVal X ((t : ℂ), mkRad N j s, (t : ℂ), winHi N j) ω,
      fun ω => (√2)⁻¹ • fcPairVal X ((t : ℂ), mkRad N j u, (t : ℂ), winHi N j) ω; P] = s
    simp only [smul_eq_mul]
    rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_fcPairVal hX (hgood s) (hgood u)]
    have hs := mkRad_pos N j s
    have hu := mkRad_pos N j u
    simp only [fcPairCov, kernelCov2]
    rw [kernelCov_fc_real_sameCenter hs hu, kernelCov_fc_real_sameCenter hs hr,
      kernelCov_fc_real_sameCenter hr hu, kernelCov_fc_real_sameCenter hr hr,
      max_eq_left (mkRad_anti N j hsu), max_eq_right (mkRad_le N j s),
      max_eq_left (mkRad_le N j u), max_self, log_mkRad]
    have h2 : (√2)⁻¹ * ((√2)⁻¹ * 2) = 1 := by
      rw [← mul_assoc, ← sq, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    linear_combination (s : ℝ) * h2

/-! ## The pathwise identity -/

theorem bExp_eq (γ Δ s : ℝ) :
    γ / √2 * ((√2)⁻¹ * Δ) - (γ / √2) ^ 2 / 2 * s = γ / 2 * Δ - γ ^ 2 / 4 * s := by
  have hi : (√2)⁻¹ ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have e : γ / √2 * ((√2)⁻¹ * Δ) - (γ / √2) ^ 2 / 2 * s =
      γ * Δ * (√2)⁻¹ ^ 2 - γ ^ 2 * (√2)⁻¹ ^ 2 / 2 * s := by
    rw [div_eq_mul_inv]; ring
  rw [e, hi]; ring

theorem bdryDens_mkRad (γ : ℝ) (x : FieldSample) (N j : ℕ) (t : ℝ) (s : ℝ≥0) :
    bdryDens γ x (mkRad N j s) t = bdryDens γ x (winHi N j) t *
      rexp (γ / 2 * mkPath x N j (t : ℂ) s - γ ^ 2 / 4 * s) := by
  unfold bdryDens mkPath
  rw [mkRad, Real.mul_rpow (winHi_pos N j).le (Real.exp_pos _).le, ← Real.exp_mul]
  rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

/-- The boundary window: `bSupWin` for `b = true`, `bInfWin` otherwise. -/
def bWin (γ : ℝ) (N : ℕ) (b : Bool) (x : FieldSample) (j : ℕ) (u : ℝ) : ℝ≥0∞ :=
  if b then bSupWin γ x N j u else bInfWin γ x N j u

/-- **The pathwise boundary window identity** on a regular sample. -/
theorem bWin_eq_of_regular {x : FieldSample} (hx : IsRegularSample x) (γ : ℝ) (N : ℕ)
    (b : Bool) (j : ℕ) (t : ℝ) :
    bWin γ N b x j t = ENNReal.ofReal (bdryDens γ x (winHi N j) t) *
        mkF (γ / √2) N b (fun q => (√2)⁻¹ * mkPath x N j (t : ℂ) q) ∧
      mkF (γ / √2) N b (fun q => (√2)⁻¹ * mkPath x N j (t : ℂ) q) ≠ ∞ := by
  have htH : (t : ℂ) ∈ Hbar := ofReal_mem_Hbar t
  set g : ℝ≥0 → ℝ≥0∞ := fun s => ENNReal.ofReal (rexp (γ / √2 * ((√2)⁻¹ *
    mkPath x N j (t : ℂ) s) - (γ / √2) ^ 2 / 2 * s)) with hg
  have hgc : Continuous g := by
    refine ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp ?_)
    exact (continuous_const.mul (continuous_const.mul
      (continuous_mkPath_of_regular hx N j htH))).sub (continuous_const.mul NNReal.continuous_coe)
  have hA : 0 ≤ bdryDens γ x (winHi N j) t := GoodSample.bdryDens_nonneg γ x (winHi_pos N j) t
  have hApos : 0 < bdryDens γ x (winHi N j) t := by
    unfold bdryDens; exact mul_pos (Real.rpow_pos_of_pos (winHi_pos N j) _) (Real.exp_pos _)
  have hpt : ∀ s, ENNReal.ofReal (bdryDens γ x (mkRad N j s) t) =
      ENNReal.ofReal (bdryDens γ x (winHi N j) t) * g s := by
    intro s
    rw [bdryDens_mkRad, ENNReal.ofReal_mul hA, hg]
    simp only
    rw [bExp_eq]
  have : Nonempty (swWinSet N) := ⟨⟨0, zero_mem_swWinSet N⟩⟩
  have hmkE : (fun q : swWinSet N => mkE (γ / √2) N
      (fun q => (√2)⁻¹ * mkPath x N j (t : ℂ) q) q) = fun q : swWinSet N => g (q : ℝ≥0) := rfl
  have hfin : (⨆ q : swWinSet N, g q) ≠ ∞ := by
    obtain ⟨t₀, -, ht₀⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := swWinLen N)).exists_isMaxOn
      ⟨0, le_rfl, zero_le⟩ hgc.continuousOn
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le fun q => ht₀ ⟨zero_le, q.2.1⟩)
  cases b
  · have hfin' : (⨅ q : swWinSet N, g q) ≠ ∞ := ne_top_of_le_ne_top hfin iInf_le_iSup
    refine ⟨?_, by simp only [mkF, Bool.false_eq_true, if_false]; exact hfin'⟩
    simp only [bWin, mkF, Bool.false_eq_true, if_false, bInfWin]
    rw [← image_mkRad_Iic, iInf_image]
    simp_rw [hpt]
    rw [hmkE, ← iInf_Iic_eq_rat hgc N, ENNReal.mul_iInf_of_ne (by simpa using hApos)
      ENNReal.ofReal_ne_top]
    refine iInf_congr fun s => ?_
    rw [ENNReal.mul_iInf_of_ne (by simpa using hApos) ENNReal.ofReal_ne_top]
  · refine ⟨?_, by simp only [mkF, if_true]; exact hfin⟩
    simp only [bWin, mkF, if_true, bSupWin]
    rw [← image_mkRad_Iic, iSup_image]
    simp_rw [hpt]
    rw [hmkE, ← iSup_Iic_eq_rat hgc N, ENNReal.mul_iSup]
    refine iSup_congr fun s => ?_
    rw [ENNReal.mul_iSup]

end QuantumZipper.F1
