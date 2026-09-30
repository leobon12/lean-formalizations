import QuantumZipper.Proofs.Zipper.D3PlusN2CMLoc

/-!
# D3⁺(i), node N2-cutoff: a cutoff of a harmonic correction with small Dirichlet energy

Task D3P-N2 (decision D24). Proves `N2CutoffStmt` (`D3PlusN2CMLoc.lean`): for `h` continuous with
`h ∘ foldH` harmonic on `ball 0 ρ` and `h 0 = 0`, the function
`ψ_ε z = χ(z/ε) · h(foldH z)`, `χ z = smoothTransition((4 − ‖z‖²)/3)` (`= 1` on `‖z‖ ≤ 1`, `= 0`
on `‖z‖ ≥ 2`), is `C²`, compactly supported in `closedBall 0 (2ε)`, even across `ℝ`, equal to
`h` on `closedBall 0 ε ∩ Hbar`, and `E_H(ψ_ε) ≤ 2 C² ε²` with `C` independent of `ε`:
on `closedBall 0 (2ε)`, `‖∇ψ_ε‖ ≤ ‖∇g‖ + |g| ‖∇χ‖/ε ≤ M + (2Mε) K/ε`, `g = h ∘ foldH`,
`|g z| ≤ M ‖z‖` (mean value inequality, `g 0 = 0`).

This is the standard cutoff estimate behind D24 (Berestycki–Powell arXiv:2004.04720, p. 79: a
function harmonic near a point and vanishing there has Dirichlet energy `O(ε²)` on `B(0, ε)`);
own elementary proof (cost rule: minor standard estimate).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace D3Plus

/-- The fixed radial cutoff: `1` on `closedBall 0 1`, `0` outside `ball 0 2`. -/
def cutChi (z : ℂ) : ℝ := Real.smoothTransition ((4 - ‖z‖ ^ 2) / 3)

theorem contDiff_cutChi {n : ℕ∞} : ContDiff ℝ n cutChi :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub (contDiff_norm_sq ℝ)).div_const _)

theorem cutChi_nonneg (z : ℂ) : 0 ≤ cutChi z := Real.smoothTransition.nonneg _

theorem cutChi_le_one (z : ℂ) : cutChi z ≤ 1 := Real.smoothTransition.le_one _

theorem cutChi_eq_one {z : ℂ} (hz : ‖z‖ ≤ 1) : cutChi z = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
  linarith

theorem cutChi_eq_zero {z : ℂ} (hz : 2 ≤ ‖z‖) : cutChi z = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have : 4 ≤ ‖z‖ ^ 2 := by nlinarith
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)

theorem hasCompactSupport_cutChi : HasCompactSupport cutChi :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 2) fun z hz =>
    cutChi_eq_zero (by simp only [mem_closedBall, dist_zero_right, not_le] at hz; linarith)

theorem exists_bound_fderiv_cutChi : ∃ K, 0 ≤ K ∧ ∀ z, ‖fderiv ℝ cutChi z‖ ≤ K := by
  have h1 : ContDiff ℝ 1 cutChi := contDiff_cutChi (n := 1)
  have hc : Continuous (fderiv ℝ cutChi) := h1.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support (hasCompactSupport_cutChi.fderiv (𝕜 := ℝ))
  exact ⟨max C 0, le_max_right _ _, fun z => (hC z).trans (le_max_left _ _)⟩

theorem foldH_conj_n2 (u : ℂ) : foldH (conj u) = foldH u := by
  unfold foldH
  rcases lt_trichotomy u.im 0 with h | h | h
  · rw [if_pos (by rw [Complex.conj_im]; linarith), if_neg (not_le.2 h)]
  · have hu : conj u = u := Complex.conj_eq_iff_im.2 h
    rw [hu, if_pos h.symm.le, if_pos h.symm.le]
  · rw [if_neg (by rw [Complex.conj_im]; linarith), if_pos h.le, Complex.conj_conj]

theorem foldH_of_mem_Hbar {z : ℂ} (hz : z ∈ Hbar) : foldH z = z := by
  unfold foldH
  exact if_pos hz

/-- **Cutoff with small Dirichlet energy** (`N2CutoffStmt`; own elementary proof). -/
theorem n2Cutoff_holds : N2CutoffStmt := by
  intro r h hr hh h0 η hη
  obtain ⟨hc, ρ, hρ, hharm⟩ := hh
  set g : ℂ → ℝ := fun z => h (foldH z) with hgdef
  have hg0 : g 0 = 0 := by
    simp only [hgdef]
    rw [foldH_of_mem_Hbar (by simp [Hbar])]
    exact h0
  have hsub : closedBall (0 : ℂ) (ρ / 2) ⊆ ball 0 ρ := closedBall_subset_ball (by linarith)
  have hgcd : ContDiffOn ℝ 2 g (ball 0 ρ) := hharm.contDiffOn
  have hDg : ContinuousOn (fderiv ℝ g) (ball 0 ρ) :=
    hgcd.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)
  obtain ⟨M0, hM0⟩ :=
    (isCompact_closedBall (0 : ℂ) (ρ / 2)).exists_bound_of_continuousOn (hDg.mono hsub)
  set M := max M0 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hDgM : ∀ z ∈ closedBall (0 : ℂ) (ρ / 2), ‖fderiv ℝ g z‖ ≤ M := fun z hz =>
    (hM0 z hz).trans (le_max_left _ _)
  have hgd : ∀ z ∈ ball (0 : ℂ) ρ, DifferentiableAt ℝ g z := fun z hz =>
    (hharm z hz).1.differentiableAt (by norm_num)
  have hglin : ∀ z ∈ closedBall (0 : ℂ) (ρ / 2), |g z| ≤ M * ‖z‖ := by
    intro z hz
    have := (convex_closedBall (0 : ℂ) (ρ / 2)).norm_image_sub_le_of_norm_fderiv_le
      (fun x hx => hgd x (hsub hx)) hDgM (mem_closedBall_self (by linarith)) hz
    simpa [hg0] using this
  obtain ⟨K, hK0, hK⟩ := exists_bound_fderiv_cutChi
  set C := M + 2 * M * K with hCdef
  have hC : 0 ≤ C := by positivity
  have hT : Tendsto (fun ε : ℝ => 2 * C ^ 2 * ε ^ 2) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun ε : ℝ => 2 * C ^ 2 * ε ^ 2) := by fun_prop
    simpa using this.tendsto 0
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith : (0 : ℝ) < ρ / 4)),
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith : (0 : ℝ) < r / 4)),
    nhdsWithin_le_nhds (hT.eventually (gt_mem_nhds hη))] with ε hε0 hερ hεr hεη
  simp only [mem_Ioi, mem_Iio] at hε0 hερ hεr
  set ψ : ℂ → ℝ := fun z => cutChi (ε⁻¹ • z) * g z with hψdef
  have hnorm : ∀ y : ℂ, ‖ε⁻¹ • y‖ = ε⁻¹ * ‖y‖ := fun y => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε0)]
  have hzero : ∀ y : ℂ, 2 * ε ≤ ‖y‖ → ψ y = 0 := fun y hy => by
    have : 2 ≤ ‖ε⁻¹ • y‖ := by
      rw [hnorm, le_inv_mul_iff₀ hε0]; linarith
    simp only [hψdef, cutChi_eq_zero this, zero_mul]
  have hloc0 : ∀ z : ℂ, 2 * ε < ‖z‖ → ψ =ᶠ[𝓝 z] fun _ => (0 : ℝ) := fun z hz => by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with y hy
    exact hzero y (le_of_lt hy)
  have h1 : ContDiff ℝ 1 cutChi := contDiff_cutChi (n := 1)
  have hderiv : ∀ z, ‖fderiv ℝ ψ z‖ ≤ C := by
    intro z
    by_cases hz : ‖z‖ ≤ 2 * ε
    · have hzb : z ∈ closedBall (0 : ℂ) (ρ / 2) := mem_closedBall_zero_iff.2 (by linarith)
      have hA : HasFDerivAt (fun y : ℂ => cutChi (ε⁻¹ • y))
          ((fderiv ℝ cutChi (ε⁻¹ • z)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ ℂ)) z :=
        (h1.differentiable one_ne_zero (ε⁻¹ • z)).hasFDerivAt.comp z
          ((hasFDerivAt_id z).const_smul ε⁻¹)
      have hB : HasFDerivAt g (fderiv ℝ g z) z := (hgd z (hsub hzb)).hasFDerivAt
      have hP : HasFDerivAt ψ (cutChi (ε⁻¹ • z) • fderiv ℝ g z +
          g z • (fderiv ℝ cutChi (ε⁻¹ • z)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ ℂ)) z :=
        hA.mul hB
      rw [hP.fderiv]
      have e1 : ‖cutChi (ε⁻¹ • z)‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (cutChi_nonneg _)]; exact cutChi_le_one _
      have e2 : ‖g z‖ ≤ M * (2 * ε) := by
        rw [Real.norm_eq_abs]
        exact (hglin z hzb).trans (mul_le_mul_of_nonneg_left hz hM)
      have e3 : ‖(fderiv ℝ cutChi (ε⁻¹ • z)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ ℂ)‖ ≤
          K * ε⁻¹ := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        refine mul_le_mul (hK _) ?_ (norm_nonneg _) hK0
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε0)]
        exact mul_le_of_le_one_right (inv_pos.2 hε0).le ContinuousLinearMap.norm_id_le
      calc _ ≤ ‖cutChi (ε⁻¹ • z) • fderiv ℝ g z‖ +
            ‖g z • (fderiv ℝ cutChi (ε⁻¹ • z)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ ℂ)‖ :=
            norm_add_le _ _
        _ ≤ 1 * M + M * (2 * ε) * (K * ε⁻¹) := by
          rw [norm_smul, norm_smul]
          exact add_le_add (mul_le_mul e1 (hDgM z hzb) (norm_nonneg _) zero_le_one)
            (mul_le_mul e2 e3 (norm_nonneg _) (by positivity))
        _ = C := by
          rw [hCdef]; field_simp
    · rw [(hloc0 z (by linarith)).fderiv_eq, fderiv_const_apply, norm_zero]
      exact hC
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `C²`
    refine contDiff_iff_contDiffAt.2 fun z => ?_
    by_cases hz : ‖z‖ < ρ
    · exact ((contDiff_cutChi (n := 2)).comp (contDiff_id.const_smul ε⁻¹)).contDiffAt.mul
        (hharm z (mem_ball_zero_iff.2 hz)).1
    · exact contDiffAt_const.congr_of_eventuallyEq (hloc0 z (by linarith))
  · exact HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * ε)) fun z hz =>
      hzero z (by simp only [mem_closedBall, dist_zero_right, not_le] at hz; linarith)
  · intro z
    simp only [hψdef, hgdef, foldH_conj_n2]
    congr 1
    unfold cutChi
    rw [hnorm, hnorm, Complex.norm_conj]
  · refine (closure_minimal (fun z hz => ?_) isClosed_closedBall).trans
      (closedBall_subset_ball (show 2 * ε < r by linarith))
    by_contra hz'
    simp only [mem_closedBall, dist_zero_right, not_le] at hz'
    exact hz (hzero z hz'.le)
  · rintro z ⟨hz1, hz2⟩
    have : ‖ε⁻¹ • z‖ ≤ 1 := by
      rw [hnorm, inv_mul_le_iff₀ hε0, mul_one]
      simpa using hz1
    simp only [hψdef, hgdef, cutChi_eq_one this, one_mul, foldH_of_mem_Hbar hz2]
  · -- the energy
    have hpt : ∀ z, ‖fderiv ℝ ψ z‖ ^ 2 ≤
        (closedBall (0 : ℂ) (2 * ε)).indicator (fun _ => C ^ 2) z := by
      intro z
      by_cases hz : z ∈ closedBall (0 : ℂ) (2 * ε)
      · rw [indicator_of_mem hz]
        exact pow_le_pow_left₀ (norm_nonneg _) (hderiv z) 2
      · rw [indicator_of_notMem hz]
        simp only [mem_closedBall, dist_zero_right, not_le] at hz
        rw [(hloc0 z hz).fderiv_eq, fderiv_const_apply, norm_zero]
        norm_num
    have hint : Integrable ((closedBall (0 : ℂ) (2 * ε)).indicator fun _ => C ^ 2) volume :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const (measure_closedBall_lt_top.ne))
    have hI : ∫ z in H, ‖fderiv ℝ ψ z‖ ^ 2 ≤ C ^ 2 * (Real.pi * (2 * ε) ^ 2) := by
      calc ∫ z in H, ‖fderiv ℝ ψ z‖ ^ 2
          ≤ ∫ z in H, (closedBall (0 : ℂ) (2 * ε)).indicator (fun _ => C ^ 2) z :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity)
              hint.integrableOn (Eventually.of_forall hpt)
        _ ≤ ∫ z, (closedBall (0 : ℂ) (2 * ε)).indicator (fun _ => C ^ 2) z :=
            setIntegral_le_integral hint (Eventually.of_forall fun z =>
              indicator_nonneg (fun _ _ => by positivity) z)
        _ = C ^ 2 * (Real.pi * (2 * ε) ^ 2) := by
            rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul,
              Measure.real, Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
              ENNReal.toReal_ofReal (by positivity)]
            simp only [ENNReal.coe_toReal, NNReal.coe_real_pi]
            ring
    unfold dirichletEnergyOn
    calc (2 * Real.pi)⁻¹ * ∫ z in H, ‖fderiv ℝ ψ z‖ ^ 2
        ≤ (2 * Real.pi)⁻¹ * (C ^ 2 * (Real.pi * (2 * ε) ^ 2)) :=
          mul_le_mul_of_nonneg_left hI (by positivity)
      _ = 2 * C ^ 2 * ε ^ 2 := by field_simp
      _ ≤ η := hεη.le

end D3Plus
end QuantumZipper
