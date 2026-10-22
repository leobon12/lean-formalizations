import HigherDimLQGMetric.ConvField.TruncRadial

/-! Parameter continuity for compact truncations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology TopologicalSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem l2b_continuous_iteratedFDeriv_snd {Ψ : X → Rd d → ℝ}
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry Ψ)) (i : ℕ) :
    Continuous fun p : X × Rd d => iteratedFDeriv ℝ i (Ψ p.1) p.2 := by
  let ι : Rd d →L[ℝ] X × Rd d := ContinuousLinearMap.inr ℝ X (Rd d)
  have key : ∀ p : X × Rd d, iteratedFDeriv ℝ i (Ψ p.1) p.2 =
      (iteratedFDeriv ℝ i (Function.uncurry Ψ) p).compContinuousLinearMap
        fun _ => ι := by
    intro p
    have h1 : Ψ p.1 =
        (fun w => Function.uncurry Ψ (w + (p.1, 0))) ∘ ι := by
      funext y
      simp [ι]
    have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        fun w => Function.uncurry Ψ (w + (p.1, 0)) :=
      hΨ.comp (contDiff_id.add contDiff_const)
    rw [h1, ι.iteratedFDeriv_comp_right hg _ (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    congr 2
    simp [ι]
  simp_rw [key]
  let L := ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ)
    (E := fun _ : Fin i => Rd d) (E₁ := fun _ : Fin i => X × Rd d)
    (F := ℝ) (fun _ => ι)
  exact L.continuous.comp (hΨ.continuous_iteratedFDeriv (by exact_mod_cast le_top))

theorem l2b_contDiff_convTrunc_exp_uncurry (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry fun (q : ℝ × Rd d) (w : Rd d) =>
        convKernelEps κ (Real.exp q.1) (q.2 - w) *
          radialProfile d (((n : ℝ) + 1)⁻¹ • (w - q.2))) := by
  have hform : (Function.uncurry fun (q : ℝ × Rd d) (w : Rd d) =>
        convKernelEps κ (Real.exp q.1) (q.2 - w) *
          radialProfile d (((n : ℝ) + 1)⁻¹ • (w - q.2))) =
      fun p : (ℝ × Rd d) × Rd d =>
        (Real.exp (p.1.1 * (-(d : ℝ))) *
          convKernel κ (Real.exp (-p.1.1) • (p.1.2 - p.2))) *
          radialProfile d (((n : ℝ) + 1)⁻¹ • (p.2 - p.1.2)) := by
    funext p
    change Real.exp p.1.1 ^ (-(d : ℝ)) *
      convKernel κ ((Real.exp p.1.1)⁻¹ • (p.1.2 - p.2)) *
        radialProfile d (((n : ℝ) + 1)⁻¹ • (p.2 - p.1.2)) = _
    rw [← Real.exp_mul, ← Real.exp_neg]
  rw [hform]
  have hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × Rd d) × Rd d => p.1.1) :=
    contDiff_fst.comp contDiff_fst
  have hz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × Rd d) × Rd d => p.1.2) :=
    contDiff_snd.comp contDiff_fst
  have hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × Rd d) × Rd d => p.2) := contDiff_snd
  exact ((Real.contDiff_exp.comp (hu.mul contDiff_const)).mul
    ((convKernel_contDiff (by omega) hκ).comp
      ((Real.contDiff_exp.comp hu.neg).smul (hz.sub hw)))).mul
    ((radialProfile d).contDiff.comp ((hw.sub hz).const_smul _))

set_option linter.style.haveILetI false in
theorem l2b_continuous_convTrunc_exp_on_ball (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (n : ℕ) (z₀ : Rd d) :
    Continuous fun q : ℝ × closedBall z₀ 1 =>
      convTrunc κ (Real.exp q.1) (q.2 : Rd d) n := by
  let S : Set (Rd d) := closedBall z₀ 1
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall z₀ 1)
  let K : Compacts (Rd d) :=
    ⟨closedBall z₀ (2 * ((n : ℝ) + 1) + 2), isCompact_closedBall _ _⟩
  let Ψ : (ℝ × S) → Rd d → ℝ := fun q w =>
    convKernelEps κ (Real.exp q.1) ((q.2 : Rd d) - w) *
      radialProfile d (((n : ℝ) + 1)⁻¹ • (w - (q.2 : Rd d)))
  have hs : ∀ q : ℝ × S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ q) := by
    intro q
    have h := l2b_contDiff_convTrunc_exp_uncurry hd hκ n
    have hmap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : Rd d => (((q.1, (q.2 : Rd d)) : ℝ × Rd d), w)) :=
      contDiff_const.prodMk contDiff_id
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using h.comp hmap
  have hK : ∀ q : ℝ × S, ∀ w ∉ (K : Set (Rd d)), Ψ q w = 0 := by
    intro q w hw
    have hwfar : 2 * ((n : ℝ) + 1) + 2 < ‖w - z₀‖ := by
      simpa [K, mem_closedBall, dist_eq_norm] using hw
    have hq : ‖(q.2 : Rd d) - z₀‖ ≤ 1 := by
      have hq' : (q.2 : Rd d) ∈ closedBall z₀ 1 := q.2.2
      rw [mem_closedBall, dist_eq_norm] at hq'
      exact hq'
    have htri : ‖w - z₀‖ ≤ ‖w - (q.2 : Rd d)‖ + ‖(q.2 : Rd d) - z₀‖ := by
      calc
        ‖w - z₀‖ = ‖(w - (q.2 : Rd d)) + ((q.2 : Rd d) - z₀)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have hdist : 2 * ((n : ℝ) + 1) ≤ ‖w - (q.2 : Rd d)‖ := by linarith
    have hscale : 2 ≤ ‖((n : ℝ) + 1)⁻¹ • (w - (q.2 : Rd d))‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (by positivity))]
      rw [mul_comm]
      exact (le_mul_inv_iff₀ (by positivity : (0 : ℝ) < n + 1)).2 hdist
    dsimp [Ψ]
    rw [radialProfile_eq_zero hscale, mul_zero]
  have hD : ∀ i : ℕ, Continuous fun p : (ℝ × S) × Rd d =>
      iteratedFDeriv ℝ i (Ψ p.1) p.2 := by
    intro i
    have hfull := l2b_continuous_iteratedFDeriv_snd
      (l2b_contDiff_convTrunc_exp_uncurry hd hκ n) i
    have hmap : Continuous (fun p : (ℝ × S) × Rd d =>
        (((p.1.1, (p.1.2 : Rd d)) : ℝ × Rd d), p.2)) := by fun_prop
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using hfull.comp hmap
  have hc := continuous_testFamK K Ψ hs hK hD
  have he : (fun q : ℝ × S => convTrunc κ (Real.exp q.1) (q.2 : Rd d) n) =
      ofSuppRd K ∘ testFamK K Ψ hs hK := by
    funext q
    ext w
    rw [l2b_convTrunc_apply hd hκ]
    rfl
  rw [he]
  exact (ofSuppRd K).continuous.comp hc

theorem l2b_continuous_convTrunc_exp (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) (n : ℕ) :
    Continuous fun q : ℝ × Rd d => convTrunc κ (Real.exp q.1) q.2 n := by
  rw [continuous_iff_continuousAt]
  intro q₀
  let z₀ : Rd d := q₀.2
  let S : Set (Rd d) := closedBall z₀ 1
  have hmem (q : ℝ × Rd d) :
      z₀ + l2b_unitProj (q.2 - z₀) ∈ S := by
    change dist (z₀ + l2b_unitProj (q.2 - z₀)) z₀ ≤ 1
    rw [dist_eq_norm, add_sub_cancel_left]
    exact l2b_norm_unitProj_le_one _
  let proj : (ℝ × Rd d) → ℝ × S := fun q =>
    (q.1, ⟨z₀ + l2b_unitProj (q.2 - z₀), hmem q⟩)
  have hproj : Continuous proj := by
    have hzc : Continuous fun q : ℝ × Rd d => z₀ + l2b_unitProj (q.2 - z₀) :=
      continuous_const.add (l2b_continuous_unitProj.comp
        (continuous_snd.sub continuous_const))
    exact continuous_fst.prodMk (hzc.subtype_mk hmem)
  let F : ℝ × Rd d → TestRd d := fun q => convTrunc κ (Real.exp q.1) q.2 n
  let G' : ℝ × Rd d → TestRd d := fun q =>
    convTrunc κ (Real.exp (proj q).1) ((proj q).2 : Rd d) n
  have hG : Continuous G' :=
    (l2b_continuous_convTrunc_exp_on_ball hd hκ n z₀).comp hproj
  have hU : IsOpen {q : ℝ × Rd d | ‖q.2 - z₀‖ < 1} :=
    isOpen_lt (continuous_norm.comp (continuous_snd.sub continuous_const)) continuous_const
  have hq₀ : q₀ ∈ {q : ℝ × Rd d | ‖q.2 - z₀‖ < 1} := by
    change ‖q₀.2 - z₀‖ < 1
    simp [z₀]
  have heq : F =ᶠ[𝓝 q₀] G' := by
    refine Filter.eventuallyEq_iff_exists_mem.2
      ⟨{q : ℝ × Rd d | ‖q.2 - z₀‖ < 1}, hU.mem_nhds hq₀, ?_⟩
    intro q hq
    dsimp [F, G', proj]
    rw [l2b_unitProj_eq_self (le_of_lt hq)]
    simp
  exact hG.continuousAt.congr_of_eventuallyEq heq

end HigherDimLQGMetric
