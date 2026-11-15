/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Lemma47AngleData
import InteractingSLE.Foundations.Loewner.ConformalImageFullClearance

/-!
# Lemma 4.7 at a relative angle: the deterministic union mean

The angle-specific sample argument from `CrossRestartKernelQSample` is parametrized;
its chart geometry, finite exceptional sets, and uniqueness theorem are reused.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Complex Set Metric Filter Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC)
namespace InteractingSLE.Sec5.Lemma47Angle
open WangWu hiding ratPt exists_ratPt_dist_lt
open MartChar.RealFlow Restart.RetAux79 Sec7.StripSysField GlueCond Cond44Ref CrossCond.Theta GlueImg
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open CrossRestart CrossRestart.KernelQ
variable {Wα Wβ W' : ℝ → ℝ} {α β η' : ℝ → ℂ} {t q T : ℝ}
/-- The union mean in the image chart of the counterflow at relative angle `θ`. -/
theorem eqOn_imgChart_cfGlue_angle (hd : IsCfImgSetup Wα α t Wβ q W' η' T) {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hq : 0 < q) (hβ : IsLoewnerTrace Wβ β) (hβp : IsProperArc β)
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {u₀ uq u' uA u w : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (huq : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => -rightImg (fun r => -Wβ r) (-xL i) q - Wβ q)
        (fun j => rightImg Wβ (xR j) q - Wβ q))
      (forceJumpSet (fun i => -rightImg (fun r => -Wβ r) (-xL i) q - Wβ q)
        (fun j => rightImg Wβ (xR j) q - Wβ q)) uq)
    (hu' : IsBoundedHarmonicExtension (cfWordData κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR))
      (cfWordJumps κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR)) u')
    (huA : IsBoundedHarmonicExtension
      (forceBoundaryData (16 / κ) (qρLT κ θ ρL ρR xL xR) (qρRT κ θ ρL ρR xL xR)
        (fun i => -rightImg (fun r => -Wα r) (-qxLT κ θ ρL ρR xL xR i) t - Wα t)
        (fun j => rightImg Wα (qxRT κ θ ρL ρR xL xR j) t - Wα t))
      (forceJumpSet (fun i => -rightImg (fun r => -Wα r) (-qxLT κ θ ρL ρR xL xR i) t - Wα t)
        (fun j => rightImg Wα (qxRT κ θ ρL ρR xL xR j) t - Wα t)) uA)
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData (16 / κ) (slitRhoL (qρLT κ θ ρL ρR xL xR) κ θ)
        (slitRhoR (qρRT κ θ ρL ρR xL xR) κ θ)
        (fun i => -rightImg (fun r => -W' r) (-imgMarkL (qxLT κ θ ρL ρR xL xR) Wβ q i) T - W' T)
        (fun j => rightImg W' (imgMarkR (qxRT κ θ ρL ρR xL xR) Wβ q j) T - W' T))
      (forceJumpSet (fun i => -rightImg (fun r => -W' r) (-imgMarkL (qxLT κ θ ρL ρR xL xR) Wβ q i) T - W' T)
        (fun j => rightImg W' (imgMarkR (qxRT κ θ ρL ρR xL xR) Wβ q j) T - W' T)) u)
    (hFA : ∀ z₀ ∈ fwdHull Wβ q ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, negInv '' fwdHull Wα t ∩ ball z₀ r ⊆ fwdHull Wβ q) →
      Tendsto (fun z => w z - (couplingMean κ Wβ q uq z - u₀ z))
        (𝓝[H \ (fwdHull Wβ q ∪ negInv '' fwdHull Wα t)] z₀) (𝓝 0))
    (hFG : ∀ z₀ ∈ negInv '' fwdHull Wα t,
      Tendsto (fun z => w z - (-couplingMean (16 / κ) Wα t uA (negInv z) + u' (negInv z)))
        (𝓝[H \ (fwdHull Wβ q ∪ negInv '' fwdHull Wα t)] z₀) (𝓝 0))
    (huniq : ∀ z₀ ∈ H \ (fwdHull Wβ q ∪ negInv '' fwdHull Wα t), ∀ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ (fwdHull Wβ q ∪ negInv '' fwdHull Wα t)) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ (fwdHull Wβ q ∪ negInv '' fwdHull Wα t)) z₀)
        {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn L (connectedComponentIn (H \ (fwdHull Wβ q ∪ negInv '' fwdHull Wα t)) z₀) →
      (∀ z ∈ connectedComponentIn (H \ (fwdHull Wβ q ∪ negInv '' fwdHull Wα t)) z₀,
        deriv φc z = ‖deriv φc z‖ * exp (L z * I)) →
      E.Finite →
      (∀ p ∈ sphere (0 : ℂ) 1, p ∉ E →
        Tendsto (fun ζ => (w (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - chiC κ * L (f ζ))) (𝓝[ball 0 1] p) (𝓝 0)) →
      ∀ z ∈ connectedComponentIn (H \ (fwdHull Wβ q ∪ negInv '' fwdHull Wα t)) z₀,
        w z + u₀ z = G (φc z) - chiC κ * L z) :
    ∀ z ∈ H \ (fwdHull Wβ q ∪ negInv '' fwdHull Wα t), w z + u₀ z =
      -u (fwdMap W' T (revChart Wβ q (negInv z))) - (π - θ) * chiC κ -
        chiC κ * ((logDerivFwd W' T (revChart Wβ q (negInv z))).im + (logDerivPsi Wβ q (negInv z)).im -
          2 * arg z) := by
  classical
  set A := fwdHull Wβ q with hAdef
  set K := fwdHull Wα t with hKdef
  set DQ := H \ (A ∪ negInv '' K) with hDQ
  set DR := H \ (K ∪ negInv '' A) with hDR
  set χ := chiC κ with hχ
  have hk : 0 < 16 / κ := by positivity
  have hkk : (16 : ℝ) / (16 / κ) = κ := by field_simp
  have hc : chiC (16 / κ) = -χ := Sec4.chiC_sixteen_div hκ
  have hKH : K ⊆ H := (QuantumZipper.fwdHull_mono (W := Wα)).2 t
  have hAH : A ⊆ H := (QuantumZipper.fwdHull_mono (W := Wβ)).2 q
  -- the two domains correspond under `R`
  have hRQ : negInv '' DR = DQ := by
    rw [hDR, negInv_image_H_diff_union, hDQ, union_comm]
  have hQR : negInv '' DQ = DR := by
    rw [← hRQ, image_negInv_image_negInv]
  have hmR : MapsTo negInv DR DQ := fun z hz => hRQ ▸ mem_image_of_mem _ hz
  have hmQ : MapsTo negInv DQ DR := fun z hz => hQR ▸ mem_image_of_mem _ hz
  -- the two centrings: `u′ = 3π/2 χ − 2χ arg − 𝔥₀ ∘ R` on `ℍ`
  have hb : IsPiecewiseConstantBoundaryData (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) :=
    isPiecewiseConstant_forceData κ ρL ρR xL xR _
  have hub : IsBoundedHarmonicExtension (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR)
      (fun z => u₀ z + -(θ * χ)) := by
    have := GlueCond.isBoundedHarmonicExtension_add_const hu₀ (-(θ * χ))
    rwa [← coe_forceJumpFinset] at this
  have hu'eq : ∀ z ∈ H, u' z = (π + θ) * χ - 2 * χ * arg z - u₀ (negInv z) := by
    intro z hz
    have h1 := GlueImg.negInv_add_eq_of_returnBHE hκ hb hub hu' (WangWu.negInv_mem_H hz)
    rw [WangWu.negInv_negInv, GlueImg.arg_negInv_of_mem_H hz] at h1
    linear_combination h1
  -- the obstacle data are the flow line's data at `q`
  obtain ⟨v, hv⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / (16 / κ))
    (cfRhoL (16 / κ) (bDataT (qρLT κ θ ρL ρR xL xR) (qρRT κ θ ρL ρR xL xR) (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR)
      (-θ) (16 / κ)) (forceJumpFinset (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR)))
    (cfRhoR (16 / κ) (bDataT (qρLT κ θ ρL ρR xL xR) (qρRT κ θ ρL ρR xL xR) (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR)
      (-θ) (16 / κ)) (forceJumpFinset (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR)))
    (cfMarkL (16 / κ) (bDataT (qρLT κ θ ρL ρR xL xR) (qρRT κ θ ρL ρR xL xR) (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR)
      (-θ) (16 / κ)) (forceJumpFinset (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR)) Wβ q)
    (cfMarkR (16 / κ) (bDataT (qρLT κ θ ρL ρR xL xR) (qρRT κ θ ρL ρR xL xR) (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR)
      (-θ) (16 / κ)) (forceJumpFinset (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR)) Wβ q)
  have hvu : EqOn v uq H := eqOn_bhe_cfDataAt_flow_angle hκ ρL ρR hxL hxR hd.hWβ hd.hs hv huq
  -- the union mean read in the chart `R`
  set M : ℂ → ℝ := fun z => -(w (negInv z) + u₀ (negInv z)) + (π + θ) * χ - 2 * χ * arg z with hM
  set mG : ℂ → ℝ := fun z => -couplingMean κ Wβ q uq (negInv z) + (π + θ) * χ - 2 * χ * arg z with hmG
  -- the chart identity of the obstacle mean
  have hId : ∀ z ∈ H \ negInv '' A, mG z + chiC (16 / κ) * (logDerivPsi Wβ q z).im + 0 =
      retMean (16 / κ) v (revChart Wβ q z) + (-θ) * chiC (16 / κ) := by
    intro z hz
    have h1 := GlueImg.neg_couplingMean_add_chiC_mul hk hd.hWβ hd.hs uq hz
    rw [hkk] at h1
    have hΨ : revChart Wβ q z ∈ H := revChart_mem_H hd.hWβ hd.hs hz
    have hv' := hvu (WangWu.negInv_mem_H hΨ)
    simp only [retMean, retShift, cfOffset, cfCoeff, infinitySourceChart_lift, hkk] at h1 ⊢
    rw [hv']
    simp only [hmG]
    rw [hc] at h1 ⊢
    linear_combination h1
  -- the counterflow side
  have hA : ∀ z₀ ∈ K, Tendsto (fun z => M z + 0 - couplingMean (16 / κ) Wα t uA z) (𝓝[DR] z₀) (𝓝 0) := by
    intro z₀ hz₀
    have hz₀0 : z₀ ≠ 0 := ne_zero_of_mem_H (hKH hz₀)
    have h1 := (hFG (negInv z₀) ⟨z₀, hz₀, rfl⟩).comp (tendsto_negInv_nhdsWithin_of_ne hz₀0 hmR)
    have h2 := h1.neg
    rw [neg_zero] at h2
    refine h2.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    simp only [Function.comp_apply, WangWu.negInv_negInv, hM, hu'eq z hz.1]
    ring
  -- the flow-slit side
  have hG : ∀ z₀ ∈ negInv '' A ∪ {z : ℂ | z.im = 0}, (∃ r > 0, K ∩ ball z₀ r ⊆ negInv '' A) →
      Tendsto (fun z => M z - mG z) (𝓝[DR] z₀) (𝓝 0) := by
    rintro z₀ hz₀ ⟨r, hr, hsub⟩
    by_cases h0 : z₀ = 0
    · exfalso
      subst h0
      obtain ⟨k, hk1, hk2⟩ := Metric.mem_closure_iff.1
        (ConformalImageFull.zero_mem_closure_fwdHull hd.hWα hd.hWα0 hd.ht) r hr
      have hkb : k ∈ K ∩ ball 0 r := ⟨hk1, by rw [mem_ball, dist_comm]; exact hk2⟩
      exact disjoint_left.1 hd.hdisj hk1 (hsub hkb)
    have hQ : negInv z₀ ∈ A ∪ {z : ℂ | z.im = 0} := by
      rcases hz₀ with ⟨a, ha, rfl⟩ | him
      · exact Or.inl (by rw [WangWu.negInv_negInv]; exact ha)
      · exact Or.inr (im_negInv_eq_zero him)
    have hcond : ∃ r' > 0, negInv '' K ∩ ball (negInv z₀) r' ⊆ A := by
      obtain ⟨r', hr', hball⟩ := exists_ball_negInv_subset h0 hr
      refine ⟨r', hr', ?_⟩
      rintro g ⟨⟨k, hk, rfl⟩, hg⟩
      have hk' : negInv (negInv k) ∈ K ∩ ball z₀ r := ⟨by rw [WangWu.negInv_negInv]; exact hk, hball _ hg⟩
      obtain ⟨a, ha, hae⟩ := hsub hk'
      rw [negInv_involutive.injective hae] at ha
      exact ha
    have h1 := (hFA (negInv z₀) hQ hcond).comp (tendsto_negInv_nhdsWithin_of_ne h0 hmR)
    have h2 := h1.neg
    rw [neg_zero] at h2
    refine h2.congr' (eventually_nhdsWithin_of_forall fun z _ => ?_)
    simp only [Function.comp_apply, hM, hmG]
    ring
  have hInf : Tendsto (fun z => M z - mG z) (Bornology.cobounded ℂ ⊓ 𝓟 DR) (𝓝 0) := by
    obtain ⟨R₀, hR₀⟩ := (isBounded_fwdHull hd.hWα t).subset_closedBall 0
    have hcond : ∃ r > 0, negInv '' K ∩ ball 0 r ⊆ A := by
      refine ⟨(|R₀| + 1)⁻¹, by positivity, ?_⟩
      rintro g ⟨⟨k, hk, rfl⟩, hg⟩
      exfalso
      have hkn : ‖k‖ ≤ |R₀| := by
        have := hR₀ hk
        rw [mem_closedBall, dist_zero_right] at this
        exact this.trans (le_abs_self _)
      have hk0 : k ≠ 0 := ne_zero_of_mem_H (hKH hk)
      have hg' : ‖negInv k‖ < (|R₀| + 1)⁻¹ := by rwa [mem_ball, dist_zero_right] at hg
      rw [norm_negInv] at hg'
      have hkpos : 0 < ‖k‖ := norm_pos_iff.2 hk0
      have := (inv_lt_inv₀ hkpos (by positivity)).1 hg'
      linarith
    have h1 := (hFA 0 (Or.inr (by simp)) hcond).comp (tendsto_negInv_cobounded hmR)
    have h2 := h1.neg
    rw [neg_zero] at h2
    refine h2.congr' (eventually_inf_principal.2 (Eventually.of_forall fun z _ => ?_))
    simp only [Function.comp_apply, hM, hmG]
    ring
  -- the boundary values in the image chart (chart `R`)
  obtain ⟨E, hE, hlim⟩ := hd.exists_finite_tendsto_imgChart_restart hκ hκ4 θ hq hβ hβp
    (qρLT κ θ ρL ρR xL xR) (qρRT κ θ ρL ρR xL xR) (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR)
    (fun i => Theorem14.GW3Word.flowLineXL_nonpos _ _ i) (fun j => Theorem14.GW3Word.flowLineXR_nonneg _ _ j)
    (M := M) (mG := mG) (c := 0) hv hG hInf hId huA hA hu
  -- the charts read in `Q`
  have hAG : K ⊆ H \ negInv '' A := fun z hz => ⟨hKH hz, fun h => disjoint_left.1 hd.hdisj hz h⟩
  have hΦR := isConformalBijection_imgPhiChart hd.hWβ hd.hWβ0 hd.hs hd.hW' hd.hW'0 hd.hT.le hAG hd.hK'
  have hφcR := isConformalBijection_imgFwdChart hd.hWβ hd.hWβ0 hd.hs hd.hW' hd.hW'0 hd.hT.le hAG hd.hK'
  have hnR : IsConformalBijection negInv DR DQ := by
    have := isConformalBijection_negInv_restrict (U := DR) sdiff_subset
    rwa [hRQ] at this
  have hnQ : IsConformalBijection negInv DQ DR := by
    have := isConformalBijection_negInv_restrict (U := DQ) sdiff_subset
    rwa [hQR] at this
  have hΦQ := isConformalBijection_comp hnR hΦR
  have hφcQ := isConformalBijection_comp hφcR hnQ
  have hIH : I ∈ H := show (0 : ℝ) < I.im by simp
  have hz₀ := hΦQ.2.mapsTo hIH
  have hcc : connectedComponentIn DQ ((negInv ∘ fun y => revChartInv Wβ q (fwdMapInv W' T y)) I) = DQ := by
    have hpre : IsPreconnected DQ := by
      rw [← hΦQ.2.image_eq]
      exact (convex_halfSpace_im_gt 0).isPreconnected.image _ hΦQ.1.continuousOn
    exact hpre.connectedComponentIn hz₀
  -- the derivative lift in the chart `Q`
  have hCo : IsOpen DR := isOpen_H_diff_union hd.hWα hd.ht.le hd.hGc (ω := Wβ) (s := q)
  have hDQo : IsOpen DQ := by
    rw [← hRQ]
    exact isOpen_image_negInv hCo sdiff_subset
  have hmaps := revChart_mapsTo_H_diff hd.hWβ hd.hWβ0 hd.hs hAG
  rw [← hd.hK'] at hmaps
  have hCsub : DR ⊆ H \ negInv '' A := fun z hz => ⟨hz.1, fun h => hz.2 (Or.inr h)⟩
  have hdR : DifferentiableOn ℂ (revChart Wβ q) DR :=
    fun z hz => (differentiableAt_revChart hd.hWβ hd.hs (hCsub hz)).differentiableWithinAt
  have hLR := IsDerivLog.comp hCo (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hd.hW' hd.hT.le)
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hd.hW' hd.hT.le) hdR hmaps (isDerivLog_fwdMap hd.hW' hd.hT.le)
    ((isDerivLog_revChart hd.hWβ hd.hs).mono hCsub)
  have hdφR : DifferentiableOn ℂ ((fun z => fwdMap W' T z) ∘ revChart Wβ q) DR := hφcR.1
  have hLQ := IsDerivLog.comp hDQo hCo hdφR (differentiableOn_negInv.mono sdiff_subset) hmQ hLR
    (isDerivLog_neg_inv.mono sdiff_subset)
  set LQ : ℂ → ℝ := fun z => (logDerivFwd W' T (revChart Wβ q (negInv z))).im +
    (logDerivPsi Wβ q (negInv z)).im - 2 * arg z with hLQdef
  have hLQim : ∀ z, LQ z = ((fun z => logDerivFwd W' T (revChart Wβ q z) + logDerivPsi Wβ q z) (negInv z) +
      (fun z : ℂ => -2 * log z) z).im := by
    intro z
    simp only [hLQdef, add_im, mul_im, log_im]
    norm_num
    ring
  have hLQc : ContinuousOn LQ DQ := by
    have := Complex.continuous_im.comp_continuousOn hLQ.1.continuousOn
    exact this.congr fun z _ => hLQim z
  have hderQ : ∀ z ∈ DQ, deriv ((fun z => fwdMap W' T z) ∘ revChart Wβ q ∘ negInv) z =
      ‖deriv ((fun z => fwdMap W' T z) ∘ revChart Wβ q ∘ negInv) z‖ * exp (LQ z * I) := by
    intro z hz
    have e := hLQ.2 z hz
    have hfe : ((fun z => fwdMap W' T z) ∘ revChart Wβ q ∘ negInv) =
        (((fun z => fwdMap W' T z) ∘ revChart Wβ q) ∘ negInv) := rfl
    rw [hfe, ← e]
    refine (GlueImg.exp_eq_norm_mul_exp_im _).trans ?_
    rw [hLQim z]
  -- the image-chart boundary limits read in the chart `Q`
  set ΦQ : ℂ → ℂ := negInv ∘ fun y => revChartInv Wβ q (fwdMapInv W' T y) with hΦQdef
  set φcQ : ℂ → ℂ := (fun z => fwdMap W' T z) ∘ revChart Wβ q ∘ negInv with hφcQdef
  have hlimQ : ∀ x : ℝ, x ∉ E → Tendsto (fun y => (fun z => w z + u₀ z) (ΦQ y) + 0 -
      ((fun y => -u y - (π - θ) * χ) y - χ * (fun y => LQ (ΦQ y)) y)) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    intro x hx
    have h2 := (hlim x hx).neg
    rw [neg_zero] at h2
    refine h2.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
    have hR : revChartInv Wβ q (fwdMapInv W' T y) ∈ DR := hΦR.2.mapsTo hy
    have e2 : revChart Wβ q (revChartInv Wβ q (fwdMapInv W' T y)) = fwdMapInv W' T y :=
      revChart_revChartInv hd.hWβ hd.hWβ0 hd.hs (QuantumZipper.RS.fwdMapInv_mem_H hd.hW' hd.hW'0 hd.hT.le hy)
    have e3 := GlueImg.arg_negInv_of_mem_H hR.1
    simp only [hΦQdef, hLQdef, Function.comp_apply, WangWu.negInv_negInv, e2, e3, hM, hc]
    ring
  have hφ : ∀ y ∈ H, φcQ (ΦQ y) = y := by
    intro y hy
    simp only [hΦQdef, hφcQdef, Function.comp_apply, WangWu.negInv_negInv]
    rw [revChart_revChartInv hd.hWβ hd.hWβ0 hd.hs (QuantumZipper.RS.fwdMapInv_mem_H hd.hW' hd.hW'0 hd.hT.le hy),
      QuantumZipper.RS.fwdMap_fwdMapInv hd.hW' hd.hW'0 hd.hT.le hy]
  have hdisk := tendsto_disk_of_imgChart (Φ := ΦQ) (φc := φcQ) (M := fun z => w z + u₀ z) (v := w) (F := u₀)
    (G := fun y => -u y - (π - θ) * χ) (χ := χ) (L := LQ) (Lb := fun y => LQ (ΦQ y)) (c := 0) hlimQ
    (fun y _ => by ring) hφ (fun y _ => rfl)
  have hEd : (insert (1 : ℂ) ((fun w : ℝ => cayley (w : ℂ)) '' E)).Finite := (hE.image _).insert 1
  have hGh : InnerProductSpace.HarmonicOnNhd (fun y => -u y - (π - θ) * χ) {w : ℂ | 0 < w.im} := fun y hy =>
    (hu.1 y hy).neg.sub (InnerProductSpace.harmonicAt_const _)
  have hGb : ∃ M, ∀ w : ℂ, 0 < w.im → |(fun y => -u y - (π - θ) * χ) w| ≤ M := by
    obtain ⟨C, hC⟩ := hu.2.1
    refine ⟨C + |(π - θ) * χ|, fun y hy => ?_⟩
    have h1 := hC y hy
    calc |-u y - (π - θ) * χ| ≤ |-u y| + |(π - θ) * χ| := abs_sub _ _
      _ = |u y| + |(π - θ) * χ| := by rw [abs_neg]
      _ ≤ C + |(π - θ) * χ| := by linarith
  have key := huniq _ hz₀
  rw [hcc] at key
  intro z hz
  have h := key (ΦQ ∘ cayleyInv) φcQ (fun y => -u y - (π - θ) * χ) LQ _
    (isConformalBijection_comp hΦQ isConformalBijection_cayleyInv) hφcQ hGh hGb hLQc hderQ hEd hdisk z hz
  rw [h]
  simp only [hφcQdef, hLQdef, Function.comp_apply]

end InteractingSLE.Sec5.Lemma47Angle
