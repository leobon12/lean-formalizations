/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField7Recon
import InteractingSLE.WangWu.NonBoundaryKernel
import InteractingSLE.WangWu.Bridge

/-!
# Whole-field identification (WF2) at `κ = 4`

Packet PROVE-WHOLEFIELD7 (follow-up note Part C, `source/external/AstraIG1/ig1_followup_proofs.txt` L1382–1910;
rulings R36, R38, R40).

* **C.5** (`ae_condExp_exp_eq_kerCF_of_trace`): for the frozen `κ = 4` coupling whose driver almost surely has a
  continuous generating trace through its lifetime, at every bounded driving stop `σ < ζ` and for every test function
  `φ`: `E[e^{i(h,φ)} | 𝓕_σ] = exp(i ∫ η̄_σ φ − ½ Q_{U_σ}(φ, φ))` (`kerCF`). Proposition R1's reconstruction
  (`WangWu.ae_condExp_exp_eq_gaussCF`) with the set `A = offLabels` off the labelled rational balls: its avoidance
  events are in `𝓕_σ`; off `A` the C.4 kernel holds (pieces of a partition of unity at a fine scale are labels);
  `A ⊆ η[0,σ]`, whose covering numbers are thin by (WF1) (`ae_tendsto_dyadicCount_trace_four`).
* **The `κ = 4` conclusion** (`hasWholeFieldKernels_of_isCompleteForceWord`): a force word all of whose evolutions
  have a continuous trace through the lifetime (`LP.IsCompleteForceWord 4`) has the whole-field kernel (WF2) for every
  frozen coupling (`WangWu.HasWholeFieldKernels`). The covariance is identified with `G_{ℍ∖η[0,τ]}` by
  `zeroGFFTestCov_compl_image_eq_retainedGreenEnergy` along the complete trace (the given trace through `S` agrees
  with it on `[0, S]`, `IsGeneratingTrace.eq_of_le`), which covers the edge case `τ = S`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LQGMetric QuantumZipper LocalSets Ito Coupling

section Main

universe u

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

omit mΩ [IsProbabilityMeasure P] in
/-- The Gaussian value with a version of the frozen mean and of the retained Green kernel is the kernel value. -/
theorem gaussCF_eq_kerCF {ω : Ω} {t : ℝ≥0} {v : ℂ → ℝ}
    (hv : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ H →
      v z = WangWu.frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) t z)
    {g : ℂ × ℂ → ℝ} (hg : ∀ p : ℂ × ℂ, p.1 ∈ H → p.2 ∈ H → g p = WangWu.retainedGreen (W · ω) t p.1 p.2)
    (ψ : TestOn upperHalfPlaneOpens) :
    WangWu.gaussCF (∫ z, v z * ψ z) (WangWu.greenForm (fun a b => g (a, b)) ψ) =
      kerCF ρL ρR W VL VR t ψ ω := by
  have hm : (∫ z, v z * ψ z) =
      ∫ z, WangWu.frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) t z * ψ z := by
    refine integral_congr_ae ?_
    filter_upwards [hv] with z hz
    by_cases hzH : z ∈ H
    · rw [hz hzH]
    · rw [testOn_eq_zero_of_notMem_H ψ hzH, mul_zero, mul_zero]
  have hq : WangWu.greenForm (fun a b => g (a, b)) ψ = WangWu.retainedGreenEnergy (W · ω) t ψ := by
    unfold WangWu.greenForm WangWu.retainedGreenEnergy
    refine integral_congr_ae (Eventually.of_forall fun a => integral_congr_ae
      (Eventually.of_forall fun b => ?_))
    show ψ a * g (a, b) * ψ b = ψ a * WangWu.retainedGreen (W · ω) t a b * ψ b
    by_cases ha : ψ a = 0
    · simp [ha]
    by_cases hb : ψ b = 0
    · simp [hb]
    rw [hg (a, b) (ψ.tsupport_subset (subset_tsupport _ ha)) (ψ.tsupport_subset (subset_tsupport _ hb))]
  rw [WangWu.gaussCF, kerCF, hm, hq]

/-- **C.5 at `κ = 4`: the whole-field kernel at a bounded stop.** For the frozen `κ = 4` coupling whose driver almost
surely has a continuous generating trace through its lifetime, a bounded driving stop `σ < ζ` and a test function
`φ`: almost surely `E[e^{i(h,φ)} | 𝓕_σ] = exp(i ∫ η̄_σ φ − ½ Q_{U_σ}(φ, φ))`. -/
theorem ae_condExp_exp_eq_kerCF_of_trace (hC : IsOptionalHullCoupling 4 xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσN : ∀ ω, σ ω ≤ N)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, (P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | hσ.measurableSpace]) ω =
      kerCF ρL ρR W VL VR (σ ω) φ ω := by
  have hE := hC.1
  -- the label events of the rational balls
  have hlab : ∀ q : ℚ × ℚ × ℚ, ∃ G : Set Ω, MeasurableSet[hσ.measurableSpace] G ∧ (¬ IsGoodBall q → G = ∅) ∧
      ∀ᵐ ω ∂P, IsGoodBall q → (ω ∈ G ↔ IsLabel (W · ω) (closedBall (qCentre q) (qRad q)) (σ ω)) := by
    intro q
    by_cases hq : IsGoodBall q
    · obtain ⟨G, hG, hGe⟩ := exists_labelEvent hE (by norm_num) hX hσ hσζ (isCompact_closedBall _ _) hq.2
      exact ⟨G, hG, fun h' => absurd hq h', hGe.mono fun ω hω _ => hω⟩
    · exact ⟨∅, @MeasurableSet.empty _ hσ.measurableSpace, fun _ => rfl,
        Eventually.of_forall fun ω h' => absurd h' hq⟩
  choose G hGm hG0 hGe using hlab
  have hGall : ∀ᵐ ω ∂P, ∀ q, IsGoodBall q →
      (ω ∈ G q ↔ IsLabel (W · ω) (closedBall (qCentre q) (qRad q)) (σ ω)) := ae_all_iff.2 hGe
  have hGgood : ∀ ω q, ω ∈ G q → IsGoodBall q := fun ω q hω => by
    by_contra hq; rw [hG0 q hq] at hω; exact hω
  -- versions of the frozen mean and of the retained Green kernel
  have hdu := Ito.drivingFiltration_le_usualAugmentation hE hX
  obtain ⟨Yv, hYm, hYb, -, hYae⟩ :=
    WangWu.exists_frozenMean_version hE (IsStoppingTime.mono_filtration hdu hσ) hσζ hσN
  have hYae' : ∀ᵐ ω ∂P, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ H → Yv (σ ω) z ω =
      WangWu.frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (σ ω) z := by
    filter_upwards [hYae] with ω hω
    filter_upwards [hω] with z hz hzH
    rw [hz hzH (σ ω), min_self]
  have hgr : ∀ ω, ∃ g : ℂ × ℂ → ℝ, Measurable g ∧
      ((IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (B · ω) (ζ ω) ∧
        (σ ω : ℝ≥0∞) < ζ ω) →
        ∀ p : ℂ × ℂ, p.1 ∈ H → p.2 ∈ H → g p = WangWu.retainedGreen (W · ω) (σ ω) p.1 p.2) ∧
      (¬ (IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (B · ω)
        (ζ ω) ∧ (σ ω : ℝ≥0∞) < ζ ω) → g = 0) := by
    intro ω
    by_cases hω : IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
      (B · ω) (ζ ω) ∧ (σ ω : ℝ≥0∞) < ζ ω
    · obtain ⟨g, hg, hge⟩ := WangWu.exists_measurable_retainedGreen hω.1 hω.2
      exact ⟨g, hg, fun _ => hge, fun h' => absurd hω h'⟩
    · exact ⟨0, measurable_const, fun h' => absurd h' hω, fun _ => rfl⟩
  choose g hgm hge hg0 using hgr
  -- the hypotheses of the reconstruction
  obtain ⟨Mm, hMm⟩ := hu₀.2.1
  have hh0 := isZeroBoundaryGFF_centredField hC hu₀
  have hF : ∀ ω (ψ : TestOn upperHalfPlaneOpens), h ω ψ = centredField h u₀ ω ψ + ∫ z, u₀ z * ψ z :=
    fun ω ψ => by rw [centredField_apply h hu₀.1 ω ψ]; ring
  have hA𝒢 : ∀ ψ : TestOn upperHalfPlaneOpens,
      MeasurableSet[hσ.measurableSpace] {ω | Disjoint (tsupport ψ) (offLabels G ω)} := fun ψ =>
    measurableSet_disjoint_offLabels hGm ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  have hvm : ∀ ω, Measurable fun z => Yv (σ ω) z ω := fun ω => (hYm (σ ω)).comp measurable_prodMk_right
  have hGk : ∀ ω (a b : ℂ), a ∈ H → b ∈ H → a ≠ b →
      0 ≤ (fun a b => g ω (a, b)) a b ∧ (fun a b => g ω (a, b)) a b ≤ QuantumZipper.greenH a b := by
    intro ω a b ha hb hab
    by_cases hω : IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
      (B · ω) (ζ ω) ∧ (σ ω : ℝ≥0∞) < ζ ω
    · show 0 ≤ g ω (a, b) ∧ g ω (a, b) ≤ _
      rw [hge ω hω (a, b) ha hb]
      exact ⟨WangWu.retainedGreen_nonneg _ _ _ _, WangWu.retainedGreen_le_greenH hω.1
        (lt_of_le_of_lt bot_le hω.2) ha hb hab _⟩
    · show 0 ≤ g ω (a, b) ∧ g ω (a, b) ≤ _
      rw [hg0 ω hω]
      exact ⟨le_rfl, QuantumZipper.greenH_nonneg (le_of_lt (show (0 : ℝ) < a.im from ha))
        (le_of_lt (show (0 : ℝ) < b.im from hb)) hab⟩
  -- the kernel off `A` (C.4 on the pieces)
  have hker : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (offLabels G ω) →
      (P[fun ω' => Complex.exp (Complex.I * (h ω' ψ : ℂ)) | hσ.measurableSpace]) ω =
        WangWu.gaussCF (∫ z, Yv (σ ω) z ω * ψ z) (WangWu.greenForm (fun a b => g ω (a, b)) ψ) := by
    intro ψ
    obtain ⟨R, hR⟩ := ψ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
    have hsum : ∀ n, ∑ k ∈ WangWu.pouIdx (WangWu.scaleIdx R n), WangWu.pouTest ψ n k = ψ := fun n =>
      WangWu.sum_pouTest hR (WangWu.le_scaleIdx R n)
    have hC4 : ∀ n : ℕ, ∀ᵐ ω ∂P, (∀ k ∈ WangWu.pouIdx (WangWu.scaleIdx R n),
        IsLabel (W · ω) (tsupport (WangWu.pouTest ψ n k)) (σ ω)) →
        (P[fun ω' => Complex.exp (Complex.I * (h ω' ψ : ℂ)) | hσ.measurableSpace]) ω =
          kerCF ρL ρR W VL VR (σ ω) ψ ω := fun n => by
      have := ae_condExp_exp_eq_kerCF_of_isLabel hC hu₀ hX (fun k => WangWu.pouTest ψ n k)
        (WangWu.pouIdx (WangWu.scaleIdx R n)) hσ hσζ hσN
      simp only [hsum n] at this
      exact this
    filter_upwards [ae_all_iff.2 hC4, hGall, hYae', hE.2.2.2.2, hσζ] with ω hc4 hgω hyω hp hlt hd
    obtain ⟨n₀, hn₀⟩ := exists_scale_isLabel (fun q hq => (hgω q (hGgood ω q hq)).1 hq) ψ hd
    rw [hc4 n₀ fun k _ => hn₀ n₀ le_rfl k]
    exact (gaussCF_eq_kerCF hyω (hge ω ⟨hp, hlt⟩) ψ).symm
  -- (WF1) for `A ⊆ η[0,σ]`
  have hcov : ∀ᵐ ω ∂P, Tendsto (fun j => (Dimension.dyadicCount (id j) (offLabels G ω ∩ tsupport φ) : ℝ) *
      ((id j : ℕ) + 1) / 4 ^ (id j)) atTop (𝓝 0) := by
    filter_upwards [htr, ae_tendsto_dyadicCount_trace_four hE, hGall, hE.2.2.2.2, hσζ] with ω ⟨η, hη⟩ hcnt hgω
      hp hlt
    have hsub : offLabels G ω ∩ tsupport φ ⊆ η '' Icc 0 (σ ω) ∩ tsupport φ :=
      inter_subset_inter_left _ (offLabels_subset_image hp.2.2.2.1 hη hlt fun q hq hl => (hgω q hq).2 hl)
    refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (hcnt η hη (σ ω) hlt (tsupport φ) φ.hasCompactSupport.isCompact φ.tsupport_subset)
    have h4 : (0 : ℝ) < 4 ^ n := by positivity
    simp only [id]
    gcongr
    exact_mod_cast Set.ncard_le_ncard (Dimension.dyadicHits_mono hsub)
      (Dimension.dyadicHits_finite (φ.hasCompactSupport.isCompact.isBounded.subset inter_subset_right))
  have hmain := WangWu.ae_condExp_exp_eq_gaussCF (P := P) (F := h) (A := offLabels G) hσ.measurableSpace_le
    hh0 hMm hF hA𝒢 hvm (fun ω z => hYb (σ ω) z ω) (G := fun ω a b => g ω (a, b)) (fun ω => hgm ω) hGk hker φ
    tendsto_id hcov
  filter_upwards [hmain, hYae', hE.2.2.2.2, hσζ] with ω h1 hyω hp hlt
  rw [h1]
  exact gaussCF_eq_kerCF hyω (hge ω ⟨hp, hlt⟩) φ

end Main

section Conclusion

universe u

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The whole-field identification (WF2) at `κ = 4`** (follow-up note Part C, Theorem "original-hull to full-range
upgrade", ruling R38; the `κ = 4` bridge of rulings R36/R40). If every integrated `SLE₄(ρ)` evolution of the force
word has, almost surely, a continuous generating trace through its lifetime (`LP.IsCompleteForceWord 4`), then every
frozen coupling of the word (`IsOptionalHullCoupling 4`) has the whole-field kernel `WangWu.HasWholeFieldKernel`: at
every stopping time `τ ≤ S` (`S < ζ` bounded) and for every continuous generating trace `η` through `S`,
`E[e^{i(h,φ)} | 𝓕_τ] = exp(i ∫ M_τ φ − ½ G_{ℍ∖η[0,τ]}(φ, φ))`. -/
theorem hasWholeFieldKernels_of_isCompleteForceWord (htr : LP.IsCompleteForceWord.{u} 4 xL xR ρL ρR) :
    WangWu.HasWholeFieldKernels.{u} xL xR ρL ρR := by
  intro Ω mΩ P hP 𝓕 W VL VR B ζ h hC
  have hE := hC.1
  obtain ⟨hX, -⟩ := hC.2.2.2
  obtain ⟨u₀, hu₀⟩ := exists_bhe 4 ρL ρR xL xR
  have htr' := htr P 𝓕 W VL VR B ζ hE
  refine ⟨hX, fun S τ hS hτ hSN hSζ hτS φ => ?_⟩
  obtain ⟨N, hN⟩ := hSN
  have hτne : ∀ ω, τ ω ≠ ⊤ := fun ω => ne_top_of_le_ne_top WithTop.coe_ne_top ((hτS ω).trans (hN ω))
  set σ : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hσdef
  have hστ : (fun ω => (σ ω : WithTop ℝ≥0)) = τ := funext fun ω => coe_untopD_of_ne_top (hτne ω)
  have hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0) := hστ ▸ hτ
  have hms : hσ.measurableSpace = hτ.measurableSpace := IsStoppingTime.measurableSpace_congr hσ hτ hστ
  have hσS : ∀ ω, (σ ω : WithTop ℝ≥0) ≤ S ω := fun ω => (congrFun hστ ω).trans_le (hτS ω)
  have hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω := by
    filter_upwards [hSζ] with ω hω
    exact lt_of_le_of_lt (hσS ω) hω
  have hσN : ∀ ω, σ ω ≤ N := fun ω => by
    have := (hσS ω).trans (hN ω)
    exact_mod_cast this
  have hc5 := ae_condExp_exp_eq_kerCF_of_trace hC hu₀ hX hσ hσζ hσN
    (htr'.mono fun ω hω => by obtain ⟨η, hη, -⟩ := hω; exact ⟨η, hη⟩) φ
  filter_upwards [hc5, htr', hE.2.2.2.2, hSζ, hσζ, hE.ae_dimH_image_inter_H_le (by norm_num) (by norm_num)]
    with ω h5 hηfω hp hSω hσω hdim η hη
  obtain ⟨ηf, hηf, -⟩ := hηfω
  -- the given trace agrees with the complete one on `[0, S]`
  have hwS : ContinuousOn (fun t => W t ω) {s : ℝ≥0 | (s : ℝ≥0∞) < (S ω : ℝ≥0∞)} :=
    hp.2.2.2.1.mono fun s hs => lt_trans hs hSω
  have himg : η '' Icc 0 (σ ω) = ηf '' Icc 0 (σ ω) := by
    refine image_congr fun t ht => hη.eq_of_le (hηf.mono_horizon hSω.le) hwS hp.1 ?_
    exact le_trans (WithTop.coe_le_coe.2 ht.2) (hσS ω)
  have harea : volume (ηf '' Icc 0 (σ ω) ∩ H) = 0 := by
    refine volume_eq_zero_of_dimH_lt_two (lt_of_le_of_lt (hdim ηf hηf (Icc 0 (σ ω)) fun s hs =>
      le_trans (ENNReal.coe_le_coe.2 hs.2) hσω.le) ?_)
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (Dimension.interiorDimBound_lt_two (by norm_num))
  rw [← hms]
  rw [show condExp hσ.measurableSpace P (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
    (P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | hσ.measurableSpace]) ω from rfl, h5, kerCF, himg,
    zeroGFFTestCov_compl_image_eq_retainedGreenEnergy hηf hp.2.2.2.1 hp.1 hσω harea φ]

/-- **Field determination at `κ = 4` for a complete force word**: with Wang–Wu's Theorem 4.25 for the word, every frozen
`κ = 4` coupling of a force word whose evolutions have a continuous trace through the lifetime has a field-determined
killed history (`WangWu.hasFieldDeterminedHistories_of_wholeField` with the whole-field kernel proved here). -/
theorem hasFieldDeterminedHistories_of_isCompleteForceWord (htr : LP.IsCompleteForceWord.{u} 4 xL xR ρL ρR)
    (h425 : WangWu.HasDeterminedFullCouplings.{u} xL xR ρL ρR) :
    LP.HasFieldDeterminedHistories.{u} 4 xL xR ρL ρR :=
  WangWu.hasFieldDeterminedHistories_of_wholeField (hasWholeFieldKernels_of_isCompleteForceWord htr) htr h425

end Conclusion

end WholeField

end InteractingSLE
