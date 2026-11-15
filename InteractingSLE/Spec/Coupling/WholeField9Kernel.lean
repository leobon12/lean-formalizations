/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField9Induct
import InteractingSLE.Spec.Coupling.WholeField9Recon
import InteractingSLE.Spec.Coupling.WholeField9Cover
import InteractingSLE.Spec.Coupling.WholeField7Main

/-!
# C.5 for `0 < κ ≤ 4`: the whole-field kernel in conditional-mean form

Packet PROVE-WHOLEFIELD9 (follow-up note C.5, `source/external/AstraIG1/ig1_followup_proofs.txt` L1705–1840; ruling
R38).

For the frozen coupling with `0 < κ ≤ 4` whose driver almost surely has a continuous generating trace through its
lifetime (the hypothesis of specification Aux. lemma 16), at every bounded driving stop `σ < ζ` and for every test `φ`
and real `t`:

  `E[e^{it(h,φ)} | 𝓕_σ] = exp(i t E[(h,φ) | 𝓕_σ] − ½ t² Q_{U_σ}(φ))`   (`ae_condExp_exp_eq_gaussCF_of_trace`).

Proof: PROVE-WHOLEFIELD7's assembly (`WholeField7Main`) with the label events of the rational balls, the set
`A = offLabels` (thin by (WF1) for `κ ≤ 4`, `WholeField9Cover`), C.4 in conditional-mean form on the pieces of a
partition of unity (`WholeField9Induct`), and the conditional-mean reconstruction (`WholeField9Recon`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LQGMetric QuantumZipper LocalSets Ito Coupling

section Main

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The label events of the rational balls** at a driving stop. -/
theorem exists_labelEvents (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) :
    ∃ G : ℚ × ℚ × ℚ → Set Ω, (∀ q, MeasurableSet[hσ.measurableSpace] (G q)) ∧
      (∀ ω q, ω ∈ G q → IsGoodBall q) ∧
      ∀ᵐ ω ∂P, ∀ q, IsGoodBall q → (ω ∈ G q ↔ IsLabel (W · ω) (closedBall (qCentre q) (qRad q)) (σ ω)) := by
  have hlab : ∀ q : ℚ × ℚ × ℚ, ∃ G : Set Ω, MeasurableSet[hσ.measurableSpace] G ∧ (¬ IsGoodBall q → G = ∅) ∧
      ∀ᵐ ω ∂P, IsGoodBall q → (ω ∈ G ↔ IsLabel (W · ω) (closedBall (qCentre q) (qRad q)) (σ ω)) := by
    intro q
    by_cases hq : IsGoodBall q
    · obtain ⟨G, hG, hGe⟩ := exists_labelEvent hE hκ hX hσ hσζ (isCompact_closedBall _ _) hq.2
      exact ⟨G, hG, fun h' => absurd hq h', hGe.mono fun ω hω _ => hω⟩
    · exact ⟨∅, @MeasurableSet.empty _ hσ.measurableSpace, fun _ => rfl,
        Eventually.of_forall fun ω h' => absurd h' hq⟩
  choose G hGm hG0 hGe using hlab
  refine ⟨G, hGm, fun ω q hω => ?_, ae_all_iff.2 hGe⟩
  by_contra hq; rw [hG0 q hq] at hω; exact hω

/-- **C.5 for `0 < κ ≤ 4` in conditional-mean form.** For the frozen coupling whose driver almost surely has a
continuous generating trace through its lifetime, a bounded driving stop `σ < ζ`, a test `φ` and a real `t`: almost
surely, `E[e^{it(h,φ)} | 𝓕_σ] = exp(i t E[(h,φ) | 𝓕_σ] − ½ t² Q_{U_σ}(φ))`. -/
theorem ae_condExp_exp_eq_gaussCF_of_trace (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσN : ∀ ω, σ ω ≤ N)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    (φ : TestOn upperHalfPlaneOpens) (t : ℝ) :
    ∀ᵐ ω ∂P, (P[fun ω' => cexp (Complex.I * ((t * h ω' φ : ℝ) : ℂ)) | hσ.measurableSpace]) ω =
      WangWu.gaussCF (t * (P[fun ω' => h ω' φ | hσ.measurableSpace]) ω)
        (t ^ 2 * WangWu.retainedGreenEnergy (W · ω) (σ ω) φ) := by
  have hE := hC.1
  obtain ⟨G, hGm, hGgood, hGall⟩ := exists_labelEvents hE hκ hX hσ hσζ
  -- a Borel version of the retained Green kernel along each regular path
  have hgr : ∀ ω, ∃ g : ℂ × ℂ → ℝ, Measurable g ∧
      ((ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 ∧ (σ ω : ℝ≥0∞) < ζ ω) →
        ∀ p : ℂ × ℂ, p.1 ∈ H → p.2 ∈ H → g p = WangWu.retainedGreen (W · ω) (σ ω) p.1 p.2) ∧
      (¬ (ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 ∧ (σ ω : ℝ≥0∞) < ζ ω) →
        g = 0) := by
    intro ω
    by_cases hω : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 ∧ (σ ω : ℝ≥0∞) < ζ ω
    · obtain ⟨g, hg, hge⟩ := exists_measurable_retainedGreen_of_path hω.1 hω.2.1 hω.2.2
      exact ⟨g, hg, fun _ => hge, fun h' => absurd hω h'⟩
    · exact ⟨0, measurable_const, fun h' => absurd h' hω, fun _ => rfl⟩
  choose g hgm hge hg0 using hgr
  have hgf : ∀ ω (ψ : TestOn upperHalfPlaneOpens),
      (ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 ∧ (σ ω : ℝ≥0∞) < ζ ω) →
      WangWu.greenForm (fun a b => g ω (a, b)) ψ = WangWu.retainedGreenEnergy (W · ω) (σ ω) ψ := by
    intro ω ψ hω
    unfold WangWu.greenForm WangWu.retainedGreenEnergy
    refine integral_congr_ae (Eventually.of_forall fun a => integral_congr_ae
      (Eventually.of_forall fun b => ?_))
    show ψ a * g ω (a, b) * ψ b = ψ a * WangWu.retainedGreen (W · ω) (σ ω) a b * ψ b
    by_cases ha : ψ a = 0
    · simp [ha]
    by_cases hb : ψ b = 0
    · simp [hb]
    rw [hge ω hω (a, b) (ψ.tsupport_subset (subset_tsupport _ ha)) (ψ.tsupport_subset (subset_tsupport _ hb))]
  have hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 ∧
      (σ ω : ℝ≥0∞) < ζ ω := by
    filter_upwards [hE.2.2.2.2, hσζ] with ω hp hlt using ⟨hp.2.2.2.1, hp.1, hlt⟩
  -- the hypotheses of the reconstruction
  obtain ⟨u₀, hu₀⟩ := exists_bhe κ ρL ρR xL xR
  obtain ⟨Mm, hMm⟩ := hu₀.2.1
  have hh0 := isZeroBoundaryGFF_centredField hC hu₀
  have hF : ∀ ω (ψ : TestOn upperHalfPlaneOpens), h ω ψ = centredField h u₀ ω ψ + ∫ z, u₀ z * ψ z :=
    fun ω ψ => by rw [centredField_apply h hu₀.1 ω ψ]; ring
  have hA𝒢 : ∀ ψ : TestOn upperHalfPlaneOpens,
      MeasurableSet[hσ.measurableSpace] {ω | Disjoint (tsupport ψ) (offLabels G ω)} := fun ψ =>
    measurableSet_disjoint_offLabels hGm ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  have hGk : ∀ ω (a b : ℂ), a ∈ H → b ∈ H → a ≠ b →
      0 ≤ (fun a b => g ω (a, b)) a b ∧ (fun a b => g ω (a, b)) a b ≤ QuantumZipper.greenH a b := by
    intro ω a b ha hb hab
    by_cases hω : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 ∧ (σ ω : ℝ≥0∞) < ζ ω
    · show 0 ≤ g ω (a, b) ∧ g ω (a, b) ≤ _
      rw [hge ω hω (a, b) ha hb]
      exact ⟨WangWu.retainedGreen_nonneg _ _ _ _,
        retainedGreen_le_greenH_of_path hω.1 hω.2.1 hω.2.2 ha hb hab⟩
    · show 0 ≤ g ω (a, b) ∧ g ω (a, b) ≤ _
      rw [hg0 ω hω]
      exact ⟨le_rfl, QuantumZipper.greenH_nonneg (le_of_lt (show (0 : ℝ) < a.im from ha))
        (le_of_lt (show (0 : ℝ) < b.im from hb)) hab⟩
  -- the kernel off `A` (C.4 on the pieces)
  have hker : ∀ (ψ : TestOn upperHalfPlaneOpens) (s : ℝ), ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (offLabels G ω) →
      (P[fun ω' => cexp (Complex.I * ((s * h ω' ψ : ℝ) : ℂ)) | hσ.measurableSpace]) ω =
        WangWu.gaussCF (s * (P[fun ω' => h ω' ψ | hσ.measurableSpace]) ω)
          (s ^ 2 * WangWu.greenForm (fun a b => g ω (a, b)) ψ) := by
    intro ψ s
    obtain ⟨R, hR⟩ := ψ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
    have hsum : ∀ n, ∑ k ∈ WangWu.pouIdx (WangWu.scaleIdx R n), WangWu.pouTest ψ n k = ψ := fun n =>
      WangWu.sum_pouTest hR (WangWu.le_scaleIdx R n)
    have hC4 : ∀ n : ℕ, ∀ᵐ ω ∂P, (∀ k ∈ WangWu.pouIdx (WangWu.scaleIdx R n),
        IsLabel (W · ω) (tsupport (WangWu.pouTest ψ n k)) (σ ω)) →
        (P[fun ω' => cexp (Complex.I * (h ω' (s • ψ) : ℂ)) | hσ.measurableSpace]) ω =
          cmKer P hσ.measurableSpace h W (σ ω) (s • ψ) ω := fun n => by
      have := ae_condExp_exp_eq_cmKer_of_isLabel hC hκ hX (fun k => WangWu.pouTest ψ n k)
        (WangWu.pouIdx (WangWu.scaleIdx R n)) hσ hσζ hσN s
      simp only [hsum n] at this
      exact this
    filter_upwards [ae_all_iff.2 hC4, hGall, hpath, ae_cmKer_smul (P := P) hσ.measurableSpace h W σ s ψ]
      with ω hc4 hgω hp hsm hd
    obtain ⟨n₀, hn₀⟩ := exists_scale_isLabel (fun q hq => (hgω q (hGgood ω q hq)).1 hq) ψ hd
    rw [← exp_pairing_smul, hc4 n₀ fun k _ => hn₀ n₀ le_rfl k, hsm, hgf ω ψ hp, WangWu.gaussCF]
  -- (WF1) for `A ⊆ η[0,σ]`
  have hcov : ∀ᵐ ω ∂P, Tendsto (fun j => (Dimension.dyadicCount (id j) (offLabels G ω ∩ tsupport φ) : ℝ) *
      ((id j : ℕ) + 1) / 4 ^ (id j)) atTop (𝓝 0) := by
    filter_upwards [htr, ae_tendsto_dyadicCount_trace hκ hκ4 hE, hGall, hE.2.2.2.2, hσζ] with ω ⟨η, hη⟩
      hcnt hgω hp hlt
    have hsub : offLabels G ω ∩ tsupport φ ⊆ η '' Icc 0 (σ ω) ∩ tsupport φ :=
      inter_subset_inter_left _ (offLabels_subset_image hp.2.2.2.1 hη hlt fun q hq hl => (hgω q hq).2 hl)
    refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (hcnt η hη (σ ω) hlt (tsupport φ) φ.hasCompactSupport.isCompact φ.tsupport_subset)
    have h4 : (0 : ℝ) < 4 ^ n := by positivity
    simp only [id]
    gcongr
    exact_mod_cast Set.ncard_le_ncard (Dimension.dyadicHits_mono hsub)
      (Dimension.dyadicHits_finite (φ.hasCompactSupport.isCompact.isBounded.subset inter_subset_right))
  have hmain := ae_condExp_exp_eq_gaussCF_condMean (P := P) (F := h) (A := offLabels G)
    hσ.measurableSpace_le hh0 hMm hF hA𝒢 (G := fun ω a b => g ω (a, b)) (fun ω => hgm ω) hGk hker φ
    tendsto_id hcov t
  filter_upwards [hmain, hpath] with ω h1 hp
  rw [h1, hgf ω φ hp]

end Main

end WholeField

end InteractingSLE
