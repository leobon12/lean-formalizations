/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofFinalFiltration

/-!
# Transporting the stopped (S) and (L) identities

Packet PROVE-RETPLUMB. Both identities transport to the actual measurable
pushforward of a conditional law in the image filtration. The lifetime is an
arbitrary boundary stop, not an assumed continuation threshold.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open LQGMetric (DistOn TestOn)
open Sec7.PocketTraversal DomainMarkov DomainMarkov.K2 FCDet
open Coupling LocalSets
variable {Ω S : Type*} [mΩ : MeasurableSpace Ω] [mS : MeasurableSpace S]
  {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → S} {𝓗 : Filtration ℝ≥0 mΩ}
  {M : Set Ω} {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {V : Ω → ℝ≥0∞} {V' : S → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {W' : ℝ≥0 → S → ℝ}
  {X : Ω → DistOn upperHalfPlaneOpens} {X' : S → DistOn upperHalfPlaneOpens}
  {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
  {xL' : S → Fin nL → ℝ} {xR' : S → Fin nR → ℝ}

/-- The field complement identity survives conditional model transport. -/
theorem hasSafeMembers_map_retImage (hM : MeasurableSet[𝓗 0] M) (hY : Measurable Y)
    (hX' : Measurable X') (hXY : ∀ ω, X' (Y ω) = X ω)
    (hWY : ∀ ω t, W' t (Y ω) = W t ω) (hVY : ∀ ω, V' (Y ω) = V ω)
    (hL : HasSafeMembers P 𝓗 M V W X) :
    HasSafeMembers ((P[|M]).map Y) (retImageFiltration Y 𝓗) univ V' W' X' := by
  have hMm := 𝓗.le 0 _ hM
  intro q Fb hFb D hD hDae f Ξ
  have hDm := (retImageFiltration Y 𝓗).le q _ hD
  have hfm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable fun s =>
      Complex.exp (Complex.I * (X' s φ : ℂ)) := fun φ =>
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (((measurable_pi_apply φ).comp (Measurable.of_comap_le le_rfl)).comp hX')))
  rw [setIntegral_map_cond hMm hY hDm (hfm _).aestronglyMeasurable,
    setIntegral_map_cond hMm hY hDm (hfm _).aestronglyMeasurable, mul_smul_comm]
  congr 1
  have hE : MeasurableSet[𝓗 q] (M ∩ Y ⁻¹' D) :=
    (𝓗.mono (zero_le : (0 : ℝ≥0) ≤ q) _ hM).inter (measurable_retImageFiltration Y 𝓗 q hD)
  have hp := ae_imp_of_ae_cond hMm (ae_of_ae_map hY.aemeasurable hDae)
  have hcond : ∀ᵐ ω ∂P, ω ∈ M ∩ Y ⁻¹' D → ω ∈ M ∧ (q : ℝ≥0∞) < V ω ∧
      Disjoint (ballsK Fb) (QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) (q : ℝ)) := by
    filter_upwards [hp] with ω hω hωE
    obtain ⟨_, hl, hd⟩ := hω hωE.1 hωE.2
    rw [hVY] at hl
    simp only [hWY] at hd
    exact ⟨hωE.1, hl, hd⟩
  simpa only [hXY] using hL q Fb hFb (M ∩ Y ⁻¹' D) hE hcond f Ξ

/-- The stopped Gaussian identity survives conditional model transport. The
safe indicator makes every mapped right-hand integrand measurable. -/
theorem hasSafeLaw_map_retImage (hM : MeasurableSet[𝓗 0] M) (hY : Measurable Y)
    (hX' : Measurable X') (hXY : ∀ ω, X' (Y ω) = X ω)
    (hWY : ∀ ω t, W' t (Y ω) = W t ω) (hVY : ∀ ω, V' (Y ω) = V ω)
    (hLY : ∀ ω, xL' (Y ω) = xL ω) (hRY : ∀ ω, xR' (Y ω) = xR ω)
    (hW0' : ∀ s, W' 0 s = 0) (hWc' : ∀ s, Continuous (W' · s))
    (hWa' : StronglyAdapted (retImageFiltration Y 𝓗) W')
    (hLm' : Measurable[retImageFiltration Y 𝓗 0] xL')
    (hRm' : Measurable[retImageFiltration Y 𝓗 0] xR')
    (hVs' : ∀ t : ℝ≥0, MeasurableSet[retImageFiltration Y 𝓗 t] {s | V' s ≤ t})
    (hS : HasSafeLaw κ ρL ρR P 𝓗 M V W (geomLW W xL) (geomRW W xR) X) :
    HasSafeLaw κ ρL ρR ((P[|M]).map Y) (retImageFiltration Y 𝓗) univ V' W'
      (geomLW W' xL') (geomRW W' xR') X' := by
  classical
  have hMm := 𝓗.le 0 _ hM
  have hweak := isWeakPath_geom hW0' hWc' xL' xR' V'
  have hWa₀ := MartChar.adaptedBefore_of_stronglyAdapted hVs' hWa'
  have hL₀ := fun i => MartChar.adaptedBefore_of_stronglyAdapted hVs'
    (stronglyAdapted_geomLW hWa' hWc' hLm' i)
  have hR₀ := fun j => MartChar.adaptedBefore_of_stronglyAdapted hVs'
    (stronglyAdapted_geomRW hWa' hWc' hRm' j)
  have hav : ∀ (ω : Ω) (φ : ℂ → ℝ) (q : ℝ≥0),
      Y ω ∈ avoidSet W' V' φ q ↔ ω ∈ avoidSet W V φ q := by
    intro ω φ q
    simp only [avoidSet, mem_ofPred_eq, hVY, hWY]
  intro φ q D hD hDae
  have hDm := (retImageFiltration Y 𝓗).le q _ hD
  let u' := bheProc κ ρL ρR W' (geomLW W' xL') (geomRW W' xR')
  let g' : S → ℂ := (safeU W' V' univ φ q).indicator (cfAt κ W' u' φ 1 fun _ => q)
  have hgm : Measurable g' :=
    (measurable_safeU_indicator_cfAt_of_weak hweak hWa₀ MeasurableSet.univ u'
      (fun s r => isBoundedHarmonicExtension_bheProc s r) hL₀ hR₀ φ q).mono
        ((retImageFiltration Y 𝓗).le q) le_rfl
  have hfm : Measurable fun s => Complex.exp (Complex.I * (X' s φ : ℂ)) :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (((measurable_pi_apply φ).comp (Measurable.of_comap_le le_rfl)).comp hX')))
  have hRHS : ∫ s in D, cfAt κ W' u' φ 1 (fun _ => q) s ∂((P[|M]).map Y) =
      ∫ s in D, g' s ∂((P[|M]).map Y) := by
    apply setIntegral_congr_ae hDm
    filter_upwards [hDae] with s hs hsD
    exact (indicator_of_mem (mem_safeU_of_mem_avoidSet hweak φ (mem_univ s) (hs hsD).2) _).symm
  rw [hRHS, setIntegral_map_cond hMm hY hDm hfm.aestronglyMeasurable,
    setIntegral_map_cond hMm hY hDm hgm.aestronglyMeasurable]
  congr 1
  have hE : MeasurableSet[𝓗 q] (M ∩ Y ⁻¹' D) :=
    (𝓗.mono (zero_le : (0 : ℝ≥0) ≤ q) _ hM).inter (measurable_retImageFiltration Y 𝓗 q hD)
  have hp := ae_imp_of_ae_cond hMm (ae_of_ae_map hY.aemeasurable hDae)
  have hcond : ∀ᵐ ω ∂P, ω ∈ M ∩ Y ⁻¹' D → ω ∈ M ∧ ω ∈ avoidSet W V φ q := by
    filter_upwards [hp] with ω hω hωE
    exact ⟨hωE.1, (hav ω φ q).1 (hω hωE.1 hωE.2).2⟩
  have key := hS φ q (M ∩ Y ⁻¹' D) hE hcond
  have hr : ∫ ω in M ∩ Y ⁻¹' D,
      cfAt κ W (bheProc κ ρL ρR W (geomLW W xL) (geomRW W xR)) φ 1 (fun _ => q) ω ∂P =
      ∫ ω in M ∩ Y ⁻¹' D, g' (Y ω) ∂P := by
    apply setIntegral_congr_ae (hMm.inter (hY hDm))
    filter_upwards [hcond] with ω hω hωE
    have hmem := mem_safeU_of_mem_avoidSet hweak φ (mem_univ (Y ω)) ((hav ω φ q).2 (hω hωE).2)
    rw [show g' (Y ω) = _ from indicator_of_mem hmem _]
    exact (cfAt_congr (hWY ω) (hLY ω) (hRY ω) κ φ q).symm
  simpa only [hXY] using key.trans hr

end InteractingSLE.Restart.RetAux79
