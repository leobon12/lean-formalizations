import InteractingSLE.Spec.Sec2.T24BrV2

/-!
# Theorem 2.4, forward implication for candidate v2

Normalize the driver on a measurable null set and take its canonical geometric
force coordinates. Their threshold is measurable and is a curve stopping time.
Measurable modification transports the given evolution to these versions, and
the regular-coordinate forward theorem applies. Strict localization then passes
back to the original coordinates and lifetime on their common conull event.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec2.T24Bridge.V2

open MartChar Sec7.PocketTraversal

/-- **Theorem 2.4, forward implication**, with v2's a.s. geometric images and strict localization. -/
theorem forward24 {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'} {π : Ω' → Ω}
    {𝓕' : Filtration ℝ≥0 mΩ'} {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω' → ℝ} {η : ℝ≥0 → Ω → ℂ}
    (hη : ∀ t, StronglyMeasurable (η t)) (hW : ∀ t, Measurable (W t))
    (hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω))
    (hV : ∀ᵐ ω ∂P, (∀ i, IsLeftForceImage (W · ω) (xL i) (VL i · ω)) ∧
      ∀ j, IsRightForceImage (W · ω) (xR j) (VR j · ω))
    (hπ : MeasurePreserving π Q P)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR Q 𝓕' (fun t ω => W t (π ω))
      (fun i t ω => VL i t (π ω)) (fun i t ω => VR i t (π ω)) B
      (fun ω => continuationThreshold ρL ρR (W · (π ω))
        (fun i t => VL i t (π ω)) (fun i t => VR i t (π ω))))
    (U : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω t, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω))
      (forceJumpSet (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)) (U ω t))
    {z : ℂ} (hz : 0 < z.im) :
    IsContLocalMartingaleBeforeV2 (usualAugmentation (Filtration.natural η hη) P) P
      (fun ω => (min (QuantumZipper.swallowTime (Ito.rpath (W · ω)) z)
        (continuationThreshold ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω)) : ℝ≥0∞))
      (fun t ω => couplingMean κ (Ito.rpath (W · ω)) t (U ω t) z) := by
  let 𝓖 := usualAugmentation (Filtration.natural η hη) P
  have hgood := hgen.and hV
  obtain ⟨G, hGm, hG0, hGp⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧
      ∀ ω ∈ G, (Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω)) ∧
        (∀ i, IsLeftForceImage (W · ω) (xL i) (VL i · ω)) ∧
          ∀ j, IsRightForceImage (W · ω) (xR j) (VR j · ω) := by
    refine ⟨(toMeasurable P {ω | ¬ ((Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω)) ∧
      (∀ i, IsLeftForceImage (W · ω) (xL i) (VL i · ω)) ∧
        ∀ j, IsRightForceImage (W · ω) (xR j) (VR j · ω))})ᶜ,
      (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
    · rw [compl_compl, measure_toMeasurable]
      exact ae_iff.1 hgood
    · intro ω hω
      by_contra hh
      exact hω (subset_toMeasurable _ _ hh)
  have hGa : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hG0
  have hG : MeasurableSet[𝓖 0] G := by
    simpa only [compl_compl] using
      (Ito.measurableSet_usualAugmentation_of_null (𝓕 := Filtration.natural η hη) hGm.compl hG0 0).compl
  have hGt (t : ℝ≥0) : MeasurableSet[𝓖 t] G := 𝓖.mono zero_le _ hG
  let Wc : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then W t ω else 0
  have hWceq (ω : Ω) (hω : ω ∈ G) (t : ℝ≥0) : Wc t ω = W t ω := by simp only [Wc, hω, ↓reduceIte]
  have hWcc : ∀ ω, Continuous (Wc · ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [Wc, hω, ↓reduceIte] using (hGp ω hω).1.1
    · simp only [Wc, hω, ↓reduceIte]
      exact continuous_const
  have hWc0 : ∀ ω, Wc 0 ω = 0 := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [hWceq ω hω]
      exact Sec7.SideHeight.w_zero_of_isGeneratingTrace (hGp ω hω).1.2 ENNReal.zero_lt_top
    · simp only [Wc, hω, ↓reduceIte]
  have hWa := stronglyAdapted_driver_curveFiltration hη hW hgen
  have hWca : StronglyAdapted 𝓖 Wc := fun t =>
    ((hWa t).measurable.ite (hGt t) measurable_const).stronglyMeasurable
  let L := geomLW Wc (fun _ : Ω => xL)
  let R := geomRW Wc (fun _ : Ω => xR)
  have hLa : ∀ i, StronglyAdapted 𝓖 (L i) := stronglyAdapted_geomLW hWca hWcc measurable_const
  have hRa : ∀ i, StronglyAdapted 𝓖 (R i) := stronglyAdapted_geomRW hWca hWcc measurable_const
  have hLc : ∀ i ω, Continuous (L i · ω) := fun i ω => (isForcePath_geomLW hWcc (fun _ => xL) ω i).1
  have hRc : ∀ i ω, Continuous (R i · ω) := fun i ω => (isForcePath_geomRW hWcc (fun _ => xR) ω i).1
  have hL0 : ∀ i ω, L i 0 ω = xL i := fun i ω => geomLW_zero hWcc hWc0 (hF.2.1 i)
  have hR0 : ∀ i ω, R i 0 ω = xR i := fun i ω => geomRW_zero hWcc hWc0 (hF.2.2.2 i)
  have hLeq (ω : Ω) (hω : ω ∈ G) (i : Fin nL) (t : ℝ≥0) : L i t ω = VL i t ω := by
    have hh := left_eq_geom ((hGp ω hω).2.1 i) t
    unfold geomLW Bessel.realPath at hh
    unfold L geomLW Bessel.realPath
    simpa only [Wc, hω, ↓reduceIte] using hh.symm
  have hReq (ω : Ω) (hω : ω ∈ G) (i : Fin nR) (t : ℝ≥0) : R i t ω = VR i t ω := by
    have hh := right_eq_geom ((hGp ω hω).2.2 i) t
    unfold geomRW Bessel.realPath at hh
    unfold R geomRW Bessel.realPath
    simpa only [Wc, hω, ↓reduceIte] using hh.symm
  let ζ : Ω → ℝ≥0∞ := fun ω => thresholdTime ρL ρR (Wc · ω) (fun i t => L i t ω) (fun i t => R i t ω)
  have hζ : IsStoppingTime 𝓖 ζ := fun t => measurableSet_thresholdTime_le hWcc hLc hRc hWca hLa hRa
    (geomLW_merge hWcc (fun _ => xL)) (geomRW_merge hWcc (fun _ => xR)) t
  have hζeq (ω : Ω) (hω : ω ∈ G) : ζ ω =
      continuationThreshold ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) := by
    rw [continuationThreshold_eq_thresholdTime]
    unfold ζ
    congr 1
    · exact funext (hWceq ω hω)
    · exact funext fun i => funext (hLeq ω hω i)
    · exact funext fun i => funext (hReq ω hω i)
  have hE' := isIntegratedSLEEvolution_congr_ae_usualAugmentation hE
    (fun t => ((hWca t).mono (𝓖.le t)).measurable.comp hπ.measurable)
    (fun i t => ((hLa i t).mono (𝓖.le t)).measurable.comp hπ.measurable)
    (fun i t => ((hRa i t).mono (𝓖.le t)).measurable.comp hπ.measurable)
    (hζ.measurable'.comp hπ.measurable)
    ((hπ.quasiMeasurePreserving.ae hGa).mono fun ω hω =>
      ⟨hζeq (π ω) hω, hWceq (π ω) hω, hLeq (π ω) hω, hReq (π ω) hω⟩)
  let Uc : Ω → ℝ≥0 → ℂ → ℝ := fun ω t => if ω ∈ G then U ω t else
    meanExt κ ρL ρR (Wc t ω) (fun i => L i t ω) (fun i => R i t ω)
  have hUc : ∀ ω t, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => L i t ω - Wc t ω) (fun i => R i t ω - Wc t ω))
      (forceJumpSet (fun i => L i t ω - Wc t ω) (fun i => R i t ω - Wc t ω)) (Uc ω t) := by
    intro ω t
    by_cases hω : ω ∈ G
    · simpa only [Uc, hω, ↓reduceIte, hWceq ω hω, hLeq ω hω, hReq ω hω] using hu ω t
    · simpa only [Uc, hω, ↓reduceIte] using
        isBoundedHarmonicExtension_meanExt κ ρL ρR (Wc t ω) (fun i => L i t ω) (fun i => R i t ω)
  have hcg : ∀ᵐ ω ∂P, Continuous (Wc · ω) ∧ IsGeneratingTrace (Wc · ω) ⊤ (η · ω) := by
    filter_upwards [hGa] with ω hω
    have hew : (Wc · ω) = (W · ω) := funext (hWceq ω hω)
    exact ⟨hWcc ω, hew ▸ (hGp ω hω).1.2⟩
  have hc : IsContLocalMartingaleBeforeV2 𝓖 P
      (fun ω => (min (QuantumZipper.swallowTime (Ito.rpath (Wc · ω)) z) (ζ ω) : ℝ≥0∞))
      (fun t ω => couplingMean κ (Ito.rpath (Wc · ω)) t (Uc ω t) z) := by
    by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
    · have hζ0 : ∀ ω, ζ ω = 0 := by
        intro ω
        rw [show ζ ω = continuationThreshold ρL ρR (Wc · ω)
          (fun i t => L i t ω) (fun i t => R i t ω) from (continuationThreshold_eq_thresholdTime _ _ _ _ _).symm]
        apply le_antisymm _ bot_le
        unfold continuationThreshold
        apply iInf_le_of_le 0
        have hh : ForceWord.ThresholdCondition ρL ρR (Wc 0 ω) (fun i => L i 0 ω) (fun i => R i 0 ω) := by
          simpa only [hWc0, hL0, hR0] using hseed
        exact iInf_le_of_le hh le_rfl
      have hmin (ω : Ω) : min (QuantumZipper.swallowTime (Ito.rpath (Wc · ω)) z) (ζ ω) = 0 := by
        rw [hζ0]
        exact min_eq_right zero_le
      have heζ : (fun ω => ((min (QuantumZipper.swallowTime (Ito.rpath (Wc · ω)) z) (ζ ω) : ℝ≥0∞) :
          WithTop ℝ≥0)) = fun _ : Ω => (0 : WithTop ℝ≥0) := by
        funext ω
        rw [hmin]
        rfl
      rw [heζ]
      exact isContLocalMartingaleBeforeV2_zero (𝓕 := 𝓖) (P := P)
        (fun t ω => couplingMean κ (Ito.rpath (Wc · ω)) t (Uc ω t) z)
    · exact isContLocalMartingaleBeforeV2_of_evolution_regular hκ hη hπ hcg hE'
        hWcc hLc hRc hWca hLa hRa hWc0 hL0 hR0
        (geomLW_le hWcc (fun _ => xL)) (le_geomRW hWcc (fun _ => xR)) hζ hseed Uc hUc hz
  apply isContLocalMartingaleBeforeV2_of_ae_eq (𝓕 := Filtration.natural η hη) _ hc
  filter_upwards [hGa] with ω hω
  have hew : (Wc · ω) = (W · ω) := funext (hWceq ω hω)
  refine ⟨?_, fun t _ => ?_⟩
  · rw [hew, hζeq ω hω]
  · simp only [hew, Uc, hω, ↓reduceIte]

end InteractingSLE.Sec2.T24Bridge.V2
