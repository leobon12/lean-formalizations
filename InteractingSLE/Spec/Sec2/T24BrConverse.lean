import InteractingSLE.Spec.Sec2.T24BrDefs
import InteractingSLE.Spec.Sec2.T24BrAdapted
import InteractingSLE.Spec.Sec2.T24BrImage
import InteractingSLE.Spec.Sec2.T24BrPullback
import InteractingSLE.Spec.Restart.ConverseBefore

/-!
# Theorem 2.4: the converse on the candidate's probability-space extension

Restrict first to a measurable conull set of genuine generating paths, pull back the
martingale hypothesis, and apply the landed before-threshold converse with independent noise.
The original driver and force-image formulas are retained exactly on the extension.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec2.T24Bridge

open Sec7.PocketTraversal

/-- Identification of the candidate's threshold with the landed threshold from its coordinates. -/
theorem geomContinuationThreshold_eq_thresholdTime {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    (hL : ∀ i t, leftForceImage w (xL i) t = vL i t)
    (hR : ∀ j t, rightForceImage w (xR j) t = vR j t) :
    geomContinuationThreshold xL xR ρL ρR w = MartChar.thresholdTime ρL ρR w vL vR := by
  classical
  unfold geomContinuationThreshold MartChar.thresholdTime
  simp only [hL, hR]
  split_ifs with h
  · rw [ENNReal.coe_sInf h]
    rfl
  · rw [Set.not_nonempty_iff_eq_empty] at h
    refine iInf_eq_top.2 fun t => iInf_eq_top.2 fun ht => ?_
    have hm : t ∈ MartChar.thresholdSet ρL ρR w vL vR := ht
    rw [h] at hm
    exact absurd hm (Set.notMem_empty t)

/-- **Theorem 2.4, converse**, with the candidate's formulas and its a.s. path hypotheses. -/
theorem converse24 {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {η : ℝ≥0 → Ω → ℂ}
    (hη : ∀ t, StronglyMeasurable (η t)) {W : ℝ≥0 → Ω → ℝ}
    (hW : ∀ t, Measurable (W t))
    (hηW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω) ∧
      (∀ t, η t ω ∈ closure QuantumZipper.H) ∧ Tendsto (fun t => ‖η t ω‖) atTop atTop)
    (hmart : ∀ U : Ω → ℝ≥0 → ℂ → ℝ,
      (∀ ω t, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR (fun i => leftForceImage (W · ω) (xL i) t - W t ω)
          (fun j => rightForceImage (W · ω) (xR j) t - W t ω))
        (forceJumpSet (fun i => leftForceImage (W · ω) (xL i) t - W t ω)
          (fun j => rightForceImage (W · ω) (xR j) t - W t ω)) (U ω t)) →
      ∀ z ∈ QuantumZipper.H, IsContLocalMartingaleBefore
        (usualAugmentation (Filtration.natural η hη) P) P
        (fun ω => min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
          (geomContinuationThreshold xL xR ρL ρR (W · ω)))
        (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (U ω t) z)) :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω),
      MeasurePreserving π P' P ∧
      ∃ (𝓕' : Filtration ℝ≥0 mΩ') (B : ℝ≥0 → Ω' → ℝ),
        IsIntegratedSLEEvolution κ xL xR ρL ρR P' 𝓕' (fun t ω => W t (π ω))
          (fun i t ω => leftForceImage (fun s => W s (π ω)) (xL i) t)
          (fun j t ω => rightForceImage (fun s => W s (π ω)) (xR j) t) B
          (fun ω => geomContinuationThreshold xL xR ρL ρR (fun s => W s (π ω))) := by
  classical
  let 𝓖 := usualAugmentation (Filtration.natural η hη) P
  have hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω) :=
    hηW.mono fun _ h => ⟨h.1, h.2.1⟩
  have hWa := stronglyAdapted_driver_curveFiltration hη hW hgen
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgen)
  let G : Set Ω := Nᶜ
  have hGm : MeasurableSet G := hNm.compl
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    simpa only [G, mem_compl_iff] using measure_eq_zero_iff_ae_notMem.1 hN0
  have hgood : ∀ ω : G, Continuous (W · (ω : Ω)) ∧
      IsGeneratingTrace (W · (ω : Ω)) ⊤ (η · (ω : Ω)) := by
    intro ω
    by_contra hb
    exact ω.2 (hNsub hb)
  let Q : Measure G := P.comap ((↑) : G → Ω)
  have hπ : MeasurePreserving ((↑) : G → Ω) Q P := measurePreserving_conull_subtype hGm hGae
  have : IsProbabilityMeasure (Q.map ((↑) : G → Ω)) := hπ.map_eq.symm ▸ inferInstance
  have : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_of_map hπ.measurable.aemeasurable
  let 𝓖g := pullbackFiltration 𝓖 ((↑) : G → Ω) hπ.measurable
  let Wg : ℝ≥0 → G → ℝ := fun t ω => W t ω
  have hWgc : ∀ ω, Continuous (Wg · ω) := fun ω => (hgood ω).1
  have hWg0 : ∀ ω, Wg 0 ω = 0 := fun ω =>
    Sec7.SideHeight.w_zero_of_isGeneratingTrace (hgood ω).2 ENNReal.zero_lt_top
  have hWga : StronglyAdapted 𝓖g Wg := fun t =>
    (hWa t).comp_measurable (measurable_iff_comap_le.2 le_rfl)
  have hL : ∀ (ω : G) i t, leftForceImage (W · (ω : Ω)) (xL i) t =
      geomLW Wg (fun _ => xL) i t ω := fun ω i t =>
    left_force_image_eq_geomLW (xL := fun _ : G => xL)
      (hWgc ω) (hWg0 ω) i (hF.2.1 i) t
  have hR : ∀ (ω : G) j t, rightForceImage (W · (ω : Ω)) (xR j) t =
      geomRW Wg (fun _ => xR) j t ω := fun ω j t =>
    right_force_image_eq_geomRW (xR := fun _ : G => xR)
      (hWgc ω) (hWg0 ω) j (hF.2.2.2 j) t
  have hT : ∀ ω : G, geomContinuationThreshold xL xR ρL ρR (W · (ω : Ω)) =
      MartChar.thresholdTime ρL ρR (Wg · ω)
        (fun i t => geomLW Wg (fun _ => xL) i t ω)
        (fun j t => geomRW Wg (fun _ => xR) j t ω) := fun ω =>
    geomContinuationThreshold_eq_thresholdTime (hL ω) (hR ω)
  have hVLa := fun i => stronglyAdapted_geomLW hWga hWgc
    (measurable_const : Measurable[𝓖g 0] (fun _ : G => xL)) i
  have hVRa := fun j => stronglyAdapted_geomRW hWga hWgc
    (measurable_const : Measurable[𝓖g 0] (fun _ : G => xR)) j
  have hTst : IsStoppingTime 𝓖g (fun ω => MartChar.thresholdTime ρL ρR (Wg · ω)
      (fun i t => geomLW Wg (fun _ => xL) i t ω)
      (fun j t => geomRW Wg (fun _ => xR) j t ω)) := fun t =>
    MartChar.measurableSet_thresholdTime_le hWgc
      (fun i ω => (isForcePath_geomLW hWgc _ ω i).1)
      (fun j ω => (isForcePath_geomRW hWgc _ ω j).1) hWga hVLa hVRa
      (fun ω i j s t hst he => geomLW_merge hWgc _ ω i j s t hst he)
      (fun ω i j s t hst he => geomRW_merge hWgc _ ω i j s t hst he) t
  have hm : ∀ z ∈ QuantumZipper.H, MartChar.IsLocalMartingaleBefore 𝓖g Q
      (fun ω => min (QuantumZipper.swallowTime (MartChar.wpath Wg ω) z)
        (MartChar.thresholdTime ρL ρR (Wg · ω)
          (fun i t => geomLW Wg (fun _ => xL) i t ω)
          (fun j t => geomRW Wg (fun _ => xR) j t ω)))
      (MartChar.coupProc κ ρL ρR Wg (geomLW Wg (fun _ => xL))
        (geomRW Wg (fun _ => xR)) z) := by
    intro z hz
    have h := (hmart (fun ω t => MartChar.meanExt κ ρL ρR (W t ω)
      (fun i => leftForceImage (W · ω) (xL i) t)
      (fun j => rightForceImage (W · ω) (xR j) t))
      (fun ω t => MartChar.isBoundedHarmonicExtension_meanExt _ _ _ _ _ _) z hz).2
    have hp := isLocalMartingaleBefore_pullback hπ (MeasurableEmbedding.subtype_coe hGm) h
    change MartChar.IsLocalMartingaleBefore 𝓖g Q
      (fun ω => min (QuantumZipper.swallowTime (MartChar.wpath Wg ω) z)
        (geomContinuationThreshold xL xR ρL ρR (W · (ω : Ω))))
      (fun t ω => couplingMean κ (MartChar.wpath Wg ω) t
        (MartChar.meanExt κ ρL ρR (W t ω)
          (fun i => leftForceImage (W · (ω : Ω)) (xL i) t)
          (fun j => rightForceImage (W · (ω : Ω)) (xR j) t)) z) at hp
    unfold MartChar.coupProc
    simpa only [hT, hL, hR, Wg] using hp
  obtain ⟨P₀, hP₀, 𝓦, B, hE, -, -⟩ := Restart.ConverseBefore.isRandomWordEvolution_prod
    (𝒢 := ⊥) (F := Set.univ) hκ bot_le MeasurableSet.univ measurable_const measurable_const
    (fun _ => hF.2.1) (fun _ => hF.2.2.2) (fun _ => hF.1) (fun _ => hF.2.2.1)
    hWg0 hWgc hWga hTst hm (ae_of_all _ fun _ _ => le_rfl)
  obtain ⟨-, -, -, -, hB, hWb, hVLb, hVRb, hpath⟩ := hE
  refine ⟨G × (ℕ → ℝ), inferInstance, Q.prod P₀, fun p => (p.1 : Ω),
    hπ.comp measurePreserving_fst, WholeField.prodFiltration 𝓖g 𝓦, B, ?_⟩
  simp only [hL, hR, hT]
  exact ⟨hB, hWb, hVLb, hVRb,
    hpath.mono fun p hp => hp (mem_preimage.2 (mem_univ _))⟩

end InteractingSLE.Sec2.T24Bridge
