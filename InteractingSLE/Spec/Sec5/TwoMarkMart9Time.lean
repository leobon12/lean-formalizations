/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkMart9First

/-!
# Local retargeting observable martingales in inverse-clock time

Compact containment gives bounded continuous stopped observables. The existing
bounded optional-time theorem reads their source martingales in the actual
inverse-clock filtration, whose image stops announce the image lifetime.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Mart9

open Zhan.Retarget

variable {Ω : Type*} {κ a b : ℝ} {xL ρL : Fin 0 → ℝ} {ρR : Fin 2 → ℝ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
  {e : Ω → ℝ≥0∞} {S : ℕ → Ω → ℝ≥0} {G : Set Ω}

/-- The stopped coordinate process lies in the ordered compact box, including off the good event. -/
theorem stoppedCoords_mem_orderedBox (ha : 0 < a) (hab : a < b)
    (hgood : ∀ ω ∈ G, IsGood κ a b xL ρL ρR W B VL VR e S ω)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    Adapt8.stoppedCoords xL ![a, b] a 0 G W B VL VR (rLoc 0 G S W VL VR B e n) t ω ∈
      orderedBox κ xL ρL ρR a b n := by
  by_cases hω : ω ∈ G
  · simpa only [Adapt8.stoppedCoords, rCoord, hω, ↓reduceIte] using
      mem_orderedBox ha hab hgood hω (min_le_right t (rLoc 0 G S W VL VR B e n ω))
  · simp only [Adapt8.stoppedCoords, rCoord, hω, ↓reduceIte]
    exact ⟨Or.inl rfl, hab.le⟩

/-- A continuous observable is uniformly bounded on each stopped coordinate process. -/
theorem exists_bound_stopped_observable (ha : 0 < a) (hab : a < b)
    (hgood : ∀ ω ∈ G, IsGood κ a b xL ρL ρR W B VL VR e S ω)
    {F : RCoord 0 2 × ℝ → ℝ} (hF : ContinuousOn F (obsRegion κ xL ![a, b] ρL ρR 0)) (n : ℕ) :
    ∃ C, ∀ t ω, |F (Adapt8.stoppedCoords xL ![a, b] a 0 G W B VL VR
      (rLoc 0 G S W VL VR B e n) t ω)| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_orderedBox (κ := κ) (xL := xL) (ρL := ρL) (ρR := ρR)
    (a := a) (b := b) n).exists_bound_of_continuousOn
      (hF.mono fun _ hp => rKc_subset_obsRegion κ xL ![a, b] ρL ρR 0 a
        (initial_mem_region ha hab) n hp.1)
  exact ⟨C, fun t ω => by
    simpa only [Real.norm_eq_abs] using hC _ (stoppedCoords_mem_orderedBox ha hab hgood n t ω)⟩

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- Localizing both space and Brownian amplitude gives announced inverse-time observable martingales. -/
theorem exists_announced_image_observables {A : ℕ → Ω → ℝ≥0}
    (ha : 0 < a) (hab : a < b)
    (hE : Sec2.IsSLEEvolutionUpTo κ xL ![a, b] ρL ρR P 𝓕 W VL VR B e)
    (hA : Coupling.IsAnnouncingSeq 𝓕 P e A) :
    ∃ (G : Set Ω) (S : ℕ → Ω → ℝ≥0) (𝓘 : Filtration ℝ≥0 mΩ) (τ : Ω → ℝ≥0∞),
      MeasurableSet G ∧ P Gᶜ = 0 ∧
      (∀ ω ∈ G, IsGood κ a b xL ρL ρR W B VL VR e S ω) ∧
      Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P
        (fun ω => sepTime (W · ω) (VR 0 · ω) (e ω)) S ∧
      (∀ᵐ ω ∂P, τ ω = newHorizon a (W · ω) (VR 0 · ω)
        (sepTime (W · ω) (VR 0 · ω) (e ω))) ∧
      Coupling.IsAnnouncingSeq 𝓘 P τ
        (Clock7.imageStop (a := a) (G := G) (W := W) (V := VR 0)
          (A := rLoc 0 G S W VL VR B e)) ∧
      AdaptedBefore 𝓘 τ (fun u ω =>
        newW (j := 0) (m := 1) ![a, b] (W · ω) (fun i t => VR i t ω) u) ∧
      (∀ i, AdaptedBefore 𝓘 τ (fun u ω =>
        newVL (j := 0) (m := 1) ![a, b] (W · ω)
          (fun i t => VL i t ω) (fun i t => VR i t ω) i u)) ∧
      AdaptedBefore 𝓘 τ (fun u ω =>
        newB (j := 0) (m := 1) κ xL ![a, b] ρL ρR (W · ω)
          (fun i t => VL i t ω) (fun i t => VR i t ω) u) ∧
      ∀ F : RCoord 0 2 × ℝ → ℝ,
        ContDiffOn ℝ 3 F (obsRegion κ xL ![a, b] ρL ρR 0) →
        (∀ p ∈ obsRegion κ xL ![a, b] ρL ρR 0,
          (∀ i, p.1.1 i ≠ drv κ xL ![a, b] ρL ρR p) →
          (∀ i, p.1.2.1 i ≠ drv κ xL ![a, b] ρL ρR p) →
            Ito.itoGen F p (dens κ xL ![a, b] ρL ρR 0 p) = 0) →
        ∀ n, Martingale (fun u ω => F
          (Adapt8.stoppedCoords xL ![a, b] a 0 G W B VL VR (rLoc 0 G S W VL VR B e n)
            (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0))
              (Clock7.inverseTime G a W (VR 0)
                (fun ω => sepTime (W · ω) (VR 0 · ω) (e ω)) u) ω) ω)) 𝓘 P := by
  have := hE.brownian.isProbabilityMeasure'
  obtain ⟨S, hS⟩ := Version6.exists_isAnnouncingSeq_sepTime hE hA (k := 0) ha
  obtain ⟨G, hGm, hGc, hgood⟩ := exists_good hE hS
  let R := rLoc 0 G S W VL VR B e
  let U := fun ω => sepTime (W · ω) (VR 0 · ω) (e ω)
  let 𝓖 := usualAugmentation 𝓕 P
  have hG0 : MeasurableSet[𝓖 0] G := by
    simpa only [compl_compl] using
      (Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hGm.compl hGc 0).compl
  have hR := isAnnouncingSeq_localizer ha hab hE hGm hGc hgood hS
  have hs : ∀ ω ∈ G, SepUpTo (W · ω) (VR 0 · ω) (U ω) :=
    fun ω hω => ((hgood ω hω).data ha hab).sep
  have hb : ∀ ω ∈ G, ∀ n, (R n ω : ℝ≥0∞) < U ω := fun ω hω => (hgood ω hω).loc_lt
  have hc : ∀ ω ∈ G, ∀ s : ℝ≥0, (s : ℝ≥0∞) < U ω → ∃ n, s ≤ R n ω := by
    intro ω hω s hsu
    obtain ⟨n, hn⟩ := exists_forall_le_localizer ha hab hgood (hgood ω hω) hω (hS.2.1 ω) hsu
    exact ⟨n, hn n le_rfl⟩
  have hreg := stopped_coords_regular ha hab hE hGm hGc hgood hS.1
  have hm : ∀ n r, Measurable[𝓖 r] fun ω => if ω ∈ G then
      clk (rate a (W · ω) (VR 0 · ω)) (min r (R n ω)) else 0 := by
    intro n r
    convert ((hreg n).1 r).fst.snd.snd.snd.snd using 1
    funext ω
    by_cases hω : ω ∈ G <;>
      simp only [Adapt8.stoppedCoords, rCoord, rCoordAt, hω, ↓reduceIte, NNReal.coe_min, R]
  let 𝓘 := Clock7.imageFiltration ha hG0 hR.1 hs hb hc hm
  let τ : Ω → ℝ≥0∞ := fun ω => if ω ∈ G then newHorizon a (W · ω) (VR 0 · ω) (U ω) else 0
  have hGa : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hGc
  have hinv : ∀ ω ∈ G, ∀ u : ℝ≥0, (u : ℝ≥0∞) < newHorizon a (W · ω) (VR 0 · ω) (U ω) →
      0 ≤ invClk (rate a (W · ω) (VR 0 · ω)) u ∧
      (((invClk (rate a (W · ω) (VR 0 · ω)) u).toNNReal : ℝ≥0) : ℝ≥0∞) < e ω := by
    intro ω hω u hu
    obtain ⟨s, -, -, -, hmem, -⟩ := newTime_spec (hs ω hω) ha hu
    exact ⟨hmem.1, (invClk_lt (hs ω hω) ha hu).trans_le (sepTime_le _ _ _)⟩
  refine ⟨G, S, 𝓘, τ, hGm, hGc, hgood, hS, ?_,
    Clock7.isAnnouncingSeq_imageStop ha hG0 hR.1 hs hb hc hm hGa hR.2.1, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hGa] with ω hω
    simp only [τ, U, hω, ↓reduceIte]
  · refine Adapt8.adaptedBefore_of_coords ha hG0 hR.1 hs hb hc hm
      (fun n => (hreg n).1) (fun n => (hreg n).2)
      (measurable_phiW (j := 0) (m := 1) κ xL ![a, b] ρL ρR) ?_
    intro ω hω u hu
    exact newW_eq_phiW (hgood ω hω).path (hinv ω hω u hu).1 (hinv ω hω u hu).2
  · intro i
    refine Adapt8.adaptedBefore_of_coords ha hG0 hR.1 hs hb hc hm
      (fun n => (hreg n).1) (fun n => (hreg n).2)
      (measurable_phiVL (nL := 0) (j := 0) (m := 1) i) ?_
    intro ω hω u hu
    exact newVL_eq_phiVL (j := 0) (m := 1) (xR := ![a, b]) (w := (W · ω))
      (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) (b := (B · ω))
      (hinv ω hω u hu).1 i
  · refine Adapt8.adaptedBefore_of_coords ha hG0 hR.1 hs hb hc hm
      (fun n => (hreg n).1) (fun n => (hreg n).2)
      (Adapt8.measurable_phiNoise (j := 0) (m := 1) κ xL ![a, b] ρL ρR) ?_
    intro ω hω u hu
    exact Adapt8.newB_eq_phiNoise (hgood ω hω).path (hinv ω hω u hu).1 (hinv ω hω u hu).2
  · intro F hF hgen n
    have hM := martingale_observable_stopped ha hab hE hGm hGc hgood hS.1 hF hgen n
    obtain ⟨C, hC⟩ := exists_bound_stopped_observable ha hab hgood hF.continuousOn n
    have hcont : ∀ ω, Continuous fun t => F
        (Adapt8.stoppedCoords xL ![a, b] a 0 G W B VL VR (R n) t ω) := fun ω =>
      hF.continuousOn.comp_continuous ((hreg n).2 ω) fun t =>
        rKc_subset_obsRegion κ xL ![a, b] ρL ρR 0 a (initial_mem_region ha hab) n
          (stoppedCoords_mem_orderedBox ha hab hgood n t ω).1
    have hMT := martingale_comp_timeChange
      (Clock7.isStoppingTime_inverseTime ha hG0 hR.1 hs hb hc hm)
      (Clock7.inverseTime_mono ha hs) hM hcont hC (n : ℝ≥0) 1 0
    simpa only [one_mul, add_zero, Adapt8.stoppedCoords, Sec2.TwoSeed.brownG,
      𝓘, Clock7.imageFiltration, U] using hMT

end InteractingSLE.Sec5.TwoMark.Mart9
