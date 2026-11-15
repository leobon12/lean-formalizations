/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkAdapt8Noise

/-!
# Adapted canonical first-mark image processes for an announced local evolution

The inverse-clock filtration, announced image lifetime, canonical driver, force
marks and canonical noise are constructed without additional adaptedness inputs.
The Brownian law of the image noise is a separate obligation.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Adapt8

open Zhan.Retarget

/-- An announced local two-mark evolution has adapted canonical first-target image coordinates. -/
theorem exists_announced_adapted_first {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ a b : ℝ}
    {xL ρL : Fin 0 → ℝ} {ρR : Fin 2 → ℝ} {W B : ℝ≥0 → Ω → ℝ}
    {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
    {e : Ω → ℝ≥0∞} {A : ℕ → Ω → ℝ≥0} (ha : 0 < a) (hab : a < b)
    (hE : Sec2.IsSLEEvolutionUpTo κ xL ![a, b] ρL ρR P 𝓕 W VL VR B e)
    (hA : Coupling.IsAnnouncingSeq 𝓕 P e A) :
    ∃ (𝓘 : Filtration ℝ≥0 mΩ) (τ : Ω → ℝ≥0∞) (Q : ℕ → Ω → ℝ≥0),
      (∀ᵐ ω ∂P, τ ω = newHorizon a (W · ω) (VR 0 · ω)
        (sepTime (W · ω) (VR 0 · ω) (e ω))) ∧
      Coupling.IsAnnouncingSeq 𝓘 P τ Q ∧
      AdaptedBefore 𝓘 τ (fun u ω =>
        newW (j := 0) (m := 1) ![a, b] (W · ω) (fun i t => VR i t ω) u) ∧
      (∀ i, AdaptedBefore 𝓘 τ (fun u ω =>
        newVL (j := 0) (m := 1) ![a, b] (W · ω)
          (fun i t => VL i t ω) (fun i t => VR i t ω) i u)) ∧
      AdaptedBefore 𝓘 τ (fun u ω =>
        newB (j := 0) (m := 1) κ xL ![a, b] ρL ρR (W · ω)
          (fun i t => VL i t ω) (fun i t => VR i t ω) u) := by
  classical
  let U := fun ω => sepTime (W · ω) (VR 0 · ω) (e ω)
  let 𝓖 := usualAugmentation 𝓕 P
  have hEu : Sec2.IsSLEEvolutionUpTo κ xL ![a, b] ρL ρR P 𝓖 W VL VR B e :=
    ⟨Ito.isFilteredBrownianReal_usualAugmentation hE.brownian,
      Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) hE.adapted_W,
      fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) (hE.adapted_VL i),
      fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) (hE.adapted_VR i), hE.ae_path⟩
  obtain ⟨S, hS⟩ := Version6.exists_isAnnouncingSeq_sepTime hE hA (k := 0) ha
  have hgoodae : ∀ᵐ ω ∂P,
      Sec2.IsSLEPathUpTo κ xL ![a, b] ρL ρR (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (B · ω) (e ω) ∧ Continuous (B · ω) ∧
      (∀ n, (S n ω : ℝ≥0∞) < U ω) ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) < U ω → ∃ n, s ≤ S n ω) :=
    hE.ae_path.and (hE.brownian.1.cont.and ((ae_all_iff.2 hS.2.2.1).and hS.2.2.2))
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgoodae)
  let G := Nᶜ
  have hG : MeasurableSet[𝓖 0] G :=
    (Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hNm hN0 0).compl
  have hGa : ∀ᵐ ω ∂P, ω ∈ G := measure_eq_zero_iff_ae_notMem.1 hN0
  have hgood : ∀ ω ∈ G,
      Sec2.IsSLEPathUpTo κ xL ![a, b] ρL ρR (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (B · ω) (e ω) ∧ Continuous (B · ω) ∧
      (∀ n, (S n ω : ℝ≥0∞) < U ω) ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) < U ω → ∃ n, s ≤ S n ω) := by
    intro ω hω
    by_contra hn
    exact hω (hNsub hn)
  have hs : ∀ ω ∈ G, SepUpTo (W · ω) (VR 0 · ω) (U ω) := by
    intro ω hω
    exact (Local2.retargetData_first ha hab ((hgood ω hω).1.mono (sepTime_le _ _ _))
      (fun _ ht => lt_of_lt_sepTime ht)).sep
  have hb : ∀ ω ∈ G, ∀ n, (S n ω : ℝ≥0∞) < U ω := fun ω hω => (hgood ω hω).2.2.1
  have hc : ∀ ω ∈ G, ∀ s : ℝ≥0, (s : ℝ≥0∞) < U ω → ∃ n, s ≤ S n ω :=
    fun ω hω => (hgood ω hω).2.2.2
  have hreg := fun n => stopped_coords_regular ha hEu hG (fun ω hω => (hgood ω hω).1)
    (fun ω hω => (hgood ω hω).2.1) (hS.1 n) (fun ω hω => hb ω hω n)
    (fun _ => sepTime_le _ _ _) hs
  have hm : ∀ n r, Measurable[𝓖 r] fun ω =>
      @ite ℝ (ω ∈ G) (Classical.propDecidable _)
        (clk (rate a (W · ω) (VR 0 · ω)) (min r (S n ω))) 0 := by
    intro n r
    convert ((hreg n).1 r).fst.snd.snd.snd.snd using 1
    funext ω
    by_cases hω : ω ∈ G <;>
      simp only [stoppedCoords, rCoord, rCoordAt, hω, ↓reduceIte, NNReal.coe_min]
  let 𝓘 := Clock7.imageFiltration ha hG hS.1 hs hb hc hm
  let τ : Ω → ℝ≥0∞ := fun ω => @ite ℝ≥0∞ (ω ∈ G) (Classical.propDecidable _)
    (newHorizon a (W · ω) (VR 0 · ω) (U ω)) 0
  have hinv : ∀ ω ∈ G, ∀ u : ℝ≥0, (u : ℝ≥0∞) < newHorizon a (W · ω) (VR 0 · ω) (U ω) →
      0 ≤ invClk (rate a (W · ω) (VR 0 · ω)) u ∧
      (((invClk (rate a (W · ω) (VR 0 · ω)) u).toNNReal : ℝ≥0) : ℝ≥0∞) < e ω := by
    intro ω hω u hu
    obtain ⟨s, -, -, -, hmem, -⟩ := newTime_spec (hs ω hω) ha hu
    exact ⟨hmem.1, (invClk_lt (hs ω hω) ha hu).trans_le (sepTime_le _ _ _)⟩
  refine ⟨𝓘, τ, Clock7.imageStop (a := a) (G := G) (W := W) (V := VR 0) (A := S),
    ?_, Clock7.isAnnouncingSeq_imageStop ha hG hS.1 hs hb hc hm hGa hS.2.1, ?_, ?_, ?_⟩
  · filter_upwards [hGa] with ω hω
    simp only [τ, U, hω, ↓reduceIte]
  · refine adaptedBefore_of_coords ha hG hS.1 hs hb hc hm
      (fun n => (hreg n).1) (fun n => (hreg n).2)
      (measurable_phiW (j := 0) (m := 1) κ xL ![a, b] ρL ρR) ?_
    intro ω hω u hu
    exact newW_eq_phiW (hgood ω hω).1 (hinv ω hω u hu).1 (hinv ω hω u hu).2
  · intro i
    refine adaptedBefore_of_coords ha hG hS.1 hs hb hc hm
      (fun n => (hreg n).1) (fun n => (hreg n).2)
      (measurable_phiVL (nL := 0) (j := 0) (m := 1) i) ?_
    intro ω hω u hu
    exact newVL_eq_phiVL (j := 0) (m := 1) (xR := ![a, b]) (w := (W · ω))
      (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) (b := (B · ω))
      (hinv ω hω u hu).1 i
  · refine adaptedBefore_of_coords ha hG hS.1 hs hb hc hm
      (fun n => (hreg n).1) (fun n => (hreg n).2)
      (measurable_phiNoise (j := 0) (m := 1) κ xL ![a, b] ρL ρR) ?_
    intro ω hω u hu
    exact newB_eq_phiNoise (hgood ω hω).1 (hinv ω hω u hu).1 (hinv ω hω u hu).2

end InteractingSLE.Sec5.TwoMark.Adapt8
