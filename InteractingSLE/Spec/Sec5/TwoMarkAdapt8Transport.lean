/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkAdapt8Coordinates

/-!
# Adaptedness in the local inverse-clock filtration

Optional evaluation of stopped source coordinates and exhaustion by their clock
images prove adaptedness before the masked image lifetime.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Adapt8

open Zhan.Retarget

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
  {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {k : Fin nR}
  {G : Set Ω} {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {U : Ω → ℝ≥0∞} {A : ℕ → Ω → ℝ≥0}

variable (ha : 0 < a) (hG : MeasurableSet[𝓕 0] G)
  (hA : ∀ n, IsStoppingTime 𝓕 fun ω => (A n ω : WithTop ℝ≥0))
  (hs : ∀ ω ∈ G, SepUpTo (W · ω) (VR k · ω) (U ω))
  (hb : ∀ ω ∈ G, ∀ n, (A n ω : ℝ≥0∞) < U ω)
  (hc : ∀ ω ∈ G, ∀ s : ℝ≥0, (s : ℝ≥0∞) < U ω → ∃ n, s ≤ A n ω)
  (hm : ∀ n r, Measurable[𝓕 r] fun ω => if ω ∈ G then
    clk (rate a (W · ω) (VR k · ω)) (min r (A n ω)) else 0)

include ha hG hA hs hb hc hm

/-- Measurable functions of the inverse-time source coordinates are adapted locally. -/
theorem adaptedBefore_of_coords
    (hZm : ∀ n r, Measurable[𝓕 r] (stoppedCoords xL xR a k G W B VL VR (A n) r))
    (hZc : ∀ n ω, Continuous (stoppedCoords xL xR a k G W B VL VR (A n) · ω))
    {X : ℝ≥0 → Ω → ℝ} {Φ : RCoord nL nR × ℝ → ℝ} (hΦ : Measurable Φ)
    (hX : ∀ ω ∈ G, ∀ u : ℝ≥0, (u : ℝ≥0∞) < newHorizon a (W · ω) (VR k · ω) (U ω) →
      X u ω = Φ (rCoordAt a k (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
        (invClk (rate a (W · ω) (VR k · ω)) u).toNNReal,
        B (invClk (rate a (W · ω) (VR k · ω)) u).toNNReal ω)) :
    AdaptedBefore (Clock7.imageFiltration ha hG hA hs hb hc hm)
      (fun ω => if ω ∈ G then newHorizon a (W · ω) (VR k · ω) (U ω) else 0) X := by
  intro u D hD
  let 𝓘 := Clock7.imageFiltration ha hG hA hs hb hc hm
  let I := Clock7.inverseTime G a W (VR k) U u
  let Z := fun n ω => stoppedCoords xL xR a k G W B VL VR (A n)
    (Sec2.TwoSeed.capTime (A n) I ω) ω
  have hI : IsStoppingTime 𝓕 I := Clock7.isStoppingTime_inverseTime ha hG hA hs hb hc hm u
  have hGI : MeasurableSet[𝓘 u] G := by
    have hz := isStoppingTime_const 𝓕 (0 : ℝ≥0)
    have hle := IsStoppingTime.measurableSpace_mono hz hI (fun ω => by
      simp only [WithTop.coe_zero]; exact zero_le)
    rw [IsStoppingTime.measurableSpace_const] at hle
    exact hle _ hG
  have hSm : ∀ n, MeasurableSet[𝓘 u] {ω | u ≤ Clock7.imageStop
      (a := a) (G := G) (W := W) (V := VR k) (A := A) n ω} := fun n => by
    simpa only [WithTop.coe_le_coe] using
      (Clock7.isStoppingTime_imageStop ha hG hA hs hb hc hm n).measurableSet_ge u
  have hZ : ∀ n, Measurable[𝓘 u] (Z n) := fun n =>
    measurable_cap_stoppedCoords (hZm n) (hZc n) (hA n) hI
  have hval : ∀ ω ∈ G, ∀ n, u ≤ Clock7.imageStop
      (a := a) (G := G) (W := W) (V := VR k) (A := A) n ω →
      (u : ℝ≥0∞) < newHorizon a (W · ω) (VR k · ω) (U ω) ∧ Φ (Z n ω) = X u ω := by
    intro ω hω n hn
    have hcl := clk_lt_newHorizon' (hs ω hω) ha (hb ω hω n)
    have hn' : u ≤ (clk (rate a (W · ω) (VR k · ω)) (A n ω)).toNNReal := by
      simpa only [Clock7.imageStop, hω, ↓reduceIte] using hn
    have hu := (ENNReal.coe_le_coe.2 hn').trans_lt hcl.2
    have hle := (invClk_le_iff (hs ω hω) ha hu (hb ω hω n)).2
      ((Real.le_toNNReal_iff_coe_le hcl.1).1 hn')
    have hcap : Sec2.TwoSeed.capTime (A n) I ω =
        (invClk (rate a (W · ω) (VR k · ω)) u).toNNReal := by
      apply WithTop.coe_injective
      rw [Sec2.TwoSeed.coe_capTime]
      simp only [I, Clock7.inverseTime, hω, hu, ↓reduceIte]
      exact min_eq_right (WithTop.coe_le_coe.2 hle)
    refine ⟨hu, ?_⟩
    simp only [Z, stoppedCoords, rCoord, hω, ↓reduceIte, hcap, min_eq_left hle]
    exact (hX ω hω u hu).symm
  have he : {ω | (u : ℝ≥0∞) < (if ω ∈ G then
      newHorizon a (W · ω) (VR k · ω) (U ω) else 0) ∧ X u ω ∈ D} =
      G ∩ ⋃ n, ({ω | u ≤ Clock7.imageStop
        (a := a) (G := G) (W := W) (V := VR k) (A := A) n ω} ∩ (Φ ∘ Z n) ⁻¹' D) := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [hω, ↓reduceIte, mem_ofPred_eq, mem_inter_iff, true_and,
        mem_iUnion, mem_preimage, Function.comp_apply]
      constructor
      · rintro ⟨hu, hXD⟩
        obtain ⟨n, hn⟩ := hc ω hω _ (invClk_lt (hs ω hω) ha hu)
        have hcl := clk_lt_newHorizon' (hs ω hω) ha (hb ω hω n)
        have hn' : u ≤ Clock7.imageStop
            (a := a) (G := G) (W := W) (V := VR k) (A := A) n ω := by
          simp only [Clock7.imageStop, hω, ↓reduceIte]
          exact (Real.le_toNNReal_iff_coe_le hcl.1).2
            ((invClk_le_iff (hs ω hω) ha hu (hb ω hω n)).1 hn)
        exact ⟨n, hn', by rw [(hval ω hω n hn').2]; exact hXD⟩
      · rintro ⟨n, hn, hZD⟩
        exact ⟨(hval ω hω n hn).1, by rwa [← (hval ω hω n hn).2]⟩
    · simp only [hω, ↓reduceIte, mem_ofPred_eq, mem_inter_iff, false_and, iff_false, not_and]
      intro h
      exact absurd h (not_lt.2 bot_le)
  rw [he]
  exact hGI.inter (MeasurableSet.iUnion fun n => (hSm n).inter ((hΦ.comp (hZ n)) hD))

end InteractingSLE.Sec5.TwoMark.Adapt8
