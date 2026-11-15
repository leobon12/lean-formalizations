/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MbFill

/-!
# Prefixes as initial segments of the walk curve, and their lifts

Packet PROVE-T14-SB2LIFT (round 16; the hypotheses of `fillCorr_of_curves`). A proper curve `β₀` from `0` is a closed
embedding (`isClosedEmbedding_of_isProperCurve`). So:

* **`exists_eq_image_Icc_of_isPreconnected`**: a compact preconnected part of its range containing `β₀ 0` is an
  initial segment `β₀([0, t])`; **`exists_eq_image_Icc_tail`**: if it also contains `β₀ t_L`, it is
  `β₀([0, t_L + s])`;
* `rayChartLim_of_ext`: `RayChartLim` from the boundary extension of the inverse chart;
* **`liftImage_image_Icc`**: the lift image of `β₀([0, t_L + s])` is `γ([0, s])`. So the relative prefix is the
  matching initial segment of the lift curve as soon as it is the lift image of the actual one (SB2LIFTSET's history
  correspondence);
* **`fillCorr_of_liftImage`**: `FillCorr` at a pair of launches when the actual prefixes after the launch and at the
  times of the piece are compact preconnected parts of the walk containing `0` and `R`, the relative ones are their lift
  images (at matching times of the two pieces), and points on the curves beyond the record are in the closed fills.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw GW1W

/-- **`RayChartLim` from the boundary extension of the inverse chart** (the inputs of SB2LIFTSET's
`rayChartInj_of_continuousWithinAt`: `ĝ` is the boundary limit of `c⁻¹` on `ℍ̄` and `ĝ (ι x − m) = x` for `x > R`). -/
theorem rayChartLim_of_ext {c : Chart} {R m : ℝ} {ι : ℝ → ℝ} {ĝ : ℂ → ℂ}
    (hlim : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (ĝ q))) (hĝx : ∀ x : ℝ, R < x → ĝ ((ι x - m : ℝ) : ℂ) = x) :
    RayChartLim c R m ι := fun y hy => by
  have h := hlim _ (show (0 : ℝ) ≤ (((ι y - m : ℝ)) : ℂ).im by simp)
  rwa [hĝx y hy] at h

variable {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **A compact preconnected part of a proper curve's range containing its start is an initial segment.** -/
theorem exists_eq_image_Icc_of_isPreconnected (hβ : Supp9B.IsProperCurve β₀) {K : Set ℂ} (hKc : IsCompact K)
    (hKp : IsPreconnected K) (hKr : K ⊆ range β₀) (h0 : β₀ 0 ∈ K) : ∃ t, K = β₀ '' Icc 0 t := by
  have hemb := isClosedEmbedding_of_isProperCurve hβ
  have hKP : β₀ '' (β₀ ⁻¹' K) = K := image_preimage_eq_of_subset hKr
  have hPc : IsCompact (β₀ ⁻¹' K) := (isProperMap_of_isProperCurve hβ).isCompact_preimage hKc
  have hPp : IsPreconnected (β₀ ⁻¹' K) := by
    rw [← hKP] at hKp
    exact hemb.isEmbedding.isInducing.isPreconnected_image.1 hKp
  have hP0 : (0 : ℝ≥0) ∈ β₀ ⁻¹' K := h0
  obtain ⟨t, htP, htmax⟩ := hPc.exists_isGreatest ⟨0, hP0⟩
  refine ⟨t, ?_⟩
  conv_lhs => rw [← hKP]
  congr 1
  ext u
  exact ⟨fun hu => ⟨zero_le, htmax hu⟩, fun hu => hPp.Icc_subset hP0 htP hu⟩

/-- **An initial segment containing `β₀ t_L` has length `t_L + s`.** -/
theorem exists_eq_image_Icc_tail (hβ : Supp9B.IsProperCurve β₀) {K : Set ℂ} (hKc : IsCompact K)
    (hKp : IsPreconnected K) (hKr : K ⊆ range β₀) (h0 : β₀ 0 ∈ K) (hL : β₀ tL ∈ K) :
    ∃ s, K = β₀ '' Icc 0 (tL + s) := by
  obtain ⟨t, rfl⟩ := exists_eq_image_Icc_of_isPreconnected hβ hKc hKp hKr h0
  obtain ⟨u, hu, hut⟩ := hL
  have hut' : u = tL := hβ.2.1 hut
  have htL : tL ≤ t := hut' ▸ hu.2
  exact ⟨t - tL, by rw [add_tsub_cancel_of_le htL]⟩

/-- **The lift image of an initial segment is the matching initial segment of the lift curve.** -/
theorem liftImage_image_Icc (hβ : Function.Injective β₀) (s : ℝ≥0) :
    liftImage β₀ tL γ (β₀ '' Icc 0 (tL + s)) = γ '' Icc 0 s := by
  unfold liftImage
  congr 1
  ext u
  constructor
  · rintro ⟨t, ht, htu⟩
    have : t = tL + u := hβ htu
    exact ⟨zero_le, (add_le_add_iff_left tL).1 (this ▸ ht.2)⟩
  · intro hu
    exact ⟨tL + u, ⟨zero_le, (add_le_add_iff_left tL).2 hu.2⟩, rfl⟩

/-- A compact preconnected part of the walk containing `0` and `R` (the actual prefix data). -/
def IsWalkSeg (β₀ : ℝ≥0 → ℂ) (tL : ℝ≥0) (K : Set ℂ) : Prop :=
  IsCompact K ∧ IsPreconnected K ∧ K ⊆ range β₀ ∧ β₀ 0 ∈ K ∧ β₀ tL ∈ K

/-- **Points on the actual prefix and on its lift beyond `a` are in the closed fills.** -/
def OnSegFill (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (ι : ℝ → ℝ) (a : ℝ) (K : Set ℂ) : Prop :=
  ∀ x : ℝ, a < x → ((x : ℂ) ∈ K → (x : ℂ) ∈ closure (fillH K)) ∧
    (((ι x : ℝ) : ℂ) ∈ liftImage β₀ tL γ K → ((ι x : ℝ) : ℂ) ∈ closure (fillH (liftImage β₀ tL γ K)))

variable {κ θ R : ℝ} {ι : ℝ → ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ}

theorem onCurveFill_of_onSegFill {a : ℝ} {s : ℝ≥0} (hβ : Function.Injective β₀)
    (h : OnSegFill β₀ γ tL ι a (β₀ '' Icc 0 (tL + s))) : OnCurveFill β₀ γ tL ι a s := by
  intro x hx
  have h' := h x hx
  rw [liftImage_image_Icc hβ] at h'
  exact h'

/-- **`FillCorr` from the lift images of the actual prefixes.** -/
theorem fillCorr_of_liftImage {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ : ℕ} (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
    (hβ : Supp9B.IsProperCurve β₀) (hD : LiftCurveData β₀ γ tL R ι)
    (hRa : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hP₁ : IsWalkSeg β₀ tL (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)))
    (hP₂ : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1) =
      liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)))
    (hon : OnSegFill β₀ γ tL ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
      (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)))
    (hpart₁ : ∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ (D₁ n₁) →
      IsWalkSeg β₀ tL (partPrefix κ b₁ J₁ θ D₁ n₁ r) ∧
      OnSegFill β₀ γ tL ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
        (partPrefix κ b₁ J₁ θ D₁ n₁ r) ∧
      ∃ r' : ℝ, 0 ≤ r' ∧ r' < stopTime ⊤ (D₂ n₂) ∧
        partPrefix κ b₂ J₂ θ D₂ n₂ r' = liftImage β₀ tL γ (partPrefix κ b₁ J₁ θ D₁ n₁ r))
    (hpart₂ : ∀ r' : ℝ, 0 ≤ r' → r' < stopTime ⊤ (D₂ n₂) → ∃ r : ℝ, 0 ≤ r ∧ r < stopTime ⊤ (D₁ n₁) ∧
      IsWalkSeg β₀ tL (partPrefix κ b₁ J₁ θ D₁ n₁ r) ∧
      OnSegFill β₀ γ tL ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
        (partPrefix κ b₁ J₁ θ D₁ n₁ r) ∧
      partPrefix κ b₂ J₂ θ D₂ n₂ r' = liftImage β₀ tL γ (partPrefix κ b₁ J₁ θ D₁ n₁ r)) :
    FillCorr κ θ b₁ J₁ D₁ n₁ b₂ J₂ D₂ n₂ ι := by
  have hseg : ∀ K : Set ℂ, IsWalkSeg β₀ tL K → ∃ s, K = β₀ '' Icc 0 (tL + s) ∧
      liftImage β₀ tL γ K = γ '' Icc 0 s := fun K hK => by
    obtain ⟨s, hs⟩ := exists_eq_image_Icc_tail hβ hK.1 hK.2.1 hK.2.2.1 hK.2.2.2.1 hK.2.2.2.2
    exact ⟨s, hs, by rw [hs, liftImage_image_Icc hβ.2.1]⟩
  refine fillCorr_of_curves hι hD hRa ?_ (fun r hr0 hr => ?_) (fun r' hr0' hr' => ?_)
  · obtain ⟨s, h1, h2⟩ := hseg _ hP₁
    refine ⟨s, h1, hP₂.trans h2, ?_⟩
    rw [h1] at hon
    exact onCurveFill_of_onSegFill hβ.2.1 hon
  · obtain ⟨hK, hon', r', hr0', hr', h⟩ := hpart₁ r hr0 hr
    obtain ⟨s, h1, h2⟩ := hseg _ hK
    rw [h1] at hon'
    exact ⟨s, h1, onCurveFill_of_onSegFill hβ.2.1 hon', r', hr0', hr', h.trans (h1 ▸ h2)⟩
  · obtain ⟨r, hr0, hr, hK, hon', h⟩ := hpart₂ r' hr0' hr'
    obtain ⟨s, h1, h2⟩ := hseg _ hK
    rw [h1] at hon'
    exact ⟨s, h.trans (h1 ▸ h2), onCurveFill_of_onSegFill hβ.2.1 hon', r, hr0, hr, h1⟩

end InteractingSLE.Theorem14.SB.Lk
