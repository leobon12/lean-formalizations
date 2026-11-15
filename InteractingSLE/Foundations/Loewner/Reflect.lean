/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LPProbReflect
import InteractingSLE.Spec.Restart.ClockFlow
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane

/-!
# Reflection of Loewner maps and of the planar notions across the imaginary axis

Packet PROVE-LEMMA76B. The reflection `R(z) = −z̄` (`LP.reflectC`) conjugates the chordal Loewner chain driven by
`W` to the chain driven by `−W`: hulls (`LP.fwdHull_neg`, PROVE-R17), forward maps, their logarithmic derivatives, the
inverse maps, generating traces (`LP.isGeneratingTrace_reflect`, PROVE-R17) and good paths. The planar notions used
for sides (the filling `fillH`, the free/trapped dichotomy of `HalfPlaneSep`) are reflection invariant. This is the
API behind every "the reflected assertion" of the specification at the level of single traces (Lemma 7.6's swapped
half, Aux. lemma 31's left arm, …).

## Main results

* `fwdMap_neg`: `f_T^{−W}(R z) = R (f_T^{W}(z))`, for every `z` (the junk value `0` is fixed by `R`);
* `logDerivFwd_neg`: `log (f_T^{−W})′ (R z) = conj (log (f_T^{W})′ z)`; in particular the derivative arguments are
  opposite (`im_logDerivFwd_neg`);
* `fwdMapInv_neg`: the inverse maps are conjugate too;
* `fillH_image_reflectC`, `isFreeAt_reflectC`, `isTrappedAt_reflectC`;
* `Restart.IsPathGood.reflect`: a good path from `x` reflects to a good path from `−x`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal ComplexConjugate

open QuantumZipper (H)

namespace InteractingSLE

namespace LP

/-! ### Forward maps -/

theorem reflectC_injective : Function.Injective reflectC := fun z w h => by
  simpa using congrArg reflectC h

theorem reflectC_ofReal (x : ℝ) : reflectC (x : ℂ) = ((-x : ℝ) : ℂ) := by simp [reflectC]

theorem reflectC_sub (z w : ℂ) : reflectC (z - w) = reflectC z - reflectC w := by
  simp [reflectC]; ring

theorem reflectC_add (z w : ℂ) : reflectC (z + w) = reflectC z + reflectC w := by
  simp [reflectC]; ring

@[simp] theorem reflectC_zero : reflectC 0 = 0 := by simp [reflectC]

theorem re_reflectC (z : ℂ) : (reflectC z).re = -z.re := by simp [reflectC]

/-- The reflection of a solution of the forward flow is the solution of the reflected flow, and conversely. -/
theorem exists_isForwardSol_neg_iff {W : ℝ → ℝ} {z : ℂ} {T : ℝ} :
    (∃ u, QuantumZipper.IsForwardSol (-W) (reflectC z) T u) ↔ ∃ u, QuantumZipper.IsForwardSol W z T u := by
  constructor
  · rintro ⟨u, hu⟩
    have := isForwardSol_neg hu
    rw [neg_neg, reflectC_reflectC] at this
    exact ⟨_, this⟩
  · rintro ⟨u, hu⟩
    exact ⟨_, isForwardSol_neg hu⟩

/-- **The forward maps of `W` and `−W` are conjugate by the reflection** (at a time `T ≥ 0`). -/
theorem fwdMap_neg (W : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    QuantumZipper.fwdMap (-W) T (reflectC z) = reflectC (QuantumZipper.fwdMap W T z) := by
  by_cases hex : ∃ u, QuantumZipper.IsForwardSol W z T u
  · have hex' := exists_isForwardSol_neg_iff.2 hex
    unfold QuantumZipper.fwdMap
    rw [dite_eq_left_of_eq_true (eq_true hex), dite_eq_left_of_eq_true (eq_true hex')]
    exact QuantumZipper.ASep.isForwardSol_unique_any hex'.choose_spec
      (isForwardSol_neg hex.choose_spec) ⟨hT, le_rfl⟩
  · have hex' : ¬ ∃ u, QuantumZipper.IsForwardSol (-W) (reflectC z) T u := fun h =>
      hex (exists_isForwardSol_neg_iff.1 h)
    unfold QuantumZipper.fwdMap
    rw [dite_eq_right_of_eq_false (eq_false hex), dite_eq_right_of_eq_false (eq_false hex'), reflectC_zero]

/-- **The logarithmic derivatives of `W` and `−W` are conjugate**: `log (f_T^{−W})′ (R z) = conj (log (f_T^{W})′ z)`. -/
theorem logDerivFwd_neg (W : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    QuantumZipper.logDerivFwd (-W) T (reflectC z) = conj (QuantumZipper.logDerivFwd W T z) := by
  unfold QuantumZipper.logDerivFwd
  rw [map_neg, ← intervalIntegral.intervalIntegral_conj]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hs0 : 0 ≤ s := by
    rw [uIcc_of_le hT] at hs
    exact hs.1
  rw [fwdMap_neg W hs0 z]
  have h2 : conj (2 : ℂ) = 2 := map_ofNat _ 2
  simp only [reflectC, neg_sq, map_div₀, map_pow, h2]

/-- The derivative arguments of the reflected chain are opposite. -/
theorem im_logDerivFwd_neg (W : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    (QuantumZipper.logDerivFwd (-W) T (reflectC z)).im = -(QuantumZipper.logDerivFwd W T z).im := by
  rw [logDerivFwd_neg W hT, conj_im]

/-! ### Planar notions -/

theorem image_reflectC_ball (z : ℂ) (ε : ℝ) : reflectC '' ball z ε = ball (reflectC z) ε := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_ball, isometry_reflectC.dist_eq]
    exact hv
  · intro hw
    refine ⟨reflectC w, ?_, reflectC_reflectC w⟩
    rw [mem_ball, ← isometry_reflectC.dist_eq, reflectC_reflectC]
    exact hw

theorem reflectC_image_H : reflectC '' H = H := by
  rw [reflectC_image_eq_preimage]
  ext z
  exact reflectC_mem_H_iff

theorem closure_image_reflectC (A : Set ℂ) : closure (reflectC '' A) = reflectC '' closure A :=
  (reflectHomeo.image_closure A).symm

/-- **The filling is reflection invariant.** -/
theorem fillH_image_reflectC (A : Set ℂ) : fillH (reflectC '' A) = reflectC '' fillH A := by
  have hcc : ∀ z, connectedComponentIn (H \ closure (reflectC '' A)) (reflectC z) =
      reflectC '' connectedComponentIn (H \ closure A) z := by
    intro z
    rw [closure_image_reflectC, H_diff_reflectC_image]
    have := reflectHomeo.image_connectedComponentIn (s := H \ closure A) (x := z)
    rw [coe_reflectHomeo] at this
    by_cases hz : z ∈ H \ closure A
    · exact (this hz).symm
    · rw [connectedComponentIn_eq_empty hz, image_empty]
      refine connectedComponentIn_eq_empty fun h => hz ?_
      obtain ⟨v, hv, hvz⟩ := h
      rw [← reflectC_injective hvz]
      exact hv
  ext w
  constructor
  · rintro ⟨hwH, hw⟩
    refine ⟨reflectC w, ⟨reflectC_mem_H_iff.2 hwH, ?_⟩, reflectC_reflectC w⟩
    rcases hw with hw | hw
    · left
      rw [closure_image_reflectC] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      rwa [reflectC_reflectC]
    · right
      rw [← reflectC_reflectC w, hcc, isBounded_reflectC_image_iff] at hw
      exact hw
  · rintro ⟨v, ⟨hvH, hv⟩, rfl⟩
    refine ⟨reflectC_mem_H_iff.2 hvH, ?_⟩
    rcases hv with hv | hv
    · left
      rw [closure_image_reflectC]
      exact mem_image_of_mem _ hv
    · right
      rw [hcc, isBounded_reflectC_image_iff]
      exact hv

theorem H_diff_fillH_image_reflectC (A : Set ℂ) :
    H \ fillH (reflectC '' A) = reflectC '' (H \ fillH A) := by
  rw [fillH_image_reflectC, H_diff_reflectC_image]

theorem isFreeAt_reflectC {F : Set ℂ} {z : ℂ} (h : HalfPlaneSep.IsFreeAt F z) :
    HalfPlaneSep.IsFreeAt (reflectC '' F) (reflectC z) := by
  obtain ⟨ε, hε, hsub⟩ := h
  refine ⟨ε, hε, ?_⟩
  rw [← image_reflectC_ball, H_diff_fillH_image_reflectC]
  rintro _ ⟨⟨v, hv, rfl⟩, hvH⟩
  exact mem_image_of_mem _ (hsub ⟨hv, reflectC_mem_H_iff.1 hvH⟩)

theorem isTrappedAt_reflectC {F : Set ℂ} {z : ℂ} (h : HalfPlaneSep.IsTrappedAt F z) :
    HalfPlaneSep.IsTrappedAt (reflectC '' F) (reflectC z) := by
  obtain ⟨ε, hε, hd⟩ := h
  refine ⟨ε, hε, ?_⟩
  rw [← image_reflectC_ball, H_diff_fillH_image_reflectC]
  exact (disjoint_image_iff reflectC_injective).2 hd

end LP

namespace Restart

/-- **A good path reflects to a good path**: `−η̄` from `−x`, driven by `−w`. -/
theorem IsPathGood.reflect {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} (hp : IsPathGood η ζ x) :
    IsPathGood (fun t => LP.reflectC (η t)) ζ (-x) := by
  obtain ⟨hi, w, hw, hw0, hg⟩ := hp
  refine ⟨fun s hs t ht hst => hi hs ht (LP.reflectC_injective hst), -w, hw.neg, by simp [hw0], ?_⟩
  have h := LP.isGeneratingTrace_reflect hg
  have e : (fun t => LP.reflectC (η t - x)) = fun t => LP.reflectC (η t) - ((-x : ℝ) : ℂ) := by
    funext t
    rw [LP.reflectC_sub, LP.reflectC_ofReal]
  rwa [e] at h

end Restart

end InteractingSLE
