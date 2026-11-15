/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MzSample

/-!
# The stage-coordinate retained set is filled

Packet PROVE-SB2-LCMEAN, round 15 (item 4, chart facts under the upper kernel). `Mz.ident_at_sample` needs the
retained set in B's stage coordinates, `Mn.stageRetained cℓ Y`, to be filled: no point of its complement lies in its
filling. This holds when its complement is the image of `ℍ` under a domain chart (preconnected) and B's stage chart
`cℓ` is normalized: its inverse is within a bounded distance of the identity, so the stage-coordinate retained set is
bounded (the retained fill `fill Y` is), and its complement is unbounded:

* `isBounded_stageRetained`;
* **`notMem_fillH_stageRetained`**.

All statements are deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Bornology
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Mz

/-- The stage-coordinate retained set is bounded when B's stage chart is normalized and the retained fill bounded. -/
theorem isBounded_stageRetained {cℓ : Chart} (hcℓ : WalkIntCanon.IsNormalized cℓ) {Y : Set ℂ}
    (hY : IsBounded (fillH Y)) : IsBounded (Mn.stageRetained cℓ Y) := by
  obtain ⟨M, hM⟩ := hcℓ.inverse_bound
  obtain ⟨R, hR⟩ := hY.subset_closedBall 0
  refine (isBounded_closedBall (x := (0 : ℂ)) (r := R + M)).subset fun v hv => ?_
  have h1 := hM v hv.1
  have h2 := hR hv.2
  rw [mem_closedBall, dist_zero_right] at h2 ⊢
  calc ‖v‖ = ‖cℓ.2.1 v - (cℓ.2.1 v - v)‖ := by ring_nf
    _ ≤ ‖cℓ.2.1 v‖ + ‖cℓ.2.1 v - v‖ := norm_sub_le _ _
    _ ≤ R + M := add_le_add h2 h1

/-- **The stage-coordinate retained set is filled**: no point of its complement in `ℍ` lies in its filling. -/
theorem notMem_fillH_stageRetained {cℓ c' : Chart} (hcℓ : WalkIntCanon.IsNormalized cℓ) {Y : Set ℂ}
    (hY : IsBounded (fillH Y)) (hd : IsDomainChart (H \ Mn.stageRetained cℓ Y) c') :
    ∀ z ∈ H \ Mn.stageRetained cℓ Y, z ∉ fillH (Mn.stageRetained cℓ Y) := by
  set A := Mn.stageRetained cℓ Y with hA
  have hpc : IsPreconnected (H \ A) := by
    rw [← hd.image_eq]
    exact (convex_halfSpace_im_gt 0).isPreconnected.image _ hd.isConformal.1.continuousOn
  have hopen : IsOpen (H \ A) := hd.isOpen
  have hsub : H \ A ⊆ H \ closure A := by
    rintro z ⟨hzH, hzA⟩
    refine ⟨hzH, fun hcl => ?_⟩
    obtain ⟨w, hw, hwA⟩ := mem_closure_iff.1 hcl (H \ A) hopen ⟨hzH, hzA⟩
    exact hw.2 hwA
  have hunb : ¬ IsBounded (H \ A) := by
    intro hb
    obtain ⟨R₁, hR₁⟩ := (hb.union (isBounded_stageRetained hcℓ hY)).subset_closedBall 0
    set z₀ : ℂ := ((|R₁| + 1 : ℝ) : ℂ) * Complex.I with hz₀
    have hz₀H : z₀ ∈ H := by
      show 0 < z₀.im
      simp only [hz₀, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
        Complex.I_re, mul_zero, add_zero]
      positivity
    have h1 : z₀ ∈ (H \ A) ∪ A := by
      by_cases hzA : z₀ ∈ A
      · exact Or.inr hzA
      · exact Or.inl ⟨hz₀H, hzA⟩
    have h2 := hR₁ h1
    rw [mem_closedBall, dist_zero_right, hz₀, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < |R₁| + 1)] at h2
    linarith [le_abs_self R₁]
  intro z hz
  exact FinRel.notMem_fillH_of_isPreconnected hz hpc hsub hunb

end InteractingSLE.Theorem14.SB.Mz
