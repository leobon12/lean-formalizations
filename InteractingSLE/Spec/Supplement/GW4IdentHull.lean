/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.ConformalImageFull
import InteractingSLE.Spec.Sec6.DrivingCriterion
import QuantumZipper.Proofs.RS.HullBasics

/-!
# Theorem GW4: a relative hull family determines its driver

Packet PROVE-T14-GW4R. The identification half of Theorem GW4's traversal (`GW4Traverse.GW4RelativeIdentStatement`,
"The full kernel and the one phase", pp. 638–639) asserts that the centred counterflow of the component field is every
continuous relative driver `W_rel` whose Loewner hulls are the chart images `Φ(K'_{T s} ∩ R⁻¹(C))` of the ambient
traversal, for some clock `T`. This file proves the deterministic half of that remark (PROVE-T14-GW4T handoff §5 (B),
"hull families of the form (ii) determine the clock … and then the driver"; the strict monotonicity of half-plane
capacity it needs was missing there):

* `hcap_fwdHull_eq`: `hcap(K_t) = 2t` for every continuous driver (no normalization `W 0 = 0`), by translation;
* `eq_of_subset_of_hcap_eq`: **strict monotonicity of half-plane capacity**: nested compact `ℍ`-hulls of equal
  capacity are equal (from the composition rule `HPHull.hcap_eq_add` and `HPHull.hcap_eq_zero_iff`);
* `fwdHull_eq_of_subset`: nested Loewner hulls at the same capacity time are equal;
* `eq_zero_of_fwdHull_eq`: the hulls determine the starting point of the driver;
* `eq_of_forall_fwdHull_eq`: hulls equal at every time give equal drivers on `[0, ∞)`;
* **`eq_of_fwdHull_eq_comp`**: if the hulls of two continuous drivers are `A (T₁ s)` and `A (T₂ s)` for one monotone
  family `A` of sets and any two clocks `T₁`, `T₂`, the drivers are equal (no property of the clocks is needed: the
  two hulls are nested and have the same capacity `2s`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace InteractingSLE

namespace Theorem14

namespace GW4Ident

/-! ### Capacity of the Loewner hulls -/

/-- **`hcap(K_t) = 2t` for every continuous driver.** The hulls of `W` are those of `W − W 0` translated by `W 0`
(`ConformalImageFull.fwdHull_add_const`), and translation preserves capacity (`HPHull.hcap_affHomeo` with `r = 1`). -/
theorem hcap_fwdHull_eq {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    HPHull.hcap ⟨QuantumZipper.fwdHull W t, isHPHull_fwdHull hW ht⟩ = 2 * t := by
  set U : ℝ → ℝ := fun s => W s - W 0 with hU
  have hUc : Continuous U := hW.sub continuous_const
  have hU0 : U 0 = 0 := by simp [hU]
  have hWU : (fun s => U s + W 0) = W := by funext s; simp [hU]
  have hset : QuantumZipper.fwdHull W t = affHomeo 1 one_pos (W 0) '' QuantumZipper.fwdHull U t := by
    have key := ConformalImageFull.fwdHull_add_const U (W 0) t
    rw [hWU] at key
    rw [key, coe_affHomeo]
    simp only [Complex.ofReal_one, one_mul]
  have e1 := HPHull.hcap_congr (A := ⟨QuantumZipper.fwdHull W t, isHPHull_fwdHull hW ht⟩)
    (B := ⟨affHomeo 1 one_pos (W 0) '' QuantumZipper.fwdHull U t,
      (isHPHull_fwdHull hUc ht).image_affHomeo one_pos⟩) hset
  rw [e1, HPHull.hcap_affHomeo ⟨QuantumZipper.fwdHull U t, isHPHull_fwdHull hUc ht⟩ one_pos,
    hcap_fwdHull hUc hU0 ht, one_pow, one_mul]

/-- **Strict monotonicity of half-plane capacity**: nested compact `ℍ`-hulls with the same capacity are equal
([Law05] §3.4: `hcap(B) = hcap(g_A(B \ A)) + hcap(A)` and `hcap = 0` only for the empty hull). -/
theorem eq_of_subset_of_hcap_eq {A B : HPHull} (hAB : A.1 ⊆ B.1) (h : A.hcap = B.hcap) : A.1 = B.1 := by
  obtain ⟨g, hg⟩ := A.2.exists_isMapOut
  have e := HPHull.hcap_eq_add hAB hg
  have h0 : HPHull.hcap ⟨g '' (B.1 \ A.1), hg.isHPHull_image A.2 B.2 hAB⟩ = 0 := by linarith
  have h0' := (HPHull.hcap_eq_zero_iff _).1 h0
  exact le_antisymm hAB (sdiff_eq_empty.1 (image_eq_empty.1 h0'))

/-- **Nested Loewner hulls at the same capacity time are equal.** -/
theorem fwdHull_eq_of_subset {W₁ W₂ : ℝ → ℝ} (hW₁ : Continuous W₁) (hW₂ : Continuous W₂) {t : ℝ} (ht : 0 ≤ t)
    (h : QuantumZipper.fwdHull W₁ t ⊆ QuantumZipper.fwdHull W₂ t) :
    QuantumZipper.fwdHull W₁ t = QuantumZipper.fwdHull W₂ t :=
  eq_of_subset_of_hcap_eq (A := ⟨_, isHPHull_fwdHull hW₁ ht⟩) (B := ⟨_, isHPHull_fwdHull hW₂ ht⟩) h
    (by rw [hcap_fwdHull_eq hW₁ ht, hcap_fwdHull_eq hW₂ ht])

/-! ### The hulls determine the driver -/

/-- For a continuous driver from `0` and `ε > 0`, all short enough times have hulls in `closedBall 0 ε`. -/
theorem eventually_fwdHull_subset_closedBall {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ t : ℝ, 0 < t → t ≤ δ → QuantumZipper.fwdHull W t ⊆ closedBall 0 ε := by
  obtain ⟨δ₁, hδ₁, hδ₁W⟩ := Metric.continuous_iff.1 hW 0 (ε / 2) (half_pos hε)
  refine ⟨min (δ₁ / 2) ((ε / 6) ^ 2), lt_min (half_pos hδ₁) (by positivity), fun t ht htδ => ?_⟩
  have hM : ∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ ε / 2 := by
    intro r hr
    have hr' : dist r 0 < δ₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hr.1]
      linarith [min_le_left (δ₁ / 2) ((ε / 6) ^ 2), hr.2]
    have := hδ₁W r hr'
    rw [Real.dist_eq, hW0, sub_zero] at this
    exact this.le
  refine (QuantumZipper.CaraR.fwdHull_subset_closedBall hW ht hM).trans (closedBall_subset_closedBall ?_)
  have hsq : Real.sqrt t ≤ ε / 6 := by
    rw [show ε / 6 = Real.sqrt ((ε / 6) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (htδ.trans (min_le_right _ _))
  linarith

/-- **The hulls determine the starting point of the driver**: if the hulls of continuous `W₁`, `W₂` agree at all
small positive times and `W₁ 0 = 0`, then `W₂ 0 = 0` (both hull families shrink to the starting points). -/
theorem eq_zero_of_fwdHull_eq {W₁ W₂ : ℝ → ℝ} (hW₁ : Continuous W₁) (hW₂ : Continuous W₂) (hW₁0 : W₁ 0 = 0)
    (h : ∀ t : ℝ, 0 < t → QuantumZipper.fwdHull W₁ t = QuantumZipper.fwdHull W₂ t) : W₂ 0 = 0 := by
  set c := W₂ 0 with hc
  set U : ℝ → ℝ := fun s => W₂ s - c with hU
  have hUc : Continuous U := hW₂.sub continuous_const
  have hU0 : U 0 = 0 := by simp [hU, hc]
  have hWU : (fun s => U s + c) = W₂ := by funext s; simp [hU]
  by_contra hne
  have hpos : 0 < |c| := abs_pos.2 hne
  obtain ⟨δ₁, hδ₁, h₁⟩ := eventually_fwdHull_subset_closedBall hW₁ hW₁0 (ε := |c| / 4) (by positivity)
  obtain ⟨δ₂, hδ₂, h₂⟩ := eventually_fwdHull_subset_closedBall hUc hU0 (ε := |c| / 4) (by positivity)
  set t := min δ₁ δ₂ with ht
  have ht0 : 0 < t := lt_min hδ₁ hδ₂
  obtain ⟨z, hz⟩ := QuantumZipper.RS.fwdHull_nonempty_of_pos hW₁ hW₁0 ht0
  have hz₁ := h₁ t ht0 (min_le_left _ _) hz
  have hz₂ : z ∈ QuantumZipper.fwdHull W₂ t := h t ht0 ▸ hz
  have key := ConformalImageFull.fwdHull_add_const U c t
  rw [hWU] at key
  rw [key] at hz₂
  obtain ⟨u, hu, rfl⟩ := hz₂
  have hu₂ := h₂ t ht0 (min_le_right _ _) hu
  rw [mem_closedBall, dist_zero_right] at hz₁ hu₂
  have key : ‖(c : ℂ)‖ ≤ ‖u + c‖ + ‖u‖ := by
    calc ‖(c : ℂ)‖ = ‖(u + c) - u‖ := by ring_nf
      _ ≤ ‖u + c‖ + ‖u‖ := norm_sub_le _ _
  rw [Complex.norm_real, Real.norm_eq_abs] at key
  linarith

/-- **Hulls equal at every time give equal drivers on `[0, ∞)`** (`Sec6.eqOn_of_fwdHull_eq` on every `[0, s]`, after
`eq_zero_of_fwdHull_eq`). -/
theorem eq_of_forall_fwdHull_eq {W₁ W₂ : ℝ≥0 → ℝ} (hW₁ : Continuous W₁) (hW₂ : Continuous W₂) (hW₁0 : W₁ 0 = 0)
    (h : ∀ s : ℝ≥0, QuantumZipper.fwdHull (fun r : ℝ => W₁ r.toNNReal) s =
      QuantumZipper.fwdHull (fun r : ℝ => W₂ r.toNNReal) s) : W₁ = W₂ := by
  have hc₁ : Continuous (fun r : ℝ => W₁ r.toNNReal) := hW₁.comp continuous_real_toNNReal
  have hc₂ : Continuous (fun r : ℝ => W₂ r.toNNReal) := hW₂.comp continuous_real_toNNReal
  have h' : ∀ t : ℝ, 0 ≤ t → QuantumZipper.fwdHull (fun r : ℝ => W₁ r.toNNReal) t =
      QuantumZipper.fwdHull (fun r : ℝ => W₂ r.toNNReal) t := by
    intro t ht
    have := h t.toNNReal
    rwa [Real.coe_toNNReal t ht] at this
  have h0₁ : (fun r : ℝ => W₁ r.toNNReal) 0 = 0 := by simp [hW₁0]
  have h0₂ : (fun r : ℝ => W₂ r.toNNReal) 0 = 0 :=
    eq_zero_of_fwdHull_eq hc₁ hc₂ h0₁ fun t ht => h' t ht.le
  funext s
  have := Sec6.eqOn_of_fwdHull_eq hc₁ hc₂ h0₁ h0₂ (NNReal.coe_nonneg s) (fun r hr => h' r hr.1)
    (show (s : ℝ) ∈ Icc 0 (s : ℝ) from ⟨NNReal.coe_nonneg s, le_rfl⟩)
  simpa only [Real.toNNReal_coe] using this

/-- **A monotone hull family determines its driver, whatever the clocks**: if the hulls of continuous `W₁`, `W₂`
(`W₁ 0 = 0`) are `A (T₁ s)` and `A (T₂ s)` for a monotone family `A`, then `W₁ = W₂`. For each `s` the two hulls are
nested (the clock values are comparable) and both have capacity `2s`, so they are equal
(`fwdHull_eq_of_subset`); then `eq_of_forall_fwdHull_eq`. -/
theorem eq_of_fwdHull_eq_comp {A : ℝ≥0 → Set ℂ} (hA : Monotone A) {W₁ W₂ : ℝ≥0 → ℝ} {T₁ T₂ : ℝ≥0 → ℝ≥0}
    (hW₁ : Continuous W₁) (hW₂ : Continuous W₂) (hW₁0 : W₁ 0 = 0)
    (h₁ : ∀ s : ℝ≥0, QuantumZipper.fwdHull (fun r : ℝ => W₁ r.toNNReal) s = A (T₁ s))
    (h₂ : ∀ s : ℝ≥0, QuantumZipper.fwdHull (fun r : ℝ => W₂ r.toNNReal) s = A (T₂ s)) : W₁ = W₂ := by
  have hc₁ : Continuous (fun r : ℝ => W₁ r.toNNReal) := hW₁.comp continuous_real_toNNReal
  have hc₂ : Continuous (fun r : ℝ => W₂ r.toNNReal) := hW₂.comp continuous_real_toNNReal
  refine eq_of_forall_fwdHull_eq hW₁ hW₂ hW₁0 fun s => ?_
  rcases le_total (T₁ s) (T₂ s) with hT | hT
  · refine fwdHull_eq_of_subset hc₁ hc₂ (NNReal.coe_nonneg s) ?_
    rw [h₁, h₂]
    exact hA hT
  · refine (fwdHull_eq_of_subset hc₂ hc₁ (NNReal.coe_nonneg s) ?_).symm
    rw [h₁, h₂]
    exact hA hT

end GW4Ident

end Theorem14

end InteractingSLE
