/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLeafStep

/-!
# SB4's zero-duration switch: S1 at time zero

Packet PROVE-T14-SB4LEAF. At a switch whose new piece has zero available duration (an inadmissible seed group:
"its available new history is the singleton seed and there is nothing to add", supplement p. 634), the sewing
certificate `HasActualTailSewing` needs SB3's S1 comparison only at the time `a = 0`. That comparison is elementary:
a path at time `0` is the single point `η 0` on the real line, and every compact set of `closure ℍ` lies in the closed
right side of the proper completion that runs left from `η 0` along the real line far beyond the set and then
straight up.

* `zeroCompletion`, `isProperCompletion_zeroCompletion`, `subset_closedRightSide_zeroCompletion`;
* **`isOneSided_zero`**: S1 at time `0` for every compact set of `closure ℍ` and every path starting on `ℝ`;
* **`HasRelTailGeometry.hasActualTailSewing_zero`**: the S1-free sewing data with zero lifetime are a sewing
  certificate (no SB3 input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Lf

open Supp9B

/-- The proper completion at time `0` from the real point `m`: left along the real line to `-N`
(over the own-time interval `[0, m + N]`), then straight up. -/
def zeroCompletion (m N : ℝ) : ℝ≥0 → ℂ := fun t =>
  if (t : ℝ) ≤ m + N then ((m - t : ℝ) : ℂ) else ((-N : ℝ) : ℂ) + (((t : ℝ) - (m + N) : ℝ) : ℂ) * I

theorem zeroCompletion_of_le {m N : ℝ} {t : ℝ≥0} (ht : (t : ℝ) ≤ m + N) :
    zeroCompletion m N t = ((m - t : ℝ) : ℂ) := by simp only [zeroCompletion, ht, ite_true]

theorem zeroCompletion_of_lt {m N : ℝ} {t : ℝ≥0} (ht : m + N < (t : ℝ)) :
    zeroCompletion m N t = ((-N : ℝ) : ℂ) + (((t : ℝ) - (m + N) : ℝ) : ℂ) * I := by
  simp only [zeroCompletion, not_le.2 ht, ite_false]

theorem zeroCompletion_re_im {m N : ℝ} (t : ℝ≥0) :
    ((t : ℝ) ≤ m + N → (zeroCompletion m N t).re = m - t ∧ (zeroCompletion m N t).im = 0) ∧
      (m + N < (t : ℝ) → (zeroCompletion m N t).re = -N ∧ (zeroCompletion m N t).im = (t : ℝ) - (m + N)) := by
  refine ⟨fun ht => ?_, fun ht => ?_⟩
  · rw [zeroCompletion_of_le ht]; simp
  · rw [zeroCompletion_of_lt ht]; simp

theorem continuous_zeroCompletion (m N : ℝ) : Continuous (zeroCompletion m N) := by
  refine Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) continuous_const ?_
  intro t ht
  rw [ht]
  apply Complex.ext <;> simp

theorem zeroCompletion_im_nonneg (m N : ℝ) (t : ℝ≥0) : 0 ≤ (zeroCompletion m N t).im := by
  rcases le_or_gt (t : ℝ) (m + N) with ht | ht
  · rw [((zeroCompletion_re_im t).1 ht).2]
  · rw [((zeroCompletion_re_im t).2 ht).2]; linarith

theorem zeroCompletion_injective (m N : ℝ) : Function.Injective (zeroCompletion m N) := by
  intro s t hst
  have hre := congrArg Complex.re hst
  have him := congrArg Complex.im hst
  apply NNReal.coe_injective
  rcases le_or_gt (s : ℝ) (m + N) with hs | hs <;> rcases le_or_gt (t : ℝ) (m + N) with ht | ht
  · rw [((zeroCompletion_re_im s).1 hs).1, ((zeroCompletion_re_im t).1 ht).1] at hre; linarith
  · rw [((zeroCompletion_re_im s).1 hs).2, ((zeroCompletion_re_im t).2 ht).2] at him; linarith
  · rw [((zeroCompletion_re_im s).2 hs).2, ((zeroCompletion_re_im t).1 ht).2] at him; linarith
  · rw [((zeroCompletion_re_im s).2 hs).2, ((zeroCompletion_re_im t).2 ht).2] at him; linarith

theorem tendsto_norm_zeroCompletion (m N : ℝ) :
    Tendsto (fun t => ‖zeroCompletion m N t‖) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    ((tendsto_atTop_add_const_right _ (-(m + N)) (NNReal.tendsto_coe_atTop.2 tendsto_id)))
  filter_upwards [eventually_gt_atTop (⟨max (m + N) 0, le_max_right _ _⟩ : ℝ≥0)] with t ht
  have ht' : m + N < (t : ℝ) := lt_of_le_of_lt (le_max_left _ _) (show max (m + N) 0 < (t : ℝ) from ht)
  have h1 := Complex.abs_im_le_norm (zeroCompletion m N t)
  rw [((zeroCompletion_re_im t).2 ht').2] at h1
  simp only [id]
  linarith [le_abs_self ((t : ℝ) - (m + N))]

/-- The completion at time `0` is a proper completion of every path starting at `m`. -/
theorem isProperCompletion_zeroCompletion {η : ℝ≥0 → ℂ} {m N : ℝ} (hη0 : η 0 = m) (hmN : 0 ≤ m + N) :
    IsProperCompletion η 0 (zeroCompletion m N) := by
  refine ⟨continuous_zeroCompletion m N, zeroCompletion_injective m N, zeroCompletion_im_nonneg m N,
    tendsto_norm_zeroCompletion m N, fun t ht => ?_⟩
  have ht0 : t = 0 := le_antisymm ht zero_le
  subst ht0
  rw [zeroCompletion_of_le (by simpa using hmN), hη0]
  simp

/-- **The closed right side of the completion at time `0` contains every set of `closure ℍ` right of `-N`.** -/
theorem subset_closedRightSide_zeroCompletion {m N : ℝ} (hmN : -N < m) {X : Set ℂ}
    (hXH : ∀ z ∈ X, 0 ≤ z.im) (hXN : ∀ z ∈ X, -N < z.re) :
    X ⊆ closedRightSide (zeroCompletion m N) := by
  have hmN' : 0 ≤ m + N := by linarith
  have h0 : zeroCompletion m N 0 = (m : ℂ) := by
    rw [zeroCompletion_of_le (by simpa using hmN')]; simp
  set U : Set ℂ := {z | m < z.re} ∪ {z | -N < z.re ∧ 0 < z.im} with hU
  have hU1 : IsPreconnected {z : ℂ | m < z.re} := (convex_halfSpace_re_gt m).isPreconnected
  have hU2 : IsPreconnected {z : ℂ | -N < z.re ∧ 0 < z.im} :=
    ((convex_halfSpace_re_gt (-N)).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hUc : IsPreconnected U := by
    refine hU1.union ((m + 1 : ℝ) + I) ?_ ?_ hU2
    · show m < ((m + 1 : ℝ) + I).re; simp
    · refine ⟨?_, ?_⟩
      · simp only [add_re, ofReal_re, I_re, add_zero]
        linarith
      · simp
  have hUS : U ⊆ (seedRayClosure (zeroCompletion m N))ᶜ := by
    rintro z hz (⟨t, rfl⟩ | ⟨hre, him⟩)
    · rcases le_or_gt (t : ℝ) (m + N) with ht | ht
      · obtain ⟨h1, h2⟩ := (zeroCompletion_re_im t).1 ht
        rcases hz with hz | hz
        · have : m < m - t := h1 ▸ hz; linarith [t.2]
        · exact absurd hz.2 (by rw [h2]; exact lt_irrefl 0)
      · obtain ⟨h1, -⟩ := (zeroCompletion_re_im t).2 ht
        rcases hz with hz | hz
        · have : m < -N := h1 ▸ hz; linarith
        · exact absurd hz.1 (by rw [h1]; exact lt_irrefl _)
    · rw [h0] at hre him
      simp only [Complex.ofReal_re, Complex.ofReal_im] at hre him
      rcases hz with hz | hz
      · have : m < z.re := hz
        linarith
      · have : 0 < z.im := hz.2
        linarith
  have hbase : zeroCompletion m N 0 + 1 - I ∈ U := Or.inl (by rw [h0]; simp)
  have hsub : U ⊆ rightSide (zeroCompletion m N) :=
    hUc.subset_connectedComponentIn hbase hUS
  intro z hz
  rcases (hXH z hz).lt_or_eq with him | him
  · exact Or.inl (hsub (Or.inr ⟨hXN z hz, him⟩))
  · rcases lt_or_ge m z.re with hre | hre
    · exact Or.inl (hsub (Or.inl hre))
    · refine Or.inr (Or.inl ⟨⟨m - z.re, by linarith⟩, ?_⟩)
      have hle : ((⟨m - z.re, by linarith⟩ : ℝ≥0) : ℝ) ≤ m + N := by
        show m - z.re ≤ m + N; linarith [hXN z hz]
      rw [zeroCompletion_of_le hle]
      apply Complex.ext
      · simp only [Complex.ofReal_re]
        show m - (m - z.re) = z.re
        ring
      · simp [← him]

/-- **S1 at time `0`** (Convention S1 for the trivial prefix): every compact set of `closure ℍ` is one-sided for a
path starting at a real point. -/
theorem isOneSided_zero {X : Set ℂ} (hX : IsCompact X) (hXH : ∀ z ∈ X, 0 ≤ z.im) {η : ℝ≥0 → ℂ} {m : ℝ}
    (hη0 : η 0 = m) : IsOneSided X η 0 := by
  obtain ⟨M, hM⟩ := hX.isBounded.exists_norm_le
  set N : ℝ := max (M + 1) (|m| + 1) with hN
  have hmN : -N < m := by
    have : |m| + 1 ≤ N := le_max_right _ _
    linarith [neg_abs_le m]
  have hXN : ∀ z ∈ X, -N < z.re := fun z hz => by
    have h1 : M + 1 ≤ N := le_max_left _ _
    have h2 := hM z hz
    have h3 := Complex.abs_re_le_norm z
    linarith [neg_abs_le z.re]
  exact ⟨zeroCompletion m N, isProperCompletion_zeroCompletion hη0 (by linarith),
    subset_closedRightSide_zeroCompletion hmN hXH hXN⟩

/-- **A zero-lifetime switch needs no SB3 input**: the S1-free sewing data with zero available lifetime are a sewing
certificate, because the S1 comparisons are asked only at time `0`. -/
theorem _root_.InteractingSLE.Theorem14.SB.Leaf.HasRelTailGeometry.hasActualTailSewing_zero
    {A S Wrel : Set ℂ} {u : ℝ} {η : ℝ≥0 → ℂ} (hg : Leaf.HasRelTailGeometry A S Wrel u η 0) :
    HasActualTailSewing A S := by
  have hη0 : η 0 = u := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, -⟩ := hg
    exact h
  refine hg.hasActualTailSewing fun γ hγ _ _ s a ha => ?_
  have ha0 : a = 0 := by
    have : (a : ℝ≥0∞) = 0 := le_antisymm ha zero_le
    exact_mod_cast this
  subst ha0
  refine isOneSided_zero ((isCompact_Icc.image hγ.1).union (isCompact_Icc.image Complex.continuous_ofReal))
    ?_ hη0
  rintro z (⟨t, -, rfl⟩ | ⟨x, -, rfl⟩)
  · exact hγ.2.2.1 t
  · simp

end InteractingSLE.Theorem14.SB.Lf
