/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxDil6

/-!
# GW2's open lines: the stage chart's two normalizations, set-level

Packet PROVE-GW2-STAGEMEAN, R120 round (the stage-start dilation, stage side). Deterministic:

* `fwdMap_mem_shift_hull` (Loewner semigroup): a point of `K_{a+v} ∖ K_a` is sent by `f_a` into the hull of the
  shifted driver at `v`;
* **`stage_near_zero`**: for a stage chart `c₀.loewner R a` whose shape at the stage times `u n` reads the union
  `B (u n)` off the relative hull at the clock `A (u n) → a`, the `cL`-preimages of sets inside the launch images
  of `B (u n)` are sent near `0`;
* **`stage_far`**: the `cL`-preimages of the conditional counterflow's continuation, when they lie in the original
  counterflow's continuation, are sent far away (`stgChart_continuation_far`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW2Omx

open Supp8.GB6 (relMap gb6Rec)
open Supp8.Q3Rel (invHull)

/-- **Loewner semigroup on hulls**: `f_a(K_{a+v} ∖ K_a)` lies in the hull of the shifted driver at `v`. -/
theorem fwdMap_mem_shift_hull {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {a v : ℝ} (ha : 0 ≤ a) (hv : 0 ≤ v)
    {y : ℂ} (hy : y ∈ fwdHull U (a + v)) (hya : y ∉ fwdHull U a) :
    fwdMap U a y ∈ fwdHull (fun r => U (a + r) - U a) v := by
  have hyH : y ∈ H := hy.1
  have hfH : fwdMap U a y ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hU ha ⟨hyH, hya⟩
  have hinv : fwdMapInv U a (fwdMap U a y) = y := QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 ha ⟨hyH, hya⟩
  by_contra hK
  have hy' : y ∈ H \ fwdHull U (a + v) := by
    rw [← Sec5.Markov.image_fwdMapInv_diff_fwdHull hU hU0 ha hv]
    exact ⟨_, ⟨hfH, hK⟩, hinv⟩
  exact hy'.2 hy

/-- **The stage chart sends the launch preimages of the new explored part near `0`.** -/
theorem stage_near_zero {cL c₀ : Chart} (hcL : cL.IsConformal) (hc₀ : c₀.IsConformal) {R : ℝ → ℝ}
    (hR : Continuous R) (hR0 : R 0 = 0) {a : ℝ} (ha : 0 ≤ a) {u : ℕ → ℝ} {A : ℕ → ℝ} (hAa : ∀ n, a ≤ A n)
    (hA : Tendsto A atTop (𝓝 a)) {B : ℕ → Set ℂ}
    (hshape : ∀ n, H \ B n = c₀.2.1 '' (H \ fwdHull R (A n))) {V : ℝ → ℝ}
    (hunion : ∀ n, fwdHull V (u n) ⊆ cL.1 '' (B n ∩ (cL.dom : Set ℂ))) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ cL.2.1 '' fwdHull V (u n) ∩ ((c₀.loewner R a).dom : Set ℂ),
      ‖(c₀.loewner R a).1 z‖ < ε := by
  intro ε hε
  set Rs : ℝ → ℝ := fun r => R (a + r) - R a with hRs
  have hRsc : Continuous Rs := (hR.comp (continuous_const.add continuous_id)).sub continuous_const
  have hRs0 : Rs 0 = 0 := by simp [hRs]
  obtain ⟨δ, hδ, hball⟩ := GW4Ident.eventually_fwdHull_subset_closedBall hRsc hRs0 (half_pos hε)
  have hAδ : ∀ᶠ n in atTop, A n - a < δ := by
    have h1 : Tendsto (fun n => A n - a) atTop (𝓝 0) := by
      simpa using hA.sub_const a
    exact (tendsto_order.1 h1).2 δ hδ
  filter_upwards [hAδ] with n hn
  rintro z ⟨⟨w, hw, rfl⟩, hzd⟩
  obtain ⟨hzc, hy⟩ := loewner_dom_fwd hc₀ hR hR0 ha hzd
  -- the point lies in `B n`
  obtain ⟨z', hz', hz'w⟩ := hunion n hw
  have hwH : w ∈ H := by
    rw [← hz'w]
    exact hcL.fwd_mem hz'.2
  have hzz : cL.2.1 w = z' := by rw [← hz'w, hcL.inv_fwd hz'.2]
  have hzB : cL.2.1 w ∈ B n := hzz ▸ hz'.1
  -- its relative point lies in the relative hull at `A n`
  have hyA : c₀.1 (cL.2.1 w) ∈ fwdHull R (A n) := by
    by_contra hK
    have hmem : cL.2.1 w ∈ c₀.2.1 '' (H \ fwdHull R (A n)) :=
      ⟨c₀.1 (cL.2.1 w), ⟨hc₀.fwd_mem hzc, hK⟩, hc₀.inv_fwd hzc⟩
    rw [← hshape n] at hmem
    exact hmem.2 hzB
  have hyA' : c₀.1 (cL.2.1 w) ∈ fwdHull R (a + (A n - a)) := by
    rw [add_sub_cancel]
    exact hyA
  have hmem := fwdMap_mem_shift_hull hR hR0 ha (sub_nonneg.2 (hAa n)) hyA' hy.2
  have hle : A n - a ≤ δ := hn.le
  rcases (sub_nonneg.2 (hAa n)).lt_or_eq with hpos | hzero
  · have hb := hball (A n - a) hpos hle hmem
    change ‖fwdMap R a (c₀.1 (cL.2.1 w))‖ < ε
    have : ‖fwdMap R a (c₀.1 (cL.2.1 w))‖ ≤ ε / 2 := by simpa [dist_zero_right] using hb
    linarith
  · rw [← hzero, QuantumZipper.RS.fwdHull_zero_eq_empty hRsc] at hmem
    exact absurd hmem (notMem_empty _)

/-- **The stage chart sends the launch preimages of the conditional counterflow's continuation far away.** -/
theorem stage_far {Ω : Type*} {s : ℝ≥0} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hW0 : W 0 ω = 0) (hWc : Continuous fun t => W t ω) (hs : (s : ℝ≥0∞) < ζ ω)
    {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) (a : ℝ≥0) {S₁ : ℕ → Set ℂ} {w : ℕ → ℝ}
    (hw : ∀ n, 0 < w n) (hw0 : Tendsto w atTop (𝓝 0))
    (hsub : ∀ n, S₁ n ⊆ invHull (fun u : ℝ => W u.toNNReal ω) (s + w n) \
      invHull (fun u : ℝ => W u.toNNReal ω) s) :
    ∀ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ S₁ n ∩
        ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec s W ζ ω)) R a).dom : Set ℂ),
      M < ‖(GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec s W ζ ω)) R a).1 z‖ := by
  intro M
  obtain ⟨δ, hδ, hfar⟩ := stgChart_continuation_far hW0 hWc hs hR hR0 a M
  filter_upwards [(tendsto_order.1 hw0).2 δ hδ] with n hn
  rintro z ⟨hz, hzd⟩
  exact hfar (w n) (hw n) hn.le z (hsub n hz) hzd

end InteractingSLE.Theorem14.GW2Omx
