/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FmWord
import InteractingSLE.Spec.Sec7.Lemma78MeanReal

/-!
# D34's second clause, part (a): original heights on the free real ray from the mean identity (one sample)

Worker PROVE-SB2-F3LAW (round 2, target 3, step (H) of handoff §R2.6). At a real point `x` with a neighbourhood
missing the retained set `A`, off the original jumps, the mean identity
`w + u₀ = β.mean ∘ c.1 − χ · c.2.2` on `ℍ \ A` (F3's identity, NOJUMP's premise) has limits along `ℍ \ A`:
`w → 0` (`IsLocalSetMean.ae_tendsto_zero_of_real`), `u₀ → b x`, `c.1 → y` real, `c.2.2 → 0` and `β.mean → β.fn y`
(`isBoundedHarmonicExtension_mean`) at a non-jump `y`. Hence `β.fn y = b x`.

* `neBot_nhdsWithin_diff_of_real`, **`fn_eq_of_meanIdentity_at`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H chiC)

namespace InteractingSLE.Theorem14.SB.Fm

open Restart Exist Exist.StagedLaw

/-- A real point with a ball missing `A` is a limit point of `ℍ \ A`. -/
theorem neBot_nhdsWithin_diff_of_real {A : Set ℂ} {x : ℝ} {r : ℝ} (hr : 0 < r)
    (hdisj : Disjoint (ball (x : ℂ) r) A) : (𝓝[H \ A] (x : ℂ)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot]
  have ht : Tendsto (fun ε : ℝ => (x : ℂ) + (ε : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
    have h0 : Tendsto (fun ε : ℝ => (x : ℂ) + (ε : ℂ) * Complex.I) (𝓝 0) (𝓝 ((x : ℂ) + ((0 : ℝ) : ℂ) *
        Complex.I)) :=
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).tendsto 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < r := by
    have := Iio_mem_nhds hr
    exact nhdsWithin_le_nhds this
  filter_upwards [hev, self_mem_nhdsWithin] with ε hεr hε0
  have hε0' : (0 : ℝ) < ε := hε0
  refine ⟨show (0 : ℝ) < ((x : ℂ) + (ε : ℂ) * Complex.I).im by simpa using hε0', fun hA => ?_⟩
  have hmem : (x : ℂ) + (ε : ℂ) * Complex.I ∈ ball (x : ℂ) r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hε0']
    exact hεr
  exact Set.disjoint_left.1 hdisj hmem hA

/-- **The word's height at the image of a free real point is the original height** (one sample). -/
theorem fn_eq_of_meanIdentity_at (κ : ℝ) {A : Set ℂ} {c : Chart} {β : BoundaryWord} (hβ : β.IsSorted)
    {b : ℝ → ℝ} {jumps : Finset ℝ} {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {w : ℂ → ℝ}
    (hid : EqOn (fun z => w z + u₀ z) (fun z => β.mean (c.1 z) - chiC κ * c.2.2 z) (H \ A))
    {x : ℝ} (hx : x ∉ jumps) {r : ℝ} (hr : 0 < r) (hdisj : Disjoint (ball (x : ℂ) r) A)
    (hw : Tendsto w (𝓝[H \ A] (x : ℂ)) (𝓝 0)) {y : ℝ} (hy : y ∉ β.jumps)
    (hc : Tendsto c.1 (𝓝[H \ A] (x : ℂ)) (𝓝[H] (y : ℂ))) (hl : Tendsto c.2.2 (𝓝[H \ A] (x : ℂ)) (𝓝 0)) :
    β.fn y = b x := by
  have hNe := neBot_nhdsWithin_diff_of_real hr hdisj
  have hle : 𝓝[H \ A] (x : ℂ) ≤ 𝓝[H] (x : ℂ) := nhdsWithin_mono _ sdiff_subset
  have hL : Tendsto (fun z => w z + u₀ z) (𝓝[H \ A] (x : ℂ)) (𝓝 (0 + b x)) :=
    hw.add ((hu₀.2.2 x (by exact_mod_cast hx)).mono_left hle)
  have hm := (Restart.BoundaryWord.isBoundedHarmonicExtension_mean β hβ).2.2 y (by exact_mod_cast hy)
  have hR : Tendsto (fun z => β.mean (c.1 z) - chiC κ * c.2.2 z) (𝓝[H \ A] (x : ℂ))
      (𝓝 (β.fn y - chiC κ * 0)) := (hm.comp hc).sub (hl.const_mul _)
  have hL' : Tendsto (fun z => β.mean (c.1 z) - chiC κ * c.2.2 z) (𝓝[H \ A] (x : ℂ)) (𝓝 (0 + b x)) :=
    hL.congr' (eventually_nhdsWithin_of_forall fun z hz => hid hz)
  have := tendsto_nhds_unique hR hL'
  linarith

end InteractingSLE.Theorem14.SB.Fm
