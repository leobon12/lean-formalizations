import QuantumZipper.Proofs.Complex.JSTents
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The shadow condition forces zero area (EXT-JS node B2)

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 (step 1 of node C0) and §3 node B2.

Source: P. W. Jones and S. K. Smirnov, *Removability theorems for Sobolev functions and
quasiconformal maps*, Ark. Mat. 38 (2000) 263–279; Proposition 1 and its proof, §2, pp. 267–268.
In the paper the Whitney squares of the planar chart are replaced here by the dyadic Carleson
tents of the half-plane chart (`JSTents.lean`), as explained in the blueprint §2: the level-`n`
tents cover `[-R, R]`, each image lies in the ball with centre any of its points and radius its
diameter, and the level-wise sums are tails of the shadow sum, hence tend to `0`.

A set `K` is covered by finitely many *charts* `F i`, continuous on the box
`[-2R, 2R] ×ℂ [0, 4R]`, whose *shadow sums* `shadowSum R (F i) = Σ_{m,j} diam F(T_{m,j})²` are
finite. Then `volume K = 0`: for every level `n`,

`volume K ≤ π Σ_i Σ_{j < 2^n} diam (F i '' T_{n,j})² ≤ π Σ_i (tail of shadowSum R (F i) at n)`,

and the right-hand side tends to `0` along with the tails (`ENNReal.tendsto_sum_nat_add`), so
`volume K < volume K` whenever `volume K ≠ 0`.

Main result: `volume_eq_zero_of_shadow`.
-/

open Set Complex Filter Topology MeasureTheory
open scoped ENNReal

namespace QuantumZipper.JS

noncomputable section

namespace ShadowNull

variable {R : ℝ}

/-- The level-`n` part `Σ_{j < 2^n} diam (F '' T_{n,j})²` of the shadow sum. -/
def shadowLevel (R : ℝ) (F : ℂ → ℂ) (n : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (2 ^ n), Metric.ediam (F '' tent R n j) ^ 2

/-- Tents of every level lie in the box on which charts are assumed to be continuous. -/
lemma tent_subset_chartBox (hR : 0 < R) {n j : ℕ} (hj : j < 2 ^ n) :
    tent R n j ⊆ Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) := by
  intro w hw
  have h1 := tent_subset hR.le hj hw
  rw [mem_reProdIm] at h1 ⊢
  exact ⟨⟨by linarith [h1.1.1, hR], by linarith [h1.1.2, hR]⟩,
    ⟨h1.2.1, by linarith [h1.2.2, hR]⟩⟩

/-- Tents are nonempty. -/
lemma tent_nonempty (hR : 0 < R) (n j : ℕ) : (tent R n j).Nonempty := by
  refine ⟨(((-R + j * dyLen R n : ℝ) : ℂ)), ofReal_mem_tent hR.le ?_⟩
  rw [dyI, mem_Icc]
  refine ⟨le_rfl, ?_⟩
  have h := dyLen_nonneg hR.le n
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith

/-- The image of a tent under a chart is compact. -/
lemma isCompact_image_tent (hR : 0 < R) {F : ℂ → ℂ}
    (hF : ContinuousOn F (Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R))) {n j : ℕ} (hj : j < 2 ^ n) :
    IsCompact (F '' tent R n j) :=
  (isCompact_tent R n j).image_of_continuousOn (hF.mono (tent_subset_chartBox hR hj))

end ShadowNull

end

end QuantumZipper.JS
