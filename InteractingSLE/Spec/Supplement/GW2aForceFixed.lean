/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aForcePath
import InteractingSLE.Spec.Supplement.GW2aForceBessel
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution

/-!
# At a fixed time, a force collision of an integrated evolution is almost surely an absorbed merge

Packet PROVE-GW2A-FORCE (input of `FlowFixedTimeInteriorStatement`). For an integrated `SLE_κ(ρ)` evolution with an
ordered force word, `κ > 0`, and a deterministic time `t > 0`, almost surely on `{t < ζ}`:

* every right collision `V^{j,R}_t = W_t` is an absorbed merge (`AbsorbedMergeR`);
* every left collision `V^{i,L}_t = W_t` is an absorbed merge on the left (`AbsorbedMergeL`)

(`ae_absorbedMerge_of_collision`). The pathwise reduction (`absorbedMergeR_of_collision`) needs, for all rationals
`q, c > 0` with `q⁺ < t`, that the Bessel process with coefficient `c/(2κ)` from `0`, driven by the Brownian increments
`∓(B_{q⁺+s} − B_{q⁺})`, is nonzero at `t − q⁺`. Each of these countably many events has probability one
(`Bessel.measure_besselProc_zero_eq_zero`; the increments form a pre-Brownian motion, Mathlib's
`IsPreBrownianReal.shift`/`.neg`, of a continuous version of `B`, QuantumZipper's `RS.exists_good_version0`). The left
side is the right side of the reflected path (`IsIntegratedSLEPath.reflect`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW2aForce

open Sec2

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The partial sum `S_k = ∑_{i ≤ k} ρ_i` of the left weights (in the order away from the driver). -/
def partialL (ρL : Fin nL → ℝ) (k : Fin nL) : ℝ := ∑ i ∈ univ.filter (fun i : Fin nL => i ≤ k), ρL i

/-- **An absorbed merge on the left at time `t`**: two consecutive left marks `k, k+1` on the driver at `t` with
`2 + S_k ≤ 0` that are unmerged at every earlier time. -/
def AbsorbedMergeL (ρL : Fin nL → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (t : ℝ≥0) : Prop :=
  ∃ k k' : Fin nL, k'.val = k.val + 1 ∧ 2 + partialL ρL k ≤ 0 ∧ vL k' t = w t ∧ ∀ s < t, vL k' s < vL k s

/-- **The left side by reflection** (pathwise): with the Bessel paths driven by `s ↦ b(q⁺+s) − b(q⁺)` nonzero at
`t − q⁺`, every left collision at `t` is an absorbed merge on the left. -/
theorem absorbedMergeL_of_collision (hκ : 0 < κ) (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hF : IsOrderedForceWord xL xR) {t : ℝ≥0} (ht : 0 < t) (htζ : (t : ℝ≥0∞) < ζ) (X : ℚ → ℚ → ℝ≥0 → ℝ)
    (hX : ∀ q c : ℚ, 0 < c → (q : ℝ).toNNReal < t →
      Bessel.IsBesselPath ((c : ℝ) / (2 * κ)) 0 (fun s => b ((q : ℝ).toNNReal + s) - b (q : ℝ).toNNReal)
        (X q c) ∧ X q c (t - (q : ℝ).toNNReal) ≠ 0)
    {j : Fin nL} (hj : vL j t = w t) : AbsorbedMergeL ρL w vL t := by
  have hF' : IsOrderedForceWord (-xR) (-xL) :=
    ⟨fun _ _ h => neg_le_neg (hF.2.2.1 h), fun i => neg_nonpos.2 (hF.2.2.2 i),
      fun _ _ h => neg_le_neg (hF.1 h), fun i => neg_nonneg.2 (hF.2.1 i)⟩
  have hX' : ∀ q c : ℚ, 0 < c → (q : ℝ).toNNReal < t →
      Bessel.IsBesselPath ((c : ℝ) / (2 * κ)) 0
        (fun s => -((-b) ((q : ℝ).toNNReal + s) - (-b) (q : ℝ).toNNReal)) (X q c) ∧
        X q c (t - (q : ℝ).toNNReal) ≠ 0 := by
    intro q c hc hq
    have hfun : (fun s => -((-b) ((q : ℝ).toNNReal + s) - (-b) (q : ℝ).toNNReal)) =
        fun s => b ((q : ℝ).toNNReal + s) - b (q : ℝ).toNNReal := by
      funext s; simp only [Pi.neg_apply]; ring
    rw [hfun]
    exact hX q c hc hq
  obtain ⟨k, k', hk', hS, hcol, hlt⟩ := absorbedMergeR_of_collision hκ hp.reflect hF' ht htζ X hX'
    (j := j) (by simp only [Pi.neg_apply, hj])
  refine ⟨k, k', hk', hS, ?_, fun s hs => ?_⟩
  · simpa only [Pi.neg_apply, neg_inj] using hcol
  · have := hlt s hs
    simp only [Pi.neg_apply, neg_lt_neg_iff] at this
    exact this

/-! ### The probabilistic statement -/

section Prob

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζω : Ω → ℝ≥0∞}

/-- The Brownian increments after `a`. -/
def incr (B : ℝ≥0 → Ω → ℝ) (a : ℝ≥0) : ℝ≥0 → Ω → ℝ := fun s ω => B (a + s) ω - B a ω

/-- **At a fixed time, every force collision of an integrated evolution is almost surely an absorbed merge.** -/
theorem ae_absorbedMerge_of_collision [IsProbabilityMeasure P] (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζω) {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ζω ω →
      (∀ j : Fin nR, VR j t ω = W t ω → AbsorbedMergeR ρR (fun s => W s ω) (fun i s => VR i s ω) t) ∧
      (∀ i : Fin nL, VL i t ω = W t ω → AbsorbedMergeL ρL (fun s => W s ω) (fun i s => VL i s ω) t) := by
  obtain ⟨B', hB'm, hB'c, -, hB'bm, hB'eq⟩ := QuantumZipper.RS.exists_good_version0 hE.1.1
  -- the increments are pre-Brownian with continuous paths
  have hinc : ∀ a : ℝ≥0, IsPreBrownianReal (incr B' a) P := fun a => hB'bm.toIsPreBrownianReal.shift a
  have hincm : ∀ a s, Measurable (incr B' a s) := fun a s => (hB'm _).sub (hB'm _)
  have hincc : ∀ a ω, Continuous (incr B' a · ω) := fun a ω =>
    ((hB'c ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hninc : ∀ a : ℝ≥0, IsPreBrownianReal (-incr B' a) P := fun a => (hinc a).neg
  have hnincm : ∀ a s, Measurable ((-incr B' a) s) := fun a s => (hincm a s).neg
  have hnincc : ∀ a ω, Continuous ((-incr B' a) · ω) := fun a ω => (hincc a ω).neg
  -- the countably many Bessel events
  have hbes : ∀ (β : ℝ≥0 → ℝ≥0 → Ω → ℝ), (∀ a, IsPreBrownianReal (β a) P) → (∀ a s, Measurable (β a s)) →
      (∀ a ω, Continuous (β a · ω)) → ∀ q c : ℚ, ∀ᵐ ω ∂P, 0 < c → (q : ℝ).toNNReal < t →
        Bessel.IsBesselPath ((c : ℝ) / (2 * κ)) 0 (fun s => β (q : ℝ).toNNReal s ω)
          (fun s => Bessel.besselProc ((c : ℝ) / (2 * κ)) 0 (β (q : ℝ).toNNReal) s ω) ∧
        Bessel.besselProc ((c : ℝ) / (2 * κ)) 0 (β (q : ℝ).toNNReal) (t - (q : ℝ).toNNReal) ω ≠ 0 := by
    intro β hβ hβm hβc q c
    by_cases hc : (0 : ℚ) < c
    · have hc' : 0 < (c : ℝ) / (2 * κ) := div_pos (by exact_mod_cast hc) (by positivity)
      by_cases hq : (q : ℝ).toNNReal < t
      · have hne : t - (q : ℝ).toNNReal ≠ 0 := (tsub_pos_of_lt hq).ne'
        have h0 := Bessel.measure_besselProc_zero_eq_zero (hβ (q : ℝ).toNNReal) (hβm (q : ℝ).toNNReal)
          (hβc (q : ℝ).toNNReal) hc' hne
        filter_upwards [Bessel.ae_isBesselPath (hβ (q : ℝ).toNNReal) (hβc (q : ℝ).toNNReal)
          (hβm (q : ℝ).toNNReal) hc' le_rfl,
          measure_eq_zero_iff_ae_notMem.1 h0] with ω h1 h2 _ _
        exact ⟨h1, h2⟩
      · exact Eventually.of_forall fun ω _ h => absurd h hq
    · exact Eventually.of_forall fun ω h => absurd h hc
  have hR := ae_all_iff.2 fun q => ae_all_iff.2 fun c => hbes (fun a => -incr B' a) hninc hnincm hnincc q c
  have hL := ae_all_iff.2 fun q => ae_all_iff.2 fun c => hbes (fun a => incr B' a) hinc hincm hincc q c
  filter_upwards [hE.2.2.2.2, hB'eq, hR, hL] with ω hp heq hRω hLω htζ
  have hb : ∀ a s, incr B' a s ω = B (a + s) ω - B a ω := fun a s => by simp only [incr, heq]
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · refine absorbedMergeR_of_collision hκ hp hF ht htζ
      (fun q c s => Bessel.besselProc ((c : ℝ) / (2 * κ)) 0 (-incr B' (q : ℝ).toNNReal) s ω)
      (fun q c hc hq => ?_) hj
    obtain ⟨h1, h2⟩ := hRω q c hc hq
    have hfun : (fun s => (-incr B' (q : ℝ).toNNReal) s ω) =
        fun s => -(B ((q : ℝ).toNNReal + s) ω - B (q : ℝ).toNNReal ω) := by
      funext s; simp only [Pi.neg_apply, hb]
    rw [hfun] at h1
    exact ⟨h1, h2⟩
  · refine absorbedMergeL_of_collision hκ hp hF ht htζ
      (fun q c s => Bessel.besselProc ((c : ℝ) / (2 * κ)) 0 (incr B' (q : ℝ).toNNReal) s ω)
      (fun q c hc hq => ?_) hi
    obtain ⟨h1, h2⟩ := hLω q c hc hq
    have hfun : (fun s => incr B' (q : ℝ).toNNReal s ω) =
        fun s => B ((q : ℝ).toNNReal + s) ω - B (q : ℝ).toNNReal ω := by
      funext s; exact hb _ _
    rw [hfun] at h1
    exact ⟨h1, h2⟩

end Prob

end GW2aForce

end Theorem14

end InteractingSLE
