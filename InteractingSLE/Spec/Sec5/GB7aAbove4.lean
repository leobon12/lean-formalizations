/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GB7aAbove4Path
import InteractingSLE.Spec.Sec5.CfBarrier

/-!
# Lemma GB7a above `κ = 4`: the pathwise half proved, GB7a for every `κ > 0`

Packet PROVE-CFBARRIER2. Main results:

* `gb7aCmpInputAbove4 : CfBarrier.GB7aCmpInputAbove4` — **the pathwise half of Lemma GB7a's proof above `κ = 4`**
  (PROVE-CFBARRIER's named input, now a theorem): almost surely, a visit of the open interval between a right mark `k`
  and the next right mark produces the comparison picture `GB7a.RightCmp` at a rational restart time (no injectivity
  of the trace: `rightCmpPath_of_visit_any`); the left side through the reflected evolution;
* `gb7aEvol_right_any`, `gb7aEvol_left_any` — **Lemma GB7a for every `κ > 0`** (interval barrier for finite words):
  if the cumulative weight up to the mark `k` is at least `κ/2 − 2`, almost surely the trace never visits the interval
  between `k` and the next mark (the probabilistic half is PROVE-CFBARRIER's `CfBarrier.measure_rightCmp_none_eq_zero`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec5.GB7aAbove4

open GB7a

/-! ### The left side -/

section Left

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The comparison picture from a visit, left side, without injectivity**: the right side for the reflected path and
the reflected trace `−η̄`. -/
theorem leftCmpPath_of_visit_any (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR B ζ)
    (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace w ζ η)
    (hlimζ : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    {k : Fin nL} {a : ℝ} (hnext : ∀ j, xL j < xL k → xL j ≤ a)
    (hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ∧ ∃ y ∈ Ioo a (xL k), η t = y) :
    ∃ q : ℚ, RightCmpPath ρR ρL (fun t => -w t) (fun i t => -vR i t) (fun i t => -vL i t) ζ k none
      (∑ i ∈ univ.filter (fun i => xL k ≤ xL i), ρL i) (q : ℝ).toNNReal := by
  have hlim' : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nR → ℝ) (vR₀ : Fin nL → ℝ),
      Tendsto (fun t => ((-w) t, fun i => (fun i => -vR i) i t, fun i => (fun i => -vL i) i t)) (𝓝[<] T)
        (𝓝 (w₀, vL₀, vR₀)) := by
    intro T hT hζ
    obtain ⟨w₀, vL₀, vR₀, hl⟩ := hlimζ T hT hζ
    refine ⟨-w₀, -vR₀, -vL₀, ?_⟩
    have hc : Continuous fun z : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => (-z.1, -z.2.2, -z.2.1) := by
      fun_prop
    exact (hc.tendsto _).comp hl
  have hvis' : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ∧ ∃ y ∈ Ioo ((-xL) k) (-a), LP.reflectC (η t) = y := by
    obtain ⟨t, ht, y, hy, he⟩ := hvis
    refine ⟨t, ht, -y, ⟨by simp only [Pi.neg_apply]; linarith [hy.2], by linarith [hy.1]⟩, ?_⟩
    rw [he]
    simp [LP.reflectC]
  have hnext' : ∀ j, (-xL) k < (-xL) j → -a ≤ (-xL) j := fun j hj => by
    simp only [Pi.neg_apply, neg_lt_neg_iff] at hj
    simp only [Pi.neg_apply, neg_le_neg_iff]
    exact hnext j hj
  obtain ⟨q, hq⟩ := rightCmpPath_of_visit_any hp.reflect (isOrderedForceWord_reflect hord)
    (LP.isGeneratingTrace_reflect hη) hlim' hnext' hvis'
  have e : univ.filter (fun i => (-xL) i ≤ (-xL) k) = univ.filter (fun i => xL k ≤ xL i) :=
    Finset.filter_congr fun i _ => by simp only [Pi.neg_apply, neg_le_neg_iff]
  rw [e] at hq
  exact ⟨q, hq⟩

end Left

/-! ### The evolution level -/

/-- **The pathwise half of Lemma GB7a's proof above `κ = 4`** (PROVE-CFBARRIER's named input, now a theorem). -/
theorem gb7aCmpInputAbove4 : CfBarrier.GB7aCmpInputAbove4.{u} := by
  intro κ hκ4 nL nR xL xR ρL ρR hord Ω mΩ P _ 𝓕 W VL VR B ζ hE η hη
  have hκ : 0 < κ := by linarith
  have hlim := hE.ae_tendsto_threshold hκ
  have hpath := hE.2.2.2.2
  refine ⟨fun k a' _ hnext => ?_, fun k a _ hnext => ?_⟩
  · filter_upwards [hlim, hpath, hη] with ω h2 h3 h4 hvis
    obtain ⟨q, hq⟩ := rightCmpPath_of_visit_any h3 hord h4
      (fun T hT hζ => let ⟨w₀, vL₀, vR₀, hl, _⟩ := h2 T hT hζ; ⟨w₀, vL₀, vR₀, hl⟩) hnext hvis
    exact ⟨q, rightCmp_iff.2 hq⟩
  · filter_upwards [hlim, hpath, hη] with ω h2 h3 h4 hvis
    obtain ⟨q, hq⟩ := leftCmpPath_of_visit_any h3 hord h4
      (fun T hT hζ => let ⟨w₀, vL₀, vR₀, hl, _⟩ := h2 T hT hζ; ⟨w₀, vL₀, vR₀, hl⟩) hnext hvis
    exact ⟨q, rightCmp_iff.2 hq⟩

section Evolution

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Lemma GB7a for an evolution, right side, every `κ > 0`**: if the cumulative weight up to the mark `k` is at least
`κ/2 − 2`, almost surely the trace does not visit the interval between `k` and the next mark. -/
theorem gb7aEvol_right_any (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {k : Fin nR} {a' : ℝ}
    (hnext : ∀ j, xR k < xR j → a' ≤ xR j)
    (hS : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ∀ y ∈ Ioo (xR k) a', η ω t ≠ y := by
  have hin : ∀ᵐ ω ∂P, (∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ ∃ y ∈ Ioo (xR k) a', η ω t = y) →
      ∃ q : ℚ, RightCmp ρL ρR W VL VR ζ k none (∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i)
        (q : ℝ).toNNReal ω := by
    filter_upwards [hE.ae_tendsto_threshold hκ, hE.2.2.2.2, hη] with ω h2 h3 h4 hvis
    obtain ⟨q, hq⟩ := rightCmpPath_of_visit_any h3 hord h4
      (fun T hT hζ => let ⟨w₀, vL₀, vR₀, hl, _⟩ := h2 T hT hζ; ⟨w₀, vL₀, vR₀, hl⟩) hnext hvis
    exact ⟨q, rightCmp_iff.2 hq⟩
  have hnull : P (⋃ q : ℚ, {ω | RightCmp ρL ρR W VL VR ζ k none
      (∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i) (q : ℝ).toNNReal ω}) = 0 :=
    measure_iUnion_null fun q => CfBarrier.measure_rightCmp_none_eq_zero hκ hE hS _
  filter_upwards [hin, measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω hω' t ht y hy he
  exact hω' (mem_iUnion.2 (hω ⟨t, ht, y, hy, he⟩))

/-- **Lemma GB7a for an evolution, left side, every `κ > 0`** (through the reflected evolution). -/
theorem gb7aEvol_left_any (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {k : Fin nL} {a : ℝ}
    (hnext : ∀ j, xL j < xL k → xL j ≤ a)
    (hS : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xL k ≤ xL i), ρL i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ∀ y ∈ Ioo a (xL k), η ω t ≠ y := by
  have hin : ∀ᵐ ω ∂P, (∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ ∃ y ∈ Ioo a (xL k), η ω t = y) →
      ∃ q : ℚ, RightCmp ρR ρL (fun t ω => -W t ω) (fun i t ω => -VR i t ω) (fun i t ω => -VL i t ω) ζ k
        none (∑ i ∈ univ.filter (fun i => xL k ≤ xL i), ρL i) (q : ℝ).toNNReal ω := by
    filter_upwards [hE.ae_tendsto_threshold hκ, hE.2.2.2.2, hη] with ω h2 h3 h4 hvis
    obtain ⟨q, hq⟩ := leftCmpPath_of_visit_any h3 hord h4
      (fun T hT hζ => let ⟨w₀, vL₀, vR₀, hl, _⟩ := h2 T hT hζ; ⟨w₀, vL₀, vR₀, hl⟩) hnext hvis
    exact ⟨q, rightCmp_iff.2 hq⟩
  have hER := IsIntegratedSLEEvolution.reflect hE
  have hnull : P (⋃ q : ℚ, {ω | RightCmp ρR ρL (fun t ω => -W t ω) (fun i t ω => -VR i t ω)
      (fun i t ω => -VL i t ω) ζ k none (∑ i ∈ univ.filter (fun i => xL k ≤ xL i), ρL i)
        (q : ℝ).toNNReal ω}) = 0 :=
    measure_iUnion_null fun q => CfBarrier.measure_rightCmp_none_eq_zero hκ hER hS _
  filter_upwards [hin, measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω hω' t ht y hy he
  exact hω' (mem_iUnion.2 (hω ⟨t, ht, y, hy, he⟩))

end Evolution

end Sec5.GB7aAbove4

end InteractingSLE
