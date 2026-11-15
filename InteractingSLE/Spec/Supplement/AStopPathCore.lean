/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopPathSample

/-!
# The pathwise A-stop facts of a retained continuation (item 6 of `AStopSourceInputs`, pathwise)

Packet PROVE-T15-ASTOP-PATH. For a retained continuation (`Supp7.IsRetCont`) with the chart-boundary facts
(`IsAChart`), an untouched word of a fixed force type whose heights next to the tip are the canonical ones
`∓λ − θχ`, the live incident bounds and the jump avoidance of the continued path, and any continuous driver `W` from
`0` generating the canonical A-stopped clock `γ` up to its capacity lifetime `V`
(**`aStop_facts`**):

* `0 < V`;
* the seed is not a threshold (the canonical tip heights give an admissible seed);
* no threshold at any positive capacity time before `V` (Lemma G7, real contacts allowed);
* `γ` avoids the real chart points over `K = O ∪ η([0, a])` at `0 < q < V`;
* at a finite `V`, either the continuation ran to the path's own lifetime with an end point off `K`, or
  `γ V` is a real chart point over `K`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.RLC.AStopPath

open Supp7 Restart PiecewiseConstantBoundaryData MartChar.RealFlow

section Core

variable {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {a : ℝ≥0} {O : Set ℂ} {φ ψ : ℂ → ℂ}

/-- **The pathwise A-stop facts** (see the module docstring). -/
theorem aStop_facts (hR : IsRetCont η ζ x a O φ ψ) (hA : IsAChart ψ (O ∪ η '' Icc 0 a) x)
    {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {c : BoundaryWord} (hu : IsUntouchedWord b jumps (O ∪ η '' Icc 0 a) ψ c)
    (hv : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ y : ℝ, η t = y →
      (y ≤ x → leftLim b y + θ * chiC κ < sleLambda κ) ∧ (x ≤ y → -sleLambda κ < rightLim b y + θ * chiC κ))
    (hj : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ → ∀ y ∈ jumps, y ≠ x → η t ≠ y)
    (hside : ∀ y : ℝ, y ≠ 0 → ψ y ∈ H → ψ y ∉ O → ψ y ∈ η '' Icc 0 a →
      (y < 0 → c.fn y = -sleLambda κ - θ * chiC κ) ∧ (0 < y → c.fn y = sleLambda κ - θ * chiC κ))
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (htype : c ∈ FCDet.typeSet κ θ nL nR ρL ρR)
    {W : ℝ≥0 → ℝ} (hWc : Continuous W) (hW0 : W 0 = 0)
    (hg : IsGeneratingTrace W (canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0)
      (canonRetPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0)) :
    0 < canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0 ∧
    ¬ ForceWord.ThresholdCondition ρL ρR 0 (FCDet.typeXL κ θ nL nR ρL ρR c) (FCDet.typeXR κ θ nL nR ρL ρR c) ∧
    (∀ q : ℝ≥0, 0 < q →
      (q : ℝ≥0∞) < canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0 →
      ¬ ForceWord.ThresholdCondition ρL ρR (W q)
        (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-FCDet.typeXL κ θ nL nR ρL ρR c i) q)
        (fun j => rightImg (fun s : ℝ => W s.toNNReal) (FCDet.typeXR κ θ nL nR ρL ρR c j) q)) ∧
    (∀ q : ℝ≥0, 0 < q →
      (q : ℝ≥0∞) < canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0 →
      canonRetPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0 q ∉ aSet ψ (O ∪ η '' Icc 0 a)) ∧
    (canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0 ≠ ⊤ →
      (contStop η ζ a (O ∪ η '' Icc 0 a) = ζ ∧ η ζ.toNNReal ∉ O ∪ η '' Icc 0 a) ∨
        canonRetPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0
          (canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0).toNNReal ∈
          aSet ψ (O ∪ η '' Icc 0 a)) := by
  obtain ⟨hl, hr⟩ := seed_limits hR hA hside
  refine ⟨canonRetLife_pos hR, ?_, fun q hq0 hq => not_threshold_canon hR hA hκ hb hu hv hj htype hWc hW0 hg hq0 hq,
    fun q hq0 hq => notMem_of_lt_canonRetLife hR (fun w hw => hw.2) hq0 hq,
    mem_of_canonRetLife_ne_top hR fun w h1 h2 => ⟨h1, h2⟩⟩
  exact FCPlumb.not_threshold_type_of_admissible hκ htype (by rw [hl, hr]; exact isAdmissibleSeed_canonical hκ θ)

end Core

end InteractingSLE.RLC.AStopPath
