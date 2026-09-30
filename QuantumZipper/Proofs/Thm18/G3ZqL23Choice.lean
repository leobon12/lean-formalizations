import QuantumZipper.Proofs.Thm18.G3ZqL20TypQ
import QuantumZipper.Proofs.Thm18.G3ZqL10Cert
import QuantumZipper.Proofs.GFF.CircleContinuity
import QuantumZipper.Proofs.Thm18.G3ZqL11Reg
import QuantumZipper.Proofs.Thm18.G3ZqTop
import QuantumZipper.Proofs.Thm18.G3ZqPath
import QuantumZipper.Proofs.Thm18.G3ZqFLeaf
import QuantumZipper.Proofs.Thm18.G3ZqG3LRegG
import QuantumZipper.Proofs.Thm18.G3ZqG3Unif
import QuantumZipper.Proofs.Thm18.G3ZqSTop
import QuantumZipper.Proofs.Thm18.G3ZqS2Top
import QuantumZipper.Proofs.Thm18.G3ZqL21Pos

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (23): the local area condition from Z-REG's area-only regularity

The pulled-back field of the map zoom has the dyadic coordinates of `zoomFieldVia` (good path,
`G3Z2b2.g3coordsM_eq`). Under the `RegShift` clauses these are the values of the coordinate-changed
field `v = coordChange (translate y x) (local map) Q` (`zoomFieldVia_eq_coordChange_addConst`).
Hence `LocAreaQ` of the pulled-back field follows from the area-only regularity `ChoiceRegularA`
of `v` (Z-REG, D93) plus positive area proxy of `v` on half-balls about `0`
(`locAreaQ_of_choiceA`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqL

open Factorization G3Z2b2 G3Zq

/-- `LocAreaQ` only sees the dyadic values and the regularized averages. -/
theorem locAreaQ_congr {γ : ℝ} {u v : FieldSample}
    (hraw : ∀ (n k : ℕ) (z : ℂ), u (foldedCircle (dyadicRoundC n z) (radius k)) =
      v (foldedCircle (dyadicRoundC n z) (radius k)))
    (havg : avgReg u = avgReg v) (h : LocAreaQ γ v) : LocAreaQ γ u := by
  obtain ⟨ρ, hρ, k₀, hc, hp⟩ := h
  refine ⟨ρ, hρ, k₀, fun k hk z hz => ?_, fun q hq hqρ => ?_⟩
  · obtain ⟨l, hl⟩ := hc k hk z hz
    exact ⟨l, by simpa only [hraw] using hl⟩
  · obtain ⟨n, w, hw, ht⟩ := hp q hq hqρ
    exact ⟨n, w, hw, by rw [areaApprox_congr havg]; exact ht⟩

/-- **`LocAreaQ` of the pulled-back field from `RegShift` and `ChoiceRegularA`.** -/
theorem locAreaQ_of_choiceA {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hsel : G1PsiSel γ Ψ)
    {side : Bool} {a : ℝ≥0 → ℝ} (hac : Continuous a) (hs : IsSimpleChord (pathTrace (γ ^ 2) a))
    {y : FieldSample} {x : ℝ}
    (hs1 : ∀ (d : ℂ) (j : ℕ), E1.RegShift (translate y (x : ℂ))
      ((foldedCircle d (radius j)).map (g3mapP Ψ side (y, a, 1, x))))
    (hcr : G1.ChoiceRegularA γ (addConst (translate y (x : ℂ)) (0 / γ)) (g3mapP Ψ side (y, a, 1, x)))
    (hpos : ∀ q : ℝ, 0 < q → 0 < areaProxy γ
      (coordChange (addConst (translate y (x : ℂ)) (0 / γ)) (g3mapP Ψ side (y, a, 1, x)) (Qc γ)) q) :
    LocAreaQ γ (g3zqPull γ Ψ side a y x) := by
  set v := coordChange (addConst (translate y (x : ℂ)) (0 / γ)) (g3mapP Ψ side (y, a, 1, x)) (Qc γ)
    with hv
  have hm : Measurable (g3mapP Ψ side (y, a, 1, x)) :=
    (g3mapB_props hsel hac hs side one_pos (x / 1)).2.2
  have hco : g3coordsM γ 0 Ψ side (y, a, 1, x) = coords v := by
    rw [g3coordsM_eq (p := (y, a, 1, x)) hsel 0 side hac hs one_pos]
    funext i
    exact zoomFieldVia_eq_coordChange_addConst γ 0 y x hm _ (hs1 _ _)
  have hu : g3zqPull γ Ψ side a y x = reconstruct (coords v) := by
    unfold g3zqPull; rw [hco]
  obtain ⟨hreg, -, hA, -, -⟩ := hcr
  have hloc : LocAreaQ γ v :=
    locAreaQ_of_locArea (locArea_of_areaReg ⟨hreg, hA⟩ hpos)
  rw [hu]
  refine locAreaQ_congr (fun n k z => ?_) (avgReg_reconstruct_coords v) hloc
  obtain ⟨i, hi⟩ := dyadicIndex_surj n k z
  have := reconstruct_coords_apply v i
  rw [hi] at this
  exact this

end G3ZqL
end Thm18Asm
end QuantumZipper
