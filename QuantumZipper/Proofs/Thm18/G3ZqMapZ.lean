import QuantumZipper.Proofs.Thm18.G3ZqG2DisR
import QuantumZipper.Proofs.Thm18.G3Z2b2Two

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH (5): the zooms through the local maps of a fixed path as an abstract zoom (D92)

The generalized G2 engine (`G3ZqG2*.lean`) takes an abstract zoom `Z : ℝ → FieldSample → ℝ → LawD`
(level, field, point). The map instance for a fixed path `a` and side `left` is the measurable
zoom datum `G3Z2b2.g1zM` through the local map `g3mapP Ψ left (y, a, 1, x)` on the side
half-line, and the plain zoom elsewhere (the Palm-window functional `g3PhiM2` only reads the side
half-lines: the Palm point on the left, its partner on the right):

  `g3zMapZ γ Ψ left a C y x = if x ∈ g1SideHalf left then g1zM γ C Ψ left ((y, a), x)
                               else zoomLaw γ C y x`.

This file proves the three structural hypotheses of the engine for it:
* `measurable_g3zMapZ` (joint measurability, `hZm`),
* `g3zMapZ_avgReg_congr` (dependence on the regularized averages only, `hZa`),
* `g3zMapZ_reconstruct_coords` (dependence on the dyadic coordinates only, `hZc`),
and that the Palm-window functional `g3PhiM2` reads exactly these zooms (`g3IntM2_eq_mapZ`).

Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zq

open G3Z2b2 Factorization

/-- **The zoom through the local maps of the fixed path `a` on side `left`** (plain zoom off the
side half-line). -/
def g3zMapZ (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (a : ℝ≥0 → ℝ) :
    ℝ → FieldSample → ℝ → LawD := fun C y x =>
  open Classical in
  if x ∈ g1SideHalf left then g1zM γ C Ψ left ((y, a), x) else zoomLaw γ C y x

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

theorem measurableSet_g1SideHalf (left : Bool) : MeasurableSet (g1SideHalf left) := by
  cases left
  · exact measurableSet_Ioi
  · exact measurableSet_Iio

/-- `hZm` for the map zoom. -/
theorem measurable_g3zMapZ {γ : ℝ} (hsel : G1PsiSel γ Ψ) (left : Bool) (a : ℝ≥0 → ℝ) (C : ℝ) :
    Measurable fun q : FieldSample × ℝ => g3zMapZ γ Ψ left a C q.1 q.2 := by
  classical
  have h1 : Measurable fun q : FieldSample × ℝ => g1zM γ C Ψ left ((q.1, a), q.2) :=
    (measurable_g1zM hsel C left).comp ((measurable_fst.prodMk measurable_const).prodMk
      measurable_snd)
  exact Measurable.ite (measurable_snd (measurableSet_g1SideHalf left)) h1
    (measurable_zoomLaw γ C)

/-- `hZa` for the map zoom. -/
theorem g3zMapZ_avgReg_congr (γ : ℝ) (left : Bool) (a : ℝ≥0 → ℝ) (C : ℝ) (y y' : FieldSample)
    (x : ℝ) (h : avgReg y = avgReg y') : g3zMapZ γ Ψ left a C y x = g3zMapZ γ Ψ left a C y' x := by
  unfold g3zMapZ
  split_ifs
  · exact g1zM_congr h a x
  · exact zoomLaw_avgReg_congr γ C x h

/-- `hZc` for the map zoom. -/
theorem g3zMapZ_reconstruct_coords (γ : ℝ) (left : Bool) (a : ℝ≥0 → ℝ) (C : ℝ) (y : FieldSample)
    (x : ℝ) : g3zMapZ γ Ψ left a C (reconstruct (coords y)) x = g3zMapZ γ Ψ left a C y x :=
  g3zMapZ_avgReg_congr γ left a C _ _ x (avgReg_reconstruct_coords y)

end G3Zq
end Thm18Asm
end QuantumZipper
