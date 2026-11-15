/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIIdent
import InteractingSLE.Spec.Restart.FlowStopIdentCMICut

/-!
# The coupling means of the two flow-line words, and the cutoff in the seed chart

Packet PROVE-L1-CMI, step (c) of `planning/handoffs/PROVE-G3SRC.md` §4.1 (the deterministic mean identity), word
half, and the translation of the cutoff into the chart of the seed:

* **`couplingMean_flowLine_sub`**: for mark positions read off the initial positions (`ΦL`, `ΦR`, on the correct sides
  of the driver), the difference of the frozen coupling means of the `bR` and `b` flow-line words is the arg sum over
  the marks off `O`, evaluated at `f_t(z)` (`Ito.couplingMean_eq_meanHarmonic` and `meanHarmonic_flowLine_sub`);
* `CMCut.shift F y`: the cutoff read in the chart `z ↦ z + y` (real `y`), with `src`, `greenDensity` and the arg sum
  translated (`CMCut.shift_f`, `CMCut.greenDensity_shift`, `argSum0_shift`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate Laplacian

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentCMI

open QuantumZipper (H fwdMap)

/-! ### The coupling means of the two words -/

section Means

variable {κ : ℝ} {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ} {O : Set ℝ}

/-- **The difference of the coupling means of the two flow-line words** at time `t`, for mark positions read off the
initial positions, is the arg sum over the marks off `O` at `f_t(z)`. -/
theorem couplingMean_flowLine_sub (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR Ĵ) (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x)
    [DecidablePred (· ∈ O)] {y : ℝ} (hy : y ∈ O) (θ : ℝ) (ΦL ΦR : ℝ → ℝ)
    (hLR : ∀ i, ΦL (flowLineXL bR Ĵ y i) ≤ 0) (hRR : ∀ j, 0 ≤ ΦR (flowLineXR bR Ĵ y j))
    (hL : ∀ i, ΦL (flowLineXL b J y i) ≤ 0) (hR : ∀ j, 0 ≤ ΦR (flowLineXR b J y j)) {uR u : ℂ → ℝ}
    (huR : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ bR Ĵ y θ) (flowLineRhoR κ bR Ĵ y θ)
        (fun i => ΦL (flowLineXL bR Ĵ y i)) (fun j => ΦR (flowLineXR bR Ĵ y j)))
      (forceJumpSet (fun i => ΦL (flowLineXL bR Ĵ y i)) (fun j => ΦR (flowLineXR bR Ĵ y j))) uR)
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ)
        (fun i => ΦL (flowLineXL b J y i)) (fun j => ΦR (flowLineXR b J y j)))
      (forceJumpSet (fun i => ΦL (flowLineXL b J y i)) (fun j => ΦR (flowLineXR b J y j))) u)
    {w : ℝ → ℝ} {t : ℝ} {z : ℂ} (hz : fwdMap w t z ∈ H) :
    couplingMean κ w t uR z - couplingMean κ w t u z =
      ∑ p ∈ offMarks J Ĵ O, ((jmp bR p - jmp b p) * (if y < p then 1 else 0) -
        (jmp bR p - jmp b p) / Real.pi *
          Complex.arg (fwdMap w t z - (((if p < y then ΦL (p - y) else ΦR (p - y)) : ℝ) : ℂ))) := by
  rw [Ito.couplingMean_eq_meanHarmonic hLR hRR huR hz, Ito.couplingMean_eq_meanHarmonic hL hR hu hz]
  rw [← meanHarmonic_flowLine_sub hκ hb hbR hO hbO hy θ ΦL ΦR (fwdMap w t z)]
  ring

end Means

/-! ### The cutoff in the chart of the seed -/

namespace CMCut

variable (F : CMCut)

/-- **The cutoff read in the chart `z ↦ z + y`** (`y` real). -/
def shift (y : ℝ) : CMCut where
  f := fun z => F.f (z + y)
  smooth := F.smooth.comp (contDiff_id.add contDiff_const)
  compact := F.compact.comp_homeomorph (Homeomorph.addRight (y : ℂ))
  odd := fun z => by
    have e : conj z + (y : ℂ) = conj (z + y) := by rw [map_add, Complex.conj_ofReal]
    show F.f (conj z + (y : ℂ)) = -F.f (z + y)
    rw [e, F.odd]

@[simp] theorem shift_f (y : ℝ) (z : ℂ) : (F.shift y).f z = F.f (z + y) := rfl

theorem greenDensity_shift (y : ℝ) (z : ℂ) :
    QuantumZipper.K3.greenDensity (F.shift y).f z = QuantumZipper.K3.greenDensity F.f (z + y) := by
  have e : (F.shift y).f = fun w => F.f (w + (y : ℂ)) := rfl
  simp only [QuantumZipper.K3.greenDensity, e]
  congr 1
  have hΔ : Δ (fun w => F.f (w + (y : ℂ))) = fun w => Δ F.f (w + (y : ℂ)) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
      InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    funext w
    simp only [iteratedFDeriv_comp_add_right]
  rw [hΔ]

end CMCut

/-- **The arg sum in the chart of the seed**: marks shifted by `−y`. -/
theorem argSum0_shift {ι : Type*} [Fintype ι] (p c : ι → ℝ) (c₀ y : ℝ) (z : ℂ) :
    GB7a.argSum0 (fun j => p j - y) c c₀ z = GB7a.argSum0 p c c₀ (z + y) := by
  simp only [GB7a.argSum0]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  push_cast
  ring

end FlowStopIdentCMI

end Restart

end InteractingSLE
