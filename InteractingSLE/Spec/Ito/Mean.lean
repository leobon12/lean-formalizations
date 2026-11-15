import InteractingSLE.Impl.ForceBoundaryData
import InteractingSLE.Frozen.Spec.couplingMean
import InteractingSLE.Frozen.Spec.forceBoundaryData
import InteractingSLE.Frozen.Spec.forceJumpSet
import InteractingSLE.Frozen.Spec.IsBoundedHarmonicExtension

/-!
# The mean of Theorem 1.1 is the imaginary part of (2.5)

Packet PROVE-T11-ITO (Specification §3.3, L500: "let `𝔥*_t(z)` be given by the physically normalized expression
in (2.5)"; proof of Theorem 2.4, `source/spec/p001-048.md` L830–L834). Graph node `SPEC.thm-1.1#mean-explicit-formula`.

For centred force-point positions `vL i ≤ 0 ≤ vR i` every bounded harmonic extension `u` of the frozen
`forceBoundaryData κ ρL ρR vL vR` equals, on `ℍ`,

`meanHarmonic κ ρL ρR vL vR w = (1/√κ) (π (1 + ∑ ρR) − 2 arg w − ∑ ρL i arg (w − vL i) − ∑ ρR i arg (w − vR i))`

(`eqOn_meanHarmonic`), the imaginary part of the bracket in (2.5) evaluated at `w = f_t(z)`, `vᵢ = Vᵢ − W`
(`g_t(z) − V_t^j = f_t(z) − (V_t^j − W_t)`). Consequently the frozen `couplingMean` is
`meanHarmonic (f_t z) − χ Im logDerivFwd`, i.e. `𝔥_t(z) = Im H_t(z)` (`couplingMean_eq_meanHarmonic`).
The proof is the uniqueness half of the companion theorem (`Impl.eqOn_of_isBoundedHarmonicExtension`) and the
explicit extension `Impl.forceExt` of PROVE-T11-COMP.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE

namespace Ito

variable {nL nR : ℕ}

/-- The force word with weights `(ρL; ρR)` (positions unused by the boundary data). -/
def weightWord (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Impl.ForceWord where
  nL := nL
  nR := nR
  xL := fun _ => 0
  xR := fun _ => 0
  ρL := ρL
  ρR := ρR
  antitone_xL := fun _ _ _ => le_rfl
  xL_nonpos := fun _ => le_rfl
  monotone_xR := fun _ _ _ => le_rfl
  xR_nonneg := fun _ => le_rfl

/-- The explicit harmonic function: `Im` of the bracket of (2.5) at centred positions `(vL; vR)`. -/
def meanHarmonic (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ)
    (w : ℂ) : ℝ :=
  1 / Real.sqrt κ * (Real.pi * (1 + ∑ i, ρR i) - 2 * Complex.arg w
    - (∑ i, ρL i * Complex.arg (w - vL i)) - ∑ i, ρR i * Complex.arg (w - vR i))

theorem forceExt_eq_meanHarmonic (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {vL : Fin nL → ℝ}
    {vR : Fin nR → ℝ} (hvL : ∀ i, vL i ≤ 0) (hvR : ∀ i, 0 ≤ vR i) (w : ℂ) :
    Impl.forceExt κ (weightWord ρL ρR) vL vR w = meanHarmonic κ ρL ρR vL vR w := by
  simp only [Impl.forceExt, Impl.jumpExt_eq, meanHarmonic, weightWord]
  simp only [min_eq_right (hvL _), max_eq_right (hvR _), Complex.ofReal_zero, sub_zero]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have h1 : ∑ i, ρL i * (1 - (1 - Complex.arg (w - (vL i : ℂ)) / Real.pi)) =
      (∑ i, ρL i * Complex.arg (w - (vL i : ℂ))) / Real.pi := by
    rw [Finset.sum_div]; congr 1; funext i; ring
  have h2 : ∑ i, ρR i * (1 - Complex.arg (w - (vR i : ℂ)) / Real.pi) =
      (∑ i, ρR i) - (∑ i, ρR i * Complex.arg (w - (vR i : ℂ))) / Real.pi := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]; congr 1; funext i; ring
  show Real.pi / Real.sqrt κ * (-1 + 2 * (1 - Complex.arg w / Real.pi)
      - ∑ i : Fin nL, ρL i * (1 - (1 - Complex.arg (w - (vL i : ℂ)) / Real.pi))
      + ∑ i : Fin nR, ρR i * (1 - Complex.arg (w - (vR i : ℂ)) / Real.pi)) = _
  rw [h1, h2]
  field_simp
  ring

/-- **The mean is explicit.** For centred positions `vL i ≤ 0 ≤ vR i`, every bounded harmonic extension of
the force-word boundary data equals `meanHarmonic` on `ℍ`. -/
theorem eqOn_meanHarmonic {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {vL : Fin nL → ℝ}
    {vR : Fin nR → ℝ} (hvL : ∀ i, vL i ≤ 0) (hvR : ∀ i, 0 ≤ vR i) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR) (forceJumpSet vL vR) u) :
    EqOn u (meanHarmonic κ ρL ρR vL vR) QuantumZipper.H := by
  have hex := Impl.isBoundedHarmonicExtension_forceExt κ (weightWord ρL ρR) vL vR
  have heq := Impl.eqOn_of_isBoundedHarmonicExtension
    (Impl.forceJumpSet_finite (weightWord ρL ρR) vL vR) hex hu
  intro w hw
  rw [heq hw, forceExt_eq_meanHarmonic κ ρL ρR hvL hvR]

/-- **`𝔥_t(z) = Im H_t(z)`** (Theorem 1.1's mean is the imaginary part of (2.5)): for centred positions
`vL i ≤ 0 ≤ vR i`, every bounded harmonic extension `u` of the time-`t` data and `f_t(z) ∈ ℍ`,
`couplingMean κ w t u z = meanHarmonic κ ρL ρR vL vR (f_t z) − χ Im (logDerivFwd w t z)`. -/
theorem couplingMean_eq_meanHarmonic {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} (hvL : ∀ i, vL i ≤ 0) (hvR : ∀ i, 0 ≤ vR i)
    {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR) (forceJumpSet vL vR) u)
    {w : ℝ → ℝ} {t : ℝ} {z : ℂ} (hz : QuantumZipper.fwdMap w t z ∈ QuantumZipper.H) :
    couplingMean κ w t u z = meanHarmonic κ ρL ρR vL vR (QuantumZipper.fwdMap w t z) -
      QuantumZipper.chiC κ * (QuantumZipper.logDerivFwd w t z).im := by
  rw [couplingMean, eqOn_meanHarmonic hvL hvR hu hz]

end Ito

end InteractingSLE
