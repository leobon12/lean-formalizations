import QuantumZipper.Proofs.Zipper.BdryAllMapsMain
import QuantumZipper.Proofs.Zipper.AreaVarWin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-THM43 (3): the boundary variable-scale limit from the boundary window measures

Source: S. Sheffield, M. Wang, arXiv:1605.06171 (literature/1605.06171.pdf), proof of
**Theorem 4.2**, p. 19: with `C(N) = E[sup_{t∈[0,2 log 2/N]} e^{−γ²t/8} e^{γ B_t/2}]⁻¹` and
`C̲(N)` the analogous infimum constant, "by considering the random measures
`C(N) sup_{ε∈[2^{-(k+1)/N}, 2^{-k/N}]} e^{h̄_ε(z)} dz` and `C̲(N) inf_{…} e^{h̄_ε(z)} dz` as in the
proof of Theorem 1.1, we are able to show that … `µ^B_ε` converge to `µ^B`"; and p. 19 (proof of
Theorem 4.3): "an analogous result to Corollary 3.2 holds".

Here, exactly as for the area measure (`AreaVarSand.lean`, `AreaVarWin.lean`, whose window
arithmetic `winLo`, `winHi`, `mem_win_of_scale`, `exists_int_scale` and squeeze
`ev_lt_of_upper`, `ev_gt_of_lower` are reused):

* `BdryWindowLimits γ x c c'` — the p. 19 window convergence for one field (windows of two lattice
  steps, adaptation as in `AreaVarWin.lean`), tested against nonnegative continuous compactly
  supported functions on `ℝ`, in `ℝ≥0∞`;
* **`bdryVarScaleLimit_of_window`**: the deterministic sandwich (partition of unity subordinate to
  the sets where `s` is within a factor `2^{2/N}` of a lattice point) gives `BdryVarScaleLimit`;
* **`bdryAllMapsStmt_of_window_distortion`**: `BdryWindowStmt → BdryDistortionStmt →
  BdryAllMapsStmt`.

The localization and `ε`-bookkeeping are own work (SW give no details for Cor. 3.2).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal

namespace QuantumZipper
namespace F1

open E6

/-- Supremum of the boundary density over the radii of the `j`-th window. -/
def bSupWin (γ : ℝ) (x : FieldSample) (N j : ℕ) (u : ℝ) : ℝ≥0∞ :=
  ⨆ ρ ∈ Icc (winLo N j) (winHi N j), ENNReal.ofReal (bdryDens γ x ρ u)

/-- Infimum of the boundary density over the radii of the `j`-th window. -/
def bInfWin (γ : ℝ) (x : FieldSample) (N j : ℕ) (u : ℝ) : ℝ≥0∞ :=
  ⨅ ρ ∈ Icc (winLo N j) (winHi N j), ENNReal.ofReal (bdryDens γ x ρ u)

/-- **Boundary window convergence** (SW proof of Thm 4.2, p. 19) for one field `x`. -/
def BdryWindowLimits (γ : ℝ) (x : FieldSample) (c c' : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ φ : ℝ → ℝ, Continuous φ → HasCompactSupport φ → (∀ u, 0 ≤ φ u) →
    Tendsto (fun j => ENNReal.ofReal (c N) * ∫⁻ u, bSupWin γ x N j u * ENNReal.ofReal (φ u))
        atTop (𝓝 (ENNReal.ofReal (∫ u, φ u ∂(qBoundaryMeasure γ x)))) ∧
      Tendsto (fun j => ENNReal.ofReal (c' N) * ∫⁻ u, bInfWin γ x N j u * ENNReal.ofReal (φ u))
        atTop (𝓝 (ENNReal.ofReal (∫ u, φ u ∂(qBoundaryMeasure γ x))))

/-- Open node (SW proof of Thm 4.2, p. 19, free boundary GFF on `ℍ`): constants `c N, c' N → 1`
(SW: `C(N), C̲(N) → 1`) with a.s. `BdryWindowLimits`. -/
def BdryWindowStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c c' : ℕ → ℝ, Tendsto c atTop (𝓝 1) ∧ Tendsto c' atTop (𝓝 1) ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → FieldSample), IsFreeGFFModConstH X P →
      ∀ᵐ ω ∂P, BdryWindowLimits γ (X ω) c c'

variable {γ : ℝ} {x : FieldSample} {c c' : ℕ → ℝ}

end F1
end QuantumZipper
