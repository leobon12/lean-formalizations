import QuantumZipper.Proofs.Zipper.AreaVarSand
import QuantumZipper.Proofs.LQG.AreaExistenceVague

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-WINDOW (0): the statements of the Sheffield–Wang window chain

Source: S. Sheffield, M. Wang, arXiv:1605.06171 (literature/1605.06171.pdf), §3.1, proof of
Lemma 3.1 (pp. 7–8) and proof of Theorem 1.1 (p. 9).

* `FreeWindowStmt γ c c'`: the window limits `WindowLimits` (p. 9 display) a.s. for the free
  boundary GFF `X` on `ℍ` (modulo constants) itself.
* `WinSplit P A B`: SW's `L¹ + L²` split of a difference `A_j − B_j` (display after (3.2), p. 8:
  a thick part with summable first moments and a rest with summable second moments; for
  `γ < √2` the first part is `0` and the second is (3.1)).
* `SWWindowSplitStmt γ c c'`: **SW's display for the window measures (p. 9, "by estimating
  `E|μ_{2^{-k/N}}(S) − μ̄_{k,N}(S)|²` using the tower property of conditional expectation as in the
  proof of Lemma 3.1")**, for the free field, a test function `φ ≥ 0` compactly supported in `ℍ`
  instead of a dyadic square `S`, and every `N ≥ 1`: the normalized window integrals
  `c N ∫ supWin φ` (resp. `c' N ∫ infWin φ`) differ from the reference `∫ φ dμ_{2^{-j/N}}` by at
  most `Y_j + Z_j`, with `Σ E Y_j < ∞` and `Σ E Z_j² < ∞`. The field is normalized by
  `X(fc(0,1)) = 0` (SW work with the zero-boundary field on `D`; `IsFreeGFFModConstH` allows any,
  even non-integrable, random additive constant, under which moment bounds cannot hold).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

open VagueH

/-- The window limits hold almost surely for the free field. -/
def FreeWindowStmt (γ : ℝ) (c c' : ℕ → ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P →
    ∀ᵐ ω ∂P, WindowLimits γ (X ω) c c'

/-- SW's `L¹ + L²` split (p. 8): a.s. `|A_j − B_j| ≤ Y_j + Z_j` for all `j ≥ j₀` (SW: "assume
`k` is large enough such that `dist(S, ∂D) > 2^{-k-1}`"), with
`Σ_j E Y_j < ∞` and `Σ_j E Z_j² < ∞`. -/
def WinSplit {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (A B : ℕ → Ω → ℝ≥0∞) : Prop :=
  ∃ Y Z : ℕ → Ω → ℝ≥0∞, (∀ j, AEMeasurable (Y j) P) ∧ (∀ j, AEMeasurable (Z j) P) ∧
    (∑' j, ∫⁻ ω, Y j ω ∂P) ≠ ∞ ∧ (∑' j, ∫⁻ ω, Z j ω ^ 2 ∂P) ≠ ∞ ∧
    ∃ j₀ : ℕ, ∀ᵐ ω ∂P, ∀ j, j₀ ≤ j →
      A j ω ≤ B j ω + (Y j ω + Z j ω) ∧ B j ω ≤ A j ω + (Y j ω + Z j ω)

/-- The reference integral `∫_ℍ φ dμ_{2^{-j/N}}` (in `ℝ≥0∞`). -/
def winRef (γ : ℝ) (x : FieldSample) (N j : ℕ) (φ : ℂ → ℝ) : ℝ≥0∞ :=
  ∫⁻ w in H, ENNReal.ofReal (areaDens γ x (winHi N j) w * φ w)

end QuantumZipper.E6
