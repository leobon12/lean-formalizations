import QuantumZipper.Proofs.Zipper.AreaWinMkFinal
import QuantumZipper.Proofs.Zipper.BdryAllMapsSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-W1 (0): the boundary window Markov structure (statements)

Source: S. Sheffield, M. Wang, arXiv:1605.06171, proof of Theorem 4.2, pp. 18–19 ("as in the
proof of Theorem 1.1", p. 9, via the proof of Lemma 3.1, (3.1)–(3.2)); B. Duplantier,
S. Sheffield (2011), §3.1 and §6 (semicircle averages on the boundary: `t ↦ h_{r e^{-t}}(x) −
h_r(x)` is `√2` times a standard Brownian motion).

* `WinHypB`: the one-dimensional version of `E6.WinHypC` (the index set is `S ⊆ ℝ`).
* `BdryWinMarkovData`: the boundary analogue of `E6.WinMarkovData` for the normalization at a
  large circle (no exceptional set). In the `γ/2`-normalization of `TwoRadius`,
  `bdryDens_r = e^{-(γ²/4) L + (γ/2) U}` with `L = log (1/r) = 2 Lw`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Real
open scoped Topology NNReal ENNReal

namespace QuantumZipper.F1

open E6

/-- Hypotheses of the boundary window core bound (as `E6.WinHypC`, index set in `ℝ`). -/
structure WinHypB {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (S : Set ℝ) (δ K Q : ℝ)
    (L : ℝ → ℝ) (v : ℝ → ℝ≥0) (U G : ℝ → Ω → ℝ) : Prop where
  measU : Measurable (fun p : ℝ × Ω => U p.1 p.2)
  measG : Measurable (fun p : ℝ × Ω => G p.1 p.2)
  measL : Measurable L
  lawU : ∀ t ∈ S, HasLaw (U t) (gaussianReal 0 (v t)) P
  varU : ∀ t ∈ S, (v t : ℝ) ≤ 2 * L t + K
  memG : ∀ t ∈ S, MemLp (G t) 2 P
  meanG : ∀ t ∈ S, ∫ ω, G t ω ∂P = 0
  sqG : ∀ t ∈ S, ∫ ω, G t ω ^ 2 ∂P ≤ Q
  indep : ∀ t ∈ S, IndepFun (G t) (U t) P
  decor : ∀ t ∈ S, ∀ u ∈ S, δ ≤ |t - u| →
    IndepFun (G t) (fun ω => (U t ω, U u ω, G u ω)) P

/-- **The boundary window Markov structure on `S ⊆ ℝ`** (SW pp. 18–19): for `j ≥ j₀`,
`WinHypB` for `(U_j, G_j)` at decorrelation distance `2 · 2^{-j/N}` with `L = log 2^{j/N}`, and
a.s. on `S`: `bdryDens_{2^{-j/N}} = e^{-(γ²/4) L + (γ/2) U_j}`, `1 + G_j ≥ 0`,
`c · win = bdryDens_{2^{-j/N}} · (1 + G_j)`. -/
def BdryWinMarkovData {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → FieldSample)
    (γ c : ℝ) (N : ℕ) (win : FieldSample → ℕ → ℝ → ℝ≥0∞) (S : Set ℝ) : Prop :=
  ∃ (K Q : ℝ) (j₀ : ℕ) (U G : ℕ → ℝ → Ω → ℝ) (v : ℕ → ℝ → ℝ≥0),
    0 ≤ Q ∧
    (∀ j, j₀ ≤ j →
      WinHypB P S (2 * winHi N j) K Q (fun _ => 2 * Lw N j) (v j) (U j) (G j)) ∧
    (∀ j, j₀ ≤ j → ∀ᵐ ω ∂P, ∀ u ∈ S,
      bdryDens γ (X ω) (winHi N j) u
          = rexp (-(γ ^ 2 / 4) * (2 * Lw N j) + γ / 2 * U j u ω) ∧
        0 ≤ 1 + G j u ω ∧
        ENNReal.ofReal c * win (X ω) j u
          = ENNReal.ofReal (bdryDens γ (X ω) (winHi N j) u * (1 + G j u ω)))

end QuantumZipper.F1
