/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsCenteredCounterflowDriver

/-!
# The literal counterflow line of the paper, in the infinity-source chart

Packet PROVE-AF-CFLIT (audit response, priority 2, audit §3.4, p. 9). The paper (Miller–Sheffield, arXiv:1201.1496v2,
pp. 19–20) defines a counterflow line of a GFF `h` on `ℍ` as an `SLE_κ′(ρ)` coupled with `−h` as in Theorem 1.1, and on
another domain `D` through a conformal map `ψ : D → ℍ` (`ψ(x) = 0`, `ψ(y) = ∞`) with a fixed continuous branch of
`arg ψ′`: `η′` is a counterflow line of `h` when `ψ(η′)` is a counterflow line of `h ∘ ψ⁻¹ − χ arg (ψ⁻¹)′`,
`χ = χ(κ) > 0`. The specification calls this the *literal* frame, `CF_lit(h)` (spec p. 2 and p. 12), and states
Theorem 1.4 for the *centred* frame `CF_d(h) = CF_lit(h + πχ)` (FD11.1), frozen as `IsCenteredCounterflowDriver`.

This file defines the literal counterflow line from `∞` to `0` in the same chart as the frozen centred one,
`R(z) = −1/z`:

* `infinitySourceChartAt n`: the chart `R` with the branch `n` of its derivative argument,
  `arg R′(z) = Im(−2 Log z) + 2πn = −2 arg z + 2πn` (`0 < arg z < π`); `n = 0` is the FD12.1 lift of the frozen
  `infinitySourceChart`;
* **`IsLiteralCounterflowDriver`**: the paper's definition with the FD12.1 branch (the frozen `infinitySourceChart`);
* `IsLiteralCounterflowDriverAt n`: the same definition with the branch `n`.

The bridge to the centred frame is in `LiteralCounterflowBridge.lean`, the Theorem 1.4 corollaries in
`LiteralCounterflow.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **The infinity-source chart with the branch `n` of `arg R′`** (paper p. 19: "a branch of `arg ψ′` has been fixed";
FD12.1): forward map `R(z) = −1/z`, inverse map `R⁻¹ = R` (as maps), and the derivative lift
`arg R′(z) = Im(−2 Log z) + 2πn = −2 arg z + 2πn` on `ℍ` (principal `Log`, `0 < arg z < π` there), since
`R′(z) = 1/z²`. The branches of `arg R′` that are continuous on `ℍ` are exactly these, `n ∈ ℤ`; `n = 0` is the lift
`L_R = −2 Log z` of FD12.1 used by the frozen `infinitySourceChart`. -/
def infinitySourceChartAt (n : ℤ) : Chart :=
  (fun z => -z⁻¹, fun z => -z⁻¹, fun z => (-2 * Complex.log z).im + 2 * Real.pi * (n : ℝ))

/-- **The literal counterflow line `CF_lit(h)` of the paper, from `∞` to `0` on `ℍ`, with the FD12.1 branch**
(paper pp. 19–20, Definition of counterflow lines; specification p. 2 and p. 12, "the literal frame").
`W` (lifetime `ζ`) is its driving function in the chart `R`. Every choice is explicit:
* domain and marked points: `D = ℍ`, start `x = ∞`, target `y = 0`; conformal map `ψ = R`, `R(z) = −1/z`
  (`infinitySourceChart.1`), with `R(∞) = 0`, `R(0) = ∞`, and `R⁻¹ = R` as a map (`infinitySourceChart.2.1`);
* derivative lift and branch: `arg ψ′ = Im L_R`, `L_R(z) = −2 Log z`, `0 < Im Log z < π` (FD12.1, the lift
  `infinitySourceChart.2.2`), so `arg R′(z) = −2 arg z ∈ (−2π, 0)`; the inverse lift is the compatible one,
  `arg (R⁻¹)′(w) = −arg R′(R⁻¹ w) = 2π − 2 arg w` (FD12.2);
* field: the paper's transported field `hR = h ∘ R⁻¹ − χ arg (R⁻¹)′` with `χ = χ(κ) > 0` ("here `χ = χ(κ) > 0`",
  p. 20), which is `h ∘ R + χ (arg R′) ∘ R`, the frozen `IsChartTransport infinitySourceChart 1 0 χ(κ) h hR`
  (coordinate rule (1.4) with coefficient `χ(κ)`, no sign change and no added constant);
* coupling, angle and parameter: `R(η′)` is a counterflow line of `hR` on `ℍ`, that is, an `SLE_κ′(ρ)` coupled with
  `−hR` as in Theorem 1.1 at the parameter `κ′ = 16/κ` (p. 19: "coupled with a GFF `−h` … as in Theorem 1.1"): the
  angle-`0` flow line from `0` of the parameter field `−hR` at parameter `κ′` (frozen `IsFlowLineDriver (16 / κ) b'
  jumps' 0`; the angle `0` adds `0 · χ(κ′) = 0`);
* force word: the word induced by the boundary data `b'` of `−hR` (locally constant off the finite set `jumps'`):
  seed marks `0⁻`, `0⁺` with weights `−b'(0⁻)/λ′ − 1` and `b'(0⁺)/λ′ − 1`, and one mark at each genuine jump `y` of
  `b'`, of weight `(b'(y⁺) − b'(y⁻))/λ′`, on the left side for `y < 0` and on the right side for `y > 0`
  (`λ′ = λ(κ′)`; frozen `flowLineXL`/`flowLineXR`, `flowLineRhoL`/`flowLineRhoR (16 / κ) b' jumps' 0 0`). Its
  Theorem 1.1 boundary data is exactly `b'`. The chart's left side `ℝ₋` is `R(ℝ₊)`, the clockwise arc of `∂ℍ` from
  `x = ∞` to `y = 0`, which is the left side of `η′`; its right side `ℝ₊` is `R(ℝ₋)`.

The parameter field is `−hR = −h ∘ R + 2πχ − 2χ arg w` (`0 < arg w < π`), while the frozen centred
`IsCenteredCounterflowDriver` uses `−h ∘ R + πχ − 2χ arg w` (FD12.5). The two differ by the constant `πχ` for the same
field `h`: `IsCenteredCounterflowDriver κ P h W ζ ↔ IsLiteralCounterflowDriver κ P (h + πχ) W ζ`
(`AuditFix.CFLit.isCenteredCounterflowDriver_iff_literal`). -/
def IsLiteralCounterflowDriver (κ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∃ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (hR : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b' jumps' ∧
    (∀ ω, IsChartTransport infinitySourceChart 1 0 (QuantumZipper.chiC κ) (h ω) (hR ω)) ∧
    IsFlowLineDriver (16 / κ) b' jumps' 0 P (fun ω => -hR ω) W ζ

/-- **The literal counterflow line of the paper with the branch `n` of `arg R′`** (paper pp. 19–20): exactly
`IsLiteralCounterflowDriver`, with the chart `infinitySourceChartAt n`, i.e. `arg R′(z) = −2 arg z + 2πn` and the
compatible inverse lift `arg (R⁻¹)′(w) = 2π(1 − n) − 2 arg w`. Its parameter field is
`−h ∘ R + 2π(1 − n)χ − 2χ arg w`. The paper's Remark (p. 19) leaves `n` free and suggests normalizing it by
`arg ψ′(ψ⁻¹(i)) ∈ (−π, π]`, which here selects `n = 1` (`AuditFix.CFLit.remarkBranch_iff`); `n = 0` is FD12.1
(`AuditFix.CFLit.isLiteralCounterflowDriver_iff_at_zero`). -/
def IsLiteralCounterflowDriverAt (n : ℤ) (κ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∃ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (hR : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b' jumps' ∧
    (∀ ω, IsChartTransport (infinitySourceChartAt n) 1 0 (QuantumZipper.chiC κ) (h ω) (hR ω)) ∧
    IsFlowLineDriver (16 / κ) b' jumps' 0 P (fun ω => -hR ω) W ζ

end InteractingSLE
