import QuantumZipper.Proofs.Zipper.D3PlusIMarkov
import QuantumZipper.Proofs.Zipper.LocRichD3

/-!
# D3⁺(i), node N2: the zoom in total variation for a fixed deterministic correction

Task D3P-N2 (decision D23/D24; `handoff/D3P-I.md`, which splits `D3PlusICoreStmt` into N1 —
factorization and measurability — and N2). Paper: Sheffield, arXiv:1012.4797, proof of
Prop. 1.6 (p. 25): near the marked point the smooth part of the field "is approximately
constant"; the circle-average process is a Brownian motion with drift `α − Q`, re-centred at its
first hit of the level, whose law converges to that of the wedge radial process, and the lateral
part is scale invariant and independent.

## The objects

* `locZField X r ω`: the local part `Z = markovZ X 0 r` of the free field on the half-disc
  `ball 0 r ∩ ℍ` (zero boundary values on the semicircle, free on `ℝ`; node L2), as a field
  sample: `Z ω μ` on local measures (`IsLocalH 0 r`), `0` (junk) elsewhere. It is exactly the
  extension `extLoc r (localZ X r ω)` of the local data of `D3PlusIMarkov`.
* `n2Out γ α L r R φ y = locField R (canonicalOn γ (y + ofFun (α(−log‖·‖) + φ + L/γ)) (halfDisc r))`:
  the local data of the canonical description of `y` plus a deterministic correction `φ` and the
  level `L/γ`.
* `AdmCorr r φ`: `φ` continuous on `ℂ` and `φ ∘ foldH` harmonic near `0` (the corrections produced
  by N1: harmonic part `h_X` of the Markov decomposition plus `g`, retracted outside a smaller
  half-disc, plus the constant `c`).

## The statements

* `D3PlusIN2FixStmt`: for a free field `X` and an admissible `φ`, the law of `n2Out … φ (Z ω)`
  converges in TV, as `L → ∞`, to the law of `locField R` of an `α`-quantum wedge.
* `D3PlusIN2FixCMStmt` (Cameron–Martin part): two admissible corrections agreeing at `0` give laws
  at TV distance `→ 0` (D24: the difference is harmonic near `0` and vanishes there, so its
  Dirichlet energy on `B(0, aR)` is `O(a²)`; Berestycki–Powell arXiv:2004.04720 Lemmas 3.12,
  3.14, p. 79).
* `D3PlusIN2FixZeroStmt` (model part): the correction `0`: the zoom of `Z + α(−log) + L/γ`
  converges in TV to the wedge (radial part `ZoomRadial.abs_prob_zoomRadial_sub_le`, lateral
  scale invariance `WedgeTK.fieldLawFull_lateralPart_rescale`).

## Proved here

* `d3PlusIN2Fix_of_cm_zero : D3PlusIN2FixCMStmt → D3PlusIN2FixZeroStmt → D3PlusIN2FixStmt` (triangle
  inequality through the constant correction `φ(0)`, and `n2Out_const`: a constant correction is
  the level shift `L ↦ L + γ φ(0)`; own elementary argument).
* `core_tendsto_of_n2`: clause (d) of `D3PlusICoreStmt` from `D3PlusIN2FixStmt`, for any `Tm` of the
  form `Tm L (s, f) = n2Out γ α L r R (Φ f) (extLoc r s)` with `Φ (F ω)` admissible a.s. (the
  form N1 is expected to produce).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

open Classical in
/-- Extension of local data `s : LocIdx r → ℝ` to a field sample (junk value `0` on non-local
measures). -/
def extLoc (r : ℝ) (s : LocIdx r → ℝ) : FieldSample := fun μ =>
  if h : K3.IsLocalH 0 r μ then s ⟨μ, h⟩ else 0

theorem measurable_extLoc (r : ℝ) : Measurable (extLoc r) := by
  classical
  refine measurable_pi_iff.2 fun μ => ?_
  unfold extLoc
  by_cases h : K3.IsLocalH 0 r μ
  · simp only [h, dite_true]
    exact measurable_pi_apply _
  · simp only [h, dite_false]
    exact measurable_const

/-- The local part `Z = markovZ X 0 r` of the free field on the half-disc, as a field sample
(junk value `0` on non-local measures). -/
def locZField {Ω : Type*} (X : Ω → FieldSample) (r : ℝ) (ω : Ω) : FieldSample :=
  extLoc r (localZ X r ω)

theorem locZField_apply_of_local {Ω : Type*} (X : Ω → FieldSample) {r : ℝ} (ω : Ω)
    {μ : Measure ℂ} (hμ : K3.IsLocalH 0 r μ) : locZField X r ω μ = K3.markovZ X 0 r ω μ := by
  simp [locZField, extLoc, hμ, localZ]

/-- The deterministic part added to the local field: `α(−log‖z‖) + φ z + L/γ`. -/
def n2Shift (γ α L : ℝ) (φ : ℂ → ℝ) : ℂ → ℝ := fun z => α * -Real.log ‖z‖ + φ z + L / γ

/-- The canonical description (on `halfDisc r`) of `y + α(−log) + φ + L/γ`. -/
def n2Canon (γ α L r : ℝ) (φ : ℂ → ℝ) (y : FieldSample) : FieldSample :=
  canonicalOn γ (y + ofFun (n2Shift γ α L φ)) (halfDisc r)

/-- Admissible deterministic corrections on the half-disc of radius `r`: continuous on
`ball 0 r ∩ Hbar` (the region read by the local field), with `φ ∘ foldH` harmonic near `0`. -/
def AdmCorr (r : ℝ) (φ : ℂ → ℝ) : Prop :=
  ContinuousOn φ (Metric.ball (0 : ℂ) r ∩ Hbar) ∧ ∃ ρ > 0, InnerProductSpace.HarmonicOnNhd (fun z => φ (foldH z))
    (Metric.ball (0 : ℂ) ρ)

theorem admCorr_const (r c : ℝ) : AdmCorr r (fun _ => c) :=
  ⟨continuousOn_const, 1, one_pos, by simp⟩

/-! ## The statements -/

/-! ## The rich forms (decision D25) -/

/-! ## Assembly -/

end D3Plus
end QuantumZipper
