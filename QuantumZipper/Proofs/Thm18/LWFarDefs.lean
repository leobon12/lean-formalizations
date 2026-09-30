import QuantumZipper.Proofs.Thm18.G4TraceNull2Scale
import QuantumZipper.Proofs.Probability.StrongMarkov
import QuantumZipper.Proofs.Thm11.ForwardClock

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node LW-FAR: the statement plan for a far-apart two-point estimate

Task LW-FAR-PLAN (plan: `handoff/LW-FAR.md`). The consumer `g4UpTraceNullStmt_of_twoPointFar_q`
(`LWFarQChain.lean`) needs `SLETwoPointFarUnit κ q` for SOME `q > 1` (`0 < κ < 4`). This file fixes
the exact statements of the intermediate nodes of the route chosen in the plan (target exponent
`q = 3/2 − κ/8`); it contains definitions only (no proofs, no hypotheses are assumed anywhere).

Notation (`W` a driver, `t ≥ 0`, `x ∈ H_t = H \ K_t`), following G. Lawler, B. Werness,
*Multi-point Green's functions for SLE and an estimate of Beffara*, Ann. Probab. 41 (2013),
§2.1–2.2 (`literature/1011.3551.pdf`, pp. 4–10):
* `cMap W t x = g_t(x) − W_t = fwdMap W t x` (LW's `Z_t`), `upsilon W t x = Im g_t(x)/|g_t'(x)|` (LW's `Υ_t`,
  `= exp (fwdLogCR W t x)`), `sinArg W t x = Im Z_t/|Z_t|` (LW's `S_t`);
* `Pocket W t w z ρ`: the closed disk `B̄(w, ρ)` disconnects `z` from `∞` in `H_t` (V. Beffara,
  *The dimension of the SLE curves*, Ann. Probab. 36 (2008), §3.1, the quantity `ρ_t`, p. 12).

Sources of the nodes: Beurling estimate (LW Prop 2.1, p. 5; Lawler, *Conformally Invariant
Processes in the Plane*, Thm 3.69, p. 77; Garnett–Marshall, *Harmonic Measure*, Thm III.9.2);
side bound (LW eq. (2), p. 6; Beffara Lemma 6, p. 13); boundary hitting (LW Prop 2.6, p. 10);
fjord/pocket entry (LW Lemmas 4.3–4.5, pp. 23–25, used as in LW Lemmas 4.11–4.12, pp. 29–30;
Beffara Lemma 8, p. 15); conditional one-point estimate (LW Lemma 2.10, p. 12; Beffara Cor 5,
p. 9). The assembly (pocket-product bound and the dyadic sums) is an own simplification of LW
§4.4 that loses a logarithm, which the consumer can afford (see the plan).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- The standing hypotheses for the strong Markov property (`StrongMarkov.lean`): a Brownian
motion with all paths continuous and started at `0`, and its natural filtration. -/
structure SMSetup {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (𝓕 : Filtration ℝ≥0 mΩ) : Prop where
  brownian : IsBrownianReal B P
  cont : ∀ ω, Continuous (B · ω)
  meas : ∀ t, Measurable (B t)
  zero : ∀ ω, B 0 ω = 0
  natural : ∀ t, 𝓕 t = MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi

/-- **LWF-2. Boundary hitting estimate** (LW Prop 2.6, p. 10, for a disk about a real point;
exponent `8/κ − 1`). -/
def BdryHitStmt (κ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → ∀ x r : ℝ, 0 < r → 2 * r ≤ |x| →
      P {ω | ∃ t : ℝ, 0 ≤ t ∧ ‖sleTrace κ B ω t - x‖ < r} ≤
        ENNReal.ofReal (C * (r / |x|) ^ (8 / κ - 1))

/-- **LWF-4. Beurling estimate for harmonic majorants** (LW Prop 2.1, p. 5; Lawler, CIP,
Thm 3.69; Garnett–Marshall Thm III.9.2 and its corollary), analytic form: a harmonic `h` with
`0 ≤ h ≤ 1` on the component `V` of `D ∩ B(w, ρ)` containing `w`, tending to `0` at the points of
`∂D` inside the disk, where `ℂ \ D` contains a continuum crossing `{d ≤ |x − w| ≤ ρ}`, satisfies
`h(w) ≤ C (d/ρ)^{1/2}`. -/
def BeurlingHarmStmt : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (D K : Set ℂ) (w : ℂ) (d ρ : ℝ) (h : ℂ → ℝ),
    IsOpen D → w ∈ D → 0 < d → d ≤ ρ → IsConnected K → Disjoint K D →
    (K ∩ closedBall w d).Nonempty → (K \ ball w ρ).Nonempty →
    InnerProductSpace.HarmonicOnNhd h (connectedComponentIn (D ∩ ball w ρ) w) →
    (∀ x ∈ connectedComponentIn (D ∩ ball w ρ) w, 0 ≤ h x ∧ h x ≤ 1) →
    (∀ x₀ ∈ frontier D ∩ ball w ρ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ connectedComponentIn (D ∩ ball w ρ) w, dist x x₀ < δ → h x ≤ ε) →
    h w ≤ C * (d / ρ) ^ (1 / 2 : ℝ)

end LWFar
end Thm18Asm
end QuantumZipper
