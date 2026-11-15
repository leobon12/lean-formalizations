/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6Restart
import InteractingSLE.Spec.Restart.CondDet
import InteractingSLE.Spec.Sec2.MartingaleFinalImage

/-!
# Proposition GB6: the conditional law (d) as a named input, in the general restart kernel's form

Packet PROVE-GB6D. Supplement §8.6, Proposition GB6 (`source/spec/p481-528.md` L929–L975, pp. 518–520). PROVE-GB6C
reduced GB6 to `GB6RelativeLawStatement` and listed its open parts: (d) the conditional law of the relative
exploration, (e) its infinite relative lifetime, (f) the complete trace at `16/κ`, and the measurability of the
restart variable. This file states (d) — and only (d) — as a named input, in the form of PROVE-RESTARTKERNEL's general
restart kernel with PROVE-CONDDET's canonical driver codes
(`Restart.restartKernel_isFlowLineDriver_of_codeMatch_canonical`, `Restart.IsCanonicalDriverCode`): the conditional
Gaussian law of the chart field
given the marked prefix **(R1)**, and the identification of the actual relative exploration with the canonical
counterflow of the conditional field **(Det)** ("Theorem 2.4 and integrated uniqueness identify the relative driving
law through every such stopped buffer"; RESTARTKERNEL's W8 form: "Universal finite-force determination now identifies
each actual conditional future … as the canonical flow of the same conditional field").

**What (d) does not contain.** The identification (Det) is asserted only **before the first contact** `T_c` (in the
relative clock, before `ζ = sup_{t < T_c} relClock t`). That `ζ = ∞` is GB6's step (e) ("There remains a possible
extra killing at first contact, which must not be hidden in this identification … Hence `ζ = ∞`"), proved in
`GB6Life.lean`. The canonical counterflow's trace (f) is proved in `GB6Trace.lean` from Theorem 1.3's inputs at `16/κ`.

## Main definitions

* `baseR`, `baseL`: the centred images `V̂^{0,R}_σ ≥ 0`, `V̂^{0,L}_σ ≤ 0` of `0±` under the own flow chart (the ends of
  the filled real base `[a, b]` of GB6's proof); `junctionR = −1/V̂^{0,L}_σ > 0`, `junctionL = −1/V̂^{0,R}_σ < 0`: the
  two **junctions** in the relative chart (the inversion `−1/(z − W)` "takes these portions to the two terminal real
  tails, including their initial junctions");
* `tailLevel κ = Λ(1 + c)`, `c = k/2 − 2`, `k = 16/κ`; `IsGB6TailData κ c jL jR`: the boundary word `c` is at least
  `Λ(1 + c)` beyond `jR` and at most `−Λ(1 + c)` beyond `jL` (the terminal partial sums `S_R, S_L ≥ c` of GB6's proof,
  `GB6Word.protLevel_le_sumR`/`sumL`, in data form: `forceBoundaryData = ±Λ(1 + S)`);
* `IsGB6AdmData κ c`: every side partial sum of the counterflow word of `c` is `> −2` (data form);
* `IsGoodDrvCode`, `drvDec`, `drvDecTop`: decoding a driver code (`Restart.IsDriverCodeMatch`'s coding);
* **`GB6CondDetStatement`** (named input (d)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Supp8

namespace GB6

open Restart Sec2.Assembly MartChar.RealFlow LQGMetric

/-! ### The junctions of the flow's own chart -/

/-- The centred image `V̂^{0,R}_σ = g_σ(0⁺) − W_σ` of the right side of the seed (the right end of the filled real base
in the own flow chart). -/
def baseR (w : ℝ → ℝ) (σ : ℝ) : ℝ := rightImg w 0 σ - w σ

/-- The centred image `V̂^{0,L}_σ = g_σ(0⁻) − W_σ` of the left side of the seed (by reflection). -/
def baseL (w : ℝ → ℝ) (σ : ℝ) : ℝ := -rightImg (fun r => -w r) 0 σ - w σ

/-- The right junction `−1/V̂^{0,L}_σ` in the relative chart `w ↦ −1/f_σ(−1/w)` (the start of the right tail, the image
of the left flow side). -/
def junctionR (w : ℝ → ℝ) (σ : ℝ) : ℝ := -(baseL w σ)⁻¹

/-- The left junction `−1/V̂^{0,R}_σ` in the relative chart (the start of the left tail, the image of the right flow
side). -/
def junctionL (w : ℝ → ℝ) (σ : ℝ) : ℝ := -(baseR w σ)⁻¹

/-! ### The conditional word: data-form conditions -/

/-- `Λ(1 + c)` with `Λ = λ(16/κ)` and `c = k/2 − 2`, `k = 16/κ`: the boundary value at partial sum `c`. -/
def tailLevel (κ : ℝ) : ℝ := bigLambda κ * (protLevel κ + 1)

/-- **The two protected tails of the conditional counterflow word** (GB6, proof: "Both are at least `c = k/2 − 2` …
Its two final flow-boundary tails are protected by GB5"), in data form: `jL < 0 < jR`, and the word is at least
`Λ(1 + c)` on `(jR, ∞)` and at most `−Λ(1 + c)` on `(−∞, jL)` (off its jumps). -/
def IsGB6TailData (κ : ℝ) (c : BoundaryWord) (jL jR : ℝ) : Prop :=
  jL < 0 ∧ 0 < jR ∧ (∀ y : ℝ, jR < y → y ∉ c.jumps → tailLevel κ ≤ c.fn y) ∧
    ∀ y : ℝ, y < jL → y ∉ c.jumps → c.fn y ≤ -tailLevel κ

/-- **The conditional counterflow word is admissible** (GB6, proof: "Consequently the entire conditional word is
admissible"), in data form: every right partial sum `S` has `Λ(1 + S) > −Λ`, every left one `−Λ(1 + S) < Λ`. -/
def IsGB6AdmData (κ : ℝ) (c : BoundaryWord) : Prop :=
  (∀ y : ℝ, 0 < y → y ∉ c.jumps → -bigLambda κ < c.fn y) ∧ ∀ y : ℝ, y < 0 → y ∉ c.jumps → c.fn y < bigLambda κ

/-! ### Decoding driver codes -/

/-- A driver code (values at the dyadic times, lifetime) is good: uniformly continuous on the dyadic times of
`[0, d]` for every dyadic `d` before the lifetime. -/
def IsGoodDrvCode (p : PCode × ℝ≥0∞) : Prop := ∀ n k : ℕ, (dyad n k : ℝ≥0∞) < p.2 → UC p.1 (dyad n k)

/-- The decoded driver of a code (the continuous extension of its dyadic values before a positive lifetime; the
constant `p.1 0 0` for a bad code or a zero lifetime). -/
def drvDec (p : PCode × ℝ≥0∞) (t : ℝ≥0) : ℝ :=
  open Classical in if IsGoodDrvCode p ∧ 0 < p.2 then dec p.1 t else p.1 0 0

/-- The decoded driver of a code read on all of `[0, ∞)` (the constant `p.1 0 0` unless the code is good on every
`[0, N]`). -/
def drvDecTop (p : PCode × ℝ≥0∞) (t : ℝ≥0) : ℝ :=
  open Classical in if ∀ N : ℕ, UC p.1 N then dec p.1 t else p.1 0 0

/-! ### The named input (d) -/

/-- **Named input (d): GB6's conditional law, (R1) and (Det) form** (supplement p. 519–520; PROVE-RESTARTKERNEL's
general restart kernel with PROVE-CONDDET's canonical codes,
`Restart.restartKernel_isFlowLineDriver_of_codeMatch_canonical`). Binders of `GB6RelativeLawStatement`
(verbatim), an own time `s`, **any** measurable version `Hc` of the chart field (the field `h` read in the chart of the
flow's own target component `U`, in the counterflow frame, almost surely on `{s < ζα, α(s) ∈ ℍ}`), and **any**
canonical driver code `F` of the counterflow at `16/κ` (`Restart.IsCanonicalDriverCode (16/κ) 0 F`). There are a
sub-σ-algebra `𝒢` (the marked prefix), a `𝒢`-event `M`, a `𝒢`-measurable conditional word `β` and `𝒢`-measurable
junction positions `jL`, `jR` such that:

* on `M`: `β` is sorted, admissible (`IsGB6AdmData`), has its protected tails beyond `jL`, `jR` (`IsGB6TailData`), and
  the canonical driver code `F (β, Hc)` of the conditional field is good (the canonical counterflow is continuous
  before its lifetime);
* **(R1)** on `M`, conditionally on `𝒢`, `Hc` has the Gaussian characteristic functional of the GFF with word `β`
  ("Thus the conditional Poisson mean is exactly the evolving finite word, and its covariance is the zero-boundary
  Green kernel");
* **(Det)** almost surely on `{s < ζα, α(s) ∈ ℍ}`: `ω ∈ M`, `jL`, `jR` are the geometric junctions `junctionL`,
  `junctionR` of the flow prefix, and **before the first contact `T_c`** the canonical counterflow of the conditional
  field (decoded from `F (β, Hc)`) generates the chart images `Ψ(K'_t)` of the physical counterflow hulls in the
  relative clock (`relClock`).

Nothing is asserted about the canonical counterflow after the relative time `sup_{t < T_c} relClock t` (GB6's (e)). -/
def GB6CondDetStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ (s : ℝ≥0) (Hc : Ω → DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (Hc ω)) →
    ∀ F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞, IsCanonicalDriverCode (16 / κ) 0 F →
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω) (β : Ω → BoundaryWord) (jL jR : Ω → ℝ),
      MeasurableSet[𝒢.1] M ∧ Measurable[𝒢.1] β ∧ Measurable[𝒢.1] jL ∧ Measurable[𝒢.1] jR ∧
      (∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted ∧ IsGB6AdmData κ (β ω) ∧ IsGB6TailData κ (β ω) (jL ω) (jR ω) ∧
        IsGoodDrvCode (F (β ω, Hc ω))) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (Hc ω' φ : ℂ)) | 𝒢.1] ω = gaussCF (β ω) φ) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
        ω ∈ M ∧ jL ω = junctionL (fun r : ℝ => Wα r.toNNReal ω) s ∧
        jR ω = junctionR (fun r : ℝ => Wα r.toNNReal ω) s ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
            ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) →
          QuantumZipper.fwdHull (fun r : ℝ => drvDec (F (β ω, Hc ω)) r.toNNReal)
              (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t) =
            relMap (fun r : ℝ => Wα r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) t

end GB6

end Supp8

end InteractingSLE
