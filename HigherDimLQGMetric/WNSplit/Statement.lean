import HigherDimLQGMetric.Core.Defs
import HigherDimLQGMetric.Frozen.OfCont
import HigherDimLQGMetric.Frozen.AddConst
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Probability.Independence.Basic

/-!
# The white-noise split D-WN′ and the law transfer D-LT: statements (packet S5a)

Source: planning audit MA3 (`planning/audits/MA3-sections-5-6.md`), §1.11 (Lemma 6.1, findings
E8–E9), Details (a) **D-WN′** and **D-LT**, and the exact shapes of Details (c)
(`planning/audits/statements/MA3Statements.lean.txt`, `WhiteNoiseSplit`, `NormalizedLawUnique`),
copied verbatim (namespace `HigherDimLQGMetric` instead of `MA3Scratch`, with the frozen surface
and the shared `fieldSigmaOn` of `Core/Defs.lean`, ruling M15 (iii)); blueprint Part A §6
(`prop:wn-split`, `lem:law-transfer`; errata E6.1, E6.2).

* `WhiteNoiseSplit d`: a probability space carrying, for every cutoff `b > 0`, a fine random
  distribution `F b` and a coarse random continuous function `g b` with `F b + g b` a whole-space
  LGF; the fine field has finite range (`σ(F_b|_{B_ρ(w)}) ⊆ 𝒢(B_{ρ + R_𝔎 b}(w), b)`) for a family of
  σ-algebras `𝒢` that are independent over disjoint sets; the coarse oscillation on `B_{5s}(w)` at
  cutoff `Ls` is small in probability, uniformly in `s` and `w`, for `L` large.
* `NormalizedLawUnique d`: the normalized field `h − h_1(0)` has the same law for every LGF on every
  probability space.

The proofs are `whiteNoiseSplit` (`WNSplit/Split.lean`) and `normalizedLawUnique`
(`WNSplit/LawUnique.lean`), both for `d ≥ 2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- **D-WN′** (input of Lemma 6.1; packets F2/S5): a white-noise realization with, for every
cutoff `b > 0`, a fine random distribution `F_b` (scales `< b`) and a coarse random continuous
`g_b` with `F_b + g_b` an LGF; finite range of `F_b` (σ-algebras `𝒢 S b` of the noise on
`S × (0, b)`, independent for disjoint `S`); uniform smallness of the coarse oscillation. -/
def WhiteNoiseSplit (d : ℕ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (𝒢 : Set (Rd d) → ℝ → MeasurableSpace Ω) (Rk : ℝ)
    (F : ℝ → Ω → DistRd d) (g : ℝ → Ω → C(Rd d, ℝ)),
    0 < Rk ∧
    (∀ b, 0 < b → Measurable (F b) ∧ Measurable (g b) ∧
      IsWholeSpaceLGF (fun ω => F b ω + ofCont (g b ω)) P) ∧
    (∀ b, 0 < b → ∀ (w : Rd d) (ρ : ℝ), 0 < ρ →
      fieldSigmaOn (F b) (Metric.ball w ρ) ≤ 𝒢 (Metric.ball w (ρ + Rk * b)) b) ∧
    (∀ b, 0 < b → ∀ (n : ℕ) (S : Fin n → Set (Rd d)),
      Pairwise (fun i j => Disjoint (S i) (S j)) → iIndep (fun i => 𝒢 (S i) b) P) ∧
    (∀ η δ : ℝ, 0 < η → 0 < δ → ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L, L₀ ≤ L → ∀ s : ℝ, 0 < s →
      ∀ w : Rd d, P {ω | ∃ x ∈ Metric.ball w (5 * s), ∃ y ∈ Metric.ball w (5 * s),
        δ < |g (L * s) ω x - g (L * s) ω y|} ≤ ENNReal.ofReal η)

/-- law transfer (packet F2/F3): the normalized field `h − h_1(0)` has the same law for every
LGF on every probability space (port of LQGMetric `GFFLaw.map_eq_of_normalized_ae`). With Weyl
scaling for constants (a.s.), every event defined through normalized metric data therefore has the
same probability for every LGF; this gives all "uniformly over `(Ω, P, h)`" clauses above. -/
def NormalizedLawUnique (d : ℕ) : Prop :=
  ∀ {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] (h : Ω → DistRd d) (h' : Ω' → DistRd d),
    IsWholeSpaceLGF h P → IsWholeSpaceLGF h' P' →
    P.map (fun ω => addConst (h ω) (-sphereAvg (h ω) 1 0)) =
      P'.map (fun ω => addConst (h' ω) (-sphereAvg (h' ω) 1 0))

end HigherDimLQGMetric
