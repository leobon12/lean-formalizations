import SmallGammaGeodesics.Core.Interfaces
import LQGMetric.Papers.GM.S3.Defs
import LQGMetric.Topo.Disconnect

/-!
# Interface between CC9 and CC10: the good-annulus input ([3] Lemmas 3.8–3.10, D-forms)

Ruling G29. [3] Prop 3.6 (the improvement step `ConfImprove`, packet CC10) consumes the good-annulus
events of [3] Lemmas 3.8–3.10 (packets CC9a/CC9b) only through three properties:
1. annulus-locality with CC7's parameters `c₀ = 4`, `s₁ = 1/16`, `s₂ = 1/2` (the field on
   `A_{r/4,2r}(z)` modulo its circle average at radius `4r`; [3] Lemma 3.8);
2. probability at least any prescribed `p < 1`, uniformly for `z` in a compact `K ⊆ V` and `r ≤ r₀`,
   with `α` and `A` independent of `ϕ`, `δ` and the current constant `C` ([3] Lemma 3.9);
3. the D-forms of conditions 1 and 3 (CC0 D14), exactly the hypotheses `hgood1`, `hgood3` of
   `CC.p36_pair_ext_improve` (`CC/Telescope.lean`).

`GoodAnnulusInput` packages them, so that CC10 (`confImprove_of_goodAnnulus`) and CC9
(`goodAnnulusInput_holds`) can be proved in parallel (interfaces pattern, ruling G10).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.Blueprint

/-- **The good-annulus input** ([3] Lemmas 3.8–3.10 in the form [3] Prop 3.6 consumes): for every
`p < 1` there are `α ∈ (1/2, 1)` and `A ≥ 0`, independent of the map, of `δ` and of the coupling,
such that for every conformal map, every `δ > 0` and every compact `K ⊆ V` there is a scale `r₀`
(independent of the probability space) and, for every coupling, events `E z r` that are
annulus-local (CC7's parameters `c₀ = 4`, `s₁ = 1/16`, `s₂ = 1/2`), have probability `≥ p` for
`z ∈ K`, `r ≤ r₀`, and on which a.s. the D-forms of conditions 1 and 3 hold. -/
def GoodAnnulusInput (γ : ℝ) (D : DistC → ContMetric) : Prop :=
  ∀ p : ℝ, p < 1 → ∃ α A : ℝ, 1 / 2 < α ∧ α < 1 ∧ 0 ≤ A ∧
  ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V → ∀ δ : ℝ, 0 < δ →
  ∀ K : Set ℂ, IsCompact K → K ⊆ V → ∃ r₀ : ℝ, 0 < r₀ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h hbar : Ω → DistC) (f : Ω → C(ℂ, ℝ)),
    IsWholePlaneGFF h P → IsWholePlaneGFF hbar P → Measurable f →
    (∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω)) →
    ∃ E : ℂ → ℝ → Set Ω,
      -- 1. annulus-locality ([3] Lemma 3.8), in the exact form of `IsAnnulusLocal P h E 4 (1/16) (1/2)`
      (∀ z ∈ K, ∀ r ∈ Ioc (0 : ℝ) r₀,
        AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (4 * r) z))
          (annulus z ((1 / 16) * (4 * r)) ((1 / 2) * (4 * r)))) (E z r)) ∧
      -- 2. the probability bound ([3] Lemma 3.9)
      (∀ z ∈ K, ∀ r ∈ Ioc (0 : ℝ) r₀, ENNReal.ofReal p ≤ P (E z r)) ∧
      -- 3. the D-forms of conditions 1 and 3 (`hgood1`, `hgood3` of `p36_pair_ext_improve`)
      ∀ᵐ ω ∂P, ∀ z ∈ K, ∀ r ∈ Ioc (0 : ℝ) r₀, ω ∈ E z r →
        (∀ u ∈ sphere z (α * r), ∀ u' ∈ sphere z r,
          GM.UniqueGeodIn (D (h ω)) u u' (closure (annulus z (α * r) r : Set ℂ)) →
            confMetric D ϕ V (hbar ω) (f ω) u u' ≤
              ENNReal.ofReal ((1 + δ) * (D (h ω)).1 (u, u'))) ∧
        ∃ (a' b' : ℝ) (G : ℝ → ℂ),
          Disconnects (G '' Icc a' b') (sphere z (α * r)) (sphere z r) ∧
          (D (h ω)).len G a' b' ≤
            ENNReal.ofReal A * setDist (D (h ω)) (sphere z (α * r)) (sphere z r)

end SmallGammaGeodesics.CC
