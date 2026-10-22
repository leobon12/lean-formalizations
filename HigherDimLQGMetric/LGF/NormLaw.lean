import HigherDimLQGMetric.LGF.Exists
import HigherDimLQGMetric.LGF.Normalized

/-!
# The sanity anchor `normLGFLaw_spec`, reduced to sphere-average convergence (packet F2, target 4)

With the existence of the LGF (target 1, `exists_isWholeSpaceLGF`) the only remaining input of the
frozen sanity anchor `normLGFLaw_spec` is the almost sure convergence of the mollified unit-sphere
averages of an LGF (`SphereConvAS d`), which needs the sphere-average covariances of packet F3:

* `exists_isWholeSpaceLGF_law`: the law of an LGF on `𝒟'(ℝ^d)` (realized by `id`);
* `normLGFLaw_spec_of_sphereConvAS`: `SphereConvAS d → ` the statement of `normLGFLaw_spec` at `d`;
* `normLGFLaw_spec_of_sphereAvg_spec'`: the statement of the frozen `sphereAvg_spec` implies the
  statement of the frozen `normLGFLaw_spec` (both copied verbatim; the frozen theorem anchors are
  not imported). When F3 seals `sphereAvg_spec`, `normLGFLaw_spec` is
  `normLGFLaw_spec_of_sphereAvg_spec' sphereAvg_spec_impl`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The law on `𝒟'(ℝ^d)` of the whole-space LGF (`d ≥ 1`). -/
theorem exists_isWholeSpaceLGF_law (hd : 1 ≤ d) :
    ∃ μ : Measure (DistRd d), IsProbabilityMeasure μ ∧ IsWholeSpaceLGF id μ := by
  obtain ⟨Ω, _, P, h, hP, hh⟩ := exists_isWholeSpaceLGF hd
  exact ⟨P.map h, inferInstance, hh.map_id⟩

/-- **Target 4 at fixed `d`**: given the a.s. convergence of the unit-sphere averages of LGFs
(`SphereConvAS d`, packet F3), `normLGFLaw d` is a probability measure, the law of a normalized LGF,
and the only such law. -/
theorem normLGFLaw_spec_of_sphereConvAS (hd : 1 ≤ d) (hS : SphereConvAS d) :
    IsProbabilityMeasure (normLGFLaw d) ∧ IsNormalizedLGF id (normLGFLaw d) ∧
      ∀ μ : Measure (DistRd d), IsProbabilityMeasure μ → IsNormalizedLGF id μ →
        μ = normLGFLaw d := by
  obtain ⟨Ω, m, P, h, -, hh⟩ := exists_isWholeSpaceLGF hd
  exact normLGFLaw_spec_of_sphereConv hd ⟨Ω, m, P, h, hh⟩ hS

/-- **The reduction `normLGFLaw_spec ⇐ sphereAvg_spec`** (target 4): the statement of the frozen
characterization anchor `sphereAvg_spec` implies the statement of the frozen sanity anchor
`normLGFLaw_spec`. -/
theorem normLGFLaw_spec_of_sphereAvg_spec'
    (hspec : ∀ (d : ℕ), 2 ≤ d → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsLGFPlusCont h P → ∀ r : ℝ, 0 < r →
        ∀ z : Rd d, ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫ u, h ω (bumpTest n (z + r • u))
          ∂(unitSphereProb d)) atTop (𝓝 (sphereAvg (h ω) r z))) :
    ∀ (d : ℕ), 2 ≤ d → IsProbabilityMeasure (normLGFLaw d) ∧ IsNormalizedLGF id (normLGFLaw d) ∧
      ∀ μ : Measure (DistRd d), IsProbabilityMeasure μ → IsNormalizedLGF id μ →
        μ = normLGFLaw d :=
  fun d hd => normLGFLaw_spec_of_sphereConvAS (by omega)
    (sphereConvAS_of_sphereAvg_spec (hspec d hd))

end HigherDimLQGMetric
