import HigherDimLQGMetric.WNSplit.Statement
import HigherDimLQGMetric.LGF.Normalized
import HigherDimLQGMetric.Sphere.Conv

/-!
# D-LT: the normalized LGF has a unique law (packet S5a, target 2)

Source: MA3 Details (a) **D-LT** (`planning/audits/MA3-sections-5-6.md`), blueprint
`lem:law-transfer`; statement `NormalizedLawUnique` (MA3 Details (c), verbatim in
`WNSplit/Statement.lean`).

For `d ≥ 2` and any two whole-space LGFs `h`, `h'` (on any probability spaces), the normalized
fields `h − h_1(0)` and `h' − h'_1(0)` have the same law on `𝒟'(ℝ^d)` (`normalizedLawUnique`).

Proof: the mollified unit-sphere averages of every LGF converge a.s. (packet F3,
`IsWholeSpaceLGF.ae_exists_tendsto_sphereAvgSeq`), so `h − h_1(0)` is a normalized LGF (packet F2,
`IsWholeSpaceLGF.isNormalizedLGF_normalize`), and two normalized LGFs whose unit-sphere averages
converge a.s. have the same law (F2, `IsNormalizedLGF.map_eq`, the port of LQGMetric's
`GFFLaw.map_eq_of_normalized_ae`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The normalized field of an LGF (`d ≥ 2`) is a normalized LGF whose unit-sphere averages at `0`
converge almost surely. -/
theorem IsWholeSpaceLGF.wns_normalize {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistRd d} (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) :
    IsNormalizedLGF (fun ω => HigherDimLQGMetric.addConst (h ω) (-sphereAvg (h ω) 1 0)) P ∧
      ∀ᵐ ω ∂P, HigherDimLQGMetric.addConst (h ω) (-sphereAvg (h ω) 1 0) ∈ convSet d := by
  have hc : ∀ᵐ ω ∂P, h ω ∈ convSet d := hh.ae_exists_tendsto_sphereAvgSeq hd one_pos 0
  have hn := hh.isNormalizedLGF_normalize (by omega) hc
  exact ⟨hn, hn.1.ae_exists_tendsto_sphereAvgSeq hd one_pos 0⟩

/-- **D-LT, law transfer** (`NormalizedLawUnique d`, MA3 Details (c), verbatim): for `d ≥ 2`, the
normalized field `h − h_1(0)` has the same law for every whole-space LGF on every probability
space. -/
theorem normalizedLawUnique (hd : 2 ≤ d) : NormalizedLawUnique d := by
  intro Ω Ω' _ _ P P' _ _ h h' hh hh'
  obtain ⟨hn, hc⟩ := hh.wns_normalize hd
  obtain ⟨hn', hc'⟩ := hh'.wns_normalize hd
  exact IsNormalizedLGF.map_eq (by omega) hn hn' hc hc'

end HigherDimLQGMetric
