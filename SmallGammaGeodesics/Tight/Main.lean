import SmallGammaGeodesics.Tight.Band
import SmallGammaGeodesics.Upper.MainMean

/-!
# §6 assembly: functional tightness on the coordinate space

The glue of P-T1's handoff (`planning/handoffs/P-T1.md`, Details §5), after P-U3:
* `bandEv_scale_le`: the band events at scale `K δ_γ` from Lemma 5.1 (`lemma51`) and the mean bound
  (`mean_maxDev_le`), via `bandEv_scale_le_of_lemma51`;
* `tight_compact`: the compact sets of Theorem 1.2 (`tight_compact_of_bandScale`);
* `tightConcl_of_interfaces`: the conclusion `TightConcl` of Theorem 1.2 on the coordinate space, with
  the interface hypotheses `hCC` and `h42` (ruling G10), discharged at assembly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open GaussianLQG LQGMetric LQGMetric.Blueprint

/-- the band events at scale `K δ_γ` have probability `≲ K^{-3} + K^{-4}` on the good event -/
theorem bandEv_scale_le (G : GSetup) (hCC : ∀ γ, 0 < γ → γ < 2 → CC.ConfCovLE γ (G.Dfam γ))
    (h42 : Lemma42) :
    ∃ C, ∀ η : ℝ → Coord → C(unitInterval, ℂ), (∀ γ, Measurable (η γ)) →
      (∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η γ ω)) →
      ∀ K, 1 ≤ K → ∀ ε, 0 < ε → ∀ᶠ γ in 𝓝[>] (0:ℝ),
        stdP {ω | goodEv G γ ω ∧ bandEv γ (K * dlt γ) (η γ ω)} ≤
          ENNReal.ofReal (C * (K ^ (-3:ℝ) + K ^ (-4:ℝ)) + ε) :=
  bandEv_scale_le_of_lemma51 G (lemma51 G hCC h42) (mean_maxDev_le G hCC h42)

/-- **Tightness** (Theorem 1.2, compact-set form, ruling G12) on the coordinate space -/
theorem tight_compact (G : GSetup) (hCC : ∀ γ, 0 < γ → γ < 2 → CC.ConfCovLE γ (G.Dfam γ))
    (h42 : Lemma42) (η : ℝ → Coord → C(unitInterval, ℂ)) (hm : ∀ γ, Measurable (η γ))
    (hη : ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η γ ω)) :
    ∀ ε : ℝ, 0 < ε → ∃ K : Set C(unitInterval, ℂ), IsCompact K ∧
      ∀ᶠ γ in 𝓝[>] (0:ℝ),
        stdP {ω | rescaledPath (γ ^ (2/3 : ℝ)) (η γ ω) ∉ K} ≤ ENNReal.ofReal ε := by
  obtain ⟨C, hC⟩ := bandEv_scale_le G hCC h42
  exact tight_compact_of_bandScale G η hη C (hC η hm hη)

/-- **Theorem 1.2 on the coordinate space** (a.e.-measurability, tightness, (1.11)) -/
theorem tightConcl_of_interfaces (G : GSetup)
    (hCC : ∀ γ, 0 < γ → γ < 2 → CC.ConfCovLE γ (G.Dfam γ)) (h42 : Lemma42)
    (η : ℝ → Coord → C(unitInterval, ℂ)) (hm : ∀ γ, Measurable (η γ))
    (hη : ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η γ ω)) :
    TightConcl stdP η :=
  ⟨aemeasurable_rescaled η hm, tight_compact G hCC h42 η hm hη,
    tendstoInMeasure_horizDev G η hm hη⟩

end SmallGammaGeodesics
