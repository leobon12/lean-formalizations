import QuantumZipper.Proofs.Probability.LengthMarkov
import QuantumZipper.Proofs.Zipper.B2Defs

/-!
# E-SM-inst (b): strong Markov at the length times of the zipper

Node **E-SM-inst (b)** of `handoff/E-PLAN-2.md` (blueprint `blueprint/E_BRANCH_BLUEPRINT.md`,
node E-SM). This is E-SM-abs (`LengthMarkov.lintegral_levelTime_strongMarkov`) instantiated with
the left quantum length `A s ω = L⁻_s := (unzipLengths √κ (cfg κ B X ω) s).1` of the unzipped
segment `η[0,s]` of the `Γ⁰` sample `𝒵 = cfg κ B X ω`, and with the path functional read through
the driver of the unzipped configuration: at the length time `T_ℓ = levelTime L⁻ S ℓ`, the
driver `(zipCapDown √κ T_ℓ 𝒵).2 = √κ · smPath B T_ℓ` of the remaining curve is a Brownian
driver independent of `𝓕_{T_ℓ}` (Sheffield, arXiv:1012.4797, proof of Lemma 5.6 / Thm 1.8:
"unzipping by a stopping time leaves an SLE driven by a fresh Brownian motion").

The three properties of `L⁻` used here (continuity and monotonicity in `s` for every `ω`,
`𝓕`-adaptedness) are the B5 deliverables; they are explicit hypotheses (`hAc`, `hAmono`,
`hAad`), exactly as in E-SM-abs.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ESM

open LengthMarkov StrongMarkov B2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The left quantum length `L⁻_s = (unzipLengths √κ 𝒵 s).1` of the `Γ⁰` sample. -/
noncomputable def lenMinus (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (s : ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  (unzipLengths (Real.sqrt κ) (cfg κ B X ω) s).1

/-- The driver `s ↦ √κ · p (s⁺)` read from a path `p : ℝ≥0 → ℝ`. -/
noncomputable def drvMap (κ : ℝ) (p : ℝ≥0 → ℝ) : ℝ → ℝ := fun s => Real.sqrt κ * p s.toNNReal

lemma measurable_drvMap (κ : ℝ) : Measurable (drvMap κ) :=
  Measurable.of_eval fun (s : ℝ) => (measurable_pi_apply s.toNNReal).const_mul _

lemma drvMap_path (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    drvMap κ (fun t => B t ω) = drive κ B ω := rfl

/-- The driver of `zipCapDown √κ t 𝒵` is `√κ` times the restarted Brownian path. -/
lemma zipCapDown_cfg_snd (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (T : Ω → ℝ≥0)
    (ω : Ω) : (zipCapDown (Real.sqrt κ) (T ω : ℝ) (cfg κ B X ω)).2 = drvMap κ (smPath B T ω) := by
  funext s
  have h1 : ((T ω : ℝ) + max s 0).toNNReal = T ω + s.toNNReal := by
    apply NNReal.eq
    simp only [Real.coe_toNNReal', NNReal.coe_add]
    exact max_eq_left (add_nonneg (T ω).2 (le_max_right _ _))
  simp only [zipCapDown, cfg, drive, drvMap, smPath, smShift, Real.toNNReal_coe, h1]
  ring

end ESM
end QuantumZipper
