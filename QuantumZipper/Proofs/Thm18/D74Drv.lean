import QuantumZipper.Proofs.Thm18.G4Zero
import QuantumZipper.Proofs.Thm18.G4ReadFix
import QuantumZipper.Proofs.Thm18.G4WeldRound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D74: the drivers of zipped configurations are continuous and start at `0`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (p. 26): the
zipped/unzipped configurations are again pairs (field, driving function) with a continuous
driving function started at `0`. Deterministic facts about the constructive maps `zipLenUpC`,
`zipLenDown`, `zipLenC` and the a.s. consequences in the Theorem 1.8 setting.
Own elementary argument (unfolding definitions; the pattern of
`G4Core.continuous_zipLenC_snd`, but reading the chosen driver via `lenWeldDriver_spec`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace D74

theorem zipLenUpC_snd_good {γ ℓ : ℝ} {c : FieldSample × (ℝ → ℝ)} (hc : Continuous c.2)
    (hc0 : c.2 0 = 0) (h : ∃ p, IsLenWeldingDriver γ c.1 ℓ p) :
    Continuous (zipLenUpC γ ℓ c).2 ∧ (zipLenUpC γ ℓ c).2 0 = 0 := by
  obtain ⟨hT, hpc, hpz, -⟩ := lenWeldDriver_spec h
  set p := lenWeldDriver γ c.1 ℓ with hp
  have hV : Continuous (zipWeldUp γ p.1 p.2 c).2 := by
    simp only [zipWeldUp]
    refine Continuous.if_le ((hpc.comp (continuous_const.sub
      (continuous_id.max continuous_const))).sub continuous_const)
      ((hc.comp (continuous_id.sub continuous_const)).sub continuous_const) continuous_id
      continuous_const fun s hs => ?_
    rw [hs, max_eq_left hT, sub_self, hpz, hc0]
  refine ⟨?_, ?_⟩
  · simp only [zipLenUpC, canonConfig]
    rw [← hp]
    exact (hV.comp (continuous_const.mul (continuous_id.max continuous_const))).div_const _
  · simp only [zipLenUpC, canonConfig, zipWeldUp]
    rw [← hp]
    simp [hT]

theorem ae_wedgeConfig_snd_good {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) :
    ∀ᵐ ω ∂P, Continuous (wedgeConfig γ B Y ω).2 ∧ (wedgeConfig γ B Y ω).2 0 = 0 := by
  filter_upwards [ae_continuous_wedgeConfig_snd hS, hS.2.2.1.eval_zero_ae_eq_zero]
    with ω hc h0
  exact ⟨hc, drive_zero h0⟩

end D74
end Thm18Asm
end QuantumZipper
