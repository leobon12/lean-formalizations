import QuantumZipper.Proofs.Zipper.D3PlusN2Tm
import QuantumZipper.Proofs.Zipper.D3PlusIII

/-!
# D3⁺(i), node N2: the macroscopic decomposition from a continuous harmonic part

Task D3P-N2. Reduces `D3PlusIN2FixMacroStmt` (`D3PlusN2Bridge.lean`) to

* `D3PlusN2HarmPartStmt`: almost surely there is a function `H_ω`, continuous on the whole open
  half-disc `ball 0 r ∩ Hbar`, with `H_ω ∘ foldH` harmonic near `0`, such that
  `X ω (bal μ) = ∫ H_ω dμ` for every dyadic circle `μ ∈ circSet r` (`H_ω(z) = X(P_z)`, the
  Poisson/Neumann extension of the outside field: glue the continuous versions
  `K3.harmH X 0 r r'` for `r' ↑ r` and add `X(P_0)`; `K3.markov_decomposition` on the countably many
  circles; `K3.ae_harmonicOnNhd_harmH`).

`d3PlusIN2FixMacro_of_harm` (own elementary argument): `φ_ω = H_ω − X ω ρ₀ + g ω` (continuous on the
half-disc by `continuousOn_g_of_harm`, harmonic near `0` by `Setup.harm`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- **Continuous harmonic part on the whole half-disc** (a.s.). -/
def D3PlusN2HarmPartStmt : Prop :=
  ∀ (r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), 0 < r → IsFreeGFFModConstH X P →
    ∀ᵐ ω ∂P, ∃ Hω : ℂ → ℝ, ContinuousOn Hω (Metric.ball (0 : ℂ) r ∩ Hbar) ∧
      (∃ ρ > 0, InnerProductSpace.HarmonicOnNhd (fun z => Hω (foldH z)) (Metric.ball (0 : ℂ) ρ)) ∧
      ∀ μ ∈ circSet r, X ω (K3.bal 0 r μ) = ∫ z, Hω z ∂μ

/-- **The macroscopic decomposition from the harmonic part.** -/
theorem d3PlusIN2FixMacro_of_harm (hH : D3PlusN2HarmPartStmt) : D3PlusIN2FixMacroStmt := by
  intro γ α r ρ₀ Ω _ P _ X E' _ Ξ g hS
  filter_upwards [hH r P X hS.hr hS.hX] with ω hω
  obtain ⟨Hω, hc, ⟨ρ, hρ, hharm⟩, hdec⟩ := hω
  have hgc := continuousOn_g_of_harm (hS.harm ω)
  refine ⟨fun z => Hω z - X ω ρ₀ + g ω z, ⟨(hc.sub continuousOn_const).add hgc, min ρ r,
    lt_min hρ hS.hr, ?_⟩, fun μ hμ => ⟨integrable_circ ((hc.sub continuousOn_const).add hgc) hμ,
    ?_⟩⟩
  · exact ((hharm.mono (Metric.ball_subset_ball (min_le_left _ _))).sub
      (InnerProductSpace.harmonicOnNhd_const _)).add
      ((hS.harm ω).mono (Metric.ball_subset_ball (min_le_right _ _)))
  · classical
    have hloc := isLocalH_of_mem_circSet hμ
    have i1 : Integrable Hω μ := integrable_of_admCorr le_rfl hc ⟨μ, hloc⟩
    have i2 : Integrable (fun z => α * -Real.log ‖z‖ + g ω z) μ := integrable_circ hgc hμ
    obtain ⟨d, ρ', -, -, rfl⟩ := exists_of_mem_circSet hμ
    have e : (fun z => α * -Real.log ‖z‖ + (Hω z - X ω ρ₀ + g ω z)) =
        fun z => (Hω z + (α * -Real.log ‖z‖ + g ω z)) - X ω ρ₀ := by
      funext z; ring
    simp only [macroF, if_pos hμ, circVal]
    have i3 : Integrable (fun z => Hω z + (α * -Real.log ‖z‖ + g ω z)) (foldedCircle d ρ') :=
      i1.add i2
    rw [e, integral_sub i3 (integrable_const _), integral_add i1 i2, integral_const,
      Measure.real, measure_univ, ENNReal.toReal_one, one_smul, hdec _ hμ]
    ring

end D3Plus
end QuantumZipper
