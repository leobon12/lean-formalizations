import HigherDimLQGMetric.LogEnergy.Decay
import HigherDimLQGMetric.Gauss.BlockLp
set_option autoImplicit false
noncomputable section
open MeasureTheory
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

theorem annularBlock_logCov_decay {d : ℕ} (hd : 1 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ r r' : ℝ, 0 < r' → r' ≤ ε₀*r →
      ∀ X ∈ annularBlock hh a b r,
        ∀ Y ∈ annularBlock hh a b r',
          |inner ℝ X Y| ≤ C*(r'/r)*(‖X‖*‖Y‖) := by
  obtain ⟨C, ε₀, hC, hε₀, hdecay⟩ := logCov_decay hd ha hab
  refine ⟨C, ε₀, hC, hε₀, ?_⟩
  intro r r' hr' hrr X hX Y hY
  apply inner_abs_le_of_mem_closure (s:=annularPairings hh a b r)
    (t:=annularPairings hh a b r') (C:=C*(r'/r)) ?_ X hX Y hY
  intro X hX Y hY
  rcases hX with ⟨φ, hφ, rfl⟩
  rcases hY with ⟨ψ, hψ, rfl⟩
  rw [lgfPairLp_inner_eq hh φ ψ, lgfPairLp_norm_eq hh φ,
    lgfPairLp_norm_eq hh ψ]
  exact hdecay r r' hr' hrr φ ψ hφ hψ
end HigherDimLQGMetric
