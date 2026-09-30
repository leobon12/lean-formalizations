import QuantumZipper.Proofs.Zipper.D3PlusStmt
import QuantumZipper.Proofs.GFF.Existence
import QuantumZipper.Proofs.GFF.CircleMeanValue
import QuantumZipper.Proofs.GFF.LateralGerm
import QuantumZipper.Proofs.GFF.K3.MixedM7Nodes

/-!
# D3⁺: the hypotheses `Setup` are satisfiable (fidelity check)

`exists_setup`: for all `0 < γ < 2`, `α < Q`, `r > 0` there is a free field `X` on a probability
space such that `Setup γ α r (foldedCircle 0 (2r)) P X Ξ g` holds with `Ξ` trivial and `g = 0`.
So `D3PlusIIIStmt` (proved) and the open `D3PlusIStmt`, `D3PlusIIStmt` are not vacuous.

`Setup.mono_radius`: the hypotheses pass to smaller radii (used by E5, which applies LSC on
`ball 0 (r/2)`, and to match D22's `d3plus_data` at radius `r' < r`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace QuantumZipper
namespace D3Plus

theorem exists_setup {γ α r : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) (hr : 0 < r) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → FieldSample),
      IsProbabilityMeasure P ∧
      Setup γ α r (foldedCircle 0 (2 * r)) P X (fun _ => ()) (fun _ _ => (0 : ℝ)) := by
  obtain ⟨Ω, mΩ, P, X, hP, hX⟩ := exists_freeGFF
  refine ⟨Ω, mΩ, P, X, hP, ?_⟩
  exact
    { hγ := hγ
      hγ2 := hγ2
      hα := hα
      hr := hr
      hX := hX
      hΞ := measurable_const
      hind := by
        rw [MeasurableSpace.comap_const]
        exact indep_bot_left _
      hρ := isAdmissibleH_foldedCircle (by simp [Hbar]) (by positivity)
      hρ1 := measure_univ
      hρB := LateralGerm.foldedCircle_ball_eq_zero hr (by linarith)
      harm := fun _ => by simp
      gmeas := fun _ => measurable_const }

/-- `Setup` passes to smaller radii. -/
theorem Setup.mono_radius {γ α r r' : ℝ} {ρ₀ : Measure ℂ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → FieldSample} {E' : Type*} [MeasurableSpace E'] {Ξ : Ω → E'}
    {g : Ω → ℂ → ℝ} (hS : Setup γ α r ρ₀ P X Ξ g) (hr' : 0 < r') (hle : r' ≤ r) :
    Setup γ α r' ρ₀ P X Ξ g :=
  { hS with
    hr := hr'
    hρB := measure_mono_null (Metric.ball_subset_ball hle) hS.hρB
    harm := fun ω z hz => hS.harm ω z (Metric.ball_subset_ball hle hz)
    gmeas := fun z => (hS.gmeas z).mono
      (sup_le_sup_left (K3.outsideSigma_anti_radius X 0 hle) _) le_rfl }

end D3Plus
end QuantumZipper
