import LQGDimension.LFPP.CouplingAux3
import LQGDimension.LFPP.LowerAssemblyAux1
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Sanity checks for the statement's definitions

Small consistency lemmas about the definitions entering `LQGDimension.Statement.Main`,
proved from material already available in `LQGDimension.LFPP.CouplingAux3` and
`LQGDimension.LFPP.LowerAssemblyAux1`.

* `gffCircleCov_psdOn`: for a fixed radius, the circle-average covariance of the GFF is
  positive semidefinite on every finite set of centres.
* `admissible_segment`: the straight segment `t ↦ t` is an admissible LFPP path.
* `lfppDistance_pos`: the LFPP distance of a continuous field is positive.
* `isLFPPExponent_unique`: the LFPP exponent, when it exists, is unique.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real

namespace LQGDimension.Sanity

/-- For each fixed radius `ε`, the circle-average covariance of the GFF is positive
semidefinite on every finite set of centres.  This is partial evidence that
`IsGFFCircleAverage` is consistent: it says the candidate covariance kernel of the process
`z ↦ h ε z` is a genuine covariance kernel on every finite set of centres. -/
theorem gffCircleCov_psdOn {ε : ℝ} (hε : 0 < ε) (F : Finset ℂ) :
    PSDOn F (fun a b => gffCircleCov ε a ε b) := by
  set emb : ℂ ↪ ℂ × Bool := ⟨fun a => (a, true), fun a b h => congrArg Prod.fst h⟩ with hemb
  have hK := Coupling.Kc_psd (ε := ε) 1 hε (F.map emb)
  unfold PSDOn at hK ⊢
  have hsub := hK.submatrix
    (fun i : F => (⟨emb i.1, Finset.mem_map_of_mem emb i.2⟩ : F.map emb))
  have hmat : (Matrix.of fun i j : F.map emb => Coupling.Kc ε 1 i j).submatrix
      (fun i : F => (⟨emb i.1, Finset.mem_map_of_mem emb i.2⟩ : F.map emb))
      (fun i : F => (⟨emb i.1, Finset.mem_map_of_mem emb i.2⟩ : F.map emb)) =
      Matrix.of fun i j : F => gffCircleCov ε i ε j := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    exact Coupling.Kc_tt 1 hε i.1 j.1
  rwa [hmat] at hsub

/-- The straight segment `t ↦ t` is an admissible LFPP path from `0` to `1`. -/
theorem admissible_segment : IsAdmissiblePath (fun t : ℝ => (t : ℂ)) :=
  LowerAsm.admissible_ofReal

/-- The LFPP distance of a continuous field is positive. -/
theorem lfppDistance_pos (ξ : ℝ) {φ : ℂ → ℝ} (hφ : Continuous φ) : 0 < lfppDistance ξ φ :=
  LowerAsm.lfppDistance_pos ξ hφ

/-- The LFPP exponent, when it exists, is unique: limits in probability are unique, so if
`log D^ξ_ε / log ε` tends in `P`-measure to both `l₁` and `l₂` along `ε ↓ 0`, then `l₁ = l₂`. -/
theorem isLFPPExponent_unique {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : ℝ → ℂ → Ω → ℝ} {ξ l₁ l₂ : ℝ}
    (h₁ : IsLFPPExponent h P ξ l₁) (h₂ : IsLFPPExponent h P ξ l₂) : l₁ = l₂ := by
  unfold IsLFPPExponent at h₁ h₂
  have hae : ∀ᵐ _ω : Ω ∂P, l₁ = l₂ := tendstoInMeasure_ae_unique h₁ h₂
  by_contra hne
  rw [ae_iff] at hae
  have hset : {a : Ω | ¬ l₁ = l₂} = Set.univ := Set.eq_univ_of_forall fun _ => hne
  rw [hset, measure_univ] at hae
  exact one_ne_zero hae

end LQGDimension.Sanity
