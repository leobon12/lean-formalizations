import LQGMetric.Gaussian.FerniqueFinite
import LQGMetric.Gaussian.SupTailField
import Mathlib.Topology.UnitInterval

/-!
# Gaussian tails of suprema over a cube (packet F2b)

A centred Gaussian process `X` on the cube `[0,1]^m` with almost surely continuous paths and
increments `E (X_p - X_q)² ≤ L² ‖p - q‖_∞`, `Var X_p ≤ σ²`, satisfies
`P(sup_p |X_p| ≥ x) ≤ 2 exp(M²/(2σ²)) exp(-x²/(4σ²))`, `M = 20 √5 L √(m+1)` (`cube_sup_tail_F2b`).

This is the "Kolmogorov–Chentsov integrability + Borell–TIS" step of the planning audit MA3,
Details P4.4, in its chaining form: the finite-family Dudley bound
`LQGMetric.SupTail.integral_iSup_family_le`, monotone convergence along a dense sequence
(`integrable_iSup_of_continuous`) and Borell–TIS (`tail_iSup_abs_le_gaussian`). The library lemmas
need continuous paths for every `ω`; the process is modified on a null set first.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace HigherDimLFPPAS.Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ}

/-- The coordinates of a point of the cube, as a point of `ℝ^m` with the sup norm. -/
def cubeCoordF2b (p : Fin m → unitInterval) : Fin m → ℝ := fun i => (p i : ℝ)

lemma norm_cubeCoordF2b_sub_le_one (p q : Fin m → unitInterval) :
    ‖cubeCoordF2b p - cubeCoordF2b q‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  simp only [cubeCoordF2b, Pi.sub_apply, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith [(p i).2.1, (p i).2.2, (q i).2.1, (q i).2.2]

/-- **Gaussian tail of the supremum over the cube.** -/
theorem cube_sup_tail_F2b {X : (Fin m → unitInterval) → Ω → ℝ} (hX : IsGaussianProcess X P)
    (h0 : ∀ p, ∫ ω, X p ω ∂P = 0) (hc : ∀ᵐ ω ∂P, Continuous fun p => X p ω) {L σ : ℝ}
    (hL : 0 ≤ L)
    (hinc : ∀ p q, ∫ ω, (X p ω - X q ω) ^ 2 ∂P ≤ L ^ 2 * ‖cubeCoordF2b p - cubeCoordF2b q‖)
    (hvar : ∀ p, Var[X p; P] ≤ σ ^ 2) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | x ≤ ⨆ p, |X p ω|} ≤
      2 * Real.exp ((20 * √5 * L * √((m + 1) * 1)) ^ 2 / (2 * σ ^ 2)) *
        Real.exp (-x ^ 2 / (2 * (2 * σ ^ 2))) := by
  classical
  set S : Set Ω := {ω | Continuous fun p => X p ω} with hSdef
  have hS : P Sᶜ = 0 := ae_iff.mp hc
  set N : Set Ω := toMeasurable P Sᶜ with hNdef
  have hN0 : P N = 0 := by rw [hNdef, measure_toMeasurable]; exact hS
  have hSN : Sᶜ ⊆ N := subset_toMeasurable P Sᶜ
  let X' : (Fin m → unitInterval) → Ω → ℝ := fun p ω => if ω ∈ N then 0 else X p ω
  have hNc : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.mp hN0
  have hae : ∀ p, X p =ᵐ[P] X' p := fun p => by
    filter_upwards [hNc] with ω hω
    simp only [X', hω, ↓reduceIte]
  have hX' : IsGaussianProcess X' P := hX.congr hae
  have h0' : ∀ p, ∫ ω, X' p ω ∂P = 0 := fun p => by
    rw [← integral_congr_ae (hae p)]
    exact h0 p
  have hc' : ∀ ω, Continuous fun p => X' p ω := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [X', hω, ↓reduceIte]
      exact continuous_const
    · have hωS : ω ∈ S := by
        by_contra hn
        exact hω (hSN hn)
      simp only [X', hω, ↓reduceIte]
      exact hωS
  have hinc' : ∀ p q, ∫ ω, (X' p ω - X' q ω) ^ 2 ∂P ≤
      L ^ 2 * ‖cubeCoordF2b p - cubeCoordF2b q‖ := fun p q => by
    have he : (fun ω => (X p ω - X q ω) ^ 2) =ᵐ[P] fun ω => (X' p ω - X' q ω) ^ 2 := by
      filter_upwards [hae p, hae q] with ω h1 h2
      rw [h1, h2]
    rw [← integral_congr_ae he]
    exact hinc p q
  have hvar' : ∀ p, Var[X' p; P] ≤ σ ^ 2 := fun p => by
    rw [← variance_congr (hae p)]
    exact hvar p
  have hfin : ∀ (Y : (Fin m → unitInterval) → Ω → ℝ), IsGaussianProcess Y P → (∀ p, ∫ ω, Y p ω ∂P = 0) →
      (∀ p q, ∫ ω, (Y p ω - Y q ω) ^ 2 ∂P ≤ L ^ 2 * ‖cubeCoordF2b p - cubeCoordF2b q‖) →
      ∀ (n : ℕ) (t : Fin (n + 1) → (Fin m → unitInterval)),
        ∫ ω, (⨆ i, Y (t i) ω) ∂P ≤ 20 * √5 * L * √((m + 1) * 1) := by
    intro Y hY hY0 hYinc n t
    exact LQGMetric.SupTail.integral_iSup_family_le hY hY0 (Nat.succ_pos n) t cubeCoordF2b hL
      (fun i j => norm_cubeCoordF2b_sub_le_one _ _) (fun i j => hYinc _ _)
  obtain ⟨hint, hM⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous hX' hc'
    (hfin X' hX' h0' hinc')
  have hXn := LQGMetric.SupTail.isGaussianProcess_neg hX'
  have hXn0 : ∀ p, ∫ ω, -X' p ω ∂P = 0 := fun p => by rw [integral_neg, h0', neg_zero]
  have hXninc : ∀ p q, ∫ ω, (-X' p ω - -X' q ω) ^ 2 ∂P ≤
      L ^ 2 * ‖cubeCoordF2b p - cubeCoordF2b q‖ := fun p q => by
    have he : (fun ω => (-X' p ω - -X' q ω) ^ 2) = fun ω => (X' p ω - X' q ω) ^ 2 := by
      funext ω
      ring
    rw [he]
    exact hinc' p q
  obtain ⟨hint', hM'⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous hXn
    (fun ω => (hc' ω).neg) (hfin (fun p ω => -X' p ω) hXn hXn0 hXninc)
  have htail := LQGMetric.SupTail.tail_iSup_abs_le_gaussian hX' h0' hc' hint hint' hM hM'
    hvar' hx
  have hsub : {ω | x ≤ ⨆ p, |X p ω|} ⊆ {ω | x ≤ ⨆ p, |X' p ω|} ∪ N := by
    intro ω hω
    by_cases hωN : ω ∈ N
    · exact Or.inr hωN
    · left
      have he : (fun p => |X' p ω|) = fun p => |X p ω| := by
        funext p
        simp only [X', hωN, ↓reduceIte]
      show x ≤ ⨆ p, |X' p ω|
      rw [he]
      exact hω
  calc P.real {ω | x ≤ ⨆ p, |X p ω|}
      ≤ P.real ({ω | x ≤ ⨆ p, |X' p ω|} ∪ N) := measureReal_mono hsub
    _ ≤ P.real {ω | x ≤ ⨆ p, |X' p ω|} + P.real N := measureReal_union_le _ _
    _ = P.real {ω | x ≤ ⨆ p, |X' p ω|} := by
        have hN0' : P.real N = 0 := by simp only [measureReal_def, hN0, ENNReal.toReal_zero]
        rw [hN0', add_zero]
    _ ≤ _ := htail

end HigherDimLFPPAS.Gauss
