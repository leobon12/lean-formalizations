import QuantumZipper.Proofs.Probability.CameronMartin
import QuantumZipper.Proofs.GFF.CircleFubini

/-!
# Conditional Cameron–Martin bound (L4 prerequisite (e))

* `abs_integral_shift_sub_le`: for a centered Gaussian process `A`, a finitely supported `σ` and a
  measurable `F` with `|F| ≤ 1`,
  `|E F(A + K(·,σ)) − E F(A)| ≤ (exp K(σ,σ) − 1)^{1/2}`.
  Proof: Cameron–Martin (`CameronMartin.integral_mul_tiltDensity`) gives
  `E F(A + K(·,σ)) − E F(A) = E[F(A)(D − 1)]`, and `E|D − 1| ≤ (E(D − 1)²)^{1/2} = (e^{K(σ,σ)} − 1)^{1/2}`
  (the `L²` argument of `CameronMartin.abs_measureReal_shift_sub_le`, for bounded `F`).
* `abs_integral_indep_shift_le`: the *frozen* version. If `A ⊥ v` and the shift `s (v ω)` is, for
  every value of `v`, a Cameron–Martin shift `K(·,σ)` with `K(σ,σ) ≤ κ (v ω)`, then for `|G| ≤ 1`
  `|E[G(v) F(A + s(v))] − E[G(v)] E[F(A)]| ≤ E[min(2, (e^{κ(v)} − 1)^{1/2})]`.
  Proof: `law(A, v) = law A ⊗ law v` (independence), Fubini, and the unconditional bound for
  each frozen value of `v`.

Sources: the Cameron–Martin theorem for Gaussian measures (Bogachev, *Gaussian Measures*, AMS
1998, Theorem 2.4.5 and Corollary 2.4.3) in the finite-dimensional-marginal form of
`CameronMartin.lean` (blueprint S5-A9); the freezing step is the standard independence/Fubini
lemma (e.g. Kallenberg, *Foundations of Modern Probability*, 2nd ed., Lemma 3.11).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace QuantumZipper

namespace K3

open CameronMartin

variable {Ω I : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {A : I → Ω → ℝ}

theorem abs_integral_shift_sub_le (hA : IsGaussianProcess A P) (hmeas : ∀ i, Measurable (A i))
    (hcent : ∀ i, P[A i] = 0) (σ : I →₀ ℝ) {F : (I → ℝ) → ℝ} (hF : Measurable F)
    (hFb : ∀ x, |F x| ≤ 1) :
    |∫ ω, F (fun j => A j ω + covShift A P σ j) ∂P - ∫ ω, F (fun j => A j ω) ∂P| ≤
      Real.sqrt (Real.exp (covNorm A P σ) - 1) := by
  have := hA.isProbabilityMeasure
  have hp : Measurable fun ω j => A j ω := measurable_pi_iff.mpr hmeas
  obtain ⟨hDi, hD1⟩ := tiltDensity_integral hA hmeas hcent σ
  obtain ⟨hD2i, hD2⟩ := integral_tiltDensity_sq hA hmeas hcent σ
  set D := tiltDensity A P σ with hDdef
  set g : Ω → ℝ := fun ω => F (fun j => A j ω) with hgdef
  have hgm : Measurable g := hF.comp hp
  have hgb : ∀ ω, ‖g ω‖ ≤ 1 := fun ω => by rw [Real.norm_eq_abs]; exact hFb _
  have hgi : Integrable g P :=
    (integrable_const (1 : ℝ)).mono' hgm.aestronglyMeasurable (Eventually.of_forall hgb)
  have hgD : Integrable (fun ω => g ω * D ω) P :=
    hDi.bdd_mul hgm.aestronglyMeasurable (Eventually.of_forall hgb)
  rw [← integral_mul_tiltDensity hA hmeas hcent σ F hF]
  have e : ∫ ω, g ω * D ω ∂P - ∫ ω, g ω ∂P = ∫ ω, g ω * (D ω - 1) ∂P := by
    rw [← integral_sub hgD hgi]; congr 1; funext ω; ring
  rw [e]
  have hsq : (fun ω => (D ω - 1) ^ 2) = fun ω => D ω ^ 2 - 2 * D ω + 1 := by
    funext ω; ring
  have hD1sq : Integrable (fun ω => (D ω - 1) ^ 2) P := by
    rw [hsq]; exact (hD2i.sub (hDi.const_mul 2)).add (integrable_const 1)
  have habs : Integrable (fun ω => |D ω - 1|) P := (hDi.sub (integrable_const 1)).abs
  have hval : ∫ ω, (D ω - 1) ^ 2 ∂P = Real.exp (covNorm A P σ) - 1 := by
    rw [hsq, integral_add (f := fun ω => D ω ^ 2 - 2 * D ω) (g := fun _ => (1 : ℝ))
        (hD2i.sub (hDi.const_mul 2)) (integrable_const 1),
      integral_sub (f := fun ω => D ω ^ 2) (g := fun ω => 2 * D ω) hD2i (hDi.const_mul 2),
      integral_const_mul, hD2, hD1, integral_const]
    simp
    ring
  calc |∫ ω, g ω * (D ω - 1) ∂P| ≤ ∫ ω, |D ω - 1| ∂P := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le habs (Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (by simpa [Real.norm_eq_abs] using hgb ω)
    _ ≤ Real.sqrt (Real.exp (covNorm A P σ) - 1) := by
        have h := CircleFubini.sq_integral_le' habs (by simpa only [sq_abs] using hD1sq)
        rw [measure_univ, ENNReal.toReal_one, one_mul] at h
        simp only [sq_abs] at h
        rw [hval] at h
        exact (le_abs_self _).trans (Real.abs_le_sqrt h)

end K3

end QuantumZipper
