import HigherDimLQGMetric.Frozen.KernelSymbol
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Smooth fixed-interval parameter integrals

For the A2.4 auxiliary, we differentiate an integral over a fixed compact interval.
Mathlib's local dominated differentiation theorem and compactness give a generic
smoothness result on the project's Euclidean spaces.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)

private theorem param_partial_contDiff {d : ℕ} {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Rd d → ℝ → F) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f.uncurry) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (fun x : Rd d => fun u : ℝ => fderiv ℝ (f · u) x)) := by
  have hcomp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (fun p : Rd d × ℝ => fun y : Rd d => f y p.2)) := by
    exact hf.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Rd d × ℝ => fderiv ℝ (fun y : Rd d => f y p.2) p.1) :=
    hcomp.fderiv contDiff_fst (by simp)
  exact hh

private theorem param_deriv {d : ℕ} {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : Rd d → ℝ → F) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f.uncurry)
    (x₀ : Rd d) :
    HasFDerivAt (fun x : Rd d => ∫ u in Icc (0 : ℝ) 1, f x u)
      (∫ u in Icc (0 : ℝ) 1, fderiv ℝ (f · u) x₀) x₀ := by
  let f' : Rd d → ℝ → Rd d →L[ℝ] F := fun x u => fderiv ℝ (f · u) x
  have hf' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f'.uncurry :=
    param_partial_contDiff f hf
  have hcont : Continuous f.uncurry := hf.continuous
  have hcont' : Continuous f'.uncurry := hf'.continuous
  let K : Set (Rd d × ℝ) := Metric.closedBall x₀ 1 ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := (isCompact_closedBall x₀ 1).prod isCompact_Icc
  have hb : Bornology.IsBounded (f'.uncurry '' K) := (hK.image hcont').isBounded
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Icc (0 : ℝ) 1))
    (F := f) (F' := f') (x₀ := x₀)
    (s := Metric.closedBall x₀ 1) (bound := fun _ => C)
  · exact Filter.mem_of_superset (Metric.ball_mem_nhds x₀ (by norm_num : (0:ℝ)<1))
      Metric.ball_subset_closedBall
  · filter_upwards with x
    exact (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hcont.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact isCompact_Icc
  · exact (hcont'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem₀
      ((measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) 1)).nullMeasurableSet)] with u hu
    intro x hx
    exact hC (f'.uncurry (x,u)) ⟨⟨x,u⟩, ⟨hx,hu⟩, rfl⟩
  · exact integrable_const C
  · filter_upwards with u
    intro x hx
    have hfu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Rd d => f y u) :=
      hf.comp (contDiff_id.prodMk contDiff_const)
    exact ((hfu.differentiable (by simp)) x).hasFDerivAt

private theorem param_contDiff_aux {d : ℕ} (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F],
      ∀ (f : Rd d → ℝ → F),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f.uncurry →
        ContDiff ℝ (n : WithTop ℕ∞)
          (fun x : Rd d => ∫ u in Icc (0 : ℝ) 1, f x u) := by
  induction n with
  | zero =>
      intro F _ _ _ f hf
      rw [show ((0 : ℕ) : WithTop ℕ∞) = 0 by rfl, contDiff_zero]
      exact continuous_parametric_integral_of_continuous (μ := volume) hf.continuous
        (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  | succ n ih =>
      intro F _ _ _ f hf
      have hd : Differentiable ℝ (fun x : Rd d => ∫ u in Icc (0 : ℝ) 1, f x u) :=
        fun x => (param_deriv f hf x).differentiableAt
      let f' : Rd d → ℝ → Rd d →L[ℝ] F := fun x u => fderiv ℝ (f · u) x
      have hf' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f'.uncurry :=
        param_partial_contDiff f hf
      have hi := ih (Rd d →L[ℝ] F) f' hf'
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp,
        contDiff_succ_iff_fderiv]
      refine ⟨hd, by simp, ?_⟩
      convert hi using 1
      funext x
      exact (param_deriv f hf x).fderiv

/-- A jointly smooth integrand over `[0,1]` has a smooth parameter integral. -/
theorem contDiff_setIntegral_Icc_of_contDiff {d : ℕ} {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : Rd d → ℝ → F) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f.uncurry) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Rd d => ∫ u in Icc (0 : ℝ) 1, f x u) := by
  rw [contDiff_infty]
  intro n
  exact param_contDiff_aux n F f hf

end HigherDimLQGMetric
