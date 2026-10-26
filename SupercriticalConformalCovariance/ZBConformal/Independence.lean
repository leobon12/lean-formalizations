import SupercriticalConformalCovariance.ZBConformal.Markov

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace Set Metric
open LQGMetric SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.ZBConformal

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {φ : ℂ → ℂ} {U V : Opens ℂ} (hφ : IsConformalBijection φ U V)
  {h : Ω → DistC}

/-- Full-process independence in the normalized Markov decomposition, preserved by conformal
transport. The zero-boundary process is the first argument, as in the TV mixture lemma. -/
theorem exists_pullback_markov_normalized_independent
    (hh : IsNormalizedWPGFF h P)
    (hV : Disjoint (V : Set ℂ) (sphere (0 : ℂ) 1)) :
    ∃ z m : Ω → DistOn U,
      IsZeroBoundaryGFF U z P ∧
      (∀ ω, distPullback hφ (restrictTo V (h ω)) = m ω + z ω) ∧
      IndepFun (fun ω (ψ : TestOn U) => z ω ψ) m P := by
  obtain ⟨hm, hz, hsum, _, _, hind, hzb, _, _⟩ :=
    MarkovFinal.lmLem2_1 P h hh V hV
  let F : DistC → DistOn U := fun T => distPullback hφ (restrictTo V T)
  have hFm : Measurable F :=
    (measurable_distPullback hφ).comp (measurable_restrictTo V)
  let z : Ω → DistOn U := F ∘ hz
  let m : Ω → DistOn U := F ∘ hm
  have hzlaw : IsZeroBoundaryGFF U z P := isZeroBoundaryGFF_distPullback hφ hzb
  have hind' : IndepFun z m P := hind.symm.comp hFm hFm
  have hcoord : Measurable (fun T : DistOn U => fun ψ : TestOn U => T ψ) :=
    measurable_pi_iff.2 fun ψ => measurable_distOn_apply ψ
  refine ⟨z, m, hzlaw, ?_, ?_⟩
  · intro ω
    rw [hsum ω]
    change F (hm ω + hz ω) = F (hm ω) + F (hz ω)
    ext ψ
    simp only [F, distPullback_apply, add_apply]
    rfl
  · exact hind'.comp hcoord measurable_id

end SupercriticalConformalCovariance.ZBConformal
