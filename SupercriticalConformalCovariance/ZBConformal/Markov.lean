import SupercriticalConformalCovariance.ZBConformal.GFFLaw
import LQGMetric.Field.MarkovFinal
import LQGMetric.Complex.HarmonicComp
import LQGMetric.Papers.DFGPS.MarkovNorm

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory TopologicalSpace Set Metric
open LQGMetric
open SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.ZBConformal

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {φ : ℂ → ℂ} {U V : Opens ℂ} (hφ : IsConformalBijection φ U V)
  {h : Ω → DistC}

/-- Pulling back the Markov decomposition when the library's normalization and domain conditions hold. -/
theorem exists_pullback_markov_of_normalized
    (hh : IsNormalizedWPGFF h P)
    (hV : Disjoint (V : Set ℂ) (sphere (0 : ℂ) 1)) :
    ∃ z : Ω → DistOn U,
      IsZeroBoundaryGFF U z P ∧
      ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd g (U : Set ℂ) ∧
        ∀ ψ : TestOn U,
          (distPullback hφ (restrictTo V (h ω)) - z ω) ψ = ∫ x, g x * ψ x := by
  obtain ⟨hm, hz, hsum, hharm, _, _, hzb, _, _⟩ :=
    MarkovFinal.lmLem2_1 P h hh V hV
  refine ⟨fun ω => distPullback hφ (restrictTo V (hz ω)),
    isZeroBoundaryGFF_distPullback hφ hzb, ?_⟩
  filter_upwards [hharm] with ω hω
  obtain ⟨g, hg, hgpair⟩ := hω
  refine ⟨g ∘ φ, harmonicOnNhd_comp_holo V.isOpen U.isOpen hg hφ.1 hφ.2.mapsTo, ?_⟩
  intro ψ
  have heq : (restrictTo V (h ω)) (confPushTest hφ ψ) =
      (restrictTo V (hm ω)) (confPushTest hφ ψ) +
      (restrictTo V (hz ω)) (confPushTest hφ ψ) := by
    rw [hsum ω]
    rfl
  rw [sub_apply, distPullback_apply, distPullback_apply, heq,
      add_sub_cancel_right, hgpair]
  exact integral_mul_confPushTest hφ ψ g


/-- A bounded set avoids a sufficiently large normalization circle. -/
theorem exists_radius_disjoint_sphere {V : Opens ℂ}
    (hVb : Bornology.IsBounded (V : Set ℂ)) :
    ∃ r : ℝ, 0 < r ∧ Disjoint (V : Set ℂ) (sphere (0 : ℂ) r) := by
  obtain ⟨R, hR⟩ := hVb.subset_closedBall (0 : ℂ)
  refine ⟨|R| + 1, by positivity, ?_⟩
  apply Set.disjoint_left.mpr
  intro x hxV hxS
  have hle : ‖x‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR hxV
  have heq : ‖x‖ = |R| + 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hxS
  linarith [le_abs_self R]


/-- Markov decomposition after pulling a whole-plane GFF through a conformal map to a bounded
source. The harmonic remainder is measurable and has a harmonic representative almost surely. -/
theorem exists_pullback_markov_bounded
    (hh : IsWholePlaneGFF h P)
    (hVb : Bornology.IsBounded (V : Set ℂ)) :
    ∃ z : Ω → DistOn U,
      IsZeroBoundaryGFF U z P ∧
      Measurable (fun ω => distPullback hφ (restrictTo V (h ω)) - z ω) ∧
      (∀ᵐ ω ∂P, ∃ g : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd g (U : Set ℂ) ∧
        ∀ ψ : TestOn U,
          (distPullback hφ (restrictTo V (h ω)) - z ω) ψ = ∫ x, g x * ψ x) := by
  obtain ⟨r, hr, hdisj⟩ := exists_radius_disjoint_sphere hVb
  let h₀ : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) r 0)
  obtain ⟨hh₀, hn₀⟩ := DFGPS.isNormalizedAt_recenter hh hr 0
  obtain ⟨hm, hz, hsum, hharm, _, _, hzb, _, _⟩ :=
    DFGPS.markov_normAt MarkovFinal.lmLem2_1 P h₀ hh₀ hr 0 hn₀ V hdisj
  let z : Ω → DistOn U := fun ω => distPullback hφ (restrictTo V (hz ω))
  have hzlaw : IsZeroBoundaryGFF U z P := isZeroBoundaryGFF_distPullback hφ hzb
  refine ⟨z, hzlaw, ?_, ?_⟩
  · apply measurable_distOn_iff.mpr
    intro ψ
    have hleft : Measurable (fun ω => distPullback hφ (restrictTo V (h ω)) ψ) :=
      (measurable_distOn_apply ψ).comp
        ((measurable_distPullback hφ).comp ((measurable_restrictTo V).comp hh.measurable))
    have hright : Measurable (fun ω => z ω ψ) :=
      (measurable_distOn_apply ψ).comp hzlaw.measurable
    exact hleft.sub hright
  · filter_upwards [hharm] with ω hω
    obtain ⟨g, hg, hgpair⟩ := hω
    let c : ℝ := circleAvg (h ω) r 0
    have hgharm : InnerProductSpace.HarmonicOnNhd (fun x => g (φ x) + c) (U : Set ℂ) := by
      have hcomp := harmonicOnNhd_comp_holo V.isOpen U.isOpen hg hφ.1 hφ.2.mapsTo
      convert hcomp.add (InnerProductSpace.harmonicOnNhd_const (s := (U : Set ℂ)) c) using 1
      funext x
      rfl
    refine ⟨(fun x => g (φ x) + c), hgharm, ?_⟩
    intro ψ
    let χ : TestOn V := confPushTest hφ ψ
    let t : TestC := TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) χ
    have hsum_eval : (restrictTo V (h₀ ω)) χ =
        (restrictTo V (hm ω)) χ + (restrictTo V (hz ω)) χ := by
      rw [hsum ω]
      rfl
    have hconst_eval : (restrictTo V (h₀ ω)) χ =
        (restrictTo V (h ω)) χ - c * ∫ x, χ x := by
      change addConst (h ω) (-c) t = h ω t - c * ∫ x, χ x
      rw [GFFInv.addConst_apply]
      have ht : ∀ x, t x = χ x := by intro x; simp [t, TestFunction.monoCLM_apply]
      simp_rw [ht]
      ring
    have heq : (restrictTo V (h ω)) χ - (restrictTo V (hz ω)) χ =
        (∫ x, g x * χ x) + c * (∫ x, χ x) := by
      rw [hgpair χ] at hsum_eval
      have hrel : (restrictTo V (h ω)) χ =
          (restrictTo V (h₀ ω)) χ + c * ∫ x, χ x := by
        linarith only [hconst_eval]
      calc
        (restrictTo V (h ω)) χ - (restrictTo V (hz ω)) χ =
            ((restrictTo V (h₀ ω)) χ + c * ∫ x, χ x) -
              (restrictTo V (hz ω)) χ := by rw [hrel]
        _ = ((∫ x, g x * χ x) + (restrictTo V (hz ω)) χ + c * ∫ x, χ x) -
              (restrictTo V (hz ω)) χ := by rw [hsum_eval]
        _ = (∫ x, g x * χ x) + c * (∫ x, χ x) := by ring
    rw [sub_apply, distPullback_apply, distPullback_apply]
    change (restrictTo V (h ω)) χ - (restrictTo V (hz ω)) χ = _
    rw [heq]
    have htrans := integral_mul_confPushTest hφ ψ g
    have hone := integral_mul_confPushTest hφ ψ (fun _ => 1)
    have htrans' : (∫ x, g x * χ x) = ∫ x, g (φ x) * ψ x := by
      simpa only [χ] using htrans
    have hone' : (∫ x, χ x) = ∫ x, ψ x := by
      simpa only [χ, one_mul] using hone
    have hcomp : InnerProductSpace.HarmonicOnNhd (g ∘ φ) (U : Set ℂ) :=
      harmonicOnNhd_comp_holo V.isOpen U.isOpen hg hφ.1 hφ.2.mapsTo
    have hfint : Integrable (fun x => g (φ x) * ψ x) := by
      have hc : ContinuousOn (fun x => g (φ x) * ψ x) (tsupport ψ) :=
        (hcomp.continuousOn.mono ψ.tsupport_subset).mul ψ.continuous.continuousOn
      have hi : IntegrableOn (fun x => g (φ x) * ψ x) (tsupport ψ) (volume : Measure ℂ) :=
        hc.integrableOn_compact ψ.hasCompactSupport.isCompact
      apply hi.integrable_of_forall_notMem_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    have hcint : Integrable (fun x => c * ψ x) :=
      (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).const_mul c
    calc
      (∫ x, g x * χ x) + c * (∫ x, χ x) =
          (∫ x, g (φ x) * ψ x) + c * (∫ x, ψ x) :=
        congrArg₂ (fun a b : ℝ => a + c * b) htrans' hone'
      _ = (∫ x, g (φ x) * ψ x) + (∫ x, c * ψ x) := by rw [integral_const_mul]
      _ = ∫ x, (g (φ x) * ψ x + c * ψ x) := (integral_add hfint hcint).symm
      _ = ∫ x, (g (φ x) + c) * ψ x := by congr 1; funext x; ring

end SupercriticalConformalCovariance.ZBConformal
