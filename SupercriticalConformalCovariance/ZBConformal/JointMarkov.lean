import SupercriticalConformalCovariance.ZBConformal.HarmonicRepresentative

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter Topology
open LQGMetric SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.ZBConformal

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {φ : ℂ → ℂ} {U V : Opens ℂ} (hφ : IsConformalBijection φ U V)
  {h : Ω → DistC}

/-- The circle-normalized Markov theorem with an explicit jointly measurable harmonic representative.
The independence statement has the entire zero-boundary test process as its first argument. -/
theorem exists_pullback_markov_normAt_joint
    (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r)
    (hn : ∀ᵐ ω ∂P, circleAvg (h ω) r 0 = 0)
    (hV : Disjoint (V : Set ℂ) (sphere (0 : ℂ) r)) :
    ∃ (z : Ω → DistOn U) (H : Ω → ℂ → ℝ),
      IsZeroBoundaryGFF U z P ∧
      Measurable (fun p : Ω × U => H p.1 p.2) ∧
      IndepFun (fun ω (ψ : TestOn U) => z ω ψ)
        (fun ω (x : U) => H ω x) P ∧
      (∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (H ω) (U : Set ℂ) ∧
        ∀ ψ : TestOn U,
          (distPullback hφ (restrictTo V (h ω)) - z ω) ψ =
            ∫ x, H ω x * ψ x) := by
  classical
  obtain ⟨hm, hz, hsum, hharm, ⟨G, hGm, hhG⟩, hind, hzb, _, _⟩ :=
    DFGPS.markov_normAt MarkovFinal.lmLem2_1 P h hh hr 0 hn V hV
  have hGm' : Measurable G :=
    hGm.mono (MarkovZBIndep.fieldSigmaClosed_le hh _) le_rfl
  let z : Ω → DistOn U := fun ω => distPullback hφ (restrictTo V (hz ω))
  let H : Ω → ℂ → ℝ := pulledHarm hφ G (fun _ => 0)
  have hzlaw : IsZeroBoundaryGFF U z P := isZeroBoundaryGFF_distPullback hφ hzb
  have hHm : Measurable (fun p : Ω × U => H p.1 p.2) :=
    measurable_pulledHarm V hφ hGm' measurable_const
  have hcoord : Measurable (fun T : DistC => fun ψ : TestOn U =>
      distPullback hφ (restrictTo V T) ψ) :=
    measurable_pi_iff.2 fun ψ => (measurable_distOn_apply ψ).comp
      ((measurable_distPullback hφ).comp (measurable_restrictTo V))
  have hHproc : Measurable (fun T : DistC => fun x : U =>
      canonicalHarmExt V T (φ x)) :=
    measurable_pi_iff.2 fun x => (measurable_canonicalHarmExt V).comp
      (Measurable.prodMk measurable_id measurable_const)
  refine ⟨z, H, hzlaw, hHm, ?_, ?_⟩
  · have hindG : IndepFun hz G P :=
      hind.symm.congr (EventuallyEq.refl _ _) hhG
    have hI := hindG.comp hcoord hHproc
    have hzeq : (fun ω (ψ : TestOn U) => z ω ψ) =
        (fun T ψ => distPullback hφ (restrictTo V T) ψ) ∘ hz := rfl
    have hHeq : (fun ω (x : U) => H ω x) =
        (fun T (x : U) => canonicalHarmExt V T (φ x)) ∘ G := by
      funext ω x
      change (if (x : ℂ) ∈ U then canonicalHarmExt V (G ω) (φ x) + 0 else 0) = _
      simp [x.property]
    rw [hzeq, hHeq]
    exact hI
  · filter_upwards [hharm, hhG] with ω ⟨g, hg, hrep⟩ hω
    have hrepG : ∀ ψ : TestOn V, restrictTo V (G ω) ψ = ∫ x, g x * ψ x := by
      intro ψ
      rw [← hω]
      exact hrep ψ
    have hpoint : ∀ x ∈ (U : Set ℂ), H ω x = g (φ x) := by
      intro x hx
      change (if x ∈ U then canonicalHarmExt V (G ω) (φ x) + 0 else 0) = _
      split_ifs with hxu
      · simpa using canonicalHarmExt_eq V hg hrepG (hφ.2.mapsTo hx)
      · exact False.elim (hxu hx)
    have hcomp : InnerProductSpace.HarmonicOnNhd (g ∘ φ) (U : Set ℂ) :=
      harmonicOnNhd_comp_holo V.isOpen U.isOpen hg hφ.1 hφ.2.mapsTo
    have hHharm : InnerProductSpace.HarmonicOnNhd (H ω) (U : Set ℂ) := by
      intro x hx
      have he : H ω =ᶠ[𝓝 x] g ∘ φ := by
        filter_upwards [U.isOpen.mem_nhds hx] with y hy
        exact hpoint y hy
      exact (InnerProductSpace.harmonicAt_congr_nhds he).2 (hcomp x hx)
    refine ⟨hHharm, fun ψ => ?_⟩
    have hpair : (distPullback hφ (restrictTo V (h ω)) - z ω) ψ =
        (restrictTo V (hm ω)) (confPushTest hφ ψ) := by
      have heq : (restrictTo V (h ω)) (confPushTest hφ ψ) =
          (restrictTo V (hm ω)) (confPushTest hφ ψ) +
            (restrictTo V (hz ω)) (confPushTest hφ ψ) := by
        rw [hsum ω]
        rfl
      rw [sub_apply, distPullback_apply, distPullback_apply, heq, add_sub_cancel_right]
    rw [hpair, hrep, integral_mul_confPushTest hφ ψ g]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : ψ x = 0
      · simp [hx]
      · change g (φ x) * ψ x = H ω x * ψ x
        rw [hpoint x (ψ.tsupport_subset (subset_tsupport _ hx))]

/-- Bounded-domain whole-plane Markov decomposition with a jointly measurable harmonic
representative. This does not assert independence for an arbitrary random additive constant. -/
theorem exists_pullback_markov_bounded_joint
    (hh : IsWholePlaneGFF h P)
    (hVb : Bornology.IsBounded (V : Set ℂ)) :
    ∃ (z : Ω → DistOn U) (H : Ω → ℂ → ℝ),
      IsZeroBoundaryGFF U z P ∧
      Measurable (fun p : Ω × U => H p.1 p.2) ∧
      (∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (H ω) (U : Set ℂ) ∧
        ∀ ψ : TestOn U,
          (distPullback hφ (restrictTo V (h ω)) - z ω) ψ =
            ∫ x, H ω x * ψ x) := by
  obtain ⟨r, hr, hdisj⟩ := exists_radius_disjoint_sphere hVb
  let c : Ω → ℝ := fun ω => circleAvg (h ω) r 0
  have hcm : Measurable c := (measurable_circleAvg_left r 0).comp hh.measurable
  let h₀ : Ω → DistC := fun ω => addConst (h ω) (-c ω)
  obtain ⟨hh₀, hn₀⟩ := DFGPS.isNormalizedAt_recenter hh hr 0
  obtain ⟨z, H₀, hzlaw, hHm, _, hpair⟩ :=
    exists_pullback_markov_normAt_joint hφ hh₀ hr hn₀ hdisj
  let H : Ω → ℂ → ℝ := fun ω x => H₀ ω x + c ω
  have hHm' : Measurable (fun p : Ω × U => H p.1 p.2) :=
    hHm.add (hcm.comp measurable_fst)
  refine ⟨z, H, hzlaw, hHm', ?_⟩
  filter_upwards [hpair] with ω ⟨hHarm, hrep⟩
  have hHarm' : InnerProductSpace.HarmonicOnNhd (H ω) (U : Set ℂ) := by
    convert hHarm.add (InnerProductSpace.harmonicOnNhd_const (s := (U : Set ℂ)) (c ω)) using 1
    funext x
    rfl
  refine ⟨hHarm', fun ψ => ?_⟩
  let χ : TestOn V := confPushTest hφ ψ
  let t : TestC := TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) χ
  have hconst_eval : (restrictTo V (h₀ ω)) χ =
      (restrictTo V (h ω)) χ - c ω * ∫ x, χ x := by
    change addConst (h ω) (-(c ω)) t = h ω t - c ω * ∫ x, χ x
    rw [GFFInv.addConst_apply]
    have ht : ∀ x, t x = χ x := by intro x; simp [t, TestFunction.monoCLM_apply]
    simp_rw [ht]
    ring
  have hstep : (distPullback hφ (restrictTo V (h ω)) - z ω) ψ =
      (distPullback hφ (restrictTo V (h₀ ω)) - z ω) ψ + c ω * ∫ x, ψ x := by
    rw [sub_apply, sub_apply, distPullback_apply, distPullback_apply]
    change (restrictTo V (h ω)) χ - z ω ψ =
      ((restrictTo V (h₀ ω)) χ - z ω ψ) + c ω * ∫ x, ψ x
    have hone := integral_mul_confPushTest hφ ψ (fun _ => (1 : ℝ))
    have hone' : (∫ x, χ x) = ∫ x, ψ x := by
      simpa only [χ, one_mul] using hone
    rw [← hone', hconst_eval]
    ring
  rw [hstep, hrep ψ]
  have hI : Integrable (fun x => H₀ ω x * ψ x) := by
    have hc : ContinuousOn (fun x => H₀ ω x * ψ x) (tsupport ψ) :=
      (hHarm.continuousOn.mono ψ.tsupport_subset).mul ψ.continuous.continuousOn
    have hi : IntegrableOn (fun x => H₀ ω x * ψ x) (tsupport ψ) (volume : Measure ℂ) :=
      hc.integrableOn_compact ψ.hasCompactSupport.isCompact
    apply hi.integrable_of_forall_notMem_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hcI : Integrable (fun x => c ω * ψ x) :=
    (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).const_mul (c ω)
  calc
    (∫ x, H₀ ω x * ψ x) + c ω * ∫ x, ψ x =
        (∫ x, H₀ ω x * ψ x) + ∫ x, c ω * ψ x := by rw [integral_const_mul]
    _ = ∫ x, (H₀ ω x * ψ x + c ω * ψ x) := (integral_add hI hcI).symm
    _ = ∫ x, H ω x * ψ x := by congr 1; funext x; dsimp [H]; ring

end SupercriticalConformalCovariance.ZBConformal
