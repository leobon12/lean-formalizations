/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.Locality11
import InteractingSLE.Spec.Coupling.ResampleProjCore
import InteractingSLE.WangWu.BridgeTrace
import InteractingSLE.WangWu.SideValues
import InteractingSLE.WangWu.Bridge
import InteractingSLE.Spec.Coupling.WholeField2Germ

/-!
# Wang–Wu Corollary 3.9: the hull of a full level-line coupling is a local set

Packet PROVE-WW-B8. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), Corollary 3.9
(p. 15, text dump L916–927): "For every stopping time in Theorem 3.8, both `A_τ` and the filled hull `K_τ` are local
sets for `X` … The construction supplies a full stopping-time local-set coupling", and Definition 1.5 (the full
level-line coupling, `IsFullLevelLineCoupling`).

## A vacuity finding

`IsLocalSet A h P` (frozen, specification p. 49) requires `A ω ⊆ ℍ` almost surely. A random set containing a real
point almost surely is therefore never local (`not_isLocalSet_of_ae_mem`). In particular the range `arcRange γ` and the
prefixes `arcPrefix γ t` of a proper arc (which contain `γ 0 = 0`) are never local
(`not_isLocalSet_arcRange`, `not_isLocalSet_arcPrefix`): every landed statement taking
`IsLocalSet (fun ω => arcRange (γ ω)) h P` or `IsLocalSet (fun ω => arcPrefix (γ ω) t) h P` as a hypothesis (PROVE-WW-B5's
`ae_hasLeftSideLimit_of_prefix`, PROVE-WW-B7's `ae_hasSideLimits_of_prefix_meanAt`, `ae_eq_on_leftSideOf_union`, …) is
vacuous. The local sets are `arcRange γ ∩ ℍ` and `arcPrefix γ t ∩ ℍ` (for a Loewner trace, the latter is the hull
`K_t`); the germ σ-algebra, the local-set mean and the sides do not see the real point.

## The avoidance criterion from a Gaussian kernel on avoidance events

`isAvoidanceLocal_of_setIntegral_avoid`: if the avoidance events `{A ∩ V = ∅}` are, up to null sets, events of a
σ-algebra `𝒢`, and on every `𝒢`-event inside `{A ∩ V = ∅}` the Dirichlet direction `−Δf/2π` (`f ∈ C_c^∞(V)`) enters the
characteristic functional with the Gaussian factor of the projection onto `H(V)`,

  `∫_D e^{i h(−Δf/2π + Ξ)} = exp(−‖∇f‖²/2 − ⟪∇f, covVec_V Ξ⟫) ∫_D e^{i h(Ξ)}`,

then `A` satisfies Lemma 3.6 (i). This is PROVE-T11-LOC's family argument (`Coupling.isLocalSet_hull_of_isFamilyLocal`,
Astra (1.14)) with a single piece: the stop is `τ` itself, and the identity is only needed on the avoidance event.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace QuantumZipper
open scoped NNReal ENNReal RealInnerProductSpace

namespace InteractingSLE.WangWu

open LQGMetric LQGMetric.MarkovZB LQGMetric.MarkovHarm LocalSets QuantumZipper.K3 QuantumZipper.Thm11Asm

/-! ### Random sets meeting the real line are not local -/

section Vacuity

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **A random set containing a real point almost surely is not a local set** (`IsLocalSet` asks `A ⊆ ℍ`). -/
theorem not_isLocalSet_of_ae_mem {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens} {x : ℝ}
    (hx : ∀ᵐ ω ∂P, (x : ℂ) ∈ A ω) : ¬ IsLocalSet A h P := by
  intro hloc
  have hF : ∀ᵐ ω ∂P, False := by
    filter_upwards [hloc.2.1, hx] with ω h1 h2
    have := h1.1 h2
    simp [H] at this
  obtain ⟨_, hfalse⟩ := hF.exists
  exact hfalse

/-- The range of a proper arc contains `0`, so it is never a local set. -/
theorem not_isLocalSet_arcRange {γ : Ω → ℝ → ℂ} (harc : ∀ᵐ ω ∂P, IsProperArc (γ ω))
    {h : Ω → DistOn upperHalfPlaneOpens} : ¬ IsLocalSet (fun ω => arcRange (γ ω)) h P := by
  refine not_isLocalSet_of_ae_mem (x := 0) ?_
  filter_upwards [harc] with ω hω
  exact ⟨0, mem_Ici.2 le_rfl, by rw [hω.zero]; simp⟩

/-- The prefixes of a proper arc contain `0`, so they are never local sets. -/
theorem not_isLocalSet_arcPrefix {γ : Ω → ℝ → ℂ} (harc : ∀ᵐ ω ∂P, IsProperArc (γ ω)) {t : ℝ}
    (ht : 0 ≤ t) {h : Ω → DistOn upperHalfPlaneOpens} :
    ¬ IsLocalSet (fun ω => arcPrefix (γ ω) t) h P := by
  refine not_isLocalSet_of_ae_mem (x := 0) ?_
  filter_upwards [harc] with ω hω
  exact ⟨0, ⟨le_rfl, ht⟩, by rw [hω.zero]; simp⟩

end Vacuity

/-! ### The Gaussian factor of a Dirichlet direction -/

section Gauss

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- For a zero-boundary GFF on `ℍ`, `E[e^{i h(−Δf/2π)}] = exp(−‖∇f‖²/2)` (`f ∈ C_c^∞(V)`, `V ⊆ ℍ`). -/
theorem integral_cexp_lapTest {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {V : Opens ℂ} (hVH : (V : Set ℂ) ⊆ H)
    (f : zsSub (V : Set ℂ)) :
    ∫ ω, Complex.exp (Complex.I * (h ω (lapTest V f) : ℂ)) ∂P =
      ((Real.exp (-(1 / 2) * ‖gradFeat (V : Set ℂ) f.1‖ ^ 2) : ℝ) : ℂ) := by
  have hV : V ≤ upperHalfPlaneOpens := hVH
  set Φ : TestOn upperHalfPlaneOpens := lapTest V f with hΦ
  have hm : AEMeasurable (fun ω => h ω Φ) P := (hh.process.measurable Φ).aemeasurable
  rw [GFF.integral_exp_I_mul_of_hasGaussianLaw (hh.process.gaussian.hasGaussianLaw_eval Φ)
    (hh.process.centered Φ), ← covariance_self hm, hh.process.covariance_eq Φ Φ]
  have hH : IsOpen (H : Set ℂ) := upperHalfPlaneOpens.isOpen
  have e1 : zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) Φ Φ = ‖covVec H Φ‖ ^ 2 := by
    rw [show ((upperHalfPlaneOpens : Opens ℂ) : Set ℂ) = H from rfl,
      zeroGFFTestCov_eq_inner_covVec hH subset_rfl, real_inner_self_eq_norm_sq]
  rw [e1, hΦ, covVec_lapTest hV hH subset_rfl hVH f, norm_gradFeat_eq hVH f.2]

end Gauss

/-! ### The avoidance criterion from a kernel on avoidance events -/

section Avoid

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Lemma 3.6 (i) from a Gaussian kernel on avoidance events.** Let `h` be a zero-boundary GFF on `ℍ` and `A` a
hitting-measurable random set whose avoidance events `{A ∩ V = ∅}` are, up to null sets, events of a σ-algebra
`𝒢 ≤ mΩ`. Suppose that on every `𝒢`-event `D` contained (almost surely) in `{A ∩ V = ∅}`, every Dirichlet direction
`−Δf/2π`, `f ∈ C_c^∞(V)`, enters the characteristic functional with the Gaussian factor of the projection onto
`H(V)`: `∫_D e^{i h(−Δf/2π + Ξ)} = exp(−‖∇f‖²/2 − ⟪∇f, covVec_V Ξ⟫) ∫_D e^{i h(Ξ)}`. Then `A` satisfies the
avoidance criterion (Lemma 3.6 (i)). -/
theorem isAvoidanceLocal_of_setIntegral_avoid (h𝒢 : 𝒢 ≤ mΩ)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAev : ∀ V : Set ℂ, IsOpen V → V ⊆ H → ∃ E' : Set Ω, MeasurableSet[𝒢] E' ∧
      {ω | Disjoint (A ω) V} =ᵐ[P] E')
    (hid : ∀ V : Opens ℂ, (V : Set ℂ) ⊆ H → ∀ (f : zsSub (V : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens)
      (D : Set Ω), MeasurableSet[𝒢] D → (∀ᵐ ω ∂P, ω ∈ D → Disjoint (A ω) V) →
        ∫ ω in D, Complex.exp (Complex.I * (h ω (lapTest V f + Ξ) : ℂ)) ∂P =
          Complex.exp (((-(1 / 2) * ‖gradFeat (V : Set ℂ) f.1‖ ^ 2 -
            ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) Ξ⟫ : ℝ) : ℂ)) *
            ∫ ω in D, Complex.exp (Complex.I * (h ω Ξ : ℂ)) ∂P) :
    IsAvoidanceLocal A h P := by
  have hhm := hh.measurable
  have hnorm1 : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ ≤ 1 := fun x =>
    (Complex.norm_exp_I_mul_ofReal x).le
  refine Coupling.isAvoidanceLocal_of_setIntegral_lapTest hh hA fun V hVH => ?_
  have hV : V ≤ upperHalfPlaneOpens := hVH
  obtain ⟨GV, hGV, hGVd⟩ := exists_markovMap V hVH
  have hdV := hGVd hh
  refine ⟨GV, hGV, hdV, fun f Ψ => ?_⟩
  obtain ⟨E', hE'm, hEE'⟩ := hAev V V.isOpen hVH
  have hD : MeasurableSet E' := h𝒢 _ hE'm
  have hE'sub : ∀ᵐ ω ∂P, ω ∈ E' → Disjoint (A ω) V := by
    filter_upwards [hEE'] with ω hω hωE
    exact (eq_iff_iff.1 hω).2 hωE
  rw [setIntegral_congr_set hEE', setIntegral_congr_set hEE']
  set Φ : TestOn upperHalfPlaneOpens := lapTest V f with hΦ
  set c : ℂ := ∫ ω, Complex.exp (Complex.I * (h ω Φ : ℂ)) ∂P with hc_def
  have hQVm : Measurable fun ω => markovCompl GV (h ω) := (measurable_markovCompl hGV).comp hhm
  set b : Ω → ℝ := fun ω => markovCompl GV (h ω) Ψ with hb_def
  have hbm : Measurable b := (measurable_distOn_apply Ψ).comp hQVm
  have hhΦm : Measurable fun ω => h ω Φ := (measurable_distOn_apply Φ).comp hhm
  -- the Dirichlet approximation of the complementary projection
  obtain ⟨g, hg, hgL2⟩ := exists_tendsto_integral_sq_of_isMarkovDecomposition hV hdV Ψ
  set Ξ : ℕ → TestOn upperHalfPlaneOpens := fun n => Ψ - lapTest V (g n) with hΞ
  set a : ℕ → Ω → ℝ := fun n ω => h ω (Ξ n) with ha_def
  have ham : ∀ n, Measurable (a n) := fun n => (measurable_distOn_apply _).comp hhm
  have hab : ∀ n ω, a n ω - b ω = GV (h ω) Ψ - h ω (lapTest V (g n)) := fun n ω => by
    simp only [a, b, hΞ, map_sub, markovCompl, sub_apply]
    ring
  have hmem : ∀ n, MemLp (fun ω => a n ω - b ω) 2 P := fun n => by
    have h1 := memLp_markov_sub_lapTest hV hdV Ψ (g n)
    convert h1 using 1
    funext ω
    exact hab n ω
  have hlim : Tendsto (fun n => ∫ ω, (a n ω - b ω) ^ 2 ∂P) atTop (𝓝 0) := by
    refine hgL2.congr fun n => integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hab n ω]
  set r : ℕ → ℝ := fun n => -(1 / 2) * ‖gradFeat (V : Set ℂ) f.1‖ ^ 2 -
    ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) (Ξ n)⟫ with hr_def
  -- the identity along the approximations
  have hmemb : ∀ n, ∫ ω in E', Complex.exp (Complex.I * (h ω Φ : ℂ)) *
      Complex.exp (Complex.I * (a n ω : ℂ)) ∂P =
        Complex.exp ((r n : ℝ) : ℂ) * ∫ ω in E', Complex.exp (Complex.I * (a n ω : ℂ)) ∂P := by
    intro n
    have key := hid V hVH f (Ξ n) E' hE'm hE'sub
    rw [← hΦ] at key
    rw [← key]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [a, map_add, Complex.ofReal_add, mul_add, Complex.exp_add]
  -- the exponents converge
  have hinner : ∀ n, ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) (Ξ n)⟫ =
      ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) Ψ⟫ - ⟪gradFeat (V : Set ℂ) f.1,
        gradFeat (V : Set ℂ) (g n).1⟫ := fun n => by
    rw [hΞ, covVec_sub V.isOpen hVH, inner_sub_right, covVec_lapTest hV V.isOpen hVH subset_rfl (g n)]
  have hr : Tendsto r atTop (𝓝 (-(1 / 2) * ‖gradFeat (V : Set ℂ) f.1‖ ^ 2)) := by
    have h1 : Tendsto (fun n => ⟪gradFeat (V : Set ℂ) f.1, gradFeat (V : Set ℂ) (g n).1⟫) atTop
        (𝓝 ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) Ψ⟫) :=
      tendsto_const_nhds.inner hg
    have h2 : Tendsto (fun n => ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) (Ξ n)⟫) atTop (𝓝 0) := by
      simp_rw [hinner]
      simpa using (tendsto_const_nhds (x := ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) Ψ⟫)).sub h1
    have h3 := (tendsto_const_nhds (x := -(1 / 2) * ‖gradFeat (V : Set ℂ) f.1‖ ^ 2)).sub h2
    rw [sub_zero] at h3
    exact h3
  -- the constant `c`
  have hc : c = Complex.exp (((-(1 / 2) * ‖gradFeat (V : Set ℂ) f.1‖ ^ 2 : ℝ) : ℂ)) := by
    rw [hc_def, integral_cexp_lapTest hh hVH f, Complex.ofReal_exp]
  -- the limits
  have hZ1 : ∀ ω, ‖E'.indicator (fun ω => Complex.exp (Complex.I * (h ω Φ : ℂ))) ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ E'
    · rw [indicator_of_mem hω]; exact hnorm1 _
    · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
  have hZ2 : ∀ ω, ‖E'.indicator (fun _ => (1 : ℂ)) ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ E'
    · rw [indicator_of_mem hω, norm_one]
    · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
  have hZ1m : Measurable (E'.indicator fun ω => Complex.exp (Complex.I * (h ω Φ : ℂ))) :=
    (GFF.measurable_exp_I_mul hhΦm).indicator hD
  have hZ2m : Measurable (E'.indicator fun _ => (1 : ℂ)) := measurable_const.indicator hD
  have e1 : ∀ x : Ω → ℝ, ∫ ω in E', Complex.exp (Complex.I * (h ω Φ : ℂ)) *
      Complex.exp (Complex.I * (x ω : ℂ)) ∂P = ∫ ω, Complex.exp (Complex.I * (x ω : ℂ)) *
        E'.indicator (fun ω => Complex.exp (Complex.I * (h ω Φ : ℂ))) ω ∂P := fun x => by
    rw [← Coupling.setIntegral_eq_integral_indicator_mul hD]
    exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
  have e2 : ∀ x : Ω → ℝ, ∫ ω in E', Complex.exp (Complex.I * (x ω : ℂ)) ∂P =
      ∫ ω, Complex.exp (Complex.I * (x ω : ℂ)) * E'.indicator (fun _ => (1 : ℂ)) ω ∂P := fun x => by
    rw [← Coupling.setIntegral_eq_integral_indicator_mul hD]
    exact integral_congr_ae (Eventually.of_forall fun ω => (mul_one _).symm)
  have hL1 := Coupling.tendsto_integral_cexp_mul_of_tendsto_integral_sq hmem hlim hZ1
    (fun n => ((GFF.measurable_exp_I_mul (ham n)).mul hZ1m).aestronglyMeasurable)
    ((GFF.measurable_exp_I_mul hbm).mul hZ1m).aestronglyMeasurable
  have hL2 := Coupling.tendsto_integral_cexp_mul_of_tendsto_integral_sq hmem hlim hZ2
    (fun n => ((GFF.measurable_exp_I_mul (ham n)).mul hZ2m).aestronglyMeasurable)
    ((GFF.measurable_exp_I_mul hbm).mul hZ2m).aestronglyMeasurable
  simp_rw [← e1] at hL1
  simp_rw [← e2] at hL2
  have hR := ((Complex.continuous_exp.comp Complex.continuous_ofReal).tendsto _).comp hr
  have hRL := hR.mul hL2
  simp_rw [Function.comp_apply, ← hmemb] at hRL
  rw [hc]
  exact tendsto_nhds_unique hL1 hRL

end Avoid

/-! ### Deterministic facts on an avoidance event -/

section Deterministic

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **`η_t` is harmonic off the hull at every time before the lifetime** (the driver need only be continuous before
`ζ`; PROVE-WW-B7's `harmonicOnNhd_meanAt` asks for a globally continuous driver). The driver is replaced by its clamp
at a time `t₂ ∈ (t, ζ)`, which has the same hull and the same map at time `t`. -/
theorem harmonicOnNhd_meanAt_of_lt (hp : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) :
    InnerProductSpace.HarmonicOnNhd (meanAt ρL ρR w vL vR t) (H \ fwdHull (Ito.rpath w) t) := by
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htt₂' : (t : ℝ) < t₂ := by exact_mod_cast htt₂
  set W₂ : ℝ → ℝ := Ito.clampDrv (Ito.rpath w) t₂ with hW₂
  have hc : Continuous W₂ := Ito.continuous_clampDrv t₂.coe_nonneg (Ito.continuousOn_rpath hp.2.2.2.1 ht₂ζ)
  have heq : ∀ r ∈ Icc (0 : ℝ) t₂, Ito.rpath w r = W₂ r := fun r hr => (Ito.clampDrv_eqOn hr).symm
  have hK : fwdHull (Ito.rpath w) t = fwdHull W₂ t := fwdHull_eq_of_eqOn t.coe_nonneg htt₂' heq
  have hmap : ∀ z, fwdMap (Ito.rpath w) t z = fwdMap W₂ t z := fun z =>
    Ito.fwdMap_congr_of_eqOn_of_le (fun r hr => heq r hr) htt₂'.le
  obtain ⟨-, -, -, -, -, -, -, hvLw, hwvR, -⟩ := id hp
  have hcm := (isBoundedHarmonicExtension_condMean ρL ρR (vL := fun i => vL i t - w t)
    (vR := fun i => vR i t - w t) (fun i => sub_nonpos.2 (hvLw t ht i))
    (fun i => sub_nonneg.2 (hwvR t ht i))).1
  have e : meanAt ρL ρR w vL vR t = (condMean ρL ρR (fun i => vL i t - w t) (fun i => vR i t - w t)) ∘
      fwdMap W₂ t := funext fun z => by rw [meanAt, Function.comp_apply, hmap]
  rw [hK, e]
  have hO := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hc t.coe_nonneg
  have hd := QuantumZipper.FwdHolo.differentiableOn_fwdMap hc t.coe_nonneg
  intro z hz
  exact QuantumZipper.FieldLawler.fl_harmonicAt_comp (hd.analyticAt (hO.mem_nhds hz))
    (hcm _ (QuantumZipper.FwdHolo.mapsTo_fwdMap hc t.coe_nonneg hz))

/-- The complement of the hull in `ℍ` is open at every time before the lifetime. -/
theorem isOpen_H_diff_fwdHull_of_lt (hp : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) : IsOpen (H \ fwdHull (Ito.rpath w) t) := by
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htt₂' : (t : ℝ) < t₂ := by exact_mod_cast htt₂
  have hc : Continuous (Ito.clampDrv (Ito.rpath w) t₂) :=
    Ito.continuous_clampDrv t₂.coe_nonneg (Ito.continuousOn_rpath hp.2.2.2.1 ht₂ζ)
  rw [fwdHull_eq_of_eqOn t.coe_nonneg htt₂' fun r hr => (Ito.clampDrv_eqOn hr).symm]
  exact QuantumZipper.FwdHolo.isOpen_compl_fwdHull hc t.coe_nonneg

/-- `∫ g (φ + ψ) = ∫ g ψ` when `g φ` is integrable with integral zero (also when `g ψ` is not integrable). -/
theorem integral_mul_add_of_integral_eq_zero {g φ ψ : ℂ → ℝ} (hi : Integrable fun z => g z * φ z)
    (h0 : ∫ z, g z * φ z = 0) : ∫ z, g z * (φ z + ψ z) = ∫ z, g z * ψ z := by
  by_cases hψ : Integrable fun z => g z * ψ z
  · simp_rw [mul_add]
    rw [integral_add hi hψ, h0, zero_add]
  · have hn : ¬ Integrable fun z => g z * (φ z + ψ z) := fun hs =>
      hψ ((hs.sub hi).congr (Eventually.of_forall fun z => by simp only [Pi.sub_apply]; ring))
    rw [integral_undef hn, integral_undef hψ]

/-- **A Dirichlet direction is invisible to a function harmonic near its support**: if `g = v` on an open `O ⊇ V`
with `v` harmonic on `O`, then `∫ g (−Δf/2π + Ξ) = ∫ g Ξ` for `f ∈ C_c^∞(V)` and every test function `Ξ`. -/
theorem integral_mul_lapTest_add {g v : ℂ → ℝ} {O : Set ℂ} (hO : IsOpen O)
    (hv : InnerProductSpace.HarmonicOnNhd v O) (hgv : EqOn g v O) {V : Opens ℂ} (hVH : (V : Set ℂ) ⊆ H)
    (hVO : (V : Set ℂ) ⊆ O) (f : zsSub (V : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ z, g z * (lapTest V f + Ξ) z = ∫ z, g z * Ξ z := by
  have hV : V ≤ upperHalfPlaneOpens := hVH
  have hsupp : tsupport (lapTest V f) ⊆ O := (tsupport_lapTest_subset hV f).trans (f.2.2.2.trans hVO)
  have e1 : (fun z => g z * lapTest V f z) = fun z => v z * lapTest V f z := funext fun z => by
    by_cases hz : z ∈ O
    · rw [hgv hz]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hsupp h)), mul_zero, mul_zero]
  have hint : Integrable fun z => g z * lapTest V f z := by
    rw [e1]
    refine Continuous.integrable_of_hasCompactSupport ?_ (lapTest V f).hasCompactSupport.mul_left
    refine continuous_of_tsupport fun x hx => ?_
    have hxO : x ∈ O := hsupp (tsupport_mul_subset_right hx)
    exact (hv x hxO).1.continuousAt.mul (lapTest V f).continuous.continuousAt
  have h0 : ∫ z, g z * lapTest V f z = 0 := by
    rw [e1, coe_lapTest hV]
    exact HarmLoc.integral_mul_cmTest_of_harmonic hO hv (zsTest f.2) (f.2.2.2.trans hVO)
  have e2 : (fun z => g z * (lapTest V f + Ξ) z) = fun z => g z * (lapTest V f z + Ξ z) := by
    funext z; rw [FunLike.coe_add, Pi.add_apply]
  rw [e2]
  exact integral_mul_add_of_integral_eq_zero hint h0

/-- **The retained energy of `−Δf/2π + Ξ`** for `f ∈ C_c^∞(V)`, `V` off the hull, at a time `t < ζ` of a path with a
generating trace whose prefix has zero area: `Q_{U_t}(−Δf/2π + Ξ) = ‖∇f‖² + 2⟪∇f, covVec_V Ξ⟫ + Q_{U_t}(Ξ)`. -/
theorem retainedGreenEnergy_lapTest_add (hp : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ)
    (harea : volume (η '' Icc 0 t ∩ H) = 0) {V : Opens ℂ}
    (hVK : (V : Set ℂ) ⊆ H \ fwdHull (Ito.rpath w) t) (f : zsSub (V : Set ℂ))
    (Ξ : TestOn upperHalfPlaneOpens) :
    retainedGreenEnergy w t ⇑(lapTest V f + Ξ) = ‖gradFeat (V : Set ℂ) f.1‖ ^ 2 +
      2 * ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) Ξ⟫ + retainedGreenEnergy w t Ξ := by
  set U : Set ℂ := H \ η '' Icc 0 t with hUdef
  have hcpt : IsCompact (η '' Icc 0 t) :=
    isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun s hs => le_trans (ENNReal.coe_le_coe.2 hs.2) ht.le)
  have hU : IsOpen U := upperHalfPlaneOpens.isOpen.sdiff hcpt.isClosed
  have hUH : U ⊆ H := sdiff_subset
  have hKU : H \ fwdHull (Ito.rpath w) t ⊆ U := by
    obtain ⟨z, -, hz⟩ := (hη.2.2 t ht).1
    have : H \ fwdHull (fun s : ℝ => w s.toNNReal) t ⊆ H \ η '' Icc 0 t := by
      rw [← hz]; exact connectedComponentIn_subset _ _
    exact this
  have hVU : (V : Set ℂ) ⊆ U := hVK.trans hKU
  rw [← zeroGFFTestCov_compl_image_eq_retainedGreenEnergy hη hp.2.2.2.1 hp.1 ht harea,
    ← zeroGFFTestCov_compl_image_eq_retainedGreenEnergy hη hp.2.2.2.1 hp.1 ht harea,
    zeroGFFTestCov_eq_inner_covVec hU hUH, zeroGFFTestCov_eq_inner_covVec hU hUH,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  exact Coupling.norm_covVec_lapTest_add_sq hU hUH hVU f Ξ

end Deterministic

/-! ### The full level-line coupling: the hull is local -/

section Coupling

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {F : Ω → DistOn upperHalfPlaneOpens}

/-- The exponent algebra of the kernel identity. -/
theorem cexp_kernel_split (c a n p q : ℝ) :
    Complex.exp (-(Complex.I * (c : ℂ))) * Complex.exp (Complex.I * (a : ℂ) -
        (((1 / 2 : ℝ) * (n + 2 * p + q) : ℝ) : ℂ)) =
      Complex.exp (((-(1 / 2) * n - p : ℝ) : ℂ)) * (Complex.exp (-(Complex.I * (c : ℂ))) *
        Complex.exp (Complex.I * (a : ℂ) - (((1 / 2 : ℝ) * q : ℝ) : ℂ))) := by
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Zero area of the trace prefix before the lifetime (Aux. lemma 15 at `κ = 4`). -/
theorem volume_image_inter_H_eq_zero {T : ℝ≥0∞} {η : ℝ≥0 → ℂ} {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T)
    (hdim : ∀ S ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ T},
      dimH (η '' S ∩ H) ≤ ENNReal.ofReal (Dimension.interiorDimBound 4)) :
    volume (η '' Icc 0 t ∩ H) = 0 := by
  refine volume_eq_zero_of_dimH_lt_two (lt_of_le_of_lt (hdim (Icc 0 t) fun s hs =>
    le_trans (ENNReal.coe_le_coe.2 hs.2) ht.le) ?_)
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (Dimension.interiorDimBound_lt_two (by norm_num))

/-- **The kernel identity on an avoidance event** (full level-line coupling, Definition 1.5). For a stopping time
`τ < ζ` of the driving filtration, a `𝓕_τ`-event `D` on which `K_τ` avoids the open `V ⊆ ℍ`, `f ∈ C_c^∞(V)` and a
test function `Ξ`, the centred field `h⁰ = F − u₀` (`u₀` harmonic on `ℍ`) satisfies
`∫_D e^{i h⁰(−Δf/2π + Ξ)} = exp(−‖∇f‖²/2 − ⟪∇f, covVec_V Ξ⟫) ∫_D e^{i h⁰(Ξ)}`, provided the driver almost surely has
a continuous generating trace through `ζ` (for the zero area of its prefixes). -/
theorem IsFullLevelLineCoupling.setIntegral_cexp_lapTest_add [IsProbabilityMeasure P]
    (hF : IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    {V : Opens ℂ} (hVH : (V : Set ℂ) ⊆ H) (f : zsSub (V : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens)
    {D : Set Ω} (hD : MeasurableSet[hτ.measurableSpace] D)
    (hDV : ∀ᵐ ω ∂P, ω ∈ D →
      Disjoint (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) (V : Set ℂ)) :
    ∫ ω in D, Complex.exp (Complex.I * (WholeField.centredField F u₀ ω (lapTest V f + Ξ) : ℂ)) ∂P =
      Complex.exp (((-(1 / 2) * ‖gradFeat (V : Set ℂ) f.1‖ ^ 2 -
        ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) Ξ⟫ : ℝ) : ℂ)) *
        ∫ ω in D, Complex.exp (Complex.I * (WholeField.centredField F u₀ ω Ξ : ℂ)) ∂P := by
  obtain ⟨hE, hFm, _hX', hK⟩ := hF
  have h𝒢 : hτ.measurableSpace ≤ mΩ := hτ.measurableSpace_le
  have hDm : MeasurableSet D := h𝒢 _ hD
  set h0 := WholeField.centredField F u₀ with hh0
  have hh0m : Measurable h0 := WholeField.measurable_centredField hFm u₀
  set c : TestOn upperHalfPlaneOpens → ℂ := fun φ =>
    Complex.exp (-(Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ))) with hc
  have hcen : ∀ φ : TestOn upperHalfPlaneOpens,
      (fun ω => Complex.exp (Complex.I * (h0 ω φ : ℂ))) =
        c φ • fun ω => Complex.exp (Complex.I * (F ω φ : ℂ)) := fun φ => by
    funext ω
    rw [Pi.smul_apply, smul_eq_mul, hh0, WholeField.centredField_apply F hu₀, hc, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Complex.exp (Complex.I * (h0 ω φ : ℂ))) P := fun φ =>
    Integrable.of_bound (GFF.measurable_exp_I_mul ((measurable_distOn_apply φ).comp hh0m)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
  have hcond : ∀ φ : TestOn upperHalfPlaneOpens,
      P[fun ω => Complex.exp (Complex.I * (h0 ω φ : ℂ)) | hτ.measurableSpace] =ᵐ[P]
        c φ • P[fun ω => Complex.exp (Complex.I * (F ω φ : ℂ)) | hτ.measurableSpace] := fun φ => by
    rw [hcen φ]
    exact condExp_smul (c φ) _ _
  rw [← setIntegral_condExp h𝒢 (hint _) hD, ← setIntegral_condExp h𝒢 (hint _) hD,
    ← integral_const_mul]
  refine setIntegral_congr_ae hDm ?_
  filter_upwards [hcond (lapTest V f + Ξ), hcond Ξ, hK τ hτ hτζ (lapTest V f + Ξ), hK τ hτ hτζ Ξ, hDV, htr,
    hτζ, hE.2.2.2.2, hE.ae_dimH_image_inter_H_le (by norm_num) (by norm_num)]
    with ω e1 e2 k1 k2 hDω htrω hlt hp hdim hωD
  rw [e1, e2, Pi.smul_apply, Pi.smul_apply, k1, k2, smul_eq_mul, smul_eq_mul]
  set t : ℝ≥0 := (τ ω).untopD 0 with htdef
  have htζ : (t : ℝ≥0∞) < ζ ω := by
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    have hτt : τ ω = (t : WithTop ℝ≥0) := by rw [htdef, ← hs, WithTop.untopD_coe]
    have : ((t : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := hτt ▸ hlt
    exact this
  obtain ⟨η, hη⟩ := htrω
  have harea := volume_image_inter_H_eq_zero htζ (hdim η hη)
  have hVK : (V : Set ℂ) ⊆ H \ fwdHull (Ito.rpath fun s => W s ω) t := fun z hz =>
    ⟨hVH hz, fun hzK => Set.disjoint_left.1 (hDω hωD) hzK hz⟩
  have hm1 := integral_mul_lapTest_add (g := frozenMean ρL ρR (W · ω) (fun i => (VL i · ω))
    (fun i => (VR i · ω)) t) (isOpen_H_diff_fwdHull_of_lt hp htζ)
    (harmonicOnNhd_meanAt_of_lt hp htζ) (fun z hz => frozenMean_eq_meanAt hz) hVH hVK f Ξ
  have hu1 := integral_mul_lapTest_add (g := u₀) upperHalfPlaneOpens.isOpen hu₀ (fun _ _ => rfl) hVH hVH f Ξ
  have hq := retainedGreenEnergy_lapTest_add hp hη htζ harea hVK f Ξ
  simp only [hc]
  rw [hm1, hu1, hq]
  exact cexp_kernel_split _ _ _ _ _

/-- **Wang–Wu Corollary 3.9 for the filled hull, centred field.** For a full level-line coupling whose driver almost
surely has a continuous generating trace through `ζ`, with `u₀` harmonic on `ℍ` and `h⁰ = F − u₀` a zero-boundary GFF,
the hull `K_τ` at every stopping time `τ < ζ` of the driving filtration is a local set of `h⁰`. -/
theorem IsFullLevelLineCoupling.isLocalSet_hull_centredField [IsProbabilityMeasure P]
    (hF : IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField F u₀) P)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
      (WholeField.centredField F u₀) P := by
  have hE := hF.1
  have hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 := by
    filter_upwards [hE.2.2.2.2] with ω hp using ⟨hp.2.2.2.1, hp.1⟩
  obtain ⟨A, hAm, hAK, hAev⟩ := Coupling.exists_hittingVersion_hull hX hpath hτ hτζ
  have hτζ' : ∀ᵐ ω ∂P, (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω :=
    hτζ.mono fun ω h => Coupling.coe_untopD_lt_zeta h
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    filter_upwards [Coupling.ae_hull_subset_isOpen (hpath.mono fun ω h => h.1) hτζ', hAK] with ω h1 h2
    rw [h2]
    exact h1
  have hav : IsAvoidanceLocal A (WholeField.centredField F u₀) P := by
    refine isAvoidanceLocal_of_setIntegral_avoid hτ.measurableSpace_le hh0 hAm hAev
      fun V hVH f Ξ D hD hDA => ?_
    refine hF.setIntegral_cexp_lapTest_add htr hu₀ hX hτ hτζ hVH f Ξ hD ?_
    filter_upwards [hDA, hAK] with ω h1 h2 hωD
    rw [← h2]
    exact h1 hωD
  have hloc := ((isLocalSet_tfae hh0 hAm hAc).out 1 4).1 hav
  exact Coupling.IsLocalSet.congr_set hloc hAK.symm

/-- **Wang–Wu Corollary 3.9 for the filled hull**: under the hypotheses of `isLocalSet_hull_centredField`, `K_τ` is a
local set of the field `F` itself. -/
theorem IsFullLevelLineCoupling.isLocalSet_hull [IsProbabilityMeasure P]
    (hF : IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField F u₀) P)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) F P := by
  have h := Coupling.IsLocalSet.add_dist (hF.isLocalSet_hull_centredField htr hu₀ hh0 hX hτ hτζ)
    (WholeField.isHarmonicDistOn_smoothDist hu₀)
  have e : (fun ω => WholeField.centredField F u₀ ω +
      SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) = F := by
    funext ω
    simp only [WholeField.centredField, sub_add_cancel]
  rwa [e] at h

end Coupling

end InteractingSLE.WangWu
