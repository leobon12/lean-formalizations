import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLFPPAS.Signed.ConvField
import HigherDimLQGMetric.ConvField.RadialAll
import HigherDimLQGMetric.ConvField.RadialLimit
import HigherDimLQGMetric.ConvField.RadialMain
import HigherDimLQGMetric.ConvField.JointMain
import HigherDimLQGMetric.ConvField.Shifts
import HigherDimLQGMetric.ConvField.WholeSpaceLimit
import HigherDimLQGMetric.ConvField.WholeSpaceRadial
import HigherDimLQGMetric.ConvField.Spec
import HigherDimLQGMetric.ConvField.Scaling
import HigherDimLQGMetric.Assembly.ConvMollifySpec

/-!
# Sign-free copies: the radial formula, joint continuity, existence of `h ∗ K_ε`, scaling

Packet G1 (ruling L7; planning audit `planning/audits/MA3-inputs.md` §4.1 and §4.3 items 1–2). The declarations of
`HigherDimLQGMetric.ConvField.RadialAll`, `HigherDimLQGMetric.ConvField.RadialLimit`,
`HigherDimLQGMetric.ConvField.RadialMain`, `HigherDimLQGMetric.ConvField.JointMain`,
`HigherDimLQGMetric.ConvField.Shifts`, `HigherDimLQGMetric.ConvField.WholeSpaceLimit`,
`HigherDimLQGMetric.ConvField.WholeSpaceRadial`, `HigherDimLQGMetric.ConvField.Spec`,
`HigherDimLQGMetric.ConvField.Scaling`, `HigherDimLQGMetric.Assembly.ConvMollifySpec`
whose statements mention the kernel predicate, copied with hypothesis `HigherDimLFPPAS.IsAdmissibleSeed κ` (the
paper's seeds: no sign condition) in place of `HigherDimLFPP.IsLFPPKernel κ`. Each copy `<name>_seed` has the
statement of `HigherDimLQGMetric.<name>` except for the kernel hypothesis (kernel-dependent definitions it mentions
are replaced by their copies); its proof is the host proof, with calls to copied declarations redirected to the
copies and everything else reused directly. Host-private helpers called by the copied proofs are copied as private
`<name>_seed`.
No proof uses nonnegativity of the seed: `IsAdmissibleSeed` has no such field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLFPPAS.Signed

open HigherDimLQGMetric

section RadialAll
/-! Copies from `HigherDimLQGMetric.ConvField.RadialAll`. -/

open MeasureTheory Set Metric Filter Topology
open HigherDimLFPP (Rd e₁)
variable {d : ℕ} {κ : Rd d → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}

-- Verbatim host proof; it needs the host's heartbeat budget.
set_option maxHeartbeats 1000000 in
/-- Sign-free copy of `HigherDimLQGMetric.l2b_ae_convTrunc_radial_all`. -/
theorem l2b_ae_convTrunc_radial_all_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ), 0 < ε → ∀ z : Rd d, ∀ n : ℕ,
      h ω (convTrunc κ ε z n) =
        ((volume : Measure (Rd d)).toSphere univ).toReal *
          ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
            l2b_axisFactor κ n (Real.log ε) r * sphereAvg (h ω) r z := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (ℝ × Rd d)
  let _ : Countable S := hSc.to_subtype
  have hfix : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ p : S,
      h ω (convTrunc κ (Real.exp p.1.1) p.1.2 n) =
        ((volume : Measure (Rd d)).toSphere univ).toReal *
          ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
            l2b_axisFactor κ n p.1.1 r * sphereAvg (h ω) r p.1.2 := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro p
    filter_upwards [l2b_ae_convTrunc_radial_seed hd hκ hh.1 (Real.exp p.1.1) p.1.2 n]
      with ω hw
    simpa only [l2b_axisFactor] using hw
  filter_upwards [hfix, hh.1.ae_continuousOn_sphereAvg hd,
    l2b_ae_growth_all hd hh] with ω hfix hcont hgrowth
  intro ε hε z n
  let lhs : ℝ × Rd d → ℝ := fun p => h ω (convTrunc κ (Real.exp p.1) p.2 n)
  let rhs : ℝ × Rd d → ℝ := fun p =>
    ((volume : Measure (Rd d)).toSphere univ).toReal *
      ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
        l2b_axisFactor κ n p.1 r * sphereAvg (h ω) r p.2
  have hlhs : Continuous lhs :=
    (h ω).continuous.comp (l2b_continuous_convTrunc_exp_seed hd hκ n)
  have hrhs : Continuous rhs :=
    continuous_const.mul (l2b_continuous_trunc_radial_integral_seed hd hκ n (h ω)
      hcont.2 hgrowth)
  have heq : lhs = rhs := Continuous.ext_on hSd hlhs hrhs (by
    intro p hp
    exact hfix n ⟨p, hp⟩)
  have hp := congrFun heq (Real.log ε, z)
  simpa only [lhs, rhs, Real.exp_log hε] using hp

end RadialAll

section RadialLimit
/-! Copies from `HigherDimLQGMetric.ConvField.RadialLimit`. -/

open MeasureTheory Set Metric Filter Topology
open HigherDimLFPP (Rd e₁)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Sign-free copy of `HigherDimLQGMetric.l2b_integrable_radial_sphereAvg`. -/
theorem l2b_integrable_radial_sphereAvg_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) {ε : ℝ} (hε : 0 < ε)
    (T : DistRd d) (z : Rd d)
    (hcont : ContinuousOn (fun p : ℝ × Rd d => sphereAvg T p.1 p.2)
      (Ioi 0 ×ˢ univ))
    (hgrowth : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ closedBall (0 : Rd d) (N : ℝ), ∀ r : ℝ, 0 < r →
        |sphereAvg T r z| ≤ C * l2b_growthWeight r) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) *
      convKernelEps κ ε (r • e₁ d) * sphereAvg T r z) (Ioi (0 : ℝ)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
  obtain ⟨C, hC0, hC⟩ := hgrowth N
  have hz : z ∈ closedBall (0 : Rd d) (N : ℝ) := by
    rw [mem_closedBall, dist_zero_right]
    exact le_of_lt hN
  have hKc : Continuous fun r : ℝ => convKernelEps κ ε (r • e₁ d) := by
    dsimp [convKernelEps]
    exact continuous_const.mul
      ((convKernel_contDiff_seed (by omega) hκ).continuous.comp
        ((continuous_const : Continuous fun _ : ℝ => ε⁻¹).smul
          (continuous_id.smul continuous_const)))
  have hrad : ContinuousOn (fun r : ℝ => sphereAvg T r z) (Ioi 0) := by
    change ContinuousOn ((fun p : ℝ × Rd d => sphereAvg T p.1 p.2) ∘
      (fun r : ℝ => (r, z))) (Ioi 0)
    exact hcont.comp (by fun_prop : ContinuousOn (fun r : ℝ => (r, z)) (Ioi 0))
      (by simp [MapsTo])
  have hmeas : AEStronglyMeasurable (fun r : ℝ => r ^ (d - 1) *
      convKernelEps κ ε (r • e₁ d) * sphereAvg T r z)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (((continuous_id.pow _).mul hKc).continuousOn.mul hrad).aestronglyMeasurable
      measurableSet_Ioi
  have hsource : IntegrableOn (fun r : ℝ => C *
      |r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * l2b_growthWeight r|)
      (Ioi (0 : ℝ)) :=
    (l2b_integrable_radial_growth_kernel_seed hd hκ hε).norm.const_mul C
  apply hsource.mono' hmeas
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r hr => ?_)
  have hp0 : 0 ≤ r ^ (d - 1) := pow_nonneg hr.le _
  have hW0 : 0 ≤ l2b_growthWeight r :=
    (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
  have hg := hC z hz r hr
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp0,
    abs_of_nonneg hW0]
  calc r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| * |sphereAvg T r z|
      ≤ r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| *
          (C * l2b_growthWeight r) := by gcongr
    _ = C * (r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| *
        l2b_growthWeight r) := by ring

-- Verbatim host proof; it needs the host's heartbeat budget.
set_option maxHeartbeats 1000000 in
/-- Sign-free copy of `HigherDimLQGMetric.l2b_tendsto_radial_trunc`. -/
theorem l2b_tendsto_radial_trunc_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) {ε : ℝ} (hε : 0 < ε)
    (T : DistRd d) (z : Rd d)
    (hcont : ContinuousOn (fun p : ℝ × Rd d => sphereAvg T p.1 p.2)
      (Ioi 0 ×ˢ univ))
    (hgrowth : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ closedBall (0 : Rd d) (N : ℝ), ∀ r : ℝ, 0 < r →
        |sphereAvg T r z| ≤ C * l2b_growthWeight r) :
    Tendsto (fun n : ℕ => ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
      l2b_axisFactor κ n (Real.log ε) r * sphereAvg T r z) atTop
      (𝓝 (∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
        convKernelEps κ ε (r • e₁ d) * sphereAvg T r z)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
  obtain ⟨C, hC0, hC⟩ := hgrowth N
  have hz : z ∈ closedBall (0 : Rd d) (N : ℝ) := by
    rw [mem_closedBall, dist_zero_right]
    exact le_of_lt hN
  let K : ℝ → ℝ := fun r => convKernelEps κ ε (r • e₁ d)
  let g : ℝ → ℝ := fun r => r ^ (d - 1) * K r * sphereAvg T r z
  let F : ℕ → ℝ → ℝ := fun n r => g r *
    radialProfile d (((n : ℝ) + 1)⁻¹ • (r • e₁ d))
  let bound : ℝ → ℝ := fun r => C * |r ^ (d - 1) * K r * l2b_growthWeight r|
  have hbound : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (l2b_integrable_radial_growth_kernel_seed hd hκ hε).norm.const_mul C
  have hKc : Continuous K := by
    dsimp [K, convKernelEps]
    exact continuous_const.mul
      ((convKernel_contDiff_seed (by omega) hκ).continuous.comp
        ((continuous_const : Continuous fun _ : ℝ => ε⁻¹).smul
          (continuous_id.smul continuous_const)))
  have hrad : ContinuousOn (fun r : ℝ => sphereAvg T r z) (Ioi 0) := by
    change ContinuousOn ((fun p : ℝ × Rd d => sphereAvg T p.1 p.2) ∘
      (fun r : ℝ => (r, z))) (Ioi 0)
    exact hcont.comp (by fun_prop : ContinuousOn (fun r : ℝ => (r, z)) (Ioi 0))
      (by simp [MapsTo])
  have hgc : ContinuousOn g (Ioi 0) :=
    ((continuous_id.pow _).mul hKc).continuousOn.mul hrad
  have hFm (n : ℕ) : AEStronglyMeasurable (F n) (volume.restrict (Ioi (0 : ℝ))) := by
    have hcut : Continuous fun r : ℝ =>
        radialProfile d (((n : ℝ) + 1)⁻¹ • (r • e₁ d)) :=
      (radialProfile d).contDiff.continuous.comp
        ((continuous_const : Continuous fun _ : ℝ => ((n : ℝ) + 1)⁻¹).smul
          (continuous_id.smul continuous_const))
    exact (hgc.mul hcut.continuousOn).aestronglyMeasurable measurableSet_Ioi
  have hdom (n : ℕ) : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖F n r‖ ≤ bound r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hp0 : 0 ≤ r ^ (d - 1) := pow_nonneg hr.le _
    have hW0 : 0 ≤ l2b_growthWeight r :=
      (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
    have hcut0 := radialProfile_nonneg (((n : ℝ) + 1)⁻¹ • (r • e₁ d))
    have hcut1 := radialProfile_le_one (((n : ℝ) + 1)⁻¹ • (r • e₁ d))
    have hgr := hC z hz r hr
    dsimp [F, g, bound]
    rw [abs_mul, abs_mul, abs_mul,
      abs_of_nonneg hp0, abs_of_nonneg hcut0]
    have hbase0 : 0 ≤ r ^ (d - 1) * |K r| := mul_nonneg hp0 (abs_nonneg _)
    have hmain : r ^ (d - 1) * |K r| * |sphereAvg T r z| ≤
        C * |r ^ (d - 1) * K r * l2b_growthWeight r| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg hW0]
      calc r ^ (d - 1) * |K r| * |sphereAvg T r z|
          ≤ r ^ (d - 1) * |K r| * (C * l2b_growthWeight r) :=
            mul_le_mul_of_nonneg_left hgr hbase0
        _ = C * (r ^ (d - 1) * |K r| * l2b_growthWeight r) := by ring
    exact (mul_le_of_le_one_right (by positivity) hcut1).trans hmain
  have hlim : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      Tendsto (fun n : ℕ => F n r) atTop (𝓝 (g r)) := by
    filter_upwards with r
    have he : (fun n : ℕ => F n r) =ᶠ[atTop] fun _ => g r := by
      filter_upwards [l2b_cutoff_eventually_one (0 : Rd d) (r • e₁ d)] with n hn
      dsimp [F]
      simpa using congrArg (g r * ·) hn
    exact tendsto_const_nhds.congr' he.symm
  have ht := tendsto_integral_of_dominated_convergence bound hFm hbound hdom hlim
  convert ht using 1
  · funext n
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp [F, g, l2b_axisFactor]
    rw [Real.exp_log hε]
    ring

end RadialLimit

section RadialMain
/-! Copies from `HigherDimLQGMetric.ConvField.RadialMain`. -/

open MeasureTheory Set Metric Filter Topology
open HigherDimLFPP (Rd e₁)

/-- MA5 Details (c), L2b: the convolution field has the polar formula.
Sign-free copy of `HigherDimLQGMetric.L2b_radial`. -/
def L2b_radial_seed : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPPAS.IsAdmissibleSeed κ →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d),
    IsNormalizedLGF h P → ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
      convMollify κ ε (h ω) z = (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * sphereAvg (h ω) r z

/-- Sign-free copy of `HigherDimLQGMetric.l2b_ae_convMollify_tendsto`. -/
theorem l2b_ae_convMollify_tendsto_seed (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
      Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop
        (𝓝 (((volume : Measure (Rd d)).toSphere univ).toReal *
          ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
            convKernelEps κ ε (r • e₁ d) * sphereAvg (h ω) r z)) := by
  filter_upwards [l2b_ae_convTrunc_radial_all_seed hd hκ hh,
    hh.1.ae_continuousOn_sphereAvg hd, l2b_ae_growth_all hd hh]
    with ω hrad hcont hgrowth
  intro ε hε z
  have ht := (l2b_tendsto_radial_trunc_seed hd hκ hε (h ω) z hcont.2 hgrowth).const_mul
    ((volume : Measure (Rd d)).toSphere univ).toReal
  convert ht using 1
  funext n
  exact hrad ε hε z n

/-- Exact MA5 statement.
Sign-free copy of `HigherDimLQGMetric.l2b_radial`. -/
theorem l2b_radial_seed : L2b_radial_seed := by
  intro d hd κ hκ Ω _ P _ h hh
  filter_upwards [l2b_ae_convMollify_tendsto_seed d hd κ hκ P h hh] with ω hω
  intro ε hε z
  have hlim := hω ε hε z
  rw [l2b_convMollify_eq_of_tendsto hlim, l2b_sphere_area d hd]

end RadialMain

section JointMain
/-! Copies from `HigherDimLQGMetric.ConvField.JointMain`. -/

open MeasureTheory Set Metric Filter Topology
open HigherDimLFPP (Rd e₁)

/-- Sign-free copy of `HigherDimLQGMetric.l2b_ae_convMollify_continuousOn`. -/
theorem l2b_ae_convMollify_continuousOn_seed (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ContinuousOn
      (fun p : ℝ × Rd d => convMollify κ p.1 (h ω) p.2) (Ioi 0 ×ˢ univ) := by
  filter_upwards [l2b_radial_seed d hd κ hκ P h hh,
    hh.1.ae_continuousOn_sphereAvg hd, l2b_ae_growth_all hd hh]
    with ω hrad hcont hgrowth
  have hlog : ContinuousOn (fun p : ℝ × Rd d => Real.log p.1) (Ioi 0 ×ˢ univ) :=
    Real.continuousOn_log.comp continuous_fst.continuousOn (fun p hp => hp.1.ne')
  have hmap : ContinuousOn (fun p : ℝ × Rd d => (Real.log p.1, p.2))
      (Ioi 0 ×ˢ univ) := hlog.prodMk continuous_snd.continuousOn
  have hright : ContinuousOn (fun p : ℝ × Rd d =>
      (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
          convKernelEps κ p.1 (r • e₁ d) * sphereAvg (h ω) r p.2)
      (Ioi 0 ×ˢ univ) := by
    have hc := l2b_continuous_radial_integral_seed hd hκ (h ω) hcont.2 hgrowth
    have hc' : ContinuousOn (fun p : ℝ × Rd d =>
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
          convKernelEps κ p.1 (r • e₁ d) * sphereAvg (h ω) r p.2)
        (Ioi 0 ×ˢ univ) := by
      have hcomp := hc.comp_continuousOn hmap
      exact hcomp.congr (by
        intro p hp
        simp only [Function.comp_apply]
        rw [Real.exp_log hp.1])
    exact continuousOn_const.mul hc'
  refine hright.congr ?_
  intro p hp
  exact hrad p.1 hp.1 p.2

end JointMain

section Shifts
/-! Copies from `HigherDimLQGMetric.ConvField.Shifts`. -/

open MeasureTheory Set Metric Filter Topology
open HigherDimLFPP (Rd)

/-- Sign-free copy of `HigherDimLQGMetric.l2b_ae_convMollify_addConst`. -/
theorem l2b_ae_convMollify_addConst_seed (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z : Rd d, ∀ c : ℝ,
      convMollify κ ε (addConst (h ω) c) z = convMollify κ ε (h ω) z + c := by
  filter_upwards [l2b_ae_convMollify_tendsto_seed d hd κ hκ P h hh] with ω hω
  intro ε hε z c
  exact l2b_convMollify_addConst_of_tendsto_seed hd hκ hε (hω ε hε z)

/-- Sign-free copy of `HigherDimLQGMetric.l2b_convMollify_translate`. -/
theorem l2b_convMollify_translate_seed (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (ε : ℝ) (g : DistRd d) (w z : Rd d) :
    convMollify κ ε (affineComp 1 w g) z = convMollify κ ε g (z + w) :=
  l2b_convMollify_comp_translate_seed hd hκ ε g w z

end Shifts

section WholeSpaceLimit
/-! Copies from `HigherDimLQGMetric.ConvField.WholeSpaceLimit`. -/

open MeasureTheory Set Metric Filter Topology
open HigherDimLFPP (Rd)

/-- Sign-free copy of `HigherDimLQGMetric.l2b_ae_pairing_tendsto_wholeSpace`. -/
theorem l2b_ae_pairing_tendsto_wholeSpace_seed (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
      ∃ a : ℝ, Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop (𝓝 a) := by
  have hconv : ∀ᵐ ω ∂P, h ω ∈ convSet d := by
    filter_upwards [hh.ae_continuousOn_sphereAvg hd] with ω hω
    exact ⟨_, hω.1 1 one_pos 0⟩
  let g : Ω → DistRd d := fun ω => addConst (h ω) (-sphereAvg (h ω) 1 0)
  have hg : IsNormalizedLGF g P := hh.isNormalizedLGF_normalize (by omega) hconv
  filter_upwards [l2b_ae_convMollify_tendsto_seed d hd κ hκ P g hg]
    with ω hω
  intro ε hε z
  obtain ⟨a, ha⟩ : ∃ a : ℝ,
      Tendsto (fun n : ℕ => g ω (convTrunc κ ε z n)) atTop (𝓝 a) :=
    ⟨_, hω ε hε z⟩
  have hmass := (l2b_tendsto_integral_convTrunc_seed hd hκ hε z).const_mul
    (sphereAvg (h ω) 1 0)
  refine ⟨a + sphereAvg (h ω) 1 0, ?_⟩
  convert ha.add hmass using 1
  · funext n
    dsimp [g]
    rw [addConst_apply]
    ring
  · simp

end WholeSpaceLimit

section WholeSpaceRadial
/-! Copies from `HigherDimLQGMetric.ConvField.WholeSpaceRadial`. -/

open MeasureTheory Set Metric Filter Topology
open HigherDimLFPP (Rd e₁)

/-- Sign-free copy of `HigherDimLQGMetric.l2b_ae_radial_wholeSpace`. -/
theorem l2b_ae_radial_wholeSpace_seed (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
      convMollify κ ε (h ω) z =
        ((volume : Measure (Rd d)).toSphere univ).toReal *
          ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
            convKernelEps κ ε (r • e₁ d) * sphereAvg (h ω) r z := by
  have hcontH := hh.ae_continuousOn_sphereAvg hd
  have hconv : ∀ᵐ ω ∂P, h ω ∈ convSet d := by
    filter_upwards [hcontH] with ω hω
    exact ⟨_, hω.1 1 one_pos 0⟩
  let g : Ω → DistRd d := fun ω => addConst (h ω) (-sphereAvg (h ω) 1 0)
  have hg : IsNormalizedLGF g P := hh.isNormalizedLGF_normalize (by omega) hconv
  filter_upwards [hcontH, hg.1.ae_continuousOn_sphereAvg hd,
    l2b_ae_growth_all hd hg, l2b_radial_seed d hd κ hκ P g hg,
    l2b_ae_convMollify_tendsto_seed d hd κ hκ P g hg]
    with ω hcontH hcontG hgrowthG hradG hlimG
  intro ε hε z
  let c : ℝ := sphereAvg (h ω) 1 0
  have hEq : ∀ r : ℝ, 0 < r →
      sphereAvg (h ω) r z = sphereAvg (g ω) r z + c := by
    intro r hr
    have hs := sphereAvg_addConst_of_tendsto (by omega : 1 ≤ d)
      (hcontH.1 r hr z) (-c)
    change sphereAvg (g ω) r z = sphereAvg (h ω) r z + -c at hs
    linarith
  let base : ℝ → ℝ := fun r => r ^ (d - 1) * convKernelEps κ ε (r • e₁ d)
  have hgi : IntegrableOn (fun r : ℝ => base r * sphereAvg (g ω) r z) (Ioi (0 : ℝ)) :=
    l2b_integrable_radial_sphereAvg_seed hd hκ hε (g ω) z hcontG.2 hgrowthG
  have hki : IntegrableOn base (Ioi (0 : ℝ)) := l2b_integrable_radial_kernel_seed hd hκ hε
  have hci : IntegrableOn (fun r : ℝ => c * base r) (Ioi (0 : ℝ)) := hki.const_mul c
  have hI : (∫ r in Ioi (0 : ℝ), base r * sphereAvg (h ω) r z) =
      (∫ r in Ioi (0 : ℝ), base r * sphereAvg (g ω) r z) +
        c * (∫ r in Ioi (0 : ℝ), base r) := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), base r * sphereAvg (g ω) r z + c * base r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        change base r * sphereAvg (h ω) r z =
          base r * sphereAvg (g ω) r z + c * base r
        rw [hEq r hr]
        ring
      _ = (∫ r in Ioi (0 : ℝ), base r * sphereAvg (g ω) r z) +
          (∫ r in Ioi (0 : ℝ), c * base r) := integral_add hgi hci
      _ = _ := by rw [integral_const_mul]
  have heq : addConst (g ω) c = h ω := by
    dsimp [g, c]
    simpa only [neg_neg] using (addConst_neg (h ω) (-sphereAvg (h ω) 1 0))
  have hshift : convMollify κ ε (h ω) z = convMollify κ ε (g ω) z + c := by
    rw [← heq]
    exact l2b_convMollify_addConst_of_tendsto_seed hd hκ hε (hlimG ε hε z)
  rw [hshift, hradG ε hε z, ← l2b_sphere_area d hd]
  have hm := l2b_radial_kernel_mass_seed d hd κ hκ hε
  change ((volume : Measure (Rd d)).toSphere univ).toReal *
      (∫ r in Ioi (0 : ℝ), base r * sphereAvg (g ω) r z) + c =
    ((volume : Measure (Rd d)).toSphere univ).toReal *
      (∫ r in Ioi (0 : ℝ), base r * sphereAvg (h ω) r z)
  rw [hI]
  calc
    ((volume : Measure (Rd d)).toSphere univ).toReal *
        (∫ r in Ioi (0 : ℝ), base r * sphereAvg (g ω) r z) + c =
      ((volume : Measure (Rd d)).toSphere univ).toReal *
        (∫ r in Ioi (0 : ℝ), base r * sphereAvg (g ω) r z) +
      c * (((volume : Measure (Rd d)).toSphere univ).toReal *
        ∫ r in Ioi (0 : ℝ), base r) := by rw [show
        ((volume : Measure (Rd d)).toSphere univ).toReal *
          ∫ r in Ioi (0 : ℝ), base r = 1 from hm]; ring
    _ = _ := by ring

end WholeSpaceRadial

section Spec
/-! Copies from `HigherDimLQGMetric.ConvField.Spec`. -/

open MeasureTheory Set Metric Filter Topology
open HigherDimLFPP (Rd)

/-- Sign-free copy of `HigherDimLQGMetric.convMollify_spec_proof`. -/
theorem convMollify_spec_proof_seed :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPPAS.IsAdmissibleSeed κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusBddCont h P → ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂P, ∀ z : Rd d,
          Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop (𝓝 (convMollify κ ε (h ω) z)) := by
  intro d hd κ hκ Ω _ P _ h hh ε hε
  obtain ⟨_, f, _, hfbd, hg⟩ := hh
  let g : Ω → DistRd d := fun ω => h ω - ofCont (f ω)
  have hglim := l2b_ae_pairing_tendsto_wholeSpace_seed d hd κ hκ P g hg
  filter_upwards [hglim] with ω hω
  intro z
  obtain ⟨a, ha⟩ := hω ε hε z
  obtain ⟨M, hM⟩ := hfbd ω
  have hf := l2b_tendsto_pair_ofCont_seed hd hκ hε (f ω) M hM z
  have ht : Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop
      (𝓝 (a + ∫ w : Rd d, convKernelEps κ ε (z - w) * f ω w)) := by
    convert ha.add hf using 1
    funext n
    dsimp [g]
    simp only [sub_apply, sub_add_cancel]
  rwa [l2b_convMollify_eq_of_tendsto ht]

end Spec

section Scaling
/-! Copies from `HigherDimLQGMetric.ConvField.Scaling`. -/

open MeasureTheory Set Metric Filter Topology
open HigherDimLFPP (Rd e₁)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Sign-free copy of `HigherDimLQGMetric.l2b_ae_convMollify_scale`. -/
theorem l2b_ae_convMollify_scale_seed (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
      convMollify κ (ε / ρ) (affineComp ρ 0 (h ω)) z =
        convMollify κ ε (h ω) (ρ • z) := by
  have hh' : IsWholeSpaceLGF (fun ω => affineComp ρ 0 (h ω)) P := hh.affineComp hρ 0
  filter_upwards [l2b_ae_radial_wholeSpace_seed d hd κ hκ P h hh,
    l2b_ae_radial_wholeSpace_seed d hd κ hκ P
      (fun ω => affineComp ρ 0 (h ω)) hh',
    l2b_ae_sphereAvg_scale_all d hd P h hh hρ]
    with ω hrad hrad' hscale
  intro ε hε z
  rw [hrad' (ε / ρ) (div_pos hε hρ) z, hrad ε hε (ρ • z)]
  congr 1
  exact l2b_radial_integral_scale hd hε hρ
    (fun r => sphereAvg (affineComp ρ 0 (h ω)) r z)
    (fun s => sphereAvg (h ω) s (ρ • z)) (fun r hr => hscale r hr z)

end Scaling

section ConvMollifySpec
/-! Copies from `HigherDimLQGMetric.Assembly.ConvMollifySpec`. -/

open MeasureTheory Filter Topology
open HigherDimLFPP (Rd)

/-- The frozen statement of `convMollify_spec`, proved.
Sign-free copy of `HigherDimLQGMetric.convMollify_spec_impl`. -/
theorem convMollify_spec_impl_seed :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPPAS.IsAdmissibleSeed κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusBddCont h P → ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂P, ∀ z : Rd d,
          Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop (𝓝 (convMollify κ ε (h ω) z)) :=
  convMollify_spec_proof_seed

end ConvMollifySpec

end HigherDimLFPPAS.Signed
