import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLFPPAS.Signed.KernelDecay
import HigherDimLQGMetric.ConvField.AxisFactor
import HigherDimLQGMetric.ConvField.RadialCont
import HigherDimLQGMetric.ConvField.KernelUniform
import HigherDimLQGMetric.ConvField.Joint
import HigherDimLQGMetric.ConvField.Basic
import HigherDimLQGMetric.ConvField.Mass
import HigherDimLQGMetric.ConvField.RadialIntegrable
import HigherDimLQGMetric.ConvField.Affine
import HigherDimLQGMetric.ConvField.ParamTest
import HigherDimLQGMetric.ConvField.TruncRadial
import HigherDimLQGMetric.ConvField.RadialWeightIntegrable

/-!
# Sign-free copies: the convolution field: truncations, parameter continuity, radial integrability

Packet G1 (ruling L7; planning audit `planning/audits/MA3-inputs.md` §4.1 and §4.3 items 1–2). The declarations of
`HigherDimLQGMetric.ConvField.AxisFactor`, `HigherDimLQGMetric.ConvField.RadialCont`,
`HigherDimLQGMetric.ConvField.KernelUniform`, `HigherDimLQGMetric.ConvField.Joint`,
`HigherDimLQGMetric.ConvField.Basic`, `HigherDimLQGMetric.ConvField.Mass`,
`HigherDimLQGMetric.ConvField.RadialIntegrable`, `HigherDimLQGMetric.ConvField.Affine`,
`HigherDimLQGMetric.ConvField.ParamTest`, `HigherDimLQGMetric.ConvField.TruncRadial`,
`HigherDimLQGMetric.ConvField.RadialWeightIntegrable`
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

section AxisFactor
/-! Copies from `HigherDimLQGMetric.ConvField.AxisFactor`. -/

open MeasureTheory Set Metric Filter Topology
open HigherDimLFPP (Rd e₁)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Sign-free copy of `HigherDimLQGMetric.l2b_continuous_axisFactor`. -/
theorem l2b_continuous_axisFactor_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n : ℕ) :
    Continuous fun p : ℝ × ℝ => l2b_axisFactor κ n p.1 p.2 := by
  have he : Continuous fun p : ℝ × ℝ => Real.exp p.1 :=
    Real.continuous_exp.comp continuous_fst
  have hscale : Continuous fun p : ℝ × ℝ => Real.exp p.1 ^ (-(d : ℝ)) :=
    he.rpow_const (fun p => Or.inl (Real.exp_ne_zero _))
  have hinv : Continuous fun p : ℝ × ℝ => (Real.exp p.1)⁻¹ :=
    he.inv₀ (fun p => Real.exp_ne_zero _)
  have haxis : Continuous fun p : ℝ × ℝ => p.2 • e₁ d :=
    continuous_snd.smul continuous_const
  have harg : Continuous fun p : ℝ × ℝ => (Real.exp p.1)⁻¹ • (p.2 • e₁ d) :=
    hinv.smul haxis
  have hcut : Continuous fun p : ℝ × ℝ =>
      radialProfile d (((n : ℝ) + 1)⁻¹ • (p.2 • e₁ d)) :=
    (radialProfile d).contDiff.continuous.comp
      ((continuous_const : Continuous fun _ : ℝ × ℝ => ((n : ℝ) + 1)⁻¹).smul haxis)
  exact (hscale.mul ((convKernel_contDiff_seed (by omega) hκ).continuous.comp harg)).mul hcut

end AxisFactor

section RadialCont
/-! Copies from `HigherDimLQGMetric.ConvField.RadialCont`. -/

open MeasureTheory Set Metric Filter Topology
open HigherDimLFPP (Rd e₁)
variable {d : ℕ} {κ : Rd d → ℝ}

-- Verbatim host proof; it needs the host's heartbeat budget.
set_option maxHeartbeats 1000000 in
/-- Sign-free copy of `HigherDimLQGMetric.l2b_continuous_trunc_radial_integral`. -/
theorem l2b_continuous_trunc_radial_integral_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n : ℕ) (T : DistRd d)
    (hcont : ContinuousOn (fun p : ℝ × Rd d => sphereAvg T p.1 p.2)
      (Ioi 0 ×ˢ univ))
    (hgrowth : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ closedBall (0 : Rd d) (N : ℝ), ∀ r : ℝ, 0 < r →
        |sphereAvg T r z| ≤ C * l2b_growthWeight r) :
    Continuous fun p : ℝ × Rd d =>
      ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * l2b_axisFactor κ n p.1 r *
        sphereAvg T r p.2 := by
  let R : ℝ := 2 * ((n : ℝ) + 1)
  have hR1 : 1 ≤ R := by
    dsimp [R]
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hR0 : 0 ≤ R := by linarith
  let F : (ℝ × Rd d) → ℝ → ℝ := fun p r =>
    r ^ (d - 1) * l2b_axisFactor κ n p.1 r * sphereAvg T r p.2
  change Continuous fun p : ℝ × Rd d => ∫ r in Ioi (0 : ℝ), F p r
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨N, hN⟩ := exists_nat_gt (‖p₀.2‖ + 2)
  obtain ⟨C, hC0, hC⟩ := hgrowth N
  let U : Set ℝ := closedBall p₀.1 1
  have hUc : IsCompact U := isCompact_closedBall _ _
  have hKc : IsCompact (U ×ˢ Icc (0 : ℝ) R) := hUc.prod isCompact_Icc
  have hfactor : Continuous fun q : ℝ × ℝ => |l2b_axisFactor κ n q.1 q.2| :=
    (l2b_continuous_axisFactor_seed hd hκ n).abs
  obtain ⟨M₀, hM₀⟩ := hKc.bddAbove_image hfactor.continuousOn
  let M : ℝ := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ u ∈ U, ∀ r ∈ Icc (0 : ℝ) R,
      |l2b_axisFactor κ n u r| ≤ M := by
    intro u hu r hr
    exact (hM₀ (mem_image_of_mem _ (show (u, r) ∈ U ×ˢ Icc 0 R from ⟨hu, hr⟩))).trans
      (le_max_left _ _)
  let B : ℝ := R ^ (d - 1) * max (Real.log R) 1 + 1
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  let D : ℝ := M * C * B
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  let bound : ℝ → ℝ := (Icc (0 : ℝ) R).indicator fun _ => D
  have hboundI : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_const isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc
  have hnu : U ∈ 𝓝 p₀.1 := closedBall_mem_nhds _ (by norm_num)
  have hnz : closedBall (0 : Rd d) (N : ℝ) ∈ 𝓝 p₀.2 := by
    apply Filter.mem_of_superset (isOpen_ball.mem_nhds ?_) ball_subset_closedBall
    rw [mem_ball, dist_zero_right]
    linarith
  have hnb : {p : ℝ × Rd d | p.1 ∈ U ∧ p.2 ∈ closedBall (0 : Rd d) (N : ℝ)} ∈ 𝓝 p₀ :=
    mem_nhds_prod_iff.mpr ⟨U, hnu, closedBall 0 (N : ℝ), hnz, by
      rintro p ⟨hu, hz⟩
      exact ⟨hu, hz⟩⟩
  apply continuousAt_of_dominated (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := F) (bound := bound)
  · filter_upwards with p
    have hrad : ContinuousOn (fun r : ℝ => sphereAvg T r p.2) (Ioi 0) := by
      have hmap : ContinuousOn (fun r : ℝ => (r, p.2)) (Ioi 0) := by fun_prop
      change ContinuousOn ((fun q : ℝ × Rd d => sphereAvg T q.1 q.2) ∘
        (fun r : ℝ => (r, p.2))) (Ioi 0)
      exact hcont.comp hmap (by simp [MapsTo])
    have hF : ContinuousOn (F p) (Ioi 0) := by
      dsimp [F]
      exact ((continuous_id.pow _).mul
        ((l2b_continuous_axisFactor_seed hd hκ n).comp
          (continuous_const.prodMk continuous_id))).continuousOn.mul hrad
    exact hF.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [hnb] with p hp
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hu : p.1 ∈ U := hp.1
    have hz : p.2 ∈ closedBall (0 : Rd d) (N : ℝ) := hp.2
    have hr0 : 0 < r := hr
    by_cases hrR : r ≤ R
    · have hrK : r ∈ Icc (0 : ℝ) R := ⟨hr0.le, hrR⟩
      have hprod := l2b_polar_log_weight_bounded hd hR1 hr0 hrR
      have hgrow := hC p.2 hz r hr0
      have hW0 : 0 ≤ l2b_growthWeight r := by
        dsimp [l2b_growthWeight]
        exact le_max_of_le_right (zero_le_one.trans (le_max_right _ _))
      have hp0 : 0 ≤ r ^ (d - 1) := pow_nonneg hr0.le _
      have hax := hM p.1 hu r hrK
      have hmain : |F p r| ≤ D := by
        dsimp [F, D, B]
        rw [abs_mul, abs_mul, abs_of_nonneg hp0]
        calc r ^ (d - 1) * |l2b_axisFactor κ n p.1 r| * |sphereAvg T r p.2|
            ≤ r ^ (d - 1) * M * (C * l2b_growthWeight r) := by
              gcongr
            _ = M * C * (r ^ (d - 1) * l2b_growthWeight r) := by ring
            _ ≤ M * C * B := by
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg hM0 hC0)
              exact hprod
      simpa only [Real.norm_eq_abs, bound, Set.indicator_of_mem hrK] using hmain
    · have hzero : l2b_axisFactor κ n p.1 r = 0 :=
        l2b_axisFactor_eq_zero hd n p.1 (le_of_not_ge hrR)
      have hnot : r ∉ Icc (0 : ℝ) R := fun hh => hrR hh.2
      simp [F, hzero, bound, Set.indicator_of_notMem hnot]
  · exact hboundI
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hs : ContinuousAt (fun p : ℝ × Rd d => sphereAvg T r p.2) p₀ := by
      have hmem : (r, p₀.2) ∈ Ioi 0 ×ˢ univ := ⟨hr, trivial⟩
      have hc : ContinuousAt (fun q : ℝ × Rd d => sphereAvg T q.1 q.2) (r, p₀.2) :=
        hcont.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)
      exact hc.comp₂ continuousAt_const continuousAt_snd
    have hfac : ContinuousAt (fun p : ℝ × Rd d => l2b_axisFactor κ n p.1 r) p₀ :=
      (l2b_continuous_axisFactor_seed hd hκ n).continuousAt.comp
        (by fun_prop : ContinuousAt (fun p : ℝ × Rd d => (p.1, r)) p₀)
    exact ((continuousAt_const.mul hfac).mul hs)

end RadialCont

section KernelUniform
/-! Copies from `HigherDimLQGMetric.ConvField.KernelUniform`. -/

open MeasureTheory Set Metric Filter Topology
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Sign-free copy of `HigherDimLQGMetric.l2b_continuous_kernelAxis_exp`. -/
theorem l2b_continuous_kernelAxis_exp_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    Continuous fun p : ℝ × ℝ => convKernelEps κ (Real.exp p.1) (p.2 • HigherDimLFPP.e₁ d) := by
  have he : Continuous fun p : ℝ × ℝ => Real.exp p.1 :=
    Real.continuous_exp.comp continuous_fst
  have hscale : Continuous fun p : ℝ × ℝ => Real.exp p.1 ^ (-(d : ℝ)) :=
    he.rpow_const (fun p => Or.inl (Real.exp_ne_zero _))
  have hinv : Continuous fun p : ℝ × ℝ => (Real.exp p.1)⁻¹ :=
    he.inv₀ (fun p => Real.exp_ne_zero _)
  have haxis : Continuous fun p : ℝ × ℝ => p.2 • HigherDimLFPP.e₁ d :=
    continuous_snd.smul continuous_const
  have harg : Continuous fun p : ℝ × ℝ =>
      (Real.exp p.1)⁻¹ • (p.2 • HigherDimLFPP.e₁ d) := hinv.smul haxis
  exact hscale.mul ((convKernel_contDiff_seed (by omega) hκ).continuous.comp harg)

/-- Sign-free copy of `HigherDimLQGMetric.l2b_exists_uniform_kernel_decay`. -/
theorem l2b_exists_uniform_kernel_decay_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {a b : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, a ≤ ε → ε ≤ b → ∀ x : Rd d,
      |convKernelEps κ ε x| ≤ M * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by
  obtain ⟨C₀, hC₀⟩ := convKernel_decay_seed hd hκ
  let C : ℝ := max C₀ 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC (x : Rd d) : |convKernel κ x| ≤ C * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) :=
    (hC₀ x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by positivity) _))
  let D : ℝ := max 1 b
  have hD1 : 1 ≤ D := le_max_left _ _
  have hbD : b ≤ D := le_max_right _ _
  have hD0 : 0 < D := by linarith
  let M : ℝ := a ^ (-(d : ℝ)) * C * (D⁻¹) ^ (-((d : ℝ) + 1))
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M, hM0, fun ε hεa hεb x => ?_⟩
  have hε0 : 0 < ε := ha.trans_le hεa
  have hεD : ε ≤ D := hεb.trans hbD
  have hεinv : D⁻¹ ≤ ε⁻¹ := inv_anti₀ hε0 hεD
  have hDinv : D⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD1
  have hbase : D⁻¹ * (1 + ‖x‖) ≤ 1 + ‖ε⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε0)]
    have hnr : 0 ≤ ‖x‖ := norm_nonneg x
    nlinarith [mul_le_mul_of_nonneg_right hεinv hnr]
  have hbase0 : 0 < D⁻¹ * (1 + ‖x‖) := by positivity
  have hpow : (1 + ‖ε⁻¹ • x‖) ^ (-((d : ℝ) + 1)) ≤
      (D⁻¹) ^ (-((d : ℝ) + 1)) * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by
    calc
      _ ≤ (D⁻¹ * (1 + ‖x‖)) ^ (-((d : ℝ) + 1)) :=
        Real.rpow_le_rpow_of_nonpos hbase0 hbase (by
          have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          linarith)
      _ = _ := Real.mul_rpow (by positivity) (by positivity)
  have hεpow : ε ^ (-(d : ℝ)) ≤ a ^ (-(d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ha hεa (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith)
  rw [convKernelEps, abs_mul, abs_of_nonneg (Real.rpow_nonneg hε0.le _)]
  calc ε ^ (-(d : ℝ)) * |convKernel κ (ε⁻¹ • x)|
      ≤ ε ^ (-(d : ℝ)) * (C * (1 + ‖ε⁻¹ • x‖) ^ (-((d : ℝ) + 1))) := by
        gcongr
        exact hC _
    _ ≤ a ^ (-(d : ℝ)) * (C * ((D⁻¹) ^ (-((d : ℝ) + 1)) *
        (1 + ‖x‖) ^ (-((d : ℝ) + 1)))) := by
        gcongr
    _ = M * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by dsimp [M]; ring

end KernelUniform

section Joint
/-! Copies from `HigherDimLQGMetric.ConvField.Joint`. -/

open MeasureTheory Set Metric Filter Topology
open HigherDimLFPP (Rd e₁)
variable {d : ℕ} {κ : Rd d → ℝ}

-- Verbatim host proof; it needs the host's heartbeat budget.
set_option maxHeartbeats 1000000 in
/-- Sign-free copy of `HigherDimLQGMetric.l2b_continuous_radial_integral`. -/
theorem l2b_continuous_radial_integral_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (T : DistRd d)
    (hcont : ContinuousOn (fun p : ℝ × Rd d => sphereAvg T p.1 p.2)
      (Ioi 0 ×ˢ univ))
    (hgrowth : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ closedBall (0 : Rd d) (N : ℝ), ∀ r : ℝ, 0 < r →
        |sphereAvg T r z| ≤ C * l2b_growthWeight r) :
    Continuous fun p : ℝ × Rd d =>
      ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
        convKernelEps κ (Real.exp p.1) (r • e₁ d) * sphereAvg T r p.2 := by
  let F : (ℝ × Rd d) → ℝ → ℝ := fun p r =>
    r ^ (d - 1) * convKernelEps κ (Real.exp p.1) (r • e₁ d) * sphereAvg T r p.2
  change Continuous fun p : ℝ × Rd d => ∫ r in Ioi (0 : ℝ), F p r
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨N, hN⟩ := exists_nat_gt (‖p₀.2‖ + 2)
  obtain ⟨C, hC0, hC⟩ := hgrowth N
  let a : ℝ := Real.exp (p₀.1 - 1)
  let b : ℝ := Real.exp (p₀.1 + 1)
  have ha : 0 < a := Real.exp_pos _
  obtain ⟨M, hM0, hM⟩ := l2b_exists_uniform_kernel_decay_seed hd hκ (a := a) (b := b) ha
  let bound : ℝ → ℝ := fun r => M * C *
    (r ^ (d - 1) * l2b_decayEnvelope d r * l2b_growthWeight r)
  have hbound : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (l2b_integrable_radial_growth_decayEnvelope d hd).const_mul (M * C)
  have hnu : closedBall p₀.1 1 ∈ 𝓝 p₀.1 := closedBall_mem_nhds _ (by norm_num)
  have hnz : closedBall (0 : Rd d) (N : ℝ) ∈ 𝓝 p₀.2 := by
    apply Filter.mem_of_superset (isOpen_ball.mem_nhds ?_) ball_subset_closedBall
    rw [mem_ball, dist_zero_right]
    linarith
  have hnb : {p : ℝ × Rd d | p.1 ∈ closedBall p₀.1 1 ∧
      p.2 ∈ closedBall (0 : Rd d) (N : ℝ)} ∈ 𝓝 p₀ :=
    mem_nhds_prod_iff.mpr ⟨closedBall p₀.1 1, hnu,
      closedBall 0 (N : ℝ), hnz, by rintro p ⟨hu, hz⟩; exact ⟨hu, hz⟩⟩
  apply continuousAt_of_dominated (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := F) (bound := bound)
  · filter_upwards with p
    have hrad : ContinuousOn (fun r : ℝ => sphereAvg T r p.2) (Ioi 0) := by
      change ContinuousOn ((fun q : ℝ × Rd d => sphereAvg T q.1 q.2) ∘
        (fun r : ℝ => (r, p.2))) (Ioi 0)
      exact hcont.comp (by fun_prop : ContinuousOn (fun r : ℝ => (r, p.2)) (Ioi 0))
        (by simp [MapsTo])
    have hK : Continuous fun r : ℝ =>
        convKernelEps κ (Real.exp p.1) (r • e₁ d) := by
      change Continuous ((fun q : ℝ × ℝ =>
        convKernelEps κ (Real.exp q.1) (q.2 • e₁ d)) ∘ (fun r : ℝ => (p.1, r)))
      exact (l2b_continuous_kernelAxis_exp_seed hd hκ).comp (by fun_prop)
    have hF : ContinuousOn (F p) (Ioi 0) :=
      ((continuous_id.pow _).mul hK).continuousOn.mul hrad
    exact hF.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [hnb] with p hp
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hu : p.1 ∈ closedBall p₀.1 1 := hp.1
    have hz : p.2 ∈ closedBall (0 : Rd d) (N : ℝ) := hp.2
    have hule : p₀.1 - 1 ≤ p.1 ∧ p.1 ≤ p₀.1 + 1 := by
      rw [mem_closedBall, Real.dist_eq, abs_le] at hu
      constructor <;> linarith [hu.1, hu.2]
    have hεa : a ≤ Real.exp p.1 := Real.exp_le_exp.mpr hule.1
    have hεb : Real.exp p.1 ≤ b := Real.exp_le_exp.mpr hule.2
    have hk := hM (Real.exp p.1) hεa hεb (r • e₁ d)
    have hknorm : ‖r • e₁ d‖ = r := by
      rw [norm_smul, HigherDimLFPP.norm_e₁ (by omega : 0 < d), mul_one,
        Real.norm_eq_abs, abs_of_pos hr]
    rw [hknorm] at hk
    have hg := hC p.2 hz r hr
    have hp0 : 0 ≤ r ^ (d - 1) := pow_nonneg hr.le _
    have hW0 : 0 ≤ l2b_growthWeight r :=
      (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
    have henv0 : 0 ≤ l2b_decayEnvelope d r := by dsimp [l2b_decayEnvelope]; positivity
    have he : l2b_decayEnvelope d r =
        (1 + r) ^ (-((d : ℝ) + 1)) := by
      have hr0 : 0 < r := hr
      simp [l2b_decayEnvelope, max_eq_left hr0.le]
    rw [← he] at hk
    change |F p r| ≤ bound r
    dsimp [F, bound]
    rw [abs_mul, abs_mul, abs_of_nonneg hp0]
    calc r ^ (d - 1) * |convKernelEps κ (Real.exp p.1) (r • e₁ d)| *
          |sphereAvg T r p.2|
        ≤ r ^ (d - 1) * (M * l2b_decayEnvelope d r) *
            (C * l2b_growthWeight r) := by
          gcongr
      _ = M * C * (r ^ (d - 1) * l2b_decayEnvelope d r *
          l2b_growthWeight r) := by ring
  · exact hbound
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hs : ContinuousAt (fun p : ℝ × Rd d => sphereAvg T r p.2) p₀ := by
      have hmem : (r, p₀.2) ∈ Ioi 0 ×ˢ univ := ⟨hr, trivial⟩
      have hc : ContinuousAt (fun q : ℝ × Rd d => sphereAvg T q.1 q.2) (r, p₀.2) :=
        hcont.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)
      exact hc.comp₂ continuousAt_const continuousAt_snd
    have hK : ContinuousAt (fun p : ℝ × Rd d =>
        convKernelEps κ (Real.exp p.1) (r • e₁ d)) p₀ := by
      have hc : ContinuousAt (fun q : ℝ × ℝ =>
          convKernelEps κ (Real.exp q.1) (q.2 • e₁ d)) (p₀.1, r) :=
        (l2b_continuous_kernelAxis_exp_seed hd hκ).continuousAt
      exact hc.comp₂ continuousAt_fst continuousAt_const
    exact ((continuousAt_const.mul hK).mul hs)

end Joint

section Basic
/-! Copies from `HigherDimLQGMetric.ConvField.Basic`. -/

open HigherDimLFPP (Rd)
open MeasureTheory Filter Topology
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Sign-free copy of `HigherDimLQGMetric.l2b_convTrunc_apply`. -/
theorem l2b_convTrunc_apply_seed (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (ε : ℝ) (z : Rd d) (n : ℕ) (w : Rd d) :
    convTrunc κ ε z n w =
      convKernelEps κ ε (z - w) *
        radialProfile d (((n : ℝ) + 1)⁻¹ • (w - z)) := by
  unfold convTrunc
  rw [dite_eq_left (convKernel_contDiff_seed (by omega) hκ)]
  rfl

/-- Sign-free copy of `HigherDimLQGMetric.l2b_convTrunc_radial`. -/
theorem l2b_convTrunc_radial_seed (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (ε : ℝ) (z : Rd d) (n : ℕ) {w v : Rd d}
    (hwv : ‖w - z‖ = ‖v - z‖) :
    convTrunc κ ε z n w = convTrunc κ ε z n v := by
  rw [l2b_convTrunc_apply_seed hd hκ, l2b_convTrunc_apply_seed hd hκ]
  congr 1
  · apply l2b_convKernelEps_radial
    simpa only [norm_sub_rev] using hwv
  · apply radialProfile_eq_of_norm_eq
    simp only [norm_smul, hwv]

/-- Sign-free copy of `HigherDimLQGMetric.l2b_tendsto_integral_convTrunc`. -/
theorem l2b_tendsto_integral_convTrunc_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) {ε : ℝ} (hε : 0 < ε) (z : Rd d) :
    Tendsto (fun n : ℕ => ∫ w : Rd d, convTrunc κ ε z n w)
      atTop (𝓝 (1 : ℝ)) := by
  have hi : Integrable (fun w : Rd d => convKernelEps κ ε (z - w)) :=
    (integrable_convKernelEps_seed hd hκ hε).comp_sub_left z
  have hb : ∀ n, ∀ᵐ w ∂(volume : Measure (Rd d)),
      ‖convTrunc κ ε z n w‖ ≤ |convKernelEps κ ε (z - w)| := by
    intro n
    filter_upwards [] with w
    rw [l2b_convTrunc_apply_seed hd hκ, Real.norm_eq_abs, abs_mul]
    have hcut := radialProfile_nonneg (((n : ℝ) + 1)⁻¹ • (w - z))
    have hcut1 := radialProfile_le_one (((n : ℝ) + 1)⁻¹ • (w - z))
    rw [abs_of_nonneg hcut]
    exact mul_le_of_le_one_right (abs_nonneg _) hcut1
  have hl : ∀ᵐ w ∂(volume : Measure (Rd d)),
      Tendsto (fun n : ℕ => convTrunc κ ε z n w) atTop
        (𝓝 (convKernelEps κ ε (z - w))) := by
    filter_upwards [] with w
    have he : (fun n : ℕ => convTrunc κ ε z n w)
        =ᶠ[atTop] fun _ => convKernelEps κ ε (z - w) := by
      filter_upwards [l2b_cutoff_eventually_one z w] with n hn
      rw [l2b_convTrunc_apply_seed hd hκ, hn, mul_one]
    exact tendsto_const_nhds.congr' he.symm
  have ht := tendsto_integral_of_dominated_convergence
    (fun w : Rd d => |convKernelEps κ ε (z - w)|)
    (fun n => (l2b_integrable_convTrunc ε z n).aestronglyMeasurable)
    hi.abs hb hl
  have hmass : ∫ w : Rd d, convKernelEps κ ε (z - w) = 1 := by
    rw [integral_sub_left_eq_self]
    exact integral_convKernelEps_eq_one_seed hd hκ hε
  rwa [hmass] at ht

/-- Sign-free copy of `HigherDimLQGMetric.l2b_convMollify_addConst_of_tendsto`. -/
theorem l2b_convMollify_addConst_of_tendsto_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) {ε : ℝ} (hε : 0 < ε)
    {g : DistRd d} {z : Rd d} {a c : ℝ}
    (ha : Tendsto (fun n : ℕ => g (convTrunc κ ε z n)) atTop (𝓝 a)) :
    convMollify κ ε (addConst g c) z = convMollify κ ε g z + c := by
  have hc := (l2b_tendsto_integral_convTrunc_seed hd hκ hε z).const_mul c
  have hs : Tendsto (fun n : ℕ => (addConst g c) (convTrunc κ ε z n)) atTop
      (𝓝 (a + c)) := by
    convert ha.add hc using 1
    · funext n
      exact addConst_apply g c (convTrunc κ ε z n)
    · simp
  rw [l2b_convMollify_eq_of_tendsto hs, l2b_convMollify_eq_of_tendsto ha]

/-- Sign-free copy of `HigherDimLQGMetric.l2b_tendsto_pair_ofCont`. -/
theorem l2b_tendsto_pair_ofCont_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) {ε : ℝ} (hε : 0 < ε)
    (f : C(Rd d, ℝ)) (M : ℝ) (hM : ∀ w, |f w| ≤ M) (z : Rd d) :
    Tendsto (fun n : ℕ => (ofCont f) (convTrunc κ ε z n)) atTop
      (𝓝 (∫ w : Rd d, convKernelEps κ ε (z - w) * f w)) := by
  have hi : Integrable (fun w : Rd d => convKernelEps κ ε (z - w)) :=
    (integrable_convKernelEps_seed hd hκ hε).comp_sub_left z
  have hb : ∀ n, ∀ᵐ w ∂(volume : Measure (Rd d)),
      ‖convTrunc κ ε z n w * f w‖ ≤ |convKernelEps κ ε (z - w)| * M := by
    intro n
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul
      (by
        rw [l2b_convTrunc_apply_seed hd hκ, abs_mul]
        have hcut := radialProfile_nonneg (((n : ℝ) + 1)⁻¹ • (w - z))
        rw [abs_of_nonneg hcut]
        exact mul_le_of_le_one_right (abs_nonneg _)
          (radialProfile_le_one (((n : ℝ) + 1)⁻¹ • (w - z))))
      (hM w) (abs_nonneg _) (abs_nonneg _)
  have hl : ∀ᵐ w ∂(volume : Measure (Rd d)),
      Tendsto (fun n : ℕ => convTrunc κ ε z n w * f w) atTop
        (𝓝 (convKernelEps κ ε (z - w) * f w)) := by
    filter_upwards [] with w
    have he : (fun n : ℕ => convTrunc κ ε z n w * f w)
        =ᶠ[atTop] fun _ => convKernelEps κ ε (z - w) * f w := by
      filter_upwards [l2b_cutoff_eventually_one z w] with n hn
      rw [l2b_convTrunc_apply_seed hd hκ, hn, mul_one]
    exact tendsto_const_nhds.congr' he.symm
  have hm : ∀ n, AEStronglyMeasurable
      (fun w : Rd d => convTrunc κ ε z n w * f w) := by
    intro n
    exact ((convTrunc κ ε z n).continuous.mul f.continuous).aestronglyMeasurable
  have ht := tendsto_integral_of_dominated_convergence
    (fun w : Rd d => |convKernelEps κ ε (z - w)| * M)
    hm (hi.abs.mul_const M) hb hl
  convert ht using 1
  funext n
  exact ofCont_apply f (convTrunc κ ε z n)

end Basic

section Mass
/-! Copies from `HigherDimLQGMetric.ConvField.Mass`. -/

set_option linter.style.haveILetI false
open MeasureTheory Set Metric Filter Topology
open HigherDimLFPP (Rd e₁)

/-- Sign-free copy of `HigherDimLQGMetric.l2b_radial_kernel_mass`. -/
theorem l2b_radial_kernel_mass_seed (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {ε : ℝ} (hε : 0 < ε) :
    ((volume : Measure (Rd d)).toSphere univ).toReal *
      ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) = 1 := by
  haveI : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [finrank_euclideanSpace_fin]; omega)
  let f : ℝ → ℝ := fun r => convKernelEps κ ε (r • e₁ d)
  have hp := integral_fun_norm_addHaar (volume : Measure (Rd d)) f
  rw [finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul, Measure.real_def] at hp
  simp only [smul_eq_mul] at hp
  have harea : (d : ℝ) * (volume (ball (0 : Rd d) 1)).toReal =
      ((volume : Measure (Rd d)).toSphere univ).toReal := by
    rw [Measure.toSphere_apply_univ, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have heq : (∫ x : Rd d, f ‖x‖) = ∫ x : Rd d, convKernelEps κ ε x := by
    apply integral_congr_ae
    filter_upwards with x
    exact l2b_convKernelEps_axis_norm hd ε x
  rw [heq, integral_convKernelEps_eq_one_seed hd hκ hε] at hp
  rw [← harea]
  simpa only [f, mul_assoc] using hp.symm

end Mass

section RadialIntegrable
/-! Copies from `HigherDimLQGMetric.ConvField.RadialIntegrable`. -/

set_option linter.style.haveILetI false
open MeasureTheory Set Metric Filter Topology
open HigherDimLFPP (Rd e₁)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Sign-free copy of `HigherDimLQGMetric.l2b_integrable_radial_kernel`. -/
theorem l2b_integrable_radial_kernel_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) * convKernelEps κ ε (r • e₁ d))
      (Ioi (0 : ℝ)) := by
  haveI : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [finrank_euclideanSpace_fin]; omega)
  let f : ℝ → ℝ := fun r => convKernelEps κ ε (r • e₁ d)
  have hvec : Integrable (fun x : Rd d => f ‖x‖) := by
    apply (integrable_convKernelEps_seed hd hκ hε).congr
    filter_upwards with x
    exact (l2b_convKernelEps_axis_norm hd ε x).symm
  have hrad := (integrable_fun_norm_addHaar (μ := (volume : Measure (Rd d))) (f := f)).mp hvec
  simpa only [finrank_euclideanSpace_fin, smul_eq_mul] using hrad

/-- Sign-free copy of `HigherDimLQGMetric.l2b_integrable_radial_logKernel`. -/
theorem l2b_integrable_radial_logKernel_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) *
      (Real.log (2 + r) * convKernelEps κ ε (r • e₁ d))) (Ioi (0 : ℝ)) := by
  haveI : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [finrank_euclideanSpace_fin]; omega)
  let f : ℝ → ℝ := fun r => Real.log (2 + r) * convKernelEps κ ε (r • e₁ d)
  have hvec : Integrable (fun x : Rd d => f ‖x‖) := by
    apply (integrable_logMoment_convKernelEps_seed hd hκ hε).congr
    filter_upwards with x
    exact congrArg (Real.log (2 + ‖x‖) * ·)
      (l2b_convKernelEps_axis_norm hd ε x).symm
  have hrad := (integrable_fun_norm_addHaar (μ := (volume : Measure (Rd d))) (f := f)).mp hvec
  simpa only [finrank_euclideanSpace_fin, smul_eq_mul] using hrad

end RadialIntegrable

section Affine
/-! Copies from `HigherDimLQGMetric.ConvField.Affine`. -/

open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Sign-free copy of `HigherDimLQGMetric.l2b_testAffinePull_convTrunc`. -/
theorem l2b_testAffinePull_convTrunc_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (ε : ℝ)
    (w z : Rd d) (n : ℕ) :
    testAffinePull 1 w (convTrunc κ ε z n) = convTrunc κ ε (z + w) n := by
  ext x
  rw [testAffinePull_one_apply,
    l2b_convTrunc_apply_seed hd hκ,
    l2b_convTrunc_apply_seed hd hκ]
  congr 1 <;> congr 1 <;> abel_nf

/-- Sign-free copy of `HigherDimLQGMetric.l2b_convMollify_comp_translate`. -/
theorem l2b_convMollify_comp_translate_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (ε : ℝ)
    (g : DistRd d) (w z : Rd d) :
    convMollify κ ε (affineComp 1 w g) z = convMollify κ ε g (z + w) := by
  unfold convMollify
  congr 1
  funext n
  rw [affineComp_one_apply, l2b_testAffinePull_convTrunc_seed hd hκ]

end Affine

section ParamTest
/-! Copies from `HigherDimLQGMetric.ConvField.ParamTest`. -/

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open HigherDimLFPP (Rd)
variable {d : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Sign-free copy of `HigherDimLQGMetric.l2b_contDiff_convTrunc_exp_uncurry`. -/
theorem l2b_contDiff_convTrunc_exp_uncurry_seed (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry fun (q : ℝ × Rd d) (w : Rd d) =>
        convKernelEps κ (Real.exp q.1) (q.2 - w) *
          radialProfile d (((n : ℝ) + 1)⁻¹ • (w - q.2))) := by
  have hform : (Function.uncurry fun (q : ℝ × Rd d) (w : Rd d) =>
        convKernelEps κ (Real.exp q.1) (q.2 - w) *
          radialProfile d (((n : ℝ) + 1)⁻¹ • (w - q.2))) =
      fun p : (ℝ × Rd d) × Rd d =>
        (Real.exp (p.1.1 * (-(d : ℝ))) *
          convKernel κ (Real.exp (-p.1.1) • (p.1.2 - p.2))) *
          radialProfile d (((n : ℝ) + 1)⁻¹ • (p.2 - p.1.2)) := by
    funext p
    change Real.exp p.1.1 ^ (-(d : ℝ)) *
      convKernel κ ((Real.exp p.1.1)⁻¹ • (p.1.2 - p.2)) *
        radialProfile d (((n : ℝ) + 1)⁻¹ • (p.2 - p.1.2)) = _
    rw [← Real.exp_mul, ← Real.exp_neg]
  rw [hform]
  have hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × Rd d) × Rd d => p.1.1) :=
    contDiff_fst.comp contDiff_fst
  have hz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × Rd d) × Rd d => p.1.2) :=
    contDiff_snd.comp contDiff_fst
  have hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × Rd d) × Rd d => p.2) := contDiff_snd
  exact ((Real.contDiff_exp.comp (hu.mul contDiff_const)).mul
    ((convKernel_contDiff_seed (by omega) hκ).comp
      ((Real.contDiff_exp.comp hu.neg).smul (hz.sub hw)))).mul
    ((radialProfile d).contDiff.comp ((hw.sub hz).const_smul _))

set_option linter.style.haveILetI false in
/-- Sign-free copy of `HigherDimLQGMetric.l2b_continuous_convTrunc_exp_on_ball`. -/
theorem l2b_continuous_convTrunc_exp_on_ball_seed (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (n : ℕ) (z₀ : Rd d) :
    Continuous fun q : ℝ × closedBall z₀ 1 =>
      convTrunc κ (Real.exp q.1) (q.2 : Rd d) n := by
  let S : Set (Rd d) := closedBall z₀ 1
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall z₀ 1)
  let K : Compacts (Rd d) :=
    ⟨closedBall z₀ (2 * ((n : ℝ) + 1) + 2), isCompact_closedBall _ _⟩
  let Ψ : (ℝ × S) → Rd d → ℝ := fun q w =>
    convKernelEps κ (Real.exp q.1) ((q.2 : Rd d) - w) *
      radialProfile d (((n : ℝ) + 1)⁻¹ • (w - (q.2 : Rd d)))
  have hs : ∀ q : ℝ × S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ q) := by
    intro q
    have h := l2b_contDiff_convTrunc_exp_uncurry_seed hd hκ n
    have hmap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : Rd d => (((q.1, (q.2 : Rd d)) : ℝ × Rd d), w)) :=
      contDiff_const.prodMk contDiff_id
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using h.comp hmap
  have hK : ∀ q : ℝ × S, ∀ w ∉ (K : Set (Rd d)), Ψ q w = 0 := by
    intro q w hw
    have hwfar : 2 * ((n : ℝ) + 1) + 2 < ‖w - z₀‖ := by
      simpa [K, mem_closedBall, dist_eq_norm] using hw
    have hq : ‖(q.2 : Rd d) - z₀‖ ≤ 1 := by
      have hq' : (q.2 : Rd d) ∈ closedBall z₀ 1 := q.2.2
      rw [mem_closedBall, dist_eq_norm] at hq'
      exact hq'
    have htri : ‖w - z₀‖ ≤ ‖w - (q.2 : Rd d)‖ + ‖(q.2 : Rd d) - z₀‖ := by
      calc
        ‖w - z₀‖ = ‖(w - (q.2 : Rd d)) + ((q.2 : Rd d) - z₀)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have hdist : 2 * ((n : ℝ) + 1) ≤ ‖w - (q.2 : Rd d)‖ := by linarith
    have hscale : 2 ≤ ‖((n : ℝ) + 1)⁻¹ • (w - (q.2 : Rd d))‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (by positivity))]
      rw [mul_comm]
      exact (le_mul_inv_iff₀ (by positivity : (0 : ℝ) < n + 1)).2 hdist
    dsimp [Ψ]
    rw [radialProfile_eq_zero hscale, mul_zero]
  have hD : ∀ i : ℕ, Continuous fun p : (ℝ × S) × Rd d =>
      iteratedFDeriv ℝ i (Ψ p.1) p.2 := by
    intro i
    have hfull := l2b_continuous_iteratedFDeriv_snd
      (l2b_contDiff_convTrunc_exp_uncurry_seed hd hκ n) i
    have hmap : Continuous (fun p : (ℝ × S) × Rd d =>
        (((p.1.1, (p.1.2 : Rd d)) : ℝ × Rd d), p.2)) := by fun_prop
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using hfull.comp hmap
  have hc := continuous_testFamK K Ψ hs hK hD
  have he : (fun q : ℝ × S => convTrunc κ (Real.exp q.1) (q.2 : Rd d) n) =
      ofSuppRd K ∘ testFamK K Ψ hs hK := by
    funext q
    ext w
    rw [l2b_convTrunc_apply_seed hd hκ]
    rfl
  rw [he]
  exact (ofSuppRd K).continuous.comp hc

/-- Sign-free copy of `HigherDimLQGMetric.l2b_continuous_convTrunc_exp`. -/
theorem l2b_continuous_convTrunc_exp_seed (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (n : ℕ) :
    Continuous fun q : ℝ × Rd d => convTrunc κ (Real.exp q.1) q.2 n := by
  rw [continuous_iff_continuousAt]
  intro q₀
  let z₀ : Rd d := q₀.2
  let S : Set (Rd d) := closedBall z₀ 1
  have hmem (q : ℝ × Rd d) :
      z₀ + l2b_unitProj (q.2 - z₀) ∈ S := by
    change dist (z₀ + l2b_unitProj (q.2 - z₀)) z₀ ≤ 1
    rw [dist_eq_norm, add_sub_cancel_left]
    exact l2b_norm_unitProj_le_one _
  let proj : (ℝ × Rd d) → ℝ × S := fun q =>
    (q.1, ⟨z₀ + l2b_unitProj (q.2 - z₀), hmem q⟩)
  have hproj : Continuous proj := by
    have hzc : Continuous fun q : ℝ × Rd d => z₀ + l2b_unitProj (q.2 - z₀) :=
      continuous_const.add (l2b_continuous_unitProj.comp
        (continuous_snd.sub continuous_const))
    exact continuous_fst.prodMk (hzc.subtype_mk hmem)
  let F : ℝ × Rd d → TestRd d := fun q => convTrunc κ (Real.exp q.1) q.2 n
  let G' : ℝ × Rd d → TestRd d := fun q =>
    convTrunc κ (Real.exp (proj q).1) ((proj q).2 : Rd d) n
  have hG : Continuous G' :=
    (l2b_continuous_convTrunc_exp_on_ball_seed hd hκ n z₀).comp hproj
  have hU : IsOpen {q : ℝ × Rd d | ‖q.2 - z₀‖ < 1} :=
    isOpen_lt (continuous_norm.comp (continuous_snd.sub continuous_const)) continuous_const
  have hq₀ : q₀ ∈ {q : ℝ × Rd d | ‖q.2 - z₀‖ < 1} := by
    change ‖q₀.2 - z₀‖ < 1
    simp [z₀]
  have heq : F =ᶠ[𝓝 q₀] G' := by
    refine Filter.eventuallyEq_iff_exists_mem.2
      ⟨{q : ℝ × Rd d | ‖q.2 - z₀‖ < 1}, hU.mem_nhds hq₀, ?_⟩
    intro q hq
    dsimp [F, G', proj]
    rw [l2b_unitProj_eq_self (le_of_lt hq)]
    simp
  exact hG.continuousAt.congr_of_eventuallyEq heq

end ParamTest

section TruncRadial
/-! Copies from `HigherDimLQGMetric.ConvField.TruncRadial`. -/

open MeasureTheory Set Filter Topology
open HigherDimLFPP (Rd e₁)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Sign-free copy of `HigherDimLQGMetric.l2b_convTrunc_radial_about`. -/
theorem l2b_convTrunc_radial_about_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (ε : ℝ) (z : Rd d) (n : ℕ) :
    ∀ x : Rd d, convTrunc κ ε z n x =
      convTrunc κ ε z n (z + ‖x - z‖ • e₁ d) := by
  intro x
  apply l2b_convTrunc_radial_seed hd hκ ε z n
  rw [add_sub_cancel_left, norm_smul, HigherDimLFPP.norm_e₁ (by omega : 0 < d),
    mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Sign-free copy of `HigherDimLQGMetric.l2b_convTrunc_axis`. -/
theorem l2b_convTrunc_axis_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (ε r : ℝ) (z : Rd d) (n : ℕ) :
    convTrunc κ ε z n (z + r • e₁ d) =
      convKernelEps κ ε (r • e₁ d) *
        radialProfile d (((n : ℝ) + 1)⁻¹ • (r • e₁ d)) := by
  rw [l2b_convTrunc_apply_seed hd hκ]
  simp only [add_sub_cancel_left, sub_add_cancel_left]
  congr 1
  apply l2b_convKernelEps_radial
  simp only [norm_neg]

/-- Sign-free copy of `HigherDimLQGMetric.l2b_ae_convTrunc_radial`. -/
theorem l2b_ae_convTrunc_radial_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    (ε : ℝ) (z : Rd d) (n : ℕ) :
    ∀ᵐ ω ∂P, h ω (convTrunc κ ε z n) =
      ((volume : Measure (Rd d)).toSphere univ).toReal *
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
          (convKernelEps κ ε (r • e₁ d) *
            radialProfile d (((n : ℝ) + 1)⁻¹ • (r • e₁ d))) *
          sphereAvg (h ω) r z := by
  filter_upwards [l2b_ae_radial_pairing hd hh (convTrunc κ ε z n) z
    (l2b_convTrunc_radial_about_seed hd hκ ε z n)] with ω hω
  rw [hω]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [l2b_convTrunc_axis_seed hd hκ]

end TruncRadial

section RadialWeightIntegrable
/-! Copies from `HigherDimLQGMetric.ConvField.RadialWeightIntegrable`. -/

open MeasureTheory Set Metric Filter Topology
open HigherDimLFPP (Rd e₁)
variable {d : ℕ} {κ : Rd d → ℝ}

-- Verbatim host proof; it needs the host's heartbeat budget.
set_option maxHeartbeats 1000000 in
/-- Sign-free copy of `HigherDimLQGMetric.l2b_integrable_radial_growth_kernel`. -/
theorem l2b_integrable_radial_growth_kernel_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) *
      convKernelEps κ ε (r • e₁ d) * l2b_growthWeight r) (Ioi (0 : ℝ)) := by
  let K : ℝ → ℝ := fun r => convKernelEps κ ε (r • e₁ d)
  let f : ℝ → ℝ := fun r => r ^ (d - 1) * K r * l2b_growthWeight r
  have hKc : Continuous K := by
    dsimp [K, convKernelEps]
    exact continuous_const.mul
      ((convKernel_contDiff_seed (by omega) hκ).continuous.comp
        ((continuous_const : Continuous fun _ : ℝ => ε⁻¹).smul
          (continuous_id.smul continuous_const)))
  have hfc : ContinuousOn f (Ioi (0 : ℝ)) :=
    ((continuous_id.pow _).mul hKc).continuousOn.mul l2b_continuousOn_growthWeight
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))) :=
    hfc.aestronglyMeasurable measurableSet_Ioi
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).bddAbove_image
    hKc.abs.continuousOn
  let M : ℝ := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ r ∈ Icc (0 : ℝ) 1, |K r| ≤ M := by
    intro r hr
    exact (hM₀ (mem_image_of_mem _ hr)).trans (le_max_left _ _)
  have hnear : IntegrableOn f (Ioc (0 : ℝ) 1) := by
    have hbound : IntegrableOn (fun _ : ℝ => M * 2) (Ioc (0 : ℝ) 1) :=
      (integrableOn_const isCompact_Icc.measure_ne_top).mono_set Ioc_subset_Icc_self
    apply hbound.mono' ?_ ?_
    · exact hfm.mono_measure (Measure.restrict_mono_set volume
        (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0))
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr => ?_)
      have hr0 : 0 < r := hr.1
      have hw := l2b_polar_log_weight_bounded hd (R := 1) (by norm_num) hr0 hr.2
      have hW0 : 0 ≤ l2b_growthWeight r := by
        exact (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
      have hp0 : 0 ≤ r ^ (d - 1) := pow_nonneg hr0.le _
      have hk := hM r ⟨hr0.le, hr.2⟩
      have hw2 : r ^ (d - 1) * l2b_growthWeight r ≤ 2 := by
        simpa only [l2b_growthWeight, one_pow, Real.log_one, max_eq_right zero_le_one,
          one_mul, one_add_one_eq_two] using hw
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hp0,
        abs_of_nonneg hW0]
      calc r ^ (d - 1) * |K r| * l2b_growthWeight r
          = (r ^ (d - 1) * l2b_growthWeight r) * |K r| := by ring
        _ ≤ 2 * M := mul_le_mul hw2 hk (abs_nonneg _) (by norm_num)
        _ = M * 2 := by ring
  have hplain := l2b_integrable_radial_kernel_seed hd hκ hε
  have hlog := l2b_integrable_radial_logKernel_seed hd hκ hε
  have hfar : IntegrableOn f (Ioi (1 : ℝ)) := by
    have hsource : IntegrableOn (fun r : ℝ =>
        |r ^ (d - 1) * (Real.log (2 + r) * K r)| +
          |r ^ (d - 1) * K r|) (Ioi (1 : ℝ)) :=
      ((hlog.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).norm).add
        ((hplain.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).norm)
    apply hsource.mono' ?_ ?_
    · exact hfm.mono_measure (Measure.restrict_mono_set volume (Ioi_subset_Ioi
        (by norm_num : (0 : ℝ) ≤ 1)))
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r hr => ?_)
      have hr1 : 1 ≤ r := le_of_lt hr
      have hr0 : 0 ≤ r := by linarith
      have hp0 : 0 ≤ r ^ (d - 1) := pow_nonneg hr0 _
      have hW0 : 0 ≤ l2b_growthWeight r := by
        exact (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
      have hlog0 : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
      have hw := l2b_growthWeight_le_log_add_one hr1
      change |r ^ (d - 1) * K r * l2b_growthWeight r| ≤
        |r ^ (d - 1) * (Real.log (2 + r) * K r)| + |r ^ (d - 1) * K r|
      simp only [abs_mul, abs_of_nonneg hp0,
        abs_of_nonneg hW0, abs_of_nonneg hlog0]
      calc r ^ (d - 1) * |K r| * l2b_growthWeight r
          ≤ r ^ (d - 1) * |K r| * (Real.log (2 + r) + 1) := by gcongr
        _ = r ^ (d - 1) * (Real.log (2 + r) * |K r|) +
            r ^ (d - 1) * |K r| := by ring
  have hu : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) := by ext r; simp
  rw [← hu]
  exact hnear.union hfar

end RadialWeightIntegrable

end HigherDimLFPPAS.Signed
