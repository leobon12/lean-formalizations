import HigherDimLQGMetric.Kernel.CovKernelEps
import HigherDimLQGMetric.Field.Bump
import HigherDimLQGMetric.Frozen.ConvTrunc
import HigherDimLQGMetric.Frozen.ConvMollify

/-!
# Elementary facts about the truncated convolution pairing

Packet L2b. The truncation is radial about its evaluation point. These deterministic
facts are used to identify its pairing with a spherical integral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open MeasureTheory Filter Topology

variable {d : ℕ} {κ : Rd d → ℝ}

theorem l2b_convKernelEps_radial (ε : ℝ) {x y : Rd d} (hxy : ‖x‖ = ‖y‖) :
    convKernelEps κ ε x = convKernelEps κ ε y := by
  unfold convKernelEps
  congr 1
  apply convKernel_radial
  simp only [norm_smul, hxy]

theorem l2b_convTrunc_apply (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ε : ℝ) (z : Rd d) (n : ℕ) (w : Rd d) :
    convTrunc κ ε z n w =
      convKernelEps κ ε (z - w) *
        radialProfile d (((n : ℝ) + 1)⁻¹ • (w - z)) := by
  unfold convTrunc
  rw [dite_eq_left (convKernel_contDiff (by omega) hκ)]
  rfl

theorem l2b_convTrunc_radial (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ε : ℝ) (z : Rd d) (n : ℕ) {w v : Rd d}
    (hwv : ‖w - z‖ = ‖v - z‖) :
    convTrunc κ ε z n w = convTrunc κ ε z n v := by
  rw [l2b_convTrunc_apply hd hκ, l2b_convTrunc_apply hd hκ]
  congr 1
  · apply l2b_convKernelEps_radial
    simpa only [norm_sub_rev] using hwv
  · apply radialProfile_eq_of_norm_eq
    simp only [norm_smul, hwv]

theorem l2b_cutoff_eventually_one (z w : Rd d) :
    ∀ᶠ n : ℕ in atTop,
      radialProfile d (((n : ℝ) + 1)⁻¹ • (w - z)) = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖w - z‖
  refine Filter.eventually_atTop.2 ⟨N, fun n hn => radialProfile_eq_one ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < n + 1)),
    ← div_eq_inv_mul]
  apply (div_le_one (by positivity : (0 : ℝ) < n + 1)).2
  have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem l2b_integrable_convTrunc (ε : ℝ) (z : Rd d) (n : ℕ) :
    Integrable (fun w : Rd d => convTrunc κ ε z n w) :=
  integrable_testOn _

theorem l2b_tendsto_integral_convTrunc (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) (z : Rd d) :
    Tendsto (fun n : ℕ => ∫ w : Rd d, convTrunc κ ε z n w)
      atTop (𝓝 (1 : ℝ)) := by
  have hi : Integrable (fun w : Rd d => convKernelEps κ ε (z - w)) :=
    (integrable_convKernelEps hd hκ hε).comp_sub_left z
  have hb : ∀ n, ∀ᵐ w ∂(volume : Measure (Rd d)),
      ‖convTrunc κ ε z n w‖ ≤ |convKernelEps κ ε (z - w)| := by
    intro n
    filter_upwards [] with w
    rw [l2b_convTrunc_apply hd hκ, Real.norm_eq_abs, abs_mul]
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
      rw [l2b_convTrunc_apply hd hκ, hn, mul_one]
    exact tendsto_const_nhds.congr' he.symm
  have ht := tendsto_integral_of_dominated_convergence
    (fun w : Rd d => |convKernelEps κ ε (z - w)|)
    (fun n => (l2b_integrable_convTrunc ε z n).aestronglyMeasurable)
    hi.abs hb hl
  have hmass : ∫ w : Rd d, convKernelEps κ ε (z - w) = 1 := by
    rw [integral_sub_left_eq_self]
    exact integral_convKernelEps_eq_one hd hκ hε
  rwa [hmass] at ht

theorem l2b_convMollify_eq_of_tendsto {ε : ℝ} {g : DistRd d} {z : Rd d} {a : ℝ}
    (ha : Tendsto (fun n : ℕ => g (convTrunc κ ε z n)) atTop (𝓝 a)) :
    convMollify κ ε g z = a := by
  exact ha.limUnder_eq

theorem l2b_convMollify_addConst_of_tendsto (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    {g : DistRd d} {z : Rd d} {a c : ℝ}
    (ha : Tendsto (fun n : ℕ => g (convTrunc κ ε z n)) atTop (𝓝 a)) :
    convMollify κ ε (addConst g c) z = convMollify κ ε g z + c := by
  have hc := (l2b_tendsto_integral_convTrunc hd hκ hε z).const_mul c
  have hs : Tendsto (fun n : ℕ => (addConst g c) (convTrunc κ ε z n)) atTop
      (𝓝 (a + c)) := by
    convert ha.add hc using 1
    · funext n
      exact addConst_apply g c (convTrunc κ ε z n)
    · simp
  rw [l2b_convMollify_eq_of_tendsto hs, l2b_convMollify_eq_of_tendsto ha]

theorem l2b_tendsto_pair_ofCont (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (f : C(Rd d, ℝ)) (M : ℝ) (hM : ∀ w, |f w| ≤ M) (z : Rd d) :
    Tendsto (fun n : ℕ => (ofCont f) (convTrunc κ ε z n)) atTop
      (𝓝 (∫ w : Rd d, convKernelEps κ ε (z - w) * f w)) := by
  have hi : Integrable (fun w : Rd d => convKernelEps κ ε (z - w)) :=
    (integrable_convKernelEps hd hκ hε).comp_sub_left z
  have hb : ∀ n, ∀ᵐ w ∂(volume : Measure (Rd d)),
      ‖convTrunc κ ε z n w * f w‖ ≤ |convKernelEps κ ε (z - w)| * M := by
    intro n
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul
      (by
        rw [l2b_convTrunc_apply hd hκ, abs_mul]
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
      rw [l2b_convTrunc_apply hd hκ, hn, mul_one]
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

theorem l2b_convMollify_ofCont (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (f : C(Rd d, ℝ)) (M : ℝ) (hM : ∀ w, |f w| ≤ M) (z : Rd d) :
    convMollify κ ε (ofCont f) z =
      ∫ w : Rd d, convKernelEps κ ε (z - w) * f w :=
  l2b_convMollify_eq_of_tendsto (l2b_tendsto_pair_ofCont hd hκ hε f M hM z)

theorem l2b_convMollify_addFun_of_tendsto (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    {g : DistRd d} {z : Rd d} {a : ℝ}
    (ha : Tendsto (fun n : ℕ => g (convTrunc κ ε z n)) atTop (𝓝 a))
    (f : C(Rd d, ℝ)) (M : ℝ) (hM : ∀ w, |f w| ≤ M) :
    convMollify κ ε (addFun g f) z = convMollify κ ε g z +
      ∫ w : Rd d, convKernelEps κ ε (z - w) * f w := by
  have hf := l2b_tendsto_pair_ofCont hd hκ hε f M hM z
  have hs : Tendsto
      (fun n : ℕ => (addFun g f) (convTrunc κ ε z n)) atTop
      (𝓝 (a + ∫ w : Rd d, convKernelEps κ ε (z - w) * f w)) := by
    convert ha.add hf using 1
    funext n
    simp [addFun]
  rw [l2b_convMollify_eq_of_tendsto hs, l2b_convMollify_eq_of_tendsto ha]

end HigherDimLQGMetric
