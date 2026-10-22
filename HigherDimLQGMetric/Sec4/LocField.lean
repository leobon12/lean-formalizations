import HigherDimLQGMetric.B3.Interfaces
import HigherDimLQGMetric.Kernel.ConvKernelMain
import HigherDimLQGMetric.ConvField.Basic
import HigherDimLQGMetric.Field.Bump
import HigherDimLQGMetric.Field.Affine
import HigherDimLQGMetric.Field.Measurable

/-!
# The localized convolution field `ĥ*_ε` of [1] (4.1) (packet L9b)

[1] (4.1): `ĥ*_ε(z) = Z_ε⁻¹ ∫ h(w) Ψ̂_ε(z - w) K_ε(z - w) dw`, where `Ψ̂_ε` is a radial bump equal to `1` on
`B_{s/2}` and `0` off `B_s`, `s = s(ε) = ε (log ε⁻¹)^{10}`, and `Z_ε = ∫ Ψ̂_ε K_ε`. Here the integral is the
genuine pairing of the distribution `h` with the test function `w ↦ Ψ̂_ε(z - w) K_ε(z - w)` (`locTest`), the
radial bump is the B3 interface's `radBump (s/2) s`, and `Z_ε = locMass κ ε s`.

Basic API: the test function is radial about `z` and supported in `B̄_s(z)`, its integral is `Z_ε`, the field is
continuous in `z` for **every** distribution, shifts by `c` when `c` is added to `h` (if `Z_ε ≠ 0`), is
translation covariant (deterministically), and is a measurable function of `h`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-- the truncation radius `s(ε) = ε (log ε⁻¹)^{10}` of [1] (4.1) -/
def locRad (ε : ℝ) : ℝ := ε * (Real.log ε⁻¹) ^ 10

/-- the truncated kernel `v ↦ K_ε(v) Ψ̂(v)`, `Ψ̂ = ψ_{s/2, s}` -/
def locKer (κ : Rd d → ℝ) (ε s : ℝ) (v : Rd d) : ℝ :=
  convKernelEps κ ε v * radBump (s / 2) s v

theorem locKer_radial (κ : Rd d → ℝ) (ε s : ℝ) {v w : Rd d} (h : ‖v‖ = ‖w‖) :
    locKer κ ε s v = locKer κ ε s w := by
  unfold locKer
  rw [l2b_convKernelEps_radial ε h, radBump_radial _ _ h]

theorem locKer_neg (κ : Rd d → ℝ) (ε s : ℝ) (v : Rd d) : locKer κ ε s (-v) = locKer κ ε s v :=
  locKer_radial κ ε s (norm_neg v)

theorem contDiff_locKer {κ : Rd d → ℝ} (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    (ε : ℝ) {s : ℝ} (hs : 0 < s) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (locKer κ ε s) := by
  refine ContDiff.mul ?_ (contDiff_radBump (by positivity) (by linarith))
  unfold convKernelEps
  exact contDiff_const.mul (hK.comp (contDiff_id.const_smul _))

theorem locKer_eq_zero (κ : Rd d → ℝ) (ε : ℝ) {s : ℝ} (hs : 0 < s) {v : Rd d} (hv : s ≤ ‖v‖) :
    locKer κ ε s v = 0 := by
  have hb : 1 < s / (s / 2) := by rw [div_div_eq_mul_div]; field_simp; norm_num
  have hba : 0 < s / (s / 2) - 1 := by linarith
  have hx' : s / (s / 2) ≤ ‖(s / 2)⁻¹ • v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < s / 2),
      inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hv (by positivity)
  unfold locKer radBump
  rw [show (ContDiffBumpBase.ofInnerProductSpace (Rd d)).toFun (s / (s / 2)) ((s / 2)⁻¹ • v) = 0
    from Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hba.le),
    mul_zero]

theorem locKer_eq_convKernelEps (κ : Rd d → ℝ) (ε : ℝ) {s : ℝ} (hs : 0 < s) {v : Rd d}
    (hv : ‖v‖ ≤ s / 2) : locKer κ ε s v = convKernelEps κ ε v := by
  have hs2 : (0 : ℝ) < s / 2 := by positivity
  have hb : 1 < s / (s / 2) := by rw [div_div_eq_mul_div]; field_simp; norm_num
  unfold locKer radBump
  rw [(ContDiffBumpBase.ofInnerProductSpace (Rd d)).eq_one _ hb, mul_one]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs2]
  exact (inv_mul_le_iff₀ hs2).2 (by simpa using hv)

theorem radBump_mem_Icc' (a b : ℝ) (x : Rd d) : radBump a b x ∈ Icc (0 : ℝ) 1 :=
  (ContDiffBumpBase.ofInnerProductSpace (Rd d)).mem_Icc _ _

theorem hasCompactSupport_locKer (κ : Rd d → ℝ) (ε : ℝ) {s : ℝ} (hs : 0 < s) :
    HasCompactSupport (locKer κ ε s) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Rd d) s) fun v hv => ?_
  rw [mem_closedBall, dist_zero_right, not_le] at hv
  exact locKer_eq_zero κ ε hs hv.le

theorem continuous_locKer {κ : Rd d → ℝ} (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    (ε : ℝ) {s : ℝ} (hs : 0 < s) : Continuous (locKer κ ε s) :=
  (contDiff_locKer hK ε hs).continuous

open Classical in
/-- `w ↦ Ψ̂(x - w) K_ε(x - w)` as a test function (junk `0` unless `K` is smooth and `s > 0`) -/
def locTest (κ : Rd d → ℝ) (ε s : ℝ) (x : Rd d) : TestRd d :=
  if hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ) ∧ 0 < s then
    { toFun := fun w => locKer κ ε s (w - x)
      contDiff' := (contDiff_locKer hK.1 ε hK.2).comp (contDiff_id.sub contDiff_const)
      hasCompactSupport' := (hasCompactSupport_locKer κ ε hK.2).comp_homeomorph
        (Homeomorph.subRight x)
      tsupport_subset' := subset_univ _ }
  else 0

/-- `Z_ε = ∫ Ψ̂ K_ε` -/
def locMass (κ : Rd d → ℝ) (ε s : ℝ) : ℝ := ∫ v, locKer κ ε s v

/-- **The localized field** `ĥ*_ε(x) = Z_ε⁻¹ ⟨h, Ψ̂_ε K_ε(x - ·)⟩` of [1] (4.1), `s = locRad ε` -/
def locField (κ : Rd d → ℝ) (ε : ℝ) (h : DistRd d) (x : Rd d) : ℝ :=
  (locMass κ ε (locRad ε))⁻¹ * h (locTest κ ε (locRad ε) x)

section API

variable {κ : Rd d → ℝ} {ε s : ℝ}

theorem locTest_apply (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)) (hs : 0 < s)
    (x w : Rd d) : locTest κ ε s x w = locKer κ ε s (w - x) := by
  unfold locTest
  rw [dite_eq_left (And.intro hK hs)]
  rfl

theorem locTest_apply' (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)) (hs : 0 < s)
    (x w : Rd d) : locTest κ ε s x w = locKer κ ε s (x - w) := by
  rw [locTest_apply hK hs, ← locKer_neg, neg_sub]

theorem tsupport_locTest_subset (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    (hs : 0 < s) (x : Rd d) : tsupport (locTest κ ε s x : Rd d → ℝ) ⊆ closedBall x s := by
  refine closure_minimal (fun w hw => ?_) isClosed_closedBall
  rw [mem_closedBall, dist_eq_norm]
  by_contra hlt
  push Not at hlt
  exact hw (by rw [locTest_apply hK hs]; exact locKer_eq_zero κ ε hs hlt.le)

theorem integral_locTest (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)) (hs : 0 < s)
    (x : Rd d) : ∫ w, locTest κ ε s x w = locMass κ ε s := by
  simp_rw [locTest_apply hK hs]
  exact integral_sub_right_eq_self (fun v => locKer κ ε s v) x

/-- the test function is radial about its centre (the hypothesis of `l2b_ae_radial_pairing`) -/
theorem locTest_radial (hd : 0 < d) (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    (hs : 0 < s) (x w : Rd d) :
    locTest κ ε s x w = locTest κ ε s x (x + ‖w - x‖ • e₁ d) := by
  rw [locTest_apply hK hs, locTest_apply hK hs, add_sub_cancel_left]
  apply locKer_radial
  rw [norm_smul, HigherDimLFPP.norm_e₁ hd, mul_one, Real.norm_eq_abs, abs_norm]

theorem locTest_axis (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)) (hs : 0 < s)
    (x : Rd d) (r : ℝ) : locTest κ ε s x (x + r • e₁ d) = locKer κ ε s (r • e₁ d) := by
  rw [locTest_apply hK hs, add_sub_cancel_left]

/-- `x ↦ locTest x` is continuous into `𝓓(ℝ^d)`. -/
theorem continuous_locTest (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    (hs : 0 < s) : Continuous (locTest (d := d) κ ε s) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  let S := closedBall x₀ 1
  have : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let K : TopologicalSpace.Compacts (Rd d) := ⟨closedBall 0 (‖x₀‖ + 1 + s), isCompact_closedBall _ _⟩
  let g := locKer κ ε s
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := contDiff_locKer hK ε hs
  have hsm : ∀ x : S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y => g (y + -(x : Rd d)) :=
    fun x => hg.comp (contDiff_id.add contDiff_const)
  have hKs : ∀ x : S, ∀ y ∉ (K : Set (Rd d)), g (y + -(x : Rd d)) = 0 := by
    intro x y hy
    apply locKer_eq_zero κ ε hs
    have hx : ‖(x : Rd d) - x₀‖ ≤ 1 := by rw [← dist_eq_norm]; exact mem_closedBall.1 x.2
    have hy' : ‖x₀‖ + 1 + s < ‖y‖ := by simpa [K] using hy
    have h1 : ‖y‖ ≤ ‖y + -(x : Rd d)‖ + ‖(x : Rd d) - x₀‖ + ‖x₀‖ := by
      calc ‖y‖ = ‖(y + -(x : Rd d)) + ((x : Rd d) - x₀) + x₀‖ := by
            congr 1; abel
        _ ≤ _ := norm_add₃_le
    linarith
  have hD : ∀ i : ℕ, Continuous fun p : S × Rd d =>
      iteratedFDeriv ℝ i (fun y => g (y + -(p.1 : Rd d))) p.2 := by
    intro i
    simp_rw [iteratedFDeriv_comp_add_right]
    exact (hg.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      (continuous_snd.add (continuous_subtype_val.comp continuous_fst).neg)
  have hc := continuous_testFamK K (fun (x : S) y => g (y + -(x : Rd d))) hsm hKs hD
  have e : (fun x : S => locTest κ ε s (x : Rd d)) = ofSuppRd K ∘ testFamK K _ hsm hKs := by
    funext x
    refine TestFunction.ext fun y => ?_
    show locTest κ ε s (x : Rd d) y = g (y + -(x : Rd d))
    rw [locTest_apply hK hs, sub_eq_add_neg]
  have h2 : Continuous fun x : S => locTest κ ε s (x : Rd d) := by
    rw [e]; exact (ofSuppRd K).continuous.comp hc
  exact (continuousOn_iff_continuous_domRestrict.2 h2).continuousAt
    (closedBall_mem_nhds _ one_pos)

/-- `x ↦ ⟨h, locTest x⟩` is continuous for every distribution `h`. -/
theorem continuous_apply_locTest (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    (hs : 0 < s) (h : DistRd d) : Continuous fun x : Rd d => h (locTest κ ε s x) :=
  (map_continuous h).comp (continuous_locTest hK hs)

/-- translation: `locTest x (· - u) = locTest (x + u)` -/
theorem testAffinePull_one_locTest (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    (hs : 0 < s) (u x : Rd d) :
    testAffinePull 1 u (locTest κ ε s x) = locTest κ ε s (x + u) := by
  refine TestFunction.ext fun w => ?_
  rw [testAffinePull_one_apply, locTest_apply hK hs, locTest_apply hK hs]
  congr 1
  abel

end API

section Field

variable {κ : Rd d → ℝ} {ε : ℝ}

theorem continuous_locField (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    (hs : 0 < locRad ε) (h : DistRd d) : Continuous (locField κ ε h) :=
  continuous_const.mul (continuous_apply_locTest hK hs h)

/-- **Constant shifts**: `ĥ*_ε` of `h + c` is `ĥ*_ε + c` (the localized kernel has mass `Z_ε`). -/
theorem locField_addConst (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    (hs : 0 < locRad ε) (hZ : locMass κ ε (locRad ε) ≠ 0) (h : DistRd d) (c : ℝ) (x : Rd d) :
    locField κ ε (addConst h c) x = locField κ ε h x + c := by
  unfold locField
  rw [addConst_apply, integral_locTest hK hs, mul_add]
  field_simp

/-- **Translation covariance** (deterministic): `ĥ*_ε(h(· + u))(x) = ĥ*_ε(h)(x + u)`. -/
theorem locField_affineComp_one (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    (hs : 0 < locRad ε) (h : DistRd d) (u x : Rd d) :
    locField κ ε (affineComp 1 u h) x = locField κ ε h (x + u) := by
  unfold locField
  rw [affineComp_one_apply, testAffinePull_one_locTest hK hs]

/-- measurability in the field -/
theorem measurable_locField_apply (κ : Rd d → ℝ) (ε : ℝ) (x : Rd d) :
    Measurable fun h : DistRd d => locField κ ε h x :=
  measurable_const.mul (measurable_distOn_apply _)

end Field

end HigherDimLQGMetric
