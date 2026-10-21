import SmallGammaGeodesics.Lower.MobiusLawBase
import SmallGammaGeodesics.Core.TestFun
import LQGMetric.Field.GFFInvariance
import LQGMetric.Field.KilledHeatLaw
import QuantumZipper.Proofs.GFF.K3.Conformal
import QuantumZipper.Proofs.GFF.K3.Polar
import QuantumZipper.Proofs.Analysis.Pushforward
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Local Möbius invariance of the whole-plane GFF modulo constants (source §7, packet P-L2 T1)

Source: `source/small-parameter-lqg-geodesics.pdf`, §7 ("local equality of the Gaussian laws"),
corrected in planning audit GA4 (`planning/audits/GA4-sections-7-8.md`), "Details for later use",
item **A3** (and §2.4, finding GA4-4: work modulo additive constants, no circle average).

Let `|θ| ≤ 1/10`, `ψ_θ = mobPhi (-θ)`, `φ_θ = mobPhi θ = ψ_θ⁻¹`, and `W ⊆ B₅(0)`; the poles of
`φ_θ`, `ψ_θ` have modulus `≥ 10`. For `f` supported in `W` the **conformal transport** is
`T f = (f ∘ φ_θ) |φ_θ′|²` on `ψ_θ(W)` and `0` elsewhere (`mobTransportFun`), so that
`⟨h, T f⟩ = ⟨h ∘ ψ_θ, f⟩` formally. Results:

* `integral_mobTransportFun_mul`: the change of variables `∫ (T f) G = ∫ f (G ∘ ψ_θ)` for every `G`;
* `mobTransport`: `T f` is a test function (`LQGMetric.TestC`) when `f` is; `integral_mobTransport`:
  `∫ T f = ∫ f`; `mobTransport0`: `T` maps `TestC0On W` (mean-zero test functions supported in `W`)
  to mean-zero test functions;
* `logCov_mobTransportFun_eq`: `logCov (T f) (T g) = logCov f g` for mean-zero `f, g` (the Möbius
  identity `−log|ψz − ψw| = −log|z − w| + log|D(z)| + log|D(w)|`, whose last two terms integrate to
  zero against mean-zero functions);
* `map_mobTransport0_eq` (**the law statement**): for a whole-plane GFF `h`, the processes
  `ψ ↦ ⟨h, T ψ⟩` and `ψ ↦ ⟨h, ψ⟩`, indexed by `TestC0On W`, have the same law on the product
  space; `map_mobTransport0_add_eq`: the same after adding a deterministic function of the index
  (e.g. `ψ ↦ ∫ ψ g`, the shift by a deterministic test function `g`).

The open-ness of `W` is not needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace SmallGammaGeodesics

open LQGMetric

/-- **The conformal transport** by `ψ_θ = mobPhi (-θ)` (GA4 A3): `T f = (f ∘ φ_θ) |φ_θ′|²` on
`ψ_θ(W)` and `0` elsewhere, so that `⟨h, T f⟩` is the pairing of `h ∘ ψ_θ` with `f`. -/
def mobTransportFun (θ : ℝ) (W : Set ℂ) (f : ℂ → ℝ) : ℂ → ℝ :=
  (mobPhi (-θ) '' W).indicator fun x => f (mobPhi θ x) * ‖deriv (mobPhi θ) x‖ ^ 2

section Transport

variable {θ : ℝ} {W : Set ℂ} {f : ℂ → ℝ}

/-- `|ψ_θ′(z)|² (T f)(ψ_θ z) = f(z)` on `B₅(0)`. -/
theorem mobTransportFun_apply_mobPhi_neg (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5)
    (hf : tsupport f ⊆ W) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 5) :
    ‖deriv (mobPhi (-θ)) z‖ ^ 2 * mobTransportFun θ W f (mobPhi (-θ) z) = f z := by
  by_cases hzW : z ∈ W
  · rw [mobTransportFun, Set.indicator_of_mem (Set.mem_image_of_mem _ hzW),
      mobPhi_mobPhi_neg (mobDen_neg_ne_zero_of_mem_ball hθ hz)]
    have h1 := norm_deriv_mobPhi_mobPhi_neg (θ := θ) (mobDen_neg_ne_zero_of_mem_ball hθ hz)
    calc ‖deriv (mobPhi (-θ)) z‖ ^ 2 * (f z * ‖deriv (mobPhi θ) (mobPhi (-θ) z)‖ ^ 2)
        = f z * (‖deriv (mobPhi θ) (mobPhi (-θ) z)‖ * ‖deriv (mobPhi (-θ)) z‖) ^ 2 := by ring
      _ = f z := by rw [h1, one_pow, mul_one]
  · have hfz : f z = 0 := image_eq_zero_of_notMem_tsupport fun h => hzW (hf h)
    have hnot : mobPhi (-θ) z ∉ mobPhi (-θ) '' W := by
      rintro ⟨w, hw, hwz⟩
      exact hzW ((injOn_mobPhi_neg_ball hθ (hW hw) hz hwz) ▸ hw)
    rw [mobTransportFun, Set.indicator_of_notMem hnot, mul_zero, hfz]

/-- Off the pole of `φ_θ`, `T f` is given by its formula (the indicator is invisible). -/
theorem mobTransportFun_eq (hf : tsupport f ⊆ W) {x : ℂ}
    (hx : 1 + (Complex.exp (θ * Complex.I) - 1) * x ≠ 0) :
    mobTransportFun θ W f x = f (mobPhi θ x) * ‖deriv (mobPhi θ) x‖ ^ 2 := by
  by_cases hxW : x ∈ mobPhi (-θ) '' W
  · rw [mobTransportFun, Set.indicator_of_mem hxW]
  · rw [mobTransportFun, Set.indicator_of_notMem hxW]
    have : f (mobPhi θ x) = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hxW ⟨mobPhi θ x, hf h, mobPhi_neg_mobPhi hx⟩
    rw [this, zero_mul]

/-- `T f` vanishes off `ψ_θ(tsupport f)`. -/
theorem mobTransportFun_eq_zero (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5) {x : ℂ}
    (hx : x ∉ mobPhi (-θ) '' tsupport f) : mobTransportFun θ W f x = 0 := by
  by_cases hxW : x ∈ mobPhi (-θ) '' W
  · obtain ⟨w, hw, rfl⟩ := hxW
    rw [mobTransportFun, Set.indicator_of_mem (Set.mem_image_of_mem _ hw),
      mobPhi_mobPhi_neg (mobDen_neg_ne_zero_of_mem_ball hθ (hW hw))]
    have : f w = 0 := image_eq_zero_of_notMem_tsupport fun h => hx ⟨w, h, rfl⟩
    rw [this, zero_mul]
  · rw [mobTransportFun, Set.indicator_of_notMem hxW]

/-- `ψ_θ(tsupport f)` is compact. -/
theorem isCompact_image_tsupport (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5)
    (hfc : HasCompactSupport f) (hf : tsupport f ⊆ W) :
    IsCompact (mobPhi (-θ) '' tsupport f) :=
  hfc.isCompact.image_of_continuousOn fun _ hz =>
    (differentiableAt_mobPhi_neg hθ (hW (hf hz))).continuousAt.continuousWithinAt

/-- `ψ_θ(tsupport f)` avoids the pole of `φ_θ`. -/
theorem image_tsupport_subset_mobDen_ne (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5)
    (hf : tsupport f ⊆ W) :
    mobPhi (-θ) '' tsupport f ⊆ {x | 1 + (Complex.exp (θ * Complex.I) - 1) * x ≠ 0} := by
  rintro _ ⟨z, hz, rfl⟩
  exact mobDen_mobPhi_neg_ne_zero (mobDen_neg_ne_zero_of_mem_ball hθ (hW (hf hz)))

/-- `T f` has compact support, inside `ψ_θ(tsupport f)`. -/
theorem hasCompactSupport_mobTransportFun (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5)
    (hfc : HasCompactSupport f) (hf : tsupport f ⊆ W) :
    HasCompactSupport (mobTransportFun θ W f) :=
  HasCompactSupport.intro (isCompact_image_tsupport hθ hW hfc hf) fun _ hx =>
    mobTransportFun_eq_zero hθ hW hx

theorem tsupport_mobTransportFun_subset (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5)
    (hfc : HasCompactSupport f) (hf : tsupport f ⊆ W) :
    tsupport (mobTransportFun θ W f) ⊆ mobPhi (-θ) '' tsupport f :=
  closure_minimal (fun _ hx => by_contra fun h => hx (mobTransportFun_eq_zero hθ hW h))
    (isCompact_image_tsupport hθ hW hfc hf).isClosed

/-- `T f` is smooth when `f` is a smooth function with compact support in `W`. -/
theorem contDiff_mobTransportFun (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5)
    (hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f)
    (hf : tsupport f ⊆ W) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mobTransportFun θ W f) := by
  set O : Set ℂ := {x | 1 + (Complex.exp (θ * Complex.I) - 1) * x ≠ 0}
  have hOo : IsOpen O := isOpen_ne_fun (by fun_prop) continuous_const
  have hdiff : DifferentiableOn ℂ (mobPhi θ) O := fun x hx =>
    (hasDerivAt_mobPhi hx).differentiableAt.differentiableWithinAt
  have hφ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mobPhi θ) O :=
    (hdiff.contDiffOn hOo).restrict_scalars ℝ
  have hφ' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (mobPhi θ)) O :=
    ((hdiff.deriv hOo).contDiffOn hOo).restrict_scalars ℝ
  have hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => f (mobPhi θ x) * ‖deriv (mobPhi θ) x‖ ^ 2) O :=
    (hfd.comp_contDiffOn hφ).mul ((contDiff_norm_sq ℝ).comp_contDiffOn hφ')
  refine QuantumZipper.K3.contDiff_of_contDiffOn_of_support_subset hOo
    (isCompact_image_tsupport hθ hW hfc hf) (image_tsupport_subset_mobDen_ne hθ hW hf) ?_
    fun x hx => mobTransportFun_eq_zero hθ hW hx
  exact hF.congr fun x hx => mobTransportFun_eq hf hx

/-- **Change of variables** `x = ψ_θ(z)`: `∫ (T f)(x) G(x) dx = ∫ f(z) G(ψ_θ z) dz` for every `G`
(no integrability needed: both sides are Bochner integrals of the same function after the
injective `C¹` substitution, whose Jacobian is `|ψ_θ′|²`). -/
theorem integral_mobTransportFun_mul (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5)
    (hf : tsupport f ⊆ W) (G : ℂ → ℝ) :
    ∫ x, mobTransportFun θ W f x * G x = ∫ z, f z * G (mobPhi (-θ) z) := by
  have hB : MeasurableSet (Metric.ball (0 : ℂ) 5) := measurableSet_ball
  have h1 : ∫ x, mobTransportFun θ W f x * G x =
      ∫ x in mobPhi (-θ) '' Metric.ball (0 : ℂ) 5, mobTransportFun θ W f x * G x := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    have : x ∉ mobPhi (-θ) '' W := fun h => hx (Set.image_mono hW h)
    rw [mobTransportFun, Set.indicator_of_notMem this, zero_mul]
  have hderiv : ∀ z ∈ Metric.ball (0 : ℂ) 5, HasFDerivWithinAt (mobPhi (-θ))
      (fderiv ℝ (mobPhi (-θ)) z) (Metric.ball (0 : ℂ) 5) z := fun z hz =>
    ((differentiableAt_mobPhi_neg hθ hz).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  rw [h1, integral_image_eq_integral_abs_det_fderiv_smul volume hB hderiv
    (injOn_mobPhi_neg_ball hθ)]
  have h3 : ∫ z in Metric.ball (0 : ℂ) 5, |(fderiv ℝ (mobPhi (-θ)) z).det| •
      (mobTransportFun θ W f (mobPhi (-θ) z) * G (mobPhi (-θ) z)) =
      ∫ z in Metric.ball (0 : ℂ) 5, f z * G (mobPhi (-θ) z) := by
    refine setIntegral_congr_fun hB fun z hz => ?_
    rw [QuantumZipper.abs_det_fderiv_eq_normSq (differentiableAt_mobPhi_neg hθ hz), smul_eq_mul,
      ← mul_assoc, mobTransportFun_apply_mobPhi_neg hθ hW hf hz]
  rw [h3]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
  rw [image_eq_zero_of_notMem_tsupport fun h => hz (hW (hf h)), zero_mul]

/-- `∫ T f = ∫ f`. -/
theorem integral_mobTransportFun (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5)
    (hf : tsupport f ⊆ W) : ∫ x, mobTransportFun θ W f x = ∫ z, f z := by
  have h := integral_mobTransportFun_mul hθ hW hf (fun _ => 1)
  simpa only [mul_one] using h

/-- The covariance of the transported functions, after the change of variables in both
variables: `logCov (T f) (T g) = ∫∫ f(z) g(w) (−log|ψ_θ z − ψ_θ w|)`. -/
theorem logCov_mobTransportFun (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5)
    {g : ℂ → ℝ} (hf : tsupport f ⊆ W) (hg : tsupport g ⊆ W) :
    logCov (mobTransportFun θ W f) (mobTransportFun θ W g) =
      ∫ z, f z * ∫ w, g w * -Real.log ‖mobPhi (-θ) z - mobPhi (-θ) w‖ := by
  unfold logCov
  have hin : ∀ x, ∫ y, mobTransportFun θ W f x * -Real.log ‖x - y‖ * mobTransportFun θ W g y =
      mobTransportFun θ W f x * ∫ w, g w * -Real.log ‖x - mobPhi (-θ) w‖ := by
    intro x
    have h := integral_mobTransportFun_mul hθ hW hg (fun y => -Real.log ‖x - y‖)
    rw [← h, ← integral_const_mul]
    congr 1
    funext y
    ring
  simp_rw [hin]
  exact integral_mobTransportFun_mul hθ hW hf
    (fun x => ∫ w, g w * -Real.log ‖x - mobPhi (-θ) w‖)

/-- `w ↦ g(w) log|D_{−θ}(w)|` is integrable for continuous `g` with compact support in `W`. -/
theorem integrable_mul_log_mobDen (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5) {g : ℂ → ℝ}
    (hgc : Continuous g) (hgs : HasCompactSupport g) (hg : tsupport g ⊆ W) :
    Integrable fun w => g w * Real.log ‖1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * w‖ := by
  have hcont : ContinuousOn
      (fun w => g w * Real.log ‖1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * w‖)
      (Metric.ball (0 : ℂ) 5) := by
    refine hgc.continuousOn.mul (ContinuousOn.log (by fun_prop) fun w hw => ?_)
    exact norm_ne_zero_iff.2 (mobDen_neg_ne_zero_of_mem_ball hθ hw)
  refine Continuous.integrable_of_hasCompactSupport
    (hcont.continuous_of_tsupport_subset Metric.isOpen_ball
      ((tsupport_mul_subset_left).trans (hg.trans hW))) ?_
  exact hgs.mul_right

/-- **Möbius invariance of the covariance on mean-zero functions** (GA4 A3, steps 3–4):
`logCov (T f) (T g) = logCov f g` for continuous mean-zero `f, g` with compact supports in `W`. -/
theorem logCov_mobTransportFun_eq (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5) {g : ℂ → ℝ}
    (hfc : Continuous f) (hfs : HasCompactSupport f) (hf : tsupport f ⊆ W) (hf0 : ∫ z, f z = 0)
    (hgc : Continuous g) (hgs : HasCompactSupport g) (hg : tsupport g ⊆ W) (hg0 : ∫ w, g w = 0) :
    logCov (mobTransportFun θ W f) (mobTransportFun θ W g) = logCov f g := by
  rw [logCov_mobTransportFun hθ hW hf hg]
  set L : ℂ → ℝ := fun w => Real.log ‖1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * w‖
    with hL
  set K : ℝ := ∫ w, g w * L w
  have hgi : Integrable g := hgc.integrable_of_hasCompactSupport hgs
  have hfi : Integrable f := hfc.integrable_of_hasCompactSupport hfs
  have hinner : ∀ z ∈ Metric.ball (0 : ℂ) 5,
      ∫ w, g w * -Real.log ‖mobPhi (-θ) z - mobPhi (-θ) w‖ =
        (∫ w, g w * -Real.log ‖z - w‖) + K := by
    intro z hz
    have hDz := mobDen_neg_ne_zero_of_mem_ball hθ hz
    have hpt : (fun w => g w * -Real.log ‖mobPhi (-θ) z - mobPhi (-θ) w‖) =ᵐ[volume]
        fun w => g w * -Real.log ‖z - w‖ + (g w * L z + g w * L w) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1
        ((Set.countable_singleton z).measure_zero volume)] with w hw
      by_cases hwB : w ∈ Metric.ball (0 : ℂ) 5
      · have hDw := mobDen_neg_ne_zero_of_mem_ball hθ hwB
        have hzw : ‖z - w‖ ≠ 0 := by
          rw [norm_ne_zero_iff, sub_ne_zero]
          exact fun h => hw (h ▸ rfl)
        rw [norm_mobPhi_sub_mobPhi hDz hDw, Real.log_div hzw
          (mul_ne_zero (norm_ne_zero_iff.2 hDz) (norm_ne_zero_iff.2 hDw)),
          Real.log_mul (norm_ne_zero_iff.2 hDz) (norm_ne_zero_iff.2 hDw)]
        simp only [hL]
        ring
      · have hgw : g w = 0 := image_eq_zero_of_notMem_tsupport fun h => hwB (hW (hg h))
        rw [hgw]
        ring
    have hI1 : Integrable fun w => g w * -Real.log ‖z - w‖ := by
      refine (QuantumZipper.K3.integrable_log_norm_sub_mul_K3 hgc hgs z).neg.congr
        (Filter.Eventually.of_forall fun w => ?_)
      simp only [Pi.neg_apply]
      rw [norm_sub_rev]
      ring
    have hI2 : Integrable fun w => g w * L z := hgi.mul_const _
    have hI3 : Integrable fun w => g w * L w := integrable_mul_log_mobDen hθ hW hgc hgs hg
    have hI23 : Integrable fun w => g w * L z + g w * L w := hI2.add hI3
    rw [integral_congr_ae hpt, integral_add hI1 hI23, integral_add hI2 hI3,
      integral_mul_const, hg0, zero_mul, zero_add]
  have houter : (fun z => f z * ∫ w, g w * -Real.log ‖mobPhi (-θ) z - mobPhi (-θ) w‖) =
      fun z => f z * K + f z * ∫ w, g w * -Real.log ‖z - w‖ := by
    funext z
    by_cases hz : z ∈ Metric.ball (0 : ℂ) 5
    · rw [hinner z hz]
      ring
    · have : f z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hW (hf h))
      rw [this]
      ring
  rw [houter, GFFInv.integral_add_of_left (hfi.mul_const K)
    (by rw [integral_mul_const, hf0, zero_mul])]
  unfold logCov
  congr 1
  funext z
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

end Transport

/-! ### The transport on test functions -/

section TestFunctions

variable {θ : ℝ} {W : Set ℂ}

/-- **The conformal transport of a test function** supported in `W` (GA4 A3, claim 1): for
`|θ| ≤ 1/10` and `W ⊆ B₅(0)`, `T f = (f ∘ φ_θ) |φ_θ′|²` on `ψ_θ(W)`, `0` elsewhere, is a test
function. -/
def mobTransport (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5) (f : TestC)
    (hf : tsupport (f : ℂ → ℝ) ⊆ W) : TestC where
  toFun := mobTransportFun θ W f
  contDiff' := contDiff_mobTransportFun hθ hW f.contDiff f.hasCompactSupport hf
  hasCompactSupport' := hasCompactSupport_mobTransportFun hθ hW f.hasCompactSupport hf
  tsupport_subset' := Set.subset_univ _

theorem coe_mobTransport (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5) (f : TestC)
    (hf : tsupport (f : ℂ → ℝ) ⊆ W) : ⇑(mobTransport hθ hW f hf) = mobTransportFun θ W f :=
  rfl

theorem mobTransport_apply (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5) (f : TestC)
    (hf : tsupport (f : ℂ → ℝ) ⊆ W) (x : ℂ) :
    mobTransport hθ hW f hf x = mobTransportFun θ W f x :=
  rfl

/-- `∫ T f = ∫ f` (GA4 A3, claim 1). -/
theorem integral_mobTransport (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5) (f : TestC)
    (hf : tsupport (f : ℂ → ℝ) ⊆ W) : ∫ x, mobTransport hθ hW f hf x = ∫ x, f x :=
  integral_mobTransportFun hθ hW hf

/-- `T` maps mean-zero test functions supported in `W` to mean-zero test functions. -/
def mobTransport0 (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5) (ψ : TestC0On W) : TestC0 :=
  ⟨mobTransport hθ hW ψ.1.1 ψ.2, by rw [integral_mobTransport, ψ.1.2]⟩

theorem mobTransport0_coe (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5) (ψ : TestC0On W) :
    (mobTransport0 hθ hW ψ).1 = mobTransport hθ hW ψ.1.1 ψ.2 :=
  rfl

/-- `logCov (T φ) (T ψ) = logCov φ ψ` on `TestC0On W`. -/
theorem logCov_mobTransport0 (hθ : |θ| ≤ 1 / 10) (hW : W ⊆ Metric.ball 0 5)
    (φ ψ : TestC0On W) :
    logCov (mobTransport0 hθ hW φ).1 (mobTransport0 hθ hW ψ).1 = logCov φ.1.1 ψ.1.1 :=
  logCov_mobTransportFun_eq hθ hW φ.1.1.continuous φ.1.1.hasCompactSupport φ.2 φ.1.2
    ψ.1.1.continuous ψ.1.1.hasCompactSupport ψ.2 ψ.1.2

end TestFunctions

/-! ### The law statement -/

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC} {θ : ℝ} {W : Set ℂ}

/-- **Local Möbius invariance of the whole-plane GFF modulo constants** (GA4 A3): for a whole-plane
GFF `h`, `|θ| ≤ 1/10` and `W ⊆ B₅(0)`, the processes `ψ ↦ ⟨h, T ψ⟩` (the pairings of `h ∘ ψ_θ`) and
`ψ ↦ ⟨h, ψ⟩`, indexed by the mean-zero test functions supported in `W`, have the same law on the
product space. -/
theorem map_mobTransport0_eq (hh : IsWholePlaneGFF h P) (hθ : |θ| ≤ 1 / 10)
    (hW : W ⊆ Metric.ball 0 5) :
    P.map (fun ω (ψ : TestC0On W) => h ω (mobTransport0 hθ hW ψ).1) =
      P.map (fun ω (ψ : TestC0On W) => h ω ψ.1.1) := by
  have := hh.gaussian.isProbabilityMeasure
  have hX : IsGaussianProcess (fun (ψ : TestC0On W) ω => h ω (mobTransport0 hθ hW ψ).1) P :=
    hh.gaussian.comp_right (mobTransport0 hθ hW)
  have hY : IsGaussianProcess (fun (ψ : TestC0On W) ω => h ω ψ.1.1) P :=
    hh.gaussian.comp_right (Subtype.val : TestC0On W → TestC0)
  have hm : ∀ ψ : TestC0On W,
      ∫ ω, h ω (mobTransport0 hθ hW ψ).1 ∂P = ∫ ω, h ω ψ.1.1 ∂P :=
    fun ψ => (hh.centered _).trans (hh.centered _).symm
  have hc : ∀ φ ψ : TestC0On W,
      cov[fun ω => h ω (mobTransport0 hθ hW φ).1, fun ω => h ω (mobTransport0 hθ hW ψ).1; P] =
        cov[fun ω => h ω φ.1.1, fun ω => h ω ψ.1.1; P] := by
    intro φ ψ
    rw [hh.covariance_eq, hh.covariance_eq]
    exact logCov_mobTransport0 hθ hW φ ψ
  have hXm : Measurable fun ω (ψ : TestC0On W) => h ω (mobTransport0 hθ hW ψ).1 :=
    measurable_pi_iff.2 fun _ => (GFFInv.measurable_pair _).comp hh.measurable
  have hYm : Measurable fun ω (ψ : TestC0On W) => h ω ψ.1.1 :=
    measurable_pi_iff.2 fun _ => (GFFInv.measurable_pair _).comp hh.measurable
  have hfin : ∀ I : Finset (TestC0On W),
      (P.map fun ω (ψ : TestC0On W) => h ω (mobTransport0 hθ hW ψ).1).map I.restrict =
        (P.map fun ω (ψ : TestC0On W) => h ω ψ.1.1).map I.restrict := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hXm,
      Measure.map_map (Finset.measurable_restrict I) hYm]
    exact KilledHeat.map_restrict_eq_of_gaussian hX hY hm hc I
  exact IsProjectiveLimit.unique
    (P := fun I => (P.map fun ω (ψ : TestC0On W) => h ω ψ.1.1).map I.restrict) hfin
    (fun _ => rfl)

/-- The law statement after a deterministic shift `c` of the pairings (GA4 A3, consequence): with
`c ψ = ∫ ψ g` this compares `h ∘ ψ_θ + g` with `h + g` modulo constants on `W`. -/
theorem map_mobTransport0_add_eq (hh : IsWholePlaneGFF h P) (hθ : |θ| ≤ 1 / 10)
    (hW : W ⊆ Metric.ball 0 5) (c : TestC0On W → ℝ) :
    P.map (fun ω (ψ : TestC0On W) => h ω (mobTransport0 hθ hW ψ).1 + c ψ) =
      P.map (fun ω (ψ : TestC0On W) => h ω ψ.1.1 + c ψ) := by
  have hS : Measurable fun (x : TestC0On W → ℝ) (ψ : TestC0On W) => x ψ + c ψ :=
    measurable_pi_iff.2 fun ψ => (measurable_pi_apply ψ).add_const _
  have hXm : Measurable fun ω (ψ : TestC0On W) => h ω (mobTransport0 hθ hW ψ).1 :=
    measurable_pi_iff.2 fun _ => (GFFInv.measurable_pair _).comp hh.measurable
  have hYm : Measurable fun ω (ψ : TestC0On W) => h ω ψ.1.1 :=
    measurable_pi_iff.2 fun _ => (GFFInv.measurable_pair _).comp hh.measurable
  have e1 : (fun ω (ψ : TestC0On W) => h ω (mobTransport0 hθ hW ψ).1 + c ψ) =
      (fun (x : TestC0On W → ℝ) (ψ : TestC0On W) => x ψ + c ψ) ∘
        fun ω (ψ : TestC0On W) => h ω (mobTransport0 hθ hW ψ).1 := rfl
  have e2 : (fun ω (ψ : TestC0On W) => h ω ψ.1.1 + c ψ) =
      (fun (x : TestC0On W → ℝ) (ψ : TestC0On W) => x ψ + c ψ) ∘
        fun ω (ψ : TestC0On W) => h ω ψ.1.1 := rfl
  rw [e1, e2, ← Measure.map_map hS hXm, ← Measure.map_map hS hYm, map_mobTransport0_eq hh hθ hW]

end Law

end SmallGammaGeodesics
