import SmallGammaGeodesics.CC.Pullback
import LQGMetric.Field.GFFInvariance
import LQGMetric.Field.KilledHeatLaw
import QuantumZipper.Proofs.GFF.K3.Polar
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# The local law of the pulled-back GFF for a general Möbius map (GA4 A3; packet CC12a, extra)

Source: planning audit `planning/audits/GA4-sections-7-8.md`, Details **A3** (local Möbius
invariance modulo constants), proved in the repository by P-L2 for the maps `mobPhi θ`
(`Lower/MobiusLaw.lean`, `map_mobTransport0_eq`). `CC.MCInput` quantifies over **every** Möbius map
`ϕ` with `IsConfNbhd ϕ W V`, so its assembly (CC12b) needs A3 in that generality; this file proves
it with the conformal pullback `confPull` of CC1 in place of P-L2's transport.

Let `ϕ(z) = (az + b)/(cz + d)` with `ad − bc ≠ 0` and `IsConfNbhd ϕ W V`; let `ψ = invFunOn ϕ W`.
* `mob_den_ne_zero`: `ϕ` is differentiable on `W`, so `W` contains no pole: `cz + d ≠ 0` on `W`
  (at a pole `ϕ(w)(cw + d) = aw + b` near `z` would force `az + b = 0`, hence `ad − bc = 0`);
* `norm_leftInv_sub`: for `x, y ∈ ϕ(W)`,
  `‖ψx − ψy‖ = ‖x − y‖ ‖cψx + d‖ ‖cψy + d‖ / ‖ad − bc‖`;
* `logCov_confPull_eq`: `logCov (τf) (τg) = logCov f g` for mean-zero test functions `f, g`
  supported in `ϕ(V)`: two changes of variables (`IsConfPull.integral_mul`, no integrability
  needed) give `∫ f(z) ∫ g(w) (−log‖ψz − ψw‖)`, and `−log‖ψz − ψw‖ = −log‖z − w‖ + L(z) + L(w)` with
  `L = ½ log‖ad − bc‖ − log‖cψ + d‖`, whose extra terms integrate to zero against mean-zero `f, g`;
* `map_confPull_eq_of_isMobius` (**A3**): for a whole-plane GFF `h`, the processes
  `g ↦ ⟨h, τ g⟩` and `g ↦ ⟨h, g⟩` indexed by `TestC0On (ϕ(V))` have the same law (centred Gaussian
  processes with equal covariances; P-L2's argument).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Function

namespace SmallGammaGeodesics.CC

open LQGMetric

/-! ## 1. Möbius algebra -/

section Algebra

variable {ϕ : ℂ → ℂ} {a b c d : ℂ}

/-- A Möbius map has no pole at a point where it is differentiable. -/
theorem mob_den_ne_zero (had : a * d - b * c ≠ 0) (hϕ : ∀ z, ϕ z = (a * z + b) / (c * z + d))
    {z : ℂ} (hz : DifferentiableAt ℂ ϕ z) : c * z + d ≠ 0 := by
  intro h0
  have hc : c ≠ 0 := by
    rintro rfl
    apply had
    have hd : d = 0 := by simpa using h0
    rw [hd]
    ring
  have hcont : ContinuousAt (fun w => ϕ w * (c * w + d)) z :=
    hz.continuousAt.mul (by fun_prop)
  have hlim1 : Tendsto (fun w => ϕ w * (c * w + d)) (𝓝[≠] z) (𝓝 (ϕ z * (c * z + d))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun w => ϕ w * (c * w + d)) (𝓝[≠] z) (𝓝 (a * z + b)) := by
    have hev : (fun w => a * w + b) =ᶠ[𝓝[≠] z] fun w => ϕ w * (c * w + d) := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw' : c * w + d ≠ 0 := by
        intro h1
        apply hw
        have h2 : c * w = c * z := by linear_combination h1 - h0
        exact mul_left_cancel₀ hc h2
      rw [hϕ w, div_mul_cancel₀ _ hw']
    have hc2 : Tendsto (fun w : ℂ => a * w + b) (𝓝 z) (𝓝 (a * z + b)) :=
      ((by fun_prop : Continuous fun w : ℂ => a * w + b).tendsto z)
    exact (hc2.mono_left nhdsWithin_le_nhds).congr' hev
  have h3 := tendsto_nhds_unique hlim1 hlim2
  rw [h0, mul_zero] at h3
  apply had
  linear_combination a * h0 + c * h3

/-- The difference formula `ϕ z − ϕ w = (ad − bc)(z − w)/((cz + d)(cw + d))`. -/
theorem mob_sub (hϕ : ∀ z, ϕ z = (a * z + b) / (c * z + d)) {z w : ℂ} (hz : c * z + d ≠ 0)
    (hw : c * w + d ≠ 0) :
    ϕ z - ϕ w = (a * d - b * c) * (z - w) / ((c * z + d) * (c * w + d)) := by
  rw [hϕ, hϕ, div_sub_div _ _ hz hw]
  congr 1
  ring

end Algebra

/-! ## 2. The inverse of a Möbius map on `ϕ(W)` -/

section Inverse

variable {ϕ ψ : ℂ → ℂ} {W V : Set ℂ} {a b c d : ℂ}

theorem mob_den_leftInv_ne_zero (had : a * d - b * c ≠ 0)
    (hϕ : ∀ z, ϕ z = (a * z + b) / (c * z + d)) (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hψ : ∀ z ∈ W, ψ (ϕ z) = z) {x : ℂ} (hx : x ∈ ϕ '' W) : c * ψ x + d ≠ 0 :=
  mob_den_ne_zero had hϕ (hd.differentiableAt (hW.mem_nhds (leftInv_mem hψ hx)))

/-- `‖ψx − ψy‖ = ‖x − y‖ ‖cψx + d‖ ‖cψy + d‖ / ‖ad − bc‖` on `ϕ(W)`. -/
theorem norm_leftInv_sub (had : a * d - b * c ≠ 0) (hϕ : ∀ z, ϕ z = (a * z + b) / (c * z + d))
    (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hψ : ∀ z ∈ W, ψ (ϕ z) = z) {x y : ℂ}
    (hx : x ∈ ϕ '' W) (hy : y ∈ ϕ '' W) :
    ‖ψ x - ψ y‖ = ‖x - y‖ * (‖c * ψ x + d‖ * ‖c * ψ y + d‖) / ‖a * d - b * c‖ := by
  have hDx := mob_den_leftInv_ne_zero had hϕ hW hd hψ hx
  have hDy := mob_den_leftInv_ne_zero had hϕ hW hd hψ hy
  have h1 := mob_sub hϕ hDx hDy
  rw [apply_leftInv hψ hx, apply_leftInv hψ hy] at h1
  have hD : (c * ψ x + d) * (c * ψ y + d) ≠ 0 := mul_ne_zero hDx hDy
  have h2 : ψ x - ψ y = (x - y) * ((c * ψ x + d) * (c * ψ y + d)) / (a * d - b * c) := by
    rw [h1, div_mul_cancel₀ _ hD, mul_div_cancel_left₀ _ had]
  rw [h2, norm_div, norm_mul, norm_mul]

/-- The correction `L = ½ log‖ad − bc‖ − log‖cψ + d‖`. -/
def mobCorr (ψ : ℂ → ℂ) (a b c d : ℂ) (x : ℂ) : ℝ :=
  Real.log ‖a * d - b * c‖ / 2 - Real.log ‖c * ψ x + d‖

/-- **The Möbius identity** `−log‖ψx − ψy‖ = −log‖x − y‖ + L(x) + L(y)` on `ϕ(W)`, for `x ≠ y`. -/
theorem neg_log_norm_leftInv_sub (had : a * d - b * c ≠ 0)
    (hϕ : ∀ z, ϕ z = (a * z + b) / (c * z + d)) (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hψ : ∀ z ∈ W, ψ (ϕ z) = z) {x y : ℂ} (hx : x ∈ ϕ '' W) (hy : y ∈ ϕ '' W) (hxy : x ≠ y) :
    -Real.log ‖ψ x - ψ y‖ = -Real.log ‖x - y‖ + mobCorr ψ a b c d x + mobCorr ψ a b c d y := by
  have hDx := norm_ne_zero_iff.2 (mob_den_leftInv_ne_zero had hϕ hW hd hψ hx)
  have hDy := norm_ne_zero_iff.2 (mob_den_leftInv_ne_zero had hϕ hW hd hψ hy)
  have hxy' : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hxy)
  have hdet : ‖a * d - b * c‖ ≠ 0 := norm_ne_zero_iff.2 had
  rw [norm_leftInv_sub had hϕ hW hd hψ hx hy, Real.log_div (mul_ne_zero hxy' (mul_ne_zero hDx hDy))
    hdet, Real.log_mul hxy' (mul_ne_zero hDx hDy), Real.log_mul hDx hDy]
  unfold mobCorr
  ring

/-- `L` is continuous on `ϕ(W)`. -/
theorem continuousOn_mobCorr (had : a * d - b * c ≠ 0) (hϕ : ∀ z, ϕ z = (a * z + b) / (c * z + d))
    (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W) (hψ : ∀ z ∈ W, ψ (ϕ z) = z) :
    ContinuousOn (mobCorr ψ a b c d) (ϕ '' W) := by
  have hψc := continuousOn_leftInv hW hd hi hψ
  refine continuousOn_const.sub (ContinuousOn.log ?_ fun x hx => ?_)
  · exact ((continuousOn_const.mul hψc).add continuousOn_const).norm
  · exact norm_ne_zero_iff.2 (mob_den_leftInv_ne_zero had hϕ hW hd hψ hx)

end Inverse

/-! ## 3. Invariance of the covariance -/

section Cov

variable {ϕ : ℂ → ℂ} {W V : Set ℂ}

/-- **Möbius invariance of the covariance on mean-zero test functions** (GA4 A3, steps 3–4):
`logCov (τ f) (τ g) = logCov f g` for `f, g` mean-zero and supported in `ϕ(V)`,
`τ = confPull ϕ W`. -/
theorem logCov_confPull_eq (hM : IsMobius ϕ) (hϕ : IsConfNbhd ϕ W V) {f g : TestC}
    (hf : tsupport (f : ℂ → ℝ) ⊆ ϕ '' V) (hf0 : ∫ z, f z = 0)
    (hg : tsupport (g : ℂ → ℝ) ⊆ ϕ '' V) (hg0 : ∫ w, g w = 0) :
    logCov (confPull ϕ W f) (confPull ϕ W g) = logCov f g := by
  obtain ⟨a, b, c, d, had, hϕab⟩ := hM
  have hW := hϕ.isOpen_W
  have hd := hϕ.differentiableOn
  have hi := hϕ.injOn
  set ψ := invFunOn ϕ W with hψdef
  have hψ : ∀ z ∈ W, ψ (ϕ z) = z := fun _ hz => hi.leftInvOn_invFunOn hz
  have hVW : ϕ '' V ⊆ ϕ '' W := hϕ.image_subset
  have hτf := isConfPull_confPull hϕ hf
  have hτg := isConfPull_confPull hϕ hg
  -- step 1: two changes of variables
  have hcv : logCov (confPull ϕ W f) (confPull ϕ W g) =
      ∫ z, f z * ∫ w, g w * -Real.log ‖ψ z - ψ w‖ := by
    unfold logCov
    have hin : ∀ u : ℂ, ∫ v, confPull ϕ W f u * -Real.log ‖u - v‖ * confPull ϕ W g v =
        confPull ϕ W f u * ∫ y, g y * -Real.log ‖u - ψ y‖ := by
      intro u
      have e : (fun v => confPull ϕ W f u * -Real.log ‖u - v‖ * confPull ϕ W g v) =
          fun v => confPull ϕ W f u * (confPull ϕ W g v * -Real.log ‖u - v‖) := by
        funext v
        ring
      rw [e, integral_const_mul,
        IsConfPull.integral_mul hϕ hψ hg hτg (fun v => -Real.log ‖u - v‖)]
    simp_rw [hin]
    exact IsConfPull.integral_mul hϕ hψ hf hτf (fun u => ∫ y, g y * -Real.log ‖u - ψ y‖)
  -- step 2: the inner integral
  set L := mobCorr ψ a b c d with hL
  set K : ℝ := ∫ w, g w * L w with hK
  have hgi : Integrable (g : ℂ → ℝ) :=
    g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  have hfi : Integrable (f : ℂ → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hgL : Integrable fun w => g w * L w := by
    have hcont : ContinuousOn (fun w => g w * L w) (ϕ '' W) :=
      g.continuous.continuousOn.mul (continuousOn_mobCorr had hϕab hW hd hi hψ)
    refine Continuous.integrable_of_hasCompactSupport
      (hcont.continuous_of_tsupport_subset (isOpen_image_conf hW hd hi)
        ((tsupport_mul_subset_left).trans (hg.trans hVW))) ?_
    exact g.hasCompactSupport.mul_right
  have hinner : ∀ z ∈ ϕ '' W,
      ∫ w, g w * -Real.log ‖ψ z - ψ w‖ = (∫ w, g w * -Real.log ‖z - w‖) + K := by
    intro z hz
    have hpt : (fun w => g w * -Real.log ‖ψ z - ψ w‖) =ᵐ[volume]
        fun w => g w * -Real.log ‖z - w‖ + (g w * L z + g w * L w) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1
        ((Set.countable_singleton z).measure_zero volume)] with w hw
      by_cases hwW : w ∈ ϕ '' W
      · have hzw : z ≠ w := fun h => hw (h ▸ rfl)
        rw [neg_log_norm_leftInv_sub had hϕab hW hd hψ hz hwW hzw]
        ring
      · have hgw : g w = 0 := image_eq_zero_of_notMem_tsupport fun h => hwW (hVW (hg h))
        rw [hgw]
        ring
    have hI1 : Integrable fun w => g w * -Real.log ‖z - w‖ := by
      refine (QuantumZipper.K3.integrable_log_norm_sub_mul_K3 g.continuous g.hasCompactSupport
        z).neg.congr (Filter.Eventually.of_forall fun w => ?_)
      simp only [Pi.neg_apply]
      rw [norm_sub_rev]
      ring
    have hI2 : Integrable fun w => g w * L z := hgi.mul_const _
    have hI23 : Integrable fun w => g w * L z + g w * L w := hI2.add hgL
    rw [integral_congr_ae hpt, integral_add hI1 hI23, integral_add hI2 hgL,
      integral_mul_const, hg0, zero_mul, zero_add]
  -- step 3: the outer integral
  have houter : (fun z => f z * ∫ w, g w * -Real.log ‖ψ z - ψ w‖) =
      fun z => f z * K + f z * ∫ w, g w * -Real.log ‖z - w‖ := by
    funext z
    by_cases hz : z ∈ ϕ '' W
    · rw [hinner z hz]
      ring
    · have : f z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hVW (hf h))
      rw [this]
      ring
  rw [hcv, houter, GFFInv.integral_add_of_left (hfi.mul_const K)
    (by rw [integral_mul_const, hf0, zero_mul])]
  unfold logCov
  congr 1
  funext z
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

end Cov

/-! ## 4. The law statement (GA4 A3 for a general Möbius map) -/

section Law

variable {ϕ : ℂ → ℂ} {W V : Set ℂ}

/-- The pullback maps mean-zero test functions supported in `ϕ(V)` to mean-zero test functions. -/
def confPull0 (hϕ : IsConfNbhd ϕ W V) (g : TestC0On (ϕ '' V)) : TestC0 :=
  ⟨confPull ϕ W g.1.1, by rw [IsConfPull.integral_eq hϕ g.2 (isConfPull_confPull hϕ g.2), g.1.2]⟩

theorem confPull0_coe (hϕ : IsConfNbhd ϕ W V) (g : TestC0On (ϕ '' V)) :
    (confPull0 hϕ g).1 = confPull ϕ W g.1.1 :=
  rfl

/-- **GA4 A3 for a general Möbius map.** For a Möbius `ϕ` with `IsConfNbhd ϕ W V` and a whole-plane
GFF `h`, the processes `g ↦ ⟨h, τ g⟩` (the pairings of `h ∘ ϕ⁻¹` on `ϕ(V)`, `τ = confPull ϕ W`) and
`g ↦ ⟨h, g⟩`, indexed by the mean-zero test functions supported in `ϕ(V)`, have the same law. -/
theorem map_confPull_eq_of_isMobius (hM : IsMobius ϕ) (hϕ : IsConfNbhd ϕ W V) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P) :
    P.map (fun ω (g : TestC0On (ϕ '' V)) => h ω (confPull ϕ W g.1.1)) =
      P.map (fun ω (g : TestC0On (ϕ '' V)) => h ω g.1.1) := by
  have := hh.gaussian.isProbabilityMeasure
  have hX : IsGaussianProcess (fun (g : TestC0On (ϕ '' V)) ω => h ω (confPull0 hϕ g).1) P :=
    hh.gaussian.comp_right (confPull0 hϕ)
  have hY : IsGaussianProcess (fun (g : TestC0On (ϕ '' V)) ω => h ω g.1.1) P :=
    hh.gaussian.comp_right (Subtype.val : TestC0On (ϕ '' V) → TestC0)
  have hm : ∀ g : TestC0On (ϕ '' V),
      ∫ ω, h ω (confPull0 hϕ g).1 ∂P = ∫ ω, h ω g.1.1 ∂P :=
    fun g => (hh.centered _).trans (hh.centered _).symm
  have hc : ∀ f g : TestC0On (ϕ '' V),
      cov[fun ω => h ω (confPull0 hϕ f).1, fun ω => h ω (confPull0 hϕ g).1; P] =
        cov[fun ω => h ω f.1.1, fun ω => h ω g.1.1; P] := by
    intro f g
    rw [hh.covariance_eq, hh.covariance_eq]
    exact logCov_confPull_eq hM hϕ f.2 f.1.2 g.2 g.1.2
  have hXm : Measurable fun ω (g : TestC0On (ϕ '' V)) => h ω (confPull0 hϕ g).1 :=
    measurable_pi_iff.2 fun _ => (GFFInv.measurable_pair _).comp hh.measurable
  have hYm : Measurable fun ω (g : TestC0On (ϕ '' V)) => h ω g.1.1 :=
    measurable_pi_iff.2 fun _ => (GFFInv.measurable_pair _).comp hh.measurable
  have hfin : ∀ I : Finset (TestC0On (ϕ '' V)),
      (P.map fun ω (g : TestC0On (ϕ '' V)) => h ω (confPull0 hϕ g).1).map I.restrict =
        (P.map fun ω (g : TestC0On (ϕ '' V)) => h ω g.1.1).map I.restrict := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hXm,
      Measure.map_map (Finset.measurable_restrict I) hYm]
    exact KilledHeat.map_restrict_eq_of_gaussian hX hY hm hc I
  exact IsProjectiveLimit.unique
    (P := fun I => (P.map fun ω (g : TestC0On (ϕ '' V)) => h ω g.1.1).map I.restrict) hfin
    (fun _ => rfl)

end Law

end SmallGammaGeodesics.CC
