import SmallGammaGeodesics.NIC.Transport
import LQGMetric.Field.MarkovGermVer2A
import LQGMetric.Field.ExistGFF

/-!
# NIC, part 1 (T2): the transport is a quasi-isometry for `logCov`

Packet P-G1, target T2; GA2 D5 Step 4 (`‖τφ‖_*² ∈ [(1 + C₄ε)⁻¹, (1 − C₄ε)⁻¹]·‖φ‖_*²`).

**Route.** GA2's Dirichlet-dual characterization of `logCov`, with no new analysis:

* the easy half is Cauchy–Schwarz in `L²(ℝ × ℂ)` (`sq_integral_mul_le`):
  `(∫ g f)² ≤ logCov g g · E(f)` for mean-zero `g` and every test function `f`, because
  `∫ g f = logCov g ρ_f = ⟪J g, J ρ_f⟫` and `‖J ρ_f‖² = E(f)` (`LQGMetric.logCov_cmTest_right`,
  `logCov_cmTest_cmTest`, `GFFExist.inner_testL2_testL2`, with `J = testL2`, `ρ_f = cmTest f`);
* the hard half is a near-optimizer (`exists_near_optimizer`): `f = χ_R u_g` with the logarithmic
  potential `u_g` and the cutoffs `χ_R` of `LQGMetric.MarkovGermVer` has `∫ g f = logCov g g` and
  `E(f) ≤ logCov g g + η` (IMS identity `gradEnergy_cut`, decay `abs_logPot_le`,
  `integral_logPot_cutR_le`);
* the energy of a composition: `E(f ∘ Φ) ≤ κ(δ) E(f)` with `κ(δ) = (1 + δ)²(1 + 3δ) ≤ 1 + 6δ`
  (`gradEnergy_compTest_le`), from the chain rule, `‖DΦ‖ ≤ 1 + δ` and the change of variables with
  `jac Ψ ≤ 1 + 3δ`.

Then (`logCov_transport_le`, `logCov_le_logCov_transport`), for mean-zero `g`:
`logCov (τ g) (τ g) ≤ κ · logCov g g` and `logCov g g ≤ κ · logCov (τ g) (τ g)`; the packet form
with `C₄ = 12` (`δ = 2ε`) is `logCov_transport_bounds`.

The equivalent kernel route `logCov (τ g) (τ g') = ∫∫ g g' (−log|Ψx − Ψy|)` was not used: the
kernel difference `−log|Ψx−Ψy| + log|x−y|` is bounded by `O(ε)` but a bounded kernel is not
`O(ε)`-small as an operator `H^{-1} → H¹` without second-derivative (Calderón–Zygmund) bounds,
whereas the dual route needs only first derivatives and existing lemmas.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace SmallGammaGeodesics
namespace NIC

open LQGMetric LQGMetric.GFFExist LQGMetric.MarkovGermVer

/-! ## Cauchy–Schwarz -/

lemma logCov_eq_inner (g g' : TestC) (hg : ∫ x, g x = 0) (hg' : ∫ x, g' x = 0) :
    logCov g g' = ⟪testL2 g, testL2 g'⟫ := (inner_testL2_testL2 g g' hg hg').symm

/-- `logCov g g = ‖J g‖² ≥ 0` for mean-zero `g` -/
lemma logCov_self_nonneg (g : TestC) (hg : ∫ x, g x = 0) : 0 ≤ logCov g g := by
  rw [logCov_eq_inner g g hg hg]; exact real_inner_self_nonneg

/-- symmetry of `logCov` on mean-zero test functions -/
lemma logCov_comm (g g' : TestC) (hg : ∫ x, g x = 0) (hg' : ∫ x, g' x = 0) :
    logCov g g' = logCov g' g := by
  rw [logCov_eq_inner g g' hg hg', logCov_eq_inner g' g hg' hg, real_inner_comm]

/-- **The easy half of the dual characterization**: `(∫ g f)² ≤ logCov g g · E(f)`. -/
theorem sq_integral_mul_le (g : TestC) (hg : ∫ x, g x = 0) (f : TestC) :
    (∫ x, g x * f x) ^ 2 ≤ logCov g g * gradEnergy f := by
  have h1 : ∫ x, g x * f x = ⟪testL2 g, testL2 (cmTest f)⟫ := by
    rw [← logCov_cmTest_right f g, logCov_eq_inner g (cmTest f) hg (integral_cmTest f)]
  have h2 : gradEnergy f = ⟪testL2 (cmTest f), testL2 (cmTest f)⟫ := by
    rw [← logCov_cmTest_cmTest f,
      logCov_eq_inner (cmTest f) (cmTest f) (integral_cmTest f) (integral_cmTest f)]
  rw [h1, h2, logCov_eq_inner g g hg hg, sq]
  exact real_inner_mul_inner_self_le _ _

/-! ## The near-optimizer -/

/-- **The hard half of the dual characterization**: for mean-zero `g` and `η > 0` there is a test
function `f` with `∫ g f = logCov g g` and `E(f) ≤ logCov g g + η` (`f = χ_R u_g`). -/
theorem exists_near_optimizer (g : TestC) (hg : ∫ x, g x = 0) {η : ℝ} (hη : 0 < η) :
    ∃ f : TestC, ∫ x, g x * f x = logCov g g ∧ gradEnergy f ≤ logCov g g + η := by
  obtain ⟨Ω, _, P, h, _, hh⟩ := exists_wholePlaneGFF
  set ψ : TestC0 := ⟨g, hg⟩
  obtain ⟨C, R₀, hR₀, hC⟩ := abs_logPot_le ψ
  obtain ⟨K, hK0, hK⟩ := exists_bound_fderiv_bump1
  obtain ⟨r, hr⟩ := g.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set M := 2 * C ^ 2 * K ^ 2 with hM
  set R := max (max R₀ r) (max 1 (M / η + 1)) with hRdef
  have hR1 : 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRpos : 0 < R := one_pos.trans_le hR1
  have hRR₀ : R₀ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRr : r ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hRM : M / η < R :=
    (lt_add_one _).trans_le ((le_max_right _ _).trans (le_max_right _ _))
  have hχ1 : ∀ x ∈ tsupport (ψ.1 : ℂ → ℝ), cutR R x = 1 := fun x hx =>
    cutR_eq_one hRpos ((mem_closedBall_zero_iff.1 (hr hx)).trans hRr)
  have hs := (contDiff_cutR R).mul (contDiff_logPot ψ.1)
  have hc := (hasCompactSupport_cutR hRpos).mul_right (f' := logPot ψ.1)
  refine ⟨tC hs hc, ?_, ?_⟩
  · have e : ∀ x, g x * (tC hs hc) x = g x * logPot g x := fun x => by
      change g x * (cutR R x * logPot g x) = g x * logPot g x
      by_cases hx : x ∈ tsupport (g : ℂ → ℝ)
      · rw [hχ1 x hx, one_mul]
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
    simp_rw [e]
    exact integral_mul_logPot g g
  · have hE := gradEnergy_cut hh ψ (contDiff_cutR R) (hasCompactSupport_cutR hRpos) hχ1
    have hb := integral_logPot_cutR_le (ψ := ψ) hRpos (fun x hx => hC x (hRR₀.trans hx)) hK
    change gradEnergy (fun x => cutR R x * logPot g x) ≤ _
    rw [hE, integral_mul_logPot]
    have e2 : (2 * Real.pi)⁻¹ * ((C / R) ^ 2 * (K / R) ^ 2 * (Real.pi * (2 * R) ^ 2)) =
        M / R ^ 2 := by
      rw [hM]; field_simp
    have h3 : M / R ^ 2 ≤ η := by
      have hM0 : 0 ≤ M := by positivity
      have h4 : M / R ^ 2 ≤ M / R := div_le_div_of_nonneg_left hM0 hRpos (by nlinarith)
      refine h4.trans ?_
      rw [div_le_iff₀ hRpos]
      rw [div_lt_iff₀ hη] at hRM
      linarith
    have h5 : (2 * Real.pi)⁻¹ *
        ∫ x, logPot (ψ.1 : ℂ → ℝ) x ^ 2 * ‖fderiv ℝ (cutR R) x‖ ^ 2 ≤ η :=
      (mul_le_mul_of_nonneg_left hb (by positivity)).trans (e2.le.trans h3)
    change logCov g g + (2 * Real.pi)⁻¹ *
        ∫ x, logPot (ψ.1 : ℂ → ℝ) x ^ 2 * ‖fderiv ℝ (cutR R) x‖ ^ 2 ≤ logCov g g + η
    linarith

/-! ## Energy of a composition -/

/-- `κ(δ) = (1 + δ)²(1 + 3δ)`: the energy distortion of a `δ`-near-identity pair -/
def kappa (δ : ℝ) : ℝ := (1 + δ) ^ 2 * (1 + 3 * δ)

lemma one_le_kappa {δ : ℝ} (hδ : 0 ≤ δ) : 1 ≤ kappa δ := by
  unfold kappa; nlinarith [sq_nonneg δ, mul_nonneg hδ (sq_nonneg δ)]

lemma kappa_le {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 16) : kappa δ ≤ 1 + 6 * δ := by
  unfold kappa; nlinarith [mul_nonneg hδ hδ, mul_nonneg (mul_nonneg hδ hδ) hδ]

lemma integrable_norm_fderiv_sq (φ : TestC) : Integrable fun x => ‖fderiv ℝ φ x‖ ^ 2 := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact ((φ.contDiff.continuous_fderiv (by simp)).norm).pow 2
  · exact (φ.hasCompactSupport.fderiv (𝕜 := ℝ)).norm.comp_left (g := fun t : ℝ => t ^ 2)
      (by simp)

namespace NearIdPair

variable (D : NearIdPair)

lemma norm_fderiv_le (z : ℂ) : ‖fderiv ℝ D.Φ z‖ ≤ 1 + D.δ := by
  calc ‖fderiv ℝ D.Φ z‖ = ‖(fderiv ℝ D.Φ z - ContinuousLinearMap.id ℝ ℂ) +
        ContinuousLinearMap.id ℝ ℂ‖ := by rw [sub_add_cancel]
    _ ≤ ‖fderiv ℝ D.Φ z - ContinuousLinearMap.id ℝ ℂ‖ + ‖ContinuousLinearMap.id ℝ ℂ‖ :=
        norm_add_le _ _
    _ ≤ D.δ + 1 := add_le_add (D.deriv_close z) ContinuousLinearMap.norm_id_le
    _ = 1 + D.δ := add_comm _ _

lemma hasCompactSupport_comp {G : ℂ → ℝ} (hG : HasCompactSupport G) :
    HasCompactSupport fun x => G (D.Φ x) := by
  refine HasCompactSupport.intro (hG.isCompact.image D.continuous_inv) ?_
  intro x hx
  exact image_eq_zero_of_notMem_tsupport fun h => hx ⟨D.Φ x, h, D.left_inv x⟩

/-- change of variables: `∫ F(Φ x) dx = ∫ jac Ψ · F` -/
lemma integral_comp_eq (F : ℂ → ℝ) : ∫ x, F (D.Φ x) = ∫ y, jac D.Ψ y * F y := by
  have h := D.symm.integral_transportFun_mul (fun _ => 1) F
  simp only [symm_Φ, symm_Ψ, transportFun, mul_one, one_mul] at h
  exact h.symm

/-- **Energy of a composition**: `E(f ∘ Φ) ≤ κ(δ) E(f)`. -/
theorem gradEnergy_compTest_le (f : TestC) :
    gradEnergy (D.compTest f) ≤ kappa D.δ * gradEnergy f := by
  have hfd : ∀ x, fderiv ℝ (D.compTest f) x = (fderiv ℝ f (D.Φ x)).comp (fderiv ℝ D.Φ x) :=
    fun x => fderiv_comp (g := (f : ℂ → ℝ)) (f := D.Φ) x
      (f.contDiff.differentiable smooth_ne_zero (D.Φ x)) (D.differentiable x)
  have hpt : ∀ x, ‖fderiv ℝ (D.compTest f) x‖ ^ 2 ≤
      (1 + D.δ) ^ 2 * ‖fderiv ℝ f (D.Φ x)‖ ^ 2 := fun x => by
    rw [hfd, ← mul_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    calc ‖(fderiv ℝ f (D.Φ x)).comp (fderiv ℝ D.Φ x)‖
        ≤ ‖fderiv ℝ f (D.Φ x)‖ * ‖fderiv ℝ D.Φ x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ f (D.Φ x)‖ * (1 + D.δ) :=
          mul_le_mul_of_nonneg_left (D.norm_fderiv_le x) (norm_nonneg _)
      _ = (1 + D.δ) * ‖fderiv ℝ f (D.Φ x)‖ := mul_comm _ _
  have hFc : HasCompactSupport fun y => ‖fderiv ℝ f y‖ ^ 2 :=
    (f.hasCompactSupport.fderiv (𝕜 := ℝ)).norm.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hFcont : Continuous fun y => ‖fderiv ℝ f y‖ ^ 2 :=
    ((f.contDiff.continuous_fderiv (by simp)).norm).pow 2
  have hi1 : Integrable fun x => (1 + D.δ) ^ 2 * ‖fderiv ℝ f (D.Φ x)‖ ^ 2 :=
    ((hFcont.comp D.continuous).integrable_of_hasCompactSupport
      (D.hasCompactSupport_comp hFc)).const_mul _
  have hi2 : Integrable fun y => jac D.Ψ y * ‖fderiv ℝ f y‖ ^ 2 :=
    (D.symm.continuous_jac.mul hFcont).integrable_of_hasCompactSupport hFc.mul_left
  have hi3 : Integrable fun y => (1 + 3 * D.δ) * ‖fderiv ℝ f y‖ ^ 2 :=
    (integrable_norm_fderiv_sq f).const_mul _
  have step1 : ∫ x, ‖fderiv ℝ (D.compTest f) x‖ ^ 2 ≤
      (1 + D.δ) ^ 2 * ∫ x, ‖fderiv ℝ f (D.Φ x)‖ ^ 2 := by
    rw [← integral_const_mul]
    exact integral_mono (integrable_norm_fderiv_sq _) hi1 hpt
  have step2 : ∫ x, ‖fderiv ℝ f (D.Φ x)‖ ^ 2 ≤ (1 + 3 * D.δ) * ∫ y, ‖fderiv ℝ f y‖ ^ 2 := by
    rw [D.integral_comp_eq (fun y => ‖fderiv ℝ f y‖ ^ 2), ← integral_const_mul]
    refine integral_mono hi2 hi3 fun y => ?_
    exact mul_le_mul_of_nonneg_right (D.symm.jac_le y) (sq_nonneg _)
  have hpos : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  unfold gradEnergy kappa
  calc (2 * Real.pi)⁻¹ * ∫ x, ‖fderiv ℝ (D.compTest f) x‖ ^ 2
      ≤ (2 * Real.pi)⁻¹ * ((1 + D.δ) ^ 2 * ∫ x, ‖fderiv ℝ f (D.Φ x)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left step1 hpos
    _ ≤ (2 * Real.pi)⁻¹ * ((1 + D.δ) ^ 2 * ((1 + 3 * D.δ) * ∫ y, ‖fderiv ℝ f y‖ ^ 2)) := by
        gcongr
    _ = (1 + D.δ) ^ 2 * (1 + 3 * D.δ) * ((2 * Real.pi)⁻¹ * ∫ y, ‖fderiv ℝ f y‖ ^ 2) := by ring

end NearIdPair

/-! ## The quasi-isometry -/

/-- `A² ≤ c (A + η)` for all `η > 0` implies `A ≤ c` -/
lemma le_of_forall_sq_le_mul_add {A c : ℝ} (hA : 0 ≤ A)
    (h : ∀ η : ℝ, 0 < η → A ^ 2 ≤ c * (A + η)) : A ≤ c := by
  by_contra hlt
  push Not at hlt
  have h1 := h ((A - c) / 2) (by linarith)
  nlinarith

namespace NearIdPair

variable (D : NearIdPair)

/-- `τ` preserves mean-zero test functions -/
lemma integral_transport_eq_zero {g : TestC} (hg : ∫ x, g x = 0) :
    ∫ x, D.transport g x = 0 := by rw [D.integral_transport, hg]

/-- **T2, upper half**: `logCov (τ g) (τ g) ≤ κ(δ) · logCov g g`. -/
theorem logCov_transport_le (g : TestC) (hg : ∫ x, g x = 0) :
    logCov (D.transport g) (D.transport g) ≤ kappa D.δ * logCov g g := by
  have hτ := D.integral_transport_eq_zero hg
  have hB := logCov_self_nonneg g hg
  have hκ := one_le_kappa D.δ_nonneg
  refine le_of_forall_sq_le_mul_add (logCov_self_nonneg _ hτ) fun η hη => ?_
  obtain ⟨f, hf1, hf2⟩ := exists_near_optimizer (D.transport g) hτ hη
  have hcv : ∫ x, D.transport g x * f x = ∫ y, g y * D.symm.compTest f y :=
    D.integral_transport_mul g f
  have hE := D.symm.gradEnergy_compTest_le f
  rw [symm_δ] at hE
  calc logCov (D.transport g) (D.transport g) ^ 2
      = (∫ y, g y * D.symm.compTest f y) ^ 2 := by rw [← hcv, hf1]
    _ ≤ logCov g g * gradEnergy (D.symm.compTest f) := sq_integral_mul_le g hg _
    _ ≤ logCov g g * (kappa D.δ * gradEnergy f) := mul_le_mul_of_nonneg_left hE hB
    _ ≤ logCov g g * (kappa D.δ * (logCov (D.transport g) (D.transport g) + η)) := by
        gcongr
    _ = kappa D.δ * logCov g g * (logCov (D.transport g) (D.transport g) + η) := by ring

/-- **T2, lower half**: `logCov g g ≤ κ(δ) · logCov (τ g) (τ g)`. -/
theorem logCov_le_logCov_transport (g : TestC) (hg : ∫ x, g x = 0) :
    logCov g g ≤ kappa D.δ * logCov (D.transport g) (D.transport g) := by
  have hτ := D.integral_transport_eq_zero hg
  have hA := logCov_self_nonneg _ hτ
  have hκ := one_le_kappa D.δ_nonneg
  refine le_of_forall_sq_le_mul_add (logCov_self_nonneg g hg) fun η hη => ?_
  obtain ⟨f, hf1, hf2⟩ := exists_near_optimizer g hg hη
  have hcv : ∫ x, D.transport g x * D.compTest f x = ∫ y, g y * f y := by
    rw [D.integral_transport_mul g (D.compTest f)]
    simp only [compTest_apply, D.right_inv]
  have hE := D.gradEnergy_compTest_le f
  calc logCov g g ^ 2 = (∫ x, D.transport g x * D.compTest f x) ^ 2 := by rw [hcv, hf1]
    _ ≤ logCov (D.transport g) (D.transport g) * gradEnergy (D.compTest f) :=
        sq_integral_mul_le _ hτ _
    _ ≤ logCov (D.transport g) (D.transport g) * (kappa D.δ * gradEnergy f) :=
        mul_le_mul_of_nonneg_left hE hA
    _ ≤ logCov (D.transport g) (D.transport g) * (kappa D.δ * (logCov g g + η)) := by gcongr
    _ = kappa D.δ * logCov (D.transport g) (D.transport g) * (logCov g g + η) := by ring

end NearIdPair

/-- **T2 in the packet's form** (`C₄ = 12`): for `CC.IsNearIdDiffeo Φ Ψ U ε` with
`0 ≤ ε ≤ 1/32` and every mean-zero test function `g`,
`(1 + 12ε)⁻¹ logCov g g ≤ logCov (τ g) (τ g) ≤ (1 − 12ε)⁻¹ logCov g g`. -/
theorem logCov_transport_bounds {Φ Ψ : ℂ → ℂ} {U : Set ℂ} {ε : ℝ}
    (hΦ : CC.IsNearIdDiffeo Φ Ψ U ε) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 32) (g : TestC)
    (hg : ∫ x, g x = 0) :
    (1 + 12 * ε)⁻¹ * logCov g g ≤
        logCov ((NearIdPair.ofDiffeo hΦ hε0 hε).transport g)
          ((NearIdPair.ofDiffeo hΦ hε0 hε).transport g) ∧
      logCov ((NearIdPair.ofDiffeo hΦ hε0 hε).transport g)
          ((NearIdPair.ofDiffeo hΦ hε0 hε).transport g) ≤ (1 - 12 * ε)⁻¹ * logCov g g := by
  set D := NearIdPair.ofDiffeo hΦ hε0 hε
  have hκ : kappa D.δ ≤ 1 + 12 * ε := by
    have := kappa_le D.δ_nonneg D.δ_le
    simp only [D, NearIdPair.ofDiffeo_δ] at this ⊢
    linarith
  have hκ1 := one_le_kappa D.δ_nonneg
  have hB := logCov_self_nonneg g hg
  have hA := logCov_self_nonneg _ (D.integral_transport_eq_zero hg)
  have h1 := D.logCov_le_logCov_transport g hg
  have h2 := D.logCov_transport_le g hg
  have hp : 0 < 1 + 12 * ε := by linarith
  have hm : 0 < 1 - 12 * ε := by linarith
  constructor
  · rw [inv_mul_le_iff₀ hp]
    exact h1.trans (mul_le_mul_of_nonneg_right hκ hA)
  · rw [le_inv_mul_iff₀ hm]
    calc (1 - 12 * ε) * logCov (D.transport g) (D.transport g)
        ≤ (1 - 12 * ε) * (kappa D.δ * logCov g g) := mul_le_mul_of_nonneg_left h2 hm.le
      _ ≤ (1 - 12 * ε) * ((1 + 12 * ε) * logCov g g) := by gcongr
      _ = (1 - (12 * ε) ^ 2) * logCov g g := by ring
      _ ≤ logCov g g := by nlinarith [sq_nonneg (12 * ε)]

end NIC
end SmallGammaGeodesics
