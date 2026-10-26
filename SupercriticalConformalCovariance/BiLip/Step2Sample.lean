import SupercriticalConformalCovariance.BiLip.Step2Geom
import SupercriticalConformalCovariance.BiLip.Lemma21
import SupercriticalConformalCovariance.BiLip.Port.Realize
import SupercriticalConformalCovariance.Rotation.Affine
import LQGMetric.Field.Measurable

/-!
# Lemma 2.1, step 2: one instance at one scale, rescaled

Paper l. 112–123 for one instance and one pair `(z, r)` with `GeomGood φ U z r ε` and `4r < s`,
`B_s(z) ⊆ U`. With `a = r φ′(z)`, `ρ = |a|`, the source field rescaled and smoothly normalized,
`ĥ = h(z + r ·) − (h(z + r ·), 𝐟)`, GM's constant `c₀ = (ĥ ∘ F⁻¹)_{𝐟,1}(0)` and
`C = (h(z + r ·), 𝐟) + Q log ρ + c₀`:
* `G = g₀ + χ_m (k − Q log |(φ⁻¹)′|) − C` (the Lemma 3.3 proof's normalized whole-plane field: `G|_{B_{3ρ}(φ z)} =
  (h ∘ φ⁻¹) − C`);
* `G′ = G(φ(z) + a ·) + Q log |a|` (`D_G(φ(z) + a u, φ(z) + a v) = D_{G′}(u, v)`).

`ae_rescaled`: almost surely
1. `G′|_{B_3(0)} = (ĥ ∘ F⁻¹ − c₀)|_{B_3(0)}`, GM's normalized transformed field of Lemma 2.4 (2.6);
2. `e(around A_{9ρ/8,15ρ/8}(φ z)) ≤ e^{ξ(Q log r + (h(z+r·),𝐟) + c₀ + 2|Q|ε)} D_{G′}(around A_{9/8,15/8}(0))`;
3. `e^{ξ(Q log r + (h(z+r·),𝐟) + c₀ − 2|Q|ε)} acr(D_{G′}; 5/8, 7/8) ≤ e(across cl A_{5ρ/8,7ρ/8}(φ z))`.
The factors `e^{±2ξ|Q|ε}` are the Weyl comparison for the log-derivative correction (l. 120–122).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalLQGUniqueness (LSCMetric weylScale aroundDist EuclideanAnnulus IsStrongLQGMetric
  IsLFPPExponent)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier (forget)
open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent (acr)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization)
open LQGMetric (DistC DistOn TestC restrictTo addFun addConst affineComp IsGFFPlusCont)
open SupercriticalConformalCovariance.Domain (exW exWO cutF)
open SmallGammaGeodesics.CC (intDist)
open SupercriticalConformalCovariance.GM24 (invPullDist invPullSmoothAvg)

/-- the rescaled source field `h(z + r ·)` -/
def rescaledField (h : DistC) (z : ℂ) (r : ℝ) : DistC := affineComp r z h

/-- its smooth normalization `ĥ = h(z + r ·) − (h(z + r ·), 𝐟)` -/
def normField (f : TestC) (h : DistC) (z : ℂ) (r : ℝ) : DistC :=
  addConst (rescaledField h z r) (-(rescaledField h z r f))

/-- GM's normalizing constant `(ĥ ∘ F⁻¹)_{𝐟,1}(0)` -/
def gmConst (φ : ℂ → ℂ) (z : ℂ) (r s : ℝ) (f : TestC) (g : DistC) : ℝ :=
  invPullSmoothAvg (ball (0 : ℂ) (s / r)) (normMap φ z r) g f
    (inv_pos.2 (norm_pos_iff.2 (one_ne_zero : (1 : ℂ) ≠ 0)))

theorem measurable_gmConst (φ : ℂ → ℂ) (z : ℂ) (r s : ℝ) (f : TestC) :
    Measurable (gmConst φ z r s f) := by
  unfold gmConst invPullSmoothAvg SupercriticalConformalCovariance.GM24.invPullPair
  split_ifs
  · exact LQGMetric.GFFInv.measurable_pair _
  · exact measurable_const

theorem measurable_rescaledField_apply (z : ℂ) (r : ℝ) (f : TestC) :
    Measurable (fun h : DistC => rescaledField h z r f) :=
  (LQGMetric.GFFInv.measurable_pair f).comp (LQGMetric.measurable_affineComp r z)

theorem measurable_normField (f : TestC) (z : ℂ) (r : ℝ) :
    Measurable (fun h : DistC => normField f h z r) := by
  refine LQGMetric.GFFInv.measurable_distC_iff.2 fun ψ => ?_
  simp only [normField, LQGMetric.GFFInv.addConst_apply]
  exact ((LQGMetric.GFFInv.measurable_pair ψ).comp (LQGMetric.measurable_affineComp r z)).add
    (measurable_const.mul (measurable_rescaledField_apply z r f).neg)

/-- the normalizing constant `C = (h(z + r ·), 𝐟) + Q log ρ + c₀` -/
def rescConst (Q : ℝ) (φ : ℂ → ℂ) (z : ℂ) (r s : ℝ) (f : TestC) (h : DistC) : ℝ :=
  rescaledField h z r f + Q * Real.log (r * ‖deriv φ z‖) + gmConst φ z r s f (normField f h z r)

/-- the normalized whole-plane field `G = g₀ + χ_m (k − Q log |(φ⁻¹)′|) − C` -/
def rescG (Q : ℝ) {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V) (m : ℕ)
    (z : ℂ) (r s : ℝ) (f : TestC) (h g₀ : DistC) (k : C(V, ℝ)) : DistC :=
  addFun g₀ (cutF V m k - cutF V m (SupercriticalConformalCovariance.BiLip.PortTan.logDerivInv Q hφ) -
    ContinuousMap.const ℂ (rescConst Q φ z r s f h))

/-- the rescaled field `G′ = G(φ(z) + a ·) + Q log |a|` -/
def rescG' (Q : ℝ) {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V) (m : ℕ)
    (z : ℂ) (r s : ℝ) (f : TestC) (h g₀ : DistC) (k : C(V, ℝ)) : DistC :=
  addConst (GaussianLQG.rotDist (((r : ℂ) * deriv φ z) / ((‖(r : ℂ) * deriv φ z‖ : ℝ) : ℂ))
    (affineComp ‖(r : ℂ) * deriv φ z‖ (φ z) (rescG Q hφ m z r s f h g₀ k)))
    (Q * Real.log ‖(r : ℂ) * deriv φ z‖)

theorem norm_a_eq {φ : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r) :
    ‖(r : ℂ) * deriv φ z‖ = r * ‖deriv φ z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

section Main

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

theorem measurable_rescConst (Q : ℝ) (φ : ℂ → ℂ) (z : ℂ) (r s : ℝ) (f : TestC) :
    Measurable (rescConst Q φ z r s f) :=
  ((measurable_rescaledField_apply z r f).add measurable_const).add
    ((measurable_gmConst φ z r s f).comp (measurable_normField f z r))

theorem kF_bounds {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V) {m : ℕ}
    {z : ℂ} {r s ε : ℝ} (hG : GeomGood φ U z r ε) (hε : ε ≤ 1 / 32)
    (hm : closedBall (φ z) (3 * (r * ‖deriv φ z‖)) ⊆ exW V m) (f : TestC) (h : DistC)
    (k : C(V, ℝ)) (y : ℂ) (hy : y ∈ ball (φ z) (3 * (r * ‖deriv φ z‖))) :
    let F := cutF V m k - cutF V m (SupercriticalConformalCovariance.BiLip.PortTan.logDerivInv Q hφ) -
      ContinuousMap.const ℂ (rescConst Q φ z r s f h)
    let c := Q * Real.log r + rescaledField h z r f + gmConst φ z r s f (normField f h z r)
    c - 2 * |Q| * ε ≤ k ⟨y, SupercriticalConformalCovariance.Domain.exW_subset _ m (hm (ball_subset_closedBall hy))⟩ - F y ∧
      k ⟨y, SupercriticalConformalCovariance.Domain.exW_subset _ m (hm (ball_subset_closedBall hy))⟩ - F y ≤ c + 2 * |Q| * ε := by
  intro F c
  have hr := hG.1
  have hφd : 0 < ‖deriv φ z‖ := norm_pos_iff.2 hG.2.1
  have hyW : y ∈ exW (V : Set ℂ) m := hm (ball_subset_closedBall hy)
  have hFy : F y = k ⟨y, SupercriticalConformalCovariance.Domain.exW_subset _ m hyW⟩ -
      SupercriticalConformalCovariance.BiLip.PortTan.logDerivInv Q hφ ⟨y, SupercriticalConformalCovariance.Domain.exW_subset _ m hyW⟩ -
        rescConst Q φ z r s f h := by
    simp only [F, ContinuousMap.sub_apply, ContinuousMap.const_apply,
      SupercriticalConformalCovariance.Domain.cutF_eq V m _ y hyW]
  have hlog := log_deriv_inv_bound hG (by linarith) U.isOpen hφ.1 hφ.2.injOn
    (ball_subset_closedBall hy)
  have hL : SupercriticalConformalCovariance.BiLip.PortTan.logDerivInv Q hφ ⟨y, SupercriticalConformalCovariance.Domain.exW_subset _ m hyW⟩ =
      Q * Real.log ‖deriv (Function.invFunOn φ (U : Set ℂ)) y‖ := rfl
  rw [hFy, hL]
  have hρ : Real.log (r * ‖deriv φ z‖) = Real.log r + Real.log ‖deriv φ z‖ :=
    Real.log_mul hr.ne' hφd.ne'
  simp only [rescConst, hρ]
  have hQb : |Q * (Real.log ‖deriv (Function.invFunOn φ (U : Set ℂ)) y‖ + Real.log ‖deriv φ z‖)| ≤
      |Q| * (2 * ε) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hlog (abs_nonneg Q)
  rw [abs_le] at hQb
  simp only [c]
  constructor <;> nlinarith [hQb.1, hQb.2]

end Main

section Rescaled

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

theorem annulus_eq_of_eq {c c' : ℂ} {a b a' b' : ℝ} (h₁ : c = c') (h₂ : a = a') (h₃ : b = b')
    (p : 0 < a ∧ a < b) (p' : 0 < a' ∧ a' < b') :
    (⟨(c, a, b), p⟩ : EuclideanAnnulus) = ⟨(c', a', b'), p'⟩ := by
  subst h₁ h₂ h₃; rfl

/-- **One instance at one scale, rescaled** (l. 112–123). -/
theorem ae_rescaled (hQ : IsLFPPExponent ξ Q) (hD : IsStrongLQGMetric ξ Q D)
    {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h g₀ : Ω → DistC} {k : Ω → C(V, ℝ)}
    (hI : IsInstance Q U V hφ P h g₀ k) {z : ℂ} {r s ε : ℝ} (hs : 0 < s) (hzs : ball z s ⊆ U)
    (hG : GeomGood φ U z r ε) (hε : ε ≤ 1 / 32) (h4 : 4 * r < s) {m : ℕ}
    (hm : closedBall (φ z) (3 * (r * ‖deriv φ z‖)) ⊆ exW V m) (f : TestC)
    (hFd : DifferentiableOn ℂ (normMap φ z r) (ball 0 (s / r)))
    (hFi : InjOn (normMap φ z r) (ball 0 (s / r)))
    (hOimg : (ballO 0 3 : Set ℂ) ⊆ normMap φ z r '' ball 0 (s / r)) :
    ∀ᵐ ω ∂P,
      restrictTo (ballO 0 3) (rescG' Q hφ m z r s f (h ω) (g₀ ω) (k ω)) =
          invPullDist isOpen_ball hFd hFi (ballO 0 3) hOimg (normField f (h ω) z r) -
            gmConst φ z r s f (normField f (h ω) z r) • intDist (ballO 0 3) ∧
      tAround (D (g₀ ω)) ξ (k ω) (φ z) (9 / 8 * (r * ‖deriv φ z‖)) (15 / 8 * (r * ‖deriv φ z‖)) ≤
          ENNReal.ofReal (Real.exp (ξ * (Q * Real.log r + rescaledField (h ω) z r f +
              gmConst φ z r s f (normField f (h ω) z r) + 2 * |Q| * ε))) *
            aroundDist (D (rescG' Q hφ m z r s f (h ω) (g₀ ω) (k ω)))
              ⟨((0 : ℂ), 9 / 8, 15 / 8), by norm_num, by norm_num⟩ ∧
      ENNReal.ofReal (Real.exp (ξ * (Q * Real.log r + rescaledField (h ω) z r f +
              gmConst φ z r s f (normField f (h ω) z r) - 2 * |Q| * ε))) *
            acr (D (rescG' Q hφ m z r s f (h ω) (g₀ ω) (k ω))) 0 (5 / 8) (7 / 8) ≤
        tAcr (D (g₀ ω)) ξ (k ω) (φ z) (5 / 8 * (r * ‖deriv φ z‖)) (7 / 8 * (r * ‖deriv φ z‖)) := by
  have hr := hG.1
  have hφd := hG.2.1
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  set a : ℂ := (r : ℂ) * deriv φ z with ha_def
  have ha : a ≠ 0 := mul_ne_zero hrC hφd
  have hna : ‖a‖ = r * ‖deriv φ z‖ := norm_a_eq hr
  set ρ := r * ‖deriv φ z‖ with hρ
  have hρpos : 0 < ρ := mul_pos hr (norm_pos_iff.2 hφd)
  obtain ⟨hhn, hR⟩ := hI
  have hh := hhn.1
  set C : Ω → ℝ := fun ω => rescConst Q φ z r s f (h ω) with hC
  have hCm : Measurable C := (measurable_rescConst Q φ z r s f).comp hh.measurable
  set B : Opens ℂ := ballO (φ z) (3 * ρ) with hBdef
  have hBm : B ≤ exWO V m := fun y hy => hm (ball_subset_closedBall hy)
  have hBimg : (B : Set ℂ) ⊆ φ '' U := ballO_subset_image hG hφ.2.injOn
  have hnf := SupercriticalConformalCovariance.BiLip.PortTan.ae_restrictTo_normField Q hφ (h := h) (hbar := g₀) (fr := k) hR m
    hBm hBimg C
  -- the field `G` is a GFF plus a continuous function
  set Fg : Ω → C(ℂ, ℝ) := fun ω => cutF V m (k ω) - cutF V m (SupercriticalConformalCovariance.BiLip.PortTan.logDerivInv Q hφ) -
    ContinuousMap.const ℂ (C ω) with hFgdef
  have hFgm : Measurable Fg := by
    have hk := SupercriticalConformalCovariance.Domain.measurable_cutExt V.isOpen (SupercriticalConformalCovariance.Domain.tsupport_cutoff_subset (V : Set ℂ) m)
      hR.2.2.1
    rw [ContinuousMap.measurable_iff_eval] at hk ⊢
    intro x
    simp only [hFgdef, ContinuousMap.sub_apply, ContinuousMap.const_apply]
    exact ((hk x).sub measurable_const).sub hCm
  have hGc : IsGFFPlusCont (fun ω => rescG Q hφ m z r s f (h ω) (g₀ ω) (k ω)) P :=
    SupercriticalConformalCovariance.Domain.isGFFPlusCont_addFun_of_measurable hR.2.1 hFgm
  have hrot := SupercriticalConformalCovariance.Rotation.ae_complex_affine_covariance ξ Q hQ D hD P _ hGc a ha (φ z)
  filter_upwards [hnf, hrot, SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P g₀ hR.2.1]
    with ω hω1 hω2 hs₀
  obtain ⟨hf₀, hL₀, hWeyl⟩ := hs₀
  have hξ0 : (0 : ℝ) ≤ ξ := le_of_lt ξ.2
  -- the metric covariance in the form of `aroundDist_affine`
  have hT : ∀ x y : ℂ, D (rescG Q hφ m z r s f (h ω) (g₀ ω) (k ω)) (φ z + a * x, φ z + a * y) =
      D (rescG' Q hφ m z r s f (h ω) (g₀ ω) (k ω)) (x, y) := by
    intro x y
    have := hω2 x y
    rw [add_comm (a * x), add_comm (a * y)] at this
    exact this
  -- the Weyl comparison on `B_{3ρ}(φ z)`
  have hE : ∀ q, D (rescG Q hφ m z r s f (h ω) (g₀ ω) (k ω)) q =
      weylScale (ξ : ℝ) (Fg ω) (D (g₀ ω)) q := fun q => (congrFun (hWeyl (Fg ω)) q).symm
  have hRV : ball (φ z) (3 * ρ) ⊆ (V : Set ℂ) := fun y hy =>
    SupercriticalConformalCovariance.Domain.exW_subset _ m (hm (ball_subset_closedBall hy))
  have hkF : ∀ y (hy : y ∈ ball (φ z) (3 * ρ)),
      Q * Real.log r + rescaledField (h ω) z r f + gmConst φ z r s f (normField f (h ω) z r) -
          2 * |Q| * ε ≤ k ω ⟨y, hRV hy⟩ - Fg ω y ∧
        k ω ⟨y, hRV hy⟩ - Fg ω y ≤
          Q * Real.log r + rescaledField (h ω) z r f + gmConst φ z r s f (normField f (h ω) z r) +
            2 * |Q| * ε := fun y hy =>
    kF_bounds hφ hG hε hm f (h ω) (k ω) y hy
  refine ⟨?_, ?_, ?_⟩
  · -- the field identity
    have hgeomB : ∀ x ∈ (U : Set ℂ), φ x ∈ ball (φ z) (3 * (r * ‖deriv φ z‖)) → x ∈ ball z s :=
      fun x hx hxB => preimage_mem_ball hG hφ.2.injOn h4 hx hxB
    have key := rescaled_restrict_eq hφ.1 hφ.2.injOn hs hr hzs hgeomB hBimg hOimg hFd hFi f (h ω)
      (rescG Q hφ m z r s f (h ω) (g₀ ω) (k ω)) (C ω) Q hω1
    rw [rescG', key]
    congr 2
    have e : ‖(r : ℂ) * deriv φ z‖ = r * ‖deriv φ z‖ := norm_a_eq hr
    simp only [hC, rescConst, rescaledField, e]
    ring
  · -- the around bound
    have hna0 : 0 < ‖a‖ := norm_pos_iff.2 ha
    rw [show 9 / 8 * ρ = ‖a‖ * (9 / 8) by rw [hna]; ring,
      show 15 / 8 * ρ = ‖a‖ * (15 / 8) by rw [hna]; ring]
    have h1 := tAround_le (k ω) hξ0 hf₀ V.isOpen hE hRV hkF (φ z)
      (mul_pos hna0 (by norm_num : (0 : ℝ) < 9 / 8))
      (mul_lt_mul_of_pos_left (by norm_num : (9 / 8 : ℝ) < 15 / 8) hna0)
      (fun y hy => (ball_subset_ball (by rw [hna]; linarith)) hy.1)
    have h2 := aroundDist_affine ha (D (rescG Q hφ m z r s f (h ω) (g₀ ω) (k ω)))
      (D (rescG' Q hφ m z r s f (h ω) (g₀ ω) (k ω))) hT (α := 9 / 8) (β := 15 / 8)
      (by norm_num) (by norm_num)
    rw [h2] at h1
    exact h1
  · -- the across bound
    have h1 := le_tAcr (k ω) hξ0 hf₀ hL₀ V.isOpen hE hRV hkF (φ z) (5 / 8 * ρ) (7 / 8 * ρ)
      (fun y hy => (closedBall_subset_ball (by linarith)) hy.1)
    have h2 := acr_affine ha (D (rescG Q hφ m z r s f (h ω) (g₀ ω) (k ω)))
      (D (rescG' Q hφ m z r s f (h ω) (g₀ ω) (k ω))) hT (5 / 8) (7 / 8)
    rw [show 5 / 8 * ρ = ‖a‖ * (5 / 8) by rw [hna]; ring,
      show 7 / 8 * ρ = ‖a‖ * (7 / 8) by rw [hna]; ring, h2] at h1
    rw [show 5 / 8 * ρ = ‖a‖ * (5 / 8) by rw [hna]; ring,
      show 7 / 8 * ρ = ‖a‖ * (7 / 8) by rw [hna]; ring]
    exact h1

end Rescaled

end SupercriticalConformalCovariance.BiLip
