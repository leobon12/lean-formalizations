import SupercriticalConformalCovariance.BiLip.Affine
import SupercriticalConformalCovariance.BiLip.Geom
import SupercriticalConformalCovariance.GM24.AsConv
import GaussianLQG.Metric.Rotation
import LQGMetric.Field.GFFInvariance
import LQGMetric.Field.HarmExistA
import SmallGammaGeodesics.CC.ExtensionPull
import SupercriticalConformalCovariance.Domain.Cutoff

/-!
# Lemma 2.1, step 2: the rescaled target field is GM's normalized transformed field

Paper l. 112–119. For a centre `z`, a radius `r`, `a = r φ′(z)`, `ρ = |a|`, the normalized map
`F(w) = (φ(z + r w) − φ(z))/a` on `B_{s/r}(0)` (`B_s(z) ⊆ U`), the source field rescaled at `(z, r)`,
`ĥ′ = h(z + r ·)`, and its smooth normalization `ĥ = ĥ′ − (ĥ′, 𝐟)`:

`rescaled_restrict_eq`: if a whole-plane `G` restricts on `B_{3ρ}(φ z)` to `(h ∘ φ⁻¹) − C`, then
`G′ = G(φ(z) + a ·) + Q log |a|` (the affine-covariance modules' representation `addConst (rotDist (a/|a|) (affineComp |a| (φ z) G))
(Q log |a|)`) restricts on `B_3(0)` to `(ĥ ∘ F⁻¹) − (C − Q log ρ − (ĥ′, 𝐟))`.

This is "the constant factor `φ′_n(z_n)` is removed exactly by affine covariance, including the
`Q log |φ′_n(z_n)|` term" at the level of fields: with `C = (ĥ′, 𝐟) + Q log ρ + c` the restriction is exactly
GM's `(ĥ ∘ F⁻¹ − c)|_{B_3}` of Lemma 2.4 (2.6) (`tendsto_tvDist_gm24_open`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open LQGMetric (DistC DistOn TestC TestOn restrictTo addConst affineComp)
open SmallGammaGeodesics.CC (confPullFun confPullTest coe_confPullTest intDist intDist_apply
  integral_confPullFun)
open SupercriticalConformalCovariance.GM24 (invPullDist invPullPair invPullPair_eq invPullDist_apply)

/-- the normalized map at `(z, r)` -/
def normMap (φ : ℂ → ℂ) (z : ℂ) (r : ℝ) (w : ℂ) : ℂ :=
  (φ (z + (r : ℂ) * w) - φ z) / ((r : ℂ) * deriv φ z)

/-- **The conformal pullbacks correspond under the affine rescalings**: for `x ∉ B_s(z)` the right side
vanishes because `φ(x) ∉ B_{3ρ}(φ z)`. -/
theorem confPullFun_normMap {φ : ℂ → ℂ} {U : Set ℂ} {z : ℂ} {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hzs : ball z s ⊆ U) (hd : DifferentiableOn ℂ φ (ball z s)) (hi : InjOn φ (ball z s))
    (hgeomB : ∀ x ∈ U, φ x ∈ ball (φ z) (3 * (r * ‖deriv φ z‖)) → x ∈ ball z s)
    (g : ℂ → ℝ) (hg : ∀ w, g w ≠ 0 → ‖w‖ < 3) (x : ℂ) :
    confPullFun (normMap φ z r) (ball 0 (s / r)) g ((x - z) / r) =
      (r ^ 2 / (r * ‖deriv φ z‖) ^ 2) *
        confPullFun φ U (fun y => g ((y - φ z) / ((r : ℂ) * deriv φ z))) x := by
  obtain ⟨hφd, hinto, hFd, hFi, hF0, hF1, hFder⟩ := normalized_props hs hr hd hi
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hφn : 0 < ‖deriv φ z‖ := norm_pos_iff.2 hφd
  have hxw : z + (r : ℂ) * ((x - z) / r) = x := by field_simp; ring
  by_cases hx : (x - z) / (r : ℂ) ∈ ball (0 : ℂ) (s / r)
  · have hxs : x ∈ ball z s := by rw [← hxw]; exact hinto _ hx
    have hD : deriv (normMap φ z r) ((x - z) / (r : ℂ)) =
        deriv φ (z + (r : ℂ) * ((x - z) / (r : ℂ))) / deriv φ z := hFder _ hx
    rw [SmallGammaGeodesics.CC.confPullFun_of_mem hx,
      SmallGammaGeodesics.CC.confPullFun_of_mem (hzs hxs), hD, hxw]
    have hF : normMap φ z r ((x - z) / (r : ℂ)) = (φ x - φ z) / ((r : ℂ) * deriv φ z) := by
      rw [normMap, hxw]
    rw [hF, norm_div]
    field_simp
  · rw [SmallGammaGeodesics.CC.confPullFun_of_notMem hx]
    by_cases hxU : x ∈ U
    · rw [SmallGammaGeodesics.CC.confPullFun_of_mem hxU]
      have hgz : g ((φ x - φ z) / ((r : ℂ) * deriv φ z)) = 0 := by
        by_contra hne
        have h3 := hg _ hne
        have hxB : φ x ∈ ball (φ z) (3 * (r * ‖deriv φ z‖)) := by
          rw [mem_ball, dist_eq_norm]
          rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
            div_lt_iff₀ (by positivity)] at h3
          linarith
        have hxs := hgeomB x hxU hxB
        apply hx
        rw [mem_ball, dist_zero_right, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr, div_lt_div_iff_of_pos_right hr, ← dist_eq_norm]
        exact mem_ball.1 hxs
      rw [hgz]; ring
    · rw [SmallGammaGeodesics.CC.confPullFun_of_notMem hxU, mul_zero]

/-- an open ball as an element of `Opens ℂ` -/
def ballO (c : ℂ) (R : ℝ) : Opens ℂ := ⟨ball c R, isOpen_ball⟩

/-- `∫ g(T⁻¹ ·) = |a|² ∫ g` for the affine `T(u) = c + a u` -/
theorem integral_affine_pull (c a : ℂ) (ha : a ≠ 0) (g : ℂ → ℝ) :
    ∫ x, g ((x - c) / a) = ‖a‖ ^ 2 * ∫ w, g w := by
  have hT : DifferentiableOn ℂ (fun u : ℂ => c + a * u) univ := by fun_prop
  have hTi : InjOn (fun u : ℂ => c + a * u) univ := fun u _ v _ h => by
    simpa [ha] using h
  have h := integral_confPullFun (ϕ := fun u : ℂ => c + a * u) (W := univ) isOpen_univ hT hTi
    (g := fun x => g ((x - c) / a)) (fun y hy => absurd ⟨(y - c) / a, mem_univ _, by
      field_simp; ring⟩ hy)
  rw [← h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  rw [SmallGammaGeodesics.CC.confPullFun_of_mem (mem_univ w)]
  have hder : deriv (fun u : ℂ => c + a * u) w = a := by
    have : HasDerivAt (fun u : ℂ => c + a * u) a w := by
      simpa using ((hasDerivAt_id w).const_mul a).const_add c
    exact this.deriv
  simp only [hder]
  congr 2
  field_simp
  ring

/-- **The field identity**: the affinely rescaled whole-plane field restricts on `B_3(0)` to the conformal
pullback of the rescaled source field, minus an explicit constant. -/
theorem rescaled_restrict_eq {U : Opens ℂ} {φ : ℂ → ℂ} (hd : DifferentiableOn ℂ φ U)
    (hi : InjOn φ U) {z : ℂ} {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (hzs : ball z s ⊆ U)
    (hgeomB : ∀ x ∈ (U : Set ℂ), φ x ∈ ball (φ z) (3 * (r * ‖deriv φ z‖)) → x ∈ ball z s)
    (hBimg : (ballO (φ z) (3 * (r * ‖deriv φ z‖)) : Set ℂ) ⊆ φ '' U)
    (hOimg : (ballO 0 3 : Set ℂ) ⊆ normMap φ z r '' ball 0 (s / r))
    (hFd : DifferentiableOn ℂ (normMap φ z r) (ball 0 (s / r)))
    (hFi : InjOn (normMap φ z r) (ball 0 (s / r))) (f : TestC) (h G : DistC) (C Q : ℝ)
    (hG : restrictTo (ballO (φ z) (3 * (r * ‖deriv φ z‖))) G =
      invPullDist U.isOpen hd hi (ballO (φ z) (3 * (r * ‖deriv φ z‖))) hBimg h -
        C • intDist (ballO (φ z) (3 * (r * ‖deriv φ z‖)))) :
    restrictTo (ballO 0 3) (addConst (GaussianLQG.rotDist (((r : ℂ) * deriv φ z) /
        ((‖(r : ℂ) * deriv φ z‖ : ℝ) : ℂ)) (affineComp ‖(r : ℂ) * deriv φ z‖ (φ z) G))
        (Q * Real.log ‖(r : ℂ) * deriv φ z‖)) =
      invPullDist isOpen_ball hFd hFi (ballO 0 3) hOimg
          (addConst (affineComp r z h) (-(affineComp r z h f))) -
        (C - Q * Real.log ‖(r : ℂ) * deriv φ z‖ - affineComp r z h f) • intDist (ballO 0 3) := by
  have hzU : z ∈ (U : Set ℂ) := hzs (mem_ball_self hs)
  have hφd : deriv φ z ≠ 0 := QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn U.isOpen hd hi hzU
  set a : ℂ := (r : ℂ) * deriv φ z with ha_def
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have ha : a ≠ 0 := mul_ne_zero hrC hφd
  set ρ : ℝ := ‖a‖ with hρ_def
  have hρ : 0 < ρ := norm_pos_iff.2 ha
  have hρr : ρ = r * ‖deriv φ z‖ := by
    rw [hρ_def, ha_def, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  set u : ℂ := a / (ρ : ℂ) with hu_def
  have hu : u ≠ 0 := div_ne_zero ha hρC
  ext g
  set gC : TestC := TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := ballO 0 3) (Ω₂ := ⊤) g
    with hgC
  have hgCc : ⇑gC = ⇑g := SupercriticalConformalCovariance.Domain.coe_monoCLM le_top g
  -- the test function `g ∘ T⁻¹`
  set gT : TestC := LQGMetric.testAffinePull ρ (φ z) (GaussianLQG.testRot u gC) with hgT
  have hgTv : ∀ x, gT x = g ((x - φ z) / a) := by
    intro x
    rw [hgT, LQGMetric.testAffinePull_apply ρ (φ z) hρ.ne', GaussianLQG.testRot_apply hu,
      show gC = gC from rfl, hgCc]
    congr 1
    rw [hu_def]
    field_simp
  have hgsupp : ∀ w, g w ≠ 0 → ‖w‖ < 3 := by
    intro w hw
    have := g.tsupport_subset (subset_tsupport _ hw)
    simpa [ballO] using this
  have hgTsupp : tsupport (gT : ℂ → ℝ) ⊆ ballO (φ z) (3 * (r * ‖deriv φ z‖)) := by
    have hK : IsCompact ((fun w => φ z + a * w) '' tsupport (g : ℂ → ℝ)) :=
      g.hasCompactSupport.isCompact.image (by fun_prop)
    refine (closure_minimal ?_ hK.isClosed).trans ?_
    · intro x hx
      refine ⟨(x - φ z) / a, subset_tsupport _ ?_, ?_⟩
      · rw [Function.mem_support, ← hgTv]; exact hx
      · field_simp; ring
    · rintro _ ⟨w, hw, rfl⟩
      have hw3 : ‖w‖ < 3 := by
        have := g.tsupport_subset hw
        simpa [ballO] using this
      show φ z + a * w ∈ ball (φ z) (3 * (r * ‖deriv φ z‖))
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, ← hρ_def, ← hρr]
      nlinarith
  -- the left side
  have hL : restrictTo (ballO 0 3) (addConst (GaussianLQG.rotDist u (affineComp ρ (φ z) G))
      (Q * Real.log ρ)) g = (ρ ^ 2)⁻¹ * G gT + (∫ x, g x) * (Q * Real.log ρ) := by
    show addConst _ _ gC = _
    rw [LQGMetric.GFFInv.addConst_apply, GaussianLQG.rotDist_apply,
      LQGMetric.GFFInv.affineComp_apply, hgCc]
  -- `G gT` through the restriction to `B`
  have hGT : G gT = h (confPullTest U.isOpen hd hi gT (hgTsupp.trans hBimg)) -
      C * ∫ x, gT x := by
    rw [← LQGMetric.HarmExist.restrictTo_testOnHE _ G gT hgTsupp, hG, sub_apply, smul_apply,
      intDist_apply, invPullDist_apply, smul_eq_mul]
    have hcoe : ⇑(TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤)
        (Ω₁ := ballO (φ z) (3 * (r * ‖deriv φ z‖))) (Ω₂ := ⊤)
        (LQGMetric.HarmExist.testOnHE _ gT hgTsupp)) = ⇑gT :=
      SupercriticalConformalCovariance.Domain.coe_monoCLM le_top _
    have hsupp' : tsupport (⇑(TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤)
        (Ω₁ := ballO (φ z) (3 * (r * ‖deriv φ z‖))) (Ω₂ := ⊤)
        (LQGMetric.HarmExist.testOnHE _ gT hgTsupp))) ⊆ φ '' U := by
      rw [hcoe]; exact hgTsupp.trans hBimg
    rw [invPullPair_eq U.isOpen hd hi h hsupp']
    have e : confPullTest U.isOpen hd hi _ hsupp' =
        confPullTest U.isOpen hd hi gT (hgTsupp.trans hBimg) := by
      ext x
      simp only [coe_confPullTest]
      rw [hcoe]
    rw [e]
    rfl
  -- the right side
  have hgCsupp : tsupport (gC : ℂ → ℝ) ⊆ normMap φ z r '' ball 0 (s / r) := by
    rw [hgCc]; exact g.tsupport_subset.trans hOimg
  have hR1 : invPullDist isOpen_ball hFd hFi (ballO 0 3) hOimg
      (addConst (affineComp r z h) (-(affineComp r z h f))) g =
      (r ^ 2)⁻¹ * h (LQGMetric.testAffinePull r z
        (confPullTest isOpen_ball hFd hFi gC hgCsupp)) -
        (∫ x, g x) * (affineComp r z h f) := by
    rw [invPullDist_apply, invPullPair_eq isOpen_ball hFd hFi _ hgCsupp,
      LQGMetric.GFFInv.addConst_apply, LQGMetric.GFFInv.affineComp_apply, coe_confPullTest,
      integral_confPullFun isOpen_ball hFd hFi (fun y hy => image_eq_zero_of_notMem_tsupport
        fun hy' => hy (hgCsupp hy')), hgCc]
    ring
  have hfun : LQGMetric.testAffinePull r z (confPullTest isOpen_ball hFd hFi gC hgCsupp) =
      (r ^ 2 / ρ ^ 2) • confPullTest U.isOpen hd hi gT (hgTsupp.trans hBimg) := by
    ext x
    rw [LQGMetric.testAffinePull_apply r z hr.ne', coe_confPullTest, smul_apply,
      coe_confPullTest, smul_eq_mul, hgCc]
    rw [confPullFun_normMap hs hr hzs (hd.mono hzs) (hi.mono hzs) hgeomB g hgsupp x, ← hρr]
    congr 1
    congr 1
    funext y
    rw [hgTv]
  have hR2 : invPullDist isOpen_ball hFd hFi (ballO 0 3) hOimg
      (addConst (affineComp r z h) (-(affineComp r z h f))) g =
      (ρ ^ 2)⁻¹ * h (confPullTest U.isOpen hd hi gT (hgTsupp.trans hBimg)) -
        (∫ x, g x) * (affineComp r z h f) := by
    rw [hR1, hfun, map_smul, smul_eq_mul]
    field_simp
  have hint : ∫ x, gT x = ρ ^ 2 * ∫ x, g x := by
    simp only [hgTv]
    exact integral_affine_pull (φ z) a ha g
  rw [sub_apply, smul_apply, intDist_apply, smul_eq_mul, hR2]
  rw [show (GaussianLQG.rotDist (((r : ℂ) * deriv φ z) / ((‖(r : ℂ) * deriv φ z‖ : ℝ) : ℂ))
      (affineComp ‖(r : ℂ) * deriv φ z‖ (φ z) G)) = GaussianLQG.rotDist u (affineComp ρ (φ z) G)
      from rfl, hL, hGT, hint]
  field_simp
  ring

end SupercriticalConformalCovariance.BiLip
