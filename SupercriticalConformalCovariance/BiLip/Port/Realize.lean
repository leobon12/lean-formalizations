import SupercriticalConformalCovariance.GM24.Main
import SupercriticalConformalCovariance.GM24.Bridge
import SupercriticalConformalCovariance.Frozen.ConfPullbackField
import SupercriticalConformalCovariance.Domain.Axioms
import SupercriticalConformalCovariance.Lemma31.Realized
import QuantumZipper.Proofs.Complex.BasicsUnivalent

/-!
# Lemma 3.3, steps 1–2: the transformed field near a fixed disk

Paper l. 206–215. For a conformal bijection `ψ : U → V` and a realization `(h̄, f)` of
`h^ψ = h ∘ ψ⁻¹ + Q log |(ψ⁻¹)′|` on `V` (candidate `confPullbackField` of the inverse bijection,
`IsDomainRealization`), and an open `B` inside a cut-off window `exW V m`, the whole-plane field

  `G = h̄ + χ_m (f − Q log |(ψ⁻¹)′|) − c`

(`c` any random constant) restricts on `B` to `(h ∘ ψ⁻¹)|_B − c` (`ae_restrictTo_normField`). With
`c` the smooth average `(h ∘ ψ⁻¹)_{𝐟,|a|}(0)`, this is exactly GM's normalized transformed field of
Lemma 2.4 (2.6) (`nrm` of `invPullDist`), so its law is controlled by (2.6) and its
coordinates converge by (2.5).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric Function
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip.PortTan

open LQGMetric (DistC DistOn TestOn TestC restrictTo addFun ofCont IsGFFPlusCont)
open SupercriticalConformalCovariance (IsConformalBijection confPushTest confPullbackField
  IsDomainRealization)
open SupercriticalConformalCovariance.Domain (cutF exW exWO exWO_le cutF_eq coe_monoCLM ae_restrictTo_cutF ofFun_extZ_apply
  ofCont_add)
open SupercriticalConformalCovariance.GM24 (invPullDist isConformalBijection_invFunOn distPullback_inv_eq
  subset_image_of_isConformalBijection)
open SmallGammaGeodesics.CC (intDist intDist_apply coe_confPullOnCLM)

variable {ψ : ℂ → ℂ} {U V : Opens ℂ}

/-- The derivative of the inverse of a conformal bijection does not vanish on `V`. -/
theorem deriv_invFunOn_ne_zero (hψ : IsConformalBijection ψ U V) {y : ℂ} (hy : y ∈ (V : Set ℂ)) :
    deriv (invFunOn ψ (U : Set ℂ)) y ≠ 0 :=
  QuantumZipper.CA.deriv_ne_zero_of_injOn V.isOpen (isConformalBijection_invFunOn hψ).1
    (isConformalBijection_invFunOn hψ).2.injOn hy

theorem continuousOn_logDerivInv (Q : ℝ) (hψ : IsConformalBijection ψ U V) :
    ContinuousOn (fun y => Q * Real.log ‖deriv (invFunOn ψ (U : Set ℂ)) y‖) (V : Set ℂ) := by
  have hd := ((isConformalBijection_invFunOn hψ).1.deriv V.isOpen).continuousOn
  refine continuousOn_const.mul ((hd.norm).log fun y hy => ?_)
  exact norm_ne_zero_iff.2 (deriv_invFunOn_ne_zero hψ hy)

/-- `Q log |(ψ⁻¹)′|` as a continuous function on `V`. -/
def logDerivInv (Q : ℝ) (hψ : IsConformalBijection ψ U V) : C(V, ℝ) :=
  ⟨fun y => Q * Real.log ‖deriv (invFunOn ψ (U : Set ℂ)) (y : ℂ)‖,
    (continuousOn_iff_continuous_domRestrict.1 (continuousOn_logDerivInv Q hψ))⟩

theorem logDerivInv_apply (Q : ℝ) (hψ : IsConformalBijection ψ U V) (y : V) :
    logDerivInv Q hψ y = Q * Real.log ‖deriv (invFunOn ψ (U : Set ℂ)) (y : ℂ)‖ := rfl

/-- The `ofFun` term of `confPullbackField` is the `ofFun` of the continuous function on `V`. -/
theorem ofFun_logDeriv_eq (Q : ℝ) (hψ : IsConformalBijection ψ U V) :
    Distribution.ofFun V (fun x => Q * Real.log ‖deriv (invFunOn ψ (U : Set ℂ)) x‖) volume ⊤ =
      Distribution.ofFun V (Function.extend Subtype.val (logDerivInv Q hψ) 0) volume ⊤ := by
  ext φ
  have hloc1 : LocallyIntegrableOn (fun x => Q * Real.log ‖deriv (invFunOn ψ (U : Set ℂ)) x‖)
      (V : Set ℂ) volume :=
    (continuousOn_logDerivInv Q hψ).locallyIntegrableOn V.isOpen.measurableSet
  have hloc2 : LocallyIntegrableOn (Function.extend Subtype.val (logDerivInv Q hψ) 0)
      (V : Set ℂ) volume :=
    (SupercriticalConformalCovariance.Domain.continuousOn_extZ (logDerivInv Q hψ)).locallyIntegrableOn V.isOpen.measurableSet
  rw [Distribution.ofFun_apply hloc1, Distribution.ofFun_apply hloc2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  by_cases hx : x ∈ (V : Set ℂ)
  · congr 1
    rw [show x = ((⟨x, hx⟩ : V) : ℂ) from rfl, Subtype.val_injective.extend_apply]
    rfl
  · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (φ.tsupport_subset h)
    simp [this]

/-- Restricting `invPullDist` from `V` to `B ⊆ V`. -/
theorem invPullDist_monoCLM (hψ : IsConformalBijection ψ U V) {B : Opens ℂ} (hBV : B ≤ V)
    (hB : (B : Set ℂ) ⊆ ψ '' U) (h : DistC) (g : TestOn B) :
    invPullDist U.isOpen hψ.1 hψ.2.injOn V (subset_image_of_isConformalBijection hψ) h
        (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := B) (Ω₂ := V) g) =
      invPullDist U.isOpen hψ.1 hψ.2.injOn B hB h g := by
  rw [invPullDist, invPullDist]
  show h (SmallGammaGeodesics.CC.confPullOnCLM _ _ _ V _ _) =
    h (SmallGammaGeodesics.CC.confPullOnCLM _ _ _ B hB g)
  congr 1
  ext x
  rw [coe_confPullOnCLM, coe_confPullOnCLM, coe_monoCLM hBV]

/-- The transformed field paired with a test function of `V`. -/
theorem confPullbackField_inv_apply (Q : ℝ) (hψ : IsConformalBijection ψ U V) (h : DistC)
    (g : TestOn V) :
    confPullbackField Q (isConformalBijection_invFunOn hψ) (restrictTo U h) g =
      invPullDist U.isOpen hψ.1 hψ.2.injOn V (subset_image_of_isConformalBijection hψ) h g +
        Distribution.ofFun V (Function.extend Subtype.val (logDerivInv Q hψ) 0) volume ⊤ g := by
  rw [confPullbackField, add_apply, ← ofFun_logDeriv_eq Q hψ]
  congr 1
  have := congrArg (fun u : DistOn V => u g) (distPullback_inv_eq hψ h)
  exact this

/-- **The normalized whole-plane representative of the transformed field.** For a realization
`(h̄, f)` of `h^ψ` on `V`, `B ≤ exWO V m`, and any random constant `c`, almost surely
`(h̄ + χ_m (f − Q log |(ψ⁻¹)′|) − c)|_B = (h ∘ ψ⁻¹)|_B − c`. -/
theorem ae_restrictTo_normField (Q : ℝ) (hψ : IsConformalBijection ψ U V)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC} {hbar : Ω → DistC}
    {fr : Ω → C(V, ℝ)}
    (hreal : IsDomainRealization V P
      (fun ω => confPullbackField Q (isConformalBijection_invFunOn hψ) (restrictTo U (h ω)))
      hbar fr)
    (m : ℕ) {B : Opens ℂ} (hBm : B ≤ exWO V m) (hB : (B : Set ℂ) ⊆ ψ '' U) (c : Ω → ℝ) :
    ∀ᵐ ω ∂P, restrictTo B (addFun (hbar ω)
        (cutF V m (fr ω) - cutF V m (logDerivInv Q hψ) - ContinuousMap.const ℂ (c ω))) =
      invPullDist U.isOpen hψ.1 hψ.2.injOn B hB (h ω) - c ω • intDist B := by
  have hBV : B ≤ V := hBm.trans (exWO_le V m)
  filter_upwards [ae_restrictTo_cutF hreal m] with ω hω
  ext g
  set gT : TestC := TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := B) (Ω₂ := ⊤) g with hgT
  set gW : TestOn (exWO V m) :=
    TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := B) (Ω₂ := exWO V m) g with hgW
  set gV : TestOn V :=
    TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := B) (Ω₂ := V) g with hgV
  have hsupp : tsupport (gV : ℂ → ℝ) ⊆ exW V m := by
    rw [hgV, coe_monoCLM hBV]
    exact g.tsupport_subset.trans hBm
  -- the realization, paired with `gV`
  have hreal_g := hω gW
  have e1 : restrictTo (exWO V m) (addFun (hbar ω) (cutF V m (fr ω))) gW =
      addFun (hbar ω) (cutF V m (fr ω)) gT := by
    show addFun (hbar ω) (cutF V m (fr ω)) _ = _
    congr 1
    ext x
    simp only [ContinuousLinearMap.coe_coe]
    rw [coe_monoCLM le_top, hgW, coe_monoCLM hBm, hgT, coe_monoCLM le_top]
  have e2 : TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := exWO V m) (Ω₂ := V) gW = gV := by
    ext x
    rw [coe_monoCLM (exWO_le V m), hgW, coe_monoCLM hBm, hgV, coe_monoCLM hBV]
  rw [e1, e2, confPullbackField_inv_apply Q hψ (h ω) gV, invPullDist_monoCLM hψ hBV hB (h ω) g]
    at hreal_g
  erw [ofFun_extZ_apply V (logDerivInv Q hψ) gV hsupp] at hreal_g
  have e3 : TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) gV = gT := by
    ext x
    rw [coe_monoCLM le_top, hgV, coe_monoCLM hBV, hgT, coe_monoCLM le_top]
  rw [e3] at hreal_g
  -- unfold both sides as integrals
  show addFun (hbar ω) _ gT = _
  have hgTi : ∀ F : C(ℂ, ℝ), Integrable (fun x => gT x * F x) := fun F =>
    (gT.continuous.mul F.continuous).integrable_of_hasCompactSupport
      (gT.hasCompactSupport.mul_right)
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, intDist_apply, smul_eq_mul]
  simp only [addFun, add_apply] at hreal_g ⊢
  rw [LQGMetric.ofCont_apply] at hreal_g ⊢
  rw [LQGMetric.ofCont_apply] at hreal_g
  have hcomb : ∫ x, gT x * (cutF V m (fr ω) - cutF V m (logDerivInv Q hψ) -
      ContinuousMap.const ℂ (c ω)) x =
      (∫ x, gT x * cutF V m (fr ω) x) - (∫ x, gT x * cutF V m (logDerivInv Q hψ) x) -
        c ω * ∫ x, g x := by
    have hint : ∫ x, gT x = ∫ x, g x := by
      congr 1; ext x; rw [hgT, coe_monoCLM le_top]
    have hcI : Integrable (fun x => c ω * gT x) :=
      (gT.continuous.integrable_of_hasCompactSupport gT.hasCompactSupport).const_mul (c ω)
    calc ∫ x, gT x * (cutF V m (fr ω) - cutF V m (logDerivInv Q hψ) -
          ContinuousMap.const ℂ (c ω)) x
        = ∫ x, (gT x * cutF V m (fr ω) x - gT x * cutF V m (logDerivInv Q hψ) x -
            c ω * gT x) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply]
          ring
      _ = (∫ x, (gT x * cutF V m (fr ω) x - gT x * cutF V m (logDerivInv Q hψ) x)) -
            ∫ x, c ω * gT x := integral_sub ((hgTi _).sub (hgTi _)) hcI
      _ = _ := by
          rw [integral_sub (hgTi _) (hgTi _), integral_const_mul, hint]
  rw [hcomb]
  linarith

end SupercriticalConformalCovariance.BiLip.PortTan
