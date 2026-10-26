import HigherDimLFPPAS.Core.Interfaces
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Two-parameter scaling of the localized field

The truncated kernel rescales with its Jacobian, and the mass is invariant under the matching
change of variables. Pairing with the frozen affine pullback then gives the field identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped Distributions

namespace HigherDimLFPPAS.Scaling

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

theorem locFieldScaling_holds {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)) : Core.LocFieldScaling κ := by
  have _ := hd
  intro ε r hε hε1 hr
  let δ : ℝ := ε / r
  let s : ℝ := locRad ε / r
  let L : ℝ := locRad ε
  have hlog : 0 < Real.log ε⁻¹ := Real.log_pos ((one_lt_inv₀ hε).2 hε1)
  have hlocRad : 0 < locRad ε := by
    unfold locRad
    exact mul_pos hε (pow_pos hlog _)
  have hs : 0 < s := div_pos hlocRad hr
  have hL : 0 < L := by simpa only [L] using hlocRad
  have hrad : r * s = L := by
    dsimp [s, L]
    field_simp [hr.ne']
  have hpow : δ ^ (-(d : ℝ)) = r ^ d * ε ^ (-(d : ℝ)) := by
    dsimp [δ]
    rw [Real.rpow_neg (le_of_lt (div_pos hε hr)), Real.rpow_natCast,
      Real.rpow_neg hε.le, Real.rpow_natCast]
    rw [div_pow]
    field_simp [pow_ne_zero d hr.ne', pow_ne_zero d hε.ne']
  have harg (v : Rd d) : δ⁻¹ • v = ε⁻¹ • (r • v) := by
    have hscl : δ⁻¹ = ε⁻¹ * r := by
      dsimp [δ]
      field_simp [hr.ne', hε.ne']
    rw [hscl, mul_smul]
  have hkernel (v : Rd d) :
      convKernelEps κ δ v = r ^ d * convKernelEps κ ε (r • v) := by
    unfold convKernelEps
    rw [harg v, hpow]
    ring
  have hbump (v : Rd d) :
      radBump (s / 2) s v = radBump (r * s / 2) (r * s) (r • v) := by
    unfold radBump
    congr 1
    · field_simp [hr.ne', hs.ne']
    · rw [smul_smul]
      congr 1
      field_simp [hr.ne', hs.ne']
  have hlocKer (v : Rd d) :
      locKer κ δ s v = r ^ d * locKer κ ε L (r • v) := by
    unfold locKer
    rw [hkernel, hbump, hrad]
    ring
  have hmass : locMass κ δ s = locMass κ ε L := by
    unfold locMass
    calc
      (∫ v, locKer κ δ s v) = ∫ v, r ^ d * locKer κ ε L (r • v) :=
        integral_congr_ae (ae_of_all _ hlocKer)
      _ = r ^ d * ∫ v, locKer κ ε L (r • v) := by rw [integral_const_mul]
      _ = ∫ v, locKer κ ε L v := by
        have hchange : (∫ v, locKer κ ε L (r • v)) =
            (r ^ d)⁻¹ * ∫ v, locKer κ ε L v := by
          simpa only [add_zero] using
            (HigherDimLQGMetric.integral_comp_affinePt (fun v => locKer κ ε L v) hr (0 : Rd d))
        rw [hchange]
        field_simp [pow_ne_zero d hr.ne']
  refine ⟨?_, ?_⟩
  · simpa only [δ, s, L] using hmass
  · intro z g x
    have htest : (r ^ d)⁻¹ • testAffinePull r z (locTest κ δ s x) =
        locTest κ ε L (z + r • x) := by
      ext w
      simp only [smul_apply, smul_eq_mul, testAffinePull_apply hr.ne',
        locTest_apply hK hs, locTest_apply hK hL]
      have hgeom : r • (r⁻¹ • (w - z) - x) = w - (z + r • x) := by
        calc
          r • (r⁻¹ • (w - z) - x) = w - z - r • x := by
            rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
          _ = w - (z + r • x) := by abel
      rw [hlocKer, hgeom, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero d hr.ne'), one_mul]
    have hpair : (affineComp r z g) (locTest κ δ s x) =
        g (locTest κ ε L (z + r • x)) := by
      rw [affineComp_apply_eq_apply_smul, htest]
    unfold locField Core.locFieldR
    rw [hmass, hpair]

end HigherDimLFPPAS.Scaling
