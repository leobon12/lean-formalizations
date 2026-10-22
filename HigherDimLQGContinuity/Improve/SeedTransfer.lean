import HigherDimLQGContinuity.SiteEvents.TrialBase
import HigherDimLQGContinuity.LabelEvents.SiteNormal

/-!
# Transferring a favorable seed to site-normalized metrics
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- A positive scalar multiplying the secondary site metric cancels from
its own-unit seed normalization. -/
theorem q11_seed_normalization_scale_cancel {d : ℕ} (F : ContMetric d)
    {cscale S r : ℝ} (hcscale : 0 < cscale) (hS : 0 < S) (hr : r ≠ 0) (c : Rd d) :
    (((F.smul cscale hcscale).affine r hr c).smul (cscale * S)⁻¹
      (inv_pos.mpr (mul_pos hcscale hS))) =
      ((F.affine r hr c).smul S⁻¹ (inv_pos.mpr hS)) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  simp only [ContMetric.smul_apply, ContMetric.affine_apply]
  have hcscale0 : cscale ≠ 0 := hcscale.ne'
  have hS0 : S ≠ 0 := hS.ne'
  field_simp

/-- The two exact scaling identities at a seed normalize the primary and
secondary site metrics to the same trial metrics. -/
theorem q11_seed_normalization_of_scaling {d : ℕ}
    {D E : DistRd d → ContMetric d} {g g' : DistRd d}
    {ξ η r cscale : ℝ} (hr : 0 < r) (hcscale : 0 < cscale)
    (c : Rd d) (A B : ContMetric d)
    (hA : A = rho D g)
    (hB : B = (rho E g).smul cscale hcscale)
    (hDseed : siteNorm ξ D c hr g = rho D g')
    (hEseed : siteNorm η E c hr g = rho E g') :
    ((A.affine r hr.ne' c).smul (scaleS d ξ 1 r c g)⁻¹
      (inv_pos.mpr (scaleS_pos d ξ 1 hr c g))) = rho D g' ∧
    ((B.affine r hr.ne' c).smul (cscale * scaleS d η 1 r c g)⁻¹
      (inv_pos.mpr (mul_pos hcscale (scaleS_pos d η 1 hr c g)))) = rho E g' := by
  constructor
  · rw [hA]
    exact hDseed
  · rw [hB, q11_seed_normalization_scale_cancel (rho E g) hcscale
      (scaleS_pos d η 1 hr c g) hr.ne' c]
    exact hEseed

/-- A favorable trial for the recentered field is a `SeedFav` for any pair
of site metrics whose own-unit seed normalizations equal that trial pair.
The unit-window and ratio inequalities are kept explicit for the cap step. -/
theorem q11_seedFav_of_trial {d : ℕ}
    {D E : DistRd d → ContMetric d} {g : DistRd d}
    {A B : ContMetric d} {c : Rd d} {r SD SE Λ v H0 σ0 β0 m M Hsd σsd : ℝ}
    (hr : r ≠ 0) (hSD : 0 < SD) (hSE : 0 < SE)
    (hSDlo : Λ⁻¹ ≤ SD) (hSDhi : SD ≤ Λ)
    (hSElo : Λ⁻¹ ≤ SE) (hSEhi : SE ≤ Λ)
    (hratio : |Real.log (SE / SD)| ≤ v / 10)
    (hDnorm : ((A.affine r hr c).smul SD⁻¹ (inv_pos.mpr hSD)) = rho D g)
    (hEnorm : ((B.affine r hr c).smul SE⁻¹ (inv_pos.mpr hSE)) = rho E g)
    (htrial : g ∈ seedTrialEvent D E v H0 σ0 β0 m M Hsd σsd) :
    SeedFav H0 σ0 β0 m M Hsd σsd Λ v A B c r := by
  obtain ⟨hdown, hrefs⟩ := htrial
  obtain ⟨γ, hγ, hgap⟩ := hdown
  refine ⟨hr, SD, SE, hSD, hSE, hSDlo, hSDhi, hSElo, hSEhi,
    hratio, ?_, γ, ?_, ?_⟩
  · rw [hDnorm, hEnorm]
    exact hrefs
  · rw [hEnorm]
    exact hγ
  · rw [hDnorm, hEnorm]
    exact hgap

end HigherDimLQGContinuity
