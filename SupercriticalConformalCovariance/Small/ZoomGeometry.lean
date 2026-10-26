import SupercriticalConformalCovariance.Small.AffineRealization
import SmallGammaGeodesics.CC.PullbackZoom

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace Function
open LQGMetric SupercriticalConformalCovariance
open SmallGammaGeodesics.CC (zoomMap zoomSet)

namespace SupercriticalConformalCovariance.Small

/-- The domain obtained by zooming an open set agrees with the affine preimage. -/
theorem affinePreimage_eq_zoomSet (U : Opens ℂ) (z : ℂ) (r : ℝ) :
    (affinePreimage U z r : Set ℂ) = zoomSet z r U := by
  ext w
  change (r : ℂ) * w + z ∈ U ↔ z + (r : ℂ) * w ∈ U
  rw [add_comm]

/-- The conformal bijection on the two zoomed global domains. -/
theorem zoomConformal {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    IsConformalBijection (zoomMap φ z r)
      (affinePreimage U z r) (affinePreimage V (φ z) r) := by
  have hr0 : r ≠ 0 := hr.ne'
  have hU : (affinePreimage U z r : Set ℂ) = zoomSet z r U :=
    affinePreimage_eq_zoomSet U z r
  have hV : (affinePreimage V (φ z) r : Set ℂ) = zoomSet (φ z) r V :=
    affinePreimage_eq_zoomSet V (φ z) r
  constructor
  · rw [hU]
    exact SmallGammaGeodesics.CC.differentiableOn_zoomMap hr0 U.isOpen hφ.1
  · rw [hU, hV]
    refine ⟨?_, SmallGammaGeodesics.CC.injOn_zoomMap hr0 hφ.2.2.1, ?_⟩
    · intro w hw
      rw [← hφ.2.image_eq]
      rw [← SmallGammaGeodesics.CC.image_zoomMap_zoomSet hr0]
      exact mem_image_of_mem _ hw
    · intro t ht
      rw [← hφ.2.image_eq] at ht
      rw [← SmallGammaGeodesics.CC.image_zoomMap_zoomSet hr0] at ht
      obtain ⟨w, hw, hwt⟩ := ht
      exact ⟨w, hw, hwt⟩

/-- The zoomed map intertwines the affine source and target maps. -/
theorem affine_zoomMap {φ : ℂ → ℂ} (z : ℂ) {r : ℝ} (hr : 0 < r) (w : ℂ) :
    affinePt r (φ z) (zoomMap φ z r w) = φ (affinePt r z w) := by
  rw [show affinePt r (φ z) (zoomMap φ z r w) =
      φ z + (r : ℂ) * zoomMap φ z r w by
        change (r : ℂ) * zoomMap φ z r w + φ z = _
        ring]
  simpa only [show affinePt r z w = z + (r : ℂ) * w by
    change (r : ℂ) * w + z = _; ring] using
    SmallGammaGeodesics.CC.zoomAff_zoomMap (ϕ := φ) hr.ne' w

end SupercriticalConformalCovariance.Small
