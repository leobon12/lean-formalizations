import MatedCRTHarmonic.GMS4.Prop210Transfer
import MatedCRTHarmonic.GMS4b.Localized

/-!
# Algebraic part of the Proposition 2.10 density comparison

The geometric inputs are (4.5), the cell area/diameter ratio, and (4.7),
The multigraph degree versus localized inner and outer degree. This file
keeps those two inputs visible while proving their product comparison.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace MatedCRTHarmonic.GMS4F

open MatedCRTHarmonic.GMS3

variable {V E : Type*} {G : LFMultigraph V E} {o : V}

theorem uCoef_eq_cellRatio_mul_degree
    (H : CellularEmbedding G o) (x : V) :
    uCoef H x =
      (ENNReal.ofReal (cellDiam H x ^ 2) / volume (H.cell x)) *
        (G.deg x : ENNReal) := by
  rw [uCoef, ENNReal.ofReal_mul (sq_nonneg _)]
  simp only [ENNReal.ofReal_natCast]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Equations (4.5) and (4.7) imply the numerical factor two in (4.20). -/
theorem uCoef_le_two_localized_density
    (H : CellularEmbedding G o) (x : V)
    (DA degreeSum : ENNReal)
    (hratio : ENNReal.ofReal (cellDiam H x ^ 2) / volume (H.cell x) ≤ DA)
    (hdegree : (G.deg x : ENNReal) ≤ 2 * degreeSum) :
    uCoef H x ≤ 2 * (DA * degreeSum) := by
  rw [uCoef_eq_cellRatio_mul_degree]
  calc
    _ ≤ DA * (2 * degreeSum) := mul_le_mul' hratio hdegree
    _ = 2 * (DA * degreeSum) := by ac_rfl

/-- The source's (4.5) supplies the area-ratio half of (4.20) for a
selected cell whose time interval contains the first hitting time of `z`.
The remaining premise is precisely the multigraph-degree estimate (4.7). -/
theorem selectedCell_uCoef_le_two_uStar
    (H : CellularEmbedding G o) (x : V)
    (ε : ℝ) (curve : ℝ → ℂ) (z : ℂ) (t : ℝ)
    (hcell : H.cell x = curve '' Set.Icc (t - ε) t)
    (htlo : t - ε ≤ GMS4b.hitTime curve z)
    (hthi : GMS4b.hitTime curve z ≤ t)
    (hdegree : (G.deg x : ENNReal) ≤ 2 *
      (((GMS4b.degreeIn ε curve z + GMS4b.degreeOut ε curve z : ℕ∞)) : ENNReal)) :
    uCoef H x ≤ 2 * GMS4b.uStar ε curve z := by
  have hratio := GMS4b.segRatio_le_locDA (ε := ε) (c := curve)
    (t₀ := GMS4b.hitTime curve z) (s := t) htlo hthi
  have hratio' : ENNReal.ofReal (cellDiam H x ^ 2) / volume (H.cell x) ≤
      GMS4b.areaRatio ε curve z := by
    simpa [GMS4b.segRatio, GMS4b.areaRatio, cellDiam, hcell] using hratio
  exact uCoef_le_two_localized_density H x _ _ hratio' hdegree

end MatedCRTHarmonic.GMS4F

