import SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes.ENNRealWeighted




 
set_option autoImplicit false
noncomputable section
open Set unitInterval
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes

theorem geoCode_exact_speed
    (D : LSCMetric) (R : Measurability.GeodesicCodes.Path) (u v : ℂ)
    (h : Measurability.GeodesicCodes.GeoCode (D, (R, (u, v))))
    (s t : unitInterval) (hst : s ≤ t) :
    D (R s, R t) =
      ENNReal.ofReal ((t : ℝ) - (s : ℝ)) * D (u, v) := by
  let L : ℝ≥0∞ := D (u, v)
  let x : ℝ≥0∞ := D (u, R s)
  let y : ℝ≥0∞ := D (R s, R t)
  let z : ℝ≥0∞ := D (R t, v)
  have hspeed := Measurability.AttainedEvents.geoCode_all_times D R u v h
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hstR : (s : ℝ) ≤ (t : ℝ) := hst
  have hx : x ≤ ENNReal.ofReal (s : ℝ) * L := by
    have hb := hspeed (0 : unitInterval) s
    rw [h.1] at hb
    simpa [x, L, abs_of_nonneg hs0] using hb
  have hy : y ≤ ENNReal.ofReal ((t : ℝ) - (s : ℝ)) * L := by
    change D (R s, R t) ≤ _
    simpa only [abs_of_nonneg (sub_nonneg.mpr hstR)] using (hspeed s t)
  have hz : z ≤ ENNReal.ofReal (1 - (t : ℝ)) * L := by
    have hb := hspeed t (1 : unitInterval)
    rw [h.2.1] at hb
    simpa [z, L, abs_of_nonneg (sub_nonneg.mpr ht1)] using hb
  have htri : L ≤ x + y + z := by
    change D (u, v) ≤ D (u, R s) + D (R s, R t) + D (R t, v)
    calc
      D (u, v) ≤ D (u, R s) + D (R s, v) :=
        D.isExtMetric.2.2.2 u (R s) v
      _ ≤ D (u, R s) + (D (R s, R t) + D (R t, v)) := by
        gcongr
        exact D.isExtMetric.2.2.2 (R s) (R t) v
      _ = D (u, R s) + D (R s, R t) + D (R t, v) := by
        rw [add_assoc]
  have hsum : (s : ℝ) + ((t : ℝ) - (s : ℝ)) +
      (1 - (t : ℝ)) = 1 := by ring
  exact middle_eq_of_triangle_bounds L x y z
    (s : ℝ) ((t : ℝ) - (s : ℝ)) (1 - (t : ℝ))
    h.2.2.1.ne hs0 (sub_nonneg.mpr hstR) (sub_nonneg.mpr ht1)
    hsum hx hy hz htri

end SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
