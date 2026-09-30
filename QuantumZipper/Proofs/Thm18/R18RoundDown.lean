import QuantumZipper.Proofs.Thm18.R18RoundDownDet
import QuantumZipper.Proofs.Thm18.G4WeldUniq

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T7b: `Z^LEN_ℓ ∘ Z^LEN_{−ℓ} = id` on area-carrying configurations, off the curve

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1), p. 26:
"`Z^LEN_t` ... is a.s. uniquely defined via conformal welding" and is the inverse of
`Z^LEN_{−t}`. Deterministic round trip `configEqOff_zipLenUpA_zipLenDownA_of` (area-carrying copy
of `Thm18Asm.configEq_zipLenC_zipLenDown_of`, G4WeldRound.lean; **own elementary argument**, as
there): with `t` the open-arc length time, `a` the scale of the transported area and
`q = revDrv W t a = (t/a², u ↦ (W(t − a²u) − W t)/a)`, if `q` is a length-welding driver of the
unzipped field with removable doubled hull (uniqueness, Jones–Smirnov, `isLenWeldingDriver_eq_of_good`),
the carried area has scale `1` and does not charge `K_t ⊆ curveOf W`, the off-hull pushed-circle
data hold (`D74R.PushRegOffAt`, from A-sep) and `Y(a·)(·/a) ≈ Y`, then `Z_ℓ(Z_{−ℓ} c)` equals `c`
off the curve.
-/

noncomputable section

open MeasureTheory Filter Set

namespace QuantumZipper
namespace R18

open Thm18Asm Thm18Asm.G4Core

/-- Driver algebra of `Z_ℓ ∘ Z_{−ℓ}` with the unzipping driver of `zipCapDownA` rescaled by
`canonAConfig` (the extra `max` of `zipCapDown`). -/
theorem revDrv_roundtripA (W : ℝ → ℝ) (hW0 : W 0 = 0) {t a : ℝ} (ha : 0 < a) {u : ℝ}
    (hu : 0 ≤ u) :
    (if a⁻¹ ^ 2 * max u 0 ≤ t / a ^ 2 then
        (W (t - a ^ 2 * (t / a ^ 2 - max (a⁻¹ ^ 2 * max u 0) 0)) - W t) / a -
          (W (t - a ^ 2 * (t / a ^ 2)) - W t) / a
      else (W (t + max (a ^ 2 * max (a⁻¹ ^ 2 * max u 0 - t / a ^ 2) 0) 0) - W t) / a -
          (W (t - a ^ 2 * (t / a ^ 2)) - W t) / a) / a⁻¹ = W u := by
  have ha2 : a ^ 2 ≠ 0 := by positivity
  have e1 : a⁻¹ ^ 2 * max u 0 = u / a ^ 2 := by rw [max_eq_left hu]; field_simp
  have e2 : a ^ 2 * (t / a ^ 2) = t := by field_simp
  rw [e1, e2, sub_self, hW0, max_eq_left (by positivity : (0 : ℝ) ≤ u / a ^ 2)]
  split_ifs with h
  · have e3 : a ^ 2 * (t / a ^ 2 - u / a ^ 2) = t - u := by field_simp
    rw [e3, show t - (t - u) = u by ring]
    field_simp
    ring
  · have hlt : t / a ^ 2 < u / a ^ 2 := lt_of_not_ge h
    have e3 : a ^ 2 * (u / a ^ 2 - t / a ^ 2) = u - t := by field_simp
    have hpos : 0 < a ^ 2 * (u / a ^ 2 - t / a ^ 2) := mul_pos (by positivity) (by linarith)
    rw [max_eq_left (show (0 : ℝ) ≤ u / a ^ 2 - t / a ^ 2 by linarith), e3,
      max_eq_left (show (0 : ℝ) ≤ u - t by linarith), show t + (u - t) = u by ring]
    field_simp
    ring

/-- **Round trip `Z_ℓ ∘ Z_{−ℓ}` on area-carrying configurations, off the curve** (deterministic).
-/
theorem configEqOff_zipLenUpA_zipLenDownA_of {γ ℓ : ℝ} (hℓ : 0 ≤ ℓ) {c : AreaConfig}
    (hc : Continuous c.drv) (hc0 : c.drv 0 = 0) (hH : c.area Hᶜ = 0)
    (h1 : areaScale c.area = 1) {t a : ℝ} (htdef : lenTimeOpen γ ℓ c.toPair = t)
    (hadef : areaScale (zipCapDownA γ t c).area = a) (ht : 0 < t) (ha : 0 < a)
    (hK : c.area (fwdHull c.drv t ∩ H) = 0) (hsub : fwdHull c.drv t ⊆ curveOf c.drv)
    (hq : IsLenWeldingDriver γ (zipLenDownA γ ℓ c).fld ℓ (revDrv c.drv t a))
    (hrem : RemHull (revDrv c.drv t a)) (hR : D74R.PushRegOffAt γ c.toPair t 0 a)
    (hrr : RegEq (rescale (rescale c.fld (Qc γ) a) (Qc γ) a⁻¹) c.fld) :
    ConfigEqOff (zipLenA γ ℓ (zipLenDownA γ ℓ c)).toPair c.toPair := by
  rw [zipLenA_of_nonneg hℓ]
  subst hadef
  set a := areaScale (zipCapDownA γ t c).area with hadef
  set q := revDrv c.drv t a with hqdef
  have hc₃ : zipLenDownA γ ℓ c = canonAConfig γ (zipCapDownA γ t c) := by
    rw [zipLenDownA, htdef]
  have hq0 : 0 < q.1 := by simp only [hqdef, revDrv]; positivity
  -- the length-welding driver chosen by `zipLenUpA` is `q` on `[0, q.1]`
  have hp' := lenWeldDriver_spec ⟨q, hq⟩
  obtain ⟨hT, hEq⟩ := isLenWeldingDriver_eq_of_good hq hq0 hrem hp'
  have hup : zipLenUpA γ ℓ (zipLenDownA γ ℓ c) =
      canonAConfig γ (zipWeldUpA γ q.1 q.2 (zipLenDownA γ ℓ c)) := by
    rw [zipLenUpA, hT, zipWeldUpA_congr hq0.le hEq.symm]
  -- the re-zip scale is `a⁻¹`
  have hW'' : Continuous fun s => c.drv (t - s) - c.drv t :=
    (hc.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hfull : c.area.restrict (H \ fwdHull c.drv t) = c.area := by
    refine Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (measure_mono_null ?_
      (measure_union_null hH hK)))
    intro z hz
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_and, not_not] at hz
    by_cases hzH : z ∈ H
    · exact Or.inr ⟨hz hzH, hzH⟩
    · exact Or.inl hzH
  have harea : (zipWeldUpA γ q.1 q.2 (zipLenDownA γ ℓ c)).area =
      c.area.map fun z => ((a : ℂ))⁻¹ * z := by
    have key := zipWeldUpA_canonAConfig_area (γ := γ) ht.le hW'' ha (W₃ := q.2) (fun u _ => rfl)
    rw [zipWeldUpA_zipCapDownA_area ht.le hc hc0, hfull] at key
    rw [hc₃]
    exact key
  have hb : areaScale (zipWeldUpA γ q.1 q.2 (zipLenDownA γ ℓ c)).area = a⁻¹ := by
    rw [harea, areaScale_map_inv_mul _ ha, h1, one_div]
  rw [hup]
  refine ⟨?_, fun u hu => ?_⟩
  · -- the field, off the curve
    show RegEqOff (curveOf c.drv)
      (rescale (zipWeldUpA γ q.1 q.2 (zipLenDownA γ ℓ c)).fld (Qc γ)
        (areaScale (zipWeldUpA γ q.1 q.2 (zipLenDownA γ ℓ c)).area)) c.fld
    rw [hb, hc₃]
    have hG : RegEqOff (revHull q.2 q.1)
        (coordChange (rescale (coordChange c.fld (fwdMapInv c.drv t) (Qc γ)) (Qc γ) a)
          (revMapInv q.2 q.1) (Qc γ)) (rescale c.fld (Qc γ) a) :=
      regEqOff_of_coordsOff fun i hi =>
        coordsFull_rezipUp_off (c := c.toPair) hc hc0 ht.le ha hR i hi
    have hG2 := regEqOff_rescale hG (Qc γ) (inv_pos.2 ha)
    have hsub' : {w : ℂ | ((a⁻¹ : ℝ) : ℂ) * w ∈ revHull q.2 q.1} ⊆ curveOf c.drv := by
      intro w hw
      obtain ⟨z, hz, hzw⟩ := revHull_revDrv_subset hc hc0 ht ha hw
      have haC : ((a : ℂ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast ha.ne')
      have : z = w := by
        push_cast at hzw
        exact mul_left_cancel₀ haC hzw
      exact hsub (this ▸ hz)
    exact regEqOff_trans_regEq (regEqOff_mono' hsub' hG2) hrr
  · -- the driver
    show (zipWeldUpA γ q.1 q.2 (zipLenDownA γ ℓ c)).drv
        (areaScale (zipWeldUpA γ q.1 q.2 (zipLenDownA γ ℓ c)).area ^ 2 * max u 0) /
        areaScale (zipWeldUpA γ q.1 q.2 (zipLenDownA γ ℓ c)).area = c.drv u
    rw [hb, hc₃]
    simp only [zipWeldUpA, zipWeldUp, AreaConfig.toPair, canonAConfig, zipCapDownA, zipCapDown,
      hqdef, revDrv]
    have e : areaScale (Measure.map (fwdMap c.drv t) (c.area.restrict (H \ fwdHull c.drv t))) =
        a := rfl
    rw [e]
    exact revDrv_roundtripA c.drv hc0 ha hu

end R18
end QuantumZipper
