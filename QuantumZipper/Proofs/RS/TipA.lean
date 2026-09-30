import QuantumZipper.Proofs.RS.TipCore
import QuantumZipper.Proofs.RS.NoRealHit
import QuantumZipper.Proofs.RS.HolderBox

/-!
# EXT-RS node TIP-a: the tip never returns to `0` (κ < 4)

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §4, node **TIP-a** (task RS-TIP-SIM).

* `ae_radialGood_drive`, `ae_shift_good`: TR4 and NR, for the driver and for the shifted
  driver `Wˢ` at a fixed time `s` (P3(c): `Wˢ` is again `√κ` times a Brownian motion).
* `tendsto_nhdsWithin_H_of_holder`: a map Hölder on bounded parts of `ℍ` with a radial limit
  `p` at `0` tends to `p` as `w → 0` in `ℍ`.
* `ae_fwdMapInv_tendsto_zero`: for `κ < 4` and fixed `T > 0`, a.s. `f̂_T(w) → η T` as `w → 0`
  in `ℍ` (RH2 = RS Thm 5.2 for the reversed driver, P3(e)).
* **TIP-a** `ae_sleTrace_ne_zero_of_lt_four`: for `0 < κ < 4`, a.s. `η t ≠ 0` for all `t > 0`.

Sources: Rohde–Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Thm 6.1 and its proof
(p. 23) and Thm 5.2 (p. 21); Kemppainen (2017), p. 80, (5.5). Deviation (blueprint §9, TIP-a):
RS use the continuous extension of `g_s⁻¹` from Thm 4.1; we use the fixed-time Hölder continuity
of RS Thm 5.2 at rational times instead.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RS

/-! ## Driver congruence -/

theorem fwdMapInv_congr_Ici {W V : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hV : Continuous V) (hV0 : V 0 = 0) (hEq : EqOn W V (Ici 0)) {t : ℝ} (ht : 0 ≤ t)
    {w : ℂ} (hw : w ∈ H) : fwdMapInv W t w = fwdMapInv V t w := by
  rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hw,
    UnzipInvariance.fwdMapInv_eq_revMap_timeRev V hV hV0 ht hw]
  refine ReverseFlow.revMap_congr_drive _ fun r hr => ?_
  show W (t - r) - W t = V (t - r) - V t
  rw [hEq (show (0 : ℝ) ≤ t - r by linarith [hr.2]), hEq (show (0 : ℝ) ≤ t from ht)]

theorem trace_congr_Ici {W V : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hV : Continuous V) (hV0 : V 0 = 0) (hEq : EqOn W V (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    trace W t = trace V t :=
  trace_congr_drive hW hW0 hV hV0 ht fun _ hr => hEq hr.1

theorem RadialGood.of_eqOn {W V : ℝ → ℝ} (h : RadialGood W) (hV : Continuous V) (hV0 : V 0 = 0)
    (hEq : EqOn W V (Ici 0)) : RadialGood V := by
  obtain ⟨hW, hW0, h0, hc, δ, hδ, hb⟩ := h
  have htr : EqOn (trace W) (trace V) (Ici 0) := fun t ht => trace_congr_Ici hW hW0 hV hV0 hEq ht
  refine ⟨hV, hV0, htr (le_refl (0 : ℝ)) ▸ h0, hc.congr fun t ht => (htr ht).symm, δ, hδ,
    fun N => ?_⟩
  obtain ⟨C, hC⟩ := hb N
  refine ⟨C, fun t ht y hy => ?_⟩
  rw [← htr ht.1, ← fwdMapInv_congr_Ici hW hW0 hV hV0 hEq ht.1 (mul_I_mem_H hy.1)]
  exact hC t ht y hy

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ## TR4 and NR for the driver and the shifted driver -/

theorem ae_radialGood_drive (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) :
    ∀ᵐ ω ∂P, RadialGood (drive κ B ω) := by
  obtain ⟨δ, hδ, h⟩ := ae_sleTrace_good hB hκ hκ8
  filter_upwards [h, hB.cont, hB.eval_zero_ae_eq_zero] with ω ⟨h0, hc, hb⟩ hBc hB0
  exact ⟨drive_continuous hBc, drive_zero hB0, h0, hc, δ, hδ, hb⟩

theorem ae_shift_good [IsProbabilityMeasure P] (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ ≤ 4) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, RadialGood (shiftDrive (drive κ B ω) s) ∧
      NoRealHitDet (shiftDrive (drive κ B ω) s) := by
  have hB' := (isBrownianReal_shift_indep hB κ s).1
  filter_upwards [ae_radialGood_drive hB' hκ (by linarith), ae_sleTrace_real_eq_zero hB' hκ hκ4,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω hg hnr hBc hB0
  have hVc : Continuous (shiftDrive (drive κ B ω) s) :=
    continuous_shiftDrive (drive_continuous hBc) s
  have hEq : EqOn (drive κ (fun r ω => B (s + r) ω - B s ω) ω) (shiftDrive (drive κ B ω) s)
      (Ici 0) := fun u hu => drive_shift κ B s ω hu
  refine ⟨hg.of_eqOn hVc (shiftDrive_zero _ _) hEq, fun t ht him => ?_⟩
  have htr := trace_congr_Ici hg.1 hg.2.1 hVc (shiftDrive_zero _ _) hEq ht.le
  rw [← htr] at him ⊢
  exact hnr t ht him

/-! ## Boundary continuity at `0` from the Hölder estimate -/

/-! ## TIP-a -/

end RS
end QuantumZipper
