import QuantumZipper.Proofs.Zipper.Cor15RezipRegGood
import QuantumZipper.Proofs.Thm11.PushTameAS
import QuantumZipper.Proofs.Loewner.ArcDeterminesDriver

/-!
# Corollary 1.5, input R: the inverse reverse map as a measurable function of the driver

Task COR15-R, step toward the Fubini passage from a fixed driver
(`ae_evalReg_coordChange_pushed_fc`) to the Brownian driver independent of the field.

* `revMapInv_congr_H`: `revMapInv V t` depends only on `revMap V t` on `ℍ`.
* `revMapInv_eq_fwdMap_trev`: for `V` continuous with `V 0 = 0`, `revMapInv V t` is the forward
  map of the time-reversed driver `trev V t` on its alive set `ℍ \ fwdHull`, and `0` off it
  (Sheffield's A1(c), `ArcDriver.revMap_trev_spec`, `ArcDriver.fwdMap_trev_spec`).
* `measurable_revMapInv_param`: joint measurability of `(z, a) ↦ revMapInv (V_a) t z` for a
  measurable family of continuous drivers with `V_a 0 = 0` (via
  `PushTameAS.measurable_fwdMap_alive`).

**Own elementary arguments.**
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

theorem revMapInv_congr_H {V V' : ℝ → ℝ} {t : ℝ} (h : EqOn (revMap V t) (revMap V' t) H) :
    revMapInv V t = revMapInv V' t := by
  funext w
  have hp : (fun z => z ∈ H ∧ revMap V t z = w) = (fun z => z ∈ H ∧ revMap V' t z = w) := by
    funext z
    apply propext
    constructor
    · rintro ⟨hz, e⟩; exact ⟨hz, (h hz).symm.trans e⟩
    · rintro ⟨hz, e⟩; exact ⟨hz, (h hz).trans e⟩
  unfold revMapInv
  by_cases h1 : ∃! z, z ∈ H ∧ revMap V t z = w
  · have h2 : ∃! z, z ∈ H ∧ revMap V' t z = w := by rwa [hp] at h1
    rw [dif_pos h1, dif_pos h2]
    have hc := h1.choose_spec.1
    exact h2.choose_spec.2 _ ⟨hc.1, (h hc.1).symm.trans hc.2⟩
  · have h2 : ¬ ∃! z, z ∈ H ∧ revMap V' t z = w := by rwa [hp] at h1
    rw [dif_neg h1, dif_neg h2]

theorem trev_trev_eq {V : ℝ → ℝ} (hV0 : V 0 = 0) (t : ℝ) :
    ArcDriver.trev (ArcDriver.trev V t) t = V := by
  funext s
  simp [ArcDriver.trev, hV0]

open Classical in
/-- `revMapInv V t` is the forward map of `trev V t` on its alive set, `0` elsewhere. -/
theorem revMapInv_eq_fwdMap_trev {V : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0) {t : ℝ}
    (ht : 0 < t) :
    revMapInv V t = fun w => if w ∈ H \ fwdHull (ArcDriver.trev V t) t then
      fwdMap (ArcDriver.trev V t) t w else 0 := by
  set A := ArcDriver.trev V t with hAdef
  have hA : Continuous A := ArcDriver.continuous_trev hV t
  have hA0 : A 0 = 0 := ArcDriver.trev_zero V t
  have htt : ArcDriver.trev A t = V := trev_trev_eq hV0 t
  funext w
  by_cases hw : w ∈ H \ fwdHull A t
  · rw [if_pos hw]
    obtain ⟨h1, h2⟩ := ArcDriver.fwdMap_trev_spec hA hA0 ht hw
    rw [htt] at h2
    calc revMapInv V t w = revMapInv V t (revMap V t (fwdMap A t w)) := by rw [h2]
      _ = fwdMap A t w := revMapInv_revMap hV ht.le h1
  · rw [if_neg hw]
    apply revMapInv_eq_zero_of_notMem
    rintro ⟨z, hz, rfl⟩
    apply hw
    have h := ArcDriver.revMap_trev_spec hA hA0 ht hz
    rw [htt] at h
    exact h.1

/-- **Joint measurability of `revMapInv` in the driver.** -/
theorem measurable_revMapInv_param {α : Type*} [MeasurableSpace α] {Vp : α → ℝ → ℝ}
    (hVc : ∀ a, Continuous (Vp a)) (hV0 : ∀ a, Vp a 0 = 0)
    (hVm : ∀ s, Measurable fun a => Vp a s) {t : ℝ} (ht : 0 < t) :
    Measurable fun p : ℂ × α => revMapInv (Vp p.2) t p.1 := by
  classical
  set B : ℝ≥0 → α → ℝ := fun r a => ArcDriver.trev (Vp a) t r with hBdef
  have hBm : ∀ r, Measurable (B r) := fun r =>
    (hVm (t - (r : ℝ))).sub (hVm t)
  have hBc : ∀ a, Continuous fun r => B r a := fun a =>
    (ArcDriver.continuous_trev (hVc a) t).comp NNReal.continuous_coe
  have hmeas := PushTameAS.measurable_fwdMap_alive hBm hBc 1 ht.le
  have hdr : ∀ a, ∀ r ∈ Icc (0 : ℝ) t, drive 1 B a r = ArcDriver.trev (Vp a) t r := by
    intro a r hr
    simp only [drive, Real.sqrt_one, one_mul, hBdef, Real.coe_toNNReal _ hr.1]
  have hdc : ∀ a, Continuous (drive 1 B a) := fun a =>
    continuous_const.mul ((hBc a).comp continuous_real_toNNReal)
  convert hmeas using 1
  funext p
  rw [revMapInv_eq_fwdMap_trev (hVc p.2) (hV0 p.2) ht,
    CharFunRhs.fwdHull_eq_of_eqOn (hdc p.2) (ArcDriver.continuous_trev (hVc p.2) t) ht.le
      (hdr p.2), CharFunRhs.fwdMap_eq_of_eqOn (hdr p.2)]

end Cor15Group
end QuantumZipper
