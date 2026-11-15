/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenCloseForce
import InteractingSLE.Spec.Sec7.Lemma71CClock

/-!
# A canonical image driver from filled hulls

PROVE-CROSSCOND-GEN. Apply the existing difference-quotient recovery formula
directly to hull mapping-out functions. No boundary parametrization of the image
curve, simplicity, or measurable choice of local drivers is required.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal

namespace InteractingSLE.Sec5.CrossCond.Gen

open Sec7.Lemma71C ConformalImage
open WangWu.ImgWord

/-- The uncentred mapping-out function, censored to zero off its domain. -/
def hullMap (A : ℝ≥0 → Set ℂ) (s : ℝ≥0) (z : ℂ) : ℂ :=
  (H \ A s).indicator (mapOut (A s)) z

/-- Left difference quotients of the uncentred hull maps. -/
def hullQuot (A : ℝ≥0 → Set ℂ) (s : ℝ≥0) (z : ℂ) (k : ℕ) : ℝ :=
  (hullMap A s z - 2 / (((k : ℂ) + 1) *
    (hullMap A s z - hullMap A ((s : ℝ) - 1 / ((k : ℝ) + 1)).toNNReal z))).re

/-- A canonical driver read from the hull history up to `s`; the initial value
is fixed to zero. -/
def hullDriver (A : ℝ≥0 → Set ℂ) (s : ℝ≥0) : ℝ :=
  if s = 0 then 0 else limUnder atTop fun N : ℕ =>
    limUnder atTop fun k : ℕ => hullQuot A s (zPt N) k

@[simp] theorem hullDriver_zero (A : ℝ≥0 → Set ℂ) : hullDriver A 0 = 0 := by
  simp only [hullDriver, ↓reduceIte]

/-- A hull prefix determines its continuous driver by the canonical formula.
This uses the generic Loewner flow and is valid for nonsimple hull chains. -/
theorem hullDriver_eq_of_prefix {A : ℝ≥0 → Set ℂ} {w : ℝ → ℝ}
    (hw : Continuous w) (hw0 : w 0 = 0) {s : ℝ≥0}
    (hA : ∀ r ≤ s, A r = fwdHull w r) : hullDriver A s = w s := by
  by_cases hs : s = 0
  · subst s
    simpa only [hullDriver_zero, NNReal.coe_zero] using hw0.symm
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (pos_iff_ne_zero.2 hs)
  obtain ⟨R, hR⟩ := (isBounded_fwdHull hw s).subset_ball 0
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge R
  have hev : ∀ᶠ N : ℕ in atTop,
      Tendsto (fun k => hullQuot A s (zPt N) k) atTop (𝓝 (w s)) := by
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hzK : ∀ r ≤ (s : ℝ), zPt N ∉ fwdHull w r := by
      intro r hr hmem
      have h1 := hR ((QuantumZipper.fwdHull_mono (W := w)).1 hr hmem)
      rw [Metric.mem_ball, dist_zero_right, norm_zPt] at h1
      have : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hg : ∀ r ∈ Icc (0 : ℝ) s,
        hullMap A r.toNNReal (zPt N) = fwdMap w r (zPt N) + w r := by
      intro r hr
      have hrr : (r.toNNReal : ℝ) = r := Real.coe_toNNReal _ hr.1
      have hrs : r.toNNReal ≤ s := by exact_mod_cast (hrr ▸ hr.2)
      unfold hullMap
      rw [hA r.toNNReal hrs, hrr,
        indicator_of_mem (show zPt N ∈ H \ fwdHull w r from ⟨zPt_mem_H N, hzK r hr.2⟩)]
      exact IsMapOut.eqOn (isHPHull_fwdHull hw hr.1)
        (ConformalImage.isMapOut_mapOut (isHPHull_fwdHull hw hr.1))
        (isMapOut_fwdMap hw hw0 hr.1) ⟨zPt_mem_H N, hzK r hr.2⟩
    simpa only [hullQuot, Real.toNNReal_coe] using
      tendsto_drvQuot hw hs0 (zPt_mem_H N) (hzK s le_rfl) hg
  unfold hullDriver
  rw [ite_eq_right hs]
  exact (tendsto_const_nhds.congr' (hev.mono fun N hN => hN.limUnder_eq.symm)).limUnder_eq

/-- The exact deterministic local-driver property needed to canonically realize
a killed hull chain. This is a pathwise property, with no measurable selections. -/
def HasLocalHullDrivers (A : ℝ≥0 → Set ℂ) (L : WithTop ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < L → ∃ w : ℝ → ℝ,
    Continuous w ∧ w 0 = 0 ∧ ∀ r ≤ t, A r = fwdHull w r

/-- A driver continuous before its lifetime supplies the local witnesses for its
hull chain by the existing compact extension construction. -/
theorem hasLocalHullDrivers_of_driver {A : ℝ≥0 → Set ℂ} {w : ℝ≥0 → ℝ} {L : WithTop ℝ≥0}
    (hw : ContinuousOn w {t | (t : WithTop ℝ≥0) < L}) (hw0 : w 0 = 0)
    (hA : ∀ r : ℝ≥0, (r : WithTop ℝ≥0) < L → A r = fwdHull (Ito.rpath w) r) :
    HasLocalHullDrivers A L := by
  intro t ht
  obtain ⟨c, htc, v, hv, he⟩ := isLocCont_rpath hw t ht
  have hv0 : v 0 = 0 := by
    rw [← he ⟨le_rfl, t.coe_nonneg.trans htc.le⟩]
    simpa only [Ito.rpath, Real.toNNReal_zero] using hw0
  refine ⟨v, hv, hv0, fun r hr => ?_⟩
  rw [hA r (lt_of_le_of_lt (WithTop.coe_le_coe.2 hr) ht)]
  exact fwdHull_eq_of_eqOn r.coe_nonneg
    ((show (r : ℝ) ≤ t by exact_mod_cast hr).trans_lt htc) he

/-- The canonical hull formula recovers a driver continuous only before killing.
It agrees with every pre-existing pathwise relative-image construction. -/
theorem hullDriver_eq_of_driver_before {A : ℝ≥0 → Set ℂ} {w : ℝ≥0 → ℝ} {L : WithTop ℝ≥0}
    (hw : ContinuousOn w {t | (t : WithTop ℝ≥0) < L}) (hw0 : w 0 = 0)
    {s : ℝ≥0} (hs : (s : WithTop ℝ≥0) < L)
    (hA : ∀ r ≤ s, A r = fwdHull (Ito.rpath w) r) : hullDriver A s = w s := by
  obtain ⟨c, hsc, v, hv, he⟩ := isLocCont_rpath hw s hs
  have hv0 : v 0 = 0 := by
    rw [← he ⟨le_rfl, s.coe_nonneg.trans hsc.le⟩]
    simpa only [Ito.rpath, Real.toNNReal_zero] using hw0
  rw [hullDriver_eq_of_prefix hv hv0 (fun r hr => (hA r hr).trans
    (fwdHull_eq_of_eqOn r.coe_nonneg
      ((show (r : ℝ) ≤ s by exact_mod_cast hr).trans_lt hsc) he))]
  simpa only [Ito.rpath, Real.toNNReal_coe] using (he ⟨s.coe_nonneg, hsc.le⟩).symm

/-- Local continuous driver witnesses imply continuity of the canonical driver
before the available lifetime. -/
theorem continuousOn_hullDriver {A : ℝ≥0 → Set ℂ} {L : WithTop ℝ≥0}
    (hA : HasLocalHullDrivers A L) :
    ContinuousOn (hullDriver A) {s | (s : WithTop ℝ≥0) < L} := by
  intro s hs
  obtain ⟨t, hst, htL⟩ := WithTop.lt_iff_exists_coe_btwn.1 hs
  obtain ⟨w, hw, hw0, hAw⟩ := hA t htL
  have hst' : s < t := WithTop.coe_lt_coe.1 hst
  have he : (hullDriver A) =ᶠ[𝓝 s] fun r : ℝ≥0 => w r := by
    filter_upwards [Iio_mem_nhds hst'] with r hr
    exact hullDriver_eq_of_prefix hw hw0 fun u hu => hAw u (hu.trans hr.le)
  exact (((hw.comp NNReal.continuous_coe).continuousAt).congr he.symm).continuousWithinAt

end InteractingSLE.Sec5.CrossCond.Gen
