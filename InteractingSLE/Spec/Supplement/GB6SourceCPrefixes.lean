/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6SourceCVersions

/-!
# Rational physical prefixes and endpoint chart comparison

The source driver need only be continuous before its lifetime. Comparing its
frozen extension through a later live time with a continuous prefix version
uses the existing endpoint Loewner comparison theorems.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.SourceC

/-- One countable family of positive rational times is cofinal below every
extended nonnegative time. -/
theorem exists_prefix_times : ∃ T : ℕ → ℝ≥0, (∀ n, 0 < T n) ∧
    ∀ (L : ℝ≥0∞) (t : ℝ≥0), (t : ℝ≥0∞) < L → ∃ n, t < T n ∧ (T n : ℝ≥0∞) < L := by
  let Q := {q : ℚ // 0 < q}
  have : Nonempty Q := ⟨⟨1, by norm_num⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat Q
  let T : ℕ → ℝ≥0 := fun n => ⟨((e n).val : ℝ), by exact_mod_cast (e n).property.le⟩
  refine ⟨T, fun n => by
    change (0 : ℝ) < ((e n).val : ℝ)
    exact_mod_cast (e n).property, fun L t ht => ?_⟩
  obtain ⟨b, htb, hbL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  obtain ⟨q, htq, hqb⟩ := exists_rat_btwn (show (t : ℝ) < b by exact_mod_cast htb)
  have hq : (0 : ℚ) < q := by exact_mod_cast (t.coe_nonneg.trans_lt htq)
  obtain ⟨n, hn⟩ := he ⟨q, hq⟩
  refine ⟨n, ?_, ?_⟩
  · change (t : ℝ) < (e n).val
    simpa only [hn] using htq
  · have hnb : T n < b := by
      change ((e n).val : ℝ) < b
      simpa only [hn] using hqb
    exact (ENNReal.coe_lt_coe.2 hnb).trans hbL

/-- Prefix agreement preserves the retained hull and its inverse map on `H`,
even though the original driver is only locally continuous before its life. -/
theorem chart_prefix_eq {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {s : ℝ≥0}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (hv : Continuous v) (hv0 : v 0 = 0) (hs : (s : ℝ≥0∞) < ζ)
    (heq : ∀ t ≤ s, v t = w t) :
    QuantumZipper.fwdHull (Ito.rpath v) s = QuantumZipper.fwdHull (Ito.rpath w) s ∧
    ∀ z ∈ H, QuantumZipper.fwdMapInv (Ito.rpath v) s z = QuantumZipper.fwdMapInv (Ito.rpath w) s z := by
  obtain ⟨b, hsb, hbζ⟩ := exists_real_btwn_of_lt hs
  have hbc : Continuous (frozenDrive w b) := continuous_frozenDrive_of_lt hw hbζ
  have hb0 : frozenDrive w b 0 = 0 := by rw [frozenDrive_zero (s.coe_nonneg.trans hsb.le), hw0]
  have hvc : Continuous (Ito.rpath v) := hv.comp continuous_real_toNNReal
  have hvz : Ito.rpath v 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using hv0
  have hagree : EqOn (Ito.rpath v) (frozenDrive w b) (Icc 0 (s : ℝ)) := by
    intro r hr
    rw [frozenDrive_eq ⟨hr.1, hr.2.trans hsb.le⟩]
    exact heq r.toNNReal (Real.toNNReal_le_iff_le_coe.2 hr.2)
  have hK : QuantumZipper.fwdHull (frozenDrive w b) s = QuantumZipper.fwdHull (Ito.rpath w) s :=
    fwdHull_eq_of_eqOn s.coe_nonneg hsb (fun r hr => frozenDrive_eq hr)
  have hInv : QuantumZipper.fwdMapInv (frozenDrive w b) s = QuantumZipper.fwdMapInv (Ito.rpath w) s :=
    fwdMapInv_eq_of_eqOn s.coe_nonneg hsb (fun r hr => frozenDrive_eq hr)
  exact ⟨(YuanCorollary13.fwdHull_eq_of_eqOn_Icc hvc hbc s.coe_nonneg hagree).trans hK,
    fun z hz => (LP.fwdMapInv_eq_of_eqOn_Icc hvc hbc hvz hb0 s.coe_nonneg hagree hz).trans (congrFun hInv z)⟩

/-- First contact is unchanged by changing the flow trace outside its prefix. -/
theorem firstContactTime_eq_of_prefix_eq {γ : ℝ≥0 → ℂ} {α A : ℝ≥0 → ℂ} {s : ℝ≥0}
    (hA : ∀ t ≤ s, A t = α t) :
    firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun u => (A u : OnePoint ℂ)) '' Icc 0 s) =
      firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) := by
  congr 1
  apply image_congr
  intro t ht
  rw [hA t ht.2]

end InteractingSLE.Supp8.GB6.SourceC
