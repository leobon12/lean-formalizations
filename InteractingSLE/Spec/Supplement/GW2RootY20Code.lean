/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootY20Chart
import InteractingSLE.Spec.Supplement.GW2RootD12Geometry
import InteractingSLE.Spec.Supplement.GW2RootC11Capacity
import InteractingSLE.Spec.Sec7.PocketStopMarkedPath
import InteractingSLE.Spec.Restart.ClockMeasCap

/-!
# Exact capacity from a dense physical code

Packet PROVE-T14-GW2ROOT2. Open-domain restriction and chart continuity
preserve density. The existing grid capacity only sees upper-half-plane
hits, so it reads the literal capacity whenever the source geometry gives
an upper continuous prefix. No measurable parametrization is selected.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootY20

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.CoordB Restart

/-- The joint domain is exactly the physical domain in `prefixImage`. -/
theorem relDomain_eq_jointDomain (U : ℝ → ℝ) (s : ℝ) :
    relDomain U s = (fun z : ℂ => -z⁻¹) '' (H \ QuantumZipper.fwdHull U s) := by
  ext z
  rw [mem_relDomain_iff]
  constructor
  · rintro ⟨hz, hK⟩
    exact ⟨-z⁻¹, ⟨neg_inv_mem_H hz, hK⟩, neg_inv_neg_inv z⟩
  · rintro ⟨w, ⟨hw, hK⟩, rfl⟩
    exact ⟨neg_inv_mem_H hw, by simpa only [neg_inv_neg_inv] using hK⟩

/-- A dense physical code remains dense after restricting to the open
joint domain and applying its continuous chart. -/
theorem closure_codeImage {ι : Type*} (s : ℝ≥0) (r : RecData) (F : ι → ℂ) :
    closure (codeImage s r F) =
      closure (relMap (rdrv r) s '' (closure (range F) ∩ relDomain (rdrv r) s)) := by
  apply Subset.antisymm
  · exact closure_mono (image_mono (inter_subset_inter_left _ subset_closure))
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨z, ⟨hzF, hzD⟩, rfl⟩
    have hz : z ∈ closure (range F ∩ relDomain (rdrv r) s) :=
      (isOpen_relDomain (continuous_rdrv r) s.coe_nonneg).closure_inter ⟨hzF, hzD⟩
    exact (continuousAt_relMap (continuous_rdrv r) s.coe_nonneg
      ((mem_relDomain_iff _ _ _).mp hzD).1
      ((mem_relDomain_iff _ _ _).mp hzD).2).continuousWithinAt.mem_closure_image hz

/-- A Borel half-capacity reader on the full product of record and point codes. -/
def codeCapacity {ι : Type*} (s : ℝ≥0) (r : RecData) (F : ι → ℂ) : ℝ :=
  (WholeField.hcapHit (codeImage s r F)).toReal / 2

theorem measurable_codeCapacity {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    (s : ℝ≥0) {r : Ω → RecData} (hr : Measurable r) {F : Ω → ι → ℂ}
    (hF : ∀ i, Measurable fun ω => F ω i) :
    Measurable fun ω => codeCapacity s (r ω) (F ω) :=
  ((WholeField.measurable_hcapHit.comp (measurable_codeImage s hr hF)).ennreal_toReal).div_const 2

/-- For the upper part of a continuous prefix, the grid reader equals
the literal `capOf`, including real visits and the zero-time prefix. -/
theorem capOf_upper_prefix_eq_grid {Γ : ℝ≥0 → ℂ} {t : ℝ≥0}
    (hc : ContinuousOn Γ (Icc 0 t)) (h0 : (Γ 0).im ≤ 0) :
    capOf (Γ '' Icc 0 t ∩ H) =
      (WholeField.hcapHit (Γ '' Icc 0 t ∩ H)).toReal / 2 := by
  obtain ⟨_, hb, ha, hf⟩ := RootD12.upper_prefix_geometry hc h0
  have he : WholeField.hcapHit (Γ '' Icc 0 t ∩ H) = WholeField.hcapHit (Γ '' Icc 0 t) :=
    Sec7.PocketStopMarked.hcapHit_congr_closure (by rw [inter_assoc, inter_self])
  rw [RootC11.capOf_eq_hcapSet hb ha, hf, he, hcapHit_image_eq hc h0,
    ENNReal.toReal_ofReal]
  rw [ConformalImage.hcapSet_eq (isHPHull_fillH_image hc h0)]
  exact HPHull.hcap_nonneg _

/-- Once the actual upper carrier is proved, the Borel code reads its
exact capacity; no observable joined carrier is needed. -/
theorem codeCapacity_eq_capOf {ι : Type*} (s : ℝ≥0) (r : RecData) (F : ι → ℂ)
    {A : Set ℂ} (hF : closure (range F) = A) {Γ : ℝ≥0 → ℂ} {t : ℝ≥0}
    (hc : ContinuousOn Γ (Icc 0 t)) (h0 : (Γ 0).im ≤ 0)
    (himage : relMap (rdrv r) s '' (A ∩ relDomain (rdrv r) s) = Γ '' Icc 0 t ∩ H) :
    codeCapacity s r F = capOf (relMap (rdrv r) s '' (A ∩ relDomain (rdrv r) s)) := by
  have hH : codeImage s r F ⊆ H := by
    rintro _ ⟨z, ⟨_, hz⟩, rfl⟩
    exact relMap_mem_H (continuous_rdrv r) s.coe_nonneg
      ((mem_relDomain_iff _ _ _).mp hz).1 ((mem_relDomain_iff _ _ _).mp hz).2
  have hd := closure_codeImage s r F
  rw [hF, himage] at hd
  have hh : WholeField.hcapHit (codeImage s r F) =
      WholeField.hcapHit (Γ '' Icc 0 t ∩ H) :=
    Sec7.PocketStopMarked.hcapHit_congr_closure (by
      rwa [inter_eq_left.mpr hH, inter_assoc, inter_self])
  rw [himage, capOf_upper_prefix_eq_grid hc h0, codeCapacity, hh]

end InteractingSLE.Theorem14.GW2TipSystem.RootY20
