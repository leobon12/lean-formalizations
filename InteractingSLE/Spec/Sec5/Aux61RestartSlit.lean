import InteractingSLE.Spec.Sec6.DrivingUnconditional

/-!
# Finite simple slits for the restart in Aux. lemma 61

Packet PROVE-AUX61-R1. A simple curve on a compact interval, started at zero and
otherwise in the open half-plane, has a continuous Loewner driver. No unbounded
continuation is required: `YuanCharacterisation.fillH_image_eq` identifies every
initial filling with the slit itself, which gives criterion (a) directly.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61Restart

variable {γ : ℝ → ℂ} {S : ℝ}

/-- Criterion (a) for a finite simple slit whose positive times are in `ℍ`. -/
theorem drivingCriterionA_of_compact_slit (hc : ContinuousOn γ (Icc 0 S))
    (hi : InjOn γ (Icc 0 S)) (h0 : γ 0 = 0) (hH : MapsTo γ (Ioc 0 S) H) :
    Sec6.DrivingCriterionA γ S := by
  intro t ht z hz
  obtain ⟨u, hu, rfl⟩ := hz
  apply subset_closure
  refine ⟨hH ⟨ht.1.trans hu.1, hu.2⟩, ?_⟩
  rw [YuanCharacterisation.fillH_image_eq ht.1.le
    (hc.mono (Icc_subset_Icc_right ht.2.le))
    (hi.mono (Icc_subset_Icc_right ht.2.le)) (by rw [h0, zero_im])
    (hH.mono_left (Ioc_subset_Ioc_right ht.2.le))]
  rintro ⟨v, hv, heq⟩
  have hvu := hi ⟨hv.1.le, hv.2.trans ht.2.le⟩
    ⟨(ht.1.trans hu.1).le, hu.2⟩ heq
  exact (hu.1.trans_le (hvu ▸ hv.2)).false

/-- A finite simple slit has a continuous Loewner driver and capacity clock, with
the mapping-out identities at every time. This is the compact-interval form of
`Sec6.exists_driver_of_injOn`, without an unbounded-continuation hypothesis. -/
theorem exists_driver_of_compact_slit (hS : 0 < S) (hc : ContinuousOn γ (Icc 0 S))
    (hi : InjOn γ (Icc 0 S)) (h0 : γ 0 = 0) (hH : MapsTo γ (Ioc 0 S) H) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ σ : ℝ → ℝ,
      σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 S) ∧ ContinuousOn σ (Icc 0 S) ∧
        ∀ t ∈ Icc 0 S, 0 ≤ σ t ∧
          QuantumZipper.fwdHull W (σ t) = γ '' Ioc 0 t ∧
          IsMapOut (γ '' Ioc 0 t)
            (fun z => QuantumZipper.fwdMap W (σ t) z + W (σ t)) := by
  have hbar : MapsTo γ (Icc 0 S) Hbar := by
    intro u hu
    change 0 ≤ (γ u).im
    rcases eq_or_lt_of_le hu.1 with heq | hpos
    · rw [← heq, h0]
      exact le_rfl
    · exact (show 0 < (γ u).im from hH ⟨hpos, hu.2⟩).le
  have hreal : {u ∈ Ioo 0 S | (γ u).im = 0} = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    rintro u ⟨hu, h⟩
    exact (show 0 < (γ u).im from hH ⟨hu.1, hu.2.le⟩).ne' h
  obtain ⟨W, hW, hW0, σ, hσ0, hσi, hσc, hσ⟩ :=
    Sec6.exists_driver_of_drivingCriteria hS hc h0
      (Sec6.hasSimpleApproxOn_of_injOn hS hc hi h0 hbar)
      (drivingCriterionA_of_compact_slit hc hi h0 hH)
      (Sec6.drivingCriterionB_of_injOn hi (by rw [hreal, interior_empty]))
  refine ⟨W, hW, hW0, σ, hσ0, hσi, hσc, fun t ht => ?_⟩
  have hfill := YuanCharacterisation.fillH_image_eq ht.1
    (hc.mono (Icc_subset_Icc_right ht.2)) (hi.mono (Icc_subset_Icc_right ht.2))
    (by rw [h0, zero_im]) (hH.mono_left (Ioc_subset_Ioc_right ht.2))
  simpa only [hfill] using hσ t ht

end InteractingSLE.Sec5.Aux61Restart
