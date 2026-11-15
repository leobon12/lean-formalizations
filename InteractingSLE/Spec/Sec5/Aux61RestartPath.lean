import InteractingSLE.Spec.Sec5.Aux61RestartSlit

/-!
# The finite slit starting at a landed restart access

Packet PROVE-AUX61-R1; ruling R71. The value at the initial access is the
boundary limit, rather than the arbitrary value of the chart on its boundary.
The time parameter is translated from the original own time. The results also
apply to the counterflow-chart crosscuts of `Aux61Loc`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61Restart

/-- A charted path translated to start at time zero, with its landed initial
value explicitly supplied. The chart's boundary value is never evaluated. -/
def landingSlit (g : ℝ → ℂ) (r x : ℝ) (u : ℝ) : ℂ :=
  if u ≤ 0 then 0 else g (r + u) - (x : ℂ)

theorem landingSlit_zero (g : ℝ → ℂ) (r x : ℝ) : landingSlit g r x 0 = 0 :=
  ite_eq_left le_rfl

theorem landingSlit_of_pos {g : ℝ → ℂ} {r x u : ℝ} (hu : 0 < u) :
    landingSlit g r x u = g (r + u) - (x : ℂ) := ite_eq_right (not_le.2 hu)

/-- Continuity, simplicity and interiority of a path started at a real landing
point, on a compact part before its next boundary contact. -/
theorem landingSlit_properties {g : ℝ → ℂ} {r t x : ℝ} (_hrt : r < t)
    (hc : ContinuousOn g (Ioc r t)) (hi : InjOn g (Ioc r t))
    (hH : MapsTo g (Ioc r t) H) (hlim : Tendsto g (𝓝[>] r) (𝓝 (x : ℂ))) :
    ContinuousOn (landingSlit g r x) (Icc 0 (t - r)) ∧
      InjOn (landingSlit g r x) (Icc 0 (t - r)) ∧
      MapsTo (landingSlit g r x) (Ioc 0 (t - r)) H := by
  have hshift : MapsTo (fun u => r + u) (Ioc 0 (t - r)) (Ioc r t) := by
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hpos : MapsTo (landingSlit g r x) (Ioc 0 (t - r)) H := by
    intro u hu
    rw [landingSlit_of_pos hu.1]
    change 0 < (g (r + u) - (x : ℂ)).im
    simpa only [sub_im, ofReal_im, sub_zero] using
      (show 0 < (g (r + u)).im from hH (hshift hu))
  have hcont : ContinuousOn (fun u => g (r + u) - (x : ℂ)) (Ioc 0 (t - r)) :=
    (hc.comp (continuous_const.add continuous_id).continuousOn hshift).sub continuousOn_const
  have hright : Tendsto (landingSlit g r x) (𝓝[>] 0) (𝓝 0) := by
    have harg : Tendsto (fun u : ℝ => r + u) (𝓝[>] 0) (𝓝[>] r) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have harg0 : Tendsto (fun u : ℝ => r + u) (𝓝 (0 : ℝ)) (𝓝 (r + 0)) :=
          (continuous_const.add continuous_id).continuousAt.tendsto
        simpa only [add_zero] using harg0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact lt_add_of_pos_right r hu
    have h := (hlim.comp harg).sub_const (x : ℂ)
    rw [sub_self] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (landingSlit_of_pos hu).symm
  refine ⟨?_, ?_, hpos⟩
  · intro u hu
    rcases eq_or_lt_of_le hu.1 with hzero | hzero
    · subst u
      apply ContinuousWithinAt.mono _ Icc_subset_Ici_self
      apply continuousWithinAt_Ioi_iff_Ici.1
      simpa only [ContinuousWithinAt, landingSlit_zero] using hright
    · have hne : Ioc (0 : ℝ) (t - r) =ᶠ[𝓝 u] Icc 0 (t - r) := by
        filter_upwards [Ioi_mem_nhds hzero] with v hv
        have hv' : 0 < v := hv
        simp only [mem_Ioc, mem_Icc]
        exact propext (and_congr_left fun _ => iff_of_true hv' hv'.le)
      have hcp : ContinuousOn (landingSlit g r x) (Ioc 0 (t - r)) :=
        hcont.congr fun v hv => landingSlit_of_pos hv.1
      exact (hcp u ⟨hzero, hu.2⟩).congr_set hne
  · intro u hu v hv huv
    rcases eq_or_lt_of_le hu.1 with hu0 | hu0
    · subst u
      by_contra hv0
      have hvpos : 0 < v := lt_of_le_of_ne hv.1 hv0
      have hh : 0 < (landingSlit g r x v).im := hpos ⟨hvpos, hv.2⟩
      rw [← huv, landingSlit_zero, zero_im] at hh
      exact lt_irrefl _ hh
    · rcases eq_or_lt_of_le hv.1 with hv0 | hv0
      · subst v
        have hh : 0 < (landingSlit g r x u).im := hpos ⟨hu0, hu.2⟩
        rw [huv, landingSlit_zero, zero_im] at hh
        exact (lt_irrefl _ hh).elim
      · rw [landingSlit_of_pos hu0, landingSlit_of_pos hv0] at huv
        exact add_left_cancel (hi (hshift ⟨hu0, hu.2⟩) (hshift ⟨hv0, hv.2⟩)
          (sub_left_inj.1 huv))

/-- A simple path landing at a real access has a driver on every compact
pre-contact segment, in the translated original own time. -/
theorem exists_driver_of_landing_slit {g : ℝ → ℂ} {r t x : ℝ} (hrt : r < t)
    (hc : ContinuousOn g (Ioc r t)) (hi : InjOn g (Ioc r t))
    (hH : MapsTo g (Ioc r t) H) (hlim : Tendsto g (𝓝[>] r) (𝓝 (x : ℂ))) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ σ : ℝ → ℝ,
      σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 (t - r)) ∧ ContinuousOn σ (Icc 0 (t - r)) ∧
        ∀ u ∈ Icc 0 (t - r), 0 ≤ σ u ∧
          QuantumZipper.fwdHull W (σ u) = landingSlit g r x '' Ioc 0 u ∧
          IsMapOut (landingSlit g r x '' Ioc 0 u)
            (fun z => QuantumZipper.fwdMap W (σ u) z + W (σ u)) := by
  obtain ⟨hgc, hgi, hgH⟩ := landingSlit_properties hrt hc hi hH hlim
  exact exists_driver_of_compact_slit (sub_pos.2 hrt) hgc hgi (landingSlit_zero g r x) hgH

end InteractingSLE.Sec5.Aux61Restart
