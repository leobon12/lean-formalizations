/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TdMk
import InteractingSLE.Spec.Supplement.GW2SwcCarrier

/-!
# The physical set of a schedule whose LAST piece may have died

Packet PROVE-GW2-RELDET (`GW2TcCurve.SchedPhysCurveStatement`, the inclusion of the physical curve in the explored
trace after the candidate's death). PROVE-GW2-SWITCH's `Swc.run_pieces_arcs` and `Swc.physSet_eq_radialTips` assume
that EVERY piece succeeded. Their proofs use the success of the first `k` pieces only to launch piece `k`; the success
of the last piece itself is never used. The versions here need the success of all pieces but the last.

* **`run_pieces_arcs_pred`**, **`physSet_eq_radialTips_pred`**;
* **`continuous_stopDrv_of_continuousOn`**: a stopped regular driver is continuous when the driver is continuous on
  the closed interval up to its stop (Theorem 1.3's piece regularity, also at a lifetime).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMapInv)

namespace InteractingSLE.Theorem14.GW2TipSystem.Swc

open GW2Schedule Exist Staged StagedLaw

variable {Δ : ℕ → ℝ≥0∞} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The pieces and connectors of a run whose last piece may have died.** -/
theorem run_pieces_arcs_pred {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}
    (hgw : spec.2.1 = true) {θ : ℕ → ℝ} (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤) (k : ℕ)
    (hk : k + 1 ≤ spec.2.2.length) (hs : AllSucc Δ D k) :
    (ExplState.run κ b jumps spec D (k + 1)).1 = (List.range (k + 1)).map (livePiece spec.1 Δ D) ∧
      (ExplState.run κ b jumps spec D (k + 1)).2.1 = [] := by
  obtain ⟨ih1, ih2⟩ := run_pieces_arcs (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ k (Nat.le_of_succ_le hk) hs
  obtain ⟨hlive, hchart⟩ :=
    (run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ D k (Nat.le_of_succ_le hk)).1 hs
  have hins : spec.2.2[k]? = some (Sum.inl (θ k, Δ k)) := hprog k hk
  have hrun : ExplState.run κ b jumps spec D (k + 1) =
      ExplState.flowStep κ b true (ExplState.run κ b jumps spec D k) k (D k) (θ k) (Δ k) := by
    rw [run_succ, hins]
    change ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) (θ k) (Δ k) = _
    rw [hgw]
  rw [hrun, flowStep_of_isLive _ hlive]
  refine ⟨?_, ?_⟩
  · rw [CounterflowRange.pieces_launch, ih1, List.range_succ, List.map_append, List.map_singleton]
    congr 2
    unfold livePiece
    rw [← hchart]
  · rw [arcs_launch, ih2]

/-- **A stopped regular driver, continuous up to and including its stop, is continuous.** -/
theorem continuous_stopDrv_of_continuousOn {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (hfin : min t e.2 ≠ ⊤) (hc : ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ min t e.2}) :
    Continuous (stopDrv t e) ∧ stopDrv t e 0 = 0 := by
  have hg := isDrvGood_of_continuousOn_le he hfin hc
  rw [← recDrv_eq_stopDrv he hg]
  exact ⟨continuous_recDrv _ _, recDrv_zero _ _⟩

/-- **The physical set of a schedule whose last piece may have died.** -/
theorem physSet_eq_radialTips_pred {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}
    (hgw : spec.2.1 = true) {θ : ℕ → ℝ} (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤)
    (hn0 : 0 < spec.2.2.length) (hs : AllSucc Δ D (spec.2.2.length - 1))
    (hc : ∀ i < spec.2.2.length, Continuous (stopDrv (Δ i) (D i)) ∧ stopDrv (Δ i) (D i) 0 = 0) :
    ExplState.physSet κ b jumps spec D =
      (fun z => (spec.1 : ℂ) + z) ''
        radialTips (joinDrv Δ D spec.2.2.length) 0 (joinTime Δ D spec.2.2.length) := by
  set n := spec.2.2.length with hn
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn0
  obtain ⟨hp, ha⟩ := run_pieces_arcs_pred (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (n - 1)
    (by rw [hn1]) hs
  rw [hn1] at hp ha
  obtain ⟨hJ, hJ0⟩ := continuous_joinDrv hc
  have hpiece : ∀ j < n, (livePiece spec.1 Δ D j).1.tipSet (livePiece spec.1 Δ D j).2.1
      (livePiece spec.1 Δ D j).2.2 = (fun z => (spec.1 : ℂ) + z) ''
        radialTips (joinDrv Δ D n) (joinTime Δ D j) (joinTime Δ D (j + 1)) :=
    fun j hj => tipSet_livePiece spec.1 hj (hΔ j) hc
  unfold ExplState.physSet
  simp only []
  rw [hp, ha]
  ext z
  simp only [mem_union, mem_singleton_iff, mem_iUnion, List.mem_map, List.mem_range, exists_prop,
    List.not_mem_nil, iUnion_of_empty, iUnion_empty, mem_empty_iff_false, or_false]
  constructor
  · rintro (rfl | ⟨_, ⟨j, hj, rfl⟩, hz⟩)
    · exact ⟨0, ⟨0, le_rfl, joinTime_nonneg Δ D n, tendsto_fwdMapInv_zero _ hJ hJ0⟩, add_zero _⟩
    · rw [hpiece j hj] at hz
      obtain ⟨w, ⟨s, hs1, hs2, hlim⟩, rfl⟩ := hz
      exact ⟨w, ⟨s, (joinTime_nonneg Δ D j).trans hs1,
        hs2.trans (joinTime_mono (Nat.succ_le_of_lt hj)), hlim⟩, rfl⟩
  · rintro ⟨w, ⟨s, hs1, hs2, hlim⟩, rfl⟩
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · left
      have hs0 : s = 0 := by
        have : joinTime Δ D n = 0 := by rw [h0]; rfl
        linarith
      subst hs0
      rw [tendsto_nhds_unique hlim (tendsto_fwdMapInv_zero _ hJ hJ0)]
      simp only [add_zero]
    · right
      have hex : ∃ j, s ≤ joinTime Δ D (j + 1) :=
        ⟨n - 1, by rw [Nat.sub_add_cancel hpos]; exact hs2⟩
      classical
      set j := Nat.find hex with hjdef
      have hjs : s ≤ joinTime Δ D (j + 1) := Nat.find_spec hex
      have hjn : j < n := by
        have : j ≤ n - 1 := Nat.find_min' hex (by rw [Nat.sub_add_cancel hpos]; exact hs2)
        omega
      have hlow : joinTime Δ D j ≤ s := by
        rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · rw [hj0]; exact hs1
        · have hmin := Nat.find_min hex (show j - 1 < j by omega)
          rw [Nat.sub_add_cancel hjpos] at hmin
          exact (not_le.1 hmin).le
      refine ⟨livePiece spec.1 Δ D j, ⟨j, hjn, rfl⟩, ?_⟩
      rw [hpiece j hjn]
      exact ⟨w, ⟨s, hlow, hjs, hlim⟩, rfl⟩

end InteractingSLE.Theorem14.GW2TipSystem.Swc
