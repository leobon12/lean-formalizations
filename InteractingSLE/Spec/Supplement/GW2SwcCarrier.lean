/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SwcChart
import InteractingSLE.Spec.Supplement.CounterflowRange
import InteractingSLE.Spec.Supplement.GW2aContArc

/-!
# The physical set of a switched schedule is read off the joined driver

Packet PROVE-GW2-SWITCH. For a GW2 flow program whose pieces all survive their own times
(`GW2Schedule.AllSucc`), every piece is launched at the previous tip in the successive chart
(`GW2Schedule.run_gw2`). By `succChart_inv_eq` the physical points of piece `j` are the radial
limits of the inverse Loewner maps of the joined driver `joinDrv` at the times
`[joinTime j, joinTime (j + 1)]`, translated by the root. Hence:

* `livePiece`, **`run_pieces_arcs`**: the stored pieces of a live GW2 run, and no connector arcs;
* `radialTips W a b`: the radial limits `lim_{y ↓ 0} F_s(iy)` of the chain of `W`, `s ∈ [a, b]`;
* **`tipSet_livePiece`**: the tip set of piece `j` is `x + radialTips (joinDrv Δ D n) (T j) (T (j+1))`;
* **`physSet_eq_radialTips`**: the physical set of the whole live schedule is
  `x + radialTips (joinDrv Δ D n) 0 (joinTime Δ D n)`.

Deterministic; the only premises are the live-run conditions and continuity of the stopped
drivers (supplied almost surely by `PieceRegular`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMapInv)

namespace InteractingSLE.Theorem14.GW2TipSystem.Swc

open GW2Schedule Exist Staged StagedLaw

/-- **The radial tips** `lim_{y ↓ 0} F_s(i y)` of the Loewner chain of `W`, at times `s ∈ [a, b]`. -/
def radialTips (W : ℝ → ℝ) (a b : ℝ) : Set ℂ :=
  {z | ∃ s : ℝ, a ≤ s ∧ s ≤ b ∧
    Tendsto (fun y : ℝ => fwdMapInv W s (y * Complex.I)) (𝓝[>] 0) (𝓝 z)}

/-- The piece stored by a live run for instruction `j` (`ExplState.launch` in `succChart`). -/
def livePiece (x : ℝ) (Δ : ℕ → ℝ≥0∞) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) :
    Chart × (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  (succChart x Δ D j, fun r : ℝ≥0 => (D j).1 (min (r : ℝ≥0∞) (min (Δ j) (D j).2)).toNNReal,
    min (Δ j) (D j).2)

variable {Δ : ℕ → ℝ≥0∞} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

theorem joinTime_mono {j k : ℕ} (h : j ≤ k) : joinTime Δ D j ≤ joinTime Δ D k := by
  induction k, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact ih.trans (le_add_of_nonneg_right (stopTime_nonneg _ _))

theorem joinDrv_eqOn_of_le {j k : ℕ} (h : j ≤ k) :
    EqOn (joinDrv Δ D k) (joinDrv Δ D j) (Icc 0 (joinTime Δ D j)) := by
  induction k, h using Nat.le_induction with
  | base => exact fun _ _ => rfl
  | succ m hjm ih =>
    intro r hr
    exact (joinDrv_eqOn m ⟨hr.1, hr.2.trans (joinTime_mono hjm)⟩).trans (ih hr)

/-- Inside piece `j`, the successive chart composed with the piece's own inverse map is the
translated inverse map of the joined driver of all `n` pieces. -/
theorem succChart_inv_stopDrv_eq (x : ℝ) {n j : ℕ} (hjn : j < n)
    (hc : ∀ i < n, Continuous (stopDrv (Δ i) (D i)) ∧ stopDrv (Δ i) (D i) 0 = 0)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ stopTime (Δ j) (D j)) {w : ℂ} (hw : w ∈ H) :
    (succChart x Δ D j).2.1 (fwdMapInv (stopDrv (Δ j) (D j)) t w) =
      (x : ℂ) + fwdMapInv (joinDrv Δ D n) (joinTime Δ D j + t) w := by
  have hcj : ∀ i < j, Continuous (stopDrv (Δ i) (D i)) ∧ stopDrv (Δ i) (D i) 0 = 0 :=
    fun i hi => hc i (hi.trans hjn)
  have hc1 : ∀ i < j + 1, Continuous (stopDrv (Δ i) (D i)) ∧ stopDrv (Δ i) (D i) 0 = 0 :=
    fun i hi => hc i (lt_of_lt_of_le hi hjn)
  obtain ⟨hS, hS0⟩ := hc j hjn
  obtain ⟨hJn, hJn0⟩ := continuous_joinDrv hc
  obtain ⟨hJj, hJj0⟩ := continuous_joinDrv hcj
  have hT := joinTime_nonneg Δ D j
  have hv : fwdMapInv (stopDrv (Δ j) (D j)) t w ∈ H :=
    (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hS hS0 ht0 hw).1
  rw [succChart_inv_eq x hcj hv, QuantumZipper.RS.fwdMapInv_add_shift hJn hJn0 hT ht0 hw]
  have hsh : EqOn (QuantumZipper.RS.shiftDrive (joinDrv Δ D n) (joinTime Δ D j))
      (stopDrv (Δ j) (D j)) (Icc 0 t) := by
    intro u hu
    have hT1 : joinTime Δ D j + u ≤ joinTime Δ D (j + 1) := by
      rw [joinTime_succ]; linarith [hu.2]
    have hn1 : EqOn (joinDrv Δ D n) (joinDrv Δ D (j + 1)) (Icc 0 (joinTime Δ D (j + 1))) :=
      joinDrv_eqOn_of_le hjn
    have e1 := hn1 ⟨add_nonneg hT hu.1, hT1⟩
    have e2 := hn1 ⟨hT, (le_add_of_nonneg_right hu.1).trans hT1⟩
    change joinDrv Δ D n (joinTime Δ D j + u) - joinDrv Δ D n (joinTime Δ D j) = _
    rw [e1, e2]
    exact shiftDrive_joinDrv_eqOn hS0 ⟨hu.1, hu.2.trans ht⟩
  rw [LP.fwdMapInv_eq_of_eqOn_Icc (QuantumZipper.RS.continuous_shiftDrive hJn _) hS
    (QuantumZipper.RS.shiftDrive_zero _ _) hS0 ht0 hsh hw]
  exact congrArg (fun v => (x : ℂ) + v) (LP.fwdMapInv_eq_of_eqOn_Icc hJj hJn hJj0 hJn0 hT
    (fun r hr => (joinDrv_eqOn_of_le hjn.le hr).symm) hv)

/-- **The tip set of piece `j` of a live schedule** is the translated set of radial tips of the
joined driver at the times of piece `j`. -/
theorem tipSet_livePiece (x : ℝ) {n j : ℕ} (hjn : j < n) (hΔ : Δ j ≠ ⊤)
    (hc : ∀ i < n, Continuous (stopDrv (Δ i) (D i)) ∧ stopDrv (Δ i) (D i) 0 = 0) :
    (livePiece x Δ D j).1.tipSet (livePiece x Δ D j).2.1 (livePiece x Δ D j).2.2 =
      (fun z => (x : ℂ) + z) ''
        radialTips (joinDrv Δ D n) (joinTime Δ D j) (joinTime Δ D (j + 1)) := by
  have hS : min (Δ j) (D j).2 ≠ ⊤ := ne_top_of_le_ne_top hΔ (min_le_left _ _)
  have hy : ∀ t : ℝ≥0, (t : ℝ) ≤ stopTime (Δ j) (D j) →
      ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), (succChart x Δ D j).2.1
        (fwdMapInv (stopDrv (Δ j) (D j)) t ((y : ℂ) * Complex.I)) =
          (x : ℂ) + fwdMapInv (joinDrv Δ D n) (joinTime Δ D j + t) ((y : ℂ) * Complex.I) := by
    intro t ht
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyH : (y : ℂ) * Complex.I ∈ H := by
      change 0 < ((y : ℂ) * Complex.I).im
      simpa using hy
    exact succChart_inv_stopDrv_eq x hjn hc t.2 ht hyH
  ext z
  constructor
  · rintro ⟨t, ht, hlim⟩
    have htS : (t : ℝ) ≤ stopTime (Δ j) (D j) := by
      unfold stopTime
      exact_mod_cast ENNReal.le_toNNReal_of_coe_le ht hS
    refine ⟨z - x, ⟨joinTime Δ D j + t, le_add_of_nonneg_right t.2, ?_, ?_⟩, by ring⟩
    · rw [joinTime_succ]; linarith
    · have hlim' := hlim.sub_const (x : ℂ)
      refine hlim'.congr' ?_
      filter_upwards [hy t htS] with y hy'
      change (succChart x Δ D j).2.1 (fwdMapInv (stopDrv (Δ j) (D j)) t ((y : ℂ) * Complex.I)) - x = _
      rw [hy']
      ring
  · rintro ⟨w, ⟨s, hs1, hs2, hlim⟩, rfl⟩
    set t : ℝ≥0 := (s - joinTime Δ D j).toNNReal with htdef
    have ht : (t : ℝ) = s - joinTime Δ D j := Real.coe_toNNReal _ (by linarith)
    have htS : (t : ℝ) ≤ stopTime (Δ j) (D j) := by
      rw [ht]; rw [joinTime_succ] at hs2; linarith
    refine ⟨t, ?_, ?_⟩
    · have h1 : t ≤ (min (Δ j) (D j).2).toNNReal := by
        unfold stopTime at htS
        exact_mod_cast htS
      calc (t : ℝ≥0∞) ≤ ((min (Δ j) (D j).2).toNNReal : ℝ≥0∞) := ENNReal.coe_le_coe.2 h1
        _ = min (Δ j) (D j).2 := ENNReal.coe_toNNReal hS
    · have hs : joinTime Δ D j + (t : ℝ) = s := by rw [ht]; ring
      have hlim' := hlim.const_add (x : ℂ)
      rw [← hs] at hlim'
      refine hlim'.congr' ?_
      filter_upwards [hy t htS] with y hy'
      exact hy'.symm

/-- The stored pieces of a live GW2 run, and its (empty) connector arcs. -/
theorem run_pieces_arcs {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}
    (hgw : spec.2.1 = true) {θ : ℕ → ℝ} (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤) :
    ∀ k ≤ spec.2.2.length, AllSucc Δ D k →
      (ExplState.run κ b jumps spec D k).1 = (List.range k).map (livePiece spec.1 Δ D) ∧
        (ExplState.run κ b jumps spec D k).2.1 = []
  | 0, _, _ => by
    refine ⟨?_, ?_⟩ <;> simp [ExplState.run, ExplState.init]
  | k + 1, hk, hs => by
    obtain ⟨ih1, ih2⟩ := run_pieces_arcs hgw hprog hΔ k (Nat.le_of_succ_le hk) (allSucc_succ.1 hs).1
    obtain ⟨hlive, hchart⟩ :=
      (run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ D k (Nat.le_of_succ_le hk)).1
        (allSucc_succ.1 hs).1
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

/-- At time `0` the only radial tip is the origin. -/
theorem tendsto_fwdMapInv_zero (W : ℝ → ℝ) (hW : Continuous W) (hW0 : W 0 = 0) :
    Tendsto (fun y : ℝ => fwdMapInv W 0 (y * Complex.I)) (𝓝[>] 0) (𝓝 0) := by
  have hlin : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun y : ℝ => (y : ℂ) * Complex.I) :=
      Complex.continuous_ofReal.mul continuous_const
    have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  refine hlin.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyH : (y : ℂ) * Complex.I ∈ H := by
    change 0 < ((y : ℂ) * Complex.I).im
    simpa using hy
  exact (fwdMapInv_zero_time hW hW0 hyH).symm

/-- **The physical set of a live GW2 schedule** is the root plus the radial tips of the joined
driver of all its pieces, over the total own time. -/
theorem physSet_eq_radialTips {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}
    (hgw : spec.2.1 = true) {θ : ℕ → ℝ} (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤)
    (hs : AllSucc Δ D spec.2.2.length)
    (hc : ∀ i < spec.2.2.length, Continuous (stopDrv (Δ i) (D i)) ∧ stopDrv (Δ i) (D i) 0 = 0) :
    ExplState.physSet κ b jumps spec D =
      (fun z => (spec.1 : ℂ) + z) ''
        radialTips (joinDrv Δ D spec.2.2.length) 0 (joinTime Δ D spec.2.2.length) := by
  set n := spec.2.2.length with hn
  obtain ⟨hp, ha⟩ := run_pieces_arcs (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ n le_rfl hs
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
