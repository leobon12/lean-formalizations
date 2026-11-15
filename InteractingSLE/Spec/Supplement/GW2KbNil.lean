/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KbPack
import InteractingSLE.Spec.Supplement.GW2OmxInst

/-!
# Claim(k)'s base (GEOM2 round 12): the history `l = []` at one sample

Packet PROVE-GW2-GEOM2, round 12. For the history `l = []` the program is `[rootEntry, candidate]`, so the root piece
is the piece of index `0` of the future program and the stage starts at its end `T = historyTime c r [] = δ_root`.

* `specAngle_specDelta_nil`: the root piece's angle and own time;
* **`oldSuccess_nil_iff`**: the history succeeds iff the root piece lives past `T`;
* **`fwdHull_root_eq`**: on success, the hulls of the root piece and of the joined explored driver agree up to `T`;
* **`schedUnionS_nil_eq`**: on success, the stage-start union is `invHull W' s ∪ K^{root}_T`.

Deterministic (one sample).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Kb

open GW2Omx GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist
  Exist.Staged Exist.StagedLaw Sec5.Prop513Schedule GW2Olm

variable {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a : ℕ)

theorem historyTime_nil : historyTime c r [] = (rootEntry r.1).2 := rfl

theorem curIdx_nil : curIdx c r [] = 1 := rfl

theorem futSpec_nil_prog : (futSpec c r [] a).2.2 =
    Sum.inl ((rootEntry r.1).1, ((((rootEntry r.1).2 - 0 : ℝ≥0)) : ℝ≥0∞)) ::
      scheduleProgram (rootEntry r.1).2 [((candidateAngle c r a : ℝ), historyTime c r [] + candidateCap c r a)] :=
  rfl

/-- **The root piece's angle and own time** in the future program of `l = []`. -/
theorem specAngle_specDelta_nil : specAngle (futSpec c r [] a) 0 = (rootEntry r.1).1 ∧
    specDelta (futSpec c r [] a) 0 = ((historyTime c r [] : ℝ≥0) : ℝ≥0∞) := by
  have hlen : 0 < (scheduleProgram 0 (futureProgram c r [] a)).length := by
    rw [GW2Schedule.length_scheduleProgram]
    simp [futureProgram, historyProgram, schedOf]
  have h := isFlowProg_spec (rootPt r.1) true (futureProgram c r [] a) 0 hlen
  have h2 : (scheduleProgram 0 (futureProgram c r [] a))[0]? =
      some (Sum.inl ((rootEntry r.1).1, ((((rootEntry r.1).2 - 0 : ℝ≥0)) : ℝ≥0∞))) := rfl
  rw [h2] at h
  obtain ⟨h3, h4⟩ := Prod.mk.inj (Sum.inl.inj (Option.some.inj h))
  refine ⟨h3.symm, ?_⟩
  have h5 : specDelta (futSpec c r [] a) 0 = ((((rootEntry r.1).2 - 0 : ℝ≥0)) : ℝ≥0∞) := h4.symm
  rw [h5, tsub_zero]
  rfl

/-- **The history `[]` succeeds iff the root piece lives past its own time.** -/
theorem oldSuccess_nil_iff (ω : Ω) :
    oldSuccess c r [] ω ↔ ((historyTime c r [] : ℝ≥0) : ℝ≥0∞) < (futFam c r [] a 0 ω).2 := by
  constructor
  · intro hold
    have hs := Gm.allSucc_future_of_oldSuccess c r [] a ω hold 0 (by
      show 0 < (historyProgram c r []).length
      simp [historyProgram, schedOf])
    have e := (specAngle_specDelta_nil c r a).2
    change specDelta (futSpec c r [] a) 0 < (futFam c r [] a 0 ω).2 at hs
    rwa [e] at hs
  · intro h
    refine oldSuccess_of_allSucc_cur c r [] a fun j hj => ?_
    have hj0 : j = 0 := by
      have : j < 1 := hj
      omega
    subst hj0
    rw [(specAngle_specDelta_nil c r a).2]
    exact h

/-- On success the root piece's stopped driver is its driver up to `T`. -/
theorem stopDrv_root_eq {ω : Ω} (hold : oldSuccess c r [] ω) {u : ℝ} (hu : u ∈ Icc 0 (historyTime c r [] : ℝ)) :
    stopDrv (specDelta (futSpec c r [] a) 0) (futFam c r [] a 0 ω) u = (futFam c r [] a 0 ω).1 u.toNNReal := by
  refine Gm.stopDrv_eq_of_le ?_
  have hlt := (oldSuccess_nil_iff c r a ω).1 hold
  rw [(specAngle_specDelta_nil c r a).2]
  refine le_min ?_ ?_
  · exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hu.2)
  · exact (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hu.2)).trans hlt.le

/-- On success the root piece's stop time is `T`. -/
theorem stopTime_root_eq {ω : Ω} (hold : oldSuccess c r [] ω) :
    stopTime (specDelta (futSpec c r [] a) 0) (futFam c r [] a 0 ω) = (historyTime c r [] : ℝ) := by
  have hlt := (oldSuccess_nil_iff c r a ω).1 hold
  unfold stopTime
  rw [(specAngle_specDelta_nil c r a).2, min_eq_left hlt.le, ENNReal.toNNReal_coe]

/-- **On success the joined explored driver is the root piece's stopped driver up to `T`.** -/
theorem schedW_eq_stopDrv_root {ω : Ω} (hold : oldSuccess c r [] ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r [] a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r [] a) ω ⟨j, hj⟩)))
    (hS0 : stopDrv (specDelta (futSpec c r [] a) 0) (futFam c r [] a 0 ω) 0 = 0)
    {u : ℝ} (hu : u ∈ Icc 0 (historyTime c r [] : ℝ)) :
    GW2Rd.schedW c r [] a u.toNNReal ω = stopDrv (specDelta (futSpec c r [] a) 0) (futFam c r [] a 0 ω) u := by
  set Δ := specDelta (futSpec c r [] a) with hΔ
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => futFam c r [] a j ω with hD
  have hord : (historyProgram c r []).Pairwise (fun p q => p.2 < q.2) := List.pairwise_singleton _ _
  have hTOh : TimeOrdered 0 (historyProgram c r []) := Gm.timeOrdered_of_pairwise_lt hord
  have hle : u.toNNReal ≤ historyTime c r [] + candidateCap c r a := by
    rw [Real.toNNReal_le_iff_le_coe]
    have := hu.2
    have h2 : (historyTime c r [] : ℝ) ≤ ((historyTime c r [] + candidateCap c r a : ℝ≥0) : ℝ) := by
      exact_mod_cast le_add_of_nonneg_right zero_le
    linarith
  have h1 := Gm.futureJoined_eq_joinDrv c r [] a ω hTOh hold hgood hle
  have hJ1 : joinTime Δ D 1 = (historyTime c r [] : ℝ) := by
    change 0 + stopTime (Δ 0) (D 0) = _
    rw [zero_add]
    exact stopTime_root_eq c r a hold
  have hsw : GW2Rd.schedW c r [] a u.toNNReal ω = Gm.futureJoined c r [] a ω u.toNNReal :=
    congrFun (GW2Rd.schedW_of_oldSuccess c r [] a hold) u.toNNReal
  rw [hsw, h1, Real.coe_toNNReal _ hu.1]
  change joinDrv Δ D (1 + 1) u = _
  rw [joinDrv_eqOn (Δ := Δ) (D := D) 1 ⟨hu.1, hJ1 ▸ hu.2⟩]
  change (if u ≤ joinTime Δ D 0 then joinDrv Δ D 0 u else
    joinDrv Δ D 0 (joinTime Δ D 0) + stopDrv (Δ 0) (D 0) (u - joinTime Δ D 0)) = _
  have hJ0 : joinTime Δ D 0 = 0 := rfl
  rw [hJ0]
  split_ifs with h
  · have hu0 : u = 0 := le_antisymm h hu.1
    rw [hu0]
    exact hS0.symm
  · change (0 : ℝ) + stopDrv (Δ 0) (D 0) (u - 0) = _
    rw [zero_add, sub_zero]

/-- **On success the root piece's hulls up to `T` are the hulls of the joined explored driver.** -/
theorem fwdHull_root_eq {ω : Ω} (hold : oldSuccess c r [] ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r [] a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r [] a) ω ⟨j, hj⟩)))
    (hc0 : Continuous (stopDrv (specDelta (futSpec c r [] a) 0) (futFam c r [] a 0 ω)) ∧
      stopDrv (specDelta (futSpec c r [] a) 0) (futFam c r [] a 0 ω) 0 = 0)
    (hreg : IsRegularDriver (futFam c r [] a 0 ω)) {u : ℝ≥0} (hu : u ≤ historyTime c r []) :
    fwdHull (fun q : ℝ => (futFam c r [] a 0 ω).1 q.toNNReal) (u : ℝ) =
      fwdHull (fun q : ℝ => GW2Rd.schedW c r [] a q.toNNReal ω) (u : ℝ) := by
  set e := futFam c r [] a 0 ω with he
  have hlt := (oldSuccess_nil_iff c r a ω).1 hold
  obtain ⟨T', hT'1, hT'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
  have hTT' : (historyTime c r [] : ℝ) < T' := by exact_mod_cast hT'1
  have hcont : ContinuousOn (fun q : ℝ => e.1 q.toNNReal) (Icc 0 (T' : ℝ)) := by
    refine hreg.1.comp continuous_real_toNNReal.continuousOn ?_
    intro q hq
    show ((q.toNNReal : ℝ≥0) : ℝ≥0∞) < e.2
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hq.2)) hT'2
  have hut : (u : ℝ) < T' := lt_of_le_of_lt (by exact_mod_cast hu) hTT'
  rw [LocalExt.fwdHull_congr_of_eqOn_of_lt u.coe_nonneg hut Ito.clampDrv_eqOn.symm]
  have hW : Continuous fun q : ℝ => GW2Rd.schedW c r [] a q.toNNReal ω := by
    rw [show (fun q : ℝ => GW2Rd.schedW c r [] a q.toNNReal ω) =
      fun q : ℝ => Gm.futureJoined c r [] a ω q.toNNReal from
        funext fun q => congrFun (GW2Rd.schedW_of_oldSuccess c r [] a hold) q.toNNReal]
    exact (Gm.continuous_futureJoined c r [] a ω).1.comp continuous_real_toNNReal
  refine QuantumZipper.Thm14FromThm13.fwdHull_eq_of_eqOn (Ito.continuous_clampDrv T'.coe_nonneg hcont) hW
    u.coe_nonneg fun q hq => ?_
  have hqT : q ∈ Icc 0 (historyTime c r [] : ℝ) := ⟨hq.1, hq.2.trans (by exact_mod_cast hu)⟩
  show Ito.clampDrv (fun q : ℝ => e.1 q.toNNReal) T' q = GW2Rd.schedW c r [] a q.toNNReal ω
  rw [Ito.clampDrv_eqOn ⟨hq.1, hq.2.trans hut.le⟩, schedW_eq_stopDrv_root c r a hold hgood hc0.2 hqT,
    stopDrv_root_eq c r a hold hqT]

/-- **On success the stage-start union of `l = []` is the retained hull and the root piece's hull at `T`.** -/
theorem schedUnionS_nil_eq {ω : Ω} (hold : oldSuccess c r [] ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r [] a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r [] a) ω ⟨j, hj⟩)))
    (hc0 : Continuous (stopDrv (specDelta (futSpec c r [] a) 0) (futFam c r [] a 0 ω)) ∧
      stopDrv (specDelta (futSpec c r [] a) 0) (futFam c r [] a 0 ω) 0 = 0)
    (hreg : IsRegularDriver (futFam c r [] a 0 ω)) (hW'0 : c.W 0 ω = 0)
    (hW'c : ContinuousOn (fun u => c.W u ω) {u | (u : ℝ≥0∞) < c.ζ ω}) (hsζ : (c.s : ℝ≥0∞) < c.ζ ω) :
    GW2Sdi.schedUnionS c r [] a 0 ω = Supp8.Q3Rel.invHull (fun u : ℝ => c.W u.toNNReal ω) (c.s : ℝ) ∪
      fwdHull (fun q : ℝ => (futFam c r [] a 0 ω).1 q.toNNReal) (historyTime c r [] : ℝ) := by
  rw [GW2Sdi.schedUnionS_eq, Supp8.RelSafeS.invHull_record_eq hW'0 hW'c hsζ,
    fwdHull_root_eq c r a hold hgood hc0 hreg le_rfl]
  simp only [hold, ↓reduceIte, GW2Rd.schedHull, add_zero]

end InteractingSLE.Theorem14.GW2Kb
