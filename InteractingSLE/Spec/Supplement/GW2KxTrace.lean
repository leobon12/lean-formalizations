/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmTraceS

/-!
# The explored trace after the launch through the launch chart, at a root `x ≥ 0`

Packet PROVE-GW2-GEOM2, round 14 (D49: the root-`x` side of Claim(k)). STAGEMEAN's `GW2Psm.sample_trace_corr` at a
root `x = rootPt r.1 ≥ 0`: the launch chart's inverse is `x + fwdMapInv` (`succChart_inv_eq x`), so the explored
trace, translated by `x`, is the boundary extension of `cL`'s inverse at the current piece's trace.

* **`sample_trace_corrX`**: `x + ηe (T + u) = f (α u)` for `u ≤ t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW2Kx

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist Exist.Staged
  Exist.StagedLaw Sec5.Prop513Schedule GW2Omx GW2Psm

/-- **The explored trace after the launch through the launch chart** (root `x ≥ 0`, one sample). -/
theorem sample_trace_corrX {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) (t : ℝ≥0) (ω : Ω) (hold : oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)))
    {cL : Chart} {θ : ℝ} (hl : GW2Olm.curLaunch c r l a ω = some (cL, θ))
    (hc : ∀ j < GW2Olm.curIdx c r l + 1, Continuous (stopDrv (specDelta (GW2Olm.futSpec c r l a) j)
        (GW2Olm.futFam c r l a j ω)) ∧ stopDrv (specDelta (GW2Olm.futSpec c r l a) j) (GW2Olm.futFam c r l a j ω) 0 = 0)
    (hext : GW1P.HasProperBdryExt cL) (htcap : t < candidateCap c r a)
    (htζ : (t : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2)
    (hreg : IsRegularDriver (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω)) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1
      (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 α) {ηe : ℝ≥0 → ℂ}
    (hηe : IsGeneratingTrace (fun u => GW2Rd.schedW c r l a u ω) ⊤ ηe) :
    ∃ f : ℂ → ℂ, (∀ p ∈ Hbar, Tendsto cL.2.1 (𝓝[H] p) (𝓝 (f p))) ∧
      ∀ u ≤ t, (rootPt r.1 : ℂ) + ηe (historyTime c r l + u) = f (α u) := by
  obtain ⟨f, -, hf, -⟩ := hext
  refine ⟨f, hf, fun u hu => ?_⟩
  set spec := GW2Olm.futSpec c r l a with hspec
  set Δ := specDelta spec with hΔ
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => GW2Olm.futFam c r l a j ω with hD
  set k := GW2Olm.curIdx c r l with hk
  set L := futureProgram c r l a with hL
  set T : ℝ≥0 := historyTime c r l with hT
  have hlenL : L.length = k + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
  have hlen : spec.2.2.length = k + 1 := (GW2Schedule.length_scheduleProgram 0 L).trans hlenL
  have hgw : spec.2.1 = true := rfl
  have hprog := isFlowProg_spec (rootPt r.1) true L
  have hΔt : ∀ j, Δ j ≠ ⊤ := specDelta_ne_top _
  have hs : AllSucc Δ D k := by
    by_contra hn
    have h0 := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) hgw hprog hΔt D
      (show k < spec.2.2.length by omega)).2 hn
    have h1 : GW2Olm.curLaunch c r l a ω = none := h0
    rw [h1] at hl
    simp at hl
  have hl' := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) hgw hprog hΔt D
    (show k < spec.2.2.length by omega)).1 hs
  have hcL : cL = succChart (rootPt r.1) Δ D k := by
    have h1 : GW2Olm.curLaunch c r l a ω = some (succChart spec.1 Δ D k, GW2Tip.specAngle spec k) := hl'
    rw [hl] at h1
    exact (Prod.mk.inj (Option.some.inj h1)).1
  have hck : ∀ j < k, Continuous (stopDrv (Δ j) (D j)) ∧ stopDrv (Δ j) (D j) 0 = 0 :=
    fun j hj => hc j (Nat.lt_succ_of_lt hj)
  obtain ⟨hJ, hJ0⟩ := continuous_joinDrv hck
  obtain ⟨hJ1, hJ10⟩ := continuous_joinDrv hc
  have hTOh : TimeOrdered 0 (historyProgram c r l) := Gm.timeOrdered_of_pairwise_lt hord
  have hTOf : TimeOrdered 0 L := Gm.timeOrdered_of_pairwise_lt (GW2Olm.pairwise_lt_futureProgram c r l a hord)
  have hJT : joinTime Δ D k = (T : ℝ) := by
    have h1 : joinTime (specDelta (schedSpec (rootPt r.1) L)) D k = schedTime 0 L k :=
      Gm.joinTime_eq_schedTime (rootPt r.1) hTOf (by omega) hs
    refine h1.trans ?_
    have h2 : schedTime 0 L k = schedTime 0 (historyProgram c r l) (historyProgram c r l).length :=
      schedTime_append 0 _ le_rfl
    rw [h2, Gm.schedTime_length_eq_lastTime, ← GW2Sde.historyTime_eq_lastTime]
  have hTn : (0 : ℝ) ≤ T := T.coe_nonneg
  -- the launch chart's inverse
  have hinv : ∀ w ∈ H, cL.2.1 w = (rootPt r.1 : ℂ) + fwdMapInv (joinDrv Δ D k) (T : ℝ) w := by
    intro w hw
    rw [hcL, succChart_inv_eq (rootPt r.1) hck hw, hJT]
  -- the explored driver
  set J' : ℝ → ℝ := fun u => GW2Rd.schedW c r l a u.toNNReal ω with hJ'def
  have hJ'f : ∀ u : ℝ, J' u = Gm.futureJoined c r l a ω u.toNNReal := fun u => by
    rw [hJ'def]
    exact congrFun (GW2Rd.schedW_of_oldSuccess c r l a hold) u.toNNReal
  obtain ⟨hFc, hF0⟩ := Gm.continuous_futureJoined c r l a ω
  have hJ'c : Continuous J' := by
    have e : J' = fun u => Gm.futureJoined c r l a ω u.toNNReal := funext hJ'f
    rw [e]
    exact hFc.comp continuous_real_toNNReal
  have hJ'0 : J' 0 = 0 := by rw [hJ'f, Real.toNNReal_zero, hF0]
  have hJ'j : ∀ u : ℝ, 0 ≤ u → u ≤ (T : ℝ) + candidateCap c r a → J' u = joinDrv Δ D (k + 1) u := by
    intro u hu0 hu
    rw [hJ'f]
    have hle : u.toNNReal ≤ historyTime c r l + candidateCap c r a := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact_mod_cast hu
    have h := Gm.futureJoined_eq_joinDrv c r l a ω hTOh hold hgood hle
    rw [h, Real.coe_toNNReal _ hu0]
    rfl
  have heq : EqOn (joinDrv Δ D k) J' (Icc 0 (T : ℝ)) := by
    intro u hu
    rw [hJ'j u hu.1 (hu.2.trans (le_add_of_nonneg_right (candidateCap c r a).coe_nonneg))]
    exact (joinDrv_eqOn (Δ := Δ) (D := D) k ⟨hu.1, hJT ▸ hu.2⟩).symm
  have hinvJ : ∀ w ∈ H, cL.2.1 w - (rootPt r.1 : ℂ) = fwdMapInv J' (T : ℝ) w := fun w hw => by
    rw [hinv w hw, add_sub_cancel_left]
    exact QuantumZipper.RegCont.fwdMapInv_congr hJ hJ0 hJ'c hJ'0 heq ⟨hTn, le_rfl⟩ hw
  -- the piece and its restarted driver
  have hΔk : Δ k = (candidateCap c r a : ℝ≥0∞) := futureProgram_delta c r l a
  obtain ⟨hPc, hP0⟩ := hc k (Nat.lt_succ_self k)
  have hmin_ne : min (Δ k) (D k).2 ≠ ⊤ := ne_top_of_le_ne_top (hΔt k) (min_le_left _ _)
  have htst : (t : ℝ) < stopTime (Δ k) (D k) := by
    have h1 : (t : ℝ≥0∞) < min (Δ k) (D k).2 := lt_min (by rw [hΔk]; exact_mod_cast htcap) htζ
    have h2 : t < (min (Δ k) (D k).2).toNNReal := by
      rwa [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hmin_ne]
    exact_mod_cast h2
  set t₂ : ℝ := ((t : ℝ) + stopTime (Δ k) (D k)) / 2 with ht₂
  have hut₂ : (u : ℝ) < t₂ := by
    have : (u : ℝ) ≤ t := by exact_mod_cast hu
    rw [ht₂]; linarith
  have ht₂s : t₂ < stopTime (Δ k) (D k) := by rw [ht₂]; linarith
  have hcapst : stopTime (Δ k) (D k) ≤ candidateCap c r a := by
    have h1 : min (Δ k) (D k).2 ≤ (candidateCap c r a : ℝ≥0∞) := (min_le_left _ _).trans hΔk.le
    have h2 : (min (Δ k) (D k).2).toNNReal ≤ candidateCap c r a := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hmin_ne]
      exact h1
    exact_mod_cast h2
  have hshift : ∀ x ∈ Icc (0 : ℝ) t₂,
      QuantumZipper.RS.shiftDrive (fun s : ℝ => GW2Rd.schedW c r l a s.toNNReal ω) (T : ℝ) x =
        (D k).1 x.toNNReal := by
    intro x hx
    have hxs : x ∈ Icc (0 : ℝ) (stopTime (Δ k) (D k)) := ⟨hx.1, hx.2.trans ht₂s.le⟩
    have h1 : J' ((T : ℝ) + x) = joinDrv Δ D (k + 1) ((T : ℝ) + x) :=
      hJ'j _ (add_nonneg hTn hx.1) (by linarith [hxs.2, hcapst])
    have h2 : J' (T : ℝ) = joinDrv Δ D (k + 1) (T : ℝ) :=
      hJ'j _ hTn (le_add_of_nonneg_right (candidateCap c r a).coe_nonneg)
    have h3 := shiftDrive_joinDrv_eqOn (Δ := Δ) (D := D) hP0 hxs
    simp only [QuantumZipper.RS.shiftDrive, hJT] at h3
    have h4 : stopDrv (Δ k) (D k) x = (D k).1 x.toNNReal := by
      refine Gm.stopDrv_eq_of_le ?_
      have h5 : x.toNNReal ≤ (min (Δ k) (D k).2).toNNReal := by
        rw [Real.toNNReal_le_iff_le_coe]
        exact hxs.2
      calc ((x.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ((min (Δ k) (D k).2).toNNReal : ℝ≥0∞) := ENNReal.coe_le_coe.2 h5
        _ = min (Δ k) (D k).2 := ENNReal.coe_toNNReal hmin_ne
    change J' ((T : ℝ) + x) - J' (T : ℝ) = _
    rw [h1, h2, h3, h4]
  have huζ : (u : ℝ≥0∞) < (D k).2 := (ENNReal.coe_le_coe.2 hu).trans_lt htζ
  have hαbar : α u ∈ Hbar := by
    have : (𝓝[H] (0 : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℂ) ∈ Hbar by simp [QuantumZipper.Hbar])
    have hcl : α u ∈ closure {z : ℂ | 0 < z.im} := by
      have hSh : Continuous (QuantumZipper.RS.shiftDrive J' (T : ℝ)) :=
        QuantumZipper.RS.continuous_shiftDrive hJ'c _
      have hcongr : fwdMapInv (QuantumZipper.RS.shiftDrive J' (T : ℝ)) u =
          fwdMapInv (fun s : ℝ => (D k).1 s.toNNReal) u :=
        InteractingSLE.fwdMapInv_eq_of_eqOn u.coe_nonneg hut₂ hshift
      have hSh0 : QuantumZipper.RS.shiftDrive J' (T : ℝ) 0 = 0 := by
        simp [QuantumZipper.RS.shiftDrive]
      refine mem_closure_of_tendsto (hα.tendsto_fwdMapInv_tip hreg.1 hreg.2.1 huζ)
        (eventually_mem_nhdsWithin.mono fun w hw => ?_)
      rw [← hcongr]
      exact QuantumZipper.RS.fwdMapInv_mem_H hSh hSh0 u.coe_nonneg hw
    rw [Complex.closure_setOfPred_lt_im] at hcl
    exact hcl
  have hfJ : Tendsto (fwdMapInv J' (T : ℝ)) (𝓝[H] (α u)) (𝓝 (f (α u) - (rootPt r.1 : ℂ))) :=
    ((hf (α u) hαbar).sub_const (rootPt r.1 : ℂ)).congr' (eventually_mem_nhdsWithin.mono hinvJ)
  have hJnc : Continuous fun s => GW2Rd.schedW c r l a s ω := by
    rw [show (fun s => GW2Rd.schedW c r l a s ω) = Gm.futureJoined c r l a ω from
      GW2Rd.schedW_of_oldSuccess c r l a hold]
    exact hFc
  have hJn0 : GW2Rd.schedW c r l a 0 ω = 0 := by
    rw [congrFun (GW2Rd.schedW_of_oldSuccess c r l a hold) 0]
    exact hF0
  have h := trace_join_eq_ext (f := fun z => f z - (rootPt r.1 : ℂ)) hJnc hJn0 hηe T hα hreg.1 hreg.2.1 huζ hut₂
    hshift hfJ
  rw [h]
  ring

end InteractingSLE.Theorem14.GW2Kx
