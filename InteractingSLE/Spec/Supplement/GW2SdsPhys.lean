/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdsRel
import InteractingSLE.Spec.Supplement.GW2OmxChain2
import InteractingSLE.Spec.Supplement.GW2GmCross
import InteractingSLE.Spec.Supplement.GW2RuShell

/-!
# The near structure (N3), step G: the explored tip at a history time is interior to the previous hull

Packet PROVE-GW2-SDE (round 18). At every alive history `l` of J32 and every candidate `a`, the explored curve at the
history time `T_l` is an interior point of `ℍ \ K_{T'}`, `T'` the previous switching time (for `l = []`: `T' = 0`, the
root piece). Proof:

* STAGEMEAN's `GW2Omx.ae_switchTips_cur`: on success the switching tips of the schedule are interior stops of their
  pieces (Theorem 1.3 at the deterministic times);
* GEOM2's `Gm.futureJoined_eq_joinDrv_hist` and `Swc.shiftDrive_joinDrv_eqOn`: the explored driver shifted at the
  previous switch is the last piece on its window;
* **`mem_diff_of_isInteriorStop`** (deterministic): an interior stop of the piece read off a shifted global trace puts
  the original trace point in `ℍ \ K_a` (GEOM2's `Gm.mem_diff_of_shiftTip_mem_H`);
* **`ae_tip_mem_diff_hist`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMapInv)
open QuantumZipper.RS (shiftDrive)

universe u

namespace InteractingSLE.Theorem14.GW2Sds

open Restart Exist Exist.Staged Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Schedule GW2Tip GW2Rd

/-- **An interior stop of a piece read off a shifted global trace**: if the shifted driver `W(a + ·) − W(a)` is the
piece `e` stopped at `Δ` on `[0, Δ]` and the stop is interior, then `η(a + Δ)` is an interior point of `ℍ \ K_a`. -/
theorem mem_diff_of_isInteriorStop {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) {a : ℝ} (ha : 0 ≤ a) {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    {Δ : ℝ≥0} (hΔ : (Δ : ℝ≥0∞) < e.2)
    (hagree : EqOn (shiftDrive W a) (stopDrv (Δ : ℝ≥0∞) e) (Icc 0 (Δ : ℝ)))
    (hint : GW2Later.IsInteriorStop e.1 (Δ : ℝ≥0∞)) :
    η (a + Δ) ∈ H \ fwdHull W a := by
  obtain ⟨p, hpH, hp⟩ := hint
  obtain ⟨hψ, -⟩ := hη.isLoewnerTrace_shift_and_extendFrom hW hW0 ha
  have hWs := QuantumZipper.RS.continuous_shiftDrive hW a
  have hWs0 := QuantumZipper.RS.shiftDrive_zero W a
  obtain ⟨hsc, -⟩ := Gm.continuous_stopDrv_of_lt he hΔ ENNReal.coe_ne_top
  have hstop : (fun r : ℝ => e.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (Δ : ℝ≥0∞)).toNNReal) =
      stopDrv (Δ : ℝ≥0∞) e := by
    funext r
    simp only [stopDrv, retOf, min_eq_left hΔ.le]
  have hF : ∀ z, fwdMapInv (stopDrv (Δ : ℝ≥0∞) e) Δ z = fwdMapInv (shiftDrive W a) Δ z :=
    LocalExt.fwdMapInv_congr_of_continuousOn hsc.continuousOn hWs.continuousOn Δ.coe_nonneg
      (lt_add_one (Δ : ℝ)) (fun r hr => (hagree hr).symm)
  have hLT : IsLoewnerTraceLT (shiftDrive W a) ((Δ : ℝ) + 1) (loewnerTip (shiftDrive W a)) :=
    ⟨hψ.1, hψ.2.1.mono Ico_subset_Ici_self, fun t ht _ => hψ.2.2 t ht⟩
  have htip := hLT.tendsto_fwdMapInv_mul_I hWs hWs0 Δ.coe_nonneg (lt_add_one _)
  have hp' : Tendsto (fun y : ℝ => fwdMapInv (shiftDrive W a) Δ (y * Complex.I)) (𝓝[>] 0) (𝓝 p) := by
    refine hp.congr fun y => ?_
    show fwdMapInv (fun r : ℝ => e.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (Δ : ℝ≥0∞)).toNNReal)
      (((Δ : ℝ≥0∞).toNNReal : ℝ≥0) : ℝ) (y * Complex.I) = _
    rw [ENNReal.toNNReal_coe, hstop]
    exact hF _
  have hpe : loewnerTip (shiftDrive W a) Δ = p := tendsto_nhds_unique htip hp'
  exact GW2TipSystem.Gm.mem_diff_of_shiftTip_mem_H hη hW hW0 ha Δ.coe_nonneg (hpe ▸ hpH)

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **At every alive history the explored tip at the history time is interior to the previous hull**: almost surely,
for every candidate `a` whose explored driver generates a trace, `γ(T_l)` is an interior point of `ℍ \ K_{T'}`, with
`T'` the start of the last history piece. -/
theorem ae_tip_mem_diff_hist (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      IsGeneratingTrace (fun t => schedW c r l a t ω) ⊤ (schedTr c r l a ω) →
      schedTr c r l a ω (RootJ31.historyTime c r l) ∈
        H \ fwdHull (fun t : ℝ => schedW c r l a t.toNNReal ω)
          (schedTime 0 (RootJ31.historyProgram c r l) ((RootJ31.historyProgram c r l).length - 1) : ℝ) := by
  classical
  set x := rootPt r.1 with hx
  set Lh := RootJ31.historyProgram c r l with hLh
  set m := Lh.length with hm
  by_cases hpw : Lh.Pairwise (fun p q => p.2 < q.2)
  swap
  · exact Eventually.of_forall fun ω halive =>
      absurd (RootJ32.pairwise_lt_historyProgram_of_alive c r l ω halive) hpw
  filter_upwards [GW2Omx.ae_switchTips_cur h13 c r l a hpw, Gm.ae_futureJoined_trace h13 c r]
    with ω hsw hjoin halive hγ
  have hold := RootJ32.oldSuccess_of_alive c r l ω halive
  have hord : Sec5.Prop513Schedule.TimeOrdered 0 Lh := RootJ32.timeOrdered_historyProgram_of_alive c r l ω halive
  obtain ⟨hgood, -⟩ := hjoin l a hold
  set Lf := RootJ31.futureProgram c r l a with hLf
  set Δh := specDelta (schedSpec x Lh) with hΔh
  set Dh := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lh) j ω with hDh
  have hsh : AllSucc Δh Dh m := (RootJ31.oldSuccess_iff_allSucc c r l ω).mp hold
  have hm1 : 1 ≤ m := by rw [hm, hLh, GW2Ru.length_historyProgram]; omega
  set j := m - 1 with hj
  have hjm : j < m := by omega
  have hjm1 : j + 1 = m := by omega
  have hLflen : Lf.length = m + 1 := by
    simp only [hLf, RootJ31.futureProgram, List.length_append, List.length_singleton, hm, hLh]
  -- the future family succeeds on the history pieces
  have hfs : AllSucc (schedDelta 0 Lf) (fun i => GW2Olm.futFam c r l a i ω) m := by
    intro i hi
    have h1 := Gm.allSucc_future_of_oldSuccess c r l a ω hold i hi
    rwa [Gm.specDelta_schedSpec x (by omega : i < Lf.length)] at h1
  have hint := hsw hfs j hjm
  -- the last history piece
  have hD : GW2Olm.futFam c r l a j ω = Dh j :=
    RootC11.canonSpecFam_append c.hκ c.h12p c.βA c.c₀ c.h x _ hjm ω
  have hinstrH : instrTime (schedSpec x Lh) j = schedDelta 0 Lh j := by
    have hi := isFlowProg_scheduleProgram 0 Lh j (by rw [GW2Schedule.length_scheduleProgram]; exact hjm)
    simp only [instrTime, schedSpec, hi]
  have hinstr : instrTime (GW2Olm.futSpec c r l a) j = Δh j := by
    change instrTime (schedSpec x (Lh ++ _)) j = _
    rw [instrTime_schedSpec_append x _ hjm, hinstrH, hΔh, Gm.specDelta_schedSpec x hjm]
  have hlt : Δh j < (Dh j).2 := hsh j hjm
  have hstopeq : GW2aMulti.pieceStop (GW2Olm.futSpec c r l a) (fun i => GW2Olm.futFam c r l a i ω) j = Δh j := by
    unfold GW2aMulti.pieceStop
    rw [hinstr]
    show min (Δh j) (GW2Olm.futFam c r l a j ω).2 = Δh j
    rw [hD, min_eq_left hlt.le]
  change GW2Later.IsInteriorStop (GW2Olm.futFam c r l a j ω).1
    (GW2aMulti.pieceStop (GW2Olm.futSpec c r l a) (fun i => GW2Olm.futFam c r l a i ω) j) at hint
  rw [hstopeq, hD] at hint
  have hΔfin : Δh j ≠ ⊤ := specDelta_ne_top _ _
  set Δ : ℝ≥0 := (Δh j).toNNReal with hΔdef
  have hΔe : (Δ : ℝ≥0∞) = Δh j := ENNReal.coe_toNNReal hΔfin
  rw [← hΔe] at hint hlt
  -- the switching times
  have hJj : Swc.joinTime Δh Dh j = (schedTime 0 Lh j : ℝ) :=
    Gm.joinTime_eq_schedTime x hord hjm.le (hsh.mono hjm.le)
  have hJm : Swc.joinTime Δh Dh m = (RootJ31.historyTime c r l : ℝ) :=
    Gm.joinTime_eq_schedTime x hord le_rfl hsh
  have hstopT : stopTime (Δh j) (Dh j) = (Δ : ℝ) := by
    unfold stopTime
    rw [← hΔe, min_eq_left hlt.le, ENNReal.toNNReal_coe]
  have hJsucc : Swc.joinTime Δh Dh m = Swc.joinTime Δh Dh j + Δ := by
    rw [← hjm1, Swc.joinTime_succ, hstopT]
  have hTsum : (schedTime 0 Lh j : ℝ) + Δ = RootJ31.historyTime c r l := by
    rw [← hJj, ← hJsucc, hJm]
  -- the explored driver and its trace
  have hfj : schedW c r l a = fun t ω' => if RootJ31.oldSuccess c r l ω' then Gm.futureJoined c r l a ω' t else 0 :=
    rfl
  have hWf : ∀ t, schedW c r l a t ω = Gm.futureJoined c r l a ω t := fun t => by
    rw [hfj]; simp only [hold, ↓reduceIte]
  set W' : ℝ → ℝ := fun t : ℝ => schedW c r l a t.toNNReal ω with hW'
  obtain ⟨hfc, hf0⟩ := Gm.continuous_futureJoined c r l a ω
  have hW'c : Continuous W' := by
    have e : W' = fun t : ℝ => Gm.futureJoined c r l a ω t.toNNReal := funext fun t => hWf _
    rw [e]
    exact hfc.comp continuous_real_toNNReal
  have hW'0 : W' 0 = 0 := by
    simp only [hW', Real.toNNReal_zero, hWf, hf0]
  have hη := isLoewnerTrace_of_isGeneratingTrace hγ
  -- the shifted driver is the last piece on its window
  have hjd := Gm.futureJoined_eq_joinDrv_hist c r l a ω hord hold hgood
  have hS0 : stopDrv (Δh j) (Dh j) 0 = 0 :=
    (Gm.continuous_stopDrv_of_lt (isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x _ _ (c.h ω) j)
      (hΔe ▸ hlt) hΔfin).2
  have hsw' := Swc.shiftDrive_joinDrv_eqOn (Δ := Δh) (D := Dh) (k := j) hS0
  rw [hjm1, hstopT] at hsw'
  have hT0 : (0 : ℝ) ≤ schedTime 0 Lh j := NNReal.coe_nonneg _
  have hagree : EqOn (shiftDrive W' (schedTime 0 Lh j : ℝ)) (stopDrv (Δ : ℝ≥0∞) (Dh j)) (Icc 0 (Δ : ℝ)) := by
    intro u hu
    rw [hΔe, ← hsw' hu]
    have hJW : ∀ t : ℝ, 0 ≤ t → t ≤ RootJ31.historyTime c r l → W' t = Swc.joinDrv Δh Dh m t := by
      intro t ht0 htT
      have htT' : t.toNNReal ≤ RootJ31.historyTime c r l := Real.toNNReal_le_iff_le_coe.2 htT
      rw [show W' t = schedW c r l a t.toNNReal ω from rfl, hWf, hjd _ htT', Real.coe_toNNReal t ht0]
    simp only [QuantumZipper.RS.shiftDrive, hJj]
    rw [hJW _ (add_nonneg hT0 hu.1) (by rw [← hTsum]; linarith [hu.2]),
      hJW _ hT0 (by rw [← hTsum]; linarith [Δ.coe_nonneg])]
  have hmem := mem_diff_of_isInteriorStop hW'c hW'0 hη hT0
    (isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x _ _ (c.h ω) j) hlt hagree hint
  rw [hTsum, Real.toNNReal_coe] at hmem
  exact hmem

end InteractingSLE.Theorem14.GW2Sds
