/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NiUncGlue
import InteractingSLE.Spec.Supplement.GW2TlWord
import InteractingSLE.Spec.Supplement.GW2GmPrefix
import InteractingSLE.Spec.Supplement.GW2SwBCat
import InteractingSLE.Spec.Supplement.SB2JwFull
import InteractingSLE.Spec.Sec7.StripWallVersion
import InteractingSLE.Spec.Supplement.GW2RdLife

/-!
# The uncapped joined driver is transient

Packet PROVE-GW2-NEARIMG2 (D50). On a time-ordered history:
* if the piece dies (`uncLife < ⊤`), the uncapped driver is frozen after `T + ζ` (the capped candidates past the death
  read the piece stopped at its death, `Swc.joinDrv`), so its trace is transient (`tendsto_norm_trace_of_frozen`);
* if it lives forever, the uncapped driver is the history followed by the whole piece (`GW2Rd.shiftNN_schedW`), the
  piece has a transient generating trace (Theorem 1.3's `ζ = ⊤` clause, `SB.Lk.ae_pieceRegular_full_of_regular`), and
  the joined trace of a transient continuation is transient (`tendsto_joinedTrace_bdry`: the prefix's inverse map,
  extended to the boundary, moves points a bounded distance; boundary contacts allowed).

* **`tendsto_joinedTrace_bdry`** (deterministic);
* `uncW_frozen`, `uncW_eq_catPath` (one sample);
* **`uncRegStatement`**: `UncRegStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)

universe u

namespace InteractingSLE.Theorem14.GW2Ni

open Exist StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd

/-- **The joined trace of a transient continuation is transient**, for any generating continuation (boundary
contacts allowed): the prefix's inverse map, extended to the boundary, moves points a bounded distance. -/
theorem tendsto_joinedTrace_bdry {w₀ w₁ : ℝ≥0 → ℝ} {η₀ η₁ : ℝ≥0 → ℂ} {a : ℝ≥0} (h₀ : Continuous w₀)
    (h00 : w₀ 0 = 0) (hη₀ : IsGeneratingTrace w₀ a η₀) (h₁ : Continuous w₁) (h10 : w₁ 0 = 0)
    (hη₁ : IsGeneratingTrace w₁ ⊤ η₁) (ht₁ : Tendsto (fun s => ‖η₁ s‖) atTop atTop) :
    Tendsto (fun t => ‖LoewnerConcat.joinedTrace w₀ η₀ a η₁ t‖) atTop atTop := by
  have hW : Continuous (Ito.rpath w₀) := h₀.comp continuous_real_toNNReal
  have hW0 : Ito.rpath w₀ 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using h00
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 a.coe_nonneg
  have hB := (LoewnerConcat.prefix_boundary h₀ h00 hη₀).1
  have hext : ∀ p ∈ Hbar, ‖extendFrom H (fwdMapInv (Ito.rpath w₀) a) p - p‖ ≤ C := by
    intro p hp
    have hNB : (𝓝[H] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by rw [InteractingSLE.closure_H]; exact hp)
    have h2 : Tendsto (fun y => ‖fwdMapInv (Ito.rpath w₀) a y - y‖) (𝓝[H] p)
        (𝓝 ‖extendFrom H (fwdMapInv (Ito.rpath w₀) a) p - p‖) :=
      ((hB.tendsto hp).sub (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)).norm
    exact le_of_tendsto h2 (eventually_nhdsWithin_of_forall fun y hy => hC y hy)
  have hsub : Tendsto (fun t : ℝ≥0 => t - a) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b + a, fun t ht => le_tsub_of_add_le_right ht⟩
  refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right _ (-C) (ht₁.comp hsub))
  filter_upwards [eventually_gt_atTop a] with t ht
  have hj : LoewnerConcat.joinedTrace w₀ η₀ a η₁ t =
      extendFrom H (fwdMapInv (Ito.rpath w₀) a) (η₁ (t - a)) := by
    simp only [LoewnerConcat.joinedTrace, not_le.2 ht, ↓reduceIte]
  rw [hj]
  have h1 := hext _ (LoewnerConcat.trace_mem_Hbar_bdry h₁ h10 hη₁ (t - a))
  have h2 := norm_sub_norm_le (η₁ (t - a)) (extendFrom H (fwdMapInv (Ito.rpath w₀) a) (η₁ (t - a)))
  rw [norm_sub_rev (η₁ (t - a))] at h2
  show ‖η₁ (t - a)‖ + -C ≤ _
  linarith

/-! ### The joined driver past the switch -/

section Join

/-- The joined driver past the switch time `joinTime k`: the earlier pieces' value plus the stopped piece `k`. -/
theorem joinDrv_succ_of_ge (Δ : ℕ → ℝ≥0∞) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (hD0 : (D k).1 0 = 0) {x : ℝ}
    (hx : Swc.joinTime Δ D k ≤ x) :
    Swc.joinDrv Δ D (k + 1) x =
      Swc.joinDrv Δ D k (Swc.joinTime Δ D k) + stopDrv (Δ k) (D k) (x - Swc.joinTime Δ D k) := by
  simp only [Swc.joinDrv]
  split_ifs with h
  · have hx' : x = Swc.joinTime Δ D k := le_antisymm h hx
    rw [hx', sub_self]
    simp [stopDrv, retOf, hD0]
  · rfl

/-- A stopped piece is constant past its stop. -/
theorem stopDrv_of_ge {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} {x : ℝ} (hx : min t e.2 ≤ (x.toNNReal : ℝ≥0∞)) :
    stopDrv t e x = e.1 (min t e.2).toNNReal := by
  simp only [stopDrv, retOf, min_eq_right hx]

end Join

/-! ### The uncapped driver past the history -/

section Sample

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (i : ℕ)

/-- **A capped candidate past the history**: the history's value plus its piece stopped at `min (cap, ζ)`. -/
theorem schedW_eq_stop (a : ℕ) {ω : Ω} (hord : Sec5.Prop513Schedule.TimeOrdered 0 (historyProgram c r l))
    (hold : oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)))
    {s : ℝ≥0} (hTs : historyTime c r l ≤ s) (hs : s ≤ historyTime c r l + candidateCap c r a) :
    schedW c r l a s ω = Swc.joinDrv (GW2Tip.specDelta (schedSpec (rootPt r.1) (futureProgram c r l a)))
        (fun j => GW2Olm.futFam c r l a j ω) (GW2Olm.curIdx c r l) (historyTime c r l) +
      stopDrv (candidateCap c r a) (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω)
        ((s - historyTime c r l : ℝ≥0) : ℝ) := by
  set Δ := GW2Tip.specDelta (schedSpec (rootPt r.1) (futureProgram c r l a)) with hΔ
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => GW2Olm.futFam c r l a j ω with hD
  set n := GW2Olm.curIdx c r l with hn
  have hs' : GW2Schedule.AllSucc Δ D n := Gm.allSucc_future_of_oldSuccess c r l a ω hold
  have hlen : n ≤ (futureProgram c r l a).length := by
    simp only [hn, GW2Olm.curIdx, futureProgram, List.length_append, List.length_singleton]; omega
  have hJ : Swc.joinTime Δ D n = (historyTime c r l : ℝ) := by
    rw [Gm.joinTime_eq_schedTime (rootPt r.1) (timeOrdered_futureProgram c r l a hord) hlen hs',
      schedTime_curIdx]
  have hD0 : (D n).1 0 = 0 := (GW2Schedule.isRegularDriver_canonFam c.hκ c.h12p c.βA c.c₀ _ _ _ c.h n ω).2.1
  have hW : schedW c r l a s ω = Gm.futureJoined c r l a ω s := congrFun (schedW_of_oldSuccess c r l a hold) s
  rw [hW]
  rw [Gm.futureJoined_eq_joinDrv c r l a ω hord hold hgood hs]
  change Swc.joinDrv Δ D (n + 1) s = _
  rw [joinDrv_succ_of_ge Δ D n hD0 (by rw [hJ]; exact_mod_cast hTs), hJ, NNReal.coe_sub hTs,
    show Δ n = (candidateCap c r a : ℝ≥0∞) from futureProgram_delta c r l a]

end Sample

/-! ### Transience -/

section Trans

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (i : ℕ)

include h13 in
/-- The whole piece of the angle is regular at every history success (Theorem 1.3, `ζ = ⊤` clause included). -/
theorem ae_piece_regular : ∀ᵐ ω ∂c.P, oldSuccess c r l ω →
    GW1P.PieceRegular (GW2Olm.futFam c r l (angCand i 0) (GW2Olm.curIdx c r l) ω).1
      (GW2Olm.futFam c r l (angCand i 0) (GW2Olm.curIdx c r l) ω).2 := by
  set a₀ := angCand i 0
  set spec := GW2Olm.futSpec c r l a₀ with hspec
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec (GW2Olm.futFam c r l a₀) :=
    GW2Schedule.isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀ (GW2Tip.specAngle spec) (GW2Tip.specDelta spec)
      h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
      (GW2Tip.isFlowProg_spec (rootPt r.1) true (futureProgram c r l a₀)) (GW2Tip.specDelta_ne_top _)
  have hreg : ∀ k ω, Exist.Staged.IsRegularDriver (GW2Olm.futFam c r l a₀ k ω) := fun k ω =>
    GW2Schedule.isRegularDriver_canonFam c.hκ c.h12p c.βA c.c₀ _ _ _ c.h k ω
  filter_upwards [SB.Lk.ae_pieceRegular_full_of_regular h13 c.hκ c.hb hS hreg (GW2Olm.curIdx c r l)]
    with ω hω hold
  exact hω _ _ (RootK32.next_launch_of_oldSuccess c r l a₀ ω hold)

include h13 in
/-- **The uncapped joined driver is transient** (time-ordered histories). -/
theorem ae_uncTr_transient (hord : GW2Sdx.HistOrdered c r l) :
    ∀ᵐ ω ∂c.P, Tendsto (fun t => ‖uncTr c r l i ω t‖) atTop atTop := by
  have : Countable ℕ := inferInstance
  filter_upwards [ae_uncW_regular h13 c r l i, ae_angCand_facts h13 c r l i, Gm.ae_futureJoined_trace h13 c r,
    ae_piece_regular h13 c r l i] with ω hU hagr hJ hP
  obtain ⟨hag, _⟩ := hagr
  obtain ⟨hUc, hU0, hUη⟩ := hU
  set T := historyTime c r l with hT
  by_cases hold : oldSuccess c r l ω
  swap
  · refine GW2Rd.tendsto_norm_trace_of_frozen hUc hU0 one_pos (fun t _ => ?_) hUη
    simp only [uncW, schedW, hold, ↓reduceIte]
  have hgood : ∀ a, ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)) := fun a => (hJ l a hold).1
  have hlife : ∀ a, candidateAngle c r a = angleEnumeration c r i →
      (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω) = GW2Olm.futFam c r l (angCand i 0) (GW2Olm.curIdx c r l) ω :=
    fun a ha => futFam_eq_of_angle c r l (by rw [ha, candidateAngle_angCand]) ω
  have hglue : ∀ k (t : ℝ≥0), t ≤ T + (timeEnumeration c r k : ℝ≥0) →
      uncW c r l i t ω = schedW c r l (angCand i k) t ω := fun k t ht =>
    hag _ _ t (le_hist_capIdx c r l t) ht
  set piece := GW2Olm.futFam c r l (angCand i 0) (GW2Olm.curIdx c r l) ω with hpiece
  by_cases hfin : piece.2 = ⊤
  · -- the piece lives forever: the history followed by the whole piece
    obtain ⟨hp0, hpc, η₁, hη₁, htr₁⟩ := hP hold
    rw [hfin] at hpc hη₁
    have hp : Continuous piece.1 := continuousOn_univ.1 (hpc.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
    have hcat : (fun t => uncW c r l i t ω) =
        Sec7.StripSideHeightProb.catPath (fun t => uncW c r l i t ω) T piece.1 := by
      funext t
      by_cases ht : t ≤ T
      · rw [Sec7.StripSideHeightProb.catPath_of_le ht]
      · have hTt : T ≤ t := le_of_lt (not_le.1 ht)
        simp only [Sec7.StripSideHeightProb.catPath, ht, ↓reduceIte]
        set a := angCand i (capIdx c r t) with ha
        have hcap : t ≤ T + candidateCap c r a := by
          rw [candidateCap_angCand]; exact le_hist_capIdx c r l t
        have hang : candidateAngle c r a = angleEnumeration c r i := candidateAngle_angCand c r _ _
        have hσ : (((t - T : ℝ≥0)) : ℝ≥0∞) ≤ min (candidateCap c r a : ℝ≥0∞)
            (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 := by
          rw [hlife a hang, hfin, min_top_right]
          exact ENNReal.coe_le_coe.2 (tsub_le_iff_left.2 hcap)
        have hsh := shiftNN_schedW hord hold (hgood a) hσ
        rw [hlife a hang] at hsh
        simp only [Sec7.shiftNN] at hsh
        rw [← hT, add_tsub_cancel_of_le hTt] at hsh
        have hTu : uncW c r l i T ω = schedW c r l a T ω := hglue (capIdx c r t) T le_self_add
        change schedW c r l a t ω = _
        rw [hTu]
        linarith
    have hη₀ : IsGeneratingTrace (fun t => uncW c r l i t ω) T (uncTr c r l i ω) := hUη.mono_horizon le_top
    have hjt := LoewnerConcat.isGeneratingTrace_catPath_bdry hUc hU0 hp hp0 hη₀ hη₁
    rw [← hcat] at hjt
    have heq : ∀ t, uncTr c r l i ω t = LoewnerConcat.joinedTrace (fun t => uncW c r l i t ω)
        (uncTr c r l i ω) T η₁ t := fun t =>
      trace_eq_of_agree hUc hUc hU0 hU0 hUη hjt fun _ _ => rfl
    have := tendsto_joinedTrace_bdry hUc hU0 hη₀ hp hp0 hη₁ (htr₁ hfin)
    refine this.congr fun t => ?_
    rw [heq t]
  · -- the piece dies: frozen after `T + ζ`
    set ℓ := piece.2.toNNReal with hℓ
    have hfrz : ∀ t, T + ℓ ≤ t → uncW c r l i t ω = uncW c r l i (T + ℓ) ω := by
      intro t ht
      set a := angCand i (capIdx c r t) with ha
      have hang : candidateAngle c r a = angleEnumeration c r i := candidateAngle_angCand c r _ _
      have hcap : t ≤ T + candidateCap c r a := by
        rw [candidateCap_angCand]; exact le_hist_capIdx c r l t
      have hζ : (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 = (ℓ : ℝ≥0∞) := by
        rw [hlife a hang, hℓ, ENNReal.coe_toNNReal hfin]
      have hmin : min (candidateCap c r a : ℝ≥0∞) (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 =
          (ℓ : ℝ≥0∞) := by
        rw [hζ]
        exact min_eq_right (ENNReal.coe_le_coe.2 (le_of_add_le_add_left (ht.trans hcap)))
      have hTℓ : T ≤ T + ℓ := le_self_add
      have hst : ∀ s, T + ℓ ≤ s → s ≤ T + candidateCap c r a →
          schedW c r l a s ω = Swc.joinDrv (GW2Tip.specDelta (schedSpec (rootPt r.1) (futureProgram c r l a)))
            (fun j => GW2Olm.futFam c r l a j ω) (GW2Olm.curIdx c r l) T +
            (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 ℓ := by
        intro s hs1 hs2
        rw [schedW_eq_stop c r l a hord hold (hgood a) (hTℓ.trans hs1) hs2, stopDrv_of_ge, hmin,
          ENNReal.toNNReal_coe]
        rw [hmin, Real.toNNReal_coe]
        exact ENNReal.coe_le_coe.2 (le_tsub_of_add_le_left hs1)
      have hTu : uncW c r l i (T + ℓ) ω = schedW c r l a (T + ℓ) ω :=
        hglue (capIdx c r t) (T + ℓ) (ht.trans (le_hist_capIdx c r l t))
      change schedW c r l a t ω = _
      rw [hTu, hst t ht hcap, hst (T + ℓ) le_rfl (ht.trans hcap)]
    refine GW2Rd.tendsto_norm_trace_of_frozen hUc hU0 (S := T + ℓ + 1) (by positivity) (fun t ht => ?_) hUη
    rw [hfrz t ((le_self_add).trans ht), hfrz (T + ℓ + 1) le_self_add]

/-- **`UncRegStatement`** (from Theorem 1.3). -/
theorem uncRegStatement (h13 : Exist.Theorem13Statement.{u}) : UncRegStatement.{u} := by
  intro Ω _ _ c r l i hord
  filter_upwards [ae_uncW_regular h13 c r l i, ae_uncTr_transient h13 c r l i hord] with ω h1 h2
  exact ⟨h1.1, h1.2.1, h1.2.2, h2⟩

end Trans

end InteractingSLE.Theorem14.GW2Ni
