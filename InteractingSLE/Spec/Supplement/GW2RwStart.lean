/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BfJ32Shell

/-!
# The slow shell's start: the history start functional at alive histories

PROVE-GW2-ROOTX round 5. The `shell` field of `VPairInputsXCS` starts the shell at the retained functional
`GW2Bf.histStart` and asks the start clause of `startsU`, `histStart ∈ (−9/4, −7/4)`, on alive histories. BUF's
`ae_rootStart32_mem_of_alive` gives it for J32's start `rootStart32 = j32Start` of every candidate; BUF's
`ae_j32Start_eq_histStart` identifies `j32Start` with `histStart` only at a LIVE sample of the candidate. At the
conditioning sample the next candidates' clock on `[0, q]` is the passed test's own live clock (the joined drivers
agree there, BUF's `ae_sourceDriver_cons_zero_all` argument), which is all the identification uses.

* **`ae_histStart_cons_eq`**: after an alive `l` and a passed test `q` of `(l, a₀)`,
  `histStart ((θ_{a₀}, q) :: l) = −X_{l, a₀}(q)`;
* **`ae_histStart_mem_of_alive`**: at every alive nonempty history, `histStart ∈ (−9/4, −7/4)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rw

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 RootB23

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The history start after a passed test is minus the passed reading**: almost surely, after an alive `l` and a
passed test `q` of `(l, a₀)`, the retained start functional of `(θ_{a₀}, q) :: l` is `−X_{l, a₀}(q)`. The next
candidates' clock on `[0, q]` is the passed test's own live clock (the joined drivers agree there). -/
theorem ae_histStart_cons_eq (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a₀ : ℕ) (q : c.Q),
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      ω ∈ (RootJ32.experiment c r).data.tests l a₀ q →
      GW2Bf.histStart c r ((RootJ31.candidateAngle c r a₀, q) :: l) ω = -RootJ32.sourceX c r l a₀ ω q := by
  filter_upwards [Gm.ae_live_clock h13 c r, Gm.ae_futureJoined_trace h13 c r,
    GW2Bf.ae_sourceDriver_cons_zero_all h13 c r] with ω hclock hjoin hcross l a₀ q halive htest
  set a : ℕ := 0 with ha
  set θ := RootJ31.candidateAngle c r a₀ with hθ
  set l' := (θ, q) :: l with hl'
  set x := rootPt r.1 with hx
  -- the history `l` and its passed test
  obtain ⟨hTq₀, hqv₀, hlive₀, -⟩ := RootJ32.test_spec c r l a₀ q ω htest
  have hold₀ := RootJ32.oldSuccess_of_alive c r l ω halive
  have hord₀ := RootJ32.timeOrdered_historyProgram_of_alive c r l ω halive
  obtain ⟨γ₀, hγ₀, -, hm₀, hc₀, -, -⟩ := hclock l a₀ hlive₀
  obtain ⟨hgood₀, -⟩ := hjoin l a₀ hold₀
  -- the next history
  have halive' : ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l' :=
    TestEvents.aliveTests_inter_subset l a₀ q ⟨halive, htest⟩
  have hold' := RootJ32.oldSuccess_of_alive c r l' ω halive'
  have hord' := RootJ32.timeOrdered_historyProgram_of_alive c r l' ω halive'
  obtain ⟨hgood', γ, hγ⟩ := hjoin l' a hold'
  have hT' : RootJ31.historyTime c r l' = q := Gm.historyTime_cons c r l θ q
  obtain ⟨hJ, hJ0⟩ := Gm.continuous_futureJoined c r l' a ω
  obtain ⟨hJ₀, hJ₀0⟩ := Gm.continuous_futureJoined c r l a₀ ω
  -- the two joined drivers agree on `[0, q]`
  have hqcap₀ : (q : ℝ≥0) ≤ RootJ31.historyTime c r l + RootJ31.candidateCap c r a₀ :=
    hqv₀.le.trans (add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a₀ ω))
  have hJJ : ∀ t ≤ (q : ℝ≥0), Gm.futureJoined c r l' a ω t = Gm.futureJoined c r l a₀ ω t := by
    intro t ht
    have h1 := Gm.futureJoined_eq_joinDrv_hist c r l' a ω hord' hold' hgood' t (by rw [hT']; exact ht)
    have h2 := Gm.futureJoined_eq_joinDrv_query c r l a₀ ω hord₀ hold₀ hgood₀ hTq₀ hqcap₀
      (RootJ32.next_piece_live_of_test c r l a₀ q ω htest) t ht
    rw [h1, h2, hl', RootJ31.historyProgram_cons, List.length_append, List.length_singleton]
  set L' := RootJ31.historyTime c r l' + RootJ31.candidateCap c r a with hL'
  set L₀ := RootJ31.historyTime c r l + RootJ31.candidateCap c r a₀ with hL₀
  set w₀ := RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a₀ ω with hw₀
  have hqL' : (q : ℝ≥0) ≤ L' := by rw [hL', hT']; exact le_self_add
  have hw₀L : w₀ ≤ L₀ := add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a₀ ω)
  have hqw₀ : (q : ℝ≥0) ≤ w₀ := hqv₀.le
  have hpe' := Gm.futurePair_eq_recOfDriver c r l' a ω
  have hpe₀ := Gm.futurePair_eq_recOfDriver c r l a₀ ω
  rw [hpe₀] at hm₀ hc₀
  set P' := (cfRec c.s c.W c.ζ ω, recOf ((q : ℝ≥0) : ℝ≥0∞) (Gm.futureJoined c r l' a ω, ⊤)) with hP'
  set P₀ := (cfRec c.s c.W c.ζ ω, recOf (w₀ : ℝ≥0∞) (Gm.futureJoined c r l a₀ ω, ⊤)) with hP₀
  have hAP' : ∀ t ≤ (q : ℝ≥0), RootH29.forwardCapacity x c.s t (cfRec c.s c.W c.ζ ω,
      StagedEntrance.Strip.recOfDriver L' (Gm.futureJoined c r l' a ω)) =
        RootH29.forwardCapacity x c.s t P' := fun t ht => by
    rw [Gm.recOfDriver_eq_recOf]
    exact Gm.forwardCapacity_recOf_congr hJ hJ0 hJ hJ0 (ht.trans hqL') ht fun _ _ => rfl
  have hAP₀ : ∀ t ≤ w₀, RootH29.forwardCapacity x c.s t (cfRec c.s c.W c.ζ ω,
      StagedEntrance.Strip.recOfDriver L₀ (Gm.futureJoined c r l a₀ ω)) =
        RootH29.forwardCapacity x c.s t P₀ := fun t ht => by
    rw [Gm.recOfDriver_eq_recOf]
    exact Gm.forwardCapacity_recOf_congr hJ₀ hJ₀0 hJ₀ hJ₀0 (ht.trans hw₀L) ht fun _ _ => rfl
  have hPP : ∀ t ≤ (q : ℝ≥0), RootH29.forwardCapacity x c.s t P' = RootH29.forwardCapacity x c.s t P₀ :=
    fun t ht => Gm.forwardCapacity_recOf_congr hJ hJ0 hJ₀ hJ₀0 ht (ht.trans hqw₀)
      fun y hy => hJJ y (hy.trans ht)
  have heq : EqOn (fun t => RootH29.forwardCapacity x c.s t (RootJ31.futurePair c r l' a ω))
      (fun t => RootH29.forwardCapacity x c.s t (cfRec c.s c.W c.ζ ω,
        StagedEntrance.Strip.recOfDriver L₀ (Gm.futureJoined c r l a₀ ω))) (Icc 0 (q : ℝ≥0)) :=
    fun t ht => by
      dsimp only
      rw [hpe', hAP' t ht.2, hPP t ht.2, ← hAP₀ t (ht.2.trans hqw₀)]
  have hsub : Icc 0 (q : ℝ≥0) ⊆ Icc 0 w₀ := Icc_subset_Icc le_rfl hqw₀
  -- the live clock of the next candidate on `[0, T']`
  have hm : MonotoneOn (fun t => RootH29.forwardCapacity x c.s t (RootJ31.futurePair c r l' a ω))
      (Icc 0 (RootJ31.historyTime c r l')) := by
    rw [hT']
    intro t ht t' ht' htt'
    rw [heq ht, heq ht']
    exact hm₀.monotoneOn (hsub ht) (hsub ht') htt'
  have hc : ContinuousOn (fun t => RootH29.forwardCapacity x c.s t (RootJ31.futurePair c r l' a ω))
      (Icc 0 (RootJ31.historyTime c r l')) := by
    rw [hT']
    exact (hc₀.mono hsub).congr heq
  -- J32's start of the next candidate is the history functional
  have hv₀ := GW2Bf.v0_le_historyTime c r l' hord'
  have hT : ((GW2Sdg.rootHistCap c r l' a ω : ℝ≥0) : ℝ) ≤
      RootH29.forwardCapacity x c.s (RootJ31.historyTime c r l') (RootJ31.futurePair c r l' a ω) :=
    le_of_eq (Real.coe_toNNReal _ (RootJ32.forwardCapacity_nonneg _ _ _ _))
  have h0 : (((GW2Sdg.rootCapAt c r l' a (rootEntry r.1).2 ω).toNNReal : ℝ≥0) : ℝ) ≤
      RootH29.forwardCapacity x c.s (RootJ31.historyTime c r l') (RootJ31.futurePair c r l' a ω) := by
    unfold GW2Sdg.rootCapAt
    rw [Real.coe_toNNReal _ (RootJ32.forwardCapacity_nonneg _ _ _ _)]
    exact hm ⟨zero_le, hv₀⟩ ⟨zero_le, le_rfl⟩ hv₀
  have eT : GW2Sdg.rootHistCap c r l' a ω = GW2Bf.histCap c r l' (RootJ31.historyTime c r l') ω := by
    unfold GW2Sdg.rootHistCap GW2Sdg.rootCapAt GW2Bf.histCap
    rw [GW2Bf.forwardCapacity_future_eq_hist c r l' a ω le_rfl]
  have e0 : (GW2Sdg.rootCapAt c r l' a (rootEntry r.1).2 ω).toNNReal =
      GW2Bf.histCap c r l' (rootEntry r.1).2 ω := by
    unfold GW2Sdg.rootCapAt GW2Bf.histCap
    rw [GW2Bf.forwardCapacity_future_eq_hist c r l' a ω hv₀]
  have hstart : GW2Bf.j32Start c r l' a ω = GW2Bf.histStart c r l' ω := by
    unfold GW2Bf.j32Start GW2Bf.histStart
    rw [GW2Bf.j32Read_eq_hist_of_live c r l' a ω hγ hm hc hT, GW2Bf.j32Read_eq_hist_of_live c r l' a ω hγ hm hc h0,
      eT, e0]
  rw [← hstart, ← GW2Bf.rootStart32_eq_j32Start, GW2Bf.rootStart32_eq_sourceDriver_zero]
  exact hcross l a₀ q a halive htest

/-- **At every alive nonempty history the retained start functional lies in `(−9/4, −7/4)`**: the start clause of
`startsU` for a shell started at `GW2Bf.histStart`. -/
theorem ae_histStart_mem_of_alive (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (x : EntryIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) (x :: l) →
      GW2Bf.histStart c r (x :: l) ω ∈ Ioo (-(9 / 4)) (-(7 / 4)) := by
  filter_upwards [ae_histStart_cons_eq h13 c r] with ω hcons x l halive
  obtain ⟨hl, hx⟩ := halive
  obtain ⟨a₀, ha₀⟩ := mem_iUnion.1 hx
  obtain ⟨hang, htest⟩ := mem_iUnion.1 ha₀
  have hxe : x = (RootJ31.candidateAngle c r a₀, x.2) := Prod.ext hang.symm rfl
  have hband : RootJ32.sourceX c r l a₀ ω (x.2 : ℝ≥0) ∈ Ioo (7 / 4) (9 / 4) := htest.2.2.2
  rw [hxe, hcons l a₀ x.2 hl htest]
  exact ⟨by linarith [hband.2], by linarith [hband.1]⟩

end InteractingSLE.Theorem14.GW2Rw
