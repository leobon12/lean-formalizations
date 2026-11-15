/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmJ32Cross
import InteractingSLE.Spec.Supplement.GW2SdhRead

/-!
# The start range of J32's stage driver at every candidate (S4)

Packet PROVE-GW2-BUF (S4; rulings R110, R112). GEOM2's cross-program identity `Gm.ae_sourceDriver_cons_zero` gives
`Y_{(θ,q)::l, a}(0) = −X_{l, a₀}(q)` after a passed test `q` of `(l, a₀)` when the next sample `((θ,q)::l, a)` is
LIVE. The shell choice (SDE's `RootShellChoice32`) needs the start of EVERY candidate at alive histories. The next
sample's liveness enters GEOM2's proof only through a monotone continuous clock on `[0, q]`. That clock is the passed
test's own live clock, because the two joined drivers agree on `[0, q]`. So the identity holds for every candidate.

* **`ae_sourceDriver_cons_zero_all`**: a.s., after an alive `l` and a passed test `q` of `(l, a₀)`, for EVERY
  candidate `a` of `(θ, q) :: l`, `Y_{(θ,q)::l, a}(0) = −X_{l, a₀}(q)`;
* `rootStart32_eq_sourceDriver_zero`: SDE's `rootStart32` is the stage driver at `0`;
* **`ae_rootStart32_mem_of_alive`**: a.s., at every alive nonempty history, every candidate's start lies in
  `(−9/4, −7/4)` (the passed reading is in the band `(7/4, 9/4)`).
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bf

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 RootB23

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The cross-program identity for every next candidate.** -/
theorem ae_sourceDriver_cons_zero_all (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a₀ : ℕ) (q : c.Q) (a : ℕ),
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      ω ∈ (RootJ32.experiment c r).data.tests l a₀ q →
      RootJ32.sourceDriver c r ((RootJ31.candidateAngle c r a₀, q) :: l) a ω 0 =
        -RootJ32.sourceX c r l a₀ ω q := by
  filter_upwards [Gm.ae_live_clock h13 c r, Gm.ae_futureJoined_trace h13 c r]
    with ω hclock hjoin l a₀ q a halive htest
  set θ := RootJ31.candidateAngle c r a₀ with hθ
  set l' := (θ, q) :: l with hl'
  set x := rootPt r.1 with hx
  set k : ℝ≥0 := 2 ^ r.2 with hk
  have hk0 : 0 < k := pow_pos (by norm_num) _
  set v₀ := (rootEntry r.1).2 with hv₀
  -- the history `l` and its passed test
  obtain ⟨hTq₀, hqv₀, hlive₀, -⟩ := RootJ32.test_spec c r l a₀ q ω htest
  have hold₀ := RootJ32.oldSuccess_of_alive c r l ω halive
  have hord₀ := RootJ32.timeOrdered_historyProgram_of_alive c r l ω halive
  obtain ⟨γ₀, hγ₀, -, hm₀, hc₀, -, -⟩ := hclock l a₀ hlive₀
  obtain ⟨hgood₀, -⟩ := hjoin l a₀ hold₀
  -- the next history, any candidate
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
  -- record forms: the next candidate is read at horizon `q`
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
  -- the clock of the next candidate on `[0, q]` is the passed test's
  have hPP : ∀ t ≤ (q : ℝ≥0), RootH29.forwardCapacity x c.s t P' = RootH29.forwardCapacity x c.s t P₀ :=
    fun t ht => Gm.forwardCapacity_recOf_congr hJ hJ0 hJ₀ hJ₀0 ht (ht.trans hqw₀)
      fun y hy => hJJ y (hy.trans ht)
  have heq : EqOn (fun t => RootH29.forwardCapacity x c.s t (cfRec c.s c.W c.ζ ω,
      StagedEntrance.Strip.recOfDriver L' (Gm.futureJoined c r l' a ω)))
      (fun t => RootH29.forwardCapacity x c.s t (cfRec c.s c.W c.ζ ω,
        StagedEntrance.Strip.recOfDriver L₀ (Gm.futureJoined c r l a₀ ω))) (Icc 0 (q : ℝ≥0)) :=
    fun t ht => by
      dsimp only
      rw [hAP' t ht.2, hPP t ht.2, ← hAP₀ t (ht.2.trans hqw₀)]
  have hsub : Icc 0 (q : ℝ≥0) ⊆ Icc 0 w₀ := Icc_subset_Icc le_rfl hqw₀
  have hm' : MonotoneOn (fun t => RootH29.forwardCapacity x c.s t (cfRec c.s c.W c.ζ ω,
      StagedEntrance.Strip.recOfDriver L' (Gm.futureJoined c r l' a ω))) (Icc 0 (q : ℝ≥0)) :=
    fun t ht t' ht' htt' => by
      rw [heq ht, heq ht']
      exact hm₀.monotoneOn (hsub ht) (hsub ht') htt'
  have hc' : ContinuousOn (fun t => RootH29.forwardCapacity x c.s t (cfRec c.s c.W c.ζ ω,
      StagedEntrance.Strip.recOfDriver L' (Gm.futureJoined c r l' a ω))) (Icc 0 (q : ℝ≥0)) :=
    (hc₀.mono hsub).congr heq
  have hmP' : MonotoneOn (fun t => RootH29.forwardCapacity x c.s t P') (Icc 0 (q : ℝ≥0)) :=
    fun t ht t' ht' htt' => by
      show RootH29.forwardCapacity x c.s t P' ≤ RootH29.forwardCapacity x c.s t' P'
      rw [← hAP' t ht.2, ← hAP' t' ht'.2]; exact hm' ht ht' htt'
  have hmP₀ : MonotoneOn (fun t => RootH29.forwardCapacity x c.s t P₀) (Icc 0 w₀) :=
    fun t ht t' ht' htt' => by
      show RootH29.forwardCapacity x c.s t P₀ ≤ RootH29.forwardCapacity x c.s t' P₀
      rw [← hAP₀ t ht.2, ← hAP₀ t' ht'.2]; exact hm₀.monotoneOn ht ht' htt'
  -- the two capacities read at `q` and at the root time agree
  have hv₀q : v₀ ≤ (q : ℝ≥0) := (Gm.rootTime_le_historyTime c r l hord₀).trans hTq₀.le
  have hcapq : RootH29.forwardCapacity x c.s q P' = RootH29.forwardCapacity x c.s q P₀ := hPP q le_rfl
  have hvq' : RootH29.forwardCapacity x c.s v₀ P' ≤ RootH29.forwardCapacity x c.s q P' :=
    hmP' ⟨zero_le, hv₀q⟩ ⟨zero_le, le_rfl⟩ hv₀q
  -- the driver readers
  have hD : ∀ c' : ℝ≥0, (c' : ℝ) ≤ RootH29.forwardCapacity x c.s q P' →
      RootJ32.capacityDriverRead x c.s L' c' (RootJ31.futurePair c r l' a ω) =
        RootJ32.capacityDriverRead x c.s L₀ c' (RootJ31.futurePair c r l a₀ ω) := by
    intro c' hc''
    have hc'q : (c' : ℝ) ≤ RootH29.forwardCapacity x c.s q (cfRec c.s c.W c.ζ ω,
        StagedEntrance.Strip.recOfDriver L' (Gm.futureJoined c r l' a ω)) := by
      rw [hAP' q le_rfl]; exact hc''
    have hc'w₀ : (c' : ℝ) ≤ RootH29.forwardCapacity x c.s w₀ (cfRec c.s c.W c.ζ ω,
        StagedEntrance.Strip.recOfDriver L₀ (Gm.futureJoined c r l a₀ ω)) := by
      rw [hAP₀ w₀ le_rfl]
      exact (hc''.trans hcapq.le).trans (hmP₀ ⟨zero_le, hqw₀⟩ ⟨zero_le, le_rfl⟩ hqw₀)
    rw [hpe', hpe₀, RootJ32.capacityDriverRead_eq_of_clock hJ hJ0 hγ hqL' hqL' hm' hc' hc'q,
      RootJ32.capacityDriverRead_eq_of_clock hJ₀ hJ₀0 hγ₀ hw₀L hw₀L hm₀.monotoneOn hc₀ hc'w₀]
    exact Gm.capacityDriverRead_I30_congr hJ hJ0 hJ₀ hJ₀0 hγ hγ₀ le_rfl hqw₀ hJJ hmP' hmP₀ hc''
  -- assemble
  have hY : RootJ32.sourceDriver c r l' a ω 0 = ((-1) ^ l'.length) * (k : ℝ) *
      (RootJ32.capacityDriverRead x c.s L' (RootH29.forwardCapacity x c.s
          (RootJ31.historyTime c r l') (RootJ31.futurePair c r l' a ω)).toNNReal
          (RootJ31.futurePair c r l' a ω) -
        RootJ32.capacityDriverRead x c.s L' (RootH29.forwardCapacity x c.s v₀
          (RootJ31.futurePair c r l' a ω)).toNNReal (RootJ31.futurePair c r l' a ω)) := by
    change ((-1) ^ l'.length) * (k : ℝ) * (RootJ32.capacityDriverRead x c.s L'
      ((RootH29.forwardCapacity x c.s (RootJ31.historyTime c r l')
        (RootJ31.futurePair c r l' a ω)).toNNReal + 0 / k ^ 2) (RootJ31.futurePair c r l' a ω) - _) = _
    rw [zero_div, add_zero]
  have hAT : RootH29.forwardCapacity x c.s (RootJ31.historyTime c r l')
      (RootJ31.futurePair c r l' a ω) = RootH29.forwardCapacity x c.s q
        (RootJ31.futurePair c r l' a ω) :=
    congrArg (fun t => RootH29.forwardCapacity x c.s t (RootJ31.futurePair c r l' a ω)) hT'
  have hAq' : RootH29.forwardCapacity x c.s q (RootJ31.futurePair c r l' a ω) =
      RootH29.forwardCapacity x c.s q (RootJ31.futurePair c r l a₀ ω) := by
    rw [hpe', hpe₀, hAP' q le_rfl, hAP₀ q hqw₀, hcapq]
  have hAv' : RootH29.forwardCapacity x c.s v₀ (RootJ31.futurePair c r l' a ω) =
      RootH29.forwardCapacity x c.s v₀ (RootJ31.futurePair c r l a₀ ω) := by
    rw [hpe', hpe₀, hAP' v₀ hv₀q, hAP₀ v₀ (hv₀q.trans hqw₀), hPP v₀ hv₀q]
  have hle_q : (((RootH29.forwardCapacity x c.s q (RootJ31.futurePair c r l' a ω)).toNNReal : ℝ≥0) :
      ℝ) ≤ RootH29.forwardCapacity x c.s q P' := by
    rw [Real.coe_toNNReal _ (RootJ32.forwardCapacity_nonneg _ _ _ _), hpe', hAP' q le_rfl]
  have hle_v : (((RootH29.forwardCapacity x c.s v₀ (RootJ31.futurePair c r l' a ω)).toNNReal : ℝ≥0) :
      ℝ) ≤ RootH29.forwardCapacity x c.s q P' := by
    rw [Real.coe_toNNReal _ (RootJ32.forwardCapacity_nonneg _ _ _ _), hpe', hAP' v₀ hv₀q]
    exact hvq'
  -- the reading at `q` of the previous history
  have hAT0 : 0 ≤ RootH29.forwardCapacity x c.s (RootJ31.historyTime c r l)
      (RootJ31.futurePair c r l a₀ ω) := RootJ32.forwardCapacity_nonneg _ _ _ _
  have hATq : RootH29.forwardCapacity x c.s (RootJ31.historyTime c r l)
      (RootJ31.futurePair c r l a₀ ω) ≤ RootH29.forwardCapacity x c.s q
        (RootJ31.futurePair c r l a₀ ω) := by
    rw [hpe₀]
    exact hm₀.monotoneOn ⟨zero_le, hTq₀.le.trans hqw₀⟩ ⟨zero_le, hqw₀⟩ hTq₀.le
  have hcapX : (RootH29.forwardCapacity x c.s (RootJ31.historyTime c r l)
      (RootJ31.futurePair c r l a₀ ω)).toNNReal + RootJ31.sourceClock c r l a₀ q ω / k ^ 2 =
      (RootH29.forwardCapacity x c.s q (RootJ31.futurePair c r l a₀ ω)).toNNReal := by
    change _ + RootJ31.capacityIncrement k x c.s (RootJ31.historyTime c r l)
      ((q : ℝ≥0) - RootJ31.historyTime c r l) (RootJ31.futurePair c r l a₀ ω) / k ^ 2 = _
    rw [RootJ31.capacityIncrement, add_tsub_cancel_of_le hTq₀.le,
      mul_div_cancel_left₀ _ (pow_ne_zero 2 hk0.ne'), ← Real.toNNReal_add hAT0
      (sub_nonneg.2 hATq), add_sub_cancel]
  have hX : RootJ32.sourceX c r l a₀ ω q = ((-1) ^ l.length) * (k : ℝ) *
      (RootJ32.capacityDriverRead x c.s L₀ (RootH29.forwardCapacity x c.s q
          (RootJ31.futurePair c r l a₀ ω)).toNNReal (RootJ31.futurePair c r l a₀ ω) -
        RootJ32.capacityDriverRead x c.s L₀ (RootH29.forwardCapacity x c.s v₀
          (RootJ31.futurePair c r l a₀ ω)).toNNReal (RootJ31.futurePair c r l a₀ ω)) := by
    change ((-1) ^ l.length) * (k : ℝ) * (RootJ32.capacityDriverRead x c.s L₀
      ((RootH29.forwardCapacity x c.s (RootJ31.historyTime c r l)
        (RootJ31.futurePair c r l a₀ ω)).toNNReal +
          RootJ31.sourceClock c r l a₀ (((q : ℝ≥0) : ℝ)).toNNReal ω / k ^ 2)
        (RootJ31.futurePair c r l a₀ ω) - _) = _
    rw [Real.toNNReal_coe, hcapX]
  rw [hY, hAT, hD _ hle_q, hD _ hle_v, hAq', hAv', hX, hl', List.length_cons, pow_succ]
  ring

end InteractingSLE.Theorem14.GW2Bf
