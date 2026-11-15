/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmTip
import InteractingSLE.Spec.Supplement.GW2GmCap

/-!
# Clause (a) of `clock_spec` for J31 when the cap window is before contact

Packet PROVE-GW2-GEOM2. J31's stage driver `RootJ31.sourceDriver` reads the capacity tip through
`RootI30.clockInverse` with the horizon `T + cap` (history time plus the candidate's cap), while the
physical buffer `T + F ≤ T + cap` is only a separation gauge stop: contact with the counterflow may occur in
`(T + F, T + cap]`. After contact the relative hull can become unbounded, `hcapHit = ⊤`, and the capacity
reader `forwardCapacity` returns `0` there; the inverse clock then reads the tip at such a time.

This file proves clause (a) on the event that the whole cap window is before contact, with the R5 core
(`GW2GmTip.continuousAt_capacityDriverRead`):

* **`continuousAt_sourceDriver_of_lt_contact`**: almost surely, at every passed test `q`, if
  `T + cap` is strictly before the reconstructed contact, then `sourceDriver` is continuous at the clock.

The hypothesis is the exact remaining proposition for clause (a); it is not claimed for J31 in general.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart RootC24 Supp8.GB6

/-- **Clause (a) for a joined trace whose whole cap window is before contact** (deterministic). -/
theorem continuousAt_stageDriverRead_of_lt_contact {Ω' : Type*} (W : ℝ≥0 → Ω' → ℝ)
    (ζ : Ω' → ℝ≥0∞) (ω : Ω') {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
    (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤) {s : ℝ≥0} (hs : 0 < s)
    {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1) {J : ℝ≥0 → ℝ}
    (hJ : Continuous J) (hJ0 : J 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace J ⊤ γ)
    {T q L : ℝ≥0} (hTq : T < q) (hqL : q < L)
    (hcon : (L : ℝ≥0∞) < RootK32.translatedContact x s L
      (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J))
    {k : ℝ≥0} (hk : 0 < k) (ε : ℝ) (v₀ : ℝ≥0) :
    ContinuousAt (fun u => RootJ31.stageDriverRead k ε x s L v₀ T u
        (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J))
      (RootJ31.capacityIncrement k x s T (q - T)
        (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)) := by
  have hrec : StagedEntrance.Strip.recOfDriver L J = recOf (L : ℝ≥0∞) (J, ⊤) :=
    recOfDriver_eq_recOf L J
  obtain ⟨h0, hm, -, -⟩ := clock_of_joined_trace W ζ ω hα hW hW0 hζ hs hx harc hJ hJ0 hγ le_rfl hcon
  rw [hrec] at h0 hm hcon ⊢
  have hTmem : T ∈ Icc 0 L := ⟨zero_le, hTq.le.trans hqL.le⟩
  have hqmem : q ∈ Icc 0 L := ⟨zero_le, hqL.le⟩
  have hLmem : L ∈ Icc 0 L := ⟨zero_le, le_rfl⟩
  have hAT0 : 0 ≤ RootH29.forwardCapacity x s T (cfRec s W ζ ω, recOf (L : ℝ≥0∞) (J, ⊤)) := by
    rw [← h0]; exact hm.monotoneOn ⟨le_rfl, zero_le⟩ hTmem zero_le
  have hATq := hm.monotoneOn hTmem hqmem hTq.le
  have hAqL := hm hqmem hLmem hqL
  have hnc := (lt_translatedContact_iff W ζ ω hα hW hW0 hζ x s hJ hJ0 hγ le_rfl).1
    (by rwa [← hrec] at hcon)
  have hγc : Continuous γ := continuousOn_univ.1 (hγ.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hαc : Continuous α := continuousOn_univ.1 (hα.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hv : (L : ℝ≥0∞) < min (firstContactTime
      (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) (J, (⊤ : ℝ≥0∞)).2 := by
    change _ < min _ ⊤
    rw [min_top_right]
    exact (lt_firstContactTime_iff_noncontact (continuous_const.add hγc) hαc L s).2 hnc
  have hcont := continuousAt_capacityDriverRead W ζ ω hα hW hW0 hζ hs hx harc
    (isRegularDriver_top hJ hJ0) hγ hv
    (u := (RootH29.forwardCapacity x s q (cfRec s W ζ ω, recOf (L : ℝ≥0∞) (J, ⊤))).toNNReal)
    (by rw [Real.coe_toNNReal _ (hAT0.trans hATq)]; exact hAqL)
  have hcap : (RootH29.forwardCapacity x s T (cfRec s W ζ ω, recOf (L : ℝ≥0∞) (J, ⊤))).toNNReal +
      RootJ31.capacityIncrement k x s T (q - T) (cfRec s W ζ ω, recOf (L : ℝ≥0∞) (J, ⊤)) / k ^ 2 =
      (RootH29.forwardCapacity x s q (cfRec s W ζ ω, recOf (L : ℝ≥0∞) (J, ⊤))).toNNReal := by
    rw [RootJ31.capacityIncrement, add_tsub_cancel_of_le hTq.le,
      mul_div_cancel_left₀ _ (pow_ne_zero 2 hk.ne'), ← Real.toNNReal_add hAT0
      (sub_nonneg.2 hATq), add_sub_cancel]
  rw [← hcap] at hcont
  have hin : ContinuousAt (fun u : ℝ≥0 =>
      (RootH29.forwardCapacity x s T (cfRec s W ζ ω, recOf (L : ℝ≥0∞) (J, ⊤))).toNNReal + u / k ^ 2)
      (RootJ31.capacityIncrement k x s T (q - T) (cfRec s W ζ ω, recOf (L : ℝ≥0∞) (J, ⊤))) :=
    (continuous_const.add (continuous_id.div_const _)).continuousAt
  exact continuousAt_const.mul ((ContinuousAt.comp (f := fun u : ℝ≥0 =>
    (RootH29.forwardCapacity x s T (cfRec s W ζ ω, recOf (L : ℝ≥0∞) (J, ⊤))).toNNReal + u / k ^ 2)
      hcont hin).sub continuousAt_const)

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- The future record pair is the counterflow record and the joined record at `T + cap`. -/
theorem futurePair_eq_recOfDriver (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    RootJ31.futurePair c r l a ω = (cfRec c.s c.W c.ζ ω, StagedEntrance.Strip.recOfDriver
      (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) (futureJoined c r l a ω)) := by
  rw [← lastTime_futureProgram]
  rfl

/-- **Clause (a) of `clock_spec`, on the event that the cap window is before contact.** -/
theorem continuousAt_sourceDriver_of_lt_contact (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ω ∂c.P, ∀ q : c.Q, ω ∈ (RootJ31.experiment c r).data.tests l a q →
      ((RootJ31.historyTime c r l + RootJ31.candidateCap c r a : ℝ≥0) : ℝ≥0∞) <
        RootK32.translatedContact (rootPt r.1) c.s
          (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) (RootJ31.futurePair c r l a ω) →
      ContinuousAt (RootJ31.sourceDriver c r l a ω) (RootJ31.sourceClock c r l a q ω) := by
  filter_upwards [ae_futureJoined_trace h13 c r, RootCv.ae_coverEvent_spec h13 c r, c.hα,
    GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ]
    with ω hjoin hcover hα hreg hζ q htest hcon
  have hSF : RootJ31.sourceEntry c r l a ω < RootJ31.sourceFailure c r l a ω :=
    htest.1.trans htest.2.1
  have hlive : 0 < (RootJ31.sourceSample c r l a ω).1 :=
    lt_of_le_of_lt bot_le (RootJ31.entry_lt_failure_imp_reach c r l a ω hSF)
  obtain ⟨hcov, hold, -, -⟩ := RootK32.sourceSample_live_geometry c r l a ω hlive
  obtain ⟨hseed, hsH, -, -, -, harc⟩ := hcover hcov
  obtain ⟨_, _, hWc, hW0, _⟩ := hreg
  have hs : 0 < c.s := by
    by_contra hn
    have hs0 : c.s = 0 := le_antisymm (not_lt.mp hn) zero_le
    exact ne_zero_of_mem_H hsH (by rw [hs0]; exact hα.1)
  obtain ⟨-, γ, hγ⟩ := hjoin l a hold
  obtain ⟨hJ, hJ0⟩ := continuous_futureJoined c r l a ω
  have hTq : RootJ31.historyTime c r l < (q : ℝ≥0) :=
    NNReal.coe_lt_coe.mp ((RootJ31.sourceEntry_ge_historyTime c r l a ω).trans_lt htest.1)
  have hqL : (q : ℝ≥0) < RootJ31.historyTime c r l + RootJ31.candidateCap c r a := by
    have h := htest.2.1
    change ((q : ℝ≥0) : ℝ) <
      ((RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω : ℝ≥0) : ℝ) at h
    exact (NNReal.coe_lt_coe.1 h).trans_le (add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a ω))
  rw [futurePair_eq_recOfDriver] at hcon
  have key := continuousAt_stageDriverRead_of_lt_contact c.W c.ζ ω hα hWc hW0 hζ hs
    (RootH29.rootPt_nonneg_of_seedOK c hseed) harc hJ hJ0 hγ hTq hqL hcon
    (k := 2 ^ r.2) (pow_pos (by norm_num) _) ((-1) ^ l.length) (rootEntry r.1).2
  have hD : RootJ31.sourceDriver c r l a ω = fun u => RootJ31.stageDriverRead (2 ^ r.2)
      ((-1) ^ l.length) (rootPt r.1) c.s (RootJ31.historyTime c r l + RootJ31.candidateCap c r a)
      (rootEntry r.1).2 (RootJ31.historyTime c r l) u
      (cfRec c.s c.W c.ζ ω, StagedEntrance.Strip.recOfDriver
        (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) (futureJoined c r l a ω)) := by
    funext u
    rw [← futurePair_eq_recOfDriver]
    rfl
  have hC : RootJ31.sourceClock c r l a q ω = RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s
      (RootJ31.historyTime c r l) ((q : ℝ≥0) - RootJ31.historyTime c r l)
      (cfRec c.s c.W c.ζ ω, StagedEntrance.Strip.recOfDriver
        (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) (futureJoined c r l a ω)) := by
    rw [← futurePair_eq_recOfDriver]
    rfl
  rw [hD, hC]
  exact key

end InteractingSLE.Theorem14.GW2TipSystem.Gm
