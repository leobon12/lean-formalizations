/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmQTrace
import InteractingSLE.Spec.Supplement.GW2GmJ32Reg

/-!
# J32's clock from a positive buffer, and the entry criterion (tools for the observation gate)

Packet PROVE-GW2-GEOM2 (round 5).

* **`ae_clock_of_buffer_pos`**: almost surely, whenever the buffer is positive, the capacity reader of the future
  pair is a strict continuous clock from `0` on `[0, T + F]` (as `ae_live_clock`, but from `0 < F` instead of a live
  sample);
* **`switchedEntry_lt_iff`** (deterministic): on such a clock, J32's entry precedes `τ < F` exactly when the stage
  driver exceeds `2` at some rational capacity below `capInc(τ)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 Supp8.GB6 Supp8.GB6.CoordB
  Sec5.Prop513Schedule

/-- **The entry criterion.** On a strict continuous capacity clock on `[0, T + F]`, J32's entry (`switchedEntry`)
precedes `τ < F` exactly when the stage driver exceeds `2` at a rational capacity below `capInc(τ)`. -/
theorem switchedEntry_lt_iff {k : ℝ≥0} (hk : 0 < k) (ε x : ℝ) (s L v₀ : ℝ≥0) {T Fb : ℝ≥0}
    {p : RecData × RecData}
    (hm : StrictMonoOn (fun t => RootH29.forwardCapacity x s t p) (Icc 0 (T + Fb)))
    (hc : ContinuousOn (fun t => RootH29.forwardCapacity x s t p) (Icc 0 (T + Fb)))
    {τ : ℝ≥0} (hτ : τ < Fb) :
    RootJ32.switchedEntry k ε x s L v₀ T Fb p < τ ↔
      ∃ u : ℚ≥0, ((u : ℝ≥0)) < RootJ31.capacityIncrement k x s T τ p ∧
        2 < RootJ32.stageDriverRead k ε x s L v₀ T u p := by
  classical
  set A := fun t => RootH29.forwardCapacity x s t p with hAdef
  set inc : ℝ≥0 → ℝ := fun t => (RootJ31.capacityIncrement k x s T t p : ℝ) with hincdef
  have hinc : ∀ t ≤ Fb, inc t = (k : ℝ) ^ 2 * (A (T + t) - A T) := by
    intro t ht
    have hle : A T ≤ A (T + t) :=
      hm.monotoneOn ⟨zero_le, le_self_add⟩ ⟨zero_le, add_le_add le_rfl ht⟩ le_self_add
    have hle' : RootH29.forwardCapacity x s T p ≤ RootH29.forwardCapacity x s (T + t) p := hle
    simp only [hincdef, RootJ31.capacityIncrement, NNReal.coe_mul, NNReal.coe_pow,
      Real.coe_toNNReal _ (sub_nonneg.2 hle')]
    rfl
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (Fb : ℝ≥0∞)} = Icc 0 Fb := by
    ext t; simp only [mem_ofPred_eq, ENNReal.coe_le_coe, mem_Icc, zero_le, true_and]
  have hsm : StrictMonoOn inc (Icc 0 Fb) := by
    intro t ht t' ht' htt'
    rw [hinc t ht.2, hinc t' ht'.2]
    have := hm ⟨zero_le, add_le_add le_rfl ht.2⟩ ⟨zero_le, add_le_add le_rfl ht'.2⟩
      ((add_lt_add_iff_left T).2 htt')
    have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    nlinarith
  have hclockon : IsClockOn inc (Fb : ℝ≥0∞) := by
    refine ⟨?_, ?_, ?_, fun h => (ENNReal.coe_ne_top h).elim⟩
    · simp only [hincdef, RootJ31.capacityIncrement_zero, NNReal.coe_zero]
    · rw [hset]; exact hsm
    · rw [hset]
      have hmaps : MapsTo (fun t : ℝ≥0 => T + t) (Icc 0 Fb) (Icc 0 (T + Fb)) :=
        fun t ht => ⟨zero_le, add_le_add le_rfl ht.2⟩
      have h1 : ContinuousOn (fun t : ℝ≥0 => A (T + t)) (Icc 0 Fb) :=
        hc.comp (continuous_const.add continuous_id).continuousOn hmaps
      have h2 : ContinuousOn (fun t : ℝ≥0 => (k : ℝ) ^ 2 * (A (T + t) - A T)) (Icc 0 Fb) :=
        continuousOn_const.mul (h1.sub continuousOn_const)
      exact h2.congr fun t ht => hinc t ht.2
  have hτmem : τ ∈ Icc 0 Fb := ⟨zero_le, hτ.le⟩
  have hFmem : Fb ∈ Icc 0 Fb := ⟨zero_le, le_rfl⟩
  have hτF : inc τ < inc Fb := hsm hτmem hFmem hτ
  set z := RootJ32.switchedSample k ε x s L v₀ T Fb p with hz
  have hz1 : z.1 = ((RootJ31.capacityIncrement k x s T Fb p : ℝ≥0) : ℝ≥0∞) := rfl
  have hz2 : ∀ u : ℚ≥0, ((u : ℝ≥0) : ℝ≥0∞) < z.1 →
      z.2 u = RootJ32.stageDriverRead k ε x s L v₀ T u p := fun u hu => ite_eq_left hu
  have hlife : capLife inc (Fb : ℝ≥0∞) = ENNReal.ofReal (inc Fb) := by
    rw [capLife, ite_eq_right ENNReal.coe_ne_top, ENNReal.toNNReal_coe]
  have hτz : ((RootJ31.capacityIncrement k x s T τ p : ℝ≥0) : ℝ≥0∞) < z.1 := by
    rw [hz1, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]; exact hτF
  have hunf : RootJ32.switchedEntry k ε x s L v₀ T Fb p =
      if z ∈ RootD25.reachSet then
        invClock inc (Fb : ℝ≥0∞) (RootD25.entryCapacity z).toNNReal else Fb := rfl
  rw [hunf]
  constructor
  · intro hlt
    by_cases hreach : z ∈ RootD25.reachSet
    · rw [ite_eq_left hreach] at hlt
      have hfin : RootD25.entryCapacity z ≠ ⊤ := ne_top_of_lt hreach
      set e := (RootD25.entryCapacity z).toNNReal with he
      have hez : (e : ℝ≥0∞) < z.1 := by rw [he, ENNReal.coe_toNNReal hfin]; exact hreach
      have helife : (e : ℝ≥0∞) ≤ capLife inc (Fb : ℝ≥0∞) := by
        rw [hlife, hincdef, ENNReal.ofReal_coe_nnreal, ← hz1]; exact hez.le
      obtain ⟨ht0F, hinv⟩ := hclockon.invClock_spec helife
      have ht0mem : invClock inc (Fb : ℝ≥0∞) e ∈ Icc 0 Fb := ⟨zero_le, ENNReal.coe_le_coe.1 ht0F⟩
      have hlt' : (e : ℝ) < inc τ := by rw [← hinv]; exact hsm ht0mem hτmem hlt
      have hecap : RootD25.entryCapacity z <
          ((RootJ31.capacityIncrement k x s T τ p : ℝ≥0) : ℝ≥0∞) := by
        rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_lt_coe]
        exact hlt'
      unfold RootD25.entryCapacity at hecap
      obtain ⟨u, hu⟩ := iInf_lt_iff.1 hecap
      by_cases hcond : ((u : ℝ≥0) : ℝ≥0∞) < z.1 ∧ 2 < z.2 u
      · rw [ite_eq_left hcond] at hu
        refine ⟨u, ENNReal.coe_lt_coe.1 hu, ?_⟩
        rw [← hz2 u hcond.1]
        exact hcond.2
      · rw [ite_eq_right hcond] at hu
        exact absurd hu (not_lt.2 le_top)
    · rw [ite_eq_right hreach] at hlt
      exact absurd (hlt.trans hτ) (lt_irrefl _)
  · rintro ⟨u, hu, h2⟩
    have huz : ((u : ℝ≥0) : ℝ≥0∞) < z.1 := (ENNReal.coe_lt_coe.2 hu).trans hτz
    have hcond : ((u : ℝ≥0) : ℝ≥0∞) < z.1 ∧ 2 < z.2 u := ⟨huz, by rw [hz2 u huz]; exact h2⟩
    have hle : RootD25.entryCapacity z ≤ ((u : ℝ≥0) : ℝ≥0∞) := by
      unfold RootD25.entryCapacity
      exact (iInf_le _ u).trans (by rw [ite_eq_left hcond])
    have hreach : z ∈ RootD25.reachSet := hle.trans_lt huz
    rw [ite_eq_left hreach]
    have hfin : RootD25.entryCapacity z ≠ ⊤ := ne_top_of_lt hreach
    set e := (RootD25.entryCapacity z).toNNReal with he
    have hez : (e : ℝ≥0∞) < z.1 := by rw [he, ENNReal.coe_toNNReal hfin]; exact hreach
    have helife : (e : ℝ≥0∞) ≤ capLife inc (Fb : ℝ≥0∞) := by
      rw [hlife, hincdef, ENNReal.ofReal_coe_nnreal, ← hz1]; exact hez.le
    obtain ⟨ht0F, hinv⟩ := hclockon.invClock_spec helife
    have ht0mem : invClock inc (Fb : ℝ≥0∞) e ∈ Icc 0 Fb := ⟨zero_le, ENNReal.coe_le_coe.1 ht0F⟩
    by_contra hge
    have hge' : τ ≤ invClock inc (Fb : ℝ≥0∞) e := not_lt.1 hge
    have h1 : inc τ ≤ inc (invClock inc (Fb : ℝ≥0∞) e) := hsm.monotoneOn hτmem ht0mem hge'
    rw [hinv] at h1
    have heu : (e : ℝ) ≤ (u : ℝ≥0) := by
      have : (e : ℝ≥0∞) ≤ ((u : ℝ≥0) : ℝ≥0∞) := by rw [he, ENNReal.coe_toNNReal hfin]; exact hle
      exact_mod_cast this
    have : ((u : ℝ≥0) : ℝ) < inc τ := hu
    linarith

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The capacity clock from a positive buffer.** Almost surely, for every history and candidate with a positive
buffer `F`, the capacity reader of the future pair is a strict continuous clock from `0` on `[0, T + F]`, and the
joined future driver has a `⊤`-trace. -/
theorem ae_clock_of_buffer_pos (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), 0 < RootJ31.sourceBuffer c r l a ω →
      ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (futureJoined c r l a ω) ⊤ γ ∧
        RootH29.forwardCapacity (rootPt r.1) c.s 0 (RootJ31.futurePair c r l a ω) = 0 ∧
        StrictMonoOn (fun t => RootH29.forwardCapacity (rootPt r.1) c.s t
          (RootJ31.futurePair c r l a ω))
          (Icc 0 (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω)) ∧
        ContinuousOn (fun t => RootH29.forwardCapacity (rootPt r.1) c.s t
          (RootJ31.futurePair c r l a ω))
          (Icc 0 (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω)) := by
  filter_upwards [RootCv.ae_coverEvent_spec h13 c r, c.hα,
    GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ, ae_futureJoined_trace h13 c r]
    with ω hcover hα hreg hζ hjoin l a hpos
  obtain ⟨hcov, hold, -, hsep⟩ := (RootK32.sourceBuffer_pos_iff c r l a ω).1 hpos
  obtain ⟨hseed, hsH, -, -, -, harc⟩ := hcover hcov
  obtain ⟨_, _, hW, hW0, _⟩ := hreg
  have hs : 0 < c.s := by
    by_contra hn
    have hs0 : c.s = 0 := le_antisymm (not_lt.mp hn) zero_le
    exact ne_zero_of_mem_H hsH (by rw [hs0]; exact hα.1)
  obtain ⟨-, γ, hγ⟩ := hjoin l a hold
  obtain ⟨hJ, hJ0⟩ := continuous_futureJoined c r l a ω
  have hvL : RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω ≤
      Sec5.Prop513Schedule.lastTime 0 (RootJ31.futureProgram c r l a) := by
    rw [lastTime_futureProgram]
    exact add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a ω)
  have hv := RootK32.sourceBuffer_lt_contact c r l a ω hsep
  rw [← lastTime_futureProgram] at hv
  obtain ⟨h0, hm, hc, -⟩ := clock_of_joined_trace c.W c.ζ ω hα hW hW0 hζ hs
    (RootH29.rootPt_nonneg_of_seedOK c hseed) harc hJ hJ0 hγ hvL hv
  exact ⟨γ, hγ, h0, hm, hc⟩

end InteractingSLE.Theorem14.GW2TipSystem.Gm
