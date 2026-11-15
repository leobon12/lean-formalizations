/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmJ32Cross
import InteractingSLE.Spec.Supplement.GW2RootD25Passage

/-!
# J32's regularity on alive histories: the driver clauses

Packet PROVE-GW2-GEOM2 (ruling R111). The successor field `regularity` (`Gm.ExperimentGeometryV`) asks, on alive
histories with `S < F`: `0 ≤ S`, continuity of `X` at `S`, `X(S) ∈ I`, continuity of `γ` on `(S, F)` and null
boundary occupation. This file proves the first three for J32:

* `driver_eq_two_at_entry_of_lt`: the first passage of a continuous driver starting below `2` is at level `2`
  (`RootD25.driver_eq_two_at_entry` needs the start `0`);
* `sourceDriver_nil_zero`, `ae_sourceDriver_zero_lt_two`: on alive histories the stage driver starts below `2`
  (`0` at the root; `−X_l(q) < −7/4` after a passed test, by the cross-program identity);
* **`ae_regularity_X_J32`**: the three driver clauses of `regularity` on alive histories.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 RootD25 Supp8.GB6

/-- **The first passage of a continuous driver starting below `2` is at level `2`.** -/
theorem driver_eq_two_at_entry_of_lt {z : RootV7.DriverRecord} {Y : ℝ≥0 → ℝ}
    (hc : ContinuousOn Y {t | (t : ℝ≥0∞) < z.1}) (hlt : Y 0 < 2)
    (hread : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 → z.2 q = Y q)
    {t : ℝ≥0} (ht : entryCapacity z = (t : ℝ≥0∞)) : Y t = 2 := by
  have hhit : Coupling.hitBelow (fun u => -(-2 + Y u)) z.1 0 =
      (t : WithTop ℝ≥0) := (entryCapacity_eq_hitBelow hc hread).symm.trans ht
  have hg : ContinuousOn (fun u => Y u - Y 0) {s : ℝ≥0 | (s : ℝ≥0∞) < z.1} :=
    hc.sub continuousOn_const
  have hfun : (fun u => -((Y 0 - 2) + (Y u - Y 0))) = fun u => -(-2 + Y u) :=
    funext fun u => by ring
  have h := Sec5.Prop59Stage.eq_zero_of_hitBelow_eq hg (sub_self _)
    (show Y 0 - 2 < 0 by linarith) (by rw [hfun]; exact hhit)
  linarith

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- At the root the history time is the root's time, so the stage driver starts at `0`. -/
theorem sourceDriver_nil_zero (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a : ℕ) (ω : Ω) :
    RootJ32.sourceDriver c r [] a ω 0 = 0 := by
  have hT : RootJ31.historyTime c r [] = (rootEntry r.1).2 := by
    simp [RootJ31.historyTime, RootJ31.historyProgram, schedOf, entryList, schedTime]
  change ((-1) ^ ([] : List (EntryIdx c.Θ c.Q)).length) * ((2 ^ r.2 : ℝ≥0) : ℝ) *
    (RootJ32.capacityDriverRead (rootPt r.1) c.s _
      ((RootH29.forwardCapacity (rootPt r.1) c.s (RootJ31.historyTime c r [])
        (RootJ31.futurePair c r [] a ω)).toNNReal + 0 / (2 ^ r.2) ^ 2) _ - _) = 0
  rw [zero_div, add_zero, hT, sub_self, mul_zero]

/-- **On alive histories J32's stage driver starts below `2`**, almost surely. -/
theorem ae_sourceDriver_zero_lt_two (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      0 < (RootJ31.sourceSample c r l a ω).1 → RootJ32.sourceDriver c r l a ω 0 < 2 := by
  filter_upwards [ae_sourceDriver_cons_zero h13 c r] with ω hω l a halive hlive
  cases l with
  | nil => rw [sourceDriver_nil_zero]; norm_num
  | cons x l₀ =>
    obtain ⟨hprev, htest⟩ := halive
    obtain ⟨a₀, htest⟩ := mem_iUnion.mp htest
    obtain ⟨hang, ht⟩ := mem_iUnion.mp htest
    have he : (RootJ31.candidateAngle c r a₀, x.2) = x := Prod.ext hang rfl
    rw [← he] at hlive ⊢
    rw [hω l₀ a₀ x.2 a hprev ht hlive]
    have hX := ht.2.2.2
    change RootJ32.sourceX c r l₀ a₀ ω ((x.2 : ℝ≥0) : ℝ) ∈ Ioo (7 / 4) (9 / 4) at hX
    linarith [hX.1]

/-- **The driver clauses of J32's regularity on alive histories.** -/
theorem ae_regularity_X_J32 (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      (RootJ32.experiment c r).data.S l a ω < (RootJ32.experiment c r).data.F l a ω →
      0 ≤ (RootJ32.experiment c r).data.S l a ω ∧
      ContinuousAt ((RootJ32.experiment c r).data.X l a ω) ((RootJ32.experiment c r).data.S l a ω) ∧
      (RootJ32.experiment c r).data.X l a ω ((RootJ32.experiment c r).data.S l a ω) ∈
        (RootJ32.experiment c r).data.I l a := by
  filter_upwards [ae_live_clock h13 c r, ae_sourceDriver_zero_lt_two h13 c r,
    RootCv.ae_coverEvent_spec h13 c r, c.hα, GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ,
    c.hζ] with ω hclock hstart hcover hα hreg hζ halive hSF
  have hlive := RootJ32.live_of_entry_lt_failure c r l a ω hSF
  obtain ⟨hcov, -, -, -⟩ := RootK32.sourceSample_live_geometry c r l a ω hlive
  obtain ⟨hseed, hsH, -, -, -, harc⟩ := hcover hcov
  obtain ⟨_, _, hWc, hW0, _⟩ := hreg
  have hs : 0 < c.s := by
    by_contra hn
    have hs0 : c.s = 0 := le_antisymm (not_lt.mp hn) zero_le
    exact ne_zero_of_mem_H hsH (by rw [hs0]; exact hα.1)
  obtain ⟨γ, hγ, hA0, hmono, hcont, -, hnc⟩ := hclock l a hlive
  obtain ⟨hJ, hJ0⟩ := continuous_futureJoined c r l a ω
  have hpe := futurePair_eq_recOfDriver c r l a ω
  set x := rootPt r.1 with hx
  set T := RootJ31.historyTime c r l with hTdef
  set F := RootJ31.sourceBuffer c r l a ω with hFdef
  set L := RootJ31.historyTime c r l + RootJ31.candidateCap c r a with hLdef
  set k : ℝ≥0 := 2 ^ r.2 with hk
  have hk0 : 0 < k := pow_pos (by norm_num) _
  have hFL : T + F ≤ L := add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a ω)
  set A := fun t => RootH29.forwardCapacity x c.s t (RootJ31.futurePair c r l a ω) with hAdef
  have hAnn : ∀ t, 0 ≤ A t := fun t => RootJ32.forwardCapacity_nonneg _ _ _ _
  -- the increment clock on `[0, F]`
  set inc : ℝ≥0 → ℝ := fun t => (RootJ31.capacityIncrement k x c.s T t
    (RootJ31.futurePair c r l a ω) : ℝ) with hincdef
  have hinc : ∀ t ≤ F, inc t = (k : ℝ) ^ 2 * (A (T + t) - A T) := by
    intro t ht
    have hle : A T ≤ A (T + t) :=
      hmono.monotoneOn ⟨zero_le, le_self_add⟩ ⟨zero_le, add_le_add le_rfl ht⟩ le_self_add
    have hle' : RootH29.forwardCapacity x c.s T (RootJ31.futurePair c r l a ω) ≤
        RootH29.forwardCapacity x c.s (T + t) (RootJ31.futurePair c r l a ω) := hle
    simp only [hincdef, RootJ31.capacityIncrement, NNReal.coe_mul, NNReal.coe_pow,
      Real.coe_toNNReal _ (sub_nonneg.2 hle')]
    rfl
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (F : ℝ≥0∞)} = Icc 0 F := by
    ext t; simp only [mem_ofPred_eq, ENNReal.coe_le_coe, mem_Icc, zero_le, true_and]
  have hclockon : IsClockOn inc (F : ℝ≥0∞) := by
    refine ⟨?_, ?_, ?_, fun h => (ENNReal.coe_ne_top h).elim⟩
    · simp only [hincdef, RootJ31.capacityIncrement_zero, NNReal.coe_zero]
    · rw [hset]
      intro t ht t' ht' htt'
      rw [hinc t ht.2, hinc t' ht'.2]
      have := hmono ⟨zero_le, add_le_add le_rfl ht.2⟩ ⟨zero_le, add_le_add le_rfl ht'.2⟩
        ((add_lt_add_iff_left T).2 htt')
      have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
      nlinarith
    · rw [hset]
      have hmaps : MapsTo (fun t : ℝ≥0 => T + t) (Icc 0 F) (Icc 0 (T + F)) :=
        fun t ht => ⟨zero_le, add_le_add le_rfl ht.2⟩
      have h1 : ContinuousOn (fun t : ℝ≥0 => A (T + t)) (Icc 0 F) :=
        hcont.comp (continuous_const.add continuous_id).continuousOn hmaps
      have h2 : ContinuousOn (fun t : ℝ≥0 => (k : ℝ) ^ 2 * (A (T + t) - A T)) (Icc 0 F) :=
        continuousOn_const.mul (h1.sub continuousOn_const)
      exact h2.congr fun t ht => hinc t ht.2
  -- the sample and its entry
  have hreach := RootJ32.entry_lt_failure_imp_reach c r l a ω hSF
  set z := RootJ32.sourceSample c r l a ω with hz
  have hz1 : z.1 = ((RootJ31.capacityIncrement k x c.s T F (RootJ31.futurePair c r l a ω) : ℝ≥0) :
      ℝ≥0∞) := rfl
  have hfin : entryCapacity z ≠ ⊤ := ne_top_of_lt hreach
  set ℓ := (entryCapacity z).toNNReal with hℓ
  have hℓlt : (ℓ : ℝ≥0∞) < z.1 := by rw [hℓ, ENNReal.coe_toNNReal hfin]; exact hreach
  have hlife : capLife inc (F : ℝ≥0∞) = ENNReal.ofReal (inc F) := by
    rw [capLife, ite_eq_right ENNReal.coe_ne_top, ENNReal.toNNReal_coe]
  have hℓlife : (ℓ : ℝ≥0∞) ≤ capLife inc (F : ℝ≥0∞) := by
    rw [hlife, hincdef, ENNReal.ofReal_coe_nnreal, ← hz1]; exact hℓlt.le
  obtain ⟨hse_le, hse⟩ := hclockon.invClock_spec hℓlife
  set se := invClock inc (F : ℝ≥0∞) ℓ with hsedef
  have hS : RootJ32.sourceEntry c r l a ω = ((T + se : ℝ≥0) : ℝ) := by
    have hreach' : RootJ32.sourceSample c r l a ω ∈ RootD25.reachSet := hreach
    rw [sourceEntry_J32_eq]
    simp only [hreach', ↓reduceIte]
    rfl
  have hseF : se < F := by
    have h := hSF
    change RootJ32.sourceEntry c r l a ω < ((T + F : ℝ≥0) : ℝ) at h
    rw [hS] at h
    exact (add_lt_add_iff_left T).1 (NNReal.coe_lt_coe.1 h)
  -- the clock at the entry is the entry capacity
  have hclockS : RootJ31.capacityIncrement k x c.s T se (RootJ31.futurePair c r l a ω) = ℓ :=
    NNReal.coe_injective hse
  -- the stage driver is continuous below the sample's lifetime
  have hYc : ∀ u : ℝ≥0, (u : ℝ≥0∞) < z.1 → ContinuousAt (RootJ32.sourceDriver c r l a ω) u := by
    intro u hu
    rw [hz1, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at hu
    have hu' : (u : ℝ) < inc F := hu
    rw [hinc F le_rfl] at hu'
    have hcap : (((A T).toNNReal + u / k ^ 2 : ℝ≥0) : ℝ) < A (T + F) := by
      rw [NNReal.coe_add, Real.coe_toNNReal _ (hAnn T), NNReal.coe_div, NNReal.coe_pow]
      have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
      rw [add_comm, ← lt_sub_iff_add_lt, div_lt_iff₀ hk2]
      linarith
    have hm' := hmono
    have hc' := hcont
    simp only [hAdef] at hcap hm' hc'
    rw [hpe] at hcap hm' hc'
    have key := continuousAt_stageDriverRead_J32 c.W c.ζ ω hα hWc hW0 hζ hs
      (RootH29.rootPt_nonneg_of_seedOK c hseed) harc hJ hJ0 hγ hFL hnc hm' hc'
      (k := k) ((-1) ^ l.length) (rootEntry r.1).2 T hcap
    have hD : RootJ32.sourceDriver c r l a ω = fun u => RootJ32.stageDriverRead k
        ((-1) ^ l.length) x c.s L (rootEntry r.1).2 T u
        (cfRec c.s c.W c.ζ ω, StagedEntrance.Strip.recOfDriver L (futureJoined c r l a ω)) := by
      funext u
      change RootJ32.stageDriverRead _ _ _ _ _ _ _ u (RootJ31.futurePair c r l a ω) = _
      rw [hpe]
    rw [hD]
    exact key
  -- the first passage is at level `2`
  have hY2 : RootJ32.sourceDriver c r l a ω ℓ = 2 :=
    driver_eq_two_at_entry_of_lt (z := z) (fun u hu => (hYc u hu).continuousWithinAt)
      (hstart l a halive hlive) (fun q hq => RootJ32.sourceSample_read c r l a ω hq)
      (by rw [hℓ, ENNReal.coe_toNNReal hfin])
  -- the observed driver at the entry
  have hXS : ∀ t : ℝ, RootJ32.sourceX c r l a ω t = RootJ32.sourceDriver c r l a ω
      (RootJ31.capacityIncrement k x c.s T (t.toNNReal - T) (RootJ31.futurePair c r l a ω)) :=
    fun _ => rfl
  have hSnn : RootJ32.sourceEntry c r l a ω = ((T + se : ℝ≥0) : ℝ) := hS
  have hclockcont : ContinuousAt (fun τ : ℝ≥0 => RootJ31.capacityIncrement k x c.s T τ
      (RootJ31.futurePair c r l a ω)) se := by
    have hnhds : Icc (0 : ℝ≥0) F ∈ 𝓝 se := by
      rw [show Icc (0 : ℝ≥0) F = Iic F from Icc_bot]; exact Iic_mem_nhds hseF
    have hco : ContinuousOn inc (Icc 0 F) := by rw [← hset]; exact hclockon.continuousOn
    have h1 : ContinuousAt inc se := hco.continuousAt hnhds
    exact (NNReal.isEmbedding_coe.continuousAt_iff).2 h1
  refine ⟨?_, ?_, ?_⟩
  · change 0 ≤ RootJ32.sourceEntry c r l a ω
    rw [hS]; exact NNReal.coe_nonneg _
  · change ContinuousAt (RootJ32.sourceX c r l a ω) (RootJ32.sourceEntry c r l a ω)
    have hfun : RootJ32.sourceX c r l a ω = (RootJ32.sourceDriver c r l a ω) ∘
        (fun τ : ℝ≥0 => RootJ31.capacityIncrement k x c.s T τ (RootJ31.futurePair c r l a ω)) ∘
          (fun t : ℝ => t.toNNReal - T) := funext hXS
    rw [hfun, hS]
    have hin : ContinuousAt (fun t : ℝ => t.toNNReal - T) ((T + se : ℝ≥0) : ℝ) :=
      (continuous_real_toNNReal.sub continuous_const).continuousAt
    have hpt : ((T + se : ℝ≥0) : ℝ).toNNReal - T = se := by
      rw [Real.toNNReal_coe, add_tsub_cancel_left]
    refine ContinuousAt.comp ?_ (ContinuousAt.comp ?_ hin)
    · rw [Function.comp_apply, hpt, hclockS]
      exact hYc ℓ hℓlt
    · rw [hpt]; exact hclockcont
  · change RootJ32.sourceX c r l a ω (RootJ32.sourceEntry c r l a ω) ∈ Ioo (7 / 4) (9 / 4)
    rw [hXS, hS, Real.toNNReal_coe, add_tsub_cancel_left, hclockS, hY2]
    norm_num

end InteractingSLE.Theorem14.GW2TipSystem.Gm
