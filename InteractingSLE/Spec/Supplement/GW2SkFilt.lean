/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SkCore
import InteractingSLE.Spec.Supplement.RelSafeGB6Read
import InteractingSLE.Spec.Supplement.Q3StopTransfer

/-!
# GW2's stage identity: the stage clock and the stage filtration

Packet PROVE-GW2-RELDET, ruling R106. For GB6's relative exploration at any instance (explored driver `W`, retained
curve `Wα, ζα, α` at `s`, good set `GT`, an R-form version `(R, V)`), stage `n` starts at the deterministic physical
time `T`. Write `m(τ) = min (physClock τ, V)` for GB6's line clock. The stage objects are:

* the relative start `stgStartM T = m(T)` and `stgStart T = (m T).toNNReal`;
* the stage clock `stgClock T t = m(T + t) − m(T)`: continuous, monotone and `0` at `0` everywhere
  (`continuous_stgClock`, `monotone_stgClock`, `stgClock_zero`);
* the stage filtration `shiftFilt (physFilt …) T`, i.e. `physFilt (T + t)`. The clock is adapted to it
  (`measurable_stgClock`).

The stage relative driver is `stgDrv R (stgStart T)` and the stage stop is `V − stgStart T`. Then:

* **`measurableSet_inter_le_stgClock_of_canonFilt`**: the stage canonical filtration (record `x` readable at
  physical time `T`), traced on `{q ≤ stgClock T t}`, is in `physFilt (T + t)`. This is the hypothesis `h𝓗'` of
  `GW2Rd.hasRelSafe_of_lines_rec` at the stage. It is GB6's `measurableSet_inter_le_min_of_canonFilt` at the
  RANDOM levels `stgStart T + u`, via `GW2Rd.measurableSet_inter_drv_rand` and `measurableSet_inter_stop_le_rand`.
* **`reach_stgClock`**: every stage level below the stage stop is reached, wherever the stage start is finite
  (GB6's `reach_min_physClock` at rational levels).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.RelSafe

/-! ### Definitions -/

section Defs

variable {Ω : Type*}

/-- The relative clock at the stage start (GB6's line clock at `T`). -/
abbrev stgStartM (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (V : Ω → ℝ≥0∞) (T : ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  min (physClock s W Wα ζα GT T ω) (V ω)

/-- **The stage relative start.** -/
abbrev stgStart (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (V : Ω → ℝ≥0∞) (T : ℝ≥0)
    (ω : Ω) : ℝ≥0 :=
  (stgStartM s W Wα ζα GT V T ω).toNNReal

/-- **The stage clock**: GB6's line clock at `T + t` minus its value at `T`. -/
def stgClock (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (V : Ω → ℝ≥0∞) (T t : ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  min (physClock s W Wα ζα GT (T + t) ω) (V ω) - stgStartM s W Wα ζα GT V T ω

/-- **A filtration shifted by `T`.** -/
def shiftFilt [mΩ : MeasurableSpace Ω] (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ) (T : ℝ≥0) :
    MeasureTheory.Filtration ℝ≥0 mΩ where
  seq t := 𝓕 (T + t)
  mono' _ _ h := 𝓕.mono (add_le_add le_rfl h)
  le' t := 𝓕.le (T + t)

theorem shiftFilt_apply [mΩ : MeasurableSpace Ω] (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ) (T t : ℝ≥0) :
    shiftFilt 𝓕 T t = 𝓕 (T + t) := rfl

end Defs

/-! ### The clock -/

section Clock

variable {Ω : Type*} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω}
  {V : Ω → ℝ≥0∞} (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω)

include hGT in
theorem continuous_stgClock (T : ℝ≥0) (ω : Ω) : Continuous fun t => stgClock s W Wα ζα GT V T t ω :=
  (ENNReal.continuous_sub_right _).comp
    ((continuous_min_physClock hGT ω).comp (continuous_const.add continuous_id))

include hGT in
theorem monotone_stgClock (T : ℝ≥0) (ω : Ω) : Monotone fun t => stgClock s W Wα ζα GT V T t ω :=
  fun _ _ h => tsub_le_tsub_right (monotone_min_physClock hGT ω (add_le_add le_rfl h)) _

theorem stgClock_zero (T : ℝ≥0) (ω : Ω) : stgClock s W Wα ζα GT V T 0 ω = 0 := by
  simp only [stgClock, add_zero, tsub_self]

include hGT in
/-- The stage start is below the line clock at every later time. -/
theorem stgStartM_le (T t : ℝ≥0) (ω : Ω) :
    stgStartM s W Wα ζα GT V T ω ≤ min (physClock s W Wα ζα GT (T + t) ω) (V ω) :=
  monotone_min_physClock hGT ω le_self_add

include hGT in
/-- **On `{q ≤ stgClock T t}`, every stage level up to `q` is below the line clock at `T + t`.** -/
theorem coe_stgStart_add_le {T t q u : ℝ≥0} {ω : Ω} (hq : (q : ℝ≥0∞) ≤ stgClock s W Wα ζα GT V T t ω)
    (hu : u ≤ q) :
    ((stgStart s W Wα ζα GT V T ω + u : ℝ≥0) : ℝ≥0∞) ≤ min (physClock s W Wα ζα GT (T + t) ω) (V ω) := by
  have hle := stgStartM_le hGT (V := V) T t ω
  by_cases htop : stgStartM s W Wα ζα GT V T ω = ⊤
  · rw [htop, top_le_iff] at hle
    rw [hle]
    exact le_top
  · have hS : ((stgStart s W Wα ζα GT V T ω : ℝ≥0) : ℝ≥0∞) = stgStartM s W Wα ζα GT V T ω :=
      ENNReal.coe_toNNReal htop
    rw [ENNReal.coe_add, hS]
    calc stgStartM s W Wα ζα GT V T ω + u ≤ stgStartM s W Wα ζα GT V T ω + q := by gcongr
      _ ≤ stgStartM s W Wα ζα GT V T ω + stgClock s W Wα ζα GT V T t ω := by gcongr
      _ = min (physClock s W Wα ζα GT (T + t) ω) (V ω) := add_tsub_cancel_of_le hle

end Clock

/-! ### The filtration -/

section Filt

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω) (hrec : Measurable (gb6Rec s Wα ζα)) (hWm : ∀ r, Measurable (W r))
  (hGTm : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT)

include hGT hGTm in
/-- The stage start is readable at the stage start. -/
theorem measurable_stgStartM (hver : HullId.IsGB6RelVersionR s P W Wα ζα γ α R V) (T : ℝ≥0) :
    Measurable[physFilt hrec hWm P T] (stgStartM s W Wα ζα GT V T) :=
  measurable_min_physClock hGT hrec hWm hGTm hver T

include hGT hGTm in
/-- **The stage clock is adapted to the stage filtration.** -/
theorem measurable_stgClock (hver : HullId.IsGB6RelVersionR s P W Wα ζα γ α R V) (T t : ℝ≥0) :
    Measurable[shiftFilt (physFilt hrec hWm P) T t] (stgClock s W Wα ζα GT V T t) :=
  (measurable_min_physClock hGT hrec hWm hGTm hver (T + t)).sub
    ((measurable_stgStartM hGT hrec hWm hGTm hver T).mono ((physFilt hrec hWm P).mono le_self_add) le_rfl)

include hGT hGTm in
/-- **The stage canonical filtration, traced on `{q ≤ stgClock T t}`, is in the stage filtration** (the hypothesis
`h𝓗'` of `GW2Rd.hasRelSafe_of_lines_rec` at the stage). -/
theorem measurableSet_inter_le_stgClock_of_canonFilt (hver : HullId.IsGB6RelVersionR s P W Wα ζα γ α R V)
    (T : ℝ≥0) {x : Ω → RecData} (hx : Measurable[physFilt hrec hWm P T] x) {Hr : Ω → DistOn upperHalfPlaneOpens}
    (hΦ : Measurable fun ω => (x ω, relVar Hr (fun u ω => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) u)
      (fun ω => V ω - stgStart s W Wα ζα GT V T ω) ω))
    (q : ℝ≥0) {D : Set Ω} (hD : MeasurableSet[Coupling.filtrationComap Supp8.Q3Stop.canonFilt hΦ q] D)
    (t : ℝ≥0) :
    MeasurableSet[shiftFilt (physFilt hrec hWm P) T t] (D ∩ {ω | (q : ℝ≥0∞) ≤ stgClock s W Wα ζα GT V T t ω}) := by
  obtain ⟨hv, ρ, hρm, hρ, hVρ⟩ := hver
  have hRm := hv.1
  have hRc := hv.2.1
  have hR0 := hv.2.2.1
  have hVm := hv.2.2.2.2.1
  have hm : physFilt hrec hWm P (T + t) ≤ mΩ := (physFilt hrec hWm P).le (T + t)
  have hnull : Ito.nullSets P ≤ physFilt hrec hWm P (T + t) := nullSets_le_physFilt hrec hWm P (T + t)
  have hTt : physFilt hrec hWm P T ≤ physFilt hrec hWm P (T + t) := (physFilt hrec hWm P).mono le_self_add
  have hS : Measurable[physFilt hrec hWm P (T + t)] (stgStart s W Wα ζα GT V T) :=
    ENNReal.measurable_toNNReal.comp ((measurable_stgStartM hGT hrec hWm hGTm ⟨hv, ρ, hρm, hρ, hVρ⟩ T).mono hTt le_rfl)
  have hL : MeasurableSet[physFilt hrec hWm P (T + t)] {ω | (q : ℝ≥0∞) ≤ stgClock s W Wα ζα GT V T t ω} :=
    measurableSet_le measurable_const (measurable_stgClock hGT hrec hWm hGTm ⟨hv, ρ, hρm, hρ, hVρ⟩ T t)
  -- the readable driver
  set Y : ℝ≥0 → Ω → ℝ := leftReg (physDrv s W Wα ζα GT (T + t)) with hYdef
  have hY : ∀ u, Measurable[physFilt hrec hWm P (T + t)] (Y u) := fun u =>
    measurable_leftReg (measurable_physDrv_physFilt hGT hrec hWm hGTm (T + t)) u
  have hRY := ae_eq_leftReg hRc hR0 (ae_eq_physDrv_of_isGB6RelVersion hGT hv (T + t))
  have hRYL : ∀ u ≤ q, ∀ᵐ ω ∂P, ω ∈ {ω | (q : ℝ≥0∞) ≤ stgClock s W Wα ζα GT V T t ω} →
      ∀ v : ℝ≥0, v ≤ stgStart s W Wα ζα GT V T ω + u → R v ω = Y v ω := fun u hu => by
    filter_upwards [hRY] with ω hω hωL v hv'
    have h1 := (ENNReal.coe_le_coe.2 hv').trans (coe_stgStart_add_le hGT hωL hu)
    exact hω v (h1.trans (min_le_left _ _)) (h1.trans (min_le_right _ _))
  rw [inter_comm]
  refine Supp8.Q3Stop.measurableSet_inter_of_canonFilt hΦ hL (fun A hA => ?_) (fun u hu B hB => ?_)
    (fun u hu => ?_) hD
  · exact hL.inter ((hx.mono hTt le_rfl) hA)
  · -- the stage driver at `u`: two readings of `R` at random times
    have e : (fun ω => Supp8.Q3Stop.canonDrv u (x ω, relVar Hr
        (fun u ω => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) u)
        (fun ω => V ω - stgStart s W Wα ζα GT V T ω) ω)) ⁻¹' B =
        {ω | R (stgStart s W Wα ζα GT V T ω + u) ω - R (stgStart s W Wα ζα GT V T ω) ω ∈ B} := by
      ext ω
      simp only [mem_preimage, Supp8.Q3Stop.canonDrv, mem_ofPred_eq]
      have hr := relDrv_relVar (Hc := Hr) (V := fun ω => V ω - stgStart s W Wα ζα GT V T ω)
        (R := fun u ω => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) u) (ω := ω)
        (continuous_stgDrv (hRc ω) _) (stgDrv_zero _ _) u
      rw [hr]
      rfl
    rw [e]
    have hj : Measurable fun p : ℝ≥0 × Ω => R p.1 p.2 :=
      measurable_uncurry_of_continuous_of_measurable (u := fun t ω => R t ω) hRc hRm
    have hSa : Measurable (stgStart s W Wα ζα GT V T) := hS.mono hm le_rfl
    have hamb : Measurable fun ω => R (stgStart s W Wα ζα GT V T ω + u) ω - R (stgStart s W Wα ζα GT V T ω) ω :=
      (hj.comp ((hSa.add measurable_const).prodMk measurable_id)).sub (hj.comp (hSa.prodMk measurable_id))
    have hg : Measurable[physFilt hrec hWm P (T + t)] fun ω =>
        evalDn (fun v => Y v ω) (stgStart s W Wα ζα GT V T ω + u) -
        evalDn (fun v => Y v ω) (stgStart s W Wα ζα GT V T ω) :=
      (measurable_evalDn_of hY (hS.add measurable_const)).sub (measurable_evalDn_of hY hS)
    refine measurableSet_of_ae_eq hm hnull ((hm _ hL).inter (hamb hB)) (hL.inter (hg hB)) ?_
    filter_upwards [hRYL u hu] with ω hω
    by_cases hωL : ω ∈ {ω | (q : ℝ≥0∞) ≤ stgClock s W Wα ζα GT V T t ω}
    · have e1 : evalDn (fun v => Y v ω) (stgStart s W Wα ζα GT V T ω + u) =
          R (stgStart s W Wα ζα GT V T ω + u) ω := by
        rw [← evalDn_eq (hRc ω)]
        exact evalDn_congr fun v hv => (hω hωL v hv).symm
      have e2 : evalDn (fun v => Y v ω) (stgStart s W Wα ζα GT V T ω) = R (stgStart s W Wα ζα GT V T ω) ω := by
        rw [← evalDn_eq (hRc ω)]
        exact evalDn_congr fun v hv => (hω hωL v (hv.trans le_self_add)).symm
      simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, hωL, true_and, e1, e2]
    · simp only [mem_inter_iff, hωL, false_and]
  · -- the stage stop below `u`: a path-rule stop at the random level `stgStart + u`
    have e : {ω | Supp8.Q3Stop.canonStp (x ω, relVar Hr
        (fun u ω => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) u)
        (fun ω => V ω - stgStart s W Wα ζα GT V T ω) ω) ≤ (u : ℝ≥0∞)} =
        {ω | V ω ≤ ((stgStart s W Wα ζα GT V T ω + u : ℝ≥0) : ℝ≥0∞)} := by
      ext ω
      simp only [Supp8.Q3Stop.canonStp, relStp, relVar, mem_ofPred_eq, tsub_le_iff_right, ENNReal.coe_add,
        add_comm (u : ℝ≥0∞)]
    rw [e]
    refine measurableSet_inter_stop_le_rand hm hnull (measurable_rec_physFilt hrec hWm (T + t)) hρm hρ hRc hVm hVρ
      hY hL (hS.add measurable_const) ?_
    filter_upwards [hRYL u hu] with ω hω hωL v hv _ using hω hωL v hv

include hGT in
/-- **Every stage level below the stage stop is reached**, where the stage start is finite. -/
theorem reach_stgClock (T : ℝ≥0) (hver : IsGB6RelVersion s P W Wα ζα γ α R V)
    (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s Wα ζα ω ∈ gb6TS s) {F : Set Ω}
    (hF : ∀ᵐ ω ∂P, ω ∈ F → gb6Rec s Wα ζα ω ∈ gb6TS s)
    (hfin : ∀ᵐ ω ∂P, ω ∈ F → stgStartM s W Wα ζα GT V T ω ≠ ⊤) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < V ω - stgStart s W Wα ζα GT V T ω →
      ∃ t, (q : ℝ≥0∞) ≤ stgClock s W Wα ζα GT V T t ω := by
  have hall : ∀ᵐ ω ∂P, ∀ r : ℚ, ω ∈ F → ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < V ω →
      ∃ t, ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) ≤ min (physClock s W Wα ζα GT t ω) (V ω) :=
    ae_all_iff.2 fun r => reach_min_physClock hGT hver hGTae hF (Real.toNNReal r)
  filter_upwards [hall, hfin] with ω hω hf hωF hqV
  have hS : ((stgStart s W Wα ζα GT V T ω : ℝ≥0) : ℝ≥0∞) = stgStartM s W Wα ζα GT V T ω :=
    ENNReal.coe_toNNReal (hf hωF)
  rw [hS] at hqV
  have hSV : stgStartM s W Wα ζα GT V T ω ≤ V ω := by
    by_contra hc
    rw [tsub_eq_zero_of_le (le_of_lt (lt_of_not_ge hc))] at hqV
    exact (not_lt_zero hqV).elim
  have h1 : stgStartM s W Wα ζα GT V T ω + q < V ω :=
    calc stgStartM s W Wα ζα GT V T ω + q < stgStartM s W Wα ζα GT V T ω + (V ω - stgStartM s W Wα ζα GT V T ω) :=
          ENNReal.add_lt_add_left (hf hωF) hqV
      _ = V ω := add_tsub_cancel_of_le hSV
  obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h1
  obtain ⟨t, ht⟩ := hω r hωF hr2
  refine ⟨t, ?_⟩
  have h2 : ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) ≤ min (physClock s W Wα ζα GT (T + t) ω) (V ω) :=
    ht.trans (monotone_min_physClock hGT ω le_add_self)
  have h3 : stgStartM s W Wα ζα GT V T ω + q ≤ min (physClock s W Wα ζα GT (T + t) ω) (V ω) :=
    hr1.le.trans h2
  unfold stgClock
  exact ENNReal.le_sub_of_add_le_left (hf hωF) h3

end Filt

end InteractingSLE.Theorem14.GW2Rd
