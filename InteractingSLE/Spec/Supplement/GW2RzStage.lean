/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzAdapt
import InteractingSLE.Spec.Supplement.GW2SkSafe
import InteractingSLE.Spec.Supplement.GW2SkRec


/-!
# GW2 at a root `x`: the stage clock, the prefix record and the stage safe events (decision D8, layer 5)

Packet PROVE-GW2-ROOTX, round 3. RELDET's stage layer (`GW2SkFilt`, `GW2SkRec`, `GW2SkSafe`, and GB6's
`GB6LineL.hasGB6SafeMeas_of`) at a root `x₀`, with the root-`x` line clock `m(τ) = min(physClockX τ, V)`
(`GW2RzPhys`, `GW2RzAdapt`) in place of GB6's. The proofs are RELDET's with the root-`x` physical lemmas:

* `stgStartMX`, `stgStartX`, `stgClockX` (`m(T + t) − m(T)`), `stgPreRecX` (the relative driver up to the start);
* `continuous_stgClockX`, `monotone_stgClockX`, `stgClockX_zero`, `stgStartM_leX`, `coe_stgStart_add_leX`,
  `measurable_stgStartMX`, **`measurable_stgClockX`**, **`measurableSet_inter_le_stgClockX_of_canonFilt`** (`h𝓗'`
  at the stage), **`reach_stgClockX`**;
* `stgPreRec_timeX`, `rdrv_stgPreRecX`, **`measurable_stgPreRecX`** (readable at the physical stage start),
  `augDec_specX`;
* **`hasGB6SafeMeas_ofX`** (the root-`x` safe events of the whole exploration), `coe_stgStart_add_min_leX`,
  `measurableSet_stgSafeX`, **`hasStgSafeMeasX`** (the stage safe events `hSψ`, `hSb`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull drive)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW2Rz

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.RelSafe Supp8.RelSafeS Supp8.GB6LineL GW2TipSystem GW2Rd

/-! ### Definitions -/

section Defs

variable {Ω : Type*}

/-- The root-`x` relative clock at the stage start (the root-`x` line clock at `T`). -/
abbrev stgStartMX (x₀ : ℝ) (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (V : Ω → ℝ≥0∞) (T : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  min (physClockX x₀ s Wα ζα W GT T ω) (V ω)

/-- **The root-`x` stage relative start.** -/
abbrev stgStartX (x₀ : ℝ) (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (V : Ω → ℝ≥0∞) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (stgStartMX x₀ s Wα ζα W GT V T ω).toNNReal

/-- **The root-`x` stage clock**: the root-`x` line clock at `T + t` minus its value at `T`. -/
def stgClockX (x₀ : ℝ) (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (V : Ω → ℝ≥0∞) (T t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω) - stgStartMX x₀ s Wα ζα W GT V T ω

/-- **The record of the relative driver up to the root-`x` stage start.** -/
def stgPreRecX (x₀ : ℝ) (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (V : Ω → ℝ≥0∞) (T : ℝ≥0) (R : ℝ≥0 → Ω → ℝ) (ω : Ω) : RecData :=
  recOf (stgStartX x₀ s Wα ζα W GT V T ω : ℝ≥0∞) (fun u => R u ω, ⊤)

end Defs

/-! ### The clock -/

section Clock

variable {Ω : Type*} {x₀ : ℝ} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω}
  {V : Ω → ℝ≥0∞} (hGT : ∀ ω ∈ GT, PhysGoodX x₀ s Wα ζα W γ α ω) (hs₀ : 0 < s) (hx₀ : 0 ≤ x₀)

include hGT hs₀ hx₀ in
theorem continuous_stgClockX (T : ℝ≥0) (ω : Ω) : Continuous fun t => stgClockX x₀ s Wα ζα W GT V T t ω :=
  (ENNReal.continuous_sub_right _).comp
    ((continuous_min_physClockX hGT hs₀ hx₀ ω).comp (continuous_const.add continuous_id))

include hGT hs₀ hx₀ in
theorem monotone_stgClockX (T : ℝ≥0) (ω : Ω) : Monotone fun t => stgClockX x₀ s Wα ζα W GT V T t ω :=
  fun _ _ h => tsub_le_tsub_right (monotone_min_physClockX hGT hs₀ hx₀ ω (add_le_add le_rfl h)) _

theorem stgClock_zeroX (T : ℝ≥0) (ω : Ω) : stgClockX x₀ s Wα ζα W GT V T 0 ω = 0 := by
  simp only [stgClockX, add_zero, tsub_self]

include hGT hs₀ hx₀ in
/-- The stage start is below the line clock at every later time. -/
theorem stgStartM_leX (T t : ℝ≥0) (ω : Ω) :
    stgStartMX x₀ s Wα ζα W GT V T ω ≤ min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω) :=
  monotone_min_physClockX hGT hs₀ hx₀ ω le_self_add

include hGT hs₀ hx₀ in
/-- **On `{q ≤ stgClockX T t}`, every stage level up to `q` is below the line clock at `T + t`.** -/
theorem coe_stgStart_add_leX {T t q u : ℝ≥0} {ω : Ω} (hq : (q : ℝ≥0∞) ≤ stgClockX x₀ s Wα ζα W GT V T t ω)
    (hu : u ≤ q) :
    ((stgStartX x₀ s Wα ζα W GT V T ω + u : ℝ≥0) : ℝ≥0∞) ≤ min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω) := by
  have hle := stgStartM_leX hGT hs₀ hx₀ (V := V) T t ω
  by_cases htop : stgStartMX x₀ s Wα ζα W GT V T ω = ⊤
  · rw [htop, top_le_iff] at hle
    rw [hle]
    exact le_top
  · have hS : ((stgStartX x₀ s Wα ζα W GT V T ω : ℝ≥0) : ℝ≥0∞) = stgStartMX x₀ s Wα ζα W GT V T ω :=
      ENNReal.coe_toNNReal htop
    rw [ENNReal.coe_add, hS]
    calc stgStartMX x₀ s Wα ζα W GT V T ω + u ≤ stgStartMX x₀ s Wα ζα W GT V T ω + q := by gcongr
      _ ≤ stgStartMX x₀ s Wα ζα W GT V T ω + stgClockX x₀ s Wα ζα W GT V T t ω := by gcongr
      _ = min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω) := add_tsub_cancel_of_le hle

end Clock

/-! ### The filtration -/

section Filt

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {x₀ : ℝ} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  (hGT : ∀ ω ∈ GT, PhysGoodX x₀ s Wα ζα W γ α ω) (hs₀ : 0 < s) (hx₀ : 0 ≤ x₀)
  (hrec : Measurable (cfRec s Wα ζα)) (hWm : ∀ r, Measurable (W r))
  (hGTm : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT)

include hGT hs₀ hx₀ hGTm in
/-- The stage start is readable at the stage start. -/
theorem measurable_stgStartMX (hver : IsRelVersionXR x₀ s P Wα ζα W γ α R V) (T : ℝ≥0) :
    Measurable[physFilt hrec hWm P T] (stgStartMX x₀ s Wα ζα W GT V T) :=
  measurable_min_physClockX hGT hs₀ hx₀ hrec hWm hGTm hver T

include hGT hs₀ hx₀ hGTm in
/-- **The stage clock is adapted to the stage filtration.** -/
theorem measurable_stgClockX (hver : IsRelVersionXR x₀ s P Wα ζα W γ α R V) (T t : ℝ≥0) :
    Measurable[shiftFilt (physFilt hrec hWm P) T t] (stgClockX x₀ s Wα ζα W GT V T t) :=
  (measurable_min_physClockX hGT hs₀ hx₀ hrec hWm hGTm hver (T + t)).sub
    ((measurable_stgStartMX hGT hs₀ hx₀ hrec hWm hGTm hver T).mono ((physFilt hrec hWm P).mono le_self_add) le_rfl)

include hGT hs₀ hx₀ hGTm in
/-- **The stage canonical filtration, traced on `{q ≤ stgClockX T t}`, is in the stage filtration** (the hypothesis
`h𝓗'` of `GW2Rd.hasRelSafe_of_lines_rec` at the stage). -/
theorem measurableSet_inter_le_stgClock_of_canonFiltX (hver : IsRelVersionXR x₀ s P Wα ζα W γ α R V)
    (T : ℝ≥0) {x : Ω → RecData} (hx : Measurable[physFilt hrec hWm P T] x) {Hr : Ω → DistOn upperHalfPlaneOpens}
    (hΦ : Measurable fun ω => (x ω, relVar Hr (fun u ω => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) u)
      (fun ω => V ω - stgStartX x₀ s Wα ζα W GT V T ω) ω))
    (q : ℝ≥0) {D : Set Ω} (hD : MeasurableSet[Coupling.filtrationComap Supp8.Q3Stop.canonFilt hΦ q] D)
    (t : ℝ≥0) :
    MeasurableSet[shiftFilt (physFilt hrec hWm P) T t] (D ∩ {ω | (q : ℝ≥0∞) ≤ stgClockX x₀ s Wα ζα W GT V T t ω}) := by
  obtain ⟨hv, ρ, hρm, hρ, hVρ⟩ := hver
  have hRm := hv.1
  have hRc := hv.2.1
  have hR0 := hv.2.2.1
  have hVm := hv.2.2.2.2.1
  have hm : physFilt hrec hWm P (T + t) ≤ mΩ := (physFilt hrec hWm P).le (T + t)
  have hnull : Ito.nullSets P ≤ physFilt hrec hWm P (T + t) := nullSets_le_physFilt hrec hWm P (T + t)
  have hTt : physFilt hrec hWm P T ≤ physFilt hrec hWm P (T + t) := (physFilt hrec hWm P).mono le_self_add
  have hS : Measurable[physFilt hrec hWm P (T + t)] (stgStartX x₀ s Wα ζα W GT V T) :=
    ENNReal.measurable_toNNReal.comp
      ((measurable_stgStartMX hGT hs₀ hx₀ hrec hWm hGTm ⟨hv, ρ, hρm, hρ, hVρ⟩ T).mono hTt le_rfl)
  have hL : MeasurableSet[physFilt hrec hWm P (T + t)] {ω | (q : ℝ≥0∞) ≤ stgClockX x₀ s Wα ζα W GT V T t ω} :=
    measurableSet_le measurable_const (measurable_stgClockX hGT hs₀ hx₀ hrec hWm hGTm ⟨hv, ρ, hρm, hρ, hVρ⟩ T t)
  -- the readable driver
  set Y : ℝ≥0 → Ω → ℝ := leftReg (physDrvX x₀ s Wα ζα W GT (T + t)) with hYdef
  have hY : ∀ u, Measurable[physFilt hrec hWm P (T + t)] (Y u) := fun u =>
    measurable_leftReg (measurable_physDrvX_physFilt hGT hrec hWm hGTm (T + t)) u
  have hRY := ae_eq_leftReg hRc hR0 (ae_eq_physDrvX_of_isRelVersionX hGT hs₀ hx₀ hv (T + t))
  have hRYL : ∀ u ≤ q, ∀ᵐ ω ∂P, ω ∈ {ω | (q : ℝ≥0∞) ≤ stgClockX x₀ s Wα ζα W GT V T t ω} →
      ∀ v : ℝ≥0, v ≤ stgStartX x₀ s Wα ζα W GT V T ω + u → R v ω = Y v ω := fun u hu => by
    filter_upwards [hRY] with ω hω hωL v hv'
    have h1 := (ENNReal.coe_le_coe.2 hv').trans (coe_stgStart_add_leX hGT hs₀ hx₀ hωL hu)
    exact hω v (h1.trans (min_le_left _ _)) (h1.trans (min_le_right _ _))
  rw [inter_comm]
  refine Supp8.Q3Stop.measurableSet_inter_of_canonFilt hΦ hL (fun A hA => ?_) (fun u hu B hB => ?_)
    (fun u hu => ?_) hD
  · exact hL.inter ((hx.mono hTt le_rfl) hA)
  · -- the stage driver at `u`: two readings of `R` at random times
    have e : (fun ω => Supp8.Q3Stop.canonDrv u (x ω, relVar Hr
        (fun u ω => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) u)
        (fun ω => V ω - stgStartX x₀ s Wα ζα W GT V T ω) ω)) ⁻¹' B =
        {ω | R (stgStartX x₀ s Wα ζα W GT V T ω + u) ω - R (stgStartX x₀ s Wα ζα W GT V T ω) ω ∈ B} := by
      ext ω
      simp only [mem_preimage, Supp8.Q3Stop.canonDrv, mem_ofPred_eq]
      have hr := relDrv_relVar (Hc := Hr) (V := fun ω => V ω - stgStartX x₀ s Wα ζα W GT V T ω)
        (R := fun u ω => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) u) (ω := ω)
        (continuous_stgDrv (hRc ω) _) (stgDrv_zero _ _) u
      rw [hr]
      rfl
    rw [e]
    have hj : Measurable fun p : ℝ≥0 × Ω => R p.1 p.2 :=
      measurable_uncurry_of_continuous_of_measurable (u := fun t ω => R t ω) hRc hRm
    have hSa : Measurable (stgStartX x₀ s Wα ζα W GT V T) := hS.mono hm le_rfl
    have hamb : Measurable fun ω => R (stgStartX x₀ s Wα ζα W GT V T ω + u) ω - R (stgStartX x₀ s Wα ζα W GT V T ω) ω :=
      (hj.comp ((hSa.add measurable_const).prodMk measurable_id)).sub (hj.comp (hSa.prodMk measurable_id))
    have hg : Measurable[physFilt hrec hWm P (T + t)] fun ω =>
        evalDn (fun v => Y v ω) (stgStartX x₀ s Wα ζα W GT V T ω + u) -
        evalDn (fun v => Y v ω) (stgStartX x₀ s Wα ζα W GT V T ω) :=
      (measurable_evalDn_of hY (hS.add measurable_const)).sub (measurable_evalDn_of hY hS)
    refine measurableSet_of_ae_eq hm hnull ((hm _ hL).inter (hamb hB)) (hL.inter (hg hB)) ?_
    filter_upwards [hRYL u hu] with ω hω
    by_cases hωL : ω ∈ {ω | (q : ℝ≥0∞) ≤ stgClockX x₀ s Wα ζα W GT V T t ω}
    · have e1 : evalDn (fun v => Y v ω) (stgStartX x₀ s Wα ζα W GT V T ω + u) =
          R (stgStartX x₀ s Wα ζα W GT V T ω + u) ω := by
        rw [← evalDn_eq (hRc ω)]
        exact evalDn_congr fun v hv => (hω hωL v hv).symm
      have e2 : evalDn (fun v => Y v ω) (stgStartX x₀ s Wα ζα W GT V T ω) = R (stgStartX x₀ s Wα ζα W GT V T ω) ω := by
        rw [← evalDn_eq (hRc ω)]
        exact evalDn_congr fun v hv => (hω hωL v (hv.trans le_self_add)).symm
      simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, hωL, true_and, e1, e2]
    · simp only [mem_inter_iff, hωL, false_and]
  · -- the stage stop below `u`: a path-rule stop at the random level `stgStartX + u`
    have e : {ω | Supp8.Q3Stop.canonStp (x ω, relVar Hr
        (fun u ω => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) u)
        (fun ω => V ω - stgStartX x₀ s Wα ζα W GT V T ω) ω) ≤ (u : ℝ≥0∞)} =
        {ω | V ω ≤ ((stgStartX x₀ s Wα ζα W GT V T ω + u : ℝ≥0) : ℝ≥0∞)} := by
      ext ω
      simp only [Supp8.Q3Stop.canonStp, relStp, relVar, mem_ofPred_eq, tsub_le_iff_right, ENNReal.coe_add,
        add_comm (u : ℝ≥0∞)]
    rw [e]
    refine measurableSet_inter_stop_le_rand hm hnull (measurable_rec_physFiltX hrec hWm (T + t)) hρm hρ hRc hVm hVρ
      hY hL (hS.add measurable_const) ?_
    filter_upwards [hRYL u hu] with ω hω hωL v hv _ using hω hωL v hv

include hGT hs₀ hx₀ in
/-- **Every stage level below the stage stop is reached**, where the stage start is finite. -/
theorem reach_stgClockX (T : ℝ≥0) (hver : IsRelVersionX x₀ s P Wα ζα W γ α R V)
    (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ cfRec s Wα ζα ω ∈ goodX x₀ s) {F : Set Ω}
    (hF : ∀ᵐ ω ∂P, ω ∈ F → cfRec s Wα ζα ω ∈ goodX x₀ s)
    (hfin : ∀ᵐ ω ∂P, ω ∈ F → stgStartMX x₀ s Wα ζα W GT V T ω ≠ ⊤) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < V ω - stgStartX x₀ s Wα ζα W GT V T ω →
      ∃ t, (q : ℝ≥0∞) ≤ stgClockX x₀ s Wα ζα W GT V T t ω := by
  have hall : ∀ᵐ ω ∂P, ∀ r : ℚ, ω ∈ F → ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < V ω →
      ∃ t, ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) ≤ min (physClockX x₀ s Wα ζα W GT t ω) (V ω) :=
    ae_all_iff.2 fun r => reach_min_physClockX hGT hs₀ hx₀ hver hGTae hF (Real.toNNReal r)
  filter_upwards [hall, hfin] with ω hω hf hωF hqV
  have hS : ((stgStartX x₀ s Wα ζα W GT V T ω : ℝ≥0) : ℝ≥0∞) = stgStartMX x₀ s Wα ζα W GT V T ω :=
    ENNReal.coe_toNNReal (hf hωF)
  rw [hS] at hqV
  have hSV : stgStartMX x₀ s Wα ζα W GT V T ω ≤ V ω := by
    by_contra hc
    rw [tsub_eq_zero_of_le (le_of_lt (lt_of_not_ge hc))] at hqV
    exact (not_lt_zero hqV).elim
  have h1 : stgStartMX x₀ s Wα ζα W GT V T ω + q < V ω :=
    calc stgStartMX x₀ s Wα ζα W GT V T ω + q <
          stgStartMX x₀ s Wα ζα W GT V T ω + (V ω - stgStartMX x₀ s Wα ζα W GT V T ω) :=
          ENNReal.add_lt_add_left (hf hωF) hqV
      _ = V ω := add_tsub_cancel_of_le hSV
  obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h1
  obtain ⟨t, ht⟩ := hω r hωF hr2
  refine ⟨t, ?_⟩
  have h2 : ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) ≤ min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω) :=
    ht.trans (monotone_min_physClockX hGT hs₀ hx₀ ω le_add_self)
  have h3 : stgStartMX x₀ s Wα ζα W GT V T ω + q ≤ min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω) :=
    hr1.le.trans h2
  unfold stgClockX
  exact ENNReal.le_sub_of_add_le_left (hf hωF) h3

end Filt

/-! ### The prefix record -/

section Prefix

variable {Ω : Type*} {x₀ : ℝ} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {GT : Set Ω} {V : Ω → ℝ≥0∞}

theorem stgPreRec_timeX (T : ℝ≥0) (R : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (stgPreRecX x₀ s Wα ζα W GT V T R ω).2.1.toNNReal = stgStartX x₀ s Wα ζα W GT V T ω := by
  change (min (stgStartX x₀ s Wα ζα W GT V T ω : ℝ≥0∞) ⊤).toNNReal = _
  rw [min_eq_left le_top, ENNReal.toNNReal_coe]

/-- **The prefix record's driver is the relative driver up to the stage start.** -/
theorem rdrv_stgPreRecX {T : ℝ≥0} {R : ℝ≥0 → Ω → ℝ} {ω : Ω} (hRc : Continuous fun u => R u ω) (hR0 : R 0 ω = 0)
    {u : ℝ≥0} (hu : u ≤ stgStartX x₀ s Wα ζα W GT V T ω) : rdrv (stgPreRecX x₀ s Wα ζα W GT V T R ω) u = R u ω := by
  have he := isRegularDriver_top hRc hR0
  have hlt : ((stgStartX x₀ s Wα ζα W GT V T ω : ℝ≥0) : ℝ≥0∞) < (fun u => R u ω, (⊤ : ℝ≥0∞)).2 := ENNReal.coe_lt_top
  have hg := Sec7.StripMark.isDrvGood_recOf_of_lt he hlt
  have hfin : min ((stgStartX x₀ s Wα ζα W GT V T ω : ℝ≥0) : ℝ≥0∞) (fun u => R u ω, (⊤ : ℝ≥0∞)).2 ≠ ⊤ := by
    rw [min_eq_left le_top]
    exact ENNReal.coe_ne_top
  have hsT : (u : ℝ) ≤ rtime (recOf ((stgStartX x₀ s Wα ζα W GT V T ω : ℝ≥0) : ℝ≥0∞) (fun u => R u ω, ⊤)) := by
    rw [rtime_recOf_coe]
    simp only [le_top, min_eq_left, ENNReal.toNNReal_coe, NNReal.coe_le_coe]
    exact hu
  have h := rdrv_recOf_eq he hg hfin hsT
  simpa only [stgPreRecX, Real.toNNReal_coe] using h

end Prefix

/-! ### Readability of the prefix record at the stage start -/

section Read

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {x₀ : ℝ} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  (hGT : ∀ ω ∈ GT, PhysGoodX x₀ s Wα ζα W γ α ω) (hs₀ : 0 < s) (hx₀ : 0 ≤ x₀)
  (hrec : Measurable (cfRec s Wα ζα)) (hWm : ∀ r, Measurable (W r))
  (hGTm : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT)

include hGT hs₀ hx₀ hGTm in
/-- **The prefix record is readable at the physical stage start.** -/
theorem measurable_stgPreRecX (hver : IsRelVersionXR x₀ s P Wα ζα W γ α R V) (T : ℝ≥0) :
    Measurable[physFilt hrec hWm P T] (stgPreRecX x₀ s Wα ζα W GT V T R) := by
  have hv := hver.1
  have hSM := measurable_stgStartMX hGT hs₀ hx₀ hrec hWm hGTm hver T
  have hS : Measurable[physFilt hrec hWm P T] (stgStartX x₀ s Wα ζα W GT V T) :=
    ENNReal.measurable_toNNReal.comp hSM
  have hRa : ∀ (d : ℝ≥0) {B : Set ℝ}, MeasurableSet B → MeasurableSet[physFilt hrec hWm P T]
      ({ω | (d : ℝ≥0∞) ≤ min (physClockX x₀ s Wα ζα W GT T ω) (V ω)} ∩ R d ⁻¹' B) := fun d _ hB =>
    measurableSet_le_min_inter_drvX hGT hs₀ hx₀ hrec hWm hGTm hver T le_rfl hB
  have hval : ∀ q : ℚ, Measurable[physFilt hrec hWm P T] fun ω =>
      R (min ((q : ℝ).toNNReal) (stgStartX x₀ s Wα ζα W GT V T ω)) ω := fun q =>
    Supp8.GB6LineL.measurable_apply_randTime (m := physFilt hrec hWm P T) hv.2.1 (measurable_const.min hS)
      (fun ω => (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans ENNReal.coe_toNNReal_le_self) hRa
  have e : stgPreRecX x₀ s Wα ζα W GT V T R = fun ω =>
      ((fun q : ℚ => R (min ((q : ℝ).toNNReal) (stgStartX x₀ s Wα ζα W GT V T ω)) ω),
        ((stgStartX x₀ s Wα ζα W GT V T ω : ℝ≥0) : ℝ≥0∞), false) := by
    funext ω
    simp only [stgPreRecX, recOf, readRec, retOf, min_eq_left (le_top : _ ≤ (⊤ : ℝ≥0∞)), ← ENNReal.coe_min,
      ENNReal.toNNReal_coe, top_le_iff, ENNReal.coe_ne_top, decide_false]
  rw [e]
  have hv' : Measurable[physFilt hrec hWm P T] fun ω => fun q : ℚ =>
      R (min ((q : ℝ).toNNReal) (stgStartX x₀ s Wα ζα W GT V T ω)) ω :=
    (@measurable_pi_iff Ω ℚ (fun _ => ℝ) (physFilt hrec hWm P T) _ _).2 hval
  exact hv'.prodMk ((measurable_coe_nnreal_ennreal.comp hS).prodMk measurable_const)

end Read

/-! ### The decoders are exact -/

/-- **The decoders of the augmented stage record are exact**: the counterflow record (when the stage record decodes to
it), the relative start, and a continuous prefix agreeing with the relative driver up to the start. -/
theorem augDec_specX {Ω : Type*} {x₀ : ℝ} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {GT : Set Ω}
    {V : Ω → ℝ≥0∞} {T : ℝ≥0} {R : ℝ≥0 → Ω → ℝ} {N : ℕ} {x : Ω → RecData} {rec : Ω → RecData} {ω : Ω}
    (hx : stgRecDec N (x ω) = rec ω) (hRc : Continuous fun u => R u ω) (hR0 : R 0 ω = 0) :
    augσ N (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R) ω) = rec ω ∧
      augA (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R) ω) = stgStartX x₀ s Wα ζα W GT V T ω ∧
      ∀ t ≤ augA (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R) ω),
        augPre (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R) ω) t = R t ω := by
  have hd : pairEnc.symm (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R) ω) =
      (x ω, stgPreRecX x₀ s Wα ζα W GT V T R ω) := pairEnc.symm_apply_apply _
  have hA : augA (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R) ω) = stgStartX x₀ s Wα ζα W GT V T ω := by
    rw [augA, hd]
    exact stgPreRec_timeX T R ω
  refine ⟨by rw [augσ, hd]; exact hx, hA, fun t ht => ?_⟩
  rw [augPre, hd]
  exact rdrv_stgPreRecX hRc hR0 (hA ▸ ht)


/-! ### The root-`x` safe events -/

section Safe1

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {x₀ : ℝ} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

/-- **The root-`x` safe events are physical** (GB6's `GB6LineL.hasGB6SafeMeas_of` at a root `x`). For a
closed `D`, `{a(t) < V, D ∩ K̃_{a(t)} = ∅}` agrees almost surely with an event of the record, the version's driver
frozen at `a(t)` (physical: `measurable_apply_randTime`, `RelSafe.measurableSet_le_min_inter_drv`) and `a(t)`
(physical: `RelSafe.measurable_min_physClock`): `V ≤ a(t)` iff the path rule of the frozen driver is `≤ a(t)`, and
the hull at `a(t)` only sees the frozen driver. -/
theorem hasGB6SafeMeas_ofX (hGT : ∀ ω ∈ GT, PhysGoodX x₀ s Wα ζα W γ α ω) (hs₀ : 0 < s) (hx₀ : 0 ≤ x₀)
    (hrec : Measurable (cfRec s Wα ζα))
    (hWm : ∀ r, Measurable (W r)) (hGTm : MeasurableSet GT)
    (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ cfRec s Wα ζα ω ∈ goodX x₀ s) (hver : IsRelVersionXR x₀ s P Wα ζα W γ α R V) :
    (∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[physFilt hrec hWm P t]
      {ω | min (physClockX x₀ s Wα ζα W GT t ω) (V ω) < V ω ∧ Disjoint (tsupport ψ)
        (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClockX x₀ s Wα ζα W GT t ω) (V ω)).toNNReal)}) ∧
    ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[physFilt hrec hWm P t]
      {ω | min (physClockX x₀ s Wα ζα W GT t ω) (V ω) < V ω ∧ Disjoint (Coupling.ballsK Fb)
        (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClockX x₀ s Wα ζα W GT t ω) (V ω)).toNNReal)} := by
  have hGTp : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT := measurableSet_goodSetX_physFilt hrec hWm hGTm hGTae
  suffices key : ∀ (D : Set ℂ), IsClosed D → ∀ t, MeasurableSet[physFilt hrec hWm P t]
      {ω | min (physClockX x₀ s Wα ζα W GT t ω) (V ω) < V ω ∧ Disjoint D
        (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClockX x₀ s Wα ζα W GT t ω) (V ω)).toNNReal)} by
    exact ⟨fun ψ t => key _ (isClosed_tsupport ψ) t, fun Fb t => key _ (Coupling.isCompact_ballsK Fb).isClosed t⟩
  intro D hD t
  have ha := measurable_min_physClockX hGT hs₀ hx₀ hrec hWm hGTp hver t
  obtain ⟨hv, ρ, hρm, hρ, hVρ⟩ := hver
  have ha' : Measurable[physFilt hrec hWm P t] fun ω => (min (physClockX x₀ s Wα ζα W GT t ω) (V ω)).toNNReal :=
    ENNReal.measurable_toNNReal.comp ha
  -- the version's driver frozen at the clock is physical
  have hY : ∀ u, Measurable[physFilt hrec hWm P t]
      (fun ω => R (min u (min (physClockX x₀ s Wα ζα W GT t ω) (V ω)).toNNReal) ω) := fun u =>
    measurable_apply_randTime (m := physFilt hrec hWm P t) hv.2.1
      (a := fun ω => min (physClockX x₀ s Wα ζα W GT t ω) (V ω)) (measurable_const.min ha')
      (fun ω => (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans ENNReal.coe_toNNReal_le_self)
      (fun d B hB => measurableSet_le_min_inter_drvX hGT hs₀ hx₀ hrec hWm hGTp ⟨hv, ρ, hρm, hρ, hVρ⟩ t le_rfl hB)
  have hYc : ∀ ω, Continuous fun u => R (min u (min (physClockX x₀ s Wα ζα W GT t ω) (V ω)).toNNReal) ω :=
    fun ω => (hv.2.1 ω).comp (continuous_id.min continuous_const)
  -- the disjointness event of the frozen driver is physical
  have hDis : MeasurableSet[physFilt hrec hWm P t] {ω | Disjoint D
      (fwdHull (drive 1 (fun u ω => R (min u (min (physClockX x₀ s Wα ζα W GT t ω) (V ω)).toNNReal) ω) ω)
        ((min (physClockX x₀ s Wα ζα W GT t ω) (V ω)).toNNReal : ℝ))} :=
    measurableSet_disjoint_fwdHull_rand hYc hY (measurable_coe_nnreal_real.comp ha') (fun ω => NNReal.coe_nonneg _) hD
  have hhull : ∀ ω, fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClockX x₀ s Wα ζα W GT t ω) (V ω)).toNNReal =
      fwdHull (drive 1 (fun u ω => R (min u (min (physClockX x₀ s Wα ζα W GT t ω) (V ω)).toNNReal) ω) ω)
        ((min (physClockX x₀ s Wα ζα W GT t ω) (V ω)).toNNReal : ℝ) := fun ω => by
    refine LocalExt.fwdHull_congr_of_continuousOn ((hv.2.1 ω).comp continuous_real_toNNReal).continuousOn
      (QuantumZipper.NonSwallow.continuous_drive_ns hYc 1 ω).continuousOn (NNReal.coe_nonneg _) (lt_add_one _) ?_
    intro r hr
    simp only [drive, Real.sqrt_one, one_mul]
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]
  -- the stop: `V ≤ a(t)` iff the path rule of the frozen driver is `≤ a(t)`
  have hrecp := measurable_rec_physFiltX (P := P) hrec hWm t
  have hpath : Measurable[physFilt hrec hWm P t]
      fun ω => fun u => R (min u (min (physClockX x₀ s Wα ζα W GT t ω) (V ω)).toNNReal) ω :=
    (@measurable_pi_iff Ω ℝ≥0 (fun _ => ℝ) (physFilt hrec hWm P t) _ _).2 hY
  have hStop : MeasurableSet[physFilt hrec hWm P t] {ω | ρ (cfRec s Wα ζα ω,
      fun u => R (min u (min (physClockX x₀ s Wα ζα W GT t ω) (V ω)).toNNReal) ω) ≤
        min (physClockX x₀ s Wα ζα W GT t ω) (V ω)} :=
    measurableSet_le (hρm.comp (hrecp.prodMk hpath)) ha
  have hiff : ∀ᵐ ω ∂P, (min (physClockX x₀ s Wα ζα W GT t ω) (V ω) < V ω ↔
      ¬ ρ (cfRec s Wα ζα ω, fun u => R (min u (min (physClockX x₀ s Wα ζα W GT t ω) (V ω)).toNNReal) ω) ≤
        min (physClockX x₀ s Wα ζα W GT t ω) (V ω)) := by
    filter_upwards [hVρ] with ω hV
    set a := min (physClockX x₀ s Wα ζα W GT t ω) (V ω) with hadef
    rw [← not_le]
    refine not_congr ?_
    by_cases htop : a = ⊤
    · rw [htop]
      simp only [le_top]
    · have hcoe : ((a.toNNReal : ℝ≥0) : ℝ≥0∞) = a := ENNReal.coe_toNNReal htop
      constructor
      · intro hVa
        have hag : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ρ (cfRec s Wα ζα ω, fun u => R u ω) →
            R u ω = R (min u a.toNNReal) ω := fun u hu => by
          have h1 : (u : ℝ≥0∞) ≤ ((a.toNNReal : ℝ≥0) : ℝ≥0∞) := by
            rw [hcoe]
            exact (hu.trans (le_of_eq hV.symm)).trans hVa
          rw [min_eq_left (ENNReal.coe_le_coe.1 h1)]
        rw [hρ _ _ _ hag, ← hV]
        exact hVa
      · intro hρa
        have hag : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ρ (cfRec s Wα ζα ω, fun u => R (min u a.toNNReal) ω) →
            R (min u a.toNNReal) ω = R u ω := fun u hu => by
          have h1 : (u : ℝ≥0∞) ≤ ((a.toNNReal : ℝ≥0) : ℝ≥0∞) := by
            rw [hcoe]
            exact hu.trans hρa
          rw [min_eq_left (ENNReal.coe_le_coe.1 h1)]
        rw [hV, hρ _ _ _ hag]
        exact hρa
  have hEm : MeasurableSet {ω | min (physClockX x₀ s Wα ζα W GT t ω) (V ω) < V ω ∧ Disjoint D
      (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClockX x₀ s Wα ζα W GT t ω) (V ω)).toNNReal)} := by
    have h1 : MeasurableSet {ω | min (physClockX x₀ s Wα ζα W GT t ω) (V ω) < V ω} :=
      measurableSet_lt (ha.mono ((physFilt hrec hWm P).le t) le_rfl) hv.2.2.2.2.1
    have h2 := (physFilt hrec hWm P).le t _ hDis
    simp only [← hhull] at h2
    exact h1.inter h2
  refine measurableSet_of_ae_eq ((physFilt hrec hWm P).le t) (nullSets_le_physFilt hrec hWm P t) hEm
    (hStop.compl.inter hDis) ?_
  filter_upwards [hiff] with ω hω
  show (ω ∈ {ω | _}) = (ω ∈ _ ∩ _)
  simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, hhull ω, hω]

end Safe1

/-! ### The stage safe events -/

section Safe

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {x₀ : ℝ} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  (hGT : ∀ ω ∈ GT, PhysGoodX x₀ s Wα ζα W γ α ω) (hs₀ : 0 < s) (hx₀ : 0 ≤ x₀)

omit mΩ in
include hGT hs₀ hx₀ in
/-- The stage start plus the frozen stage time is below the line clock at `T + t`. -/
theorem coe_stgStart_add_min_leX (T t u : ℝ≥0) (ω : Ω) :
    ((stgStartX x₀ s Wα ζα W GT V T ω + min u (stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal : ℝ≥0) : ℝ≥0∞) ≤
      min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω) := by
  have hle := stgStartM_leX hGT hs₀ hx₀ (V := V) T t ω
  set M := min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω) with hM
  by_cases htop : stgStartMX x₀ s Wα ζα W GT V T ω = ⊤
  · rw [htop, top_le_iff] at hle
    rw [hle]
    exact le_top
  · have hS : ((stgStartX x₀ s Wα ζα W GT V T ω : ℝ≥0) : ℝ≥0∞) = stgStartMX x₀ s Wα ζα W GT V T ω :=
      ENNReal.coe_toNNReal htop
    rw [ENNReal.coe_add, hS]
    by_cases hMt : M = ⊤
    · rw [hMt]
      exact le_top
    · have hc : ((stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal : ℝ≥0∞) = stgClockX x₀ s Wα ζα W GT V T t ω :=
        ENNReal.coe_toNNReal (ne_top_of_le_ne_top hMt tsub_le_self)
      calc stgStartMX x₀ s Wα ζα W GT V T ω + (min u (stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal : ℝ≥0)
          ≤ stgStartMX x₀ s Wα ζα W GT V T ω + (stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal := by
            gcongr
            exact_mod_cast min_le_right _ _
        _ = M := by rw [hc]; exact add_tsub_cancel_of_le hle

variable (hrec : Measurable (cfRec s Wα ζα)) (hWm : ∀ r, Measurable (W r))

include hGT hs₀ hx₀ in
/-- **The stage safe events are physical**, for every closed set. -/
theorem measurableSet_stgSafeX (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ cfRec s Wα ζα ω ∈ goodX x₀ s)
    (hver : IsRelVersionXR x₀ s P Wα ζα W γ α R V) (T t : ℝ≥0) {D : Set ℂ} (hD : IsClosed D) :
    MeasurableSet[shiftFilt (physFilt hrec hWm P) T t]
      {ω | stgClockX x₀ s Wα ζα W GT V T t ω < V ω - stgStartX x₀ s Wα ζα W GT V T ω ∧
        Disjoint D (fwdHull (fun r : ℝ => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) r.toNNReal)
          (stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal)} := by
  have hGTp : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT :=
    measurableSet_goodSetX_physFilt hrec hWm hGTm hGTae
  have hv := hver.1
  have hTt : physFilt hrec hWm P T ≤ physFilt hrec hWm P (T + t) := (physFilt hrec hWm P).mono le_self_add
  have hSM : Measurable[physFilt hrec hWm P (T + t)] (stgStartMX x₀ s Wα ζα W GT V T) :=
    (measurable_stgStartMX hGT hs₀ hx₀ hrec hWm hGTp hver T).mono hTt le_rfl
  have hS : Measurable[physFilt hrec hWm P (T + t)] (stgStartX x₀ s Wα ζα W GT V T) :=
    ENNReal.measurable_toNNReal.comp hSM
  have ha : Measurable[physFilt hrec hWm P (T + t)] fun ω => (stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal :=
    ENNReal.measurable_toNNReal.comp (measurable_stgClockX hGT hs₀ hx₀ hrec hWm hGTp hver T t)
  -- the first conjunct: GB6's line safe event with the empty set
  have hlt : MeasurableSet[physFilt hrec hWm P (T + t)]
      {ω | min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω) < V ω} := by
    have h := (hasGB6SafeMeas_ofX hGT hs₀ hx₀ hrec hWm hGTm hGTae hver).2 ∅ (T + t)
    have e : Coupling.ballsK (∅ : Finset (ℚ × ℚ × ℚ)) = ∅ := by
      simp only [Coupling.ballsK, Finset.notMem_empty, iUnion_of_empty, iUnion_empty]
    simp only [e, Set.empty_disjoint, and_true] at h
    exact h
  -- the frozen stage driver
  set Z : ℝ≥0 → Ω → ℝ := fun u ω =>
    R (stgStartX x₀ s Wα ζα W GT V T ω + min u (stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal) ω -
      R (stgStartX x₀ s Wα ζα W GT V T ω) ω with hZdef
  have hRa : ∀ (d : ℝ≥0) {B : Set ℝ}, MeasurableSet B → MeasurableSet[physFilt hrec hWm P (T + t)]
      ({ω | (d : ℝ≥0∞) ≤ min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω)} ∩ R d ⁻¹' B) := fun d _ hB =>
    measurableSet_le_min_inter_drvX hGT hs₀ hx₀ hrec hWm hGTp hver (T + t) le_rfl hB
  have hZm : ∀ u, Measurable[physFilt hrec hWm P (T + t)] (Z u) := fun u => by
    refine Measurable.sub ?_ ?_
    · exact Supp8.GB6LineL.measurable_apply_randTime (m := physFilt hrec hWm P (T + t)) hv.2.1
        (hS.add (measurable_const.min ha)) (fun ω => coe_stgStart_add_min_leX hGT hs₀ hx₀ T t u ω) hRa
    · refine Supp8.GB6LineL.measurable_apply_randTime (m := physFilt hrec hWm P (T + t)) hv.2.1 hS (fun ω => ?_) hRa
      exact (ENNReal.coe_le_coe.2 le_self_add).trans (coe_stgStart_add_min_leX hGT hs₀ hx₀ T t 0 ω)
  have hZc : ∀ ω, Continuous fun u => Z u ω := fun ω =>
    ((hv.2.1 ω).comp (continuous_const.add (continuous_id.min continuous_const))).sub continuous_const
  have hDis : MeasurableSet[physFilt hrec hWm P (T + t)]
      {ω | Disjoint D (fwdHull (drive 1 Z ω) ((stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal : ℝ))} :=
    Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand hZc hZm (measurable_coe_nnreal_real.comp ha)
      (fun ω => NNReal.coe_nonneg _) hD
  -- the stage hull is the hull of the frozen driver
  have hhull : ∀ ω, fwdHull (fun r : ℝ => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) r.toNNReal)
      ((stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal : ℝ) =
      fwdHull (drive 1 Z ω) ((stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal : ℝ) := fun ω => by
    refine LocalExt.fwdHull_congr_of_continuousOn
      ((continuous_stgDrv (hv.2.1 ω) _).comp continuous_real_toNNReal).continuousOn
      (QuantumZipper.NonSwallow.continuous_drive_ns hZc 1 ω).continuousOn (NNReal.coe_nonneg _) (lt_add_one _) ?_
    intro r hr
    simp only [drive, Real.sqrt_one, one_mul, hZdef, stgDrv]
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]
  -- the first conjunct
  have hfirst : ∀ ω, stgClockX x₀ s Wα ζα W GT V T t ω < V ω - stgStartX x₀ s Wα ζα W GT V T ω ↔
      (stgStartMX x₀ s Wα ζα W GT V T ω = ⊤ ∨ min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω) < V ω) := fun ω => by
    have hle := stgStartM_leX hGT hs₀ hx₀ (V := V) T t ω
    by_cases htop : stgStartMX x₀ s Wα ζα W GT V T ω = ⊤
    · have hV : V ω = ⊤ := top_le_iff.1 (htop ▸ min_le_right _ _)
      have hM : min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω) = ⊤ := top_le_iff.1 (htop ▸ hle)
      have h0 : stgClockX x₀ s Wα ζα W GT V T t ω = 0 := by
        unfold stgClockX
        rw [hM, htop, tsub_self]
      have h1 : V ω - stgStartX x₀ s Wα ζα W GT V T ω = ⊤ := by
        rw [hV]
        exact ENNReal.top_sub_coe
      rw [h0, h1]
      simp only [htop, true_or, iff_true]
      exact ENNReal.zero_lt_top
    · have hS : ((stgStartX x₀ s Wα ζα W GT V T ω : ℝ≥0) : ℝ≥0∞) = stgStartMX x₀ s Wα ζα W GT V T ω :=
        ENNReal.coe_toNNReal htop
      rw [hS]
      simp only [htop, false_or, stgClockX]
      constructor
      · intro h
        by_contra hc
        exact (not_le.2 h) (tsub_le_tsub_right (le_of_not_gt hc) _)
      · intro h
        exact ((ENNReal.cancel_of_ne htop).tsub_lt_tsub_iff_right hle).2 h
  have hTop : MeasurableSet[physFilt hrec hWm P (T + t)] {ω | stgStartMX x₀ s Wα ζα W GT V T ω = ⊤} :=
    hSM (measurableSet_singleton ⊤)
  have e : {ω | stgClockX x₀ s Wα ζα W GT V T t ω < V ω - stgStartX x₀ s Wα ζα W GT V T ω ∧
        Disjoint D (fwdHull (fun r : ℝ => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) r.toNNReal)
          (stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal)} =
      ({ω | stgStartMX x₀ s Wα ζα W GT V T ω = ⊤} ∪ {ω | min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω) < V ω}) ∩
        {ω | Disjoint D (fwdHull (drive 1 Z ω) ((stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal : ℝ))} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_union, hfirst, hhull]
  rw [shiftFilt_apply, e]
  exact (hTop.union hlt).inter hDis

include hGT hs₀ hx₀ in
/-- **The stage safe events `hSψ`, `hSb`** of `GW2Rd.hasRelSafe_of_lines_rec`. -/
theorem hasStgSafeMeasX (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ cfRec s Wα ζα ω ∈ goodX x₀ s)
    (hver : IsRelVersionXR x₀ s P Wα ζα W γ α R V) (T : ℝ≥0) :
    (∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[shiftFilt (physFilt hrec hWm P) T t]
      {ω | stgClockX x₀ s Wα ζα W GT V T t ω < V ω - stgStartX x₀ s Wα ζα W GT V T ω ∧ Disjoint (tsupport ψ)
        (fwdHull (fun r : ℝ => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) r.toNNReal)
          (stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal)}) ∧
    ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[shiftFilt (physFilt hrec hWm P) T t]
      {ω | stgClockX x₀ s Wα ζα W GT V T t ω < V ω - stgStartX x₀ s Wα ζα W GT V T ω ∧ Disjoint (Coupling.ballsK Fb)
        (fwdHull (fun r : ℝ => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) r.toNNReal)
          (stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal)} :=
  ⟨fun ψ t => measurableSet_stgSafeX hGT hs₀ hx₀ hrec hWm hGTm hGTae hver T t (isClosed_tsupport ψ),
    fun Fb t => measurableSet_stgSafeX hGT hs₀ hx₀ hrec hWm hGTm hGTae hver T t (Coupling.isCompact_ballsK Fb).isClosed⟩

end Safe


end InteractingSLE.Theorem14.GW2Rz
