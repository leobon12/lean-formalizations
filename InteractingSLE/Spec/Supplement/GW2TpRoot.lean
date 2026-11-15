/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TpBack
import InteractingSLE.Spec.Supplement.GW2RvPkg

/-!
# The launch gauge at every root, part 4: the death family at every root `x`

Packet PROVE-GW2-RELDET (round 27). RELDET's death family (`exists_schedVersionsA_strict_death_all`, root `0`) at
EVERY root `x = rootPt r.1 ≥ 0`, on ROOTX's root-`x` versions (`GW2Rz.IsRelVersionXA`, good records `GW2Rz.goodX`):

* `launchGaugeX`: the launch gauge (`launchGaugeC`, strictly-left evaluation) read through the root-`x` read-back
  `physicalTraceX − x`; `launchLifeX`: its life along the root-`x` clock and contact;
* **`ae_launchGaugeX_coord`**: along EVERY root-`x` coordinate process (`GW2Rz.CoordX`) the gauge is positive before
  its life, continuous, and zero at it (`ae_readbackX` + `launchGaugeC_sample`) — the cap-gauge hypothesis of ROOTX's
  `GW2Rv.exists_versionsXA_of_capGauge_strict`;
* `exists_versionsXA_launchGauge`, **`exists_schedVersionsXA_strict_launch`**: the capped root-`x` family;
* `deathClockX`: the root-`x` clock of the candidate's death `T + ζ` (before the cap and the root-`x` contact; `⊤`
  otherwise); **`ae_schedLaunchLifeX_eq`** (positive lifetime), **`ae_schedLaunchLifeX_eq_top_of_zero`**;
* **`exists_schedVersionsXA_strict_death_all`**: the root-`x` death family with exhaustion at every lifetime;
* **`ae_histCapGain_le_deathClockX`**: the history's capacity plus the gain is at most the death clock (the buffer is
  at most the lifetime); **`ae_exhausts_of_deathX`**: so exhaustion below the death clock gives ROOTX's `exhausts`;
* **`schedVerXDeath`**: the death family as a `GW2Rv.SchedVerX` (ROOTX's canonical family off good roots and
  non-time-ordered histories), with `schedVerXDeath_lt_deathClockX` and `schedVerXDeath_exhausts_death`;
  `schedVerXDeathFamily`: the families for ROOTX's `GW2Rv.RootPairInputsX`;
* **`ae_srecX_mem_launchBadRec_iff`**: decision D26 (A′) at every root: the root-`x` stage record of every instance
  identifies the zero-lifetime candidate (`launchBadRec`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 Supp8.GB6.CoordB Supp8.GB6.ReadD Supp8.GB6.SourceC
  Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version GW2TipSystem GW2Rz

/-! ### The launch gauge read at a root `x` -/

section Gauge

/-- The root-`x` read-back re-centred at the root. -/
def launchReadX (x : ℝ) (s u : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) : ℂ := physicalTraceX x s u p - x

theorem measurable_launchReadX (x : ℝ) (s u : ℝ≥0) : Measurable (launchReadX x s u) :=
  (measurable_physicalTraceX x s u).sub_const _

theorem launchReadX_congr (x : ℝ) (s : ℝ≥0) : ∀ (u : ℝ≥0) (r : RecData) (w w' : ℝ≥0 → ℝ),
    (∀ v ≤ u, w v = w' v) → launchReadX x s u (r, w) = launchReadX x s u (r, w') := fun u r _ _ h => by
  unfold launchReadX
  rw [physicalTraceX_congr x s u r h]

variable (κ θ : ℝ) (B : (ℝ≥0 → ℝ) → BoundaryWord) (T cap : ℝ≥0) (x : ℝ) (s : ℝ≥0)

/-- **The launch gauge at the root `x`.** -/
abbrev launchGaugeX : GaugeReadout := launchGaugeC κ θ B T cap (launchReadX x s)

/-- The life of the launch gauge along the root-`x` clock. -/
abbrev launchLifeX {Ω : Type*} (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (w : ℝ≥0 → Ω → ℝ) (γ α : Ω → ℝ≥0 → ℂ)
    (ω : Ω) : ℝ≥0∞ :=
  launchLife κ θ B T cap (w · ω) (fun t => clockX x s W' ζ' w t ω) (contactX x s γ α ω)

end Gauge

/-! ### Along every root-`x` coordinate process -/

section Ae

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κc θc : ℝ} {bc : ℝ → ℝ} {Jc : Finset ℝ} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ} {w : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ}

omit [IsProbabilityMeasure P] in
/-- **The root-`x` clock on the good records**: `0` at `0`, strictly increasing and continuous before the contact. -/
theorem ae_clockX_props (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (W' · ω) (ζ' ω) (α ω))
    (hcf : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ Continuous (W' · ω) ∧ W' 0 ω = 0)
    (hwc : ∀ ω, Continuous (w · ω)) (hw0 : ∀ ω, w 0 ω = 0)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (w · ω) ⊤ (γ ω)) {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) :
    ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s →
      clockX x s W' ζ' w 0 ω = 0 ∧
      StrictMonoOn (fun t => clockX x s W' ζ' w t ω) {t | (t : ℝ≥0∞) < contactX x s γ α ω} ∧
      ContinuousOn (fun t => clockX x s W' ζ' w t ω) {t | (t : ℝ≥0∞) < contactX x s γ α ω} := by
  filter_upwards [hα, hcf, hγ] with ω hαω hcfω hγω hm
  obtain ⟨hζ, hWc, hW0⟩ := hcfω
  have hαt : IsGeneratingTrace (W' · ω) ⊤ (α ω) := by rw [← hζ]; exact hαω
  have hAe : ∀ v ≤ s, recordTrace v (cfRec s W' ζ' ω) = α ω v := fun v hv =>
    GaugeE.recordTrace_eq (Wα := W') (ζα := ζ') s hW0 (by rw [hζ]; exact hWc.continuousOn)
      (by rw [hζ]; exact hαt) (by rw [hζ]; exact ENNReal.coe_lt_top) hv
  have hαc : Continuous (α ω) :=
    continuousOn_univ.1 (hαt.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hA : ContinuousOn (fun v => recordTrace v (cfRec s W' ζ' ω)) (Iic s) :=
    hαc.continuousOn.congr fun v hv => hAe v hv
  have harc : ∀ u ∈ Icc 0 s, x * ‖α ω u‖ < 1 := by
    intro u hu
    have h1 := (mem_arcSet_iff hA).1 hm.2 u hu
    rwa [hAe u hu.2] at h1
  exact clock_props W' ζ' ω hαt hWc hW0 hζ hs hx harc (hwc ω) (hw0 ω) hγω

/-- **The root-`x` launch gauge along every root-`x` coordinate process** (the cap-gauge hypothesis of
`GW2Rv.exists_versionsXA_of_capGauge_strict`): almost surely on the good records, the life is positive, the gauge is
continuous before the coordinate life, positive before the gauge's life and zero at it. -/
theorem ae_launchGaugeX_coord (hF : IsFlowLineDriver κc bc Jc θc P h W' ζ')
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (W' · ω) (ζ' ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζ' ω → α' v ≠ 0)
    (hcf : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ Continuous (W' · ω) ∧ W' 0 ω = 0)
    (hwc : ∀ ω, Continuous (w · ω)) (hw0 : ∀ ω, w 0 ω = 0)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (w · ω) ⊤ (γ ω)) {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x)
    {κ θ : ℝ} {B : (ℝ≥0 → ℝ) → BoundaryWord} {T cap : ℝ≥0}
    (hBc : ∀ ω, ∀ v : ℝ≥0 → ℝ, (∀ u ≤ T, v u = w u ω) → B v = B (w · ω))
    {D : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞} (hC : CoordX x s P W' ζ' w γ α D L) :
    ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → 0 < launchLifeX κ θ B T cap x s W' ζ' w γ α ω ∧
      ContinuousOn (fun t => launchGaugeX κ θ B T cap x s t (cfRec s W' ζ' ω, fun u => D u ω))
        {t | (t : ℝ≥0∞) < L ω} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) < launchLifeX κ θ B T cap x s W' ζ' w γ α ω →
        0 < launchGaugeX κ θ B T cap x s t (cfRec s W' ζ' ω, fun u => D u ω)) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) = launchLifeX κ θ B T cap x s W' ζ' w γ α ω →
        launchGaugeX κ θ B T cap x s t (cfRec s W' ζ' ω, fun u => D u ω) = 0 := by
  filter_upwards [ae_readbackX hF hα hNR hcf hwc hw0 hγ hs hx hC, hγ] with ω hrb hγω hm
  obtain ⟨h0, hmono, -, haL, hread, hback, hXc⟩ := hrb hm
  refine launchGaugeC_sample (launchReadX_congr x s) (hBc ω) hγω (hwc ω) (hw0 ω) h0 hmono haL hback
    (fun t ht => ?_) ?_
  · unfold launchReadX
    rw [hread t ht, add_sub_cancel_left]
  · change ContinuousOn (fun u => physicalTraceX x s u (cfRec s W' ζ' ω, fun v => D v ω) - (x : ℂ)) _
    exact hXc.sub continuousOn_const

/-- **The capped root-`x` family below the launch gauge's life** (any root-`x` instance). -/
theorem exists_versionsXA_launchGauge (hF : IsFlowLineDriver κc bc Jc θc P h W' ζ')
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (W' · ω) (ζ' ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζ' ω → α' v ≠ 0)
    (hcf : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ Continuous (W' · ω) ∧ W' 0 ω = 0)
    (hwm : ∀ t, Measurable (w t)) (hwc : ∀ ω, Continuous (w · ω)) (hw0 : ∀ ω, w 0 ω = 0)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (w · ω) ⊤ (γ ω) ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x)
    {κ θ : ℝ} {B : (ℝ≥0 → ℝ) → BoundaryWord} (hB : Measurable B) {T cap : ℝ≥0}
    (hBc : ∀ ω, ∀ v : ℝ≥0 → ℝ, (∀ u ≤ T, v u = w u ω) → B v = B (w · ω)) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, IsRelVersionXA x s P W' ζ' w γ α (R n) (V n)) ∧ (∀ n ω, V n ω ≤ V (n + 1) ω) ∧
      (∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → ∀ n, V n ω < V (n + 1) ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      (∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → ∀ n, V n ω < launchLifeX κ θ B T cap x s W' ζ' w γ α ω) ∧
      ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω →
        ENNReal.ofReal (clockX x s W' ζ' w t ω) < launchLifeX κ θ B T cap x s W' ζ' w γ α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX x s W' ζ' w t ω) < V n ω := by
  obtain ⟨R₀, V₀, hRV₀, hst₀, hlt₀, hex₀⟩ := GW2Rv.exists_versionsXA_of_capGauge_strict hF hα hNR hcf hwm hwc hw0
    hγ hs hx (Gζ := launchGaugeX κ θ B T cap x s) (measurable_launchGaugeC hB (measurable_launchReadX x s))
    isCausal_launchGaugeC launchGaugeC_nonneg (Lζ := launchLifeX κ θ B T cap x s W' ζ' w γ α)
    fun _ _ hC => ae_launchGaugeX_coord hF hα hNR hcf hwc hw0 (hγ.mono fun _ h => h.1) hs hx hBc hC
  obtain ⟨R, V, hRV, hmono, hstrict, hle, hfin, hex⟩ := GW2Rv.exists_finite_family_strictX hRV₀
    (fun ω => (hst₀ ω).monotone) (ae_of_all _ fun ω _ => hst₀ ω) (measurable_recOf_cfE hF s).2
  refine ⟨R, V, hRV, fun n ω => hmono ω (Nat.le_succ n), hstrict.mono fun ω hω hm n => hω hm (Nat.lt_succ_self n),
    hfin, ?_, ?_⟩
  · filter_upwards [hlt₀] with ω hω hm n
    exact (hle n ω).trans_lt (hω hm n)
  · filter_upwards [hex₀] with ω hω hm t ht htl
    obtain ⟨m, hm'⟩ := hω hm t ht htl
    exact hex ω _ ENNReal.ofReal_ne_top m hm'

end Ae

/-! ### The schedule instance at the root point -/

section Defs

open GW2TipSystem.RootC24 GW2TipSystem.RootJ31

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- The life of the schedule instance's launch gauge at the root point. -/
abbrev schedLaunchLifeX (ω : Ω) : ℝ≥0∞ :=
  launchLifeX c.κ (candAngle c r l a) (launchWordOf c r l a) (historyTime c r l) (candidateCap c r a) (rootPt r.1)
    c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω

open scoped Classical in
/-- **The root-`x` clock of the candidate's death** `T + ζ`, when the death is before the cap and before the
root-`x` contact; `⊤` otherwise. -/
def deathClockX (ω : Ω) : ℝ≥0∞ :=
  if candLife c r l a ω ≤ candidateCap c r a ∧ ((historyTime c r l + (candLife c r l a ω).toNNReal : ℝ≥0) : ℝ≥0∞) <
      contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω then
    ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
      (historyTime c r l + (candLife c r l a ω).toNNReal) ω)
  else ⊤

end Defs

section Sched

open GW2TipSystem.RootC24 GW2TipSystem.RootJ31 Sec5.Prop513Schedule

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

include h13 in
/-- **The schedule instance's root-`x` versions capped strictly before the launch gauge's life**: finite, monotone,
strictly increasing on the good records, below the life on the good records, exhausting every root-`x` clock value
below the life before the root-`x` contact. -/
theorem exists_schedVersionsXA_strict_launch (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (R n) (V n)) ∧
      (∀ n ω, V n ω ≤ V (n + 1) ω) ∧
      (∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → ∀ n, V n ω < V (n + 1) ω) ∧
      (∀ n ω, V n ω ≠ ⊤) ∧
      (∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → ∀ n, V n ω < schedLaunchLifeX c r l a ω) ∧
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < schedLaunchLifeX c r l a ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < V n ω := by
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  have hγ : ∀ᵐ ω ∂c.P, IsGeneratingTrace (schedW c r l a · ω) ⊤ (schedTr c r l a ω) ∧
      Tendsto (fun t => ‖schedTr c r l a ω t‖) atTop atTop :=
    (ae_schedW_regular h13 c r l a).mono fun _ h => ⟨h.2.2.1, h.2.2.2⟩
  exact exists_versionsXA_launchGauge hfl hα (ae_source_noReturn h13 c) (GW2Rv.ae_source_cf_complete h13 c)
    (measurable_schedW c r l a) (continuous_schedW c r l a) (schedW_zero c r l a) hγ hs hx
    (measurable_launchWordOf c r l a) fun _ _ h => launchWordOf_congr c r l a h

include h13 in
/-- **At the root point the launch gauge's life is the candidate's death clock**, almost surely, on the history's
success (time-ordered history) at a positive lifetime. -/
theorem ae_schedLaunchLifeX_eq (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω ∂c.P, oldSuccess c r l ω → 0 < candLife c r l a ω →
      schedLaunchLifeX c r l a ω = deathClockX c r l a ω := by
  classical
  filter_upwards [ae_candDist h13 c r l a hord] with ω hω hold hζ0
  obtain ⟨hpos, hzero⟩ := hω hold hζ0
  set f := launchDist c.κ (candAngle c r l a) (launchWordOf c r l a) (historyTime c r l)
    (fun t => schedW c r l a t ω) with hfdef
  set cap := candidateCap c r a with hcap
  set T := historyTime c r l with hT
  set Tc := contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω with hTc
  set Z : Set ℝ≥0 := {σ | σ ≤ cap ∧ f σ = 0} with hZ
  have hd0 : launchStart c.κ (candAngle c r l a) (launchWordOf c r l a) (fun t => schedW c r l a t ω) ≠ 0 := by
    rw [← launchDist_zero (T := T)]
    exact (hpos 0 zero_le (by simpa using hζ0)).ne'
  have hlife : schedLaunchLifeX c r l a ω =
      if launchStart c.κ (candAngle c r l a) (launchWordOf c r l a) (fun t => schedW c r l a t ω) ≠ 0 ∧
        ∃ σ : ℝ≥0, σ ≤ cap ∧ f σ = 0 ∧ ((T + σ : ℝ≥0) : ℝ≥0∞) < Tc then
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (T + sInf Z) ω) else ⊤ := rfl
  rw [hlife, deathClockX]
  by_cases hζc : candLife c r l a ω ≤ cap
  · have hne : candLife c r l a ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hζc
    set ζ := (candLife c r l a ω).toNNReal with hζ
    have hζe : (ζ : ℝ≥0∞) = candLife c r l a ω := ENNReal.coe_toNNReal hne
    have hζcap : ζ ≤ cap := by rw [← ENNReal.coe_le_coe, hζe]; exact hζc
    have hmem : ζ ∈ Z := ⟨hζcap, hzero hζc⟩
    have hmin : ∀ σ ∈ Z, ζ ≤ σ := by
      intro σ hσ
      by_contra hlt
      have hσζ : (σ : ℝ≥0∞) < candLife c r l a ω := by rw [← hζe]; exact ENNReal.coe_lt_coe.2 (not_le.1 hlt)
      exact (hpos σ hσ.1 hσζ).ne' hσ.2
    have hinf : sInf Z = ζ :=
      le_antisymm (csInf_le (OrderBot.bddBelow Z) hmem) (le_csInf ⟨ζ, hmem⟩ hmin)
    have hiff : (∃ σ : ℝ≥0, σ ≤ cap ∧ f σ = 0 ∧ ((T + σ : ℝ≥0) : ℝ≥0∞) < Tc) ↔
        ((T + ζ : ℝ≥0) : ℝ≥0∞) < Tc := by
      constructor
      · rintro ⟨σ, hσc, hσf, hσT⟩
        exact (ENNReal.coe_le_coe.2 (add_le_add_right (hmin σ ⟨hσc, hσf⟩) T)).trans_lt hσT
      · intro h
        exact ⟨ζ, hζcap, hmem.2, h⟩
    by_cases hTζ : ((T + ζ : ℝ≥0) : ℝ≥0∞) < Tc
    · have hc1 : launchStart c.κ (candAngle c r l a) (launchWordOf c r l a) (fun t => schedW c r l a t ω) ≠ 0 ∧
          ∃ σ : ℝ≥0, σ ≤ cap ∧ f σ = 0 ∧ ((T + σ : ℝ≥0) : ℝ≥0∞) < Tc := ⟨hd0, hiff.2 hTζ⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hc1), ite_eq_left_of_eq_true _ _ (eq_true ⟨hζc, hTζ⟩), hinf]
    · have hc1 : ¬ (launchStart c.κ (candAngle c r l a) (launchWordOf c r l a) (fun t => schedW c r l a t ω) ≠ 0 ∧
          ∃ σ : ℝ≥0, σ ≤ cap ∧ f σ = 0 ∧ ((T + σ : ℝ≥0) : ℝ≥0∞) < Tc) := fun h => hTζ (hiff.1 h.2)
      have hc2 : ¬ (candLife c r l a ω ≤ cap ∧ ((T + ζ : ℝ≥0) : ℝ≥0∞) < Tc) := fun h => hTζ h.2
      rw [ite_eq_right_of_eq_false _ _ (eq_false hc1), ite_eq_right_of_eq_false _ _ (eq_false hc2)]
  · have hc1 : ¬ (launchStart c.κ (candAngle c r l a) (launchWordOf c r l a) (fun t => schedW c r l a t ω) ≠ 0 ∧
        ∃ σ : ℝ≥0, σ ≤ cap ∧ f σ = 0 ∧ ((T + σ : ℝ≥0) : ℝ≥0∞) < Tc) := by
      rintro ⟨-, σ, hσc, hσf, -⟩
      have hσζ : (σ : ℝ≥0∞) < candLife c r l a ω :=
        (ENNReal.coe_le_coe.2 hσc).trans_lt (lt_of_not_ge hζc)
      exact (hpos σ hσc hσζ).ne' hσf
    have hc2 : ¬ (candLife c r l a ω ≤ cap ∧
        ((T + (candLife c r l a ω).toNNReal : ℝ≥0) : ℝ≥0∞) < Tc) := fun h => hζc h.1
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc1), ite_eq_right_of_eq_false _ _ (eq_false hc2)]

include h13 in
/-- **At a zero lifetime the root-`x` launch gauge never dies**, almost surely on the history's success. -/
theorem ae_schedLaunchLifeX_eq_top_of_zero (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω ∂c.P, oldSuccess c r l ω → candLife c r l a ω = 0 → schedLaunchLifeX c r l a ω = ⊤ := by
  classical
  filter_upwards [ae_launchStart_eq_zero_iff h13 c r l a hord] with ω hω hold hz
  have h0 := (hω hold).2 hz
  unfold schedLaunchLifeX launchLifeX launchLife
  exact ite_eq_right_of_eq_false _ _ (eq_false fun h => h.1 h0)

include h13 in
/-- **RELDET's death family at the root point, with exhaustion at every lifetime**: root-`x` versions, finite,
monotone, strictly increasing on the good records; at a positive lifetime the caps are strictly below the root-`x`
death clock; on the history's success (at every lifetime, including `0`) every root-`x` clock value before the
root-`x` contact and below the death clock is eventually below `V n`. -/
theorem exists_schedVersionsXA_strict_death_all (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (R n) (V n)) ∧
      (∀ n ω, V n ω ≤ V (n + 1) ω) ∧
      (∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → ∀ n, V n ω < V (n + 1) ω) ∧
      (∀ n ω, V n ω ≠ ⊤) ∧
      (∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
        0 < candLife c r l a ω → ∀ n, V n ω < deathClockX c r l a ω) ∧
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < deathClockX c r l a ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < V n ω := by
  obtain ⟨R, V, hRV, hmono, hstrict, hfin, hlt, hex⟩ := exists_schedVersionsXA_strict_launch h13 c r l a hx hs
  refine ⟨R, V, hRV, hmono, hstrict, hfin, ?_, ?_⟩
  · filter_upwards [hlt, ae_schedLaunchLifeX_eq h13 c r l a hord] with ω h1 h2 hrec hold hζ0 n
    rw [← h2 hold hζ0]
    exact h1 hrec n
  · filter_upwards [hex, ae_schedLaunchLifeX_eq h13 c r l a hord,
      ae_schedLaunchLifeX_eq_top_of_zero h13 c r l a hord] with ω h1 h2 h3 hrec hold t ht htl
    refine h1 hrec t ht ?_
    rcases eq_zero_or_pos (candLife c r l a ω) with hz | hpos
    · rw [h3 hold hz]
      exact ENNReal.ofReal_lt_top
    · rw [h2 hold hpos]
      exact htl

include h13 in
/-- The root-`x` clock of the schedule instance on the good records. -/
theorem ae_schedClockX_props (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) :
    ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) 0 ω = 0 ∧
      StrictMonoOn (fun t => clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω)
        {t | (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω} ∧
      ContinuousOn (fun t => clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω)
        {t | (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω} := by
  obtain ⟨_, _, _, -, hα⟩ := source_counterflow c
  exact ae_clockX_props hα (GW2Rv.ae_source_cf_complete h13 c) (continuous_schedW c r l a)
    (schedW_zero c r l a) ((ae_schedW_regular h13 c r l a).mono fun _ h => h.2.2.1) hs hx

include h13 in
/-- **The history's capacity plus the gain is at most the root-`x` death clock** (the buffer is at most the
candidate's lifetime), almost surely at a positive gain. -/
theorem ae_histCapGain_le_deathClockX (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) :
    ∀ᵐ ξ ∂c.P, 0 < GW2Sdg.rootGain c r l a ξ →
      ((GW2Sdg.rootHistCap c r l a ξ + GW2Sdg.rootGain c r l a ξ : ℝ≥0) : ℝ≥0∞) ≤ deathClockX c r l a ξ := by
  filter_upwards [GW2Rv.ae_histCap_add_gainX h13 c r l a, ae_exactPair_rootX h13 c r l a,
    ae_schedClockX_props h13 c r l a hx hs] with ξ hsum hpair hclk hpos
  obtain ⟨hgx, hTc, -⟩ := hpair (GW2Rv.live_of_gain_pos c r l a hpos)
  obtain ⟨-, hmono, -⟩ := hclk hgx
  rw [hsum hpos, deathClockX]
  split_ifs with hd
  · obtain ⟨hζc, hTζ⟩ := hd
    have hne : candLife c r l a ξ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hζc
    have hb : sourceBuffer c r l a ξ ≤ (candLife c r l a ξ).toNNReal := by
      have h1 : (sourceBuffer c r l a ξ : ℝ≥0∞) ≤ candLife c r l a ξ := sourceBuffer_coe_le_next_lifetime c r l a ξ
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hne]
      exact h1
    exact ENNReal.ofReal_le_ofReal (hmono.monotoneOn hTc hTζ (add_le_add_right hb _))
  · exact le_top

include h13 in
/-- **Exhaustion below the root-`x` death clock gives ROOTX's exhaustion of the history's capacity plus the gain**
(the `exhausts` field of `GW2Rv.SchedVerX`). -/
theorem ae_exhausts_of_deathX (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) {V : ℕ → Ω → ℝ≥0∞}
    (hev : ∀ᵐ ξ ∂c.P, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ξ → ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < deathClockX c r l a ξ →
      ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < V n ξ) :
    ∀ᵐ ξ ∂c.P, ∀ u : ℝ≥0, u < GW2Sdg.rootGain c r l a ξ →
      ∀ᶠ n in atTop, ((GW2Sdg.rootHistCap c r l a ξ + u : ℝ≥0) : ℝ≥0∞) < V n ξ := by
  filter_upwards [hev, ae_exactPair_rootX h13 c r l a, GW2Rv.ae_histCap_add_gainX h13 c r l a,
    ae_histCapGain_le_deathClockX h13 c r l a hx hs, ae_schedClockX_props h13 c r l a hx hs]
    with ξ hevξ hpair hsum hle hclk u hu
  have hpos : 0 < GW2Sdg.rootGain c r l a ξ := lt_of_le_of_lt zero_le hu
  have hlive := GW2Rv.live_of_gain_pos c r l a hpos
  obtain ⟨hgx, hTc, -⟩ := hpair hlive
  obtain ⟨-, hold, -, -⟩ := RootK32.sourceSample_live_geometry c r l a ξ hlive
  obtain ⟨h0, hmono, hcont⟩ := hclk hgx
  set K := GW2Sdg.rootHistCap c r l a ξ with hK
  set G := GW2Sdg.rootGain c r l a ξ with hG
  set v := historyTime c r l + sourceBuffer c r l a ξ with hv
  set a' : ℝ≥0 → ℝ := fun t => clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ with ha'
  have h0T : ((0 : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ :=
    (ENNReal.coe_le_coe.2 (zero_le : (0 : ℝ≥0) ≤ v)).trans_lt hTc
  have hv0 : 0 ≤ a' v := by
    have h := hmono.monotoneOn h0T hTc (zero_le : (0 : ℝ≥0) ≤ v)
    simp only [ha'] at h ⊢
    rw [h0] at h
    exact h
  have hKG : ((K + G : ℝ≥0) : ℝ) = a' v := by
    have h2 := congrArg ENNReal.toReal (hsum hpos)
    rwa [ENNReal.coe_toReal, ENNReal.toReal_ofReal hv0] at h2
  have hu' : ((K + u : ℝ≥0) : ℝ) ≤ a' v := by
    rw [← hKG]
    exact_mod_cast add_le_add_right hu.le K
  obtain ⟨t, ht, hat⟩ := GaugeE.exists_clock_eq (a := a')
    (hcont.mono fun q hq => (ENNReal.coe_le_coe.2 hq.2).trans_lt hTc) h0 hu'
  have htc : (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ :=
    (ENNReal.coe_le_coe.2 ht.2).trans_lt hTc
  have hofr : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) = ((K + u : ℝ≥0) : ℝ≥0∞) := by
    rw [show clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ = ((K + u : ℝ≥0) : ℝ) from hat,
      ENNReal.ofReal_coe_nnreal]
  have hclt : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < deathClockX c r l a ξ := by
    rw [hofr]
    exact (ENNReal.coe_lt_coe.2 (add_lt_add_right hu K)).trans_le (hle hpos)
  filter_upwards [hevξ hgx hold t htc hclt] with n hn
  rwa [hofr] at hn

open Classical in
/-- **The root-`x` death family as a version family at a root** (`GW2Rv.SchedVerX`): at a nonnegative root point,
a positive retained time and a time-ordered history, the death family of `exists_schedVersionsXA_strict_death_all`
(chosen); ROOTX's canonical family otherwise. -/
def schedVerXDeath : GW2Rv.SchedVerX c r l a :=
  if hg : 0 ≤ rootPt r.1 ∧ 0 < c.s ∧ TimeOrdered 0 (historyProgram c r l) then
    { R := (exists_schedVersionsXA_strict_death_all h13 c r l a hg.1 hg.2.1 hg.2.2).choose
      V := (exists_schedVersionsXA_strict_death_all h13 c r l a hg.1 hg.2.1 hg.2.2).choose_spec.choose
      isA := fun _ => (exists_schedVersionsXA_strict_death_all h13 c r l a hg.1 hg.2.1 hg.2.2).choose_spec.choose_spec.1
      mono := (exists_schedVersionsXA_strict_death_all h13 c r l a hg.1 hg.2.1 hg.2.2).choose_spec.choose_spec.2.1
      fin := (exists_schedVersionsXA_strict_death_all h13 c r l a hg.1 hg.2.1 hg.2.2).choose_spec.choose_spec.2.2.2.1
      strict := fun _ =>
        (exists_schedVersionsXA_strict_death_all h13 c r l a hg.1 hg.2.1 hg.2.2).choose_spec.choose_spec.2.2.1
      exhausts := fun _ => ae_exhausts_of_deathX h13 c r l a hg.1 hg.2.1
        (exists_schedVersionsXA_strict_death_all h13 c r l a hg.1 hg.2.1 hg.2.2).choose_spec.choose_spec.2.2.2.2.2 }
  else GW2Rv.schedVerXCanon h13 c r l a

/-- **The death family's caps are strictly below the root-`x` death clock** (positive lifetime, history's success,
good records). -/
theorem schedVerXDeath_lt_deathClockX (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω → 0 < candLife c r l a ω →
      ∀ n, (schedVerXDeath h13 c r l a).V n ω < deathClockX c r l a ω := by
  have hg : 0 ≤ rootPt r.1 ∧ 0 < c.s ∧ TimeOrdered 0 (historyProgram c r l) := ⟨hx, hs, hord⟩
  unfold schedVerXDeath
  rw [dite_eq_left hg]
  exact (exists_schedVersionsXA_strict_death_all h13 c r l a hg.1 hg.2.1 hg.2.2).choose_spec.choose_spec.2.2.2.2.1

/-- **The death family exhausts the root-`x` clock below the death clock** (history's success, good records, every
lifetime). -/
theorem schedVerXDeath_exhausts_death (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω → ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < deathClockX c r l a ω →
      ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) <
        (schedVerXDeath h13 c r l a).V n ω := by
  have hg : 0 ≤ rootPt r.1 ∧ 0 < c.s ∧ TimeOrdered 0 (historyProgram c r l) := ⟨hx, hs, hord⟩
  unfold schedVerXDeath
  rw [dite_eq_left hg]
  exact (exists_schedVersionsXA_strict_death_all h13 c r l a hg.1 hg.2.1 hg.2.2).choose_spec.choose_spec.2.2.2.2.2

include h13 in
/-- **Decision D26 (A′) at every root**: the root-`x` stage record of every instance identifies the zero-lifetime
candidate, almost surely on the history's success. -/
theorem ae_srecX_mem_launchBadRec_iff (I : GW2Sde.StageInst Ω) (x₀ : ℝ) :
    ∀ᵐ ω ∂c.P, oldSuccess c r l ω → (I.srecX c r l x₀ ω ∈ launchBadRec c r l a ↔ candLife c r l a ω = 0) := by
  filter_upwards [ae_mem_launchBadRec_iff c r l a h13] with ω hω hold
  exact hω hold _

include h13 in
/-- **Off `launchBadRec` (root-`x` stage record) the candidate's lifetime is positive** (history's success). -/
theorem ae_life_pos_of_srecX_notMem (I : GW2Sde.StageInst Ω) (x₀ : ℝ) :
    ∀ᵐ ω ∂c.P, oldSuccess c r l ω → I.srecX c r l x₀ ω ∉ launchBadRec c r l a → 0 < candLife c r l a ω := by
  filter_upwards [ae_srecX_mem_launchBadRec_iff h13 c r l a I x₀] with ω hω hold hnot
  exact pos_iff_ne_zero.2 fun hz => hnot ((hω hold).2 hz)

end Sched

/-- **The root-`x` death families** (`schedVerXDeath`), every source setup, root, history and candidate: the version
family to pass to ROOTX's `GW2Rv.RootPairInputsX` (decision D27). -/
def schedVerXDeathFamily (h13 : Exist.Theorem13Statement.{u}) : GW2Rv.SchedVerXFamily.{u} :=
  fun _ _ _ c r l a => schedVerXDeath h13 c r l a

end InteractingSLE.Theorem14.GW2Rd
