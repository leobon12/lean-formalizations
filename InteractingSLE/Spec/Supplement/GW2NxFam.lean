/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NxGauge
import InteractingSLE.Spec.Supplement.GW2PsmCapB

/-!
# The stop-capped version family (decision D49 (A))

Packet PROVE-GW2-NOTHR (round 6, decision D54). The schedule instance's root-`x` versions capped strictly before the
STOP gauge's life (`GW2Nx.stopGaugeX`): RELDET's death family (`GW2Rd.schedVerXDeath`) cut off at the candidate's
cap.

* `schedStopLifeX`: the life of the stop gauge at the schedule (the launch gauge's life `GW2Rd.schedLaunchLifeX`
  cut off at the root-`x` clock of `T + cap`);
* **`exists_schedVersionsXA_strict_stop`**: finite, monotone, strictly increasing on the good records, strictly
  below `schedStopLifeX`, exhausting the root-`x` clock below it;
* **`ae_histCapGain_le_stopLifeX`**, **`ae_exhausts_of_stopX`**: the history's capacity plus the gain is at most the
  stop life (the buffer is at most both the lifetime and the cap), so ROOTX's `exhausts` holds;
* **`le_physClockX_of_stop`**: a version strictly below the stop life is at most the root-`x` physical clock of
  `T + candStop` (the candidate's stop, `GW2Psm.candStop`), on the good set, the history's success and a positive
  lifetime — the property `hVd` that STAGEMEAN's `GW2Psm.lt_stop_of_clockX` consumes;
* **`schedVerXStop`**, **`schedVerXStopFamily`**: the family as a `GW2Rv.SchedVerX` / `GW2Rv.SchedVerXFamily`;
  `schedVerXStop_lt_stopLifeX`, `schedVerXStop_exhausts_stop`, **`ae_schedVerXStop_le_physClockX`**;
* **`schedVerXStop_lt_deathClockX`**, **`schedVerXStop_exhausts_death`** (via `ae_deathClockX_le_stopLifeX`): the
  family also has the two properties of RELDET's death family (caps below the death clock; exhaustion below a FINITE
  death clock), the inputs `hcaps`/`hD27` of `GW2Nv.deathThrX_of_export_fin`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Nx

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.RelSafe
  GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd Sec5.Prop513Schedule

section Defs

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **The life of the schedule instance's stop gauge at the root point.** -/
abbrev schedStopLifeX (ω : Ω) : ℝ≥0∞ :=
  stopLifeX c.κ (candAngle c r l a) (launchWordOf c r l a) (historyTime c r l) (candidateCap c r a) (rootPt r.1)
    c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω

theorem schedStopLifeX_eq (ω : Ω) :
    schedStopLifeX c r l a ω = min (schedLaunchLifeX c r l a ω)
      (capLife (historyTime c r l) (candidateCap c r a)
        (fun t => clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω)
        (contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω)) := rfl

end Defs

section Sched

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

include h13 in
/-- **The schedule instance's root-`x` versions capped strictly before the stop gauge's life**: finite, monotone,
strictly increasing on the good records, below the stop life on the good records, exhausting every root-`x` clock
value below the stop life before the root-`x` contact. -/
theorem exists_schedVersionsXA_strict_stop (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (R n) (V n)) ∧
      (∀ n ω, V n ω ≤ V (n + 1) ω) ∧
      (∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → ∀ n, V n ω < V (n + 1) ω) ∧
      (∀ n ω, V n ω ≠ ⊤) ∧
      (∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → ∀ n, V n ω < schedStopLifeX c r l a ω) ∧
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < schedStopLifeX c r l a ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < V n ω := by
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  have hγ : ∀ᵐ ω ∂c.P, IsGeneratingTrace (schedW c r l a · ω) ⊤ (schedTr c r l a ω) ∧
      Tendsto (fun t => ‖schedTr c r l a ω t‖) atTop atTop :=
    (ae_schedW_regular h13 c r l a).mono fun _ h => ⟨h.2.2.1, h.2.2.2⟩
  exact exists_versionsXA_stopGauge hfl hα (ae_source_noReturn h13 c) (GW2Rv.ae_source_cf_complete h13 c)
    (measurable_schedW c r l a) (continuous_schedW c r l a) (schedW_zero c r l a) hγ hs hx
    (measurable_launchWordOf c r l a) (candidateCap_pos c r a) fun _ _ h => launchWordOf_congr c r l a h

include h13 in
/-- **The history's capacity plus the gain is at most the stop life** (the buffer is at most the lifetime and at
most the cap), almost surely at a positive gain. -/
theorem ae_histCapGain_le_stopLifeX (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ξ ∂c.P, 0 < GW2Sdg.rootGain c r l a ξ →
      ((GW2Sdg.rootHistCap c r l a ξ + GW2Sdg.rootGain c r l a ξ : ℝ≥0) : ℝ≥0∞) ≤ schedStopLifeX c r l a ξ := by
  filter_upwards [ae_histCapGain_le_deathClockX h13 c r l a hx hs, ae_schedLaunchLifeX_eq h13 c r l a hord,
    ae_schedLaunchLifeX_eq_top_of_zero h13 c r l a hord, GW2Rv.ae_histCap_add_gainX h13 c r l a,
    ae_exactPair_rootX h13 c r l a, ae_schedClockX_props h13 c r l a hx hs] with ξ hdc hle hz hsum hpair hclk hpos
  have hlive := GW2Rv.live_of_gain_pos c r l a hpos
  obtain ⟨-, hold, -, -⟩ := RootK32.sourceSample_live_geometry c r l a ξ hlive
  obtain ⟨hgx, hTc, -⟩ := hpair hlive
  obtain ⟨-, hmono, -⟩ := hclk hgx
  rw [schedStopLifeX_eq]
  refine le_min ?_ ?_
  · rcases eq_zero_or_pos (candLife c r l a ξ) with h0 | h0
    · rw [hz hold h0]
      exact le_top
    · rw [hle hold h0]
      exact hdc hpos
  · unfold capLife
    split_ifs with hc
    · rw [hsum hpos]
      exact ENNReal.ofReal_le_ofReal
        (hmono.monotoneOn hTc hc (add_le_add_right (sourceBuffer_le c r l a ξ) _))
    · exact le_top

include h13 in
/-- **Exhaustion below the stop life gives ROOTX's exhaustion of the history's capacity plus the gain** (the
`exhausts` field of `GW2Rv.SchedVerX`). -/
theorem ae_exhausts_of_stopX (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) (hord : TimeOrdered 0 (historyProgram c r l))
    {V : ℕ → Ω → ℝ≥0∞}
    (hev : ∀ᵐ ξ ∂c.P, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s → ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < schedStopLifeX c r l a ξ →
      ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < V n ξ) :
    ∀ᵐ ξ ∂c.P, ∀ u : ℝ≥0, u < GW2Sdg.rootGain c r l a ξ →
      ∀ᶠ n in atTop, ((GW2Sdg.rootHistCap c r l a ξ + u : ℝ≥0) : ℝ≥0∞) < V n ξ := by
  filter_upwards [hev, ae_exactPair_rootX h13 c r l a, GW2Rv.ae_histCap_add_gainX h13 c r l a,
    ae_histCapGain_le_stopLifeX h13 c r l a hx hs hord, ae_schedClockX_props h13 c r l a hx hs]
    with ξ hevξ hpair hsum hle hclk u hu
  have hpos : 0 < GW2Sdg.rootGain c r l a ξ := lt_of_le_of_lt zero_le hu
  have hlive := GW2Rv.live_of_gain_pos c r l a hpos
  obtain ⟨hgx, hTc, -⟩ := hpair hlive
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
  have hclt : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < schedStopLifeX c r l a ξ := by
    rw [hofr]
    exact (ENNReal.coe_lt_coe.2 (add_lt_add_right hu K)).trans_le (hle hpos)
  filter_upwards [hevξ hgx t htc hclt] with n hn
  rwa [hofr] at hn

include h13 in
/-- **A version strictly below the stop life is stopped at the candidate's stop** (D49 (A)): on the good set, the
history's success and a positive lifetime, it is at most the root-`x` physical clock of `T + candStop`. Before the
root-`x` contact the stop life is at most the clock of `T + candStop` (the death clock if the candidate dies by its
cap, the clock of `T + cap` otherwise); past the contact the version itself is below the clock's supremum. -/
theorem le_physClockX_of_stop (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) (hord : TimeOrdered 0 (historyProgram c r l))
    {GT : Set Ω} (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V) :
    ∀ᵐ ω ∂c.P, ω ∈ GT → cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
      0 < candLife c r l a ω → V ω < schedStopLifeX c r l a ω →
      V ω ≤ physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT
        (historyTime c r l + GW2Psm.candStop c r l a ω) ω := by
  filter_upwards [hA.2.2.2.2.2.2, ae_schedLaunchLifeX_eq h13 c r l a hord] with ω hV hlaunch hωGT hgood hold hζ0
    hlt
  obtain ⟨-, hsup, -⟩ := hV hgood
  by_cases hc : ((historyTime c r l + GW2Psm.candStop c r l a ω : ℝ≥0) : ℝ≥0∞) <
      contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω
  · rw [physClockX_eq_clockX hGT hs hx hωGT hc]
    refine hlt.le.trans ?_
    rw [schedStopLifeX_eq]
    by_cases hζc : candLife c r l a ω ≤ candidateCap c r a
    · have hstop : GW2Psm.candStop c r l a ω = (candLife c r l a ω).toNNReal := by
        unfold GW2Psm.candStop
        rw [min_eq_right hζc]
      rw [hstop] at hc ⊢
      refine (min_le_left _ _).trans (le_of_eq ?_)
      rw [hlaunch hold hζ0, deathClockX, ite_eq_left_of_eq_true _ _ (eq_true ⟨hζc, hc⟩)]
    · have hstop : GW2Psm.candStop c r l a ω = candidateCap c r a := by
        unfold GW2Psm.candStop
        rw [min_eq_left (le_of_lt (not_le.1 hζc)), ENNReal.toNNReal_coe]
      rw [hstop] at hc ⊢
      refine (min_le_right _ _).trans (le_of_eq ?_)
      unfold capLife
      rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
  · rw [physClockX_eq_iSup hGT hs hx hωGT]
    by_contra hcon
    obtain ⟨u, hu1, hu2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (not_le.1 hcon)
    obtain ⟨t, ht, hut⟩ := hsup u hu2
    have htT : t < historyTime c r l + GW2Psm.candStop c r l a ω :=
      ENNReal.coe_lt_coe.1 (ht.trans_le (not_lt.1 hc))
    have hle : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) ≤
        supBelow (fun t' => ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t' ω))
          (contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω) (historyTime c r l + GW2Psm.candStop c r l a ω) :=
      le_iSup₂_of_le (f := fun (t' : ℝ≥0) (_ : t' < historyTime c r l + GW2Psm.candStop c r l a ω ∧
          (t' : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω) =>
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t' ω)) t ⟨htT, ht⟩ le_rfl
    have hu' : (u : ℝ≥0∞) < ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt u.coe_nonneg hut)).2 hut
    exact absurd (hu1.trans (hu'.trans_le hle)) (lt_irrefl _)

open Classical in
/-- **The stop-capped family as a version family at a root** (`GW2Rv.SchedVerX`, decision D49 (A)): at a
nonnegative root point, a positive retained time and a time-ordered history, the family of
`exists_schedVersionsXA_strict_stop` (chosen); ROOTX's canonical family otherwise. -/
def schedVerXStop : GW2Rv.SchedVerX c r l a :=
  if hg : 0 ≤ rootPt r.1 ∧ 0 < c.s ∧ TimeOrdered 0 (historyProgram c r l) then
    { R := (exists_schedVersionsXA_strict_stop h13 c r l a hg.1 hg.2.1).choose
      V := (exists_schedVersionsXA_strict_stop h13 c r l a hg.1 hg.2.1).choose_spec.choose
      isA := fun _ => (exists_schedVersionsXA_strict_stop h13 c r l a hg.1 hg.2.1).choose_spec.choose_spec.1
      mono := (exists_schedVersionsXA_strict_stop h13 c r l a hg.1 hg.2.1).choose_spec.choose_spec.2.1
      fin := (exists_schedVersionsXA_strict_stop h13 c r l a hg.1 hg.2.1).choose_spec.choose_spec.2.2.2.1
      strict := fun _ => (exists_schedVersionsXA_strict_stop h13 c r l a hg.1 hg.2.1).choose_spec.choose_spec.2.2.1
      exhausts := fun _ => ae_exhausts_of_stopX h13 c r l a hg.1 hg.2.1 hg.2.2
        (exists_schedVersionsXA_strict_stop h13 c r l a hg.1 hg.2.1).choose_spec.choose_spec.2.2.2.2.2 }
  else GW2Rv.schedVerXCanon h13 c r l a

/-- **The stop family's caps are strictly below the stop life** (good records). -/
theorem schedVerXStop_lt_stopLifeX (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      ∀ n, (schedVerXStop h13 c r l a).V n ω < schedStopLifeX c r l a ω := by
  have hg : 0 ≤ rootPt r.1 ∧ 0 < c.s ∧ TimeOrdered 0 (historyProgram c r l) := ⟨hx, hs, hord⟩
  unfold schedVerXStop
  rw [dite_eq_left hg]
  exact (exists_schedVersionsXA_strict_stop h13 c r l a hg.1 hg.2.1).choose_spec.choose_spec.2.2.2.2.1

/-- **The stop family exhausts the root-`x` clock below the stop life** (good records). -/
theorem schedVerXStop_exhausts_stop (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < schedStopLifeX c r l a ω →
      ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) <
        (schedVerXStop h13 c r l a).V n ω := by
  have hg : 0 ≤ rootPt r.1 ∧ 0 < c.s ∧ TimeOrdered 0 (historyProgram c r l) := ⟨hx, hs, hord⟩
  unfold schedVerXStop
  rw [dite_eq_left hg]
  exact (exists_schedVersionsXA_strict_stop h13 c r l a hg.1 hg.2.1).choose_spec.choose_spec.2.2.2.2.2

/-- **The stop family is stopped at the candidate's stop** (D49 (A), the `hVd` of STAGEMEAN's
`GW2Psm.lt_stop_of_clockX`): on the good set, the history's success and a positive lifetime, every cap is at most the
root-`x` physical clock of `T + candStop`. -/
theorem ae_schedVerXStop_le_physClockX (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    (hord : TimeOrdered 0 (historyProgram c r l)) {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) (n : ℕ) :
    ∀ᵐ ω ∂c.P, ω ∈ GT → cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
      0 < candLife c r l a ω →
      (schedVerXStop h13 c r l a).V n ω ≤ physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT
        (historyTime c r l + GW2Psm.candStop c r l a ω) ω := by
  filter_upwards [le_physClockX_of_stop h13 c r l a hx hs hord hGT ((schedVerXStop h13 c r l a).isA hx n).1.1,
    schedVerXStop_lt_stopLifeX h13 c r l a hx hs hord] with ω h1 h2 hGTω hgood hold hζ0
  exact h1 hGTω hgood hold hζ0 (h2 hgood n)

include h13 in
/-- **Where the candidate dies before its cap and the contact, the stop life is the death clock** (history's
success, positive lifetime). -/
theorem ae_stopLifeX_eq_deathClockX
    (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω → 0 < candLife c r l a ω →
      schedStopLifeX c r l a ω = min (deathClockX c r l a ω)
        (capLife (historyTime c r l) (candidateCap c r a)
          (fun t => clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω)
          (contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω)) := by
  filter_upwards [ae_schedLaunchLifeX_eq h13 c r l a hord] with ω hlaunch _ hold hζ0
  rw [schedStopLifeX_eq, hlaunch hold hζ0]

/-- **The stop family's caps are strictly below the death clock** (RELDET's `schedVerXDeath_lt_deathClockX` for the
stop family; positive lifetime, history's success, good records). -/
theorem schedVerXStop_lt_deathClockX (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω → 0 < candLife c r l a ω →
      ∀ n, (schedVerXStop h13 c r l a).V n ω < deathClockX c r l a ω := by
  filter_upwards [schedVerXStop_lt_stopLifeX h13 c r l a hx hs hord,
    ae_stopLifeX_eq_deathClockX h13 c r l a hord] with ω h1 h2 hgood hold hζ0 n
  exact (h1 hgood n).trans_le ((h2 hgood hold hζ0).le.trans (min_le_left _ _))

include h13 in
/-- **A finite death clock is at most the stop life** (history's success, any lifetime): the launch gauge's life is
the death clock (positive lifetime) or `⊤` (zero lifetime), and a death by the cap is before the cap's clock. -/
theorem ae_deathClockX_le_stopLifeX (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
      deathClockX c r l a ω ≠ ⊤ → deathClockX c r l a ω ≤ schedStopLifeX c r l a ω := by
  filter_upwards [ae_schedLaunchLifeX_eq h13 c r l a hord, ae_schedLaunchLifeX_eq_top_of_zero h13 c r l a hord,
    ae_schedClockX_props h13 c r l a hx hs] with ω hlaunch hz hclk hgood hold hne
  obtain ⟨-, hmono, -⟩ := hclk hgood
  have hd : candLife c r l a ω ≤ candidateCap c r a ∧
      ((historyTime c r l + (candLife c r l a ω).toNNReal : ℝ≥0) : ℝ≥0∞) <
        contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω := by
    by_contra hd
    exact hne (by rw [deathClockX, ite_eq_right_of_eq_false _ _ (eq_false hd)])
  rw [schedStopLifeX_eq]
  refine le_min ?_ ?_
  · rcases eq_zero_or_pos (candLife c r l a ω) with h0 | h0
    · rw [hz hold h0]
      exact le_top
    · exact (hlaunch hold h0).ge
  · rw [deathClockX, ite_eq_left_of_eq_true _ _ (eq_true hd)]
    unfold capLife
    split_ifs with hc
    · have hne' : candLife c r l a ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hd.1
      have hle : (candLife c r l a ω).toNNReal ≤ candidateCap c r a := by
        rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hne']
        exact hd.1
      exact ENNReal.ofReal_le_ofReal (hmono.monotoneOn hd.2 hc (add_le_add_right hle _))
    · exact le_top

/-- **The stop family exhausts the root-`x` clock below a finite death clock** (RELDET's
`schedVerXDeath_exhausts_death` for the stop family, at a finite death clock; history's success, good records, any
lifetime). -/
theorem schedVerXStop_exhausts_death (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
      deathClockX c r l a ω ≠ ⊤ → ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < deathClockX c r l a ω →
      ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) <
        (schedVerXStop h13 c r l a).V n ω := by
  filter_upwards [schedVerXStop_exhausts_stop h13 c r l a hx hs hord,
    ae_deathClockX_le_stopLifeX h13 c r l a hx hs hord] with ω h1 h2 hgood hold hne t ht htl
  exact h1 hgood t ht (htl.trans_le (h2 hgood hold hne))

end Sched

/-- **The stop-capped version families** (`schedVerXStop`), every source setup, root, history and candidate: the
version family of decision D49 (A). -/
def schedVerXStopFamily (h13 : Exist.Theorem13Statement.{u}) : GW2Rv.SchedVerXFamily.{u} :=
  fun _ _ _ c r l a => schedVerXStop h13 c r l a

end InteractingSLE.Theorem14.GW2Nx
