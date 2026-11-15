/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2UbGlue
import InteractingSLE.Spec.Supplement.GW2TvWord

/-!
# The tip exclusion at one sample: the decoded past, the junction and `BadCode`

Packet PROVE-GW2-RELDET (round 38, decisions D73 route (ii) and D81). NEARIMG2's counterflow-side statement
(`GW2Ni.aliveRead_stgDrv_cDrv`) reads the junction carried along the past `pastOf cfRec cDrv b N` with monotone
boundaries `b` from `0`; the stage word's junction `GW2Ni.farJunctionX` reads it along the stage decoder
`GW2Wm.stageDec` of the stage record. This file joins them:

* `monotone_trueBdX`, `trueBdX_self`: the decoder's true boundaries are monotone, from `0` to the stage start;
* **`stageDec_srecX`**: the stage decoder of a version's stage record is the version's past along the true
  boundaries (the internals of `baseWordX_inst_eq`, via `GW2Wm.stageDec_augRecX_trueBd`);
* **`badCode_of_glued`**: a good code with infinite lifetime whose decoded driver is a driver `Dg` keeping every
  rational point beyond `J` alive at every integer time, with the far right height beyond `J`, is `BadCode`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  GW2Rz GW2Wm Sec5.Prop513Schedule

section Bd

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)

/-- **The decoder's true boundaries are monotone** (a time-ordered history, finite caps). -/
theorem monotone_trueBdX (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    {V : Ω → ℝ≥0∞} {ω : Ω} (hV : V ω ≠ ⊤) (hord : TimeOrdered 0 (historyProgram c r l)) :
    Monotone (trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyProgram c r l)
      ((entryList l).length + 1) (historyTime c r l) ω) := by
  refine monotone_nat_of_le_succ fun j => ?_
  by_cases hj : j < (entryList l).length + 1
  · exact trueBdX_mono_of c r l a hx hs hGT hV hord j hj
  · unfold trueBdX
    rw [ite_eq_right (by omega), ite_eq_right hj, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- **The last true boundary is the stage start.** -/
theorem trueBdX_self (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {GT : Set Ω} {V : Ω → ℝ≥0∞} (ω : Ω) :
    trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyProgram c r l) ((entryList l).length + 1)
      (historyTime c r l) ω ((entryList l).length + 1) =
      stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω := by
  unfold trueBdX
  rw [ite_eq_right (Nat.succ_ne_zero _), ite_eq_right (lt_irrefl _)]

/-- **The stage decoder of a version's stage record is the version's past along the true boundaries** (one sample of
the good set, the history's success, the history time before the contact). -/
theorem stageDec_srecX (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (hord : TimeOrdered 0 (historyProgram c r l)) {ω : Ω} (hω : ω ∈ GT)
    (hold : oldSuccess c r l ω)
    (hTc : (historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω) :
    stageDec (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1) (length_historyProgram c r l)
        (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V
          (historyTime c r l) R) ω) =
      pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω)
        (trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyProgram c r l) ((entryList l).length + 1)
          (historyTime c r l) ω) ((entryList l).length + 1) := by
  set L := historyProgram c r l with hL
  set N := (entryList l).length + 1 with hNdef
  have hLN : L.length = N := length_historyProgram c r l
  have hTj : ∀ j < N, schedTime 0 L j ≤ historyTime c r l := fun j hj =>
    GW2Ru.schedTime_le_historyTime c r l hord (by rw [hLN]; exact hj.le)
  have hjT : ∀ j < N, schedTime 0 L j ≤ lastTime 0 L := fun j hj => by
    rw [← GW2Sde.historyTime_eq_lastTime]
    exact hTj j hj
  have hconj : ∀ j, 0 < j → j < N →
      (schedTime 0 L j : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω :=
    fun j _ hj => (ENNReal.coe_le_coe.2 (hTj j hj)).trans_lt hTc
  have hagree : ∀ u ≤ historyTime c r l, joinedRead L
      (fun i => (fun j : Fin N => stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j ω) (Fin.cast hLN i)) u =
        schedW c r l a u ω := fun u hu => by
    have e1 : schedW c r l a u ω = Gm.futureJoined c r l a ω u := congrFun (schedW_of_oldSuccess c r l a hold) u
    rw [e1, GW2Bf.futureJoined_eq_histJoined c r l a ω hu]
    rfl
  exact stageDec_augRecX_trueBd (x₀ := rootPt r.1) (sp := c.s) (W := schedW c r l a) (Wα := c.W) (ζα := c.ζ)
    (GT := GT) (V := V) (T := historyTime c r l) (R := R) (γ := schedTr c r l a) (α := c.α) hGT hs hx L N
    hLN (xr := stageEncRec c r l) (ω := ω)
    (P := fun j : Fin N => stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j ω) rfl (hA.2.1 ω)
    (hA.2.2.1 ω) hω (hV ω) hTj hjT hconj hagree

end Bd

/-! ### `BadCode` from a glued driver -/

open MartChar.RealFlow Sec2.Assembly Supp8.GB6 Supp8.GB6.RelDrv Sec4

/-- **`BadCode` from a glued driver**: a good code with infinite lifetime whose decoded driver is `Dg`, every rational
point beyond `J > 0` alive for `Dg` at every integer time, and the far right height `λ' − πχ + θa χ` beyond `J`
(`θa ∈ (−π/2, π/2)`). -/
theorem badCode_of_glued {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : BoundaryWord} {p : PCode × ℝ≥0∞}
    (hgood : IsGoodDrvCode p) (hp2 : p.2 = ⊤) {Dg : ℝ≥0 → ℝ} (hglue : drvDec p = Dg) {J θa : ℝ}
    (hJ : 0 < J)
    (hθ : θa ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hfar : GW2Ni.FarRAt b (sleLambda (16 / κ) - Real.pi * chiC κ + θa * chiC κ) J)
    (halive : ∀ q : ℚ, J < q → ∀ n : ℕ, GW2Bh.aliveRead n q Dg) : BadCode κ b p := by
  obtain ⟨r, hr⟩ := exists_rat_gt J
  have hr0 : (0 : ℚ) < r := by exact_mod_cast hJ.trans hr
  refine ⟨hp2, hgood, r, hr0, fun x x' hx hx' hxj hx'j => ?_, fun x hx hxj => ?_, fun q hq n => ?_⟩
  · rw [hfar x (hr.trans (by exact_mod_cast hx)) hxj, hfar x' (hr.trans (by exact_mod_cast hx')) hx'j]
  · rw [hfar x (hr.trans (by exact_mod_cast hx)) hxj]
    refine ⟨lt_cumWeightRight_far hκ hκ4 hθ.1, ?_⟩
    have h := GW2Ni.cumWeightRight_far_lt hκ hκ4 hθ.2
    rwa [zero_mul, add_zero] at h
  · rw [hglue]
    exact halive q (hr.trans (by exact_mod_cast hq)) n

/-! ### The unbounded-clock tip contact at one sample -/

section Unb

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The tip event of the stage code at a first contact with an unbounded relative clock** (one sample). Versions
`(R n, V n)` of the schedule, the stage record and field of a version alive at the stage start (`n₀`), the stopped
driver match of every version alive at the stage start with the canonical code of its record and field, caps
exhausting `ℝ≥0`, the stage word's far right height beyond `farJunctionX` and the counterflow record in `gb6TS`:
the code of `n₀` is in `TipCode`. -/
theorem tipCode_unbounded (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    {GT : Set Ω} (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1) {R : ℕ → ℝ≥0 → Ω → ℝ} {V : ℕ → Ω → ℝ≥0∞}
    (hA : ∀ n, IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (R n) (V n))
    (hV : ∀ n ω, V n ω ≠ ⊤) (hord : TimeOrdered 0 (historyProgram c r l)) {ξ : Ω} (hξ : ξ ∈ GT)
    (hRξ : ∀ n, VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (R n) (V n) ξ)
    (hold : oldSuccess c r l ξ) {τ : ℝ≥0} (hτ : contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ = τ)
    (hTτ : historyTime c r l < τ)
    (hunb : ∀ y : ℝ, ∃ v : ℝ≥0, v < τ ∧ y < clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) v ξ)
    (hneg : markPosL (rdrv (cfRec c.s c.W c.ζ ξ)) (rtime (cfRec c.s c.W c.ζ ξ)) 0 < 0)
    (β : RecData → BoundaryWord) (σa kc : ℝ)
    {Fd : BoundaryWord × LQGMetric.DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞} (n₀ : ℕ)
    (hn₀ : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n₀) (historyTime c r l) ξ < V n₀ ξ)
    (hcov : ∀ U : ℝ≥0, ∃ n, (U : ℝ≥0∞) < stgVX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n)
      (historyTime c r l) ξ ∧ stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ <
        V n ξ)
    (hmatch : ∀ n, stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ < V n ξ →
      Supp8.GB6.RelDrv.IsStopDrvMatch
        (Fd (β (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n)
          (historyTime c r l) (R n)) ξ), GW2Sde.stgField σa kc c.h (schedChartX c r l a GT (R n) (V n)) ξ))
        (fun u => stgRX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (R n) (V n) (historyTime c r l) u ξ)
        (stgVX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ))
    {θa : ℝ} (hθ : θa ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hJ : 0 < GW2Ni.farJunctionX (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
      (length_historyProgram c r l) (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ
        (schedW c r l a) GT (V n₀) (historyTime c r l) (R n₀)) ξ))
    (hfar : GW2Ni.FarRAt (β (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT
        (V n₀) (historyTime c r l) (R n₀)) ξ)) (sleLambda (16 / c.κ) - Real.pi * chiC c.κ + θa * chiC c.κ)
      (GW2Ni.farJunctionX (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
        (length_historyProgram c r l) (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ
          (schedW c r l a) GT (V n₀) (historyTime c r l) (R n₀)) ξ))) :
    TipCode c.κ (β (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n₀)
        (historyTime c r l) (R n₀)) ξ))
      (Fd (β (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n₀)
        (historyTime c r l) (R n₀)) ξ),
        GW2Sde.stgField σa kc c.h (schedChartX c r l a GT (R n₀) (V n₀)) ξ)) := by
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hGT ξ hξ
  have hTc : ((historyTime c r l) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ := by
    rw [hτ]
    exact_mod_cast hTτ
  set cD := GW2Ni.cDrv (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (fun t => schedW c r l a t ξ) τ with hcD
  set a₀ := stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n₀) (historyTime c r l) ξ with ha₀
  set p := Fd (β (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n₀)
    (historyTime c r l) (R n₀)) ξ), GW2Sde.stgField σa kc c.h (schedChartX c r l a GT (R n₀) (V n₀)) ξ) with hp
  -- one code for all versions alive at the stage start
  have hm : ∀ n, stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ < V n ξ →
      Supp8.GB6.RelDrv.IsStopDrvMatch p
        (fun u => stgRX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (R n) (V n) (historyTime c r l) u ξ)
        (stgVX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ) := fun n hn => by
    have h := hmatch n hn
    have e1 := stgPreRecX_eq_of_versions c r l a hGT hs hx hξ (hRξ n) (hRξ n₀) hTc hn hn₀
    have e2 := schedChartX_eq_of_versions c r l a hGT hs hx hξ (hRξ n) (hRξ n₀) hTc hn hn₀
    have e3 : GW2Sde.stgField σa kc c.h (schedChartX c r l a GT (R n) (V n)) ξ =
        GW2Sde.stgField σa kc c.h (schedChartX c r l a GT (R n₀) (V n₀)) ξ := by
      unfold GW2Sde.stgField
      rw [e2]
    rw [e3] at h
    simp only [augRec, e1] at h
    exact h
  -- the stage drivers are the stage driver of `cDrv`
  have hdrv : ∀ n, stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ < V n ξ →
      ∀ u : ℝ≥0, (u : ℝ≥0∞) <
        stgVX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ →
        stgRX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (R n) (V n) (historyTime c r l) u ξ =
          stgDrv cD a₀ u := fun n hn u hu => by
    rw [drvX_eq_stgDrv_cDrv c r l a hGT hs hx hξ (hRξ n) hτ hunb hu,
      (stgStart_eq_and_agree c r l a hGT hs hx hξ (hRξ n) (hRξ n₀) hTc hn hn₀).1]
  by_cases hgood : IsGoodDrvCode p
  swap
  · exact Or.inl hgood
  -- infinite lifetime
  have hp2 : p.2 = ⊤ := by
    by_contra hne
    obtain ⟨n, hn, hna⟩ := hcov p.2.toNNReal
    rw [ENNReal.coe_toNNReal hne] at hn
    exact absurd ((hm n hna).1.trans_lt hn) (lt_irrefl _)
  -- the decoded driver is the stage driver of `cDrv`
  have hglue : drvDec p = stgDrv cD a₀ := funext fun u => by
    obtain ⟨n, hn, hna⟩ := hcov u
    have hc : ContinuousOn
        (fun u => stgRX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (R n) (V n) (historyTime c r l) u ξ)
        {u | (u : ℝ≥0∞) < stgVX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ} :=
      (((hRξ n).1.comp (continuous_const.add continuous_id)).sub continuous_const).continuousOn
    rw [eqOn_drvDec_of_isStopDrvMatch hgood hc (hm n hna) u hn, hdrv n hna u hn]
  refine Or.inr (Or.inl (badCode_of_glued c.hκ c.hκ4 hgood hp2 hglue hJ hθ hfar fun q hq m => ?_))
  -- NEARIMG2's counterflow side, along the version's decoded past
  set b := trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n₀) (historyProgram c r l)
    ((entryList l).length + 1) (historyTime c r l) ξ with hb
  have hbm : Monotone b := monotone_trueBdX c r l a hx hs hGT (hV n₀ ξ) hord
  have hbN : b ((entryList l).length + 1) = a₀ := trueBdX_self c r l a ξ
  have hb0 : b 0 = 0 := by simp [hb, trueBdX]
  have ha₀V : (a₀ : ℝ≥0∞) < V n₀ ξ := by
    have hne : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n₀) (historyTime c r l) ξ ≠ ⊤ :=
      ne_top_of_lt hn₀
    show ((stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n₀) (historyTime c r l) ξ).toNNReal :
      ℝ≥0∞) < V n₀ ξ
    rw [ENNReal.coe_toNNReal hne]
    exact hn₀
  have hpast := stageDec_srecX c r l a hx hs hGT (hA n₀) (hV n₀) hord hξ hold hTc
  have hpast' : pastOf (cfRec c.s c.W c.ζ ξ) (fun u => R n₀ u ξ) b ((entryList l).length + 1) =
      pastOf (cfRec c.s c.W c.ζ ξ) cD b ((entryList l).length + 1) := by
    refine GW2Wm.pastOf_congr (cfRec c.s c.W c.ζ ξ) (B := a₀) (fun u hu => ?_) ((entryList l).length + 1)
      fun j _ => ?_
    · obtain ⟨v, hvτ, hv⟩ := hunb (u : ℝ)
      exact version_eq_cDrv c r l a hGT hs hx hξ (hRξ n₀) hτ
        ((ENNReal.coe_le_coe.2 hu).trans ha₀V.le) hvτ hv
    · rcases le_total j ((entryList l).length + 1) with hjN | hjN
      · exact hbN ▸ hbm hjN
      · have : b j = a₀ := by
          rw [hb]
          unfold trueBdX
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        exact this.le
  have hjunc : GW2Ni.cfJunctionX (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
      (length_historyProgram c r l)
      (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n₀)
        (historyTime c r l) (R n₀)) ξ) =
      GW2Ni.cfJunction (GW2Ni.cfJunctionRootX (rootPt r.1) c.s) ((entryList l).length + 1)
        (pastOf (cfRec c.s c.W c.ζ ξ) cD b ((entryList l).length + 1)) := by
    unfold GW2Ni.cfJunctionX
    rw [hpast, hpast']
  have hq' : GW2Ni.cfJunction (GW2Ni.cfJunctionRootX (rootPt r.1) c.s) ((entryList l).length + 1)
      (pastOf (cfRec c.s c.W c.ζ ξ) cD b ((entryList l).length + 1)) <
      (q : ℝ) := by
    rw [← hjunc]
    exact lt_of_le_of_lt (GW2Ni.cfJunctionX_le_farJunctionX _ _ _ _ _ _) hq
  have h := GW2Ni.aliveRead_stgDrv_cDrv c.W c.ζ ξ hα hW hW0 hζ hs hx harc hwc hw0 hγ hτ hneg hunb hb0 hbm
    ((entryList l).length + 1) hq' m
  rwa [hbN] at h

end Unb

/-! ### The bounded-clock tip contact at one sample -/

/-- **`BadFin` from versions with bounded caps and unbounded drivers** (generic; the second case of
`tipCode_of_versions`). -/
theorem badFin_of_versions {p : Sec2.Assembly.PCode × ℝ≥0∞} (hgood : Supp8.GB6.IsGoodDrvCode p)
    {D : ℕ → ℝ≥0 → ℝ} {C : ℕ → ℝ≥0∞} (hD : ∀ n, ContinuousOn (D n) {u | (u : ℝ≥0∞) < C n})
    (hmatch : ∀ n, Supp8.GB6.RelDrv.IsStopDrvMatch p (D n) (C n)) {B : ℝ≥0} (hB : ∀ n, C n ≤ B)
    (hunb : ∀ M : ℝ, ∃ (n : ℕ) (u : ℝ≥0), (u : ℝ≥0∞) < C n ∧ M < |D n u|) : BadFin p := by
  have hdec : ∀ n (u : ℝ≥0), (u : ℝ≥0∞) < C n → Supp8.GB6.drvDec p u = D n u := fun n =>
    Supp8.GB6.RelDrv.eqOn_drvDec_of_isStopDrvMatch hgood (hD n) (hmatch n)
  refine ⟨fun hp2 => ?_, fun M => ?_⟩
  · have hcont : ContinuousOn (Supp8.GB6.drvDec p) (Icc 0 B) :=
      (Supp8.GB6.continuousOn_drvDec p).mono fun t _ => show (t : ℝ≥0∞) < p.2 by
        rw [hp2]; exact ENNReal.coe_lt_top
    obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    obtain ⟨n, u, hu, hMu⟩ := hunb M₀
    have huB : u ∈ Icc 0 B := ⟨zero_le, ENNReal.coe_le_coe.1 (hu.le.trans (hB n))⟩
    have h := hM₀ u huB
    rw [Real.norm_eq_abs, hdec n u hu] at h
    linarith
  · obtain ⟨n, u, hu, hMu⟩ := hunb ((M : ℝ) + 1)
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < C n} := isOpen_lt ENNReal.continuous_coe continuous_const
    have hca : ContinuousAt (D n) u := (hD n).continuousAt (hopen.mem_nhds hu)
    have hg : ContinuousAt (fun s : ℝ => D n s.toNNReal) (u : ℝ) := by
      refine ContinuousAt.comp (f := Real.toNNReal) ?_ continuous_real_toNNReal.continuousAt
      rw [Real.toNNReal_coe]
      exact hca
    have hgC : ContinuousAt (fun s : ℝ => ((s.toNNReal : ℝ≥0) : ℝ≥0∞)) (u : ℝ) :=
      (ENNReal.continuous_coe.comp continuous_real_toNNReal).continuousAt
    have hev : ∀ᶠ s in 𝓝 (u : ℝ), |D n s.toNNReal - D n u| < 1 ∧ ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < C n := by
      refine (Metric.tendsto_nhds.1 hg 1 one_pos).mono (fun s hs => ?_) |>.and ?_
      · rw [Real.dist_eq] at hs
        simpa only [Real.toNNReal_coe] using hs
      · have hu' : (fun s : ℝ => ((s.toNNReal : ℝ≥0) : ℝ≥0∞)) (u : ℝ) < C n := by
          simpa only [Real.toNNReal_coe] using hu
        exact hgC.eventually (eventually_lt_nhds hu')
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (u : ℝ) < u + ε by linarith)
    have hqd : dist (q : ℝ) u < ε := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith
    obtain ⟨h1, h2⟩ := hball hqd
    refine ⟨q, h2.trans_le (hmatch n).1, ?_⟩
    rw [hdec n _ h2]
    have := abs_sub_abs_le_abs_sub (D n u) (D n (q : ℝ).toNNReal)
    rw [abs_sub_comm] at this
    linarith

section Bdd

variable {Ω : Type u} [MeasurableSpace Ω]

open Classical in
/-- **The tip event of the stage code at a first contact with a bounded relative clock** (one sample): with
`TipUnbStatement`'s unbounded glued driver below the life, versions alive at the stage start matching their codes
and covering every clock value before the contact, the code of `n₀` is in `TipCode` (`BadFin`). -/
theorem tipCode_bounded (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    {GT : Set Ω} (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1) {R : ℕ → ℝ≥0 → Ω → ℝ} {V : ℕ → Ω → ℝ≥0∞} {ξ : Ω} (hξ : ξ ∈ GT)
    (hRξ : ∀ n, VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (R n) (V n) ξ)
    {τ : ℝ≥0} (hτ : contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ = τ) (hTτ : historyTime c r l < τ)
    {M : ℝ} (hbdd : ∀ v : ℝ≥0, v < τ → clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) v ξ ≤ M)
    (htip : ∀ B : ℝ, ∃ (u v : ℝ≥0), v < τ ∧ (u : ℝ) < clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) v ξ ∧
      B < |GW2Ni.cDrv (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (fun t => schedW c r l a t ξ) τ u|)
    (hcov : ∀ u : ℝ≥0, (∃ v : ℝ≥0, v < τ ∧ (u : ℝ) < clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) v ξ) →
      ∃ n, stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ < V n ξ ∧
        (u : ℝ≥0∞) < V n ξ)
    (hVcl : ∀ n (u : ℝ≥0), (u : ℝ≥0∞) < V n ξ → ∃ t : ℝ≥0, t < τ ∧
      (u : ℝ) < clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ)
    (β : RecData → BoundaryWord) (σa kc : ℝ)
    {Fd : BoundaryWord × LQGMetric.DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞} (n₀ : ℕ)
    (hn₀ : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n₀) (historyTime c r l) ξ < V n₀ ξ)
    (hmatch : ∀ n, stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ < V n ξ →
      Supp8.GB6.RelDrv.IsStopDrvMatch
        (Fd (β (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n)
          (historyTime c r l) (R n)) ξ), GW2Sde.stgField σa kc c.h (schedChartX c r l a GT (R n) (V n)) ξ))
        (fun u => stgRX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (R n) (V n) (historyTime c r l) u ξ)
        (stgVX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ)) :
    TipCode c.κ (β (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n₀)
        (historyTime c r l) (R n₀)) ξ))
      (Fd (β (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n₀)
        (historyTime c r l) (R n₀)) ξ),
        GW2Sde.stgField σa kc c.h (schedChartX c r l a GT (R n₀) (V n₀)) ξ)) := by
  have hTc : ((historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ := by
    rw [hτ]
    exact_mod_cast hTτ
  set cD := GW2Ni.cDrv (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (fun t => schedW c r l a t ξ) τ with hcD
  set a₀ := stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n₀) (historyTime c r l) ξ with ha₀
  set p := Fd (β (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n₀)
    (historyTime c r l) (R n₀)) ξ), GW2Sde.stgField σa kc c.h (schedChartX c r l a GT (R n₀) (V n₀)) ξ) with hp
  -- one code for all versions alive at the stage start
  have hm : ∀ n, stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ < V n ξ →
      Supp8.GB6.RelDrv.IsStopDrvMatch p
      (fun u => stgRX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (R n) (V n) (historyTime c r l) u ξ)
      (stgVX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ) := fun n hn => by
    have h := hmatch n hn
    have e1 := stgPreRecX_eq_of_versions c r l a hGT hs hx hξ (hRξ n) (hRξ n₀) hTc hn hn₀
    have e2 := schedChartX_eq_of_versions c r l a hGT hs hx hξ (hRξ n) (hRξ n₀) hTc hn hn₀
    have e3 : GW2Sde.stgField σa kc c.h (schedChartX c r l a GT (R n) (V n)) ξ =
        GW2Sde.stgField σa kc c.h (schedChartX c r l a GT (R n₀) (V n₀)) ξ := by
      unfold GW2Sde.stgField
      rw [e2]
    rw [e3] at h
    simp only [augRec, e1] at h
    exact h
  have hstart : ∀ n, stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ < V n ξ →
      stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ = a₀ := fun n hn =>
    (stgStart_eq_and_agree c r l a hGT hs hx hξ (hRξ n) (hRξ n₀) hTc hn hn₀).1
  have ha₀V : (a₀ : ℝ≥0∞) < V n₀ ξ := by
    have hne : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n₀) (historyTime c r l) ξ ≠ ⊤ :=
      ne_top_of_lt hn₀
    show ((stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n₀) (historyTime c r l) ξ).toNNReal :
      ℝ≥0∞) < V n₀ ξ
    rw [ENNReal.coe_toNNReal hne]
    exact hn₀
  by_cases hgood : Supp8.GB6.IsGoodDrvCode p
  swap
  · exact Or.inl hgood
  refine Or.inr (Or.inr ?_)
  -- the versions alive at the stage start, the others with cap `0`
  set C : ℕ → ℝ≥0∞ := fun n =>
    if stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ < V n ξ then
      stgVX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ else 0 with hC
  set D : ℕ → ℝ≥0 → ℝ := fun n u =>
    if stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ < V n ξ then
      stgRX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (R n) (V n) (historyTime c r l) u ξ
    else 0 with hDdef
  have hD : ∀ n, ContinuousOn (D n) {u | (u : ℝ≥0∞) < C n} := fun n => by
    by_cases hn : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ < V n ξ
    · have e : D n = fun u =>
          stgRX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (R n) (V n) (historyTime c r l) u ξ := by
        funext u
        simp only [hDdef, hn, ↓reduceIte]
      rw [e]
      exact (((hRξ n).1.comp (continuous_const.add continuous_id)).sub continuous_const).continuousOn
    · have e : D n = fun _ => 0 := by
        funext u
        simp only [hDdef, hn, ↓reduceIte]
      rw [e]
      exact continuousOn_const
  have hmatch' : ∀ n, Supp8.GB6.RelDrv.IsStopDrvMatch p (D n) (C n) := fun n => by
    by_cases hn : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ < V n ξ
    · have e1 : D n = fun u =>
          stgRX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (R n) (V n) (historyTime c r l) u ξ := by
        funext u
        simp only [hDdef, hn, ↓reduceIte]
      have e2 : C n = stgVX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ := by
        simp only [hC, hn, ↓reduceIte]
      rw [e1, e2]
      exact hm n hn
    · have e2 : C n = 0 := by simp only [hC, hn, ↓reduceIte]
      rw [e2]
      exact ⟨zero_le, fun _ _ h => absurd h (not_lt.2 zero_le)⟩
  -- the caps are bounded by the clock bound
  have hVM : ∀ n, V n ξ ≤ ENNReal.ofReal M := fun n => by
    by_contra h
    rw [not_le] at h
    obtain ⟨u, hu1, hu2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h
    obtain ⟨t, ht, hut⟩ := hVcl n u hu2
    have : (u : ℝ≥0∞) ≤ ENNReal.ofReal M := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (hut.le.trans (hbdd t ht))
    exact absurd hu1 (not_lt.2 this)
  have hB : ∀ n, C n ≤ ((ENNReal.ofReal M).toNNReal : ℝ≥0∞) := fun n => by
    rw [ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]
    by_cases hn : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ < V n ξ
    · simp only [hC, hn, ↓reduceIte]
      exact tsub_le_self.trans (hVM n)
    · simp only [hC, hn, ↓reduceIte]
      exact zero_le
  -- the stage drivers are unbounded
  refine badFin_of_versions hgood hD hmatch' hB fun M₁ => ?_
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := a₀)).exists_bound_of_continuousOn
    ((hRξ n₀).1.continuousOn)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, zero_le⟩)
  have hcDa₀ : cD a₀ = R n₀ a₀ ξ := by
    obtain ⟨t, ht, hat⟩ := hVcl n₀ a₀ ha₀V
    exact (version_eq_cDrv c r l a hGT hs hx hξ (hRξ n₀) hτ ha₀V.le ht hat).symm
  obtain ⟨u, v, hvτ, huv, hbig⟩ := htip (|M₁| + K + |R n₀ a₀ ξ|)
  -- the escaping time is beyond the stage start
  have hua : a₀ < u := by
    by_contra hle
    rw [not_lt] at hle
    have huV : (u : ℝ≥0∞) ≤ V n₀ ξ := (ENNReal.coe_le_coe.2 hle).trans ha₀V.le
    have heq := version_eq_cDrv c r l a hGT hs hx hξ (hRξ n₀) hτ huV hvτ huv
    have hKu := hK u ⟨zero_le, hle⟩
    rw [Real.norm_eq_abs, heq] at hKu
    have hKu' : |cD u| ≤ K := hKu
    linarith [abs_nonneg (R n₀ a₀ ξ), abs_nonneg M₁]
  obtain ⟨n, hn, huVn⟩ := hcov u ⟨v, hvτ, huv⟩
  have hau : a₀ + (u - a₀) = u := add_tsub_cancel_of_le hua.le
  refine ⟨n, u - a₀, ?_, ?_⟩
  · show ((u - a₀ : ℝ≥0) : ℝ≥0∞) < C n
    simp only [hC]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hn)]
    show ((u - a₀ : ℝ≥0) : ℝ≥0∞) < V n ξ -
      (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ : ℝ≥0∞)
    rw [hstart n hn, lt_tsub_iff_left, ← ENNReal.coe_add, hau]
    exact huVn
  · show M₁ < |D n (u - a₀)|
    simp only [hDdef]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hn)]
    show M₁ < |stgDrv (fun t => R n t ξ)
      (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (V n) (historyTime c r l) ξ) (u - a₀)|
    rw [hstart n hn]
    unfold stgDrv
    have haV : (a₀ : ℝ≥0∞) ≤ V n ξ := (ENNReal.coe_le_coe.2 hua.le).trans huVn.le
    have hac : (a₀ : ℝ) < clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) v ξ :=
      lt_trans (by exact_mod_cast hua) huv
    rw [hau]
    beta_reduce
    rw [version_eq_cDrv c r l a hGT hs hx hξ (hRξ n) hτ huVn.le hvτ huv,
      version_eq_cDrv c r l a hGT hs hx hξ (hRξ n) hτ haV hvτ hac]
    show M₁ < |cD u - cD a₀|
    rw [hcDa₀]
    have h1 := abs_sub_abs_le_abs_sub (cD u) (R n₀ a₀ ξ)
    linarith [le_abs_self M₁]
end Bdd

end InteractingSLE.Theorem14.GW2Rd
