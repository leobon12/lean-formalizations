/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1InEndK
import InteractingSLE.Spec.Sec7.StripSysPath

/-!
# Proposition BW1, the endpoint: reduction to one deterministic sample

Packet PROVE-BW1-INPUTS. `BW1Life.BW1EndpointStatement` (p. 614–615, "The endpoint and all relative stopping times")
is reduced to a statement about one sample, **`BW1EndpointDetStatement`**, whose hypotheses are exactly what holds
almost surely on BW1's threshold event:

* the first piece is regular through its stop and its traces do not return to `0` (`BW1Prop.ae_bw1_piece_hyps`);
* the physical counterflow driver is continuous from `0` with a complete transient generating trace `γ`;
* the relative driver `Wr` is continuous from `0` with a complete transient generating trace `Γ` that avoids the
  closed protected tails of the record whenever they are nondegenerate (`ae_mem_bwAvoid`, GB5 under the conditional
  law — the probabilistic content of the endpoint, PROVED);
* the clock `ℓ` of the version is continuous and strictly increasing on the relative interval `[0, L)`,
  `L = sup_m V_m`, onto the physical interval `[0, T)`, and the relative tips of `Wr` read through the chart and the
  inversion are the physical tips at `ℓ` (from the version's tip relation and `Wr = R m` before `V m`).

The conclusion is the endpoint: `L = ∞`, `T < ∞` and the physical tip at `T` is the state's point `q`.

**`bw1EndpointStatement_of_det`** (PROVED): `BW1EndpointStatement` from `BW1EndpointDetStatement` and Theorem 1.3
(at universes `u` and `0`). The remaining input `BW1EndpointDetStatement` is deterministic complex analysis (the
boundary correspondence of the state chart `g_A − W` followed by the inversion: real points outside the filled base go
to untouched real points, the junctions and flanks to the retained piece, `0` to the tip `q`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.BW1In

open Exist Exist.StagedLaw Exist.Staged Restart BW1Life Supp8.GB6

/-- **Named input (deterministic): BW1's endpoint for one sample** (p. 614–615, pathwise). For the first piece `D 0`
of BW1's program (regular through its stop, its traces not returning to `0`), ending at a threshold on the side `r`;
a physical counterflow driver `w'` continuous from `0` with a complete transient generating trace `γ`; a relative
driver `wr` continuous from `0` with a complete transient generating trace `Γ` that avoids the closed right tail
`[jR, ∞)` (`jR = −1/V̂^{0,L}_ζ`, GB6's `junctionR` of the stopped piece driver at its lifetime) when the left seed image
`V̂^{0,L}_ζ` is nondegenerate and the closed left tail `(−∞, jL]` when the right seed image is; and a clock `ℓ`,
continuous and strictly increasing on `[0, L)` onto `[0, T)` (`T` the first time the physical tip lies in the retained
set), under which the relative tips (through the state chart and the inversion) are the physical tips: then `L = ∞`,
`T < ∞` and the physical tip at `T` is the state's point `q`. -/
def BW1EndpointDetStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (t : ℝ≥0∞) (gw2 : Bool) (rest : List Instr)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (r : Bool) (w' wr : ℝ≥0 → ℝ) (γ Γ : ℝ≥0 → ℂ) (L : ℝ≥0∞) (ℓ : ℝ≥0 → ℝ≥0),
    0 < κ → κ < 4 → IsPiecewiseConstantBoundaryData b jumps →
    GW1P.PieceRegular (D 0).1 (min t (D 0).2) →
    (∀ α : ℝ≥0 → ℂ, IsGeneratingTrace (D 0).1 (D 0).2 α → ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < (D 0).2 → α v ≠ 0) →
    BW1.EndsAtThresholdSide (ExplState.run κ b jumps (bwSpec gw2 θ t rest) D 1) r →
    Continuous w' → w' 0 = 0 → IsGeneratingTrace w' ⊤ γ → Tendsto (fun s => ‖γ s‖) atTop atTop →
    Continuous wr → wr 0 = 0 → IsGeneratingTrace wr ⊤ Γ → Tendsto (fun s => ‖Γ s‖) atTop atTop →
    (baseL (BW1Prop.pieceDrv (D 0)) ((D 0).2.toNNReal : ℝ) < 0 →
      ∀ u, 0 < rightGap (junctionR (BW1Prop.pieceDrv (D 0)) ((D 0).2.toNNReal : ℝ)) (Γ u)) →
    (0 < baseR (BW1Prop.pieceDrv (D 0)) ((D 0).2.toNNReal : ℝ) →
      ∀ u, 0 < leftGap (junctionL (BW1Prop.pieceDrv (D 0)) ((D 0).2.toNNReal : ℝ)) (Γ u)) →
    StrictMonoOn ℓ {s | (s : ℝ≥0∞) < L} → ContinuousOn ℓ {s | (s : ℝ≥0∞) < L} →
    ℓ '' {s | (s : ℝ≥0∞) < L} = {u : ℝ≥0 | (u : ℝ≥0∞) <
      firstTipTime infinitySourceChart w' (SB.prefixPhysSet κ b jumps (bwSpec gw2 θ t rest) D 1)} →
    (∀ s : ℝ≥0, (s : ℝ≥0∞) < L → ∀ z : ℂ,
      ((BW1.stateChart (ExplState.run κ b jumps (bwSpec gw2 θ t rest) D 1)).trans infinitySourceChart).tipAt wr s z ↔
        infinitySourceChart.tipAt w' (ℓ s) z) →
    L = ⊤ ∧ firstTipTime infinitySourceChart w' (SB.prefixPhysSet κ b jumps (bwSpec gw2 θ t rest) D 1) < ⊤ ∧
      infinitySourceChart.tipAt w'
        (firstTipTime infinitySourceChart w' (SB.prefixPhysSet κ b jumps (bwSpec gw2 θ t rest) D 1)).toNNReal
        (BW1.statePoint (ExplState.run κ b jumps (bwSpec gw2 θ t rest) D 1))

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {θ : ℝ} {t : ℝ≥0∞} {gw2 : Bool} {rest : List Instr} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The record of a regularized piece reads the piece driver**: for a piece continuous from `0` through its stop
`min t ζ = ζ`, the record of its regularization has time `ζ` and reads the stopped piece driver on `[0, ζ]`. -/
theorem rdrv_recOf_regularize {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : GW1P.PieceRegular e.1 (min t e.2))
    (hle : e.2 ≤ t) (hfin : e.2 ≠ ⊤) :
    rtime (recOf t (StagedReg.regularize t e)) = (e.2.toNNReal : ℝ) ∧
      ∀ x ∈ Icc (0 : ℝ) (e.2.toNNReal : ℝ), rdrv (recOf t (StagedReg.regularize t e)) x = BW1Prop.pieceDrv e x := by
  have hmin : min t e.2 = e.2 := min_eq_right hle
  have hsnd := StagedReg.regularize_snd t e
  have he' := StagedReg.isRegularDriver_regularize t e
  have hfin' : min t (StagedReg.regularize t e).2 ≠ ⊤ := by rw [hsnd, hmin]; exact hfin
  have heq : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ min t e.2 → (StagedReg.regularize t e).1 s = e.1 s := fun s hs =>
    StagedReg.regularize_eq_of_le hP.1 hP.2.1 hs
  have hc' : ContinuousOn (StagedReg.regularize t e).1 {s | (s : ℝ≥0∞) ≤ min t (StagedReg.regularize t e).2} := by
    rw [hsnd]
    exact hP.2.1.congr fun s hs => heq s hs
  have hg := isDrvGood_of_continuousOn_le he' hfin' hc'
  have hrt : rtime (recOf t (StagedReg.regularize t e)) = (e.2.toNNReal : ℝ) := by
    rw [rtime_recOf]
    unfold stopTime
    rw [hsnd, hmin]
  refine ⟨hrt, fun x hx => ?_⟩
  rw [rdrv_recOf_eq he' hg hfin' (hrt ▸ hx.2)]
  have hxle : ((x.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ e.2 := by
    rw [← ENNReal.coe_toNNReal hfin]
    exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hx.2)
  rw [heq _ (hmin.symm ▸ hxle)]
  show e.1 x.toNNReal = e.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) e.2).toNNReal
  rw [min_eq_left hxle, ENNReal.toNNReal_coe]

/-- **The record's seed images and junctions are those of the stopped piece driver.** -/
theorem seeds_recOf_regularize {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : GW1P.PieceRegular e.1 (min t e.2))
    (hle : e.2 ≤ t) (hfin : e.2 ≠ ⊤) :
    markPosL (rdrv (recOf t (StagedReg.regularize t e))) (rtime (recOf t (StagedReg.regularize t e))) 0 =
        baseL (BW1Prop.pieceDrv e) (e.2.toNNReal : ℝ) ∧
      markPos (rdrv (recOf t (StagedReg.regularize t e))) (rtime (recOf t (StagedReg.regularize t e))) 0 =
        baseR (BW1Prop.pieceDrv e) (e.2.toNNReal : ℝ) ∧
      jROfRec (recOf t (StagedReg.regularize t e)) = junctionR (BW1Prop.pieceDrv e) (e.2.toNNReal : ℝ) ∧
      jLOfRec (recOf t (StagedReg.regularize t e)) = junctionL (BW1Prop.pieceDrv e) (e.2.toNNReal : ℝ) := by
  obtain ⟨hrt, hrd⟩ := rdrv_recOf_regularize hP hle hfin
  have hmin : min t e.2 = e.2 := min_eq_right hle
  have hUc : Continuous (BW1Prop.pieceDrv e) := by
    have h := hP.2.1
    rw [hmin] at h
    exact (CounterflowRange.continuous_stopped h).comp continuous_real_toNNReal
  have h0 : (0 : ℝ) ≤ (e.2.toNNReal : ℝ) := NNReal.coe_nonneg _
  have hL : markPosL (rdrv (recOf t (StagedReg.regularize t e))) (rtime (recOf t (StagedReg.regularize t e))) 0 =
      baseL (BW1Prop.pieceDrv e) (e.2.toNNReal : ℝ) := by
    rw [markPosL_zero_eq_baseL (continuous_rdrv _) (rdrv_zero _) (rtime_nonneg _), hrt]
    exact baseL_congr hUc h0 hrd
  have hR : markPos (rdrv (recOf t (StagedReg.regularize t e))) (rtime (recOf t (StagedReg.regularize t e))) 0 =
      baseR (BW1Prop.pieceDrv e) (e.2.toNNReal : ℝ) := by
    rw [markPos_zero_eq_baseR (continuous_rdrv _) (rdrv_zero _) (rtime_nonneg _), hrt]
    exact baseR_congr hUc h0 hrd
  refine ⟨hL, hR, ?_, ?_⟩
  · unfold jROfRec junctionR; rw [hL]
  · unfold jLOfRec junctionL; rw [hR]

omit mΩ [StandardBorelSpace Ω] in
/-- **BW1's record is the record of the regularized first piece.** -/
theorem bwRec_eq_recOf (ω : Ω) :
    bwRec κ b jumps (bwSpec gw2 θ t rest) E ω = recOf t (StagedReg.regularize t (E 0 ω)) := by
  have hl : (ExplState.run κ b jumps (bwSpec gw2 θ t rest)
      (fun j => StagedReg.regHist (bwSpec gw2 θ t rest) E j ω) (0 + 1)).2.2.2.1 0 ≠ none := by
    rw [GW1.launches_run_one_of_cons κ b jumps (bwSpec gw2 θ t rest) rfl]; exact Option.some_ne_none _
  exact pastMap_last_of_launch hl

/-- **BW1's endpoint from its deterministic half** (the probabilistic half — the conditional trace avoids the
protected tails — is `ae_mem_bwAvoid`). -/
theorem bw1EndpointStatement_of_det (h13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    (hdet : BW1EndpointDetStatement) : BW1EndpointStatement.{u} := by
  intro κ b jumps Ω mΩ _ P _ h W' ζ' θ t gw2 rest E hset r R V ℓ hver Wr ζr hWm hζm hcf hreg hagree
  have hset' := hset
  obtain ⟨hκ, hκ4, hb, hh, hcfW, hζ', hθ, hS⟩ := hset'
  have hpiece := BW1Prop.ae_bw1_piece_hyps h13 hκ hκ4 hb hh hS
  have hW'tr := Sec7.StripSysPath.IsCenteredCounterflowDriver.ae_hasTrace h13 hκ hcfW
  obtain ⟨_, _, _, -, -, hflW⟩ := hcfW
  have hW'reg := ae_driver_zero_continuousOn hflW
  have havoid := ae_mem_bwAvoid h13 hT13₀ hset r hWm hcf hreg
  obtain ⟨-, -, -, -, -, -, -, hverae⟩ := hver
  filter_upwards [hpiece, hW'tr, hW'reg, hζ', havoid, hverae, hreg, hagree] with ω hp hγ hW'r hζ'ω hav
    hvω hrgω hagω hω
  obtain ⟨γ, hγtr, hγtr'⟩ := hγ
  rw [hζ'ω] at hγtr hγtr'
  have hW'c : Continuous fun s => W' s ω := by
    obtain ⟨-, hc⟩ := hW'r
    rw [hζ'ω] at hc
    have huniv : {s : ℝ≥0 | (s : ℝ≥0∞) < ⊤} = univ := eq_univ_of_forall fun s => ENNReal.coe_lt_top
    rw [huniv] at hc
    exact continuousOn_univ.1 hc
  obtain ⟨-, hWc, hW0⟩ := hrgω hω
  obtain ⟨hgood, hRt, hLt⟩ := hav hω
  simp only [Set.mem_ofPred_eq] at hgood hRt hLt
  have hΓ := isGeneratingTrace_regTrace hgood
  rw [regPath_eq hWc] at hΓ
  obtain ⟨-, hmono, hcont, himg, htipR⟩ := hvω hω
  have hle := BW1Prop.le_of_endsAtThresholdSide (s := ExplState.init 0) (k := 0) hω
  have hfin := BW1Prop.ne_top_of_endsAtThresholdSide (s := ExplState.init 0) (k := 0) hω
  obtain ⟨eL, eR, ejR, ejL⟩ := seeds_recOf_regularize hp.1 hle hfin
  rw [bwRec_eq_recOf, eL, ejR] at hRt
  rw [bwRec_eq_recOf, eR, ejL] at hLt
  have htip : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ⨆ m, V m ω → ∀ z : ℂ,
      ((bwChart κ b jumps (bwSpec gw2 θ t rest) E ω).trans infinitySourceChart).tipAt (fun u => Wr u ω) s z ↔
        infinitySourceChart.tipAt (fun u => W' u ω) (ℓ ω s) z := by
    intro s hs z
    obtain ⟨m, hm⟩ := lt_iSup_iff.1 hs
    rw [tipAt_congr_of_lt _ hm (fun u hu => hagω hω m u hu) z]
    exact htipR m s hm z
  exact hdet κ b jumps θ t gw2 rest (fun j => E j ω) r (fun s => W' s ω) (fun s => Wr s ω) γ
    (regTrace fun s => Wr s ω) (⨆ m, V m ω) (ℓ ω) hκ hκ4 hb hp.1 hp.2 hω hW'c hW'r.1 hγtr (hγtr' rfl) hWc hW0
    hΓ.1 hΓ.2 hRt hLt hmono hcont himg htip

end InteractingSLE.Theorem14.BW1In
