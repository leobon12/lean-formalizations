/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw4Def
import InteractingSLE.Spec.Exist.StagedLaw3Main
import InteractingSLE.Spec.Exist.Param12Canonical
import InteractingSLE.Spec.Supplement.GW1PieceProper
import InteractingSLE.Spec.Sec7.ContinuityProb3Coding
import InteractingSLE.Spec.Sec5.Lemma56Stages

/-!
# R51's companion: staged families whose launched pieces are continuous curves almost surely

Packet PROVE-STAGEDLAW4 (ruling R51). The frozen `IsStagedHistory` constrains a piece launched after the first one only
through its conditional law; R51 adds `StagedPiecesRegular` (`StagedLaw4Def`) to the Theorem 1.4 anchors and asks the
companion to produce families that also satisfy it. The families built by PROVE-STAGED/STAGEDLAW3 have drivers that
are regular at **every** sample (`Staged.IsRegularDriver`); for such a driver the regularity of its piece is a Borel
event:

* **`pieceRegular_iff_regCond`** — for a regular driver `e` and an own time `t`, the piece's regularity
  (`GW1P.PieceRegular e.1 (min t e.2)`) is equivalent to `RegCond t e`: the record of the stopped driver is good
  (`LocalExt.IsDrvGood`: rational samples uniformly continuous; asked only at a finite stop) and `(e.1, min t e.2)`
  lies in the Borel trace set `Sec7.RandRestart.traceSet` (PROVE-RANDRESTART2, PROVE-T14-IN, PROVE-TRACECODE);
* **`measurableSet_regCond`** — `RegCond` is an event for a measurable regular family;
* **`ae_pieceRegular_of_regular`** — hence the regularity of each launched piece passes from the conditional laws
  (`GW1P.ae_condExpKernel_pieceRegular`, Theorem 1.3) to `P` (`Sec5.Lemma56Stages.ae_of_ae_condExpKernel`); the launch
  event is decided by the state before the instruction, which the conditional kernel fixes (`ae_ae_run_eq`);
* **`stagedPiecesRegular_of_regular`**, **`exists_isStagedHistory_regular_of_param`**,
  **`exists_isStagedHistory_regular_of_thm12_thm13`** — the strengthened companion from Theorems 1.2–1.3 (frozen
  types);
* `StagedPiecesRegular.ae_pieceRegular` — the converse reading in GW1P's form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open Staged Sec7.RandRestart Theorem14.GW1P

/-! ### The regularity of a regular driver's piece is a Borel condition -/

section Cond

variable {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The Borel regularity condition** of a piece with driver `e` run for own time `t`: at a finite stop the record of
the stopped driver is good, and the trace event holds on `[0, min t ζ]` (`traceSet`). -/
def RegCond (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  (min t e.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf t e))) ∧ (e.1, min t e.2) ∈ traceSet

/-- A good record makes the driver continuous up to the stop. -/
theorem continuousOn_le_of_isDrvGood (he : IsRegularDriver e) (hg : LocalExt.IsDrvGood (recHist (recOf t e))) :
    ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ min t e.2} := by
  have hc : Continuous (retOf t e).1 := by
    have h1 : (retOf t e).1 = LocalExt.histDrv (recHist (recOf t e)) :=
      funext fun s => (histDrv_recHist he hg s).symm
    rw [h1]
    exact LocalExt.continuous_histDrv _
  refine hc.continuousOn.congr fun s (hs : (s : ℝ≥0∞) ≤ min t e.2) => ?_
  change e.1 s = e.1 (min (s : ℝ≥0∞) (min t e.2)).toNNReal
  rw [min_eq_left hs, ENNReal.toNNReal_coe]

/-- A driver continuous up to a finite stop has a good record. -/
theorem isDrvGood_of_continuousOn_le (he : IsRegularDriver e) (hfin : min t e.2 ≠ ⊤)
    (hc : ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ min t e.2}) : LocalExt.IsDrvGood (recHist (recOf t e)) := by
  have hle : ∀ x ∈ Icc (0 : ℝ≥0) (min t e.2).toNNReal, (x : ℝ≥0∞) ≤ min t e.2 := fun x hx => by
    rw [← ENNReal.coe_toNNReal hfin]
    exact ENNReal.coe_le_coe.2 hx.2
  refine LocalExt.isDrvGood_of_continuousOn (g := (retOf t e).1) (T := (min t e.2).toNNReal) ?_ (fun q => ?_) ?_
  · have heq : EqOn (retOf t e).1 e.1 (Icc 0 (min t e.2).toNNReal) := fun x hx => by
      change e.1 (min (x : ℝ≥0∞) (min t e.2)).toNNReal = e.1 x
      rw [min_eq_left (hle x hx), ENNReal.toNNReal_coe]
    exact (hc.mono fun x hx => hle x hx).congr heq
  · rw [readRec_sample, retOf_eq_min hfin]
  · change e.1 (min ((0 : ℝ≥0) : ℝ≥0∞) (min t e.2)).toNNReal = 0
    rw [ENNReal.coe_zero, min_eq_left (zero_le (a := min t e.2)), ENNReal.toNNReal_zero]
    exact he.2.1

/-- A regular driver is continuous strictly before the stop. -/
theorem continuousOn_lt_min (he : IsRegularDriver e) (t : ℝ≥0∞) :
    ContinuousOn e.1 {s | (s : ℝ≥0∞) < min t e.2} :=
  he.1.mono fun _ (hs : _ < min t e.2) => (lt_of_lt_of_le hs (min_le_right t e.2) : _ < e.2)

/-- Continuity up to the stop gives the left limit at a finite positive stop. -/
theorem exists_tendsto_of_continuousOn_le {w : ℝ≥0 → ℝ} {S : ℝ≥0∞}
    (hc : ContinuousOn w {s | (s : ℝ≥0∞) ≤ S}) :
    0 < S → S < ⊤ → ∃ w₀ : ℝ, Tendsto w (𝓝[<] S.toNNReal) (𝓝 w₀) := by
  intro _ hS
  have hmem : S.toNNReal ∈ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ S} := by
    show ((S.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ S
    rw [ENNReal.coe_toNNReal hS.ne]
  refine ⟨w S.toNNReal, ((hc _ hmem).tendsto).mono_left (nhdsWithin_mono _ fun s (hs : s < S.toNNReal) => ?_)⟩
  show (s : ℝ≥0∞) ≤ S
  rw [← ENNReal.coe_toNNReal hS.ne]
  exact ENNReal.coe_le_coe.2 hs.le

/-- **The regularity of a regular driver's piece is the Borel condition `RegCond`.** -/
theorem pieceRegular_iff_regCond (he : IsRegularDriver e) (t : ℝ≥0∞) :
    PieceRegular e.1 (min t e.2) ↔ RegCond t e := by
  constructor
  · rintro ⟨-, hc, hη⟩
    refine ⟨fun hfin => isDrvGood_of_continuousOn_le he hfin hc, ?_⟩
    rw [mem_traceSet_iff (continuousOn_lt_min he t) he.2.1 (exists_tendsto_of_continuousOn_le hc)]
    exact hη
  · rintro ⟨hg, htr⟩
    have hc : ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ min t e.2} := by
      by_cases hfin : min t e.2 = ⊤
      · have hζ : e.2 = ⊤ := top_unique (hfin ▸ min_le_right t e.2)
        refine he.1.mono fun s _ => ?_
        show (s : ℝ≥0∞) < e.2
        rw [hζ]
        exact ENNReal.coe_lt_top
      · exact continuousOn_le_of_isDrvGood he (hg hfin)
    refine ⟨he.2.1, hc, ?_⟩
    rw [mem_traceSet_iff (continuousOn_lt_min he t) he.2.1 (exists_tendsto_of_continuousOn_le hc)] at htr
    exact htr

end Cond

/-- **`RegCond` is an event** for a measurable family of regular drivers. -/
theorem measurableSet_regCond {Ω : Type*} [MeasurableSpace Ω] {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : Measurable E)
    (hreg : ∀ ω, IsRegularDriver (E ω)) (t : ℝ≥0∞) : MeasurableSet {ω | RegCond t (E ω)} := by
  have hζ : Measurable fun ω => min t (E ω).2 := measurable_const.min (measurable_snd.comp hE)
  have hA : MeasurableSet {ω | min t (E ω).2 = ⊤} := hζ (measurableSet_singleton ⊤)
  have hB : MeasurableSet {ω | LocalExt.IsDrvGood (recHist (recOf t (E ω)))} :=
    (measurable_recHist.comp (measurable_recOf hE hreg t)) LocalExt.measurableSet_isDrvGood
  have h1 : MeasurableSet {ω | min t (E ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf t (E ω)))} := by
    convert hA.union hB using 1
    ext ω
    simp only [mem_ofPred_eq, mem_union, ne_eq]
    tauto
  have h2 : MeasurableSet {ω | ((E ω).1, min t (E ω).2) ∈ traceSet} :=
    ((measurable_fst.comp hE).prodMk hζ) measurableSet_traceSet
  exact h1.inter h2

/-! ### From the conditional laws to `P` -/

section Pass

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **Every launched piece of a staged history with everywhere regular drivers is `P`-a.s. regular** (Theorem 1.3
under the conditional laws; the regularity event is Borel by `pieceRegular_iff_regCond`). -/
theorem ae_pieceRegular_of_regular (h13 : Theorem13Statement.{u}) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hS : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ k ω, IsRegularDriver (E k ω)) (k : ℕ) :
    ∀ᵐ ω ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (E k ω).1 (min (instrTime spec k) (E k ω).2) := by
  set t := instrTime spec k with ht
  set L : Set Ω := {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} with hLdef
  have hL : MeasurableSet L := (runMeasStatement κ b jumps hb spec E hS.1 hreg k).1
  set G : Set Ω := Lᶜ ∪ {ω | RegCond t (E k ω)} with hGdef
  have hG : MeasurableSet G := hL.compl.union (measurableSet_regCond (hS.1 k) (hreg k) t)
  have hker : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), ω ∈ G := by
    filter_upwards [ae_ae_run_eq (P := P) runMeasStatement hb spec (k := k) (fun j _ => hS.1 j)
      (fun j _ => hreg j), ae_condExpKernel_pieceRegular h13 hκ hS k] with ω₀ hrun hpr
    rcases hl : (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k with _ | ⟨c, θ⟩
    · filter_upwards [hrun] with ω hω
      refine Or.inl fun hωL => hωL ?_
      show (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none
      rw [congrFun (launches_run_succ_of_run_eq spec hω) k, hl]
    · filter_upwards [hpr c θ hl] with ω hω
      exact Or.inr ((pieceRegular_iff_regCond (hreg k ω) t).1 hω)
  filter_upwards [Sec5.Lemma56Stages.ae_of_ae_condExpKernel (hS.2.1 k) hG hker] with ω hω c θ hl
  rcases hω with hω | hω
  · refine absurd ?_ hω
    show (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none
    rw [hl]
    exact Option.some_ne_none _
  · exact (pieceRegular_iff_regCond (hreg k ω) t).2 hω

/-- **A staged history with everywhere regular drivers is `StagedPiecesRegular`** (from Theorem 1.3). -/
theorem stagedPiecesRegular_of_regular (h13 : Theorem13Statement.{u}) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hS : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ k ω, IsRegularDriver (E k ω)) : StagedPiecesRegular κ b jumps P spec E := by
  have hall : ∀ᵐ ω ∂P, ∀ (k : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (E k ω).1 (min (instrTime spec k) (E k ω).2) :=
    ae_all_iff.2 fun k => ae_pieceRegular_of_regular h13 hκ hb hS hreg k
  filter_upwards [hall] with ω hω k θ t c hk hl
  have ht : instrTime spec k = t := by simp [instrTime, hk]
  have hr := hω k c θ hl
  rw [ht] at hr
  exact hr

end Pass

/-- **`StagedPiecesRegular` in GW1P's form**: almost surely every launched piece has regular data for its own time
`instrTime spec k`. -/
theorem _root_.InteractingSLE.StagedPiecesRegular.ae_pieceRegular {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P spec E) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (E k ω).1 (min (instrTime spec k) (E k ω).2) := by
  filter_upwards [hR] with ω hω k c θ hl
  exact hω k θ (instrTime spec k) c (eq_launch_of_launches spec (fun j => E j ω) hl).1 hl

/-! ### The strengthened companion -/

/-- The constant zero driver with lifetime `0` (the filler for programs that are not boundary-continued) gives a
`StagedPiecesRegular` family: every stop is `0`. -/
theorem stagedPiecesRegular_zero (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (spec : ExplSpec) :
    StagedPiecesRegular κ b jumps P spec (fun _ _ => ((0 : ℝ≥0 → ℝ), (0 : ℝ≥0∞))) := by
  refine Eventually.of_forall fun ω k θ t c _ _ => ?_
  have h0 : min t (0 : ℝ≥0∞) = 0 := min_eq_right (zero_le (a := t))
  refine ⟨rfl, ?_, fun _ => 0, ⟨rfl, continuousOn_const, fun s hs => ?_⟩, fun htop => ?_⟩
  · exact continuousOn_const
  · exact absurd (h0 ▸ hs) (ENNReal.not_lt_zero)
  · exact absurd (h0 ▸ htop) ENNReal.zero_ne_top

/-- **R51's companion from Theorems 1.2 (parametric) and 1.3, for every program**: one family that is
`StagedPiecesRegular` for every program and realizes every boundary-continued staged history. -/
theorem exists_isStagedHistory_regular_all_of_param (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) :
    ∃ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ spec : ExplSpec,
      StagedPiecesRegular κ b jumps P spec (E spec) ∧
        (IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec)) := by
  classical
  have hR := regularStagedHistoryConstructionStatement_of_param h12p h13 κ hκ hκ4 b jumps hb P h hh
  refine ⟨fun spec => if hs : IsBoundaryContinuedProgram spec.2.2 then (hR spec hs).choose
    else fun _ _ => ((0 : ℝ≥0 → ℝ), (0 : ℝ≥0∞)), fun spec => ?_⟩
  by_cases hs : IsBoundaryContinuedProgram spec.2.2
  · simp only [hs, ↓reduceDIte]
    obtain ⟨hS, hreg⟩ := (hR spec hs).choose_spec
    exact ⟨stagedPiecesRegular_of_regular h13 hκ hb hS hreg, fun _ => hS⟩
  · simp only [hs, ↓reduceDIte]
    exact ⟨stagedPiecesRegular_zero κ b jumps P spec, fun h' => h'.elim⟩

/-- **R51's companion from Theorems 1.2 (parametric) and 1.3**: families realizing every boundary-continued staged
history whose launched pieces are almost surely continuous curves. -/
theorem exists_isStagedHistory_regular_of_param (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) :
    ∃ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) ∧ StagedPiecesRegular κ b jumps P spec (E spec) := by
  obtain ⟨E, hE⟩ := exists_isStagedHistory_regular_all_of_param h12p h13 hκ hκ4 b jumps hb hh
  exact ⟨E, fun spec hs => ⟨(hE spec).2 hs, (hE spec).1⟩⟩

/-- **R51's companion from Theorems 1.2–1.3 (frozen types)**, in the provider shape of `exists_isStagedHistory` (version
2: the families are also `StagedPiecesRegular`). Conditional helper; not the provider. -/
theorem exists_isStagedHistory_regular_of_thm12_thm13 (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) ∧ StagedPiecesRegular κ b jumps P spec (E spec) :=
  exists_isStagedHistory_regular_of_param (Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13 hκ hκ4 b
    jumps hb hh

/-- **R51's companion from Theorems 1.2–1.3 (frozen types), for every program** (`StagedPiecesRegular` for every
program; the staged-history clause for the boundary-continued ones). Conditional helper; not the provider. -/
theorem exists_isStagedHistory_regular_all_of_thm12_thm13 (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ spec : ExplSpec,
      StagedPiecesRegular κ b jumps P spec (E spec) ∧
        (IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec)) :=
  exists_isStagedHistory_regular_all_of_param (Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13 hκ hκ4 b
    jumps hb hh

end StagedLaw

end Exist

end InteractingSLE
