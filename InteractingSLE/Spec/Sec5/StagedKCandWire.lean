/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedKCandFreeze
import InteractingSLE.Spec.Sec5.CrossCondStagedK2Cand

/-!
# Prop 5.9's root candidates: the killed laws from stopped representations

Packet PROVE-STAGEDK-CAND (ruling R78). This file connects `IsStoppedRep.isStageLawFarK` (`StagedKCandDisint`) to the
candidate tree of PROVE-STAGED7/PROVE-STAGED9:

* `startOn`, `IsStageLawFarK.congr_start`, `IsStoppedRep.congr_start`, **`IsStoppedRep.isStageLawFarK_of_onR`**: the
  start need only be past-measurable on the stage event (the canonical starts are determined by the switch data only
  on the reached events);
* `measurable_pieceSamp_of_isRegPiece`: the killed samples of a regular piece are measurable;
* **`measurableSet_canonR_inter_canonY`**: the canonical start of every candidate is measurable for the canonical
  past on the canonical reached event (PROVE-STAGED7's `canon_step_start`);
* **`isStageLawFarK_canon_of_rep`**, **`isStageLawFarK_canon_of_killedRep`**: the killed law of every candidate of a
  regular family from a stopped representation, or from the killed form `IsKilledStageRep` for the candidate itself;
* **`prop59StageLawFarKStatement_histSys_canon_of_rep`**: the killed stage law of the adaptive construction of any
  regular family (root experiment or node tree) from stopped representations of its candidates;
* **`tip0UnboundedStatement_of_candStoppedRep`**: Proposition 5.13's `htip0` from stopped representations of the fixed
  candidates of PROVE-PROP59-PIECES' root experiment (the hypothesis `hlaw` of PROVE-STAGED9's
  `tip0UnboundedStatement_of_candLawsK` discharged).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; `Theorem12ParamCond44Statement` (R74) enters only
through PROVE-PROP59-PIECES' code drivers.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Real
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.CrossCond.StagedKCand

open Prop59Stage Prop59System StagedAdapt Prop59Pieces Prop59Nodes Prop513TreeExtract Prop513Target Sec7.AdmCode
open Restart Sec4 Exist.StagedLaw Theorem14.StagedReg Prop513Schedule StagedCand StagedKill StagedK2

/-! ### Starts measurable on the stage event -/

section OnR

variable {Ω : Type*} {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {κ : ℝ}
  {R : Set Ω} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL} {iR : Fin nR} {y y' : Ω → Start nL nR}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

open scoped Classical in
/-- The start on the stage event, `0` off it. -/
def startOn (R : Set Ω) (y : Ω → Start nL nR) (ω : Ω) : Start nL nR := if ω ∈ R then y ω else 0

omit mΩ in
theorem startOn_of_mem {ω : Ω} (h : ω ∈ R) : startOn R y ω = y ω := by
  simp only [startOn, h, ↓reduceIte]

omit mΩ in
/-- A start measurable on the stage event gives a measurable `startOn`. -/
theorem measurable_startOn (hR : MeasurableSet[𝓠] R)
    (hyR : ∀ S : Set (Start nL nR), MeasurableSet S → MeasurableSet[𝓠] (R ∩ y ⁻¹' S)) :
    Measurable[𝓠] (startOn R y) := by
  classical
  intro S hS
  have e : startOn R y ⁻¹' S = (R ∩ y ⁻¹' S) ∪ (Rᶜ ∩ (fun _ : Ω => (0 : Start nL nR)) ⁻¹' S) := by
    ext ω
    by_cases h : ω ∈ R <;> simp [startOn, h]
  rw [e]
  exact (hyR S hS).union (hR.compl.inter (measurable_const hS))

/-- **The killed stage law only sees the start on the stage event.** -/
theorem IsStageLawFarK.congr_start (h : IsStageLawFarK κ P 𝓠 R ρL ρR iL iR y' W VL VR B ζ)
    (hy : ∀ ω ∈ R, y' ω = y ω) : IsStageLawFarK κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ := by
  refine ⟨?_, fun S hS p hp A hA hAR => ?_⟩
  · filter_upwards [h.1] with ω hω hωR
    rw [← hy ω hωR]
    exact hω hωR
  · have e : A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S} =
        A ∩ {ω | (y' ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hA', h'⟩
        exact ⟨hA', by rw [hy ω (hAR hA')]; exact h'⟩
      · rintro ⟨hA', h'⟩
        exact ⟨hA', by rw [← hy ω (hAR hA')]; exact h'⟩
    rw [e]
    exact h.2 S hS p hp A hA hAR

/-- **A stopped representation only sees the start on the stage event.** -/
theorem IsStoppedRep.congr_start {𝓕 : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL' : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR' : Fin nR → ℝ≥0 → Ω → ℝ} {B' : ℝ≥0 → Ω → ℝ}
    (h : IsStoppedRep κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ 𝓕 W' VL' VR' B') (hy : ∀ ω ∈ R, y' ω = y ω) :
    IsStoppedRep κ P 𝓠 R ρL ρR iL iR y' W VL VR B ζ 𝓕 W' VL' VR' B' := by
  refine ⟨h.le0, h.brownian, h.adapted_W, h.adapted_VL, h.adapted_VR, ?_⟩
  filter_upwards [h.ae_path] with ω hω hωR
  rw [hy ω hωR]
  exact hω hωR

end OnR

section OnRMain

variable {Ω : Type} {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {nL nR : ℕ} {κ : ℝ} {R : Set Ω} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL}
  {iR : Fin nR} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {𝓕 : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL' : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR' : Fin nR → ℝ≥0 → Ω → ℝ} {B' : ℝ≥0 → Ω → ℝ}

/-- **The killed law from a stopped representation, with the start past-measurable on the stage event only.** -/
theorem IsStoppedRep.isStageLawFarK_of_onR (hκ : 0 < κ)
    (h : IsStoppedRep κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ 𝓕 W' VL' VR' B') (hR : MeasurableSet[𝓠] R)
    (hyR : ∀ S : Set (Start nL nR), MeasurableSet S → MeasurableSet[𝓠] (R ∩ y ⁻¹' S))
    (hobs : Measurable (pieceSamp W VL VR ζ)) :
    IsStageLawFarK κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ :=
  IsStageLawFarK.congr_start
    ((h.congr_start fun _ hω => startOn_of_mem hω).isStageLawFarK hκ hR (measurable_startOn hR hyR) hobs)
    fun _ hω => startOn_of_mem hω

end OnRMain

/-! ### Regular pieces and the canonical tree -/

section Tree

variable {Ω : Type*} (𝓑 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {nL₀ nR₀ : ℕ}

/-- **The killed samples of a regular piece are measurable.** -/
theorem measurable_pieceSamp_of_isRegPiece {nL nR : ℕ} {p : Piece Ω nL nR} (hp : IsRegPiece p) :
    Measurable (pieceSamp p.W p.VL p.VR p.ζ) := by
  refine hp.ζ.prodMk (measurable_pi_iff.2 fun q => ?_)
  have hlt : MeasurableSet {ω | ((q : ℝ≥0) : ℝ≥0∞) < p.ζ ω} := measurableSet_lt measurable_const hp.ζ
  have hsec : ∀ {X : ℝ≥0 → Ω → ℝ}, Measurable (Function.uncurry X) → Measurable (X q) := fun hX =>
    hX.comp (measurable_const.prodMk measurable_id)
  refine Measurable.ite hlt ((hsec hp.W).prodMk ((measurable_pi_iff.2 fun i => hsec (hp.VL i)).prodMk
    (measurable_pi_iff.2 fun k => hsec (hp.VR k)))) measurable_const

variable {𝓑} {cand : CandFam Ω nL₀ nR₀} {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀} {hnR : 0 < nR₀}
  {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)} {R₀ : Set Ω}

/-- **The canonical start is past-measurable on the canonical reached event** (at the root by hypothesis; after a
switch at `q`, on the switch event of the grid point `G n m = q` the start is the next start, PROVE-STAGED7's
`canon_step_start`, a generator of the switch σ-algebra). -/
theorem measurableSet_canonR_inter_canonY (hfam : IsRegFam cand) (hy₀ : Measurable y₀)
    (hR₀ : MeasurableSet[𝓑] R₀)
    (hy₀𝓑 : ∀ S : Set (Start (nL₀ + 0) (nR₀ + 0)), MeasurableSet S → MeasurableSet[𝓑] (R₀ ∩ y₀ ⁻¹' S)) :
    ∀ (j : ℕ) (t : Fin j → ℝ≥0) (S : Set (Start (nL₀ + j) (nR₀ + j))), MeasurableSet S →
      MeasurableSet[canonQ 𝓑 cand G hnL hnR y₀ j t]
        (canonR cand G hnL hnR y₀ R₀ j t ∩ canonY cand y₀ j t ⁻¹' S)
  | 0, t, S, hS => by
    simp only [canonR, canonY_zero]
    exact hy₀𝓑 S hS
  | j + 1, t, S, hS => by
    rw [← Fin.snoc_init_self t]
    set t₀ := Fin.init t
    set q := t (Fin.last j)
    rw [canonQ_snoc, canonR_snoc]
    have e : (canonR cand G hnL hnR y₀ R₀ j t₀ ∩
        ⋃ (n : ℕ) (m : ℕ) (_ : G n m = q), swEv G hnL hnR j (candStage cand (canonY cand y₀) j t₀) n m) ∩
          canonY cand y₀ (j + 1) (Fin.snoc (α := fun _ => ℝ≥0) t₀ q) ⁻¹' S =
        ⋃ (n : ℕ) (m : ℕ) (_ : G n m = q), canonR cand G hnL hnR y₀ R₀ j t₀ ∩
          (swEv G hnL hnR j (candStage cand (canonY cand y₀) j t₀) n m ∩
            {ω | (swT G hnL hnR j (candStage cand (canonY cand y₀) j t₀) n ω,
              nextStart G hnL hnR j (candStage cand (canonY cand y₀) j t₀) n ω) ∈ univ ×ˢ S}) := by
      ext ω
      simp only [mem_inter_iff, mem_iUnion, mem_preimage, mem_ofPred_eq, mem_prod, mem_univ, true_and]
      constructor
      · rintro ⟨⟨hR, n, m, hnm, hsw⟩, hS'⟩
        refine ⟨n, m, hnm, hR, hsw, ?_⟩
        rw [(canon_step_start (R₀ := R₀) hfam hy₀ j t₀ n m hR hsw).2, hnm]
        exact hS'
      · rintro ⟨n, m, hnm, hR, hsw, hS'⟩
        refine ⟨⟨hR, n, m, hnm, hsw⟩, ?_⟩
        rw [(canon_step_start (R₀ := R₀) hfam hy₀ j t₀ n m hR hsw).2, hnm] at hS'
        exact hS'
    rw [e]
    refine @MeasurableSet.iUnion Ω _ _ _ _ fun n => @MeasurableSet.iUnion Ω _ _ _ _ fun m =>
      @MeasurableSet.iUnion Ω _ _ _ _ fun hnm => ?_
    refine MeasurableSet.inter (le_sup_left (a := canonQ 𝓑 cand G hnL hnR y₀ j t₀) _
      (measurableSet_canonR hR₀ j t₀)) ?_
    refine le_sup_right (a := canonQ 𝓑 cand G hnL hnR y₀ j t₀) _ ?_
    rw [← hnm]
    exact measurableSet_swSigma _ (MeasurableSet.univ.prod hS)

end Tree

/-! ### The killed laws of the canonical candidates -/

section Canon

variable {Ω : Type} (𝓑 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {nL₀ nR₀ : ℕ} {κ : ℝ} {cand : CandFam Ω nL₀ nR₀} {G : ℕ → ℕ → ℝ≥0}
  {hnL : 0 < nL₀} {hnR : 0 < nR₀} {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)} {R₀ : Set Ω}

/-- **The killed law of a canonical candidate from its stopped representation** (any regular family, any weights and
far marks): the canonical reached event and start are past-measurable on the event (`measurableSet_canonR`,
`measurableSet_canonR_inter_canonY`), the killed samples are measurable (`measurable_pieceSamp_of_isRegPiece`), so
`IsStoppedRep.isStageLawFarK_of_onR` applies. -/
theorem isStageLawFarK_canon_of_rep (hκ : 0 < κ) (hfam : IsRegFam cand) (hy₀ : Measurable y₀)
    (hR₀ : MeasurableSet[𝓑] R₀)
    (hy₀𝓑 : ∀ S : Set (Start (nL₀ + 0) (nR₀ + 0)), MeasurableSet S → MeasurableSet[𝓑] (R₀ ∩ y₀ ⁻¹' S))
    (j : ℕ) (t : Fin j → ℝ≥0) {ρL : Fin (nL₀ + j) → ℝ} {ρR : Fin (nR₀ + j) → ℝ} {iL : Fin (nL₀ + j)}
    {iR : Fin (nR₀ + j)}
    (hrep : ∃ (𝓕 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin (nL₀ + j) → ℝ≥0 → Ω → ℝ)
      (VR' : Fin (nR₀ + j) → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
      IsStoppedRep κ P (canonQ 𝓑 cand G hnL hnR y₀ j t) (canonR cand G hnL hnR y₀ R₀ j t) ρL ρR iL iR
        (canonY cand y₀ j t) (cand j t).W (cand j t).VL (cand j t).VR (cand j t).B (cand j t).ζ 𝓕 W' VL' VR' B') :
    IsStageLawFarK κ P (canonQ 𝓑 cand G hnL hnR y₀ j t) (canonR cand G hnL hnR y₀ R₀ j t) ρL ρR iL iR
      (canonY cand y₀ j t) (cand j t).W (cand j t).VL (cand j t).VR (cand j t).B (cand j t).ζ := by
  obtain ⟨𝓕, W', VL', VR', B', h⟩ := hrep
  exact h.isStageLawFarK_of_onR hκ (measurableSet_canonR hR₀ j t)
    (measurableSet_canonR_inter_canonY hfam hy₀ hR₀ hy₀𝓑 j t) (measurable_pieceSamp_of_isRegPiece (hfam j t))

/-- **The killed law of a canonical candidate from the killed form of its stopped conditional law**
(`IsKilledStageRep`, stated for the killed candidate itself; frozen at its left limit by
`IsKilledStageRep.isStoppedRep`). -/
theorem isStageLawFarK_canon_of_killedRep (hκ : 0 < κ) (hfam : IsRegFam cand) (hy₀ : Measurable y₀)
    (hR₀ : MeasurableSet[𝓑] R₀)
    (hy₀𝓑 : ∀ S : Set (Start (nL₀ + 0) (nR₀ + 0)), MeasurableSet S → MeasurableSet[𝓑] (R₀ ∩ y₀ ⁻¹' S))
    (j : ℕ) (t : Fin j → ℝ≥0) {ρL : Fin (nL₀ + j) → ℝ} {ρR : Fin (nR₀ + j) → ℝ} {iL : Fin (nL₀ + j)}
    {iR : Fin (nR₀ + j)}
    (hrep : ∃ (𝓕 : Filtration ℝ≥0 mΩ) (B' : ℝ≥0 → Ω → ℝ),
      IsKilledStageRep κ P (canonQ 𝓑 cand G hnL hnR y₀ j t) (canonR cand G hnL hnR y₀ R₀ j t) ρL ρR iL iR
        (canonY cand y₀ j t) (cand j t).W (cand j t).VL (cand j t).VR (cand j t).B (cand j t).ζ 𝓕 B') :
    IsStageLawFarK κ P (canonQ 𝓑 cand G hnL hnR y₀ j t) (canonR cand G hnL hnR y₀ R₀ j t) ρL ρR iL iR
      (canonY cand y₀ j t) (cand j t).W (cand j t).VL (cand j t).VR (cand j t).B (cand j t).ζ := by
  obtain ⟨𝓕, B', h⟩ := hrep
  exact isStageLawFarK_canon_of_rep 𝓑 hκ hfam hy₀ hR₀ hy₀𝓑 j t ⟨𝓕, _, _, _, B', h.isStoppedRep⟩

/-- **The killed stage law of the adaptive construction from stopped representations of the candidates** (any regular
family — PROVE-PROP59-PIECES' root experiment or a node tree of PROVE-PROP59-NODES §5.1): if every fixed candidate has
a stopped representation (stage word, far marks the last indices) for its canonical past, reached event and start, then
`Prop59StageLawFarKStatement` holds for `histSys cand G … y₀ R₀ 𝓑` (PROVE-STAGED9's
`prop59StageLawFarKStatement_histSys_canon`). -/
theorem prop59StageLawFarKStatement_histSys_canon_of_rep {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ} (hκ : 0 < κ)
    (hfam : IsRegFam cand) (hy₀ : Measurable y₀) (hR₀ : MeasurableSet[𝓑] R₀)
    (hy₀𝓑 : ∀ S : Set (Start (nL₀ + 0) (nR₀ + 0)), MeasurableSet S → MeasurableSet[𝓑] (R₀ ∩ y₀ ⁻¹' S))
    (hrep : ∀ (j : ℕ) (t : Fin j → ℝ≥0), ∃ (𝓕 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ)
      (VL' : Fin (nL₀ + j) → ℝ≥0 → Ω → ℝ) (VR' : Fin (nR₀ + j) → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
      IsStoppedRep κ P (canonQ 𝓑 cand G hnL hnR y₀ j t) (canonR cand G hnL hnR y₀ R₀ j t) (stageρL κ ρL₀ j)
        (stageρR κ ρR₀ j) (farL (Nat.lt_of_lt_of_le hnL (Nat.le_add_right nL₀ j)))
        (farR (Nat.lt_of_lt_of_le hnR (Nat.le_add_right nR₀ j))) (canonY cand y₀ j t) (cand j t).W
        (cand j t).VL (cand j t).VR (cand j t).B (cand j t).ζ 𝓕 W' VL' VR' B') :
    Prop59StageLawFarKStatement κ P hnL hnR ρL₀ ρR₀ (histSys cand G hnL hnR y₀ R₀ 𝓑) :=
  prop59StageLawFarKStatement_histSys_canon hfam hy₀ hR₀ fun j t =>
    isStageLawFarK_canon_of_rep 𝓑 hκ hfam hy₀ hR₀ hy₀𝓑 j t (hrep j t)

end Canon

/-! ### Proposition 5.13's root tip assertion -/

section Tip

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa] [StandardBorelSpace Ωa]
  (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (E : Schedule → ℕ → Ω → Driver)

/-- **Proposition 5.13's root tip assertion from stopped representations of the fixed candidates** of the root
experiment with the canonical dilated root marks. Compared with PROVE-STAGED9's `tip0UnboundedStatement_of_candLawsK`,
the per-candidate killed laws `hlaw` are replaced by: the root start is measurable for the root past `base q`
(`hbaseY`), and every fixed candidate has a stopped representation for its canonical past, reached event and start
(`hrep`: Aux. lemma 122's form of its conditional law, stopped at its first far contact). -/
theorem tip0UnboundedStatement_of_candStoppedRep (hA : PartAInputsSixteenDiv) (hhm : Measurable h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base : ℚ → MeasurableSpace (Ω × Ωa))
    (hbase : ∀ q, base q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hbaseY : ∀ q : ℚ, Measurable[base q]
      (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) (Ωa := Ωa) q))
    (hrep : ∀ q : ℚ, 0 < q → ∀ j t, ∃ (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ωa)))
      (W' : ℝ≥0 → Ω × Ωa → ℝ)
      (VL' : Fin (rootNL (sourceWord (x₀ := x₀) hκ hb) + j) → ℝ≥0 → Ω × Ωa → ℝ)
      (VR' : Fin (rootNR (sourceWord (x₀ := x₀) hκ hb) + j) → ℝ≥0 → Ω × Ωa → ℝ) (B' : ℝ≥0 → Ω × Ωa → ℝ),
      IsStoppedRep κ (P.prod Pa)
        (canonQ (base q) (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) noise (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
          (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) j t)
        (canonR (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) noise (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
          (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ j t)
        (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) j) (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) j)
        (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ j)))
        (farR (Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ j)))
        (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) noise (Ωa := Ωa) q) (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ)
            (canonXR x₀ hκ hb W ζ) q) j t)
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
          (Ωa := Ωa) q j t).W
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
          (Ωa := Ωa) q j t).VL
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
          (Ωa := Ωa) q j t).VR
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
          (Ωa := Ωa) q j t).B
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
          (Ωa := Ωa) q j t).ζ 𝓕 W' VL' VR' B') :
    Prop59Tips.Tip0UnboundedStatement P W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime) := by
  have hcfm := measurable_cfHistory_of_strip hcf
  have hxL : ∀ q, Measurable (canonXL x₀ hκ hb W ζ q) := fun _ => measurable_pi_iff.2 fun i =>
    ((measurable_rootLam _).comp hcfm).mul ((measurable_pi_apply i).comp ((measurable_rootXL hκ hb _).comp hcfm))
  have hxR : ∀ q, Measurable (canonXR x₀ hκ hb W ζ q) := fun _ => measurable_pi_iff.2 fun j =>
    ((measurable_rootLam _).comp hcfm).mul ((measurable_pi_apply j).comp ((measurable_rootXR hκ hb _).comp hcfm))
  refine tip0UnboundedStatement_of_candLawsK x₀ h44 hκ hκ4 hb P Pa h W ζ E hA hhm hG hcf hE hR noise base hbase
    fun q hq j t => ?_
  exact isStageLawFarK_canon_of_rep (base q) hκ
    (isRegFam_rootCand x₀ h44 hκ hκ4 hb hhm hcf (fun _ => (measurable_rootLam _).comp hcfm)
      (fun _ _ => rootLam_pos _ _) hxL hxR q)
    (measurable_rootStart x₀ hκ hb hxL hxR q) MeasurableSet.univ
    (fun S hS => by rw [univ_inter]; exact hbaseY q hS) j t (hrep q hq j t)

end Tip

end InteractingSLE.Sec5.CrossCond.StagedKCand
