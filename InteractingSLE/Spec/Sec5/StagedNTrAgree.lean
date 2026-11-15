/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNTrGam
import InteractingSLE.Spec.Wire.Thm12NightStage0

/-!
# Prop 5.9's node laws: PROVE-PROP59-NODETREE's node experiment is read on `Gam`

Packet PROVE-STAGED-NODETRANSFER. The target side of the transfer of a node candidate's comparison clause: at almost
every sample `ω'` of `Ω × Ωa`, the node tree `nodeD` agrees with the node tree `gamNodeData` on `Gam` at the pair
`pieceZ ω' = (qField ω'.1, cfHistory ω'.1)` (`agreeAt_nodeD_gamNodeData`; the two good sets hold almost surely,
`ae_nodeGood_pieceZ`). Hence the node candidates, starts, initial events and tip marks agree there
(**`ae_nodeAgree`**), the canonical pasts lie in the a.e.-comap of `Gam`'s (**`nodeQ_le_aeComap`**) and the reached
events agree almost surely (`nodeR_ae_eq`).

* `PieceAt.reindex`, `PieceAt.scale`, `PieceAt.lift`: agreement survives PROVE-PROP59-NODES' reindexing, the Brownian
  dilation and the lift to `Ω × Ωa`;
* `qPathF_eq_fst`, `nodeAlpha_eq_gam`: the flag candidate paths read only the field.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Real
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.CrossCond.StagedNTr

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged Sec7.AdmCode Restart
open LawUnique GlueCond CrossCond.Word49 Prop59System Prop59Stage Prop59Pieces Prop59Nodes Prop59NodeTree
open StagedCand StagedKCand StagedKill StagedRepLater StagedRepJ
open Sec4 (IsStripGFF IsStripCounterflowDriver)

/-! ### Agreement through reindexing, dilation and lift -/

section PieceAt

variable {Ω Ω' : Type*}

theorem PieceAt.reindex {a b c d : ℕ} (h₁ : a = b) (h₂ : c = d) {p : Piece Ω a c} {p' : Piece Ω' a c} {ω : Ω}
    {ω' : Ω'} (h : PieceAt p p' ω ω') : PieceAt (reindexPiece h₁ h₂ p) (reindexPiece h₁ h₂ p') ω ω' :=
  ⟨h.W, fun _ u => h.VL _ u, fun _ u => h.VR _ u, h.ζ, h.clk⟩

theorem PieceAt.scale {nL nR : ℕ} {p : Piece Ω nL nR} {p' : Piece Ω' nL nR} {ω : Ω} {ω' : Ω'} {c : Ω → ℝ≥0}
    {c' : Ω' → ℝ≥0} (h : PieceAt p p' ω ω') (hc : c ω = c' ω') :
    PieceAt (scalePiece c p) (scalePiece c' p') ω ω' where
  W u := by simp only [scalePiece, hc, h.W]
  VL i u := by simp only [scalePiece, hc, h.VL]
  VR k u := by simp only [scalePiece, hc, h.VR]
  ζ := by simp only [scalePiece, hc, h.ζ]
  clk := by simp only [scalePiece, hc, h.clk]

theorem PieceAt.lift {Ωa : Type*} {nL nR : ℕ} {p : Piece Ω nL nR} {p' : Piece Ω' nL nR} {ω' : Ω × Ωa} {γ : Ω'}
    (h : PieceAt p p' ω'.1 γ) : PieceAt (liftPiece (Ωa := Ωa) p) p' ω' γ :=
  ⟨h.W, h.VL, h.VR, h.ζ, h.clk⟩

end PieceAt

/-! ### The flag candidate paths read only the field -/

theorem qPathF_eq_fst {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (h44 : Theorem12ParamCond44Statement.{0}) (c : BoundaryWord)
    {Ω : Type*} (F : Ω → DistOn upperHalfPlaneOpens) (fl : ℕ → Bool) (j : ℕ) (t : Fin j → ℝ≥0) (ω : Ω)
    (y : HistorySpace 0 0) :
    qPathF h44 hκ hκ4 c F fl j t ω = qPathF h44 hκ hκ4 c Prod.fst fl j t ((F ω, y) : Gam) := by
  have e := continuedDriver_congr (E := codeFam h44 hκ hκ4 c F (candSchedF fl j t))
    (E' := codeFam h44 hκ hκ4 c Prod.fst (candSchedF fl j t)) (ω := ω) (ω' := ((F ω, y) : Gam)) (fun _ => rfl) 0 0
    (scheduleList (candSchedF fl j t))
  funext u
  show LP.traceAt u.toNNReal (continuedDriver (codeFam h44 hκ hκ4 c F (candSchedF fl j t)) 0 0
      (scheduleList (candSchedF fl j t)) ω) = LP.traceAt u.toNNReal (continuedDriver
      (codeFam h44 hκ hκ4 c Prod.fst (candSchedF fl j t)) 0 0 (scheduleList (candSchedF fl j t)) ((F ω, y) : Gam))
  rw [e]

section Agree

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace Ωa] (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
  (noise : ℕ → ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ)

omit mΩ in
theorem nodeAlpha_eq_gam (s : Schedule) (j : ℕ) (t : Fin j → ℝ≥0) (ω : Ω) (y : HistorySpace 0 0) :
    nodeAlpha x₀ h44 hκ hκ4 hb h s j t ω = gamNodeAlpha h44 hκ hκ4 (x₀ := x₀) hb s j t (qField x₀ κ h ω, y) := by
  by_cases hj : j ≤ nodeLen s
  · rw [nodeAlpha_of_le _ _ _ _ _ hj, gamNodeAlpha_of_le h44 hκ hκ4 hb hj]
    exact qPathF_eq_fst hκ hκ4 h44 _ (qField x₀ κ h) _ _ _ ω y
  · rw [nodeAlpha_of_lt _ _ _ _ _ (not_le.1 hj), gamNodeAlpha_of_lt h44 hκ hκ4 hb (not_le.1 hj)]
    exact qPathF_eq_fst hκ hκ4 h44 _ (qField x₀ κ h) _ _ _ ω y

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **The node tree agrees with `gamNodeData` at `(qField ω, cfHistory ω)`** on the good samples. -/
theorem agreeAt_nodeD_gamNodeData (n : ℕ) (q : ℚ) {ω : Ω}
    (hω : ω ∈ nodeGood x₀ h44 hκ hκ4 hb P h W ζ (scheduleAt n))
    (hZ : (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω) ∈ gamNodeGood h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n)) :
    (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).AgreeAt
      (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) (q : ℝ).toNNReal) ω
      (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω) :=
  ⟨rfl, rfl, rfl, ⟨fun _ => hZ, fun _ => hω⟩,
    fun j t => nodeAlpha_eq_gam x₀ h44 hκ hκ4 hb h (scheduleAt n) j t ω _, fun _ _ => Iff.rfl, rfl, rfl⟩

variable {x₀ h44 hκ hκ4 hb P h W ζ noise}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem nodeMarks_eq_gam {n : ℕ} {q : ℚ} {ω : Ω} {γ : Gam}
    (hag : (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).AgreeAt
      (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) (q : ℝ).toNNReal) ω γ) :
    nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise n q ω = gamNodeMarks h44 hκ hκ4 (x₀ := x₀) hb n (q : ℝ).toNNReal γ :=
  hag.marks _ _

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem nodeScale_eq_gam {n : ℕ} {q : ℚ} {ω : Ω} {γ : Gam}
    (hag : (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).AgreeAt
      (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) (q : ℝ).toNNReal) ω γ) :
    nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise n q ω = gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n (q : ℝ).toNNReal γ := by
  simp only [nodeScale, gamNodeScale, nodeMarks_eq_gam hag]

omit [StandardBorelSpace Ω] [MeasurableSpace Ωa] [IsProbabilityMeasure P] in
theorem nodeStart_eq_gam {n : ℕ} {q : ℚ} {ω' : Ω × Ωa} {γ : Gam}
    (hag : (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).AgreeAt
      (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) (q : ℝ).toNNReal) ω'.1 γ) :
    nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q ω' = gamNodeStart h44 hκ hκ4 (x₀ := x₀) hb n (q : ℝ).toNNReal γ := by
  simp only [nodeStart, gamNodeStart, nodeMarks_eq_gam hag, nodeScale_eq_gam hag]

omit [StandardBorelSpace Ω] [MeasurableSpace Ωa] [IsProbabilityMeasure P] in
theorem mem_nodeR0_iff_gam {n : ℕ} {q : ℚ} {ω' : Ω × Ωa} {γ : Gam}
    (hag : (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).AgreeAt
      (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) (q : ℝ).toNNReal) ω'.1 γ) :
    ω' ∈ nodeR0 (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q ↔
      γ ∈ gamNodeR0 h44 hκ hκ4 (x₀ := x₀) hb n (q : ℝ).toNNReal := by
  simp only [nodeR0, nodeR0Ω, gamNodeR0, mem_preimage, mem_ofPred_eq, hag.mem_alive, nodeMarks_eq_gam hag]

omit [StandardBorelSpace Ω] [MeasurableSpace Ωa] [IsProbabilityMeasure P] in
theorem pieceAt_nodeCand {n : ℕ} {q : ℚ} {ω' : Ω × Ωa} {γ : Gam}
    (hag : (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).AgreeAt
      (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) (q : ℝ).toNNReal) ω'.1 γ) (j : ℕ) (t : Fin j → ℝ≥0) :
    PieceAt (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q j t)
      (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n (q : ℝ).toNNReal j t) ω' γ :=
  PieceAt.lift (PieceAt.scale (PieceAt.reindex _ _ (hag.cand _ _)) (nodeScale_eq_gam hag))

end Agree

/-! ### The good sets hold almost surely -/

section Good

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace Ωa] (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)

/-- **Both good sets hold almost surely** (the clearance form of Part A for the counterflow history; the code drivers
of the node flags are good paths). -/
theorem ae_nodeGood_pieceZ (hA : PartAInputsSixteenDivOfClearance)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (s : Schedule) :
    ∀ᵐ ω' ∂(P.prod Pa), ω'.1 ∈ nodeGood x₀ h44 hκ hκ4 hb P h W ζ s ∧
      pieceZ (Ωa := Ωa) x₀ κ h W ζ ω' ∈ gamNodeGood h44 hκ hκ4 (x₀ := x₀) hb s := by
  obtain ⟨γ, htr⟩ := exists_cfTrace hκ hb hG hcf
  have h2 := Wire.Night.cfHistory_goodHit_clearance hA hκ hκ4 hb hG hcf htr
  have hE := Prop59Sched.isStagedHistory_targetSched h44 hκ hκ4 hb hG
  have hR := Prop59Sched.stagedPiecesRegular_targetSched h44 hκ hκ4 hb hG
  have hg := ae_all_valid (P := P) fun j t (_ : IsValid j t) =>
    ae_codeGood h44 hκ hκ4 hb hG hE hR (candSchedF (nodeFlag s) j t)
  have hnode : ∀ᵐ ω ∂P, NodeGood x₀ h44 hκ hκ4 hb h W ζ s ω := by
    filter_upwards [hg, h2] with ω hgω hcω
    refine ⟨hcω, fun j t hv => (isProperArc_qPathF_of h44 hκ hκ4 _ _ (hgω j t hv)).1⟩
  have h1 : ∀ᵐ ω ∂P, ω ∈ nodeGood x₀ h44 hκ hκ4 hb P h W ζ s := by
    rw [ae_iff]
    have he : {ω | ¬ ω ∈ nodeGood x₀ h44 hκ hκ4 hb P h W ζ s} =
        toMeasurable P {ω | ¬ NodeGood x₀ h44 hκ hκ4 hb h W ζ s ω} := by
      ext ω; simp [nodeGood]
    rw [he, measure_toMeasurable]
    exact ae_iff.1 hnode
  have h0 : ∀ᵐ ω ∂P, ω ∈ nodeGood x₀ h44 hκ hκ4 hb P h W ζ s ∧
      (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω) ∈ gamNodeGood h44 hκ hκ4 (x₀ := x₀) hb s := by
    filter_upwards [h1, h2, hg] with ω hω1 hω2 hω3
    exact ⟨hω1, hω2.1, fun j t hv k hk => hω3 j t hv k hk⟩
  exact Measure.quasiMeasurePreserving_fst.ae h0

end Good

end InteractingSLE.Sec5.CrossCond.StagedNTr
