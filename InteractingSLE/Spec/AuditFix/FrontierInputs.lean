/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.AuditFix.FrontierTopology
import InteractingSLE.Spec.Supplement.GW2aSingle
import InteractingSLE.Spec.Supplement.GW4TraverseTrace
import InteractingSLE.Spec.Sec5.Lemma57Visit
import InteractingSLE.Spec.Supplement.SB4RTop
import InteractingSLE.Spec.Supplement.WalkPieceProof
import InteractingSLE.Spec.Supplement.GW1LaterR51
import InteractingSLE.Spec.Supplement.GW1ConnectorFirst
import InteractingSLE.Spec.Supplement.GW1Bookkeep
import InteractingSLE.Spec.Supplement.SBLxWalk
import InteractingSLE.Spec.Supplement.SB2LuStart
import InteractingSLE.Spec.Exist.StagedLaw2Launch
import InteractingSLE.Spec.Wire.T14Asm7

/-!
# Audit fix, frontier bridge: the almost-sure inputs

Packet PROVE-AF-FRONTIER. The inputs of `Spec/AuditFix/FrontierBridge.lean` beyond the frozen frontier anchor, each
proved here from closed project results (Theorems 1.2–1.3 are `Wire.T14Asm7.h12`, `h13`, `h12₀`, `h13₀`):

* `ae_isClosed_closure_inter_H`: the completed counterflow range `K` is almost surely closed and equal to
  `closure (K ∩ ℍ)`. Theorem 1.3 (at `κ' = 16/κ`) gives a continuous transient generating trace `γ`, so
  `K = {−1/γ(t)} ∪ {0}` (`CounterflowRange.tipSet_infinitySourceChart_top`); the hulls grow on every time interval
  (`Sec5.exists_mem_fwdHull_sdiff`), so `γ` visits `ℍ` at times arbitrarily close to any time and arbitrarily late,
  and `z ↦ −1/z` maps `ℍ` to `ℍ`. This is the form used here of the paper's remark that the counterflow does not
  *trace* a boundary segment (Figure 7.22, p. 164);
* `Wire.walkProperRegStatements_of_thm12_thm13` (reused): both walks are proper simple curves from `0` (Lemma GW1);
* `Theorem14.WalkPiece.rightWalkNegRealRegStatement_of_theorem13` (reused) and its mirror
  `ae_leftWalk_posReal_subsingleton` (new): the right walk has no nondegenerate real arc in `(−∞, 0)`, the left walk
  none in `(0, ∞)` (connectors are rightward resp. leftward, GW1; an ordinary piece has no real arc, Lemma 2.5);
* `physSet_boundaryWalkSpec_of_top`: a boundary walk whose first piece has lifetime `⊤` is that piece together with
  its root `0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.AuditFix.Frontier

/-! ### The completed counterflow range is the closure of its points in `ℍ` -/

/-- **The completed range of a transient generating trace is the closure of its points in `ℍ`** (deterministic). -/
theorem subset_closure_inter_H_of_trace {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ)
    (hW : Continuous W) (hW0 : W 0 = 0) (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    counterflowCompletedRange W ⊆ closure (counterflowCompletedRange W ∩ H) := by
  have hγc : Continuous γ := Theorem14.GW4Traverse.continuous_of_isGeneratingTrace_top hγ
  have hK : counterflowCompletedRange W = {z | ∃ t, γ t ≠ 0 ∧ z = -(γ t)⁻¹} ∪ {0} := by
    unfold counterflowCompletedRange
    rw [Theorem14.CounterflowRange.tipSet_infinitySourceChart_top hγ hW hW0]
  have hmem : ∀ s, γ s ∈ H → -(γ s)⁻¹ ∈ counterflowCompletedRange W ∩ H := fun s hs => by
    refine ⟨?_, Theorem14.GW4Traverse.negInv_mem_H' hs⟩
    rw [hK]
    exact Or.inl ⟨s, Theorem14.GW4Traverse.ne_zero_of_mem_H' hs, rfl⟩
  -- the trace is in `ℍ` at some time of every interval `(r, r + ε]`
  have hlater : ∀ (r : ℝ≥0) (ε : ℝ), 0 < ε → ∃ v : ℝ≥0, r < v ∧ (v : ℝ) ≤ r + ε ∧ γ v ∈ H := by
    intro r ε hε
    have hrt : r < r + ε.toNNReal := lt_add_of_pos_right r (Real.toNNReal_pos.2 hε)
    obtain ⟨v, hrv, hvb, hvK⟩ := Sec5.exists_mem_fwdHull_sdiff hW hW0 hγ hrt
    refine ⟨v, hrv, ?_, hvK.1.1⟩
    have := NNReal.coe_le_coe.2 hvb
    rwa [NNReal.coe_add, Real.coe_toNNReal _ hε.le] at this
  intro p hp
  rw [Metric.mem_closure_iff]
  intro δ hδ
  rw [hK] at hp
  rcases hp with ⟨t, ht, rfl⟩ | hp0
  · have hcont : ContinuousAt (fun s => -(γ s)⁻¹) t := (hγc.continuousAt.inv₀ ht).neg
    obtain ⟨η, hη, hηs⟩ := Metric.continuousAt_iff.1 hcont δ hδ
    obtain ⟨v, htv, hvb, hvH⟩ := hlater t (η / 2) (half_pos hη)
    refine ⟨-(γ v)⁻¹, hmem v hvH, ?_⟩
    rw [dist_comm]
    apply hηs
    rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 htv.le))]
    linarith
  · rw [mem_singleton_iff] at hp0
    subst hp0
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 htr (δ⁻¹ + 1))
    obtain ⟨v, hNv, -, hvH⟩ := hlater N 1 one_pos
    refine ⟨-(γ v)⁻¹, hmem v hvH, ?_⟩
    have hv : δ⁻¹ + 1 ≤ ‖γ v‖ := hN v hNv.le
    rw [dist_zero_left, norm_neg, norm_inv]
    exact inv_lt_of_inv_lt₀ hδ (by linarith)

/-- **The completed counterflow range is almost surely closed and the closure of its points in `ℍ`** (Theorem 1.3 at
`16/κ`). -/
theorem ae_isClosed_closure_inter_H {κ : ℝ} (hκ : 0 < κ) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) :
    ∀ᵐ ω ∂P, IsClosed (counterflowCompletedRange (fun t => W' t ω)) ∧
      closure (counterflowCompletedRange (fun t => W' t ω) ∩ H) =
        counterflowCompletedRange (fun t => W' t ω) := by
  obtain ⟨b', J', h', -, -, hfl⟩ := hcf
  have hk : 0 < 16 / κ := by positivity
  filter_upwards [Theorem14.GW2aSingle.ae_chosenTrace Wire.T14Asm7.h13 hk hfl, hζ',
    Supp8.GB6.ae_driver_zero_continuousOn hfl] with ω hγω hζω hdω
  rw [hζω] at hγω hdω
  have hWc : Continuous fun t => W' t ω := by
    have hc := hdω.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  have htr := hγω.2 rfl
  have hcl := Theorem14.CounterflowRange.isClosed_counterflowCompletedRange hγω.1 hWc hdω.1 htr
  exact ⟨hcl, Subset.antisymm (closure_minimal inter_subset_left hcl)
    (subset_closure_inter_H_of_trace hγω.1 hWc hdω.1 htr)⟩

/-! ### The left walk has no positive real arc -/

/-- **A walk with leftward connectors and no real arc in its pieces has no positive real arc** (deterministic; the
mirror of `Theorem14.GW3SidedProof.neg_real_subsingleton`). -/
theorem pos_real_subsingleton {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ)
    (hγr : range γ = ExplState.physSet κ b jumps spec D)
    (hS : ∀ a ∈ (ExplState.run κ b jumps spec D spec.2.2.length).2.1, a ⊆ Iic 0)
    (hP : ∀ p ∈ (ExplState.run κ b jumps spec D spec.2.2.length).1,
      ∀ S ⊆ closure (p.1.tipSet p.2.1 p.2.2) ∩ range ((↑) : ℝ → ℂ), IsPreconnected S → S.Subsingleton) :
    ∀ S ⊆ range γ ∩ ((↑) : ℝ → ℂ) '' Ioi 0, IsPreconnected S → S.Subsingleton := by
  have hIci : IsClosed (((↑) : ℝ → ℂ) '' Ici 0) :=
    Complex.isometry_ofReal.isClosedEmbedding.isClosedMap _ isClosed_Ici
  refine Theorem14.WalkCont.subsingleton_of_finite_covers hγ (Theorem14.WalkCont.walkCover_finite _ _)
    (finite_singleton _) (fun F hF => Theorem14.WalkCont.isClosed_of_mem_walkCover hF)
    (fun G hG => (mem_singleton_iff.1 hG) ▸ hIci)
    (hγr ▸ Theorem14.WalkCont.physSet_subset_sUnion_walkCover _ _ _ _ _)
    (fun z hz => mem_sUnion_of_mem (image_mono Ioi_subset_Ici_self hz) (mem_singleton _)) ?_
  intro F hF G hG S hSFG hSc
  rw [mem_singleton_iff] at hG
  subst hG
  rcases hF with rfl | ⟨p, hp, rfl⟩ | ⟨a, ha, rfl⟩
  · exact subsingleton_singleton.anti fun z hz => (hSFG hz).1
  · exact hP p hp S (fun z hz => ⟨(hSFG hz).1, image_subset_range _ _ (hSFG hz).2⟩) hSc
  · exact Theorem14.WalkCont.subsingleton_of_subset_ofReal_Ici_Iic fun z hz =>
      ⟨(hSFG hz).2, Theorem14.WalkCont.closure_ofReal_image_subset (hS a ha) isClosed_Iic (hSFG hz).1⟩

/-- **The left walk contains no nondegenerate preconnected set of positive reals** (almost surely; the mirror of
`Theorem14.GW3SidedProof.RightWalkNegRealRegStatement`, from the left walk's proper parametrization, its leftward
connectors and Lemma 2.5 for its pieces). -/
theorem ae_leftWalk_posReal_subsingleton {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec)) :
    ∀ᵐ ω ∂P, ∀ S ⊆ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
        (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) ∩ ((↑) : ℝ → ℂ) '' Ioi 0,
      IsPreconnected S → S.Subsingleton := by
  have hPL := (Wire.walkProperRegStatements_of_thm12_thm13 Wire.T14Asm7.h12.{u} Wire.T14Asm7.h13.{u}
    Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀).2
  have hS := Theorem14.GW1X.walkConnectorSideRegStatement_of_theorem13.{u} Wire.T14Asm7.h13₀
  filter_upwards [hPL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    (hreg _ (Theorem14.GW1X.isBoundaryContinuedProgram_walkL b jumps)).ae_pieceRegular]
    with ω hPLω hSω hrL
  obtain ⟨γL, hγL, -, hγLr⟩ := hPLω
  rw [← hγLr]
  exact pos_real_subsingleton hγL hγLr hSω.2
    (Theorem14.WalkPiece.pieces_real_subsingleton_of_range _ _ hrL hγL hγLr)

/-! ### A walk whose first piece is complete -/

/-- **A boundary walk whose first ordinary piece has lifetime `⊤` is that piece** (deterministic): the walk is done
after its first instruction, and its physical set is the root `0` together with the trace points of its first piece
read in the identity chart. -/
theorem physSet_boundaryWalkSpec_of_top (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool)
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : (D 0).2 = ⊤) :
    ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ right) D = {0} ∪ Chart.id.tipSet (D 0).1 ⊤ := by
  have h1 := Theorem14.GW1Conn.run_one_boundaryWalkSpec κ b jumps θ right D
  have hstop : min (⊤ : ℝ≥0∞) (D 0).2 = ⊤ := by rw [hD, min_self]
  have hdone : Exist.StagedLaw.stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D 1) =
      Theorem14.GW1Conn.stDone := by
    rw [h1]
    exact (Exist.StagedLaw.launch_eq_of_top _ 0 (D 0) θ ⊤ hstop).2.2.2.2.1
  have hrun := Theorem14.SB.Lx.run_eq_of_done _ D hdone _
    (Theorem14.SB.Lk.one_lt_length_boundaryWalkSpec b jumps θ right).le
  have hchart : Chart.id.recenter 0 = Chart.id := by
    simp only [Chart.recenter, Chart.id, Complex.ofReal_zero, sub_zero, add_zero]
  have hroot : (((boundaryWalkSpec b jumps θ right).1 : ℝ) : ℂ) = 0 := by
    simp only [boundaryWalkSpec, Complex.ofReal_zero]
  rw [Theorem14.GW1Bookkeep.physSet_eq_statePhysicalSet, hrun, h1]
  unfold Theorem14.GW1Bookkeep.statePhysicalSet
  rw [Theorem14.CounterflowRange.pieces_launch, Theorem14.SB.Lk.launch_arcs, hroot]
  simp [ExplState.init, hD, hchart]

end InteractingSLE.AuditFix.Frontier
