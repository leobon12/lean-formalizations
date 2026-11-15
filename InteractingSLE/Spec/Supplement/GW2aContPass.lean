/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aContArc

/-!
# Lemma GW2a for every program: from GW1's induction step to almost-sure containment

Packet PROVE-GW2AC. GW1's induction datum (`HasStatePair`) is a statement about the regular conditional law at one
sample, not a measurable event; it cannot be integrated against `P` instruction by instruction (ruling R51). As in
PROVE-T14-BR6 (`GW2Later.ae_later_piece_subset_of_step`), only measurable containment events are carried down the chain
of retained pasts by the tower property (`KernelTower.ae_ae_of_chain`):

* `pieceTips`, **`physSet_eq`**: the physical set of a history is its root, the tips of the pieces launched by its
  instructions and the connectors recorded by them;
* `ae_mem_of_chain`: a measurable event that is almost sure under the conditional law after `k` instructions wherever
  the datum holds, is `P`-almost sure, when the datum holds before the first instruction and is propagated by the step;
* **`exists_measurable_arc_event`**: the measurable form of the containment of one connector;
* **`ae_physSet_subset_of_steps`**: GW2a's containment for one boundary-continued program from the root `0`, from GW1's
  inductive step and the connector containment under the conditional laws.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aCont

open Exist.Staged Exist.StagedLaw GW2Later CounterflowRange GW2aMulti

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-! ### The physical set by instruction -/

/-- The tips of the piece launched by instruction `k`, read in its launch chart (empty if it launches none). -/
def pieceTips (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) :
    Set ℂ :=
  if (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = none then ∅ else
    (ExplState.run κ b jumps spec D k).2.2.2.2.1.tipSet (stoppedDriver spec D k) (pieceStop spec D k)

/-- **The pieces of a run are those launched by its instructions.** -/
theorem iUnion_pieces_run (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    (⋃ p ∈ (ExplState.run κ b jumps spec D n).1, p.1.tipSet p.2.1 p.2.2) =
      ⋃ k ∈ Finset.range n, pieceTips κ b jumps spec D k := by
  induction n with
  | zero => simp [ExplState.run, ExplState.init]
  | succ n ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert, ← ih, union_comm]
    rcases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with _ | ⟨c, θ⟩
    · rw [GW1P.pieces_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D hl]
      simp only [pieceTips, hl, ↓reduceIte, union_empty]
    · obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
      have hne : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n ≠ none := by
        rw [hl]; exact Option.some_ne_none _
      rw [he, CounterflowRange.pieces_launch]
      simp only [pieceTips, hne, ↓reduceIte, List.mem_append, List.mem_singleton, iUnion_or,
        iUnion_union_distrib, iUnion_iUnion_eq_left]
      rfl

/-- **The physical set of a history** is its root, the tips of its launched pieces and its connectors. -/
theorem physSet_eq (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.physSet κ b jumps spec D = {(spec.1 : ℂ)} ∪
      (⋃ k ∈ Finset.range spec.2.2.length, pieceTips κ b jumps spec D k) ∪
        ⋃ k ∈ Finset.range spec.2.2.length, ((↑) : ℝ → ℂ) '' arcAt κ b jumps spec D k := by
  unfold ExplState.physSet
  dsimp only
  rw [iUnion_pieces_run, ← image_iUnion₂, iUnion_arcs_run, image_iUnion₂]

/-! ### The chain of retained pasts -/

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **A measurable event carried down the chain of retained pasts is almost sure** (the datum holds before the first
instruction everywhere; the regular conditional law given the empty past is `P`). -/
theorem ae_mem_of_chain {P : Measure Ω} [IsProbabilityMeasure P] {h' : Ω → DistOn upperHalfPlaneOpens}
    {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h' spec E) {D : ℕ → Ω → Prop}
    (hD0 : ∀ ω, D 0 ω) {A : Set Ω} (hA : MeasurableSet A) (k : ℕ)
    (htop : ∀ᵐ ω ∂P, D k ω → ∀ᵐ x ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω), x ∈ A)
    (hstep : ∀ j < k, ∀ᵐ ω ∂P, D j ω →
      ∀ᵐ x ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω), D (j + 1) x) :
    ∀ᵐ x ∂P, x ∈ A := by
  have hchain := KernelTower.ae_ae_of_chain (P := P) (𝒢 := fun j => pastSigma κ b jumps spec E j)
    (fun j => pastSigma_mono (κ := κ) (b := b) (jumps := jumps) spec E (Nat.le_succ j))
    (fun j => hS.2.1 j) (D := D) hA k htop hstep 0 (Nat.zero_le k)
  have hν : ∀ ω, condExpKernel P (pastSigma κ b jumps spec E 0) ω = P := fun ω => by
    rw [GW1.pastSigma_zero_eq_bot]
    exact GW1.condExpKernel_bot_apply P ω
  obtain ⟨ω, hω⟩ := hchain.exists
  have h1 := hω (hD0 ω)
  rwa [hν] at h1

/-! ### The measurable form of a connector's containment -/

/-- **A measurable event for the containment of the connector recorded by instruction `k`** (measurable drivers regular
at every sample; Theorem 1.3 for the counterflow): it is implied, almost surely under almost every regular conditional
law given the retained past, by the containment itself, and it implies the containment. -/
theorem exists_measurable_arc_event (hT13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) (spec : ExplSpec)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ)
    (h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ) :
    ∃ A : Set Ω, MeasurableSet A ∧
      (∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
        ((↑) : ℝ → ℂ) '' arcAt κ b jumps spec (fun j => E j ω) k ⊆ counterflowCompletedRange (fun t => W' t ω) →
          ω ∈ A) ∧
      ∀ ω ∈ A, ((↑) : ℝ → ℂ) '' arcAt κ b jumps spec (fun j => E j ω) k ⊆
        counterflowCompletedRange (fun t => W' t ω) := by
  classical
  obtain ⟨b', J', h', -, -, hfl'⟩ := id hcf
  have hk16 : 0 < 16 / κ := by positivity
  obtain ⟨h'', 𝓕, VL', VR', B', -, hC'⟩ := id hfl'
  have hAd : AdaptedBefore 𝓕 ζ' W' := hC'.1.2.1
  set K : ℝ≥0 → Ω → ℝ := fun t ω => if (t : ℝ≥0∞) < ζ' ω then W' t ω else 0 with hKdef
  have hKm : ∀ t, Measurable (K t) := fun t => (WholeField.measurable_killedVal hAd t).mono (𝓕.le t) le_rfl
  set γ := GW2aSingle.chosenTrace W' ζ' with hγdef
  have hgood : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ W' 0 ω = 0 ∧ Continuous (fun t => W' t ω) ∧
      IsGeneratingTrace (fun t => W' t ω) ⊤ (γ ω) ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop := by
    filter_upwards [hζ', Supp8.GB6.ae_driver_zero_continuousOn hfl', GW2aSingle.ae_chosenTrace hT13 hk16 hfl']
      with ω hζω hdω hγω
    rw [hζω] at hdω hγω
    have hWc : Continuous fun t => W' t ω := by
      have hc := hdω.2
      simp only [ENNReal.coe_lt_top, ofPred_true] at hc
      exact continuousOn_univ.1 hc
    exact ⟨hζω, hdω.1, hWc, hγω.1, hγω.2 rfl⟩
  obtain ⟨G, hGae, hGm, hGp⟩ := hgood.exists_measurable_mem
  have hRT : ∀ ω ∈ G, closure (cfDense fun t => K t ω) = counterflowCompletedRange fun t => W' t ω :=
    fun ω hω => by
      have hK : (fun t => K t ω) = fun t => W' t ω := by
        funext t
        simp only [hKdef, (hGp ω hω).1, ENNReal.coe_lt_top, ite_true]
      rw [hK]
      obtain ⟨-, h0, hc, hγ', htr⟩ := hGp ω hω
      exact closure_cfDense_eq hγ' hc h0 htr
  set A : Set Ω := G ∩ {ω | ∀ q : ℚ, (q : ℝ) ∈ arcAt κ b jumps spec (fun j => E j ω) k →
    infEDist (((q : ℝ) : ℂ)) (cfDense fun t => K t ω) = 0} with hAdef
  have hAm : MeasurableSet A := by
    refine hGm.inter ?_
    have e : {ω | ∀ q : ℚ, (q : ℝ) ∈ arcAt κ b jumps spec (fun j => E j ω) k →
        infEDist (((q : ℝ) : ℂ)) (cfDense fun t => K t ω) = 0} = ⋂ q : ℚ,
          ({ω | (q : ℝ) ∈ arcAt κ b jumps spec (fun j => E j ω) k}ᶜ ∪
            {ω | infEDist (((q : ℝ) : ℂ)) (cfDense fun t => K t ω) = 0}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, imp_iff_not_or]
    rw [e]
    exact MeasurableSet.iInter fun q => (measurableSet_mem_arcAt hb spec hEm hreg k q).compl.union
      (measurableSet_eq_fun (measurable_infEDist_cfDense hKm measurable_const) measurable_const)
  refine ⟨A, hAm, ?_, ?_⟩
  · filter_upwards [Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hGae] with ω₀ hG₀
    filter_upwards [hG₀] with ω hωG hsub
    refine ⟨hωG, fun q hq => ?_⟩
    rw [← mem_closure_iff_infEDist_zero, hRT ω hωG]
    exact hsub ⟨q, hq, rfl⟩
  · rintro ω ⟨hωG, hωq⟩ _ ⟨y, hy, rfl⟩
    rw [← hRT ω hωG]
    have hcl := arcAt_subset_closure_rat (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω) k hy
    have hmap : MapsTo ((↑) : ℝ → ℂ) (arcAt κ b jumps spec (fun j => E j ω) k ∩ range ((↑) : ℚ → ℝ))
        (closure (cfDense fun t => K t ω)) := by
      rintro _ ⟨hq, q, rfl⟩
      rw [mem_closure_iff_infEDist_zero]
      exact hωq q hq
    have h1 : ((y : ℝ) : ℂ) ∈ closure (closure (cfDense fun t => K t ω)) :=
      map_mem_closure Complex.continuous_ofReal hcl hmap
    rwa [closure_closure] at h1

/-! ### Containment from the step -/

omit [StandardBorelSpace Ω] in
theorem angle_mem_Icc_of_getElem {p : List Instr} (hp : IsBoundaryContinuedProgram p) {k : ℕ} {θ : ℝ}
    {t : ℝ≥0∞} (hk : p[k]? = some (Sum.inl (θ, t))) : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
  hp θ t (List.mem_of_getElem? hk)

/-- **GW2a's containment for one program from GW1's inductive step** (supplement p. 623: "Finite induction proves all
the assertions"). For a boundary-continued program from the root `0`, a staged history with measurable drivers regular
at every sample whose pieces are almost surely regular (ruling R51), GW1's datum propagated from each instruction to the
next under the regular conditional laws (`hstep`), and the containment of each recorded connector under the
conditional law wherever the datum holds (`harc`), the physical set is almost surely in the completed counterflow
range. Named inputs: GB6's restart law, GW0's forward implication and Theorem 1.3 (for the pieces, through
`GW2Later.ae_condExpKernel_piece_subset_of_pair`). -/
theorem ae_physSet_subset_of_steps (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {gw : Bool} {p : List Instr}
    (hp : IsBoundaryContinuedProgram p) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h ⟨0, gw, p⟩ E) (hR : StagedPiecesRegular κ b jumps P ⟨0, gw, p⟩ E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hstep : ∀ j, ∀ᵐ ω₀ ∂P, HasStatePair κ b jumps P h W' ⟨0, gw, p⟩ E j ω₀ →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨0, gw, p⟩ E j) ω₀),
        HasStatePair κ b jumps P h W' ⟨0, gw, p⟩ E (j + 1) ω)
    (harc : ∀ k, ∀ᵐ ω₀ ∂P, HasStatePair κ b jumps P h W' ⟨0, gw, p⟩ E k ω₀ →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨0, gw, p⟩ E k) ω₀),
        ((↑) : ℝ → ℂ) '' arcAt κ b jumps ⟨0, gw, p⟩ (fun j => E j ω) k ⊆
          counterflowCompletedRange (fun t => W' t ω)) :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨0, gw, p⟩ (fun j => E j ω) ⊆
      counterflowCompletedRange (fun t => W' t ω) := by
  set spec : ExplSpec := ⟨0, gw, p⟩ with hspec
  have hD0 : ∀ ω, HasStatePair κ b jumps P h W' spec E 0 ω := fun ω => hasStatePair_zero hcf hζ' E ω
  have hstep' : ∀ k, ∀ j < k, ∀ᵐ ω₀ ∂P, HasStatePair κ b jumps P h W' spec E j ω₀ →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀),
        HasStatePair κ b jumps P h W' spec E (j + 1) ω := fun _ j _ => hstep j
  -- the pieces
  have hpiece : ∀ k, ∀ᵐ ω ∂P, pieceTips κ b jumps spec (fun j => E j ω) k ⊆
      counterflowCompletedRange (fun t => W' t ω) := by
    intro k
    obtain ⟨A, hAm, hker, hpath⟩ := exists_measurable_piece_event_run hGB6 hGW0 hT13 hκ hκ4 hb hcf hζ' hS hR hreg k
      fun θ t hk => angle_mem_Icc_of_getElem hp hk
    have htop : ∀ᵐ ω₀ ∂P, HasStatePair κ b jumps P h W' spec E k ω₀ →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), ω ∈ A := by
      filter_upwards [hker] with ω₀ h1 hD
      exact h1 (hasLaunchPair_of_hasStatePair hD)
    filter_upwards [ae_mem_of_chain hS hD0 hAm k htop (hstep' k)] with ω hω
    unfold pieceTips
    split_ifs with hl
    · exact empty_subset _
    · obtain ⟨⟨c, θ⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
      have hc := (eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω) hl').2.2
      rw [← hc]
      exact hpath ω hω c θ hl'
  -- the connectors
  have harc' : ∀ k, ∀ᵐ ω ∂P, ((↑) : ℝ → ℂ) '' arcAt κ b jumps spec (fun j => E j ω) k ⊆
      counterflowCompletedRange (fun t => W' t ω) := by
    intro k
    obtain ⟨A, hAm, hker, hpath⟩ := exists_measurable_arc_event hT13 hκ hb hcf hζ' spec hS.1 hreg k (hS.2.1 k)
    have htop : ∀ᵐ ω₀ ∂P, HasStatePair κ b jumps P h W' spec E k ω₀ →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), ω ∈ A := by
      filter_upwards [hker, harc k] with ω₀ h1 h2 hD
      filter_upwards [h1, h2 hD] with ω h3 h4 using h3 h4
    filter_upwards [ae_mem_of_chain hS hD0 hAm k htop (hstep' k)] with ω hω
    exact hpath ω hω
  filter_upwards [ae_all_iff.2 hpiece, ae_all_iff.2 harc'] with ω h1 h2
  rw [physSet_eq]
  refine union_subset (union_subset ?_ ?_) ?_
  · rintro z hz
    rw [mem_singleton_iff.1 hz]
    exact mem_union_right _ (by simp [hspec])
  · exact iUnion₂_subset fun k _ => h1 k
  · exact iUnion₂_subset fun k _ => h2 k

end GW2aCont

end Theorem14

end InteractingSLE
