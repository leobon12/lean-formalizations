/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsWord
import InteractingSLE.Spec.Supplement.WalkWordsRun

/-!
# The ordinary set of a walk is closed and has finitely many junctions

Packet PROVE-WALK-WORDS (the two facts that wire `exists_isPiecewiseConstant_componentWord` almost surely). The
physical set of a boundary walk is the range of a proper curve `γ` (a closed embedding of `ℝ≥0`), and each recorded
piece is a closed connected subset of it (`PieceData`: the continuous image of the own-time interval). The `γ`-times of
a piece then form a closed interval of `ℝ≥0`, so a point of a piece in the closure of the rest of the walk is the image
of an end of one of these finitely many intervals:

* `finite_inter_closure_diff` (generic): for finitely many preconnected subsets `K i` of the range of a closed embedding
  `γ : ℝ≥0 → ℂ`, the set `(⋃ K i) ∩ cl(range γ ∖ ⋃ K i)` is finite (inside `γ({inf, sup})` of the time intervals);
* `PieceData.isPreconnected_tipSet`;
* **`ordOf_facts`**: `IsClosed (ordOf s)` and `(ordOf s ∩ cl(physOf spec s ∖ ordOf s)).Finite`, for a final state
  whose physical set is the range of a proper curve and whose pieces carry `PieceData`;
* **`walkComponentWordStatement_of_walks`**: almost surely, every component chart's canonical word is piecewise constant
  and satisfies (GW3.1) (`WalkComponentWordStatement`, `hMatch`'s finite word), from the five named inputs of
  `GW3SidedProof.gw3GeometryRegStatement_of_walks`.

No clearance or chronology input is needed: only that the walk is one simple curve.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex Metric Function
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkWords

open WalkBdry WalkMean WalkNorm

/-- **Finitely many junctions** (generic): finitely many preconnected subsets of the range of a closed embedding
`γ : ℝ≥0 → ℂ` meet the closure of the rest of the range in finitely many points. -/
theorem finite_inter_closure_diff {γ : ℝ≥0 → ℂ} (hγ : IsClosedEmbedding γ) {ι : Type*} (l : List ι)
    {K : ι → Set ℂ} (hKp : ∀ i ∈ l, IsPreconnected (K i)) (hKr : ∀ i ∈ l, K i ⊆ range γ) :
    ((⋃ i ∈ l, K i) ∩ closure (range γ \ ⋃ i ∈ l, K i)).Finite := by
  have hF : (γ '' ⋃ i ∈ {x | x ∈ l}, ({sInf (γ ⁻¹' K i), sSup (γ ⁻¹' K i)} : Set ℝ≥0)).Finite :=
    (l.finite_toSet.biUnion fun i _ => Set.toFinite _).image γ
  refine hF.subset ?_
  rintro z ⟨hz, hzc⟩
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 hz
  obtain ⟨t, rfl⟩ := hKr i hi hzi
  have hcl : closure (range γ \ ⋃ i ∈ l, K i) ⊆ γ '' closure (γ ⁻¹' ⋃ i ∈ l, K i)ᶜ := by
    refine closure_minimal ?_ (hγ.isClosedMap _ isClosed_closure)
    rintro _ ⟨⟨u, rfl⟩, hu⟩
    exact ⟨u, subset_closure hu, rfl⟩
  obtain ⟨t', ht', htt'⟩ := hcl hzc
  rw [hγ.injective htt'] at ht'
  have hT : (γ ⁻¹' K i).OrdConnected := by
    have hp : IsPreconnected (γ ⁻¹' K i) := by
      rw [← hγ.isInducing.isPreconnected_image, image_preimage_eq_of_subset (hKr i hi)]
      exact hKp i hi
    exact isPreconnected_iff_ordConnected.1 hp
  have htT : t ∈ γ ⁻¹' K i := hzi
  by_contra hnot
  have h1 : t ≠ sInf (γ ⁻¹' K i) := fun h => hnot ⟨t, mem_iUnion₂.2 ⟨i, hi, Or.inl h⟩, rfl⟩
  have h2 : t ≠ sSup (γ ⁻¹' K i) := fun h => hnot ⟨t, mem_iUnion₂.2 ⟨i, hi, Or.inr h⟩, rfl⟩
  obtain ⟨a, ha, hat⟩ := exists_lt_of_csInf_lt ⟨t, htT⟩
    (lt_of_le_of_ne (csInf_le (OrderBot.bddBelow _) htT) (Ne.symm h1))
  obtain ⟨c, hc, htc⟩ : ∃ c ∈ γ ⁻¹' K i, t < c := by
    by_cases hb : BddAbove (γ ⁻¹' K i)
    · exact exists_lt_of_lt_csSup ⟨t, htT⟩ (lt_of_le_of_ne (le_csSup hb htT) h2)
    · obtain ⟨c, hc, htc⟩ := not_bddAbove_iff.1 hb t
      exact ⟨c, hc, htc⟩
  have hsub : Ioo a c ⊆ γ ⁻¹' ⋃ i ∈ l, K i := fun x hx =>
    mem_iUnion₂.2 ⟨i, hi, hT.out ha hc ⟨hx.1.le, hx.2.le⟩⟩
  obtain ⟨x, hx, hxU⟩ := mem_closure_iff_nhds.1 ht' (Ioo a c) (isOpen_Ioo.mem_nhds ⟨hat, htc⟩)
  exact hxU (hsub hx)

/-- A recorded piece is connected (the continuous image of its own-time interval). -/
theorem PieceData.isPreconnected_tipSet {pc : Piece} {A : Set ℂ} {f : ℂ → ℂ} {W : ℝ≥0 → ℝ} {α : ℝ≥0 → ℂ}
    (h : PieceData pc A f W α) : IsPreconnected (pc.1.tipSet pc.2.1 pc.2.2) := by
  rw [h.tipSet_eq]
  have hoc : ({t : ℝ≥0 | (t : ℝ≥0∞) ≤ pc.2.2}).OrdConnected :=
    ⟨fun _ _ _ hc _ hx => le_trans (ENNReal.coe_le_coe.2 hx.2) hc⟩
  exact (isPreconnected_iff_ordConnected.2 hoc).image _ h.continuousOn

/-- **The ordinary set of a walk is closed and has finitely many junctions** with the rest of the walk. -/
theorem ordOf_facts {spec : ExplSpec} {s : ExplState} {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ)
    (hr : range γ = physOf spec s)
    (hpd : ∀ pc ∈ s.1, ∃ (A : Set ℂ) (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ), PieceData pc A f W α) :
    IsClosed (ordOf s) ∧ (ordOf s ∩ closure (physOf spec s \ ordOf s)).Finite := by
  refine ⟨s.1.finite_toSet.isClosed_biUnion fun pc hpc => ?_, ?_⟩
  · obtain ⟨A, f, W, α, h⟩ := hpd pc hpc
    exact h.isClosed_tipSet
  · rw [← hr]
    refine finite_inter_closure_diff (WalkCont.isClosedEmbedding_of_isProperCurve hγ) s.1
      (K := fun pc => pc.1.tipSet pc.2.1 pc.2.2) (fun pc hpc => ?_) (fun pc hpc z hz => ?_)
    · obtain ⟨A, f, W, α, h⟩ := hpd pc hpc
      exact h.isPreconnected_tipSet
    · rw [hr]
      exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨pc, hpc, hz⟩))

/-- **The finite boundary word of every component chart** (proved conclusion; `hMatch`'s word): almost surely, for
every component chart `c`, the canonical word `componentWord κ b (ordOf R) (ordOf L) c.inv` has a finite jump set off
which it is locally constant, and satisfies (GW3.1). Same hypotheses as `WalkIntFiber.WalkPhysicalGeometryStatement`. -/
def WalkComponentWordStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ᵐ ω ∂P, WalkBetweenFacts κ b jumps E ω) →
      ∀ᵐ ω ∂P, ∀ C ∈ betweenComponents
        (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1)
        (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2),
        ∀ c : Chart, IsComponentChart
          (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1)
          (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2) C c →
        ∃ jumpsC : Finset ℝ,
          IsPiecewiseConstantBoundaryData
            (componentWord κ b (ordOf (walkRuns κ b jumps E ω).1) (ordOf (walkRuns κ b jumps E ω).2) c.2.1)
            jumpsC ∧
          IsComponentBoundaryData κ b (ordOf (walkRuns κ b jumps E ω).1) (ordOf (walkRuns κ b jumps E ω).2) c.2.1
            (componentWord κ b (ordOf (walkRuns κ b jumps E ω).1) (ordOf (walkRuns κ b jumps E ω).2) c.2.1)
            jumpsC

/-- **`WalkComponentWordStatement`** from the five named inputs of `GW3SidedProof.gw3GeometryRegStatement_of_walks`
(the landing maps), GW1 piece simplicity and regularity (piece data), and the proper walk parametrizations. -/
theorem walkComponentWordStatement_of_walks (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hNR : GW3SidedProof.RightWalkNegRealRegStatement.{u}) :
    WalkComponentWordStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts
  have hRR := hR _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)
  have hRL := hR _ (GW1X.isBoundaryContinuedProgram_walkL b jumps)
  filter_upwards [walkComponentLandingStatement_of_walks hPR hPL hA hF hNR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ'
    E hE hR hreg hfacts, hfacts, hRR, hRL] with ω hland hfω hωR hωL
  obtain ⟨hpf, hs, -, -⟩ := hfω
  obtain ⟨⟨γR, hγR, -, hrR⟩, ⟨γL, hγL, -, hrL⟩, -⟩ := hpf
  have hpdR : ∀ pc ∈ (walkRuns κ b jumps E ω).1.1,
      ∃ (A : Set ℂ) (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ), PieceData pc A f W α := fun pc hpc => by
    obtain ⟨pre, post, hs'⟩ := List.append_of_mem hpc
    obtain ⟨f, W, α, hd⟩ := exists_pieceData (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)
      (fun k c θ hl => WalkNorm.pieceRegular_of_event hωR k c θ hl) (fun k c θ hl => hs true k c θ hl) hs'
    exact ⟨_, f, W, α, hd⟩
  have hpdL : ∀ pc ∈ (walkRuns κ b jumps E ω).2.1,
      ∃ (A : Set ℂ) (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ), PieceData pc A f W α := fun pc hpc => by
    obtain ⟨pre, post, hs'⟩ := List.append_of_mem hpc
    obtain ⟨f, W, α, hd⟩ := exists_pieceData (boundaryWalkSpec b jumps (Real.pi / 2) false)
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)
      (fun k c θ hl => WalkNorm.pieceRegular_of_event hωL k c θ hl) (fun k c θ hl => hs false k c θ hl) hs'
    exact ⟨_, f, W, α, hd⟩
  obtain ⟨hcR, hjR⟩ := ordOf_facts (spec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (s := (walkRuns κ b jumps E ω).1) hγR hrR hpdR
  obtain ⟨hcL, hjL⟩ := ordOf_facts (spec := boundaryWalkSpec b jumps (Real.pi / 2) false)
    (s := (walkRuns κ b jumps E ω).2) hγL hrL hpdL
  intro C hC c hc
  obtain ⟨ℓ, hℓc, hℓi, hℓ⟩ := hland C hC c hc
  have hℓx : ∀ x : ℝ, ∃ p : ℂ, ℓ x = p ∧
      (0 < x → p ∈ physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1) ∧
      (x < 0 → p ∈ physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2) := by
    intro x
    obtain ⟨p, hp, h1, h2⟩ := hc.2.2.2.2.1 x
    have : (𝓝[H] (x : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ (x : ℂ).im by simp)
    exact ⟨p, tendsto_nhds_unique (hℓ x) hp, h1, h2⟩
  obtain ⟨jumpsC, hpw⟩ := exists_isPiecewiseConstant_componentWord (κ := κ) hb
    (fun z hz => mem_ordOf_or_im_eq_zero hz) (fun z hz => mem_ordOf_or_im_eq_zero hz) hcR hcL hjR hjL hℓc hℓi hℓ
    (fun x hx => by obtain ⟨p, rfl, h1, -⟩ := hℓx x; exact h1 hx)
    (fun x hx => by obtain ⟨p, rfl, -, h2⟩ := hℓx x; exact h2 hx)
  exact ⟨jumpsC, hpw, isComponentBoundaryData_componentWord jumpsC⟩

end InteractingSLE.Theorem14.WalkWords
