/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsModel

/-!
# Theorem 1.4's common-arc leaf: the left prime-end access is proved

Packet PROVE-WALK-WORDS. PROVE-T14-WALKINT reduced the common-arc leaf `WalkBdry.WalkPairGeomStatement` to
`WalkIntBridge.WalkPairAccessGeometryStatement`: two recorded prefixes through an interior common point with their
designated **left** side points, and a continuous identification of the two left incident collars
(`WalkIntBridge.SideIdentification`) — "prescribed left prime-end access; physical landing equality remains
insufficient".

This file proves that statement from **`WalkPairArcDataStatement`**, which retains only the bookkeeping of the
common arc and no prime-end, side or chart-transition content: two recorded prefixes `pcR`, `pcL` with global Loewner
models `(Wʳ, ηʳ)`, `(Wˡ, ηˡ)` of their drivers (simple up to the prefix times, fresh after times `s₀ < t`), a common
physical point `p = pcR⁻¹(ηʳ(tʳ)) = pcL⁻¹(ηˡ(tˡ))`, the **same traversal direction** (later points of `ηʳ` up to `τʳ`
are points of `ηˡ` strictly between `tˡ` and `τˡ` — GW4's contact order), and the local walk geometry at `p` (both walks
are their prefixes there, they coincide there, and the left walk is its own piece's trace there).

* the side points `yʳ`, `yˡ` and the landings come from PROVE-T14-WALKNORM's cut lemma
  (`WalkNorm.exists_isLeftSidePt_of_cut`, `WalkNorm.tendsto_prefixChart_inv_of_eq`);
* the incident-side identification is `nonempty_sideIdentification` (the fibre lemma and the orientation of the
  boundary correspondence), its domain hypothesis `exists_ball_mem_loewner_image` (near a fresh trace point the hull
  is the trace) with `WalkIntBridge.prefixChart_disjoint_prefixSet`.

**`walkPairAccessGeometryStatement_of_arcData`**, and the original leaves `walkPairGeomCOStatement_of_arcData`,
`walkPairGeomStatement_of_arcData`. R48: Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkWords

open WalkBdry WalkNorm WalkMean WalkInf

/-- **Named input: the bookkeeping of a common arc of the two walks** (no side, prime-end or transition content; see
the module docstring). Same hypotheses as `WalkIntBridge.WalkPairAccessGeometryStatement`. -/
def WalkPairArcDataStatement : Prop :=
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
      (∀ᵐ ω ∂P, WalkPairPathFacts κ b jumps E ω) →
      (∀ᵐ ω ∂P, WalkPiecesSimple κ b jumps E ω) →
      ∀ᵐ ω ∂P, ∀ pR ∈ (walkRuns κ b jumps E ω).1.1,
        ∀ pL ∈ (walkRuns κ b jumps E ω).2.1,
        ∀ S ⊆ closure (pR.1.tipSet pR.2.1 pR.2.2) ∩
          closure (pL.1.tipSet pL.2.1 pL.2.2), IsPreconnected S → ¬ S.Subsingleton →
          ∃ (preR postR preL postL : List Piece) (pcR pcL : Piece) (τR τL : ℚ≥0) (WR WL : ℝ → ℝ)
            (ηR ηL : ℝ → ℂ) (TR TL s₀R s₀L tR tL r : ℝ),
            (walkRuns κ b jumps E ω).1.1 = preR ++ pcR :: postR ∧ (((τR : ℝ≥0)) : ℝ≥0∞) < pcR.2.2 ∧
            (walkRuns κ b jumps E ω).2.1 = preL ++ pcL :: postL ∧ (((τL : ℝ≥0)) : ℝ≥0∞) < pcL.2.2 ∧
            pcR.1.IsConformal ∧ pcL.1.IsConformal ∧
            Continuous WR ∧ WR 0 = 0 ∧ IsLoewnerTrace WR ηR ∧ ((τR : ℝ≥0) : ℝ) < TR ∧
              ContinuousOn (pieceDrv pcR) (Icc 0 TR) ∧ EqOn (pieceDrv pcR) WR (Icc 0 TR) ∧
            Continuous WL ∧ WL 0 = 0 ∧ IsLoewnerTrace WL ηL ∧ ((τL : ℝ≥0) : ℝ) < TL ∧
              ContinuousOn (pieceDrv pcL) (Icc 0 TL) ∧ EqOn (pieceDrv pcL) WL (Icc 0 TL) ∧
            0 ≤ s₀R ∧ s₀R < tR ∧ tR < ((τR : ℝ≥0) : ℝ) ∧ InjOn ηR (Icc 0 ((τR : ℝ≥0) : ℝ)) ∧
              (∀ s ∈ Ioc s₀R ((τR : ℝ≥0) : ℝ), ηR s ∈ H) ∧
            0 ≤ s₀L ∧ s₀L < tL ∧ tL < ((τL : ℝ≥0) : ℝ) ∧ InjOn ηL (Icc 0 ((τL : ℝ≥0) : ℝ)) ∧
              (∀ s ∈ Ioc s₀L ((τL : ℝ≥0) : ℝ), ηL s ∈ H) ∧
            pcR.1.2.1 (ηR tR) = pcL.1.2.1 (ηL tL) ∧
            (∀ s ∈ Ioc tR ((τR : ℝ≥0) : ℝ), ∃ s' ∈ Ioo tL ((τL : ℝ≥0) : ℝ),
              pcR.1.2.1 (ηR s) = pcL.1.2.1 (ηL s')) ∧
            0 < r ∧
            wsetOf (walkRuns κ b jumps E ω).1 ∩ ball (pcR.1.2.1 (ηR tR)) r ⊆ prefixSet preR pcR τR ∧
            wsetOf (walkRuns κ b jumps E ω).2 ∩ ball (pcR.1.2.1 (ηR tR)) r ⊆ prefixSet preL pcL τL ∧
            wsetOf (walkRuns κ b jumps E ω).1 ∩ ball (pcR.1.2.1 (ηR tR)) r =
              wsetOf (walkRuns κ b jumps E ω).2 ∩ ball (pcR.1.2.1 (ηR tR)) r ∧
            ∀ z ∈ wsetOf (walkRuns κ b jumps E ω).2 ∩ ball (pcR.1.2.1 (ηR tR)) r,
              ∃ s' ∈ Icc 0 ((τL : ℝ≥0) : ℝ), ηL s' ∈ H ∧ z = pcL.1.2.1 (ηL s')

/-- A real time before a rational prefix time is before the piece's stop. -/
theorem toNNReal_le_stop {pc : Piece} {τ : ℚ≥0} (hτ : (((τ : ℝ≥0)) : ℝ≥0∞) < pc.2.2) {t : ℝ}
    (ht : t ≤ ((τ : ℝ≥0) : ℝ)) : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ pc.2.2 := by
  refine le_trans ?_ hτ.le
  exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 ht)

/-- **`WalkIntBridge.WalkPairAccessGeometryStatement` from the bookkeeping of the common arc**: the left prime-end
access (the side points, their landings, and the incident-side identification) is proved. -/
theorem walkPairAccessGeometryStatement_of_arcData (hdata : WalkPairArcDataStatement.{u}) :
    WalkIntBridge.WalkPairAccessGeometryStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts hsimple
  have hRR := hR _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)
  have hRL := hR _ (GW1X.isBoundaryContinuedProgram_walkL b jumps)
  filter_upwards [hdata κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg hfacts hsimple, hRR, hRL]
    with ω hω hωR hωL pR hpR pL hpL S hS hSc hSn
  obtain ⟨preR, postR, preL, postL, pcR, pcL, τR, τL, WR, WL, ηR, ηL, TR, TL, s₀R, s₀L, tR, tL, r,
    hsplitR, haliveR, hsplitL, haliveL, hcR, hcL,
    hWR, hWR0, hηR, hτTR, hpcR, hagR, hWL, hWL0, hηL, hτTL, hpcL, hagL,
    hs₀R, hs₀tR, htτR, hinjR, hHR, hs₀L, hs₀tL, htτL, hinjL, hHL,
    hp, hlater, hr, hcontR, hcontL, hagree, hlocL⟩ := hω pR hpR pL hpL S hS hSc hSn
  have hrR := fun j c θ hl => pieceRegular_of_event hωR j c θ hl
  set p : ℂ := pcR.1.2.1 (ηR tR) with hpdef
  have htR : 0 ≤ tR := hs₀R.trans hs₀tR.le
  have htL : 0 ≤ tL := hs₀L.trans hs₀tL.le
  have hHR' : ∀ s ∈ Icc tR ((τR : ℝ≥0) : ℝ), ηR s ∈ H := fun s hs => hHR s ⟨hs₀tR.trans_le hs.1, hs.2⟩
  have hHL' : ∀ s ∈ Icc tL ((τL : ℝ≥0) : ℝ), ηL s ∈ H := fun s hs => hHL s ⟨hs₀tL.trans_le hs.1, hs.2⟩
  have hagR' : EqOn (pieceDrv pcR) WR (Icc 0 ((τR : ℝ≥0) : ℝ)) := hagR.mono (Icc_subset_Icc_right hτTR.le)
  have hagL' : EqOn (pieceDrv pcL) WL (Icc 0 ((τL : ℝ≥0) : ℝ)) := hagL.mono (Icc_subset_Icc_right hτTL.le)
  -- the side points and the landings
  obtain ⟨yR, hyRs, hFyR, hlaterR⟩ :=
    exists_isLeftSidePt_of_cut (pc := pcR) (τ := (τR : ℝ≥0)) hηR hWR hWR0 hagR' htR htτR hinjR hHR'
  obtain ⟨yL, hyLs, hFyL, -⟩ :=
    exists_isLeftSidePt_of_cut (pc := pcL) (τ := (τL : ℝ≥0)) hηL hWL hWL0 hagL' htL htτL hinjL hHL'
  have hpH : ηR tR ∈ H := hHR' tR ⟨le_rfl, htτR.le⟩
  have hqH : ηL tL ∈ H := hHL' tL ⟨le_rfl, htτL.le⟩
  have hlandR : Tendsto (prefixChart pcR (τR : ℝ≥0)).2.1 (𝓝[H] (yR : ℂ)) (𝓝 p) :=
    tendsto_prefixChart_inv_of_eq hηR hWR hWR0 hcR hτTR hpcR hagR' hpH hFyR
  have hlandL : Tendsto (prefixChart pcL (τL : ℝ≥0)).2.1 (𝓝[H] (yL : ℂ)) (𝓝 p) := by
    rw [hp]
    exact tendsto_prefixChart_inv_of_eq hηL hWL hWL0 hcL hτTL hpcL hagL' hqH hFyL
  -- trace points are walk points
  have hwR : ∀ s ∈ Icc 0 ((τR : ℝ≥0) : ℝ), ηR s ∈ H → pcR.1.2.1 (ηR s) ∈ wsetOf (walkRuns κ b jumps E ω).1 :=
    fun s hs hsH => mem_wsetOf_of_model hsplitR hcR hηR hWR hWR0 hpcR hagR hs.1 (hs.2.trans_lt hτTR)
      (toNNReal_le_stop haliveR hs.2) hsH
  have hwL : ∀ s ∈ Icc 0 ((τL : ℝ≥0) : ℝ), ηL s ∈ H → pcL.1.2.1 (ηL s) ∈ wsetOf (walkRuns κ b jumps E ω).2 :=
    fun s hs hsH => mem_wsetOf_of_model hsplitL hcL hηL hWL hWL0 hpcL hagL hs.1 (hs.2.trans_lt hτTL)
      (toNNReal_le_stop haliveL hs.2) hsH
  have hpR : p ∈ wsetOf (walkRuns κ b jumps E ω).1 := hwR tR ⟨htR, htτR.le⟩ hpH
  have hpL : p ∈ wsetOf (walkRuns κ b jumps E ω).2 := by
    rw [hp]; exact hwL tL ⟨htL, htτL.le⟩ hqH
  refine ⟨⟨preR, postR, preL, postL, pcR, pcL, τR, τL, yR, yL, p, r, hsplitR, haliveR, hyRs,
    hsplitL, haliveL, hyLs, hlandR, hlandL, ⟨hpR, hpL⟩, hr, hcontR, hcontL, hagree⟩, ?_⟩
  -- the incident-side identification
  have hlocal : ∃ ρ > 0, ∀ s ∈ Icc 0 ((τR : ℝ≥0) : ℝ), ηR s ∈ H → pcR.1.2.1 (ηR s) ∈ ball p ρ →
      ∃ s' ∈ Icc 0 ((τL : ℝ≥0) : ℝ), ηL s' ∈ H ∧ pcR.1.2.1 (ηR s) = pcL.1.2.1 (ηL s') := by
    refine ⟨r, hr, fun s hs hsH hsb => ?_⟩
    have hmem : pcR.1.2.1 (ηR s) ∈ wsetOf (walkRuns κ b jumps E ω).2 ∩ ball p r := by
      rw [← hagree]; exact ⟨hwR s hs hsH, hsb⟩
    exact hlocL _ hmem
  have hdom : ∃ ρ > 0, ∀ z ∈ H, (pcR.1.loewner WR ((τR : ℝ≥0) : ℝ)).2.1 z ∈ ball p ρ →
      (pcR.1.loewner WR ((τR : ℝ≥0) : ℝ)).2.1 z ∈ (pcL.1.loewner WL ((τL : ℝ≥0) : ℝ)).2.1 '' H := by
    obtain ⟨ρ₀, hρ₀, hball⟩ := exists_ball_mem_loewner_image hcL hηL hWL hWL0 hs₀L hs₀tL htτL.le hinjL hHL
    obtain ⟨hcR', -⟩ := prefixChart_props (κ := κ) (b := b) (jumps := jumps) _ _ _
      (fun j _ c θ hl => hrR j c θ hl) (fun j => hreg _ j ω) hsplitR haliveR
    have hdisj := WalkIntBridge.prefixChart_disjoint_prefixSet (κ := κ) (b := b) (jumps := jumps)
      (-(Real.pi / 2)) true _ hrR (fun j => hreg _ j ω) hsplitR haliveR
    refine ⟨min ρ₀ r, lt_min hρ₀ hr, fun z hz hzb => ?_⟩
    have hinv : (prefixChart pcR (τR : ℝ≥0)).2.1 z = (pcR.1.loewner WR ((τR : ℝ≥0) : ℝ)).2.1 z :=
      prefixChart_inv_eq_loewner hWR hpcR hagR hτTR z
    set w := (pcR.1.loewner WR ((τR : ℝ≥0) : ℝ)).2.1 z with hwdef
    have hwdom : w ∈ ((prefixChart pcR (τR : ℝ≥0)).dom : Set ℂ) := by
      rw [← hinv]; exact hcR'.inv_mem_dom hz
    refine hball w ?_ fun ⟨v, ⟨s, hs, hsv⟩, hvw⟩ => ?_
    · rw [← hp]; exact ball_subset_ball (min_le_left _ _) hzb
    · have hsH : ηL s ∈ H := hHL s hs
      have hwL' : w ∈ wsetOf (walkRuns κ b jumps E ω).2 ∩ ball p r := by
        refine ⟨?_, ball_subset_ball (min_le_right _ _) hzb⟩
        rw [← hvw, ← hsv]
        exact hwL s ⟨hs₀L.trans hs.1.le, hs.2⟩ hsH
      rw [← hagree] at hwL'
      exact Set.disjoint_left.1 hdisj hwdom (hcontR hwL')
  obtain ⟨G⟩ := nonempty_sideIdentification hcR hcL hηR hWR hWR0 hηL hWL hWL0 htR htτR hHR' htL htτL hinjL hHL'
    hyRs.1 hFyR hlaterR hyLs.1 hFyL hp hlater hlocal hdom
  exact ⟨SideIdentification.congrInv G (prefixChart_inv_eq_loewner hWR hpcR hagR hτTR)
    (prefixChart_inv_eq_loewner hWL hpcL hagL hτTL)⟩

/-- PROVE-T14-WALKINF's `WalkPairGeomCOStatement` from the bookkeeping of the common arc and GW1 piece simplicity. -/
theorem walkPairGeomCOStatement_of_arcData (hS : GW1Z.GW1PieceSimpleStatement.{u})
    (hdata : WalkPairArcDataStatement.{u}) : WalkInf.WalkPairGeomCOStatement.{u} :=
  WalkIntBridge.walkPairGeomCOStatement_of_accessGeometry hS (walkPairAccessGeometryStatement_of_arcData hdata)

/-- **Theorem 1.4's leaf `WalkBdry.WalkPairGeomStatement`** from the bookkeeping of the common arc, the contact
order, the proper walk parametrizations and GW1 piece simplicity. -/
theorem walkPairGeomStatement_of_arcData (hCO : GW4BarrierSelf.WalkContactOrderRegStatement.{u})
    (hPR : WalkCont.RightWalkProperRegStatement.{u}) (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u})
    (hS : GW1Z.GW1PieceSimpleStatement.{u}) (hdata : WalkPairArcDataStatement.{u}) :
    WalkBdry.WalkPairGeomStatement.{u} :=
  walkPairGeomStatement_of_co hCO hPR hPL (walkPairGeomCOStatement_of_arcData hS hdata)

end InteractingSLE.Theorem14.WalkWords
