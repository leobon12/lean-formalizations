/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JLower
import InteractingSLE.Spec.Supplement.SBLyLeaf

/-!
# SB4's tail sewing with the amended SB3 (ruling R95): SB2(2) supplies the premise

Packet PROVE-T14-SBLEAVES5. PROVE-T14-SB2FIN4's feed `Lu.ae_actualTailSewing_of_sb2LowerLaunchEntry` and its
consumer `Retain.ae_actualTailSewing_of_frame_word` apply the old `SB.SB3InductionGenStatement`, which is believed
false (F9; ruling R95). Here they are repeated with the amended `Ly.SB3InductionGenRStatement`, whose premise
`Ly.LowerLeftAdmissible` must hold for the relative data `affData 1 m b'` of SB2(2)'s lower tail.

The source states it inside SB2(2) (supplement p. 632, `source/spec/p625-671.md` L141, (SB2.1)): "All these old groups
are admissible. Any surviving initial-bridge intervals have their original lower groups, admissible by the bridge
hypothesis. All original-real groups and the lower walk's low connectors have their original weights". On the
interval `(m, 0)` between the upper tip and the entry point it follows from SB2(2)'s active word
(`Lu.IsActiveHighWord`) and the bridge hypothesis (`lowerLeftAdmissible_of_activeHighWord`); left of the upper tip
(`y ≤ m`, the old upper-left sides and the original boundary left of the upper seed) SB2(2)'s Lean statement records
no word, so that clause is added:

* `ae_actualTailSewing_of_frame_wordR` (the consumer with the amended SB3 and the premise);
* `lowerLeftAdmissible_of_activeHighWord` (the premise from the active word, the bridge hypothesis and the clause
  left of the tip);
* **`SB2LowerLaunchEntryAdmStatement`**: `Lu.SB2LowerLaunchEntryStatement` with the admissibility of the relative
  word left of the upper tip (named input; it implies the landed statement, `sb2LowerLaunchEntryStatement_of_adm`);
* **`ae_actualTailSewing_of_sb2LowerLaunchEntryAdm`**: the feed with the amended SB3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lz

open Lx Lu Leaf FlowDilate Sec4 Exist.Staged Exist.StagedLaw

/-- **SB4's tail sewing with the amended SB3** (`Retain.ae_actualTailSewing_of_frame_word` with
`Ly.SB3InductionGenRStatement` and its premise on the relative data). -/
theorem ae_actualTailSewing_of_frame_wordR
    (hSB3 : Ly.SB3InductionGenRStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {bc : ℝ → ℝ} {jc : Finset ℝ} (hbc : IsPiecewiseConstantBoundaryData bc jc)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {hl : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {θ : ℝ}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ bc jc θ Q hl W ζ)
    {m : ℝ} (hm : m ≤ 0) {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hEL : IsBoundaryContinuedProgram
        (boundaryWalkSpec (affData 1 m bc) (affJumps 1 m jc) (-(Real.pi / 2)) true).2.2 →
      IsStagedHistory κ (affData 1 m bc) (affJumps 1 m jc) Q
          (fun ω => affField m one_pos (hl ω))
          (boundaryWalkSpec (affData 1 m bc) (affJumps 1 m jc) (-(Real.pi / 2)) true) EL ∧
        StagedPiecesRegular κ (affData 1 m bc) (affJumps 1 m jc) Q
          (boundaryWalkSpec (affData 1 m bc) (affJumps 1 m jc) (-(Real.pi / 2)) true) EL)
    (hadm : Ly.LowerLeftAdmissible κ (affData 1 m bc) (affJumps 1 m jc))
    {l : List (ℝ × ℝ≥0)} {original : Set ℝ}
    (hangles : ∀ p ∈ l, -(Real.pi / 2) < p.1)
    (hgaps : ∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ)
    (hbridge : ∀ p ∈ l, ∀ B ∈ original,
      -2 < Sec4.cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ) ∧
        (-2 < Sec4.cumWeightRight κ (B + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ)))
    (hθ : ∃ q ∈ l, θ = q.1)
    (hclass : ∀ y ∈ Ioo m 0, y ∉ affJumps 1 m jc →
      (∃ p ∈ l, affData 1 m bc y = sleLambda κ - p.1 * chiC κ ∨
          affData 1 m bc y = -sleLambda κ - p.1 * chiC κ) ∨
        affData 1 m bc y ≤ -sleLambda κ - -(Real.pi / 2) * chiC κ ∨
          affData 1 m bc y ∈ original)
    (hpos : ∀ᵐ ω ∂Q, 0 < ζ ω)
    {f : ℂ → ℂ} {A S : Ω → Set ℂ} {T : ℝ≥0∞}
    (hread : ∀ᵐ ω ∂Q, A ω ⊆ f '' (GW2aSingle.chosenTrace W ζ ω ''
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ min T (ζ ω)}))
    (hframe : ∀ᵐ ω ∂Q, Retain.RetainedTailFrame f (S ω)
      (relWalkSet κ (affData 1 m bc) (affJumps 1 m jc) EL ω) m) :
    ∀ᵐ ω ∂Q, HasActualTailSewing (A ω) (S ω) := by
  obtain ⟨hbcM, hGM, hflow⟩ := relFlowLine_of_isFlowLineDriver h13 hκ hbc hfl m
  have hword : IsRelSB3WordInstance κ Q (fun ω => affField m one_pos (hl ω))
      (affData 1 m bc) (affJumps 1 m jc) EL m θ
      (fun ω t => aff 1 m (GW2aSingle.chosenTrace W ζ ω t)) ζ l original :=
    ⟨hbcM, hGM, hEL, hm, hθ, hclass, hflow, hpos⟩
  have hS1 := Ly.ae_isOneSided_of_relSB3InstanceR hSB3 h12 h13 hκ hκ4
    ⟨isRelSB3Instance_of_word hκ hκ4 hangles hgaps hbridge hword, hadm⟩
  have hgeo := Retain.ae_relTailGeometry_of_frame_readout h13 hκ hfl hread hframe
  filter_upwards [hS1, hgeo] with ω hSω hgω
  exact hgω.hasActualTailSewing hSω

/-- **R95's premise for SB2(2)'s relative data from its active word** (supplement p. 632, (SB2.1)): on `(m, 0)` every
height is an old upper side `λ − ψχ` or `−λ − ψχ` of an angle `ψ > −π/2` (left weight `−2 + (ψ + π/2)χ/λ > −2`,
resp. `(ψ + π/2)χ/λ > 0`), a low height, or a retained bridge height (admissible by the bridge hypothesis); left of the
upper tip the clause `hleft` is used. -/
theorem lowerLeftAdmissible_of_activeHighWord {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, -(Real.pi / 2) < p.1)
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    {b' : ℝ → ℝ} {jumps' : Finset ℝ} {m : ℝ}
    (hleft : ∀ y, y ≤ m → y ∉ affJumps 1 m jumps' →
      -2 < cumWeightLeft κ (affData 1 m b' y + -(Real.pi / 2) * chiC κ))
    (hword : IsActiveHighWord κ b jumps u l b' jumps' m) :
    Ly.LowerLeftAdmissible κ (affData 1 m b') (affJumps 1 m jumps') := by
  intro y hy hyJ
  rcases le_or_gt y m with hym | hmy
  · exact hleft y hym hyJ
  have hlam := sleLambda_pos hκ
  have hchi := chiC_pos hκ hκ4
  rcases hword y ⟨hmy, hy⟩ hyJ with ⟨p, hp, hv | hv⟩ | hv | ⟨z, ⟨hz, hzJ⟩, hv⟩
  · refine Ly.cumWeightLeft_gt_of_height_lt hκ ?_
    rw [hv]
    have := hlθ p hp
    nlinarith
  · refine Ly.cumWeightLeft_gt_of_height_lt hκ ?_
    rw [hv]
    have := hlθ p hp
    nlinarith
  · refine Ly.cumWeightLeft_gt_of_height_lt hκ ?_
    linarith
  · rw [← hv]
    exact hL z hz hzJ

/-- **Lemma SB2(2), entry form, with the admissibility of the relative word left of the upper tip** (named input;
supplement p. 632, `source/spec/p625-671.md` L141: "All these old groups are admissible [...] All original-real groups
[...] have their original weights"). `Lu.SB2LowerLaunchEntryStatement` with one more conclusion: at every point
`y ≤ m` of the lower tail's frame off the jumps (left of the upper tip: the old upper-left sides, of left weight
`(ψ_j + π/2)χ/λ > 0`, and the original boundary left of the upper seed, admissible by the counterflow's ambient
bound), the lower-flow left cumulative weight exceeds `−2`. -/
def SB2LowerLaunchEntryAdmStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1)).2.2.2.1 k =
            some (c, θ) →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
            h' b' jumps' →
          ∃ (m : ℝ) (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), m ≤ 0 ∧
            (∀ y, y ≤ m → y ∉ affJumps 1 m jumps' →
              -2 < cumWeightLeft κ (affData 1 m b' y + -(Real.pi / 2) * chiC κ)) ∧
            IsRightEntryValue c (realMax (upperPrefix κ b jumps E u l k ω₀)) (-m) ∧
            IsActiveHighWord κ b jumps u l b' jumps' m ∧
            IsStagedHistory κ (affData 1 m b') (affJumps 1 m jumps')
              (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
              (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' jumps' m) EL ∧
            StagedPiecesRegular κ (affData 1 m b') (affJumps 1 m jumps')
              (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
              (relLowerSpec b' jumps' m) EL ∧
            (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
              WalkRightAdds κ (affData 1 m b') (affJumps 1 m jumps') (fun _ => EL) ω) ∧
            ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
              lowerWalkSet κ b jumps E ω ∩ (H \ fillH (upperPrefix κ b jumps E u l k ω)) ⊆
                  relPhysSet κ (affData 1 m b') (affJumps 1 m jumps') (c.recenter (-m))
                    (relLowerSpec b' jumps' m) (fun j => EL j ω) ∧
                relPhysSet κ (affData 1 m b') (affJumps 1 m jumps') (c.recenter (-m))
                    (relLowerSpec b' jumps' m) (fun j => EL j ω) ⊆ lowerWalkSet κ b jumps E ω

/-- The amended SB2(2) implies the landed entry form (the added clause is dropped). -/
theorem sb2LowerLaunchEntryStatement_of_adm (h : SB2LowerLaunchEntryAdmStatement.{u}) :
    SB2LowerLaunchEntryStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ hf hh W' ζ' hcf hζ' E hE hER u l k hu hl hlθ hL hleft
  filter_upwards [h κ hκ hκ4 b jumps hb P hf hh W' ζ' hcf hζ' E hE hER u l k hu hl hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  obtain ⟨m, EL, hm, -, rest⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG'
  exact ⟨m, EL, hm, rest⟩

/-- **SB2(2) feeds SB4's consumer with the amended SB3** (`Lu.ae_actualTailSewing_of_sb2LowerLaunchEntry` with
`Ly.SB3InductionGenRStatement`; R95's premise on the relative data from `SB2LowerLaunchEntryAdmStatement`). Only the
consumer's own inputs `hpos`, `hread` and `hframe` remain. -/
theorem ae_actualTailSewing_of_sb2LowerLaunchEntryAdm (hSB2 : SB2LowerLaunchEntryAdmStatement.{u})
    (hSB3 : Ly.SB3InductionGenRStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} (hu : u ≤ 0) (hl : l.Pairwise (fun p q => p.2 < q.2))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hgaps : ∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ)
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hH : ∀ p ∈ l, ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + p.1 * chiC κ) ∨
      κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hleft : ∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1)).2.2.2.1 k =
          some (c, θ) →
      ∃ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens) (m : ℝ)
        (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
        IsPiecewiseConstantBoundaryData b' jumps' ∧ (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) ∧
        IsFlowLineDriver κ b' jumps' θ
          (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀) h'
          (fun t ω => (E (upperSpec u l) k ω).1 t) (fun ω => (E (upperSpec u l) k ω).2) ∧
        m ≤ 0 ∧ IsRightEntryValue c (realMax (upperPrefix κ b jumps E u l k ω₀)) (-m) ∧
        Ly.LowerLeftAdmissible κ (affData 1 m b') (affJumps 1 m jumps') ∧
        ∀ {f : ℂ → ℂ} {A S : Ω → Set ℂ} {T : ℝ≥0∞},
          (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
            0 < (E (upperSpec u l) k ω).2) →
          (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
            A ω ⊆ f '' (GW2aSingle.chosenTrace (fun t ω => (E (upperSpec u l) k ω).1 t)
              (fun ω => (E (upperSpec u l) k ω).2) ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ min T (E (upperSpec u l) k ω).2})) →
          (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
            Retain.RetainedTailFrame f (S ω) (relWalkSet κ (affData 1 m b') (affJumps 1 m jumps') EL ω) m) →
          ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
            HasActualTailSewing (A ω) (S ω) := by
  have hEu := hE _ (isBoundaryContinuedProgram_upperSpec (u := u) hlθ)
  filter_upwards [hSB2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hl hlθ hL hleft,
    hEu.2.2.2 k]
    with ω₀ hS hW
  intro c θ hlaunch
  obtain ⟨b', J', h', hb', hT', hfl⟩ := hW c θ hlaunch
  have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl
  obtain ⟨m, EL, hm, hlm, hent, hword, hst, hreg, -, -⟩ := hS c θ hlaunch b' J' h' hb' hT' hG'
  have hadm := lowerLeftAdmissible_of_activeHighWord hκ hκ4 (fun p hp => (hlθ p hp).1) hL hlm hword
  refine ⟨b', J', h', m, EL, hb', hT', hfl, hm, hent, hadm, ?_⟩
  intro f A S T hpos hread hframe
  have hθ : ∃ q ∈ l, θ = q.1 :=
    exists_mem_of_scheduleProgram_getElem? 0 l k (eq_launch_of_launches _ _ hlaunch).1
  exact ae_actualTailSewing_of_frame_wordR hSB3 h12 h13 hκ hκ4 hb' hfl hm (fun _ => ⟨hst, hreg⟩) hadm
    (fun p hp => (hlθ p hp).1) hgaps (distinctSeed_bridge hL hH) hθ hword hpos hread hframe

end InteractingSLE.Theorem14.SB.Lz
