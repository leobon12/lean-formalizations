/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CbConv
import InteractingSLE.Spec.Supplement.SB2CzHull
import InteractingSLE.Spec.Supplement.SB2CvOff

/-!
# The record of a tail stage for the induction's step (D80 item 2)

Packet PROVE-SB2-CANON, round 8. F3LAW's tail step `Fo.tail_step` takes the record matching `Dr` of B's stage `ℓ`: a
driver measurable for `Ms.stageMarks (ℓ + 1)`, regular at every sample, with almost surely on F2b′'s live event `F`
the record of the canonical driver of `(shiftW x₀ β, field in Mo.hullChart (fill K) x₀)` (F2b′'s `K`, `x₀`).

* **`canonDrvAt_congr`**: the canonical driver at a sample depends on the hull only through its fill, and on the word
  and the offset only at the sample;
* **`tail_record`**: `Dr` from the chain facts a.s. on `F` (CANON's (P4), `ae_chainFacts_tail`): the exact retained
  hull (`exists_exactRetHull`) and offset (`exists_offset_stageMarks`), the tail event of `Ms.stageMarks (ℓ + 1)`
  (`exists_eq_of_measurableSet_inf_aeSigma`), the chain facts moved to them (`chainFacts_congr`), and
  `Qx.exists_canonRec`.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Lv Lk Mf Ms Lu Mx Mz

/-- **The canonical driver at a sample depends on the hull only through its fill, on the word and offset only at the
sample.** -/
theorem canonDrvAt_congr (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {Ω : Type u}
    {h : Ω → DistOn upperHalfPlaneOpens} {c c' : Ω → BoundaryWord} {K K' : Ω → Set ℂ} {x₀ x₀' : Ω → ℝ}
    {hKc : ∀ ω, IsCompact (K ω)} {hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)}
    {hK'c : ∀ ω, IsCompact (K' ω)} {hK'p : ∀ ω, IsPreconnected (K' ω ∪ Restart.lowerHalf)} {ω : Ω}
    (hK : fillH (K ω) = fillH (K' ω)) (hc : c ω = c' ω) (hx : x₀ ω = x₀' ω) :
    Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω = Qx.canonDrvAt h12p hκ h c' x₀' hK'c hK'p ω := by
  have hchart : Mo.hullChart (fillH (K ω)) (x₀ ω) = Mo.hullChart (fillH (K' ω)) (x₀' ω) := by rw [hK, hx]
  have hfield : Fl.canonField κ h x₀ hKc hKp ω = Fl.canonField κ h x₀' hK'c hK'p ω := by
    have ht := Fl.isChartTransport_canonField κ h x₀ hKc hKp ω
    rw [hchart] at ht
    exact Fl.canonField_eq_of_transport (K := K') (x₀ := x₀') hK'c hK'p ht
  change driverOf h12p hκ (-(Real.pi / 2)) (c ω, Fl.canonField κ h x₀ hKc hKp ω) =
    driverOf h12p hκ (-(Real.pi / 2)) (c' ω, Fl.canonField κ h x₀' hK'c hK'p ω)
  rw [hc, hfield]

/-- **The record matching of a tail stage** (the `Dr` input of `Fo.tail_step`). See the module docstring. -/
theorem tail_record (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {𝓖 : Filtration ℝ≥0 mΩ}
    (h𝓖0 : 𝓖 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    {β : Ω → BoundaryWord} (hβm : Measurable β) {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {F : Set Ω}
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hx₀ : Measurable[lineFiltC P 𝓖 0] x₀) (hF : MeasurableSet[lineFiltC P 𝓖 0] F)
    (hFl : ∀ᵐ ω ∂P, ω ∈ F → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none ∧
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2)
    (hFfill : ∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = fillH (Nc.retX κ b jumps E u l k ℓ ω))
    (hfacts : ∀ᵐ ω ∂P, ω ∈ F → Qx.ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h
      (fun ω => BoundaryWord.shiftW (x₀ ω) (β ω)) x₀ hKc hKp ω) :
    ∃ Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, Measurable[stageMarks κ b jumps E u l k (ℓ + 1)] Dr ∧
      (∀ ω, IsRegularDriver (Dr ω)) ∧
      ∀ᵐ ω ∂P, ω ∈ F → recOf ⊤ (Dr ω) = recOf ⊤ (driverOf h12p hκ (-(Real.pi / 2))
        (BoundaryWord.shiftW (x₀ ω) (β ω), Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ)
          (h ω))) := by
  classical
  obtain ⟨hE', hreg', hrun'⟩ := StagedReg.regFam_spec hb hE hER
  have hw : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have h𝒮₁ : Ms.stageMarks κ b jumps E u l k (ℓ + 1) ≤ mΩ :=
    sup_le ((hE' _ hsu).2.1 k) ((hE' _ hw).2.1 (ℓ + 1))
  have hmono : Ms.stageMarks κ b jumps E u l k ℓ ≤ Ms.stageMarks κ b jumps E u l k (ℓ + 1) :=
    Mz.stageMarks_mono (Nat.le_succ ℓ)
  have hG0 : pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ≤
      mΩ := by rw [← h𝓖0]; exact 𝓖.le 0
  have hx₀' : Measurable[mΩ ⊓ aeSigma (pastSigma κ b jumps (Lu.upperSpec u l)
      (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        (ℓ + 1)) P] x₀ := by
    rw [← h𝓖0]; exact hx₀
  have hF' : MeasurableSet[mΩ ⊓ aeSigma (pastSigma κ b jumps (Lu.upperSpec u l)
      (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        (ℓ + 1)) P] F := by
    rw [← h𝓖0]; exact hF
  -- the exact hull, the exact offset and the tail event
  obtain ⟨K₁, G₁, hK₁m, hK₁c, hK₁p, hG₁, hG₁cov, hG₁f⟩ :=
    exists_exactRetHull h12p h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ hu₀
  obtain ⟨x₁, hx₁m, hx₁e⟩ := exists_offset_stageMarks E u l k ℓ hℓ hwℓ hG0 hx₀'
  obtain ⟨T, hTm, hFT⟩ := exists_eq_of_measurableSet_inf_aeSigma
    (capPast_le_stageMarks_succ E u l k ℓ hℓ hwℓ) hF'
  have hc₁m : Measurable fun ω => BoundaryWord.shiftW (x₁ ω) (β ω) :=
    BoundaryWord.measurable_shiftW.comp ((hx₁m.mono (hmono.trans h𝒮₁) le_rfl).prodMk hβm)
  -- on a launch of positive lifetime the two offsets agree
  have hxeq : ∀ᵐ ω ∂P, ω ∈ F → x₀ ω = x₁ ω := by
    filter_upwards [hFl, hx₁e, hrun' _ hw] with ω h1 h2 hrw hωF
    obtain ⟨hl, hpos⟩ := h1 hωF
    have hlr : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠
        none := by rw [hrw (ℓ + 1)]; exact hl
    have hlife : (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 =
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 := by
      have e1 := Fl.retained_lifetime_of_launch hlr
      have e2 := Fl.retained_lifetime_of_launch hl
      rw [hrw (ℓ + 1)] at e1
      exact e1.symm.trans e2
    exact h2 hlr (by rw [hlife]; exact (pos_iff_ne_zero.1 hpos)) (hreg' _ ℓ ω).2.1
  -- the chain facts on the event `G₁ ∩ T` of `Ms.stageMarks (ℓ + 1)`, for the exact objects
  have hG : MeasurableSet[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] (G₁ ∩ T) := (hmono _ hG₁).inter hTm
  have hfacts₁ : ∀ᵐ ω ∂P, ω ∈ G₁ ∩ T →
      Qx.ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h (fun ω => BoundaryWord.shiftW (x₁ ω) (β ω)) x₁
        hK₁c hK₁p ω := by
    filter_upwards [hFT.mem_iff, hfacts, hG₁f, hFfill, hxeq] with ω hFTω hf hG₁ω hfill hx hω
    have hωF : ω ∈ F := hFTω.2 hω.2
    have hK : fillH (K₁ ω) = fillH (K ω) := by rw [(hG₁ω hω.1).2, hfill hωF]
    exact chainFacts_congr h12p hκ E u l k ℓ hK (by simp only [hx hωF]) (hx hωF).symm (hf hωF)
  obtain ⟨Dr, hDrm, hDrreg, hDreq⟩ := Qx.exists_canonRec h12p hκ E u l k ℓ (hER _ hw) (hER _ hsu) h𝒮₁ hh.1 hc₁m
    hK₁c hK₁p (fun n j => hmono _ (hK₁m n j)) (hx₁m.mono hmono le_rfl) hG hfacts₁
  refine ⟨Dr, hDrm, hDrreg, ?_⟩
  filter_upwards [hDreq, hFT.mem_iff, hG₁cov, hG₁f, hFfill, hxeq, hFl] with ω hD hFTω hcov hG₁ω hfill hx hl hωF
  have hωG₁ : ω ∈ G₁ := hcov (hl hωF).1
  have hK : fillH (K₁ ω) = fillH (K ω) := by rw [(hG₁ω hωG₁).2, hfill hωF]
  have hdrv := canonDrvAt_congr h12p hκ (h := h) (c := fun ω => BoundaryWord.shiftW (x₁ ω) (β ω))
    (c' := fun ω => BoundaryWord.shiftW (x₀ ω) (β ω)) (hKc := hK₁c) (hKp := hK₁p) (hK'c := hKc) (hK'p := hKp)
    hK (by simp only [hx hωF]) (hx hωF).symm
  change recOf ⊤ (Dr ω) = recOf ⊤ (Qx.canonDrvAt h12p hκ h (fun ω => BoundaryWord.shiftW (x₀ ω) (β ω)) x₀ hKc hKp ω)
  rw [hD ⟨hωG₁, hFTω.1 hωF⟩, hdrv]

end InteractingSLE.Theorem14.SB.Cz
