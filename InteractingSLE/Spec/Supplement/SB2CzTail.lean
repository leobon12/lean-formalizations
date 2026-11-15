/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CzCanon
import InteractingSLE.Spec.Supplement.SB2CzLaw
import InteractingSLE.Spec.Supplement.SB2FlZero

/-!
# `Mz.TailCanonAt ℓ` from the retained law of the induction and the chain facts

Packet PROVE-SB2-CANON. **`tailCanonAt_of_mvLaw`** reduces one stage of the target `Mz.SB2LowerStageCanonStatement`
to the outputs of the producers, in the form they produce them:

* the retained law `Fl.MvLaw` at B's stage `ℓ` (F3LAW's step / the base laws), given marks `𝓜` between the retained
  past `Ms.stageMarks ℓ` and `mΩ`, for some retained hull `K'` and a word `β` measurable for the completed retained
  past, on an event containing almost every launch of B's stage `ℓ`, the retained set being `fill (A ∪ B_{<ℓ})` there;
* an offset `x₀` measurable for the completed retained past (F2b′'s `x₀` once shown to be a function of it);
* an event `T` of `Ms.stageMarks (ℓ + 1)` containing almost every tail launch of positive lifetime;
* almost surely on `T`, at a launch of positive lifetime, the chain facts `Qx.ChainFacts` of the canonical driver for
  `K'`, `x₀` and the word `shiftW x₀ β` (the identification of B's piece with the canonical code).

The exact objects of `Mz.TailCanonAt` are built here: the hull `exists_exactRetHull`, an exact version of `x₀`, the word
and its law given the retained past (`exists_stageLaw_of_mvLaw`), and the event `G = G₁ ∩ {ζ_ℓ ≠ 0} ∩ T` of
`Ms.stageMarks (ℓ + 1)` (`chainFacts_congr` moves the chain facts to the exact objects).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.Staged Exist.StagedLaw Lu Mx Mz LocalSets

/-- **The chain facts depend on the hull only through its fill**, and on the word and offset only at the sample. -/
theorem chainFacts_congr (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ}
    {jumps : Finset ℝ} {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0))
    (k ℓ : ℕ) {h : Ω → DistOn upperHalfPlaneOpens} {c c' : Ω → BoundaryWord} {K K' : Ω → Set ℂ} {x₀ x₀' : Ω → ℝ}
    {hKc : ∀ ω, IsCompact (K ω)} {hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)}
    {hK'c : ∀ ω, IsCompact (K' ω)} {hK'p : ∀ ω, IsPreconnected (K' ω ∪ Restart.lowerHalf)} {ω : Ω}
    (hK : fillH (K ω) = fillH (K' ω)) (hc : c ω = c' ω) (hx : x₀ ω = x₀' ω)
    (hf : Qx.ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h c' x₀' hK'c hK'p ω) :
    Qx.ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h c x₀ hKc hKp ω := by
  have hchart : Mo.hullChart (fillH (K ω)) (x₀ ω) = Mo.hullChart (fillH (K' ω)) (x₀' ω) := by rw [hK, hx]
  have hfield : Fl.canonField κ h x₀ hKc hKp ω = Fl.canonField κ h x₀' hK'c hK'p ω := by
    have ht := Fl.isChartTransport_canonField κ h x₀ hKc hKp ω
    rw [hchart] at ht
    exact Fl.canonField_eq_of_transport (K := K') (x₀ := x₀') hK'c hK'p ht
  have hdrv : Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω = Qx.canonDrvAt h12p hκ h c' x₀' hK'c hK'p ω := by
    change driverOf h12p hκ (-(Real.pi / 2)) (c ω, Fl.canonField κ h x₀ hKc hKp ω) =
      driverOf h12p hκ (-(Real.pi / 2)) (c' ω, Fl.canonField κ h x₀' hK'c hK'p ω)
    rw [hc, hfield]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf
  refine ⟨h1, ?_, h3, ?_, ?_, ?_⟩
  · rw [hchart]; exact h2
  · rw [hchart, hdrv]; exact h4
  · rw [hdrv]; exact h5
  · rw [hdrv]; exact h6

/-- **`Mz.TailCanonAt ℓ` from the retained law of the induction and the chain facts.** -/
theorem tailCanonAt_of_mvLaw (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    -- the retained law at `ℓ`
    (h𝒮𝓜 : Ms.stageMarks κ b jumps E u l k ℓ ≤ 𝓜) (h𝓜 : 𝓜 ≤ mΩ)
    {A K' : Ω → Set ℂ} {G' : Set Ω} {Y : Ω → DistOn upperHalfPlaneOpens} {β : Ω → BoundaryWord} {M : ℝ}
    (hlaw : Fl.MvLaw κ 𝓜 P h A K' G' Y β M) (hβ : Measurable[aeSigma (Ms.stageMarks κ b jumps E u l k ℓ) P] β)
    (hcovL : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → ω ∈ G')
    (hA : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → A ω = fillH (Nc.retX κ b jumps E u l k ℓ ω))
    -- the offset
    {x₀ : Ω → ℝ} (hx₀ : Measurable[mΩ ⊓ aeSigma (Ms.stageMarks κ b jumps E u l k ℓ) P] x₀)
    -- the tail event
    {T : Set Ω} (hT : MeasurableSet[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] T)
    (hTcov : ∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω)
        (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (lowerD b jumps E ω) + 2 ≤ ℓ →
      (lowerD b jumps E ω ℓ).2 ≠ 0 → ω ∈ T)
    -- the chain facts (identification of B's piece with the canonical code)
    (hfacts : ∀ᵐ ω ∂P, ω ∈ T → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → (lowerD b jumps E ω ℓ).2 ≠ 0 →
      Qx.ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h (fun ω => BoundaryWord.shiftW (x₀ ω) (β ω)) x₀
        hlaw.2.1 hlaw.2.2.1 ω) :
    TailCanonAt h12p hκ b jumps P h E u l k ℓ := by
  classical
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hw : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu : IsBoundaryContinuedProgram (upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have h𝒮 : Ms.stageMarks κ b jumps E u l k ℓ ≤ mΩ := h𝒮𝓜.trans h𝓜
  have h𝒮₁ : Ms.stageMarks κ b jumps E u l k (ℓ + 1) ≤ mΩ :=
    sup_le ((hE' _ hsu).2.1 k) ((hE' w hw).2.1 (ℓ + 1))
  have hmono : Ms.stageMarks κ b jumps E u l k ℓ ≤ Ms.stageMarks κ b jumps E u l k (ℓ + 1) :=
    stageMarks_mono (Nat.le_succ ℓ)
  -- the exact hull
  obtain ⟨K, G₁, hKm, hKc, hKp, hG₁, hG₁cov, hG₁f⟩ :=
    exists_exactRetHull h12p h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ hu₀
  -- the exact offset
  have hx₀Ω : Measurable x₀ := hx₀.mono inf_le_left le_rfl
  have hx₀k : ∀ᵐ ω₀ ∂P, ω₀ ∈ (univ : Set Ω) →
      ∀ᵐ ω ∂(condExpKernel P (Ms.stageMarks κ b jumps E u l k ℓ) ω₀), x₀ ω = x₀ ω₀ := by
    filter_upwards [ae_ae_eq_of_measurable_aeSigma h𝒮 hx₀] with ω₀ h1 _ using h1
  obtain ⟨x₁, hx₁m, hx₁e⟩ := Qx.exists_measurable_ae_eq_of_kernel_const (P := P) h𝒮 hx₀Ω hx₀k
  -- the law given the retained past
  have hG₁G' : ∀ᵐ ω ∂P, ω ∈ G₁ → ω ∈ G' := by
    filter_upwards [hG₁f, hcovL] with ω h1 h2 hω using h2 (h1 hω).1
  have hKA : ∀ᵐ ω ∂P, ω ∈ G₁ → fillH (K ω) = A ω := by
    filter_upwards [hG₁f, hA] with ω h1 h2 hω using (h1 hω).2.trans (h2 (h1 hω).1).symm
  obtain ⟨c, hcm, hce, hlawc⟩ :=
    exists_stageLaw_of_mvLaw h𝒮𝓜 h𝓜 hh.1 hlaw hβ hKc hKp hKm hx₁m hG₁ hG₁G' hKA
  -- the zero-lifetime event of B's piece `ℓ`
  set Z : Set Ω := {ω | ((ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω) (ℓ + 1)).2.2.1 ℓ).2.1 ≠ 0}
    with hZdef
  have hZ : MeasurableSet[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] Z := by
    refine le_sup_right (a := pastSigma κ b jumps (upperSpec u l) (StagedReg.regFam E (upperSpec u l)) k) _ ?_
    have hm : Measurable[pastSigma κ b jumps w (StagedReg.regFam E w) (ℓ + 1)]
        (pastMap κ b jumps w (StagedReg.regFam E w) (ℓ + 1)) := Measurable.of_comap_le le_rfl
    have hc : Measurable[pastSigma κ b jumps w (StagedReg.regFam E w) (ℓ + 1)] fun ω =>
        (pastMap κ b jumps w (StagedReg.regFam E w) (ℓ + 1) ω ⟨ℓ, Nat.lt_succ_self ℓ⟩).2.1 :=
      measurable_fst.comp (measurable_snd.comp ((measurable_pi_apply _).comp hm))
    exact (measurableSet_eq_fun hc measurable_const).compl
  -- the event `G`
  set G : Set Ω := G₁ ∩ Z ∩ T with hGdef
  have hG : MeasurableSet[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] G := ((hmono _ hG₁).inter hZ).inter hT
  -- on a launch, `Z` is the positivity of the raw lifetime
  have hZiff : ∀ᵐ ω ∂P, (ExplState.run κ b jumps w (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      (ω ∈ Z ↔ (lowerD b jumps E ω ℓ).2 ≠ 0) := by
    filter_upwards [hrun w hw] with ω hr hl
    have hlr : (ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      rw [hr (ℓ + 1)]; exact hl
    have e : ((ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω) (ℓ + 1)).2.2.1 ℓ).2.1 =
        (lowerD b jumps E ω ℓ).2 := by
      rw [hr (ℓ + 1)]
      exact Fl.retained_lifetime_of_launch hl
    simp only [hZdef, mem_ofPred_eq, e]
  have hRw := hER w hw
  have hRu := hER _ hsu
  refine tailCanonAt_of_chainFacts h12p hκ b jumps P h E u l k ℓ hRw hRu h𝒮₁ hh.1 hKc hKp hcm hKm hx₁m hG ?_ ?_
    ?_ ?_
  · filter_upwards [hlawc] with ω₁ h1 hω₁ using h1 hω₁.1.1
  · filter_upwards [hG₁cov, hZiff, hTcov] with ω h1 h2 h3 hup hl htail hz
    exact ⟨⟨h1 hl, (h2 hl).2 hz⟩, h3 hup hl htail hz⟩
  · filter_upwards [hG₁f] with ω h1 hω using (h1 hω.1.1).2
  · filter_upwards [hG₁f, hfacts, hZiff, hce, hx₁e, hlaw.2.2.2.2.1, hG₁G', hA] with ω h1 h2 h3 h4 h5 h6 h7 h8 hω
    obtain ⟨hl, hfK⟩ := h1 hω.1.1
    have hz : (lowerD b jumps E ω ℓ).2 ≠ 0 := (h3 hl).1 hω.1.2
    have hfK' : fillH (K' ω) = fillH (K ω) := by
      rw [h6 (h7 hω.1.1), h8 hl]; exact hfK.symm
    have hx : x₁ ω = x₀ ω := (h5 (mem_univ ω)).symm
    refine chainFacts_congr h12p hκ E u l k ℓ hfK'.symm ?_ hx (h2 hω.2 hl hz)
    rw [h4 hω.1.1, hx]

end InteractingSLE.Theorem14.SB.Cz
