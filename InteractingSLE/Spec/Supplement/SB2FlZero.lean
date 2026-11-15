/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FlTail

/-!
# The step `ℓ → ℓ + 2` of SB2(2)'s retained-law induction at a piece of lifetime `0`

Worker PROVE-SB2-F3LAW (target 1). When B's piece `ℓ` has lifetime `0` (a launch from an inadmissible seed; D26: these
have positive probability), the piece is its real seed and the connector `ℓ + 1` launches nothing, so the retained set
through the start of stage `ℓ + 2` is the one before `ℓ` (`Qx.stageSet_succ_succ_eq_of_zero`; the zero-time piece of
stage `ℓ + 2` adds no point of `ℍ`, `stageSet_capSpec_zero_succ`). The law therefore passes to the larger marks of stage
`ℓ + 2` with the same hull, field and word, by the landed core `Qw.ae_isGFF_of_coarse_of_marked_on` (the marked kernel
of the retained union and the nested Gaussian identity).

* `retained_lifetime_of_launch`;
* **`mvLaw_piecewise`**: two retained laws on two events glue into one (piecewise hull, field, word);
* **`mvLaw_succ_succ_zero`**: `MvLaw` at `ℓ` ⇒ `MvLaw` at `ℓ + 2` with the same `K`, `Y`, `β`, `M`, on an event
  containing almost surely the samples of the law's event where B launches at `ℓ` a piece of lifetime `0` and launches
  again at `ℓ + 2`.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fl

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Supp8.Q3Stop Lv Lk Mf Ms Qw

/-- At a launch of the walk at `ℓ`, the retained lifetime of instruction `ℓ` is the piece's lifetime. -/
theorem retained_lifetime_of_launch {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)).2.2.2.1 ℓ ≠ none) :
    ((ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)).2.2.1 ℓ).2.1 = (D ℓ).2 := by
  rw [retained_run_succ_self]
  simp only [hl, ↓reduceIte]
  rw [GW1WalkExit.instrTime_walk_of_launch hl]
  exact min_eq_right le_top

/-- **The step at a piece of lifetime `0`** (Theorems 1.2–1.3). See the module docstring. -/
theorem mvLaw_succ_succ_zero (h12p : Theorem12ParamStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (hwℓ₂ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ + 2]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {𝓖 𝓖' : Filtration ℝ≥0 mΩ} {A₁ A₁' : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : 𝓖 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hA : ∀ᵐ ω ∂P, A₁ 0 ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω) ω)
    (h𝓖' : 𝓖' 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3))
    (hA' : ∀ᵐ ω ∂P, A₁' 0 ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ω)
    {Gℓ : Set Ω} {Kℓ : Ω → Set ℂ} {Yℓ : Ω → DistOn upperHalfPlaneOpens} {β₁ : Ω → BoundaryWord} {Mℓ : ℝ}
    (hlaw : MvLaw κ (lineFiltC P 𝓖 0) P h (A₁ 0) Kℓ Gℓ Yℓ β₁ Mℓ) :
    ∃ G₂ : Set Ω, MvLaw κ (lineFiltC P 𝓖' 0) P h (A₁' 0) Kℓ G₂ Yℓ β₁ Mℓ ∧
      ∀ᵐ ω ∂P, ω ∈ Gℓ →
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 = 0 →
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠ none →
        ω ∈ G₂ := by
  classical
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hbc := Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ
  have hup := hE' (Lu.upperSpec u l) hbc
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hEw := hE' _ hw
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hℓlt : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length :=
    (List.getElem?_eq_some_iff.1 hwℓ).1
  have hℓ₂lt : ℓ + 2 < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length :=
    (List.getElem?_eq_some_iff.1 hwℓ₂).1
  have hℓ₂le : ℓ + 2 ≤ (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length := hℓ₂lt.le
  have hcap₂ := isStagedHistory_capSpec (τ := ((0 : ℝ≥0) : ℝ≥0∞)) hb hEw (hreg' _) hℓ₂lt hwℓ₂
  have h𝓜def : lineFiltC P 𝓖 0 = mΩ ⊓ aeSigma (𝓖 0) P := rfl
  have hℋdef : lineFiltC P 𝓖' 0 = mΩ ⊓ aeSigma (𝓖' 0) P := rfl
  have h𝓖𝓖' : 𝓖 0 ≤ 𝓖' 0 := by
    rw [h𝓖, h𝓖']
    exact sup_le_sup le_rfl (capPast_le_capPast _ hwℓ hℓ₂le)
  have h𝓜ℋ : lineFiltC P 𝓖 0 ≤ lineFiltC P 𝓖' 0 := by
    rw [h𝓜def, hℋdef]
    exact inf_le_inf_left _ (WalkLaw.aeSigma_mono h𝓖𝓖')
  have hℋ : lineFiltC P 𝓖' 0 ≤ mΩ := (lineFiltC P 𝓖').le 0
  have h𝓖'ℋ : 𝓖' 0 ≤ lineFiltC P 𝓖' 0 := by
    rw [hℋdef]
    exact le_inf (𝓖'.le 0) (le_aeSigma _ _)
  obtain ⟨hKℓm, hKℓc, hKℓp, hGℓ, hKℓA, hYℓm, hYℓt, hβ₁m, hβ₁srt, hMℓ0, hβ₁b, hlawℓ⟩ := hlaw
  -- the retained union through the start of stage `ℓ + 2`, marked local
  obtain ⟨hA1, ho1, -, hloc1⟩ := Lcd.stageUnion_markedLocal h12p h13 hκ hκ4 hb hh hup hcap₂ (hreg' _) (hreg' _)
    hu₀ k (ℓ + 3)
  have h𝓜₂ : pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3) ≤ mΩ :=
    sup_le (hup.2.1 k) (hcap₂.2.1 (ℓ + 3))
  obtain ⟨Bp, hBpm, hBpc, hBpae, hBploc⟩ := Lcd.exists_lineVersion (P := P) ⟨_, h𝓜₂⟩
    (fun ω => union_subset (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω))
    ho1 hA1 hloc1
  obtain ⟨hÂm, hÂc, hÂloc, hÂl⟩ := fillVer_package hh0 h𝓜₂ hBpc hBpm hBploc
  have hÂmΩ : Measurable[mΩ, hittingSigma] (fillVer Bp) := hÂm.mono h𝓜₂ le_rfl
  have hÂℋ : IsHistoryAvoidanceLocal (lineFiltC P 𝓖' 0) (fillVer Bp) (centredField h u₀) P := by
    have h1 := Restart.FCPlumb.isHistoryAvoidanceLocal_aeSigma (P := P) hÂloc
    rw [hℋdef, h𝓖']
    exact h1
  -- the events of the zero-lifetime step
  have hWC := Qx.ae_walkChainFacts_regFam h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER
  have hrunw := hrun _ hw
  have hpast : pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 2) ≤ lineFiltC P 𝓖' 0 := by
    refine le_trans ?_ h𝓖'ℋ
    rw [h𝓖']
    exact (past_le_capPast _ hℓ₂le le_rfl).trans le_sup_right
  have hΛ₀ : MeasurableSet[lineFiltC P 𝓖' 0] {ω | (ExplState.run κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠
        none} :=
    hpast _ ((pastSigma_mono _ _ (by omega)) _ (Lv.measurableSet_launch_pastSigma (κ := κ)
      (spec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true) hb hEw.1 (hreg' _) ℓ))
  have hΛ₂ : MeasurableSet[lineFiltC P 𝓖' 0] {ω | (ExplState.run κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠
        none} :=
    hpast _ (Lv.measurableSet_launch_pastSigma (κ := κ)
      (spec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true) hb hEw.1 (hreg' _) (ℓ + 2))
  have hZ : MeasurableSet[lineFiltC P 𝓖' 0] {ω | ((ExplState.run κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.1 ℓ).2.1 =
        0} := by
    refine hpast _ ((pastSigma_mono _ _ (Nat.le_succ _)) _ ?_)
    have hm : Measurable[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)]
        (pastMap κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) :=
      Measurable.of_comap_le le_rfl
    have hc : Measurable[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)] fun ω =>
        (pastMap κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω
          ⟨ℓ, Nat.lt_succ_self ℓ⟩).2.1 :=
      measurable_fst.comp (measurable_snd.comp ((measurable_pi_apply _).comp hm))
    exact measurableSet_eq_fun hc measurable_const
  set G₂ : Set Ω := Gℓ ∩ {ω | (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠
        none} ∩
      {ω | ((ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.1 ℓ).2.1 =
        0} ∩
      {ω | (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠
        none} with hG₂def
  have hG₂ : MeasurableSet[lineFiltC P 𝓖' 0] G₂ := (((h𝓜ℋ _ hGℓ).inter hΛ₀).inter hZ).inter hΛ₂
  have hG₂ℓ : G₂ ⊆ Gℓ := fun ω hω => hω.1.1.1
  -- on `G₂`, the retained union through the start of `ℓ + 2` is the one before `ℓ`
  have hsets : ∀ᵐ ω ∂P, ω ∈ G₂ →
      Bp ω = WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω ∧
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω =
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω := by
    filter_upwards [hBpae, hWC] with ω h1 hWω hωG
    have hl0 := hωG.1.1.2
    have hz := hωG.1.2
    have hl2 := hωG.2
    simp only [mem_ofPred_eq] at hl0 hz hl2
    rw [retained_lifetime_of_launch hl0] at hz
    obtain ⟨old, q₀, q₁, hS⟩ := Qx.pieceSimpleAt_of_chainFacts hWω hl0
    have e1 := Qx.stageSet_succ_succ_eq_of_zero hl0 hS hz
    have e2 : WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 3) ω =
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω :=
      stageSet_capSpec_zero_succ hWω hl2 (hreg' _ (ℓ + 2) ω).2.1
    have e3 : WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω =
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω := by
      rw [WalkInf.stageSet_capSpec_of_le hℓ₂le ω le_rfl, WalkInf.stageSet_capSpec_of_le hℓlt.le ω le_rfl, e1]
    refine ⟨?_, e3⟩
    rw [h1, e2, e3]
  have hGA : ∀ᵐ ω ∂P, ω ∈ G₂ → fillVer Bp ω = fillH (Kℓ ω) := by
    filter_upwards [hsets, hA, hKℓA] with ω h1 h2 h3 hωG
    rw [Qr.fillVer_congr (B' := fun ω => WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
      (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω) (h1 hωG).1, ← h2, h3 (hG₂ℓ hωG)]
  have hlaw₂ := ae_isGFF_of_coarse_of_marked_on hh hu₀ h𝓜ℋ hℋ (G := G₂) (fun n j => h𝓜ℋ _ (hKℓm n j)) hKℓc hKℓp
    hYℓm (by filter_upwards [hYℓt] with ω h1 hωG using h1 (hG₂ℓ hωG)) hβ₁m hβ₁srt hGℓ hlawℓ hÂmΩ hÂc hÂℋ hÂl hG₂
    hG₂ℓ hGA
  refine ⟨G₂, ⟨fun n j => h𝓜ℋ _ (hKℓm n j), hKℓc, hKℓp, hG₂, ?_, hYℓm,
    by filter_upwards [hYℓt] with ω h1 hωG using h1 (hG₂ℓ hωG), hβ₁m.mono h𝓜ℋ le_rfl, hβ₁srt, hMℓ0, hβ₁b, hlaw₂⟩,
    ?_⟩
  · filter_upwards [hsets, hA, hA', hKℓA] with ω h1 h2 h3 h4 hωG
    rw [h3, Qr.fillVer_congr (B' := fun ω => WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
      (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω) (by rw [(h1 hωG).2]), ← h2, h4 (hG₂ℓ hωG)]
  · filter_upwards [hrunw] with ω hr hωG hl0 hz hl2
    refine ⟨⟨⟨hωG, ?_⟩, ?_⟩, ?_⟩
    · show (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none
      rw [hr]; exact hl0
    · show ((ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.1 ℓ).2.1 = 0
      rw [hr, retained_lifetime_of_launch hl0]
      exact hz
    · show (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠
          none
      rw [hr]; exact hl2

open Classical in
/-- **Two retained laws on two events glue** (piecewise hull, field and word; the larger bound). -/
theorem mvLaw_piecewise {κ : ℝ} {Ω : Type*} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (h𝓜 : 𝓜 ≤ mΩ)
    {A K₁ K₂ : Ω → Set ℂ} {G₁ G₂ : Set Ω} {Y₁ Y₂ : Ω → DistOn upperHalfPlaneOpens} {β₁ β₂ : Ω → BoundaryWord}
    {M₁ M₂ : ℝ} (h₁ : MvLaw κ 𝓜 P h A K₁ G₁ Y₁ β₁ M₁) (h₂ : MvLaw κ 𝓜 P h A K₂ G₂ Y₂ β₂ M₂) :
    MvLaw κ 𝓜 P h A (fun ω => G₁.piecewise K₁ K₂ ω) (G₁ ∪ G₂) (G₁.piecewise Y₁ Y₂) (G₁.piecewise β₁ β₂)
      (max M₁ M₂) := by
  classical
  obtain ⟨hK₁m, hK₁c, hK₁p, hG₁, hK₁A, hY₁m, hY₁t, hβ₁m, hβ₁s, hM₁, hβ₁b, hl₁⟩ := h₁
  obtain ⟨hK₂m, hK₂c, hK₂p, hG₂, hK₂A, hY₂m, hY₂t, hβ₂m, hβ₂s, hM₂, hβ₂b, hl₂⟩ := h₂
  have hG₁Ω : MeasurableSet G₁ := h𝓜 _ hG₁
  refine ⟨fun n j => ?_, fun ω => ?_, fun ω => ?_, hG₁.union hG₂, ?_, hY₁m.piecewise hG₁Ω hY₂m, ?_,
    hβ₁m.piecewise hG₁ hβ₂m, fun ω => ?_, le_max_of_le_left hM₁, fun ω y hy => ?_, ?_⟩
  · have e : {ω | (Restart.dyadicSquare n j ∩ G₁.piecewise K₁ K₂ ω).Nonempty} =
        (G₁ ∩ {ω | (Restart.dyadicSquare n j ∩ K₁ ω).Nonempty}) ∪
          (G₁ᶜ ∩ {ω | (Restart.dyadicSquare n j ∩ K₂ ω).Nonempty}) := by
      ext ω
      by_cases hω : ω ∈ G₁
      · simp [hω]
      · simp [hω]
    rw [e]
    exact (hG₁.inter (hK₁m n j)).union (hG₁.compl.inter (hK₂m n j))
  · by_cases hω : ω ∈ G₁ <;> simp only [Set.piecewise, hω, ↓reduceIte] <;> first | exact hK₁c ω | exact hK₂c ω
  · by_cases hω : ω ∈ G₁ <;> simp only [Set.piecewise, hω, ↓reduceIte] <;> first | exact hK₁p ω | exact hK₂p ω
  · filter_upwards [hK₁A, hK₂A] with ω e1 e2 hω
    by_cases h1 : ω ∈ G₁
    · simp only [Set.piecewise, h1, ↓reduceIte]; exact e1 h1
    · simp only [Set.piecewise, h1, ↓reduceIte]; exact e2 (hω.resolve_left h1)
  · filter_upwards [hY₁t, hY₂t] with ω e1 e2 hω
    by_cases h1 : ω ∈ G₁
    · simp only [Set.piecewise, h1, ↓reduceIte]; exact e1 h1
    · simp only [Set.piecewise, h1, ↓reduceIte]; exact e2 (hω.resolve_left h1)
  · by_cases hω : ω ∈ G₁ <;> simp only [Set.piecewise, hω, ↓reduceIte] <;> first | exact hβ₁s ω | exact hβ₂s ω
  · by_cases hω : ω ∈ G₁
    · simp only [Set.piecewise, hω, ↓reduceIte] at hy ⊢; exact (hβ₁b ω y hy).trans (le_max_left _ _)
    · simp only [Set.piecewise, hω, ↓reduceIte] at hy ⊢; exact (hβ₂b ω y hy).trans (le_max_right _ _)
  · -- the law: on `G₁` the glued field is `Y₁`, on `G₂ \ G₁` it is `Y₂`
    have hYm : Measurable (G₁.piecewise Y₁ Y₂) := hY₁m.piecewise hG₁Ω hY₂m
    have e1 := Fl.ae_isGFF_congr_on (P := P) h𝓜 hG₁ hYm hl₁ (Eventually.of_forall fun ω hω => by
      simp only [Set.piecewise, hω, ↓reduceIte])
    have hG₂₁ : MeasurableSet[𝓜] (G₂ \ G₁) := hG₂.diff hG₁
    have hl₂' : ∀ᵐ ω₀ ∂P, ω₀ ∈ G₂ \ G₁ →
        IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) Y₂ (β₂ ω₀).fn (β₂ ω₀).jumps := by
      filter_upwards [hl₂] with ω₀ h1 hω₀ using h1 hω₀.1
    have e2 := Fl.ae_isGFF_congr_on (P := P) h𝓜 hG₂₁ hYm hl₂' (Eventually.of_forall fun ω hω => by
      simp only [Set.piecewise, hω.2, ↓reduceIte])
    filter_upwards [e1, e2] with ω₀ f1 f2 hω₀
    by_cases h1 : ω₀ ∈ G₁
    · simp only [Set.piecewise, h1, ↓reduceIte]; exact f1 h1
    · simp only [Set.piecewise, h1, ↓reduceIte]; exact f2 ⟨hω₀.resolve_left h1, h1⟩

end InteractingSLE.Theorem14.SB.Fl
