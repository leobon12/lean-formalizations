/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FlZero
import InteractingSLE.Spec.Supplement.SB2QtSets

/-!
# The law step `ℓ → ℓ + 2` when the retained hull does not change

Packet PROVE-T14-SB2LIFT (round 38, decision D89). F3LAW's `Fl.mvLaw_succ_succ_zero` passes the retained law from
stage `ℓ` to stage `ℓ + 2` (same hull `K`, field `Y`, word `β`, bound `M`) at a piece of lifetime `0`. The lifetime is
used only to show that the retained union does not grow. This file is the same proof, with the event
`{fill of the retained union at ℓ + 2 = fill of the one at ℓ}` as the selector, read through line versions of both
unions (`Lcd.exists_lineVersion`, `Qt.measurableSet_eq_of_hitting`).

* `Sx.fillVer_eq_of_subset`: a set between `B₁` and `fillVer B₁` (a hull) has the fill of `B₁`.
* **`mvLaw_succ_succ_fill`**: `MvLaw` at `ℓ` gives `MvLaw` at `ℓ + 2` with the same `K`, `Y`, `β`, `M`, on an event
  containing almost surely every sample of the law's event with a launch at `ℓ + 2` whose regularized stage set after
  `ℓ + 2` instructions lies in the retained hull `A₁ 0` of stage `ℓ`.

R48: Theorems 1.2–1.3 appear only as hypotheses.
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

/-- **A larger set inside the fill of a hull has the same fill** (`fillVer` form). -/
theorem _root_.InteractingSLE.Theorem14.SB.Sx.fillVer_eq_of_subset {Ω : Type*} {B₁ B₂ : Ω → Set ℂ} {ω : Ω}
    (hB₁H : B₁ ω ⊆ H) (h12 : B₁ ω ⊆ B₂ ω) (hHP : IsHPHull (fillVer B₁ ω)) (h2 : B₂ ω ⊆ fillVer B₁ ω) :
    fillVer B₂ ω = fillVer B₁ ω := by
  have hb₁ : Bornology.IsBounded (B₁ ω) := by
    by_contra hnb
    rw [fillVer_of_not_bounded hnb] at hHP
    exact hnb hHP.2.1
  have hb₂ : Bornology.IsBounded (B₂ ω) := hHP.2.1.subset h2
  rw [fillVer_of_bounded hb₂]
  have hSF : fillH (closure (B₁ ω)) = fillVer B₁ ω := (fillVer_of_bounded hb₁).symm
  have h := Qt.fillH_closure_union_of_subset hHP hSF hB₁H h2
  rwa [union_eq_self_of_subset_left h12] at h

/-- **The step when the retained hull does not change** (Theorems 1.2–1.3). See the module docstring. -/
theorem mvLaw_succ_succ_fill (h12p : Theorem12ParamStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
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
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠ none →
        WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 2) ω ⊆ A₁ 0 ω →
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
  -- the stage-`ℓ` retained union, measurable for the stage-`ℓ` marks
  obtain ⟨hA1ℓ, ho1ℓ, -, hloc1ℓ⟩ := Lcd.stageUnion_markedLocal h12p h13 hκ hκ4 hb hh hup hEw (hreg' _) (hreg' _)
    hu₀ k ℓ
  have h𝓜ℓ : pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ≤ mΩ :=
    sup_le (hup.2.1 k) (hEw.2.1 ℓ)
  obtain ⟨Bpℓ, hBpℓm, hBpℓc, hBpℓae, hBpℓloc⟩ := Lcd.exists_lineVersion (P := P) ⟨_, h𝓜ℓ⟩
    (fun ω => union_subset (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω))
    ho1ℓ hA1ℓ hloc1ℓ
  obtain ⟨hÂℓm, hÂℓc, -, -⟩ := fillVer_package hh0 h𝓜ℓ hBpℓc hBpℓm hBpℓloc
  have h𝓜ℓ₂ : pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ≤
      pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3) :=
    sup_le_sup le_rfl (past_le_capPast _ hℓ₂le (by omega))
  have h𝓜₂ℋ : pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3) ≤
      lineFiltC P 𝓖' 0 := by
    rw [← h𝓖']; exact h𝓖'ℋ
  have hEq : MeasurableSet[lineFiltC P 𝓖' 0] {ω | fillVer Bp ω = fillVer Bpℓ ω} :=
    h𝓜₂ℋ _ (Qt.measurableSet_eq_of_hitting hÂm (hÂℓm.mono h𝓜ℓ₂ le_rfl) hÂc hÂℓc)
  set G₂ : Set Ω := Gℓ ∩ {ω | (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠
        none} ∩ {ω | fillVer Bp ω = fillVer Bpℓ ω} with hG₂def
  have hG₂ : MeasurableSet[lineFiltC P 𝓖' 0] G₂ := ((h𝓜ℋ _ hGℓ).inter hΛ₂).inter hEq
  have hG₂ℓ : G₂ ⊆ Gℓ := fun ω hω => hω.1.1
  -- the stage sets: the capped ones before the cap, and the zero-time piece at `ℓ + 2`
  have hcapℓ : ∀ ω, WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
      (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω =
      WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω := fun ω =>
    WalkInf.stageSet_capSpec_of_le hℓlt.le ω le_rfl
  have hcap2 : ∀ ω, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠
        none → WalkChainFacts κ b jumps (-(Real.pi / 2))
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) →
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
        (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        (ℓ + 3) ω =
      WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 2) ω := fun ω hl2 hWω => by
    rw [stageSet_capSpec_zero_succ hWω hl2 (hreg' _ (ℓ + 2) ω).2.1, WalkInf.stageSet_capSpec_of_le hℓ₂le ω le_rfl]
  have hcap2' : ∀ ω, WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
        (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        (ℓ + 2) ω =
      WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 2) ω := fun ω =>
    WalkInf.stageSet_capSpec_of_le hℓ₂le ω le_rfl
  -- on `G₂`, the fill of the retained union at `ℓ + 2` is the hull at `ℓ`
  have hGA : ∀ᵐ ω ∂P, ω ∈ G₂ → fillVer Bp ω = fillH (Kℓ ω) := by
    filter_upwards [hBpℓae, hA, hKℓA] with ω h1 h2 h3 hωG
    rw [hωG.2, Qr.fillVer_congr (B' := fun ω => WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
      (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω) (by rw [h1, hcapℓ]), ← h2, h3 (hG₂ℓ hωG)]
  have hlaw₂ := ae_isGFF_of_coarse_of_marked_on hh hu₀ h𝓜ℋ hℋ (G := G₂) (fun n j => h𝓜ℋ _ (hKℓm n j)) hKℓc hKℓp
    hYℓm (by filter_upwards [hYℓt] with ω h1 hωG using h1 (hG₂ℓ hωG)) hβ₁m hβ₁srt hGℓ hlawℓ hÂmΩ hÂc hÂℋ hÂl hG₂
    hG₂ℓ hGA
  refine ⟨G₂, ⟨fun n j => h𝓜ℋ _ (hKℓm n j), hKℓc, hKℓp, hG₂, ?_, hYℓm,
    by filter_upwards [hYℓt] with ω h1 hωG using h1 (hG₂ℓ hωG), hβ₁m.mono h𝓜ℋ le_rfl, hβ₁srt, hMℓ0, hβ₁b, hlaw₂⟩,
    ?_⟩
  · filter_upwards [hBpae, hA', hWC, hGA] with ω h1 h3 hWω hGAω hωG
    rw [h3, ← hGAω hωG, Qr.fillVer_congr (B' := fun ω => WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
      (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) (by rw [h1, hcap2 ω hωG.1.2 hWω, hcap2'])]
  · filter_upwards [hrunw, hBpae, hBpℓae, hA, hKℓA, hWC] with ω hr h1 h2 h3 h4 hWω hωG hl2 hsub
    have hl2r : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠
          none := by rw [hr]; exact hl2
    refine ⟨⟨hωG, hl2r⟩, ?_⟩
    show fillVer Bp ω = fillVer Bpℓ ω
    have hF : fillVer (fun ω => WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
        (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪ WalkLaw.stageSet κ b jumps
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω = A₁ 0 ω := by
      rw [h3, Qr.fillVer_congr (B' := fun ω => WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
        (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
            ℓ ω) (by rw [hcapℓ])]
    have hHP : IsHPHull (A₁ 0 ω) := h4 hωG ▸ Mo.isHPHull_fillH hKℓc hKℓp ω
    have hmono : WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω ⊆
        WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 2) ω := by
      rw [show ℓ + 2 = ℓ + 1 + 1 from rfl, WalkLaw.stageSet_succ, WalkLaw.stageSet_succ]
      exact subset_union_left.trans subset_union_left
    have hU : WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ⊆ A₁ 0 ω := by
      rw [← hF]
      exact subset_union_left.trans (subset_fillVer (fun ω => union_subset (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω)
        (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω)) ω)
    have hfill := Sx.fillVer_eq_of_subset (B₁ := fun ω => WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
        (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪ WalkLaw.stageSet κ b jumps
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
      (B₂ := fun ω => WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
        (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪ WalkLaw.stageSet κ b jumps
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 2) ω) (ω := ω)
      (union_subset (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω))
      (union_subset_union_right _ hmono) (by rw [hF]; exact hHP) (by rw [hF]; exact union_subset hU hsub)
    rw [Qr.fillVer_congr (B' := fun ω => WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
        (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪ WalkLaw.stageSet κ b jumps
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 2) ω)
        (by rw [h1, hcap2 ω hl2r hWω]), hfill,
      Qr.fillVer_congr (B' := fun ω => WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
        (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪ WalkLaw.stageSet κ b jumps
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) h2]

end InteractingSLE.Theorem14.SB.Fl
