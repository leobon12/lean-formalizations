/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CdVer

/-!
# The root step of SB2(2)'s induction: the retained law at `relOff + 2` (D80)

Packet PROVE-SB2-CONDFIN, round 15 (decision D80). **`mvLaw_succ_succ_jointX_root`**: F3LAW's joint step
`Fo.mvLaw_succ_succ_jointX` for NOJUMP's ROOT versions `Cr.RootVersionS` (tail start `entrR`): from the retained law
at `ℓ = relOff`, the root objects for its word, K2's root outputs (`Cr.ae_k2_root`: the stopped matches and the
lifetime), the record and a retained hull of `ℓ + 2`, the retained law at `ℓ + 2` with the step word and the stepped
hull. The proof is the tail step's, with the two version lemmas replaced by their root twins (`SB2CdVer`).
**`mvLaw_succ_succ_joint_root`**: the drop-in form.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cd

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Supp8.Q3Stop Lv Lk Mf Ms Qw Fl Fo
open Supp8.GB6.RelDrv (IsStopDrvMatch)

/-- **Root twin** (`Cr.RootVersionS`, D80) of `Fo.mvLaw_succ_succ_jointX`, with the versions, K2's outputs, `hKF`
and `hFl` on the version event `Fr` and the step on an event `F ⊆ Fr` (a.s.) of the line σ-algebra at time `0`
(`F = Fr` when `Fr` is one; see `SB2CdRoot`).
**The joint-A₂ step with its word and hull exposed** (D51 item 1; for D34's left heights): the law at `ℓ + 2`
has the explicit step word `Qw.stepWord κ (−π/2) x₀ (shiftW x₀ β₁) (maskDrv F driver)` on an event `G₂ ⊆ F`, on
which the retained hull is the stepped hull `Qw.stepHull (fill K) x₀ W T` of the relative piece (good records). -/
theorem mvLaw_succ_succ_jointX_root (h12p : Theorem12ParamStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
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
    {𝓖 𝓖' : Filtration ℝ≥0 mΩ} {A₁ A₂ A₁' : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : 𝓖 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hA : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
        ω ∧
      A₂ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1) ω) ω)
    (h𝓖' : 𝓖' 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3))
    (hA' : ∀ᵐ ω ∂P, A₁' 0 ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ω)
    -- the law at `ℓ`
    {Gℓ : Set Ω} {Kℓ : Ω → Set ℂ} {Yℓ : Ω → DistOn upperHalfPlaneOpens} {β₁ : Ω → BoundaryWord} {Mℓ : ℝ}
    (hlaw : MvLaw κ (lineFiltC P 𝓖 0) P h (A₁ 0) Kℓ Gℓ Yℓ β₁ Mℓ)
    (hβ₁s : Measurable[aeSigma (stageMarks κ b jumps E u l k ℓ) P] β₁)
    -- F2b′'s objects at `ℓ` for the word `β₁`
    {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {F Fr : Set Ω} {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0}
    {relLife : Ω → ℝ≥0∞} (hKm : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hKF : ∀ᵐ ω ∂P, ω ∈ Fr → fillH (K ω) = A₁ 0 ω) (hx₀ : Measurable[lineFiltC P 𝓖 0] x₀)
    (hF : MeasurableSet[lineFiltC P 𝓖 0] F) (hFFr : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ Fr)
    (hFl : ∀ᵐ ω ∂P, ω ∈ Fr → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (S : Cr.RootVersionS κ (-(Real.pi / 2)) P Fr 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
      (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) types pc tL
      (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife)
    (hcl2 : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ Fr →
      (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 → ∃ m, (S.ver m).a t ω < S.V m ω)
    (htypes : types.Countable)
    (hcover : ∀ᵐ ω ∂P, ω ∈ Fr → angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω)) ∈ types)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P,
      ω ∈ wordTypeCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) Fr w →
      ω ∈ seedCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) Fr w)
    -- the kernel half at `ℓ`: K2's stopped match and the canonical lifetime
    (hK2 : ∀ᵐ ω ∂P, ω ∈ Fr → ∀ m, IsStopDrvMatch (driverCode h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
      (fun t => (S.ver m).W t ω) (S.V m ω))
    (hlife : ∀ᵐ ω ∂P, ω ∈ Fr → (driverOf h12p hκ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω),
      Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 = relLife ω)
    (hFG : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ Gℓ)
    -- the record matching
    {Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDr : Measurable[stageMarks κ b jumps E u l k (ℓ + 1)] Dr)
    (hDrreg : ∀ ω, IsRegularDriver (Dr ω))
    (hDreq : ∀ᵐ ω ∂P, ω ∈ F → recOf ⊤ (Dr ω) = recOf ⊤ (driverOf h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))))
    -- a retained hull of stage `ℓ + 2`
    {K₂ : Ω → Set ℂ} (hK₂m : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖' 0) K₂)
    (hK₂c : ∀ ω, IsCompact (K₂ ω)) (hK₂p : ∀ ω, IsPreconnected (K₂ ω ∪ Restart.lowerHalf)) {L₂ : Set Ω}
    (hL₂ : MeasurableSet[lineFiltC P 𝓖' 0] L₂) (hL₂K : ∀ᵐ ω ∂P, ω ∈ L₂ → fillH (K₂ ω) = A₁' 0 ω) :
    ∃ (G₂ : Set Ω) (Y₂ : Ω → DistOn upperHalfPlaneOpens) (M₂ : ℝ),
      MvLaw κ (lineFiltC P 𝓖' 0) P h (A₁' 0) K₂ G₂ Y₂ (stepWord κ (-(Real.pi / 2)) x₀
        (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) (maskDrv F fun ω => driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω))) M₂ ∧
      Measurable[aeSigma (stageMarks κ b jumps E u l k (ℓ + 2)) P] (stepWord κ (-(Real.pi / 2)) x₀
        (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) (maskDrv F fun ω => driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω))) ∧
      G₂ ⊆ F ∧
      (∀ ω ∈ G₂, (driverOf h12p hκ (-(Real.pi / 2))
        (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)).2 ≠ ⊤) ∧
      (∀ᵐ ω ∂P, ω ∈ G₂ →
        LocalExt.IsDrvGood (recHist (recOf ⊤ (driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)))) →
        fillH (K₂ ω) = stepHull (fillH (K ω)) (x₀ ω) (recDrv (driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)))
          ((driverOf h12p hκ (-(Real.pi / 2))
            (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)).2.toNNReal : ℝ)) ∧
      ∀ᵐ ω ∂P, ω ∈ F → ω ∈ L₂ →
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
  have hcap := isStagedHistory_capSpec (τ := ((0 : ℝ≥0) : ℝ≥0∞)) hb hEw (hreg' _) hℓlt hwℓ
  have hcap₂ := isStagedHistory_capSpec (τ := ((0 : ℝ≥0) : ℝ≥0∞)) hb hEw (hreg' _) hℓ₂lt hwℓ₂
  -- the generator of the line σ-algebra at `ℓ`
  have hp1 : Measurable (pastMap κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k) :=
    Measurable.of_comap_le (hup.2.1 k)
  have hp2 : Measurable (pastMap κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
      (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
      (ℓ + 1)) :=
    Measurable.of_comap_le (hcap.2.1 (ℓ + 1))
  have hp := hp1.prodMk hp2
  have h𝓖p : 𝓖 0 = MeasurableSpace.comap (fun ω =>
      (pastMap κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω,
        pastMap κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1) ω)) inferInstance := by
    rw [h𝓖]
    exact (MeasurableSpace.comap_prodMk _ _).symm
  have h𝓜def : lineFiltC P 𝓖 0 = mΩ ⊓ aeSigma (𝓖 0) P := rfl
  have hℋdef : lineFiltC P 𝓖' 0 = mΩ ⊓ aeSigma (𝓖' 0) P := rfl
  have h𝓜 : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  have hp𝓜 : Measurable[lineFiltC P 𝓖 0] fun ω =>
      (pastMap κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω,
        pastMap κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1) ω) := by
    rw [measurable_iff_comap_le, ← h𝓖p, h𝓜def]
    exact le_inf (𝓖.le 0) (le_aeSigma _ _)
  have h𝓜p : lineFiltC P 𝓖 0 ≤ aeSigma (MeasurableSpace.comap (fun ω =>
      (pastMap κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω,
        pastMap κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1) ω)) inferInstance) P := by
    rw [← h𝓖p, h𝓜def]
    exact inf_le_right
  -- the law at `ℓ`, read in F2b′'s chart
  obtain ⟨hKℓm, hKℓc, hKℓp, hGℓ, hKℓA, hYℓm, hYℓt, hβ₁m, hβ₁srt, hMℓ0, hβ₁b, hlawℓ⟩ := hlaw
  have hFΩ : MeasurableSet F := h𝓜 _ hF
  have hlawF : ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      IsGFFWithBoundaryData (condExpKernel P (lineFiltC P 𝓖 0) ω₀) Yℓ (β₁ ω₀).fn (β₁ ω₀).jumps := by
    filter_upwards [hlawℓ, hFG] with ω₀ h1 h2 hω₀ using h1 (h2 hω₀)
  have hKΩ : @IsDyadicHitMeasurable Ω mΩ K := fun n j => h𝓜 _ (hKm n j)
  have hx₀m : Measurable x₀ := hx₀.mono h𝓜 le_rfl
  have heq0 : ∀ᵐ ω ∂P, ω ∈ F → Yℓ ω = canonField κ h (fun _ => (0 : ℝ)) hKc hKp ω := by
    filter_upwards [hFG, hKℓA, hKF, hYℓt, hFFr] with ω h1 h2 h3 h4 h5 hωF
    have e : fillH (Kℓ ω) = fillH (K ω) := (h2 (h1 hωF)).trans (h3 (h5 hωF)).symm
    have h5 := h4 (h1 hωF)
    rw [e] at h5
    exact canonField_eq_of_transport (x₀ := fun _ => (0 : ℝ)) hKc hKp h5
  have hlaw0 := ae_isGFF_congr_on h𝓜 hF (measurable_canonField κ hh.1 hKc hKp hKΩ measurable_const) hlawF heq0
  have hlawx := Mu.ae_isGFF_hullChart_shift h𝓜 hKc hKp hx₀ (measurable_canonField κ hh.1 hKc hKp hKΩ hx₀m)
    hlaw0
  -- σ-algebra comparisons
  have hℓ₂le : ℓ + 2 ≤ (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length := hℓ₂lt.le
  have h𝓖𝓖' : 𝓖 0 ≤ 𝓖' 0 := by
    rw [h𝓖, h𝓖']
    exact sup_le_sup le_rfl (capPast_le_capPast _ hwℓ hℓ₂le)
  have h𝓜ℋ : lineFiltC P 𝓖 0 ≤ lineFiltC P 𝓖' 0 := by
    rw [h𝓜def, hℋdef]
    exact inf_le_inf_left _ (WalkLaw.aeSigma_mono h𝓖𝓖')
  have hℋ : lineFiltC P 𝓖' 0 ≤ mΩ := (lineFiltC P 𝓖').le 0
  have hsm1 : stageMarks κ b jumps E u l k (ℓ + 1) ≤ 𝓖' 0 := by
    rw [h𝓖']
    exact sup_le_sup le_rfl (past_le_capPast _ hℓ₂le (by omega))
  have h𝓖'ℋ : 𝓖' 0 ≤ lineFiltC P 𝓖' 0 := by
    rw [hℋdef]
    exact le_inf (𝓖'.le 0) (le_aeSigma _ _)
  have h𝓖s : 𝓖 0 ≤ stageMarks κ b jumps E u l k (ℓ + 2) := by
    rw [h𝓖]
    exact sup_le_sup le_rfl (capPast_le_past _ hwℓ)
  have hss : stageMarks κ b jumps E u l k ℓ ≤ stageMarks κ b jumps E u l k (ℓ + 2) :=
    sup_le_sup le_rfl (pastSigma_mono _ _ (by omega))
  have hs1s : stageMarks κ b jumps E u l k (ℓ + 1) ≤ stageMarks κ b jumps E u l k (ℓ + 2) :=
    sup_le_sup le_rfl (pastSigma_mono _ _ (by omega))
  -- the canonical driver and its record
  have hβ𝓜 : Measurable[lineFiltC P 𝓖 0] fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω) :=
    BoundaryWord.measurable_shiftW.comp (hx₀.prodMk hβ₁m)
  have hem : Measurable fun ω => driverOf h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω) :=
    (measurable_driverOf h12p hκ _).comp ((hβ𝓜.mono h𝓜 le_rfl).prodMk
      (measurable_canonField κ hh.1 hKc hKp hKΩ hx₀m))
  have hregm : ∀ ω, IsRegularDriver (maskDrv F (fun ω => driverOf h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)) ω) :=
    isRegularDriver_maskDrv fun ω => Mz.isRegularDriver_driverOf h12p hκ _ _
  have hrΩ : Measurable fun ω => recOf ⊤ (maskDrv F (fun ω => driverOf h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)) ω) :=
    measurable_recOf (measurable_maskDrv hFΩ hem) hregm ⊤
  have hDrm : Measurable[stageMarks κ b jumps E u l k (ℓ + 1)] fun ω => recOf ⊤ (Dr ω) :=
    @measurable_recOf Ω (stageMarks κ b jumps E u l k (ℓ + 1)) _ hDr hDrreg ⊤
  have heqr : (fun ω => recOf ⊤ (maskDrv F (fun ω => driverOf h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)) ω)) =ᵐ[P]
      fun ω => if ω ∈ F then recOf ⊤ (Dr ω) else recOf ⊤ Mz.zeroDrv := by
    filter_upwards [hDreq] with ω hω
    by_cases hωF : ω ∈ F
    · simp only [hωF, ↓reduceIte, maskDrv_of_mem hωF]
      exact (hω hωF).symm
    · simp only [hωF, ↓reduceIte, maskDrv_of_notMem hωF]
  have hrtℋ : Measurable[lineFiltC P 𝓖' 0] fun ω => if ω ∈ F then recOf ⊤ (Dr ω) else recOf ⊤ Mz.zeroDrv :=
    Measurable.ite (h𝓜ℋ _ hF) (hDrm.mono (hsm1.trans h𝓖'ℋ) le_rfl) measurable_const
  have hrℋ : Measurable[lineFiltC P 𝓖' 0] fun ω => recOf ⊤ (maskDrv F (fun ω => driverOf h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)) ω) := by
    refine (measurable_inf_aeSigma_of_ae_eq hrΩ hrtℋ heqr).mono ?_ le_rfl
    rw [hℋdef]
    exact inf_le_inf_left _ (StagedEntrance.aeSigma_le_aeSigma inf_le_right)
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
  -- GW1's chain facts, the zero-time piece at `ℓ + 2`, and the retained hull of stage `ℓ + 2`
  have hWC := Qx.ae_walkChainFacts_regFam h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER
  have hrunw := hrun _ hw
  have hBpS : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠
        none →
      Bp ω = WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω := by
    filter_upwards [hBpae, hWC] with ω h1 h2 hl
    rw [h1]
    have h3 : WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 3) ω =
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω :=
      stageSet_capSpec_zero_succ h2 hl (hreg' _ (ℓ + 2) ω).2.1
    rw [h3]
  have hS₂hull : ∀ᵐ ω ∂P, ω ∈ L₂ →
      IsHPHull (fillH (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω)) ∧
      fillH (K₂ ω) = fillH (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ∧
      fillVer (fun ω => WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ω =
        fillH (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) := by
    filter_upwards [hL₂K, hA'] with ω h1 h2 hωL
    have hK₂h : IsHPHull (fillH (K₂ ω)) := Mo.isHPHull_fillH hK₂c hK₂p ω
    rw [h1 hωL, h2] at hK₂h
    have hbd : Bornology.IsBounded (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
        (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) := by
      by_contra hnb
      rw [fillVer_of_not_bounded (B := fun ω => WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
        (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) hnb] at hK₂h
      exact hnb hK₂h.2.1
    have hfv := fillVer_of_bounded (B := fun ω => WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
        (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) hbd
    rw [Qx.fillH_closure] at hfv
    rw [hfv] at hK₂h
    refine ⟨hK₂h, ?_, hfv⟩
    rw [h1 hωL, h2, hfv]
  -- the terminal hull identity and the finite relative lifetime
  have hstepH := ae_fill_eq_stepHull_joint_root h12p hκ u l k ℓ hKc hKp htypes S hcl2 hcover hseed hK2 hlife hA hWC
    hrunw hKF hFl
  have hA₁q : ∀ q : ℚ, ∀ᵐ ω ∂P, ω ∈ Fr → A₁ (Real.toNNReal q) ω = fillH (K ω) := by
    intro q
    filter_upwards [hA (Real.toNNReal q), hA 0, hKF, hrunw, hFl] with ω hq h0 hK hr hl hωF
    have hl' : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠
          none := by
      rw [hr]; exact hl hωF
    obtain ⟨-, hlen⟩ := Qx.walk_instr_of_launch hl'
    rw [hK hωF, h0.1, hq.1]
    unfold fillVer
    beta_reduce
    rw [WalkInf.stageSet_capSpec_of_le hlen.le ω le_rfl, WalkInf.stageSet_capSpec_of_le hlen.le ω le_rfl]
  have hphys := ae_phys_joint u l k ℓ hA hWC hrunw hKF hFl
  have hlifeTop := ae_relLife_ne_top_of_versions_root hKc hKp htypes S hcover hseed hA₁q hphys
  -- the event of the step
  have hΛ₂ : MeasurableSet[lineFiltC P 𝓖' 0] {ω | (ExplState.run κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠
        none} := by
    have h1 := Lv.measurableSet_launch_pastSigma (κ := κ) (spec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      hb hEw.1 (hreg' _) (ℓ + 2)
    refine h𝓖'ℋ _ ?_
    rw [h𝓖']
    exact ((past_le_capPast _ hℓ₂le le_rfl).trans le_sup_right) _ h1
  have hR2 : MeasurableSet[lineFiltC P 𝓖' 0] {ω | (recOf ⊤ (maskDrv F (fun ω => driverOf h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)) ω)).2.1 ≠ ⊤} :=
    (measurableSet_eq_fun ((measurable_fst.comp measurable_snd).comp hrℋ) measurable_const).compl
  set G : Set Ω := F ∩ {ω | (recOf ⊤ (maskDrv F (fun ω => driverOf h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)) ω)).2.1 ≠ ⊤} ∩ L₂ ∩
      {ω | (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠
          none} with hGdef
  have hGℋ : MeasurableSet[lineFiltC P 𝓖' 0] G := (((h𝓜ℋ _ hF).inter hR2).inter hL₂).inter hΛ₂
  have hGF : G ⊆ F := fun ω hω => hω.1.1.1
  have hGζ : ∀ ω ∈ G, (driverOf h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)).2 ≠ ⊤ := fun ω hω => by
    have h1 := hω.1.1.2
    simp only [mem_ofPred_eq] at h1
    rw [maskDrv_of_mem hω.1.1.1] at h1
    have h2 : (recOf ⊤ (driverOf h12p hκ (-(Real.pi / 2))
        (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω))).2.1 =
        (driverOf h12p hκ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)).2 :=
      min_eq_right le_top
    rwa [h2] at h1
  have hGA : ∀ᵐ ω ∂P, ω ∈ G → fillVer Bp ω = fillH (K₂ ω) := by
    filter_upwards [hBpS, hS₂hull] with ω h1 h2 hωG
    obtain ⟨-, h3, h4⟩ := h2 hωG.1.2
    rw [Qr.fillVer_congr (B' := fun ω => WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
      (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) (h1 hωG.2), h4, h3]
  have hK₂ : ∀ᵐ ω ∂P, ω ∈ G →
      LocalExt.IsDrvGood (recHist (recOf ⊤ (driverOf h12p hκ (-(Real.pi / 2))
        (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)))) →
      fillH (K₂ ω) = stepHull (fillH (K ω)) (x₀ ω) (recDrv (driverOf h12p hκ (-(Real.pi / 2))
        (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)))
        ((driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)).2.toNNReal : ℝ) := by
    filter_upwards [hstepH, hS₂hull, hlife, hFFr] with ω h1 h2 h3 h0 hωG hg
    obtain ⟨hHP, h4, -⟩ := h2 hωG.1.2
    have hrel : relLife ω ≠ ⊤ := by
      rw [← h3 (h0 hωG.1.1.1)]
      exact hGζ ω hωG
    rw [h4]
    exact h1 (h0 hωG.1.1.1) hrel hg hHP
  -- the step core
  have : StandardBorelSpace (PastData k) := inferInstance
  have : StandardBorelSpace (PastData (ℓ + 1)) := inferInstance
  have hcore := ae_isGFF_next h12p h13 hκ hh hu₀ hp h𝓜 hp𝓜 h𝓜p hKc hKp hKΩ hx₀ hβ𝓜 hF
    (θ := -(Real.pi / 2)) hlawx hℋ h𝓜ℋ hrℋ hK₂m hK₂c hK₂p hÂmΩ hÂc hÂℋ hÂl hGℋ hGF hGζ hGA hK₂
  -- the law at `ℓ + 2`
  have hK₂Ω : @IsDyadicHitMeasurable Ω mΩ K₂ := fun n j => hℋ _ (hK₂m n j)
  have hs2 : lineFiltC P 𝓖 0 ≤ aeSigma (stageMarks κ b jumps E u l k (ℓ + 2)) P := by
    rw [h𝓜def]
    exact inf_le_right.trans (WalkLaw.aeSigma_mono h𝓖s)
  refine ⟨G, canonField κ h (fun _ => (0 : ℝ)) hK₂c hK₂p,
    max Mℓ (sleLambda κ + |-(Real.pi / 2) * chiC κ|),
    ⟨hK₂m, hK₂c, hK₂p, hGℋ, ?_, measurable_canonField κ hh.1 hK₂c hK₂p hK₂Ω measurable_const,
      Eventually.of_forall fun ω _ => isChartTransport_canonField κ h (fun _ => (0 : ℝ)) hK₂c hK₂p ω,
      measurable_stepWord κ _ (hx₀.mono h𝓜ℋ le_rfl) (hβ𝓜.mono h𝓜ℋ le_rfl) hrℋ,
      isSorted_stepWord κ _ x₀ _ _, le_max_of_le_left hMℓ0,
      abs_fn_stepWord_le hκ _ x₀ _ (fun ω => abs_fn_shiftW_le (hβ₁b ω) (x₀ ω)), hcore⟩, ?_, hGF, hGζ, hK₂, ?_⟩
  · filter_upwards [hL₂K] with ω h1 hωG using h1 hωG.1.2
  · -- the word is measurable for the completed retained past of stage `ℓ + 2`
    have hx₀s : Measurable[aeSigma (stageMarks κ b jumps E u l k (ℓ + 2)) P] x₀ := hx₀.mono hs2 le_rfl
    have hβ₁s2 : Measurable[aeSigma (stageMarks κ b jumps E u l k (ℓ + 2)) P] β₁ :=
      hβ₁s.mono (WalkLaw.aeSigma_mono hss) le_rfl
    have hβs : Measurable[aeSigma (stageMarks κ b jumps E u l k (ℓ + 2)) P]
        fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω) :=
      BoundaryWord.measurable_shiftW.comp (hx₀s.prodMk hβ₁s2)
    have hrts : Measurable[aeSigma (stageMarks κ b jumps E u l k (ℓ + 2)) P]
        fun ω => if ω ∈ F then recOf ⊤ (Dr ω) else recOf ⊤ Mz.zeroDrv :=
      Measurable.ite (hs2 _ hF) (hDrm.mono (hs1s.trans (le_aeSigma _ _)) le_rfl) measurable_const
    have hrs : Measurable[aeSigma (stageMarks κ b jumps E u l k (ℓ + 2)) P]
        fun ω => recOf ⊤ (maskDrv F (fun ω => driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)) ω) :=
      (WholeField.measurable_aeSigma_of_ae_eq' (P := P) hrts heqr).mono
        (StagedEntrance.aeSigma_le_aeSigma le_rfl) le_rfl
    exact measurable_stepWord κ _ hx₀s hβs hrs
  · -- the coverage
    filter_upwards [hS₂hull, hlifeTop, hlife, hrunw, hFFr] with ω h1 h2 h3 h4 h5 hωF hωL hl
    have hΛ : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠
          none := by
      rw [h4]; exact hl
    obtain ⟨hHP, -, -⟩ := h1 hωL
    have hR : (recOf ⊤ (maskDrv F (fun ω => driverOf h12p hκ (-(Real.pi / 2))
        (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)) ω)).2.1 ≠ ⊤ := by
      rw [maskDrv_of_mem hωF]
      have e2 : (recOf ⊤ (driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω))).2.1 =
          (driverOf h12p hκ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)).2 :=
        min_eq_right le_top
      rw [e2, h3 (h5 hωF)]
      exact h2 (h5 hωF) hHP
    exact ⟨⟨⟨hωF, hR⟩, hωL⟩, hΛ⟩


/-- **Root twin** (`Cr.RootVersionS`, D80) of `Fo.mvLaw_succ_succ_joint`.
**SB2(2)'s retained law, step `ℓ → ℓ + 2`, with the JOINT second line set (D51 item 1)**: `Fl.mvLaw_succ_succ`
for `Nd.SB2LowerStageVersionStatement5`'s line family (`A₂ t = fill (A ∪ B_{≤ℓ} capped at t)`); at `ℓ = relOff` with
the tail start `tL = τE` it is the root step (D51 item 2). -/
theorem mvLaw_succ_succ_joint_root (h12p : Theorem12ParamStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
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
    {𝓖 𝓖' : Filtration ℝ≥0 mΩ} {A₁ A₂ A₁' : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : 𝓖 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hA : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
        ω ∧
      A₂ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1) ω) ω)
    (h𝓖' : 𝓖' 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3))
    (hA' : ∀ᵐ ω ∂P, A₁' 0 ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ω)
    -- the law at `ℓ`
    {Gℓ : Set Ω} {Kℓ : Ω → Set ℂ} {Yℓ : Ω → DistOn upperHalfPlaneOpens} {β₁ : Ω → BoundaryWord} {Mℓ : ℝ}
    (hlaw : MvLaw κ (lineFiltC P 𝓖 0) P h (A₁ 0) Kℓ Gℓ Yℓ β₁ Mℓ)
    (hβ₁s : Measurable[aeSigma (stageMarks κ b jumps E u l k ℓ) P] β₁)
    -- F2b′'s objects at `ℓ` for the word `β₁`
    {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {F Fr : Set Ω} {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0}
    {relLife : Ω → ℝ≥0∞} (hKm : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hKF : ∀ᵐ ω ∂P, ω ∈ Fr → fillH (K ω) = A₁ 0 ω) (hx₀ : Measurable[lineFiltC P 𝓖 0] x₀)
    (hF : MeasurableSet[lineFiltC P 𝓖 0] F) (hFFr : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ Fr)
    (hFl : ∀ᵐ ω ∂P, ω ∈ Fr → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (S : Cr.RootVersionS κ (-(Real.pi / 2)) P Fr 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
      (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) types pc tL
      (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife)
    (hcl2 : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ Fr →
      (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 → ∃ m, (S.ver m).a t ω < S.V m ω)
    (htypes : types.Countable)
    (hcover : ∀ᵐ ω ∂P, ω ∈ Fr → angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω)) ∈ types)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P,
      ω ∈ wordTypeCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) Fr w →
      ω ∈ seedCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) Fr w)
    -- the kernel half at `ℓ`: K2's stopped match and the canonical lifetime
    (hK2 : ∀ᵐ ω ∂P, ω ∈ Fr → ∀ m, IsStopDrvMatch (driverCode h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
      (fun t => (S.ver m).W t ω) (S.V m ω))
    (hlife : ∀ᵐ ω ∂P, ω ∈ Fr → (driverOf h12p hκ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω),
      Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 = relLife ω)
    (hFG : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ Gℓ)
    -- the record matching
    {Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDr : Measurable[stageMarks κ b jumps E u l k (ℓ + 1)] Dr)
    (hDrreg : ∀ ω, IsRegularDriver (Dr ω))
    (hDreq : ∀ᵐ ω ∂P, ω ∈ F → recOf ⊤ (Dr ω) = recOf ⊤ (driverOf h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))))
    -- a retained hull of stage `ℓ + 2`
    {K₂ : Ω → Set ℂ} (hK₂m : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖' 0) K₂)
    (hK₂c : ∀ ω, IsCompact (K₂ ω)) (hK₂p : ∀ ω, IsPreconnected (K₂ ω ∪ Restart.lowerHalf)) {L₂ : Set Ω}
    (hL₂ : MeasurableSet[lineFiltC P 𝓖' 0] L₂) (hL₂K : ∀ᵐ ω ∂P, ω ∈ L₂ → fillH (K₂ ω) = A₁' 0 ω) :
    ∃ (G₂ : Set Ω) (Y₂ : Ω → DistOn upperHalfPlaneOpens) (β₂ : Ω → BoundaryWord) (M₂ : ℝ),
      MvLaw κ (lineFiltC P 𝓖' 0) P h (A₁' 0) K₂ G₂ Y₂ β₂ M₂ ∧
      Measurable[aeSigma (stageMarks κ b jumps E u l k (ℓ + 2)) P] β₂ ∧
      ∀ᵐ ω ∂P, ω ∈ F → ω ∈ L₂ →
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠ none →
        ω ∈ G₂ := by
  obtain ⟨G₂, Y₂, M₂, h1, h2, -, -, -, h3⟩ := mvLaw_succ_succ_jointX_root h12p h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ'
    hE hER hlθ k ℓ hwℓ hwℓ₂ h𝓖 hA h𝓖' hA' hlaw hβ₁s hKm hKc hKp hKF hx₀ hF hFFr hFl S hcl2 htypes hcover hseed hK2
    hlife hFG hDr hDrreg hDreq hK₂m hK₂c hK₂p hL₂ hL₂K
  exact ⟨G₂, Y₂, _, M₂, h1, h2, h3⟩


end InteractingSLE.Theorem14.SB.Cd
