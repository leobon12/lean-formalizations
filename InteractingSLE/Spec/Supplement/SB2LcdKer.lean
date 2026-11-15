/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LcdUnion
import InteractingSLE.Spec.Supplement.RelSafeS6
import InteractingSLE.Spec.Supplement.GB6LineL3
import InteractingSLE.Spec.Supplement.GW2RdLocCore
import InteractingSLE.Spec.Sec7.R5SameLate

/-!
# SB2(2)'s union kernel on the physical lines of the lower walk

Packet PROVE-T14-SB2LCOND (round 2). Supplement p. 631: "At every rational ordinary time of the other history, its
marked union with `A` has the Gaussian local-set kernel."

* **`exists_lineVersion`** (generic): a set-valued map that is, in R58 form, a history-marked local set for marks
  `𝓜 ≤ mΩ` (avoidance events in `aeSigma 𝓜`, complement in `ℍ` a.s. open) has a version in exactly the form K2's
  lines ask (`BW1Lines.hasSafeMembers_life_of_lineLocal`'s `hBm`, `hBc`, `hloc`): measurable for the hitting
  σ-algebra (even for `𝓜`), inside `ℍ` with open complement at EVERY sample, almost surely equal to the given map,
  and marked local for `𝓜` (the relative closure in `ℍ` of `WalkLaw.exists_version_of_aeSigma`'s version);
* **`exists_kernel_of_lineVersion`** (generic): such a version has a local-set mean `g`, and given its germs and the
  marks the centred field paired with any test is Gaussian with mean `g` and the zero-boundary covariance of the
  complement (`RelSafeS.ae_condExp_cexp_marked`, Aux. lemma 18 with marks);
* **`sb2LowerLines_kernel`** (SB2(2)): both for the union of the upper prefix after `k` instructions and the lower walk
  through instruction `ℓ` with its piece `ℓ` stopped at own time `τ` (`sb2LowerLines_markedLocal`'s set and marks).

What K2's lines still need on top of this kernel is the identification of the mean `g` read in the relative chart of
the lifted stage (the union mean with the active relative word, a right-entry-chart mirror of R84/R89's
`FinRel.ae_chartTransport_eq_couplingMean_of_relConfigJK`) and the hull identity between the physical union and the
relative hull (SB2LIFT's geometric half).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lcd

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets

section Generic

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- **A line version of an R58-form marked local set**: hitting-measurable (for the marks), inside `ℍ` with open
complement at every sample, almost surely equal to the given map, marked local for the same marks. -/
theorem exists_lineVersion (𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}) {S : Ω → Set ℂ} {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hSH : ∀ ω, S ω ⊆ H) (hSo : ∀ᵐ ω ∂P, IsOpen (H \ S ω))
    (hS : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[aeSigma 𝓜.1 P] {ω | Disjoint (S ω) U})
    (hloc : WholeField.IsHistoryAvoidanceLocal 𝓜.1 S h₀ P) :
    ∃ B : Ω → Set ℂ, Measurable[𝓜.1, hittingSigma] B ∧ (∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω)) ∧
      (∀ᵐ ω ∂P, B ω = S ω) ∧ WholeField.IsHistoryAvoidanceLocal 𝓜.1 B h₀ P := by
  obtain ⟨A', -, hA'ae, hA'm⟩ := WalkLaw.exists_version_of_aeSigma (𝒢 := 𝓜.1) hSH hSo hS
  refine ⟨fun ω => relClosureH (A' ω), ?_, fun ω => ⟨Supp8.GB6LineL.relClosureH_subset_H _,
    Supp8.GB6LineL.isOpen_H_diff_relClosureH _⟩, ?_, ?_⟩
  · refine Sec7.R5Same.measurable_hitting_of_disjoint fun V hV hVH => ?_
    have e : {ω | Disjoint (relClosureH (A' ω)) V} = {ω | Disjoint (A' ω) V} := by
      ext ω
      exact GW2Rd.disjoint_relClosureH_iff hV hVH
    rw [e]
    exact hA'm ⟨V, hV⟩ hVH
  · filter_upwards [hA'ae, hSo] with ω h1 h2
    rw [h1]
    exact relClosureH_eq (hSH ω) h2
  · refine WalkLaw.isHistoryAvoidanceLocal_congr_ae ?_ hloc
    filter_upwards [hA'ae, hSo] with ω h1 h2
    rw [h1]
    exact (relClosureH_eq (hSH ω) h2).symm

/-- **The Gaussian local-set kernel of a line version**: a local-set mean `g`, and given the germs of the version and
the marks, the centred field paired with any test is Gaussian with mean `g` and the zero-boundary covariance of the
complement. -/
theorem exists_kernel_of_lineVersion (𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}) {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {B : Ω → Set ℂ}
    (hBm : Measurable[𝓜.1, hittingSigma] B) (hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hloc : WholeField.IsHistoryAvoidanceLocal 𝓜.1 B h₀ P) :
    ∃ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean B h₀ P g ∧ ∀ φ : TestOn upperHalfPlaneOpens,
      ∀ᵐ ω ∂P, P[fun ω' => Complex.exp (Complex.I * (h₀ ω' φ : ℂ)) | germSigma B h₀ ⊔ 𝓜.1] ω =
        Complex.exp (Complex.I * (g ω φ : ℂ)) * ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ B ω) φ φ) : ℝ) : ℂ) := by
  have hBm' : Measurable[mΩ, hittingSigma] B := hBm.mono 𝓜.2 le_rfl
  have hBc' : ∀ᵐ ω ∂P, B ω ⊆ H ∧ IsOpen (H \ B ω) := Eventually.of_forall hBc
  have hl : IsLocalSet B h₀ P := ((isLocalSet_tfae hh hBm' hBc').out 4 1).2 hloc.isAvoidanceLocal
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hh hBm' hl
  exact ⟨g, hg, fun φ => Supp8.RelSafeS.ae_condExp_cexp_marked hh hBm' hBc 𝓜.2 hloc hg φ⟩

end Generic

/-! ### SB2(2) -/

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **SB2(2)'s union kernel on the lower walk's physical lines.** For the regularized family, the union of the upper
prefix after `k` instructions and the lower walk through instruction `ℓ` with its piece `ℓ` stopped at own time `τ`
has a line version `B` (almost surely equal to it) with the Gaussian local-set kernel given its germs and the joined
retained pasts `𝓜 = pastSigma_upper(k) ⊔ pastSigma_capped(ℓ + 1)`. -/
theorem sb2LowerLines_kernel (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ) {θ : ℝ}
    {t : ℝ≥0∞} (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (θ, t))) (τ : ℝ≥0∞)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ (𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}) (B : Ω → Set ℂ) (g : Ω → DistOn upperHalfPlaneOpens),
      𝓜.1 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ∧
      Measurable[𝓜.1, hittingSigma] B ∧ (∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω)) ∧
      (∀ᵐ ω ∂P, B ω = WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω) ∧
      WholeField.IsHistoryAvoidanceLocal 𝓜.1 B (WholeField.centredField h u₀) P ∧
      IsLocalSetMean B (WholeField.centredField h u₀) P g ∧ ∀ φ : TestOn upperHalfPlaneOpens,
        ∀ᵐ ω ∂P, P[fun ω' => Complex.exp (Complex.I * (WholeField.centredField h u₀ ω' φ : ℂ)) |
            germSigma B (WholeField.centredField h u₀) ⊔ 𝓜.1] ω =
          Complex.exp (Complex.I * (g ω φ : ℂ)) *
            ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ B ω) φ φ) : ℝ) : ℂ) := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hup := hE' (Lu.upperSpec u l) (Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ)
  have hcap := isStagedHistory_capSpec (τ := τ) hb (hE' _ hw) (hreg' _) hℓ hwℓ
  obtain ⟨hA, ho, -, hloc⟩ := stageUnion_markedLocal h12p h13 hκ hκ4 hb hh hup hcap (hreg' _) (hreg' _) hu₀ k (ℓ + 1)
  have h𝓜 : pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ≤ mΩ :=
    sup_le (hup.2.1 k) (hcap.2.1 (ℓ + 1))
  set 𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ} := ⟨_, h𝓜⟩ with h𝓜def
  obtain ⟨B, hBm, hBc, hBae, hBloc⟩ := exists_lineVersion (P := P) 𝓜
    (fun ω => union_subset (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω))
    ho hA hloc
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨g, hg, hker⟩ := exists_kernel_of_lineVersion 𝓜 hh0 hBm hBc hBloc
  exact ⟨𝓜, B, g, rfl, hBm, hBc, hBae, hBloc, hg, hker⟩

end InteractingSLE.Theorem14.SB.Lcd
