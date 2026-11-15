/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkMeanKernel
import InteractingSLE.Spec.Supplement.WalkLeafWire
import InteractingSLE.WangWu.PrefixLocalMean

/-!
# Theorem 1.4's union mean: the probabilistic assembly

Packet PROVE-T14-WALKMEAN. The leaf `WalkLaw.WalkUnionMeanRegAEStatement` (follow-up note A–E, D.5–D.6; Lemma GW3,
p. 636) asks for a measurable version `A'` of the union of the two walks and a function `μ` with four clauses: (1) the
pairings of `μ` are functions of the joined retained past `𝒥`; (2) `μ` is continuous on the between union; (3) `μ` is
the conditional mean of the field given the germs of `A'` and `𝒥`; (4) the component-chart formula (GW3.1).

This file proves clauses (1)–(3) and reduces the leaf to a **pathwise** statement about the local-set mean of the
union, `WalkUnionMeanPathStatement`: almost surely, on the between union, the local-set mean (plus the harmonic
extension `u₀` of the original data) is `Φ (runs)` for a **deterministic** function `Φ` of the two final runs, and
`Φ (runs)` obeys the chart formula (4). The pathwise statement contains no σ-algebra and no measurability.

* Clause (1) (D.5, "Measurability in the past") is **not** obtained from a Borel construction of the classified word
  or of conformal maps. The local-set mean is jointly measurable through its bump pairings (`bumpLim`); its value
  on the between union is a function of the runs, which agree on almost every fibre of the past
  (`WalkLaw.exists_run_eq_of_pastMap_eq`); so its average under the regular conditional kernel given `𝒥`
  (`kerAvg`) is a `𝒥`-measurable function equal to it on the between union (`ae_kerAvg_eq`).
* Clause (3) is the local-set mean of `A'` given the germs and the marks
  (`WangWu.IsLocalSetMean.ae_eq_condExp_germSigma_sup`), with the union marked by `𝒥` (`WalkLaw.walkUnion_markedAE` for the regularized family, PROVE-T14-WALK's marked
  locality from Theorems 1.2–1.3, and a transfer of the marks up to null sets).

## Main results

* `WalkUnionMeanPathStatement` (named input; pathwise, run-determined union mean with the chart formula);
* **`walkUnionMeanRegAEStatement_of_path`**: `WalkUnionMeanRegAEStatement` from Theorems 1.2 (param) and 1.3 and the
  pathwise statement; `walkUnionMeanRegAEStatement_of_path_roots` from the wiring's roots.

R48: Theorems 1.2–1.3 are used as hypotheses; these results serve Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkMean

open WalkLaw GW3Between LocalSets

/-! ### The final runs of the two walks -/

/-- The final states of the right and the left walk run with the drivers `E`. -/
def walkRuns (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (ω : Ω) : ExplState × ExplState :=
  (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length,
    ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)
      (boundaryWalkSpec b jumps (Real.pi / 2) false).2.2.length)

/-- The physical set of a history as a function of its final state (`ExplState.physSet` unfolded). -/
def physOf (spec : ExplSpec) (s : ExplState) : Set ℂ :=
  {(spec.1 : ℂ)} ∪ (⋃ p ∈ s.1, p.1.tipSet p.2.1 p.2.2) ∪ ⋃ a ∈ s.2.1, ((↑) : ℝ → ℂ) '' a

theorem physSet_eq_physOf (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.physSet κ b jumps spec D = physOf spec (ExplState.run κ b jumps spec D spec.2.2.length) := rfl

/-- The between union of the two walks as a function of their final states. -/
def betweenOf (b : ℝ → ℝ) (jumps : Finset ℝ) (r : ExplState × ExplState) : Set ℂ :=
  betweenUnion (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) r.1)
    (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) r.2)

/-! ### Two generic lemmas -/

section Generic

variable {Ω : Type*} {𝒢 ℋ ℋ' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- A random set whose avoidance events of open subsets of `ℍ` are events of a sub-σ-algebra is a random closed set
for the hitting σ-algebra. -/
theorem measurable_hitting_of_avoid (h𝒢 : 𝒢 ≤ mΩ) {A : Ω → Set ℂ}
    (hA : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝒢] {ω | Disjoint (A ω) U}) :
    Measurable[mΩ, hittingSigma] A := by
  refine @measurable_generateFrom Ω (Set ℂ) mΩ _ _ ?_
  rintro _ ⟨V, hVo, hVH, rfl⟩
  have e : A ⁻¹' {B | (B ∩ V).Nonempty} = {ω | Disjoint (A ω) ((⟨V, hVo⟩ : Opens ℂ) : Set ℂ)}ᶜ := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, Set.not_disjoint_iff_nonempty_inter]
    rfl
  rw [e]
  exact (h𝒢 _ (hA ⟨V, hVo⟩ hVH)).compl

/-- The history-marked avoidance criterion passes to marks that are events of the given marks up to null sets. -/
theorem isHistoryAvoidanceLocal_of_le_aeSigma {A : Ω → Set ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} (hle : ℋ ≤ aeSigma ℋ' P)
    (hloc : WholeField.IsHistoryAvoidanceLocal ℋ' A h P) : WholeField.IsHistoryAvoidanceLocal ℋ A h P := by
  intro U G hUH hG hd F hF
  obtain ⟨F', hF', hFF'⟩ := hle F hF
  obtain ⟨g, hg, hge⟩ := hloc U G hUH hG hd F' hF'
  refine ⟨g, hg, Filter.EventuallyEq.trans ?_ hge⟩
  refine condExp_congr_ae (indicator_ae_eq_of_ae_eq_set ?_)
  filter_upwards [hFF'] with ω hω
  simp only [mem_inter_iff, mem_ofPred_eq, eq_iff_iff]
  exact and_congr_right fun _ => Iff.of_eq hω

end Generic

/-! ### The named input -/

/-- **Named input: the union mean of the two walks, pathwise and determined by the runs** (follow-up note A–E,
D.2–D.6; Lemma GW3 and its proof, pp. 636–637). For a measurable version `A'` of the union of the two walks and
any version `g` of its local-set mean for the centred field `h − u₀`: there is a **deterministic** function `Φ` of the
two final runs such that, almost surely, `Φ (runs)` is harmonic on the between union, represents `g + u₀` there, and
obeys the component-chart formula (GW3.1) on every between component. ("Conditional on the labelled walks, … the
exact component heights": the mean is a function of the walks; the chart may be any component chart, its lift any
branch, so the formula fixes `Φ (runs)` only together with the representation clause.) -/
def WalkUnionMeanPathStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ A' : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A' → (∀ᵐ ω ∂P, A' ω = walkUnionSet κ b jumps E ω) →
    ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A' (WholeField.centredField h u₀) P g →
      ∃ Φ : ExplState × ExplState → ℂ → ℝ, ∀ᵐ ω ∂P,
        InnerProductSpace.HarmonicOnNhd (Φ (walkRuns κ b jumps E ω))
          (betweenUnion
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω))
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω))) ∧
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ betweenUnion
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω))
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) →
          g ω φ = ∫ z, (Φ (walkRuns κ b jumps E ω) z - u₀ z) * φ z) ∧
        ∀ C ∈ betweenComponents
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω))
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)),
          ∃ c : Chart, IsComponentChart
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
                (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω))
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
                (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) C c ∧
            ∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
              IsComponentBoundaryData κ b
                (ExplState.ordinarySet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
                  (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω))
                (ExplState.ordinarySet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
                  (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) c.2.1 bC jumpsC ∧
              ∀ u₀' : ℂ → ℝ, IsBoundedHarmonicExtension bC jumpsC u₀' →
                ∀ w ∈ H, u₀' w = Φ (walkRuns κ b jumps E ω) (c.2.1 w) + QuantumZipper.chiC κ * c.2.2 (c.2.1 w)

/-! ### The assembly -/

/-- **`WalkUnionMeanRegAEStatement` from Theorems 1.2–1.3 and the pathwise union mean.** -/
theorem walkUnionMeanRegAEStatement_of_path (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hpath : WalkUnionMeanPathStatement.{u}) :
    WalkUnionMeanRegAEStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ hSB P hP h hh W' ζ' hcf hζ' E hE hreg u₀ hu₀ wR wL
  classical
  have hpi := Real.pi_pos
  -- the regularized family
  obtain ⟨hE₁, hreg₁', hrun⟩ := StagedReg.regFam_spec hb hE hreg
  set E₁ := StagedReg.regFam E with hE₁def
  have hreg₁ : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E₁ spec) := fun spec hs => stagedPiecesRegular_regHist (hreg spec hs)
  have hprR : IsBoundaryContinuedProgram wR.2.2 := GW1X.isBoundaryContinuedProgram_walkR b jumps
  have hprL : IsBoundaryContinuedProgram wL.2.2 := GW1X.isBoundaryContinuedProgram_walkL b jumps
  have hdet := pastDetRegStatement_of_thm12_thm13 h12p h13
  have hRl := WalkLeaf.walkMarkedLocalRegAEStatement_of_thm12_thm13 h12p h13 (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith⟩ true
  have hLl := WalkLeaf.walkMarkedLocalRegAEStatement_of_thm12_thm13 h12p h13 (θ := Real.pi / 2)
    ⟨by linarith, le_rfl⟩ false
  obtain ⟨hAev, hAo, -, hloc₁⟩ := walkUnion_markedAE hdet hRl hLl hκ hκ4 hb hh hE₁ hreg₁ hreg₁' hu₀
  have hJle₁ : jointPast κ b jumps E₁ ≤ mΩ := sup_le ((hE₁ _ hprR).2.1 _) ((hE₁ _ hprL).2.1 _)
  have hJle : jointPast κ b jumps E ≤ mΩ := sup_le ((hE _ hprR).2.1 _) ((hE _ hprL).2.1 _)
  -- a measurable version of the union
  obtain ⟨A', -, hA'ae₁, hA'ev⟩ := exists_version_of_aeSigma (A := walkUnionSet κ b jumps E₁)
    (fun ω => union_subset (walkSet_subset_H _ _ _ _ _ ω) (walkSet_subset_H _ _ _ _ _ ω)) hAo hAev
  have hA'm : Measurable[mΩ, hittingSigma] A' := measurable_hitting_of_avoid hJle₁ hA'ev
  have hrunR := hrun _ hprR
  have hrunL := hrun _ hprL
  have hUeq : ∀ᵐ ω ∂P, walkUnionSet κ b jumps E₁ ω = walkUnionSet κ b jumps E ω := by
    filter_upwards [hrunR, hrunL] with ω h1 h2
    simp only [walkUnionSet, walkSet]
    rw [StagedReg.physSet_eq_of_run_eq (h1 _), StagedReg.physSet_eq_of_run_eq (h2 _)]
  have hA'ae : ∀ᵐ ω ∂P, A' ω = walkUnionSet κ b jumps E ω := by
    filter_upwards [hA'ae₁, hUeq] with ω h1 h2
    rw [h1, h2]
  -- the centred field, the marks and the local-set mean
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hloc₁' : WholeField.IsHistoryAvoidanceLocal (jointPast κ b jumps E₁) A' (WholeField.centredField h u₀) P :=
    isHistoryAvoidanceLocal_congr_ae (hA'ae₁.mono fun ω h => h.symm) hloc₁
  have hjp : ∀ (E₂ : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), jointPast κ b jumps E₂ =
      MeasurableSpace.comap (fun ω => (Exist.Staged.pastMap κ b jumps wR (E₂ wR) wR.2.2.length ω,
        Exist.Staged.pastMap κ b jumps wL (E₂ wL) wL.2.2.length ω)) inferInstance := fun E₂ =>
    (MeasurableSpace.comap_prodMk _ _).symm
  have hpae : (fun ω => (Exist.Staged.pastMap κ b jumps wR (E₁ wR) wR.2.2.length ω,
        Exist.Staged.pastMap κ b jumps wL (E₁ wL) wL.2.2.length ω)) =ᵐ[P]
      fun ω => (Exist.Staged.pastMap κ b jumps wR (E wR) wR.2.2.length ω,
        Exist.Staged.pastMap κ b jumps wL (E wL) wL.2.2.length ω) := by
    filter_upwards [StagedReg.ae_pastMap_regHist (hreg _ hprR) wR.2.2.length,
      StagedReg.ae_pastMap_regHist (hreg _ hprL) wL.2.2.length] with ω h1 h2
    exact Prod.ext h1 h2
  have hJJ : jointPast κ b jumps E ≤ aeSigma (jointPast κ b jumps E₁) P := by
    rw [hjp E, hjp E₁]
    exact StagedReg.comap_le_aeSigma hpae
  have hloc : WholeField.IsHistoryAvoidanceLocal (jointPast κ b jumps E) A' (WholeField.centredField h u₀) P :=
    isHistoryAvoidanceLocal_of_le_aeSigma hJJ hloc₁'
  have hAc : ∀ᵐ ω ∂P, A' ω ⊆ H ∧ IsOpen (H \ A' ω) := by
    filter_upwards [hA'ae₁, hAo] with ω h1 h2
    rw [h1]
    exact ⟨union_subset (walkSet_subset_H _ _ _ _ _ _) (walkSet_subset_H _ _ _ _ _ _), h2⟩
  have hlocA : IsLocalSet A' (WholeField.centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hA'm hAc).out 1 4).1 hloc.isAvoidanceLocal
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hh0 hA'm hlocA
  -- the pathwise union mean, transferred to the runs of `E`
  obtain ⟨Φ, hΦ₁⟩ := hpath κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E₁ hE₁ hreg₁ hreg₁' u₀ hu₀ A' hA'm hA'ae₁ g hg
  have hΦ : ∀ᵐ ω ∂P,
      InnerProductSpace.HarmonicOnNhd (Φ (walkRuns κ b jumps E ω))
        (betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω))
          (ExplState.physSet κ b jumps wL (fun k => E wL k ω))) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ betweenUnion
          (ExplState.physSet κ b jumps wR (fun k => E wR k ω)) (ExplState.physSet κ b jumps wL (fun k => E wL k ω)) →
        g ω φ = ∫ z, (Φ (walkRuns κ b jumps E ω) z - u₀ z) * φ z) ∧
      ∀ C ∈ betweenComponents (ExplState.physSet κ b jumps wR (fun k => E wR k ω))
          (ExplState.physSet κ b jumps wL (fun k => E wL k ω)),
        ∃ c : Chart, IsComponentChart (ExplState.physSet κ b jumps wR (fun k => E wR k ω))
            (ExplState.physSet κ b jumps wL (fun k => E wL k ω)) C c ∧
          ∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
            IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω))
              (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω)) c.2.1 bC jumpsC ∧
            ∀ u₀' : ℂ → ℝ, IsBoundedHarmonicExtension bC jumpsC u₀' →
              ∀ w ∈ H, u₀' w = Φ (walkRuns κ b jumps E ω) (c.2.1 w) +
                QuantumZipper.chiC κ * c.2.2 (c.2.1 w) := by
    filter_upwards [hΦ₁, hrunR, hrunL] with ω hω h1 h2
    have e : walkRuns κ b jumps E₁ ω = walkRuns κ b jumps E ω := Prod.ext (h1 _) (h2 _)
    rw [e, StagedReg.physSet_eq_of_run_eq (h1 _), StagedReg.physSet_eq_of_run_eq (h2 _),
      ordinarySet_eq_of_run_eq (h1 _), ordinarySet_eq_of_run_eq (h2 _)] at hω
    exact hω
  -- the regular conditional laws given the joined past live on fibres of the runs
  obtain ⟨NR, hNR, hfibR⟩ := exists_run_eq_of_pastMap_eq (hreg _ hprR) wR.2.2.length
  obtain ⟨NL, hNL, hfibL⟩ := exists_run_eq_of_pastMap_eq (hreg _ hprL) wL.2.2.length
  have hpRm : Measurable[jointPast κ b jumps E] (Exist.Staged.pastMap κ b jumps wR (E wR) wR.2.2.length) :=
    (comap_measurable _).mono le_sup_left le_rfl
  have hpLm : Measurable[jointPast κ b jumps E] (Exist.Staged.pastMap κ b jumps wL (E wL) wL.2.2.length) :=
    (comap_measurable _).mono le_sup_right le_rfl
  have hfR := Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) hJle hpRm
  have hfL := Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) hJle hpLm
  have hNRk := KernelTower.ae_ae_condExpKernel_of_ae (P := P) hJle hNR
  have hNLk := KernelTower.ae_ae_condExpKernel_of_ae (P := P) hJle hNL
  have hfib : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (jointPast κ b jumps E) ω₀),
      walkRuns κ b jumps E ω = walkRuns κ b jumps E ω₀ := by
    filter_upwards [hfR, hfL, hNRk, hNLk, hNR, hNL] with ω₀ e1 e2 n1 n2 h0R h0L
    filter_upwards [e1, e2, n1, n2] with ω f1 f2 m1 m2
    exact Prod.ext (hfibR ω m1 ω₀ h0R f1) (hfibL ω m2 ω₀ h0L f2)
  -- the bump limit of the local-set mean is the run-determined mean on the between union
  have hgm : Measurable g := hg.1.mono (germSigma_le hA'm hh0.measurable) le_rfl
  have hu₀c : ContinuousOn u₀ H := hu₀.1.continuousOn
  set M : Ω × ℂ → ℝ := bumpLim g u₀ with hMdef
  have hMm : Measurable M := measurable_bumpLim hgm hu₀c
  have hBUo : ∀ᵐ ω ∂P, IsOpen (betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω))
      (ExplState.physSet κ b jumps wL (fun k => E wL k ω))) := by
    filter_upwards [hAo, hUeq] with ω h1 h2
    rw [h2, walkUnionSet, H_diff_walkSet_union] at h1
    exact isOpen_betweenUnion h1
  have hMΦ : ∀ᵐ ω ∂P, ∀ z ∈ betweenOf b jumps (walkRuns κ b jumps E ω),
      M (ω, z) = Φ (walkRuns κ b jumps E ω) z := by
    filter_upwards [hΦ, hBUo] with ω hω ho z hz
    have hVH : betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω))
        (ExplState.physSet κ b jumps wL (fun k => E wL k ω)) ⊆ H := fun w hw => (betweenUnion_subset hw).1
    have hv : InnerProductSpace.HarmonicOnNhd (fun w => Φ (walkRuns κ b jumps E ω) w - u₀ w)
        (betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω))
          (ExplState.physSet κ b jumps wL (fun k => E wL k ω))) := fun w hw =>
      (hω.1 w hw).sub (hu₀.1 w (hVH hw))
    rw [hMdef, bumpLim_eq_of_harmonic ho hVH hv hω.2.1 hz, sub_add_cancel]
  have hμ := ae_kerAvg_eq hJle hfib hMΦ
  set μ := kerAvg (jointPast κ b jumps E) P M with hμdef
  refine ⟨A', hA'm, hA'ae, μ, fun φ => measurable_integral_kerAvg_mul hMm φ.continuous.measurable, ?_, ?_, ?_⟩
  · -- continuity on the between union
    filter_upwards [hμ, hΦ] with ω h1 h2
    have hc : ContinuousOn (Φ (walkRuns κ b jumps E ω)) (betweenUnion
        (ExplState.physSet κ b jumps wR (fun k => E wR k ω)) (ExplState.physSet κ b jumps wL (fun k => E wL k ω))) :=
      fun z hz => (h2.1 z hz).1.continuousAt.continuousWithinAt
    exact hc.congr fun z hz => h1 z hz
  · -- the conditional mean given the germs and the joined past
    intro φ
    filter_upwards [hμ, hΦ, hBUo, WangWu.IsLocalSetMean.ae_eq_condExp_germSigma_sup hh0 hA'm hlocA hJle hloc hg φ]
      with ω h1 h2 ho h3 hsupp
    have hsH : tsupport φ ⊆ H := hsupp.trans fun w hw => (betweenUnion_subset hw).1
    have hΦc : ContinuousOn (Φ (walkRuns κ b jumps E ω)) (betweenUnion
        (ExplState.physSet κ b jumps wR (fun k => E wR k ω)) (ExplState.physSet κ b jumps wL (fun k => E wL k ω))) :=
      fun z hz => (h2.1 z hz).1.continuousAt.continuousWithinAt
    have hi1 := LocalSets.integrable_mul_test ho hΦc φ hsupp
    have hi2 := LocalSets.integrable_mul_test QuantumZipper.isOpen_H hu₀c φ hsH
    have hμφ : (fun z => μ ω z * φ z) = fun z => Φ (walkRuns κ b jumps E ω) z * φ z := by
      funext z
      by_cases hz : z ∈ tsupport φ
      · rw [h1 z (hsupp hz)]
      · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
    rw [← h3, h2.2.1 φ hsupp, hμφ]
    simp_rw [sub_mul]
    exact integral_sub hi1 hi2
  · -- the component charts
    filter_upwards [hμ, hΦ] with ω h1 h2 C hC
    obtain ⟨c, hc, bC, jC, hbC, hcb, hform⟩ := h2.2.2 C hC
    refine ⟨c, hc, bC, jC, hbC, hcb, fun u₀' hu₀' w hw => ?_⟩
    rw [hform u₀' hu₀' w hw, h1 _ (subset_betweenUnion hC (hc.2.2.1 hw))]

/-- **`WalkUnionMeanRegAEStatement` from the roots of the expanded wiring and the pathwise union mean.** -/
theorem walkUnionMeanRegAEStatement_of_path_roots (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hpath : WalkUnionMeanPathStatement.{u}) :
    WalkUnionMeanRegAEStatement.{u} :=
  walkUnionMeanRegAEStatement_of_path (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13 hpath

end InteractingSLE.Theorem14.WalkMean
