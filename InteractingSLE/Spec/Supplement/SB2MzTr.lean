/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MzPart
import InteractingSLE.Spec.Supplement.SBTail2RetainFreeze

/-!
# Transfers to the upper kernel: the stage laws and the offset events

Packet PROVE-SB2-LCMEAN, round 15 (item 4). Under the upper kernel `Q = condExpKernel P (upper past) ω₀`, the gluing
uses the marks `marksQ n`: the upper past, B's past before stage `n` (both for the raw drivers) and the stage marks
`Ms.stageMarks n` (regularized drivers). They contain the upper past exactly, are countably generated, and agree with
`Ms.stageMarks n` up to null sets.

* `marksQ` and its API (`marksQ_le`, `marksQ_mono`, `stageMarks_le_marksQ`, `upperPast_le_marksQ`,
  `countablyGenerated_marksQ`, `marksQ_le_aeSigma`);
* **`ae_ae_isGFF_marksQ`**: a conditional GFF law given `Ms.stageMarks n` under `P` holds, for `P`-a.e. `ω₀`, given
  `marksQ n` under `Q`;
* **`ae_offset_decided`**: for `P`-a.e. `ω₀`, each offset event of B at `R = realMax (upper prefix at ω₀)` is, up to
  `Q`-null sets, an event of `marksQ (o + 2)` (`Mz.exists_measurableSet_relOffEvent`, the runs frozen under the kernels
  (`Retain.ae_ae_run_eq`) and moved to `Q` (`Lk.ae_ae_nested_of_ae_sup`), `WalkLaw.mem_aeSigma_of_frozen`).

All statements are standard (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mz

open Restart Exist Exist.Staged Exist.StagedLaw Lu

section Marks

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
  (l : List (ℝ × ℝ≥0)) (k : ℕ)

/-- **The marks under the upper kernel** at the start of B's stage `n`. -/
@[instance_reducible]
def marksQ (n : ℕ) : MeasurableSpace Ω :=
  pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k ⊔
    pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) n ⊔ Ms.stageMarks κ b jumps E u l k n

variable {κ b jumps E u l k}

theorem upperPast_le_marksQ (n : ℕ) :
    pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k ≤ marksQ κ b jumps E u l k n :=
  le_sup_left.trans le_sup_left

theorem lowerPast_le_marksQ (n : ℕ) :
    pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) n ≤ marksQ κ b jumps E u l k n :=
  le_sup_right.trans le_sup_left

theorem stageMarks_le_marksQ (n : ℕ) : Ms.stageMarks κ b jumps E u l k n ≤ marksQ κ b jumps E u l k n :=
  le_sup_right

theorem marksQ_mono : Monotone (marksQ κ b jumps E u l k) := fun _ _ hmn =>
  sup_le_sup (sup_le_sup le_rfl (pastSigma_mono _ _ hmn)) (sup_le_sup le_rfl (pastSigma_mono _ _ hmn))

end Marks

section Meas

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ}

theorem pastSigma_le (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec)
    {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDm : ∀ j, Measurable (D j)) (hreg : ∀ j ω, IsRegularDriver (D j ω))
    (n : ℕ) : pastSigma κ b jumps spec D n ≤ mΩ := by
  rw [pastSigma_eq_comap]
  exact (measurable_pastMap runMeasStatement hb spec (fun j _ => hDm j) (fun j _ => hreg j) n le_rfl).comap_le

omit mΩ in
theorem countablyGenerated_pastSigma (spec : ExplSpec) (D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    @MeasurableSpace.CountablyGenerated Ω (pastSigma κ b jumps spec D n) := by
  rw [pastSigma_eq_comap]
  have : MeasurableSpace.CountablyGenerated (PastData n) := by
    let := upgradeStandardBorel (PastData n)
    infer_instance
  exact MeasurableSpace.CountablyGenerated.comap _

omit mΩ in
theorem countablyGenerated_marksQ (n : ℕ) :
    @MeasurableSpace.CountablyGenerated Ω (marksQ κ b jumps E u l k n) :=
  MeasurableSpace.CountablyGenerated.sup
    (MeasurableSpace.CountablyGenerated.sup (countablyGenerated_pastSigma _ _ _)
      (countablyGenerated_pastSigma _ _ _))
    (MeasurableSpace.CountablyGenerated.sup (countablyGenerated_pastSigma _ _ _)
      (countablyGenerated_pastSigma _ _ _))

/-- A past of the raw drivers is, up to null sets, the past of the regularized ones. -/
theorem pastSigma_le_aeSigma_reg [StandardBorelSpace Ω] {P : Measure Ω} {spec : ExplSpec}
    {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hR : StagedPiecesRegular κ b jumps P spec D) (n : ℕ) :
    pastSigma κ b jumps spec D n ≤
      LocalSets.aeSigma (pastSigma κ b jumps spec (StagedReg.regHist spec D) n) P := by
  rw [pastSigma_eq_comap, pastSigma_eq_comap]
  exact StagedReg.comap_le_aeSigma (StagedReg.ae_pastMap_regHist hR n)

end Meas

section Transfer

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ}

/-- The marks under the upper kernel are events. -/
theorem marksQ_le (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEu : IsStagedHistory κ b jumps P h (upperSpec u l) (E (upperSpec u l)))
    (hEl : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))) (n : ℕ) :
    marksQ κ b jumps E u l k n ≤ mΩ :=
  sup_le (sup_le (hEu.2.1 k) (hEl.2.1 n))
    (sup_le (pastSigma_le hb _ (StagedReg.measurable_regHist hEu.1) StagedReg.isRegularDriver_regHist k)
      (pastSigma_le hb _ (StagedReg.measurable_regHist hEl.1) StagedReg.isRegularDriver_regHist n))

omit [IsProbabilityMeasure P] in
/-- The marks under the upper kernel agree with the stage marks up to null sets. -/
theorem marksQ_le_aeSigma
    (hRu : StagedPiecesRegular κ b jumps P (upperSpec u l) (E (upperSpec u l)))
    (hRl : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))) (n : ℕ) :
    marksQ κ b jumps E u l k n ≤ LocalSets.aeSigma (Ms.stageMarks κ b jumps E u l k n) P :=
  sup_le (sup_le ((pastSigma_le_aeSigma_reg hRu k).trans (WalkLaw.aeSigma_mono (P := P) le_sup_left))
    ((pastSigma_le_aeSigma_reg hRl n).trans (WalkLaw.aeSigma_mono (P := P) le_sup_right)))
    (LocalSets.le_aeSigma _ P)

/-- **A stage law moves to the marks under the upper kernel.** -/
theorem ae_ae_isGFF_marksQ (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEu : IsStagedHistory κ b jumps P h (upperSpec u l) (E (upperSpec u l)))
    (hRu : StagedPiecesRegular κ b jumps P (upperSpec u l) (E (upperSpec u l)))
    (hEl : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    (hRl : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))) {n : ℕ} {G : Set Ω}
    {Z : Ω → DistOn upperHalfPlaneOpens} {c : Ω → BoundaryWord}
    (hlaw : ∀ᵐ ω₁ ∂P, ω₁ ∈ G → IsGFFWithBoundaryData (condExpKernel P (Ms.stageMarks κ b jumps E u l k n) ω₁) Z
      (c ω₁).fn (c ω₁).jumps) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω₁ ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ω₁ ∈ G → IsGFFWithBoundaryData (condExpKernel (condExpKernel P
        (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀) (marksQ κ b jumps E u l k n) ω₁) Z
        (c ω₁).fn (c ω₁).jumps := by
  have hMQ := marksQ_le (k := k) hb hEu hEl n
  have hSM : Ms.stageMarks κ b jumps E u l k n ≤ mΩ := (stageMarks_le_marksQ n).trans hMQ
  have hker : ∀ᵐ ω ∂P, condExpKernel P (Ms.stageMarks κ b jumps E u l k n) ω =
      condExpKernel P (marksQ κ b jumps E u l k n) ω :=
    KernelTower.ae_condExpKernel_eq_of_le_aeSigma hSM hMQ
      ((stageMarks_le_marksQ n).trans (LocalSets.le_aeSigma _ P)) (marksQ_le_aeSigma hRu hRl n)
  have hlaw' : ∀ᵐ ω₁ ∂P, ω₁ ∈ G → IsGFFWithBoundaryData (condExpKernel P (marksQ κ b jumps E u l k n) ω₁) Z
      (c ω₁).fn (c ω₁).jumps := by
    filter_upwards [hlaw, hker] with ω₁ h1 h2 hG
    rw [← h2]
    exact h1 hG
  let := upgradeStandardBorel (PastData k)
  have hf : Measurable (pastMap κ b jumps (upperSpec u l) (E (upperSpec u l)) k) := by
    rw [measurable_iff_comap_le, ← pastSigma_eq_comap]
    exact hEu.2.1 k
  have hup := upperPast_le_marksQ (κ := κ) (b := b) (jumps := jumps) (E := E) (u := u) (l := l) (k := k) n
  rw [pastSigma_eq_comap] at hup ⊢
  exact Mx.ae_ae_isGFF_upper hf hMQ hup (countablyGenerated_marksQ n) hlaw'

/-- **The offset events are, under the upper kernel and up to null sets, events of the marks.** For `P`-a.e. `ω₀`,
with `R` the right end of the upper prefix at `ω₀`, the event that B's offset is `o` (with `R` entered by `o + 1`) is,
up to `Q`-null sets, an event of `marksQ (o + 2)`. -/
theorem ae_offset_decided (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEu : IsStagedHistory κ b jumps P h (upperSpec u l) (E (upperSpec u l)))
    (hEl : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    (hRl : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))) (o : ℕ) :
    ∀ᵐ ω₀ ∂P, ∃ A : Set Ω, MeasurableSet[marksQ κ b jumps E u l k (o + 2)] A ∧
      A =ᵐ[condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀]
        {ω | relOffEvent κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
          (lowerD b jumps E ω) o} := by
  set spec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hspec
  have h𝒢 : marksQ κ b jumps E u l k (o + 2) ≤ mΩ := marksQ_le hb hEu hEl (o + 2)
  -- the regular event of the regularized lower family and the agreement of the runs
  have hR' := WalkLaw.stagedPiecesRegular_regHist hRl
  obtain ⟨M, hMae, hMm, hMp⟩ := hR'.ae_pieceRegular.exists_measurable_mem
  have hrunreg := StagedReg.ae_run_regHist hRl
  -- the runs before `o + 2` are frozen under the kernels given the marks
  have hfrP : ∀ᵐ x ∂P, ∀ᵐ ω ∂(condExpKernel P (marksQ κ b jumps E u l k (o + 2)) x), ∀ n, n ≤ o + 2 →
      ExplState.run κ b jumps spec (fun j => E spec j ω) n = ExplState.run κ b jumps spec (fun j => E spec j x) n := by
    have hn : ∀ n, ∀ᵐ x ∂P, ∀ᵐ ω ∂(condExpKernel P (marksQ κ b jumps E u l k (o + 2)) x), n ≤ o + 2 →
        ExplState.run κ b jumps spec (fun j => E spec j ω) n =
          ExplState.run κ b jumps spec (fun j => E spec j x) n := by
      intro n
      by_cases hno : n ≤ o + 2
      · filter_upwards [Retain.ae_ae_run_eq spec hRl h𝒢 ((pastSigma_mono _ _ hno).trans
          (lowerPast_le_marksQ (κ := κ) (b := b) (jumps := jumps) (E := E) (u := u) (l := l) (k := k)
            (o + 2)))] with x hx
        filter_upwards [hx] with ω hω _
        exact hω
      · exact Eventually.of_forall fun x => Eventually.of_forall fun ω h => absurd h hno
    filter_upwards [ae_all_iff.2 hn] with x hx
    exact ae_all_iff.2 fun n => hx n
  -- moved to the upper kernel
  let := upgradeStandardBorel (PastData k)
  have hf : Measurable (pastMap κ b jumps (upperSpec u l) (E (upperSpec u l)) k) := by
    rw [measurable_iff_comap_le, ← pastSigma_eq_comap]
    exact hEu.2.1 k
  have hup : MeasurableSpace.comap (pastMap κ b jumps (upperSpec u l) (E (upperSpec u l)) k) inferInstance ≤
      (marksQ κ b jumps E u l k (o + 2)) := by
    rw [← pastSigma_eq_comap]
    exact upperPast_le_marksQ (o + 2)
  have hsup : MeasurableSpace.comap (pastMap κ b jumps (upperSpec u l) (E (upperSpec u l)) k) inferInstance ⊔
      (marksQ κ b jumps E u l k (o + 2)) =
      (marksQ κ b jumps E u l k (o + 2)) := sup_eq_right.2 hup
  have hcg : @MeasurableSpace.CountablyGenerated Ω
      (MeasurableSpace.comap (pastMap κ b jumps (upperSpec u l) (E (upperSpec u l)) k) inferInstance ⊔
        (marksQ κ b jumps E u l k (o + 2))) := by
    rw [hsup]
    exact countablyGenerated_marksQ (o + 2)
  have hfrQ := Lk.ae_ae_nested_of_ae_sup (ℋ := marksQ κ b jumps E u l k (o + 2))
    (p := fun x μ => ∀ᵐ ω ∂μ, ∀ n, n ≤ o + 2 →
      ExplState.run κ b jumps spec (fun j => E spec j ω) n = ExplState.run κ b jumps spec (fun j => E spec j x) n)
    hf h𝒢 hcg (by rw [hsup]; exact hfrP)
  rw [← pastSigma_eq_comap] at hfrQ
  filter_upwards [hfrQ, KernelTower.ae_ae_condExpKernel_of_ae (hEu.2.1 k) hMae,
    KernelTower.ae_ae_condExpKernel_of_ae (hEu.2.1 k) hrunreg] with ω₀ hfr₀ hM₀ hrun₀
  set R₀ := realMax (upperPrefix κ b jumps E u l k ω₀)
  obtain ⟨S', hS'm, hS'⟩ := exists_measurableSet_relOffEvent hb (-(Real.pi / 2))
    (D := StagedReg.regHist spec (E spec)) (StagedReg.measurable_regHist hEl.1) StagedReg.isRegularDriver_regHist
    hMm hMp R₀ o
  have hmem := WalkLaw.mem_aeSigma_of_frozen (P := condExpKernel P
      (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀) h𝒢
    (E := {ω | relOffEvent κ (-(Real.pi / 2)) b jumps R₀ (lowerD b jumps E ω) o}) hS'm
    (M := M ∩ {ω | ∀ n, ExplState.run κ b jumps spec (fun j => StagedReg.regHist spec (E spec) j ω) n =
      ExplState.run κ b jumps spec (fun j => E spec j ω) n})
    (by filter_upwards [hM₀, hrun₀] with ω h1 h2; exact ⟨h1, h2⟩)
    (fun ω hω => by
      rw [← hS' ω hω.1]
      exact (relOffEvent_congr _ _ _ _ R₀ o fun n _ => (hω.2 n).symm))
    (by
      filter_upwards [hfr₀] with x hx
      filter_upwards [hx] with ω hω
      exact relOffEvent_congr _ _ _ _ R₀ o hω)
  obtain ⟨A, hA, hSA⟩ := hmem
  exact ⟨A, hA, hSA.symm⟩

end Transfer

end InteractingSLE.Theorem14.SB.Mz
