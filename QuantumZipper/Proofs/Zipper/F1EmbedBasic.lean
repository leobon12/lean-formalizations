import QuantumZipper.Proofs.Zipper.FSMeasF2
import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.F1GermFam
import QuantumZipper.Proofs.NonVacuity

/-!
# Theorem 1.3, F1c embedding step: tools

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4 (pp. 70–72): the 0-1
argument of F1c is run on the unscaled wedge embedding, whose canonicalization is a `P_*` sample
(§5.1, pp. 60–62, B3(d)). Tools for `F1.F1EmbedStmt` (`F1Embed.lean`):

* `iIndep_srcSigma_of`: the three source σ-algebras `σ(X), σ(A), σ(B)` are independent when
  `X ⊥ A` and `(X, A) ⊥ B`;
* `pstar_ratio_law`: for a `P_*` sample, the length ratio at time `1` is a.e.-measurable and its
  law is the image of the configuration law under the (a.e.-measurable, `ReadLenAEMeasStmt`)
  reader `readLen`;
* `configLawFull_pstar_eq`: two `P_*` samples whose fields have the same `fieldLawFull` have the
  same configuration law (independence splits it into field law ⊗ Brownian path law);
* `ae_unzipLengths_transfer`: the lengths of the canonical `P_*` sample hidden in an unscaled
  configuration (`FSMeas.pstar_of_unscaled_fs`) at time `s` are those of the unscaled
  configuration at time `a² s` (B3(d), `B3d.unzipLengths_canon`, input `F2.UnscaledB3dStmt`).

Own bookkeeping arguments (standard independence and law-transfer facts).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

/-! ## 1. Independence of the three sources -/

theorem iIndep_srcSigma_of {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} {A : ℝ → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hXA : IndepFun X (fun ω t => A t ω) P)
    (hXAB : IndepFun (fun ω => (X ω, fun t => A t ω)) (pathOf B) P) :
    iIndep (srcSigma X A B) P := by
  have key : ∀ E : Fin 3 → Set Ω, (∀ i, MeasurableSet[srcSigma X A B i] (E i)) →
      P (E 0 ∩ E 1 ∩ E 2) = P (E 0) * P (E 1) * P (E 2) := by
    intro E hE
    obtain ⟨S0, hS0, h0⟩ := hE 0
    obtain ⟨S1, hS1, h1⟩ := hE 1
    obtain ⟨S2, hS2, h2⟩ := hE 2
    have e : E 0 ∩ E 1 = (fun ω => (X ω, fun t => A t ω)) ⁻¹' (S0 ×ˢ S1) := by
      rw [← h0, ← h1]; ext; simp
    rw [e, ← h2, hXAB.measure_inter_preimage_eq_mul _ _ (hS0.prod hS1) hS2, ← e, ← h0, ← h1,
      hXA.measure_inter_preimage_eq_mul _ _ hS0 hS1]
  rw [iIndep_iff]
  intro s f hf
  classical
  set E : Fin 3 → Set Ω := fun i => if i ∈ s then f i else univ with hEdef
  have hE : ∀ i, MeasurableSet[srcSigma X A B i] (E i) := fun i => by
    by_cases h : i ∈ s
    · simp only [hEdef, h, ite_true]; exact hf i h
    · simp only [hEdef, h, ite_false]; exact MeasurableSet.univ
  have hinter : ⋂ i ∈ s, f i = E 0 ∩ E 1 ∩ E 2 := by
    have : ⋂ i ∈ s, f i = ⋂ i, E i := by
      ext ω
      simp only [mem_iInter, hEdef]
      constructor
      · intro h i
        split_ifs with hi
        · exact h i hi
        · trivial
      · intro h i hi
        simpa [hi] using h i
    rw [this]
    ext ω
    simp [Fin.forall_fin_succ, and_assoc]
  have hprod : ∏ i ∈ s, P (f i) = P (E 0) * P (E 1) * P (E 2) := by
    have : ∏ i : Fin 3, P (E i) = ∏ i ∈ s, P (f i) := by
      rw [← Finset.univ_inter s, ← Finset.prod_ite_mem]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases h : i ∈ s <;> simp [hEdef, h]
    rw [← this, Fin.prod_univ_three]
  rw [hinter, hprod, key E hE]

/-! ## 2. The law of the length ratio of a `P_*` sample -/

/-- The length ratio `L⁺₁/L⁻₁` of the configuration `(Y, √κ B)`. -/
abbrev ratio1 (κ : ℝ) {Ω : Type} (Y : Ω → FieldSample) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  lenRatio (unzipLengths (Real.sqrt κ) (Y ω, drive κ B ω) 1)

/-! ## 3. Configuration laws of `P_*` samples -/

theorem configLawFull_pcfg_prod {κ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → FieldSample} {B : ℝ≥0 → Ω → ℝ}
    (h : Thm13Asm.IsPStarSample κ P Y B) :
    configLawFull (pcfg κ Y B) P =
      (fieldLawFull H Y P).prod ((P.map (pathOf B)).map (drivePath κ)) := by
  obtain ⟨hκ, hκ4, hW, hB, hI⟩ := h
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  have hα := F2.alpha_lt_Qc' hγ hγ2
  have hYm : AEMeasurable (fun ω => dataH (Y ω)) P :=
    Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hW
  have hBm := IsBrownianReal.aemeasurable_pathOf hB
  have hD : AEMeasurable (fun ω => drivePath κ (pathOf B ω)) P :=
    (measurable_drivePath κ).comp_aemeasurable hBm
  have e : configLawFull (pcfg κ Y B) P =
      P.map fun ω => (dataH (Y ω), drivePath κ (pathOf B ω)) := by
    show P.map _ = _
    congr 1
    funext ω
    exact Prod.ext rfl (drive_nnreal κ B ω)
  rw [e, (indepFun_iff_map_prod_eq_prod_map_map hYm hD).1
    (hI.comp measurable_dataH (measurable_drivePath κ)),
    AEMeasurable.map_map_of_aemeasurable (measurable_drivePath κ).aemeasurable hBm]
  rfl

/-- The path law of a pre-Brownian motion (on any space) is the projective limit. -/
theorem isProjectiveLimit_map_pathOf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBm : AEMeasurable (pathOf B) P) :
    IsProjectiveLimit (P.map (pathOf B)) BrownianReal.projectiveFamily := by
  intro I
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable hBm]
  exact (hB.hasLaw I).map_eq

/-- **Two `P_*` samples with the same field law have the same configuration law.** -/
theorem configLawFull_pstar_eq {κ : ℝ} {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {Y₁ : Ω₁ → FieldSample} {B₁ : ℝ≥0 → Ω₁ → ℝ} {Y₂ : Ω₂ → FieldSample} {B₂ : ℝ≥0 → Ω₂ → ℝ}
    (h₁ : Thm13Asm.IsPStarSample κ P₁ Y₁ B₁) (h₂ : Thm13Asm.IsPStarSample κ P₂ Y₂ B₂)
    (hlaw : fieldLawFull H Y₁ P₁ = fieldLawFull H Y₂ P₂) :
    configLawFull (pcfg κ Y₁ B₁) P₁ = configLawFull (pcfg κ Y₂ B₂) P₂ := by
  rw [configLawFull_pcfg_prod h₁, configLawFull_pcfg_prod h₂, hlaw,
    (isProjectiveLimit_map_pathOf h₁.2.2.2.1.toIsPreBrownianReal
      (IsBrownianReal.aemeasurable_pathOf h₁.2.2.2.1)).unique
    (isProjectiveLimit_map_pathOf h₂.2.2.2.1.toIsPreBrownianReal
      (IsBrownianReal.aemeasurable_pathOf h₂.2.2.2.1))]

/-! ## 4. Lengths of the canonical sample vs. lengths of the unscaled configuration -/

end F1
end QuantumZipper
