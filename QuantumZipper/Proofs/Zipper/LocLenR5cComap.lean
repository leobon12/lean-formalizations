import QuantumZipper.Proofs.Zipper.LocHitScalePStar
import QuantumZipper.Proofs.Zipper.LocLenF2Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5c (D75): B5 locality for the open-arc length zipper `zipLenDownArc`

Open-arc copy (`handoff/FOLLOW-PAPER-13.md`, task R5c) of the LOCRICH-COMAP chain
(`E6LocAbsBasic.lean`, `LocRichComapBasic.lean`, `LocRichComapMain.lean`,
`LocRichComapField.lean:229`, `LocRichComapPath.lean:166`), with `zipLenDown ↦ zipLenDownArc`,
`tHit ↦ lenTimeArc`, `unzipLengths ↦ unzipLengthsArc`. The proofs are verbatim copies; the only
analytic input changed is the drive-locality of the open-arc lengths
(`LocLen.unzipLengthsArc_eq_of_drive_eqOn`).

* `LocalAbsArc`, `LocalAbsRichArcStmt`, **`unzipMeasArc_of_localAbsRich : LocalAbsRichArcStmt →
  UnzipMeasArcStmt`** (copy of `E6.unzipMeasStmt_of_localAbsRich`);
* `LocHitScaleArcStmt`, `localAbsRichArcStmt_of_hitScale` (copy of
  `E6.localAbsRichStmt_of_hitScale`).

Sheffield arXiv:1012.4797 §5.4, pp. 70–72 asserts this locality without proof (the unzipping
by quantum length `ℓ` only sees the field near `η[0, t_ℓ]`); own elementary bookkeeping, as for
the originals.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper.LocLen.R5c

open E6 D3Plus MeasUnzip CharFun

variable {Ω' : Type*} [MeasurableSpace Ω']

/-! ## `LocalAbs` for `zipLenDownArc` and `UnzipMeasArcStmt` -/

/-- Copy of `E6.LocalAbs` (E6.lean:62) for `zipLenDownArc` and `loc = locRich`. -/
def LocalAbsArc (γ ℓ₁ : ℝ) (P' : Measure Ω') (c' : Ω' → Cfg) (Reg : Set Cfg) : Prop :=
  ∀ R : ℕ, ∀ ε : ℝ≥0∞, 0 < ε → ∃ R' : ℕ, ∃ F : FullData → FullData, ∃ A : Set FullData,
    Measurable F ∧ MeasurableSet A ∧ P' {ω' | locRich R' (c' ω') ∉ A} ≤ ε ∧
    ∀ y ∈ Reg, locRich R' y ∈ A → locRich R (zipLenDownArc γ ℓ₁ y) = F (locRich R' y)

/-- Copy of `E6.LocalAbsRichStmt` (E6LocAbsBasic.lean:159) for `zipLenDownArc`. -/
def LocalAbsRichArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ ℓ₁ : ℝ, 0 < ℓ₁ → ∃ Reg : Set Cfg, (∀ᵐ ω' ∂P', (Y ω', drive κ B' ω') ∈ Reg) ∧
      LocalAbsArc (Real.sqrt κ) ℓ₁ P' (fun ω' => (Y ω', drive κ B' ω')) Reg

/-- Copy of `E6.LocRichComapStmt` (E6LocAbsBasic.lean:75). -/
def LocRichComapArcStmt (γ ℓ₁ : ℝ) (P' : Measure Ω') (c' : Ω' → Cfg) (Reg : Set Cfg) : Prop :=
  ∀ R : ℕ, ∀ ε : ℝ≥0∞, 0 < ε → ∃ R' : ℕ, ∃ A : Set FullData, ∃ g : Cfg → FullData,
    MeasurableSet A ∧ P' {ω' | locRich R' (c' ω') ∉ A} ≤ ε ∧
    Measurable[(inferInstance : MeasurableSpace FullData).comap (locRich R')] g ∧
    ∀ y ∈ Reg, locRich R' y ∈ A → locRich R (zipLenDownArc γ ℓ₁ y) = g y

/-- Copy of `E6.localAbs_of_comap`. -/
theorem localAbsArc_of_comap {γ ℓ₁ : ℝ} {P' : Measure Ω'} {c' : Ω' → Cfg} {Reg : Set Cfg}
    (h : LocRichComapArcStmt γ ℓ₁ P' c' Reg) : LocalAbsArc γ ℓ₁ P' c' Reg := by
  intro R ε hε
  obtain ⟨R', A, g, hA, hPA, hg, hloc⟩ := h R ε hε
  obtain ⟨F, hF, hgF⟩ := exists_measurable_factor_fullData hg
  exact ⟨R', F, A, hF, hA, hPA, fun y hy hyA => (hloc y hy hyA).trans (hgF y)⟩

/-- Copy of `E6.aemeasurable_locRich_unzip_of_localAbs_ae`. -/
theorem aemeasurable_locRich_unzipArc_of_localAbs_ae {γ ℓ₁ : ℝ} {P' : Measure Ω'}
    {c' : Ω' → Cfg} {Reg : Set Cfg} (hLoc : LocalAbsArc γ ℓ₁ P' c' Reg)
    (hc'm : ∀ R, AEMeasurable (fun ω' => locRich R (c' ω')) P') (hReg' : ∀ᵐ ω' ∂P', c' ω' ∈ Reg)
    (R : ℕ) : AEMeasurable (fun ω' => locRich R (zipLenDownArc γ ℓ₁ (c' ω'))) P' := by
  have hε : ∀ n : ℕ, (0 : ℝ≥0∞) < (n : ℝ≥0∞)⁻¹ := fun n =>
    ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n)
  choose R' F A hF hA hPA hloc using fun n : ℕ => hLoc R _ (hε n)
  set m : ℕ → Ω' → FullData := fun n => (hc'm (R' n)).mk _ with hmdef
  have hm : ∀ n, Measurable (m n) := fun n => (hc'm (R' n)).measurable_mk
  have hme : ∀ n, ∀ᵐ ω' ∂P', locRich (R' n) (c' ω') = m n ω' := fun n =>
    (hc'm (R' n)).ae_eq_mk
  set E : ℕ → Set Ω' := fun n => m n ⁻¹' A n with hEdef
  have hE : ∀ n, MeasurableSet (E n) := fun n => hm n (hA n)
  have h1 : ∀ n, AEMeasurable (fun ω' => locRich R (zipLenDownArc γ ℓ₁ (c' ω')))
      (P'.restrict (E n)) := by
    intro n
    refine ⟨fun ω' => F n (m n ω'), (hF n).comp (hm n), ?_⟩
    filter_upwards [ae_restrict_mem (hE n), ae_restrict_of_ae hReg', ae_restrict_of_ae (hme n)]
      with ω' hω hreg heq
    have hω' : locRich (R' n) (c' ω') ∈ A n := by rw [heq]; exact hω
    rw [hloc n (c' ω') hreg hω', heq]
  have h2 := aemeasurable_iUnion_iff.2 h1
  have hnull : P' (⋃ n, E n)ᶜ = 0 := by
    refine le_antisymm (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun n => ?_)
      (by simp)
    have hsub : (⋃ n, E n)ᶜ ⊆ {ω' | locRich (R' n) (c' ω') ∉ A n} ∪
        {ω' | locRich (R' n) (c' ω') ≠ m n ω'} := by
      intro ω' hω'
      by_cases heq : locRich (R' n) (c' ω') = m n ω'
      · left
        intro hin
        exact hω' (mem_iUnion.2 ⟨n, show m n ω' ∈ A n by rw [← heq]; exact hin⟩)
      · exact Or.inr heq
    have h0 : P' {ω' | locRich (R' n) (c' ω') ≠ m n ω'} = 0 := ae_iff.1 (hme n)
    calc P' (⋃ n, E n)ᶜ ≤ P' {ω' | locRich (R' n) (c' ω') ∉ A n} +
          P' {ω' | locRich (R' n) (c' ω') ≠ m n ω'} :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ (n : ℝ≥0∞)⁻¹ := by rw [h0, add_zero]; exact hPA n
  have hfull : ∀ᵐ ω' ∂P', ω' ∈ ⋃ n, E n := measure_eq_zero_iff_ae_notMem.1 hnull |>.mono
    fun ω' h => by simpa using h
  rwa [Measure.restrict_eq_self_of_ae_mem hfull] at h2

/-- Copy of `E6.aemeasurable_dataFull_unzip_of_localAbs_ae`. -/
theorem aemeasurable_dataFull_unzipArc_of_localAbs_ae {γ ℓ₁ : ℝ} {P' : Measure Ω'}
    {c' : Ω' → Cfg} {Reg : Set Cfg} (hLoc : LocalAbsArc γ ℓ₁ P' c' Reg)
    (hc'm : ∀ R, AEMeasurable (fun ω' => locRich R (c' ω')) P') (hReg' : ∀ᵐ ω' ∂P', c' ω' ∈ Reg) :
    AEMeasurable (dataFull fun ω' => zipLenDownArc γ ℓ₁ (c' ω')) P' := by
  refine aemeasurable_of_truncFull _ fun R => ?_
  have hf : (fun ω' => truncFull R (dataFull (fun ω' => zipLenDownArc γ ℓ₁ (c' ω')) ω')) =
      fun ω' => locRich R (zipLenDownArc γ ℓ₁ (c' ω')) :=
    funext fun ω' => truncFull_cfgFull R _
  rw [hf]
  exact aemeasurable_locRich_unzipArc_of_localAbs_ae hLoc hc'm hReg' R

/-- **`UnzipMeasArcStmt` from B5 locality** (copy of `E6.unzipMeasStmt_of_localAbsRich`,
E6LocAbsBasic.lean:166). -/
theorem unzipMeasArc_of_localAbsRich (h : LocalAbsRichArcStmt) : UnzipMeasArcStmt := by
  intro κ Ω' _ P' _ Y B' hP ℓ₁ hℓ
  obtain ⟨Reg, hReg', hLoc⟩ := h κ P' Y B' hP ℓ₁ hℓ
  exact aemeasurable_dataFull_unzipArc_of_localAbs_ae hLoc (aemeasurable_locRich_pstar hP) hReg'

/-! ## The almost-sure σ-algebra form (copy of `LocRichComapBasic.lean`) -/

/-- Copy of `E6.LocRichComapAEStmt`. -/
def LocRichComapAEArcStmt (γ ℓ₁ : ℝ) (P' : Measure Ω') (c' : Ω' → Cfg) : Prop :=
  ∀ R : ℕ, ∀ ε : ℝ≥0∞, 0 < ε → ∃ R' : ℕ, ∃ A : Set FullData, ∃ g : Cfg → FullData,
    MeasurableSet A ∧ P' {ω' | locRich R' (c' ω') ∉ A} ≤ ε ∧
    Measurable[(inferInstance : MeasurableSpace FullData).comap (locRich R')] g ∧
    ∀ᵐ ω' ∂P', locRich R' (c' ω') ∈ A → locRich R (zipLenDownArc γ ℓ₁ (c' ω')) = g (c' ω')

/-- Copy of `E6.exists_reg_locRichComap_of_ae`. -/
theorem exists_reg_locRichComapArc_of_ae {γ ℓ₁ : ℝ} {P' : Measure Ω'} {c' : Ω' → Cfg}
    (h : LocRichComapAEArcStmt γ ℓ₁ P' c') :
    ∃ Reg : Set Cfg, (∀ᵐ ω' ∂P', c' ω' ∈ Reg) ∧ LocRichComapArcStmt γ ℓ₁ P' c' Reg := by
  have hε : ∀ n : ℕ, (0 : ℝ≥0∞) < (n : ℝ≥0∞)⁻¹ := fun n =>
    ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n)
  choose R' A g hA hPA hg hae using fun R n => h R _ (hε n)
  refine ⟨{y | ∀ R n, locRich (R' R n) y ∈ A R n → locRich R (zipLenDownArc γ ℓ₁ y) = g R n y},
    ?_, ?_⟩
  · have : ∀ᵐ ω' ∂P', ∀ R n, locRich (R' R n) (c' ω') ∈ A R n →
        locRich R (zipLenDownArc γ ℓ₁ (c' ω')) = g R n (c' ω') := by
      rw [ae_all_iff]; intro R; rw [ae_all_iff]; exact hae R
    exact this
  · intro R ε hε0
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε0.ne'
    exact ⟨R' R n, A R n, g R n, hA R n, (hPA R n).trans hn.le, hg R n,
      fun y hy hyA => hy R n hyA⟩

/-- Copy of `E6.localAbsRichStmt_of_ae`. -/
theorem localAbsRichArcStmt_of_ae
    (h : ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
      ∀ ℓ₁ : ℝ, 0 < ℓ₁ →
        LocRichComapAEArcStmt (Real.sqrt κ) ℓ₁ P' (fun ω' => (Y ω', drive κ B' ω'))) :
    LocalAbsRichArcStmt := by
  intro κ Ω' _ P' _ Y B' hP ℓ₁ hℓ
  obtain ⟨Reg, hReg, hc⟩ := exists_reg_locRichComapArc_of_ae (h κ P' Y B' hP ℓ₁ hℓ)
  exact ⟨Reg, hReg, localAbsArc_of_comap hc⟩

end QuantumZipper.LocLen.R5c
