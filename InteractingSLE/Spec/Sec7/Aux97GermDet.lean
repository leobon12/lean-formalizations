/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedKernel
import InteractingSLE.Spec.Sec7.Prop74ProofWord
import InteractingSLE.Spec.Sec7.Aux97ProofIdent
import InteractingSLE.Spec.Sec7.LocalExtFStmt

/-!
# Aux. lemma 97's germ identification: the field-determined driver of a fixed word

Packet PROVE-AUX97G. Source: Aux. lemma 97's proof (`source/spec/p289-336.md` L553–L576, p. 327: "the flow lines of
`h` and of the recoded field agree up to the stop; the recoded field's flow line is a Borel function of the field").

For a fixed ordered word and `κ > 0`, Theorem 1.2 in its word-measurable form (`Exist.Staged.Theorem12ParamStatement`,
R44) and Theorem 1.3 (`Exist.Theorem13Statement`, exactly the frozen anchor's type) give, at every universe:

* `detDrv`, `detTrace`: the **field-determined driver** (with its lifetime) and the **field-determined trace** of the
  word, Borel functions of the field;
* `ae_detDrv_eq` (**determination**): on every coupling of the word the determined lifetime is the lifetime and the
  determined driver is the driver before the lifetime, almost surely;
* `exists_coupling_detDrv` (**realization**): on every probability space carrying a GFF with the word's data, the
  determined driver and lifetime form an optional hull coupling with that field, whose generating trace is the
  determined trace;
* `isGFFWithBoundaryData_prop74Data_of_flowField`: a field whose angle-`θ` flow field has the two-seed data of
  Proposition 7.4's flow-line word is a GFF with the two-height data `prop74Data a b`;
* `seedSumL_flowLine`, `seedSumR_flowLine`: the seed sums of the flow-line word of `b` from `0`.

These are the universe-polymorphic forms of what PROVE-CONDDET's canonical flow code does at universe `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace Aux97G

open LQGMetric (DistOn TestOn)
open Exist.Staged Sec2.Assembly

/-- A generating trace may be replaced by a path that agrees with it on `[0, T]`. -/
theorem isGeneratingTrace_of_eqOn_le {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η η' : ℝ≥0 → ℂ} (h : IsGeneratingTrace w T η)
    (he : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → η' t = η t) : IsGeneratingTrace w T η' := by
  obtain ⟨h0, hc, hfill⟩ := h
  refine ⟨(he 0 (by simp)).trans h0, hc.congr fun t ht => he t ht, fun t ht => ?_⟩
  have himg : η' '' Icc 0 t = η '' Icc 0 t := by
    refine image_congr fun s hs => he s ?_
    exact (ENNReal.coe_le_coe.2 hs.2).trans ht.le
  rw [himg]
  exact hfill t ht

section Det

variable (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
  (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)

/-- **The field-determined driver** (with its lifetime) of the word `(xL, xR, ρL, ρR)` at the field `f`. -/
def detDrv (f : DistOn upperHalfPlaneOpens) : (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  drvOf (detCode (paramΦ h12p hκ nL nR) (((xL, xR), (ρL, ρR)), f))

theorem measurable_detDrv : Measurable (detDrv h12p hκ xL xR ρL ρR) :=
  measurable_drvOf.comp ((measurable_detCode (measurable_paramΦ h12p hκ nL nR)).comp
    (measurable_const.prodMk measurable_id))

/-- The field-determined driver is continuous before its lifetime. -/
theorem continuousOn_detDrv (f : DistOn upperHalfPlaneOpens) :
    ContinuousOn (detDrv h12p hκ xL xR ρL ρR f).1 {t | (t : ℝ≥0∞) < (detDrv h12p hκ xL xR ρL ρR f).2} :=
  (drvOf_regular _).1

/-- The field-determined driver starts at `0`. -/
theorem detDrv_zero (f : DistOn upperHalfPlaneOpens) : (detDrv h12p hκ xL xR ρL ρR f).1 0 = 0 :=
  (drvOf_regular _).2.1

/-- **The field-determined trace** of the word at the field `f`. -/
def detTrace (f : DistOn upperHalfPlaneOpens) : ℝ≥0 → ℂ :=
  (paramΦ h12p hκ nL nR (((xL, xR), (ρL, ρR)), f)).2

variable {xL xR ρL ρR}

/-- Theorem 1.2 (word-measurable form) for the chosen determination map. -/
theorem ae_paramΦ (hF : IsOrderedForceWord xL xR) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    ∀ᵐ ω ∂P, (paramΦ h12p hκ nL nR (((xL, xR), (ρL, ρR)), h ω)).1 = ζ ω ∧
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
        ∀ t : ℝ≥0, (paramΦ h12p hκ nL nR (((xL, xR), (ρL, ρR)), h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal :=
  (h12p κ hκ nL nR).choose_spec.2 xL xR ρL ρR hF hC

/-- **Determination of the driver**: on every coupling of the word, almost surely the field-determined lifetime is the
lifetime and the field-determined driver is the driver before the lifetime. -/
theorem ae_detDrv_eq (h13 : Exist.Theorem13Statement.{u}) (hF : IsOrderedForceWord xL xR) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    ∀ᵐ ω ∂P, (detDrv h12p hκ xL xR ρL ρR (h ω)).2 = ζ ω ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → (detDrv h12p hκ xL xR ρL ρR (h ω)).1 t = W t ω := by
  filter_upwards [ae_detCode_eq hκ hF h13 hC (ae_paramΦ h12p hκ hF hC)] with ω ⟨x₀, hx₀, hζx, hwx, hcode⟩
  have hd : detDrv h12p hκ xL xR ρL ρR (h ω) = (drvPath (dOf x₀), cζ x₀) := by
    unfold detDrv
    rw [hcode, drvOf_of_mem (dOf_mem_DSet hx₀)]
    rfl
  rw [hd]
  refine ⟨hζx, fun t ht => ?_⟩
  show drvPath (dOf x₀) t = W t ω
  rw [(drvPath_dOf_agree x₀).2 t (hζx ▸ ht)]
  exact (hwx t ht).1

/-- **Realization**: on every probability space carrying a GFF `h₀` with the data of the word, the field-determined
driver and lifetime form an optional hull coupling with `h₀`, and the field-determined trace is almost surely its
generating trace. -/
theorem exists_coupling_detDrv (h13 : Exist.Theorem13Statement.{u}) (hF : IsOrderedForceWord xL xR) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q] {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsGFFWithBoundaryData Q h₀ (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR)) :
    ∃ (𝓕 : Filtration ℝ≥0 mΩ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsOptionalHullCoupling κ xL xR ρL ρR Q 𝓕 (fun t ω => (detDrv h12p hκ xL xR ρL ρR (h₀ ω)).1 t) VL VR B
        (fun ω => (detDrv h12p hκ xL xR ρL ρR (h₀ ω)).2) h₀ ∧
      ∀ᵐ ω ∂Q, IsGeneratingTrace (fun t => (detDrv h12p hκ xL xR ρL ρR (h₀ ω)).1 t)
        (detDrv h12p hκ xL xR ρL ρR (h₀ ω)).2 (detTrace h12p hκ xL xR ρL ρR (h₀ ω)) := by
  obtain ⟨𝓕, VL, VR, B, hC⟩ := isOptionalHullCoupling_drv h12p h13 hκ hF hh₀
    ((measurable_detDrv h12p hκ xL xR ρL ρR).comp hh₀.1) (ae_of_all _ fun _ => rfl)
  refine ⟨𝓕, VL, VR, B, hC, ?_⟩
  filter_upwards [h13 hκ hF hC.1, ae_paramΦ h12p hκ hF hC] with ω h13ω hΦω
  obtain ⟨-, η₀, hη₀, -⟩ := h13ω
  refine isGeneratingTrace_of_eqOn_le hη₀ fun t ht => ?_
  have ht' : (t : ℝ≥0∞) ≤ ((detDrv h12p hκ xL xR ρL ρR ∘ h₀) ω).2 := ht
  show (paramΦ h12p hκ nL nR (((xL, xR), (ρL, ρR)), h₀ ω)).2 t = η₀ t
  rw [hΦω.2 η₀ hη₀ t, min_eq_left ht', ENNReal.toNNReal_coe]

end Det

/-! ### The two-height data of Proposition 7.4 from the two-seed data -/

section Prop74

variable {κ : ℝ}

/-- The two-seed force data with the weights of Proposition 7.4's flow-line word at angle `θ` is
`prop74Data a b + θχ` off `0`. -/
theorem forceBoundaryData_twoSeed_eq (hκ : 0 < κ) (a b θ : ℝ) {x : ℝ} (hx : x ≠ 0) :
    forceBoundaryData κ (fun _ : Fin 1 => (a - θ * QuantumZipper.chiC κ) / sleLambda κ - 1)
        (fun _ : Fin 1 => (b + θ * QuantumZipper.chiC κ) / sleLambda κ - 1) LP.twoSeedXL LP.twoSeedXR x =
      prop74Data a b x + θ * QuantumZipper.chiC κ := by
  have hlam : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  have hlam' : Real.pi / Real.sqrt κ = sleLambda κ := rfl
  unfold forceBoundaryData prop74Data
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have hf : (Finset.univ.filter fun i : Fin 1 => x < LP.twoSeedXL i) = Finset.univ :=
      Finset.filter_true_of_mem fun i _ => by simp only [LP.twoSeedXL]; exact hlt
    simp only [hlt, ↓reduceIte]
    rw [hf, Fin.sum_univ_one, hlam']
    field_simp
    ring
  · have hf : (Finset.univ.filter fun i : Fin 1 => LP.twoSeedXR i ≤ x) = Finset.univ :=
      Finset.filter_true_of_mem fun i _ => by simp only [LP.twoSeedXR]; exact hgt.le
    have hn : ¬ x < 0 := not_lt.2 hgt.le
    simp only [hn, ↓reduceIte]
    rw [hf, Fin.sum_univ_one, hlam']
    field_simp
    ring

theorem forceJumpSet_twoSeed : forceJumpSet LP.twoSeedXL LP.twoSeedXR = {0} := by
  ext y
  simp only [forceJumpSet, LP.twoSeedXL, LP.twoSeedXR, mem_insert_iff, mem_union, mem_range, exists_const,
    or_self, mem_singleton_iff]
  constructor
  · rintro (h | h) <;> exact h.symm ▸ rfl
  · intro h
    exact Or.inl h

/-- `flowField 0 c T` is `T + c ∫ ·`. -/
theorem flowField_zero_apply (c : ℝ) (T : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) :
    Exist.flowField 0 c T φ = T φ + c * ∫ w, φ w := by
  rw [Exist.flowField_apply]
  congr 2
  ext z
  rw [Exist.pushTest_shiftChart_apply, Complex.ofReal_zero, sub_zero]

/-- **The two-height data of Proposition 7.4.** If the angle-`θ` flow field `X(·) + θχ` of `X` has the two-seed data
with the weights of the flow-line word of `prop74Data a b` (`(a − θχ)/λ − 1` and `(b + θχ)/λ − 1`), then `X` is a GFF
with the data `prop74Data a b` (jump at `0`). -/
theorem isGFFWithBoundaryData_prop74Data_of_flowField (hκ : 0 < κ) {a b θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hh₀ : IsGFFWithBoundaryData Q (fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (X ω))
      (forceBoundaryData κ (fun _ : Fin 1 => (a - θ * QuantumZipper.chiC κ) / sleLambda κ - 1)
        (fun _ : Fin 1 => (b + θ * QuantumZipper.chiC κ) / sleLambda κ - 1) LP.twoSeedXL LP.twoSeedXR)
      (forceJumpSet LP.twoSeedXL LP.twoSeedXR)) :
    IsGFFWithBoundaryData Q X (prop74Data a b) ({0} : Set ℝ) := by
  refine ⟨hXm, fun u₀ hu₀ => ?_⟩
  set c : ℝ := θ * QuantumZipper.chiC κ with hc
  have hu₁ : IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => (a - c) / sleLambda κ - 1)
      (fun _ : Fin 1 => (b + c) / sleLambda κ - 1) LP.twoSeedXL LP.twoSeedXR)
      (forceJumpSet LP.twoSeedXL LP.twoSeedXR) (fun z => u₀ z + c) := by
    obtain ⟨hharm, ⟨C, hC⟩, hlim⟩ := hu₀
    refine ⟨fun z hz => (hharm z hz).add (InnerProductSpace.harmonicAt_const c), ⟨|C| + |c|, fun z hz => ?_⟩,
      fun x hx => ?_⟩
    · exact (abs_add_le _ _).trans (add_le_add ((hC z hz).trans (le_abs_self C)) le_rfl)
    · rw [forceJumpSet_twoSeed] at hx
      have hx0 : x ≠ 0 := hx
      rw [forceBoundaryData_twoSeed_eq hκ a b θ hx0]
      exact (hlim x (by simpa using hx0)).add_const c
  have hu₀c : ContinuousOn u₀ QuantumZipper.H := LocalExt.continuousOn_of_isBoundedHarmonicExtension hu₀
  have key := hh₀.2 _ hu₁
  convert key using 2 with φ
  funext ω
  have hi : Integrable (fun z => u₀ z * φ z) :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn hu₀c φ φ.tsupport_subset
  have hφi : Integrable (fun z => φ z) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have e : (∫ z, (u₀ z + c) * φ z) = (∫ z, u₀ z * φ z) + c * ∫ z, φ z := by
    rw [← integral_const_mul, ← integral_add hi (hφi.const_mul c)]
    congr 1
    funext z
    ring
  show X ω φ - ∫ z, u₀ z * φ z = Exist.flowField 0 c (X ω) φ - ∫ z, (u₀ z + c) * φ z
  rw [flowField_zero_apply, e]
  ring

end Prop74

/-- **A GFF with the two-height data exists on every space carrying a GFF with piecewise-constant data**: `h` plus
the deterministic difference of the two bounded harmonic extensions. -/
theorem exists_isGFFWithBoundaryData_prop74Data_of {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J) (a c : ℝ) :
    ∃ X : Ω → DistOn upperHalfPlaneOpens, IsGFFWithBoundaryData P X (prop74Data a c) ({0} : Set ℝ) := by
  obtain ⟨ub, hub, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨up, hup, hupu⟩ :=
    PiecewiseConstant.existsUnique_isBoundedHarmonicExtension (isPiecewiseConstant_prop74Data a c)
  rw [Finset.coe_singleton] at hup hupu
  have hubc : ContinuousOn ub QuantumZipper.H := LocalExt.continuousOn_of_isBoundedHarmonicExtension hub
  have hupc : ContinuousOn up QuantumZipper.H := LocalExt.continuousOn_of_isBoundedHarmonicExtension hup
  have hfc : ContinuousOn (fun z => up z - ub z) QuantumZipper.H := hupc.sub hubc
  refine ⟨fun ω => h ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (fun z => up z - ub z),
    (Coupling.measurable_add_distOnConst _).comp hh.1, fun u₀ hu₀ => ?_⟩
  have heq : EqOn u₀ up QuantumZipper.H := hupu u₀ hu₀
  have key := hh.2 ub hub
  convert key using 2 with φ
  funext ω
  have hi : ∀ v : ℂ → ℝ, ContinuousOn v QuantumZipper.H → Integrable (fun z => v z * φ z) := fun v hv =>
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn hv φ φ.tsupport_subset
  have e1 : (SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (fun z => up z - ub z)) φ =
      (∫ z, up z * φ z) - ∫ z, ub z * φ z := by
    rw [SupercriticalConformalCovariance.GM24.smoothDist_apply hfc, ← integral_sub (hi up hupc) (hi ub hubc)]
    congr 1
    funext z
    ring
  have e2 : (∫ z, u₀ z * φ z) = ∫ z, up z * φ z := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ QuantumZipper.H
    · simp only [heq hz]
    · have : φ z = 0 := φ.zero_on_compl (show z ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hz)
      simp only [this, mul_zero]
  show h ω φ + (SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (fun z => up z - ub z)) φ -
      ∫ z, u₀ z * φ z = h ω φ - ∫ z, ub z * φ z
  rw [e1, e2]
  ring

/-! ### The seed sums of the flow-line word -/

/-- The left seed sum of the flow-line word of `b` from `0` at angle `θ`. -/
theorem seedSumL_flowLine (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ) :
    LocalExt.seedSumL (flowLineXL b J 0) (flowLineRhoL κ b J 0 θ) =
      -(PiecewiseConstantBoundaryData.leftLim b 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 := by
  rw [LocalExt.seedSumL_eq]
  exact sum_filter_flowLineXL_eq_zero_seed κ b J θ

/-- The right seed sum of the flow-line word of `b` from `0` at angle `θ`. -/
theorem seedSumR_flowLine (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ) :
    LocalExt.seedSumR (flowLineXR b J 0) (flowLineRhoR κ b J 0 θ) =
      (PiecewiseConstantBoundaryData.rightLim b 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 := by
  rw [LocalExt.seedSumR_eq]
  exact sum_filter_flowLineXR_eq_zero_seed κ b J θ

end Aux97G

end Sec7

end InteractingSLE
