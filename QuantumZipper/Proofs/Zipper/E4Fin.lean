import QuantumZipper.Proofs.Zipper.E4FinMain
import QuantumZipper.Proofs.Zipper.Thm13AssemblyStmt

/-!
# E4 (field at collision), all measurable test functions: `E4Stmt` from `hL3i`

`handoff/E4.md`, item E4. From the indicator case `e4good_S3` the standard machine
(`goodEq_induction`) extends E4 (with the a.e.-measurability) first to every measurable `Ψ`
(for `Φ = 1_C`), then to every measurable `Φ` (`e4good_all`). The case `δ ≤ 0` is trivial since
`ν_ω{0} = 0` a.s. (`E1.ae_nuPalm_singleton_zero`). Result: `e4_of_L3i : L3iStmt → E4Stmt`, where
`L3iStmt` is the interior law continuity `hL3i` (still open, see `handoff/E4.md`).

Standard measure theory (Kallenberg, *Foundations of Modern Probability*, 2nd ed., Lemma 1.11,
Thm 1.1); own bookkeeping. Part of the proof of Sheffield, arXiv:1012.4797, Lemma 5.6
(pp. 66–68).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E4Grid

open B2 E1 CoordsFull PalmNorm

section Forms

variable {Ω : Type*} (A : Ω → Set ℝ)

/-! ### Linearity of the integrands in `Ψ` -/

variable (q : Ω → ℝ → CfgE) (Z : Ω → ℝ → ℝ≥0∞)

theorem indPsi_const (c : ℝ≥0∞) (s : Set CfgE) :
    (fun ω x => (A ω).indicator (fun x => s.indicator (fun _ => c) (q ω x) * Z ω x) x) =
      fun ω x => c * (A ω).indicator (fun x => s.indicator 1 (q ω x) * Z ω x) x := by
  funext ω x
  by_cases hx : x ∈ A ω <;> by_cases hq : q ω x ∈ s <;> simp [hx, hq]

theorem indPsi_add (f g : CfgE → ℝ≥0∞) :
    (fun ω x => (A ω).indicator (fun x => (f + g) (q ω x) * Z ω x) x) =
      fun ω x => (A ω).indicator (fun x => f (q ω x) * Z ω x) x +
        (A ω).indicator (fun x => g (q ω x) * Z ω x) x := by
  funext ω x
  by_cases hx : x ∈ A ω <;> simp [hx, add_mul]

theorem indPsi_iSup (f : ℕ → CfgE → ℝ≥0∞) :
    (fun ω x => (A ω).indicator (fun x => (fun y => ⨆ n, f n y) (q ω x) * Z ω x) x) =
      fun ω x => ⨆ n, (A ω).indicator (fun x => f n (q ω x) * Z ω x) x := by
  funext ω x
  by_cases hx : x ∈ A ω <;> simp [hx, ENNReal.iSup_mul]

theorem indPsi_mono {f g : CfgE → ℝ≥0∞} (hfg : f ≤ g) (ω : Ω) (x : ℝ) :
    (A ω).indicator (fun x => f (q ω x) * Z ω x) x ≤
      (A ω).indicator (fun x => g (q ω x) * Z ω x) x := by
  by_cases hx : x ∈ A ω
  · simp only [indicator_of_mem hx]
    gcongr
    exact hfg _
  · simp [hx]

/-! ### Linearity of the left integrand in `Φ` -/

variable (W : Ω → ℝ → ℝ≥0∞) (φ : Ω → ℝ → ℕ → ℝ)

theorem indPhiL_const (c : ℝ≥0∞) (s : Set (ℕ → ℝ)) :
    (fun ω x => (A ω).indicator (fun x => W ω x * s.indicator (fun _ => c) (φ ω x)) x) =
      fun ω x => c * (A ω).indicator (fun x => W ω x * s.indicator 1 (φ ω x)) x := by
  funext ω x
  by_cases hx : x ∈ A ω <;> by_cases hq : φ ω x ∈ s <;> simp [hx, hq, mul_comm]

theorem indPhiL_add (f g : (ℕ → ℝ) → ℝ≥0∞) :
    (fun ω x => (A ω).indicator (fun x => W ω x * (f + g) (φ ω x)) x) =
      fun ω x => (A ω).indicator (fun x => W ω x * f (φ ω x)) x +
        (A ω).indicator (fun x => W ω x * g (φ ω x)) x := by
  funext ω x
  by_cases hx : x ∈ A ω <;> simp [hx, mul_add]

theorem indPhiL_iSup (f : ℕ → (ℕ → ℝ) → ℝ≥0∞) :
    (fun ω x => (A ω).indicator (fun x => W ω x * (fun y => ⨆ n, f n y) (φ ω x)) x) =
      fun ω x => ⨆ n, (A ω).indicator (fun x => W ω x * f n (φ ω x)) x := by
  funext ω x
  by_cases hx : x ∈ A ω <;> simp [hx, ENNReal.mul_iSup]

theorem indPhiL_mono {f g : (ℕ → ℝ) → ℝ≥0∞} (hfg : f ≤ g) (ω : Ω) (x : ℝ) :
    (A ω).indicator (fun x => W ω x * f (φ ω x)) x ≤
      (A ω).indicator (fun x => W ω x * g (φ ω x)) x := by
  by_cases hx : x ∈ A ω
  · simp only [indicator_of_mem hx]
    gcongr
    exact hfg _
  · simp [hx]

/-! ### Linearity of the right integrand in `Φ` (measurable `Φ`) -/

variable {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') (r : Ω → ℝ → Ω' → ℕ → ℝ)

theorem indPhiR_const (hr : ∀ ω x, Measurable (r ω x)) (c : ℝ≥0∞) {s : Set (ℕ → ℝ)}
    (hs : MeasurableSet s) :
    (fun ω x => (A ω).indicator (fun x => W ω x *
        ∫⁻ ω', s.indicator (fun _ => c) (r ω x ω') ∂P') x) =
      fun ω x => c * (A ω).indicator (fun x => W ω x *
        ∫⁻ ω', s.indicator 1 (r ω x ω') ∂P') x := by
  funext ω x
  have h : ∀ y : ℕ → ℝ, s.indicator (fun _ => c) y = c * s.indicator 1 y := fun y => by
    by_cases hy : y ∈ s <;> simp [hy]
  simp_rw [h]
  by_cases hx : x ∈ A ω
  · simp only [indicator_of_mem hx]
    rw [show ∫⁻ ω', c * s.indicator 1 (r ω x ω') ∂P' = c * ∫⁻ ω', s.indicator 1 (r ω x ω') ∂P'
      from lintegral_const_mul c ((measurable_one.indicator hs).comp (hr ω x)), mul_left_comm]
  · simp [hx]

theorem indPhiR_add (hr : ∀ ω x, Measurable (r ω x)) {f g : (ℕ → ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    (fun ω x => (A ω).indicator (fun x => W ω x * ∫⁻ ω', (f + g) (r ω x ω') ∂P') x) =
      fun ω x => (A ω).indicator (fun x => W ω x * ∫⁻ ω', f (r ω x ω') ∂P') x +
        (A ω).indicator (fun x => W ω x * ∫⁻ ω', g (r ω x ω') ∂P') x := by
  funext ω x
  by_cases hx : x ∈ A ω
  · simp only [indicator_of_mem hx, Pi.add_apply]
    rw [← mul_add]
    congr 1
    exact lintegral_add_left (hf.comp (hr ω x)) _
  · simp [hx]

theorem indPhiR_iSup (hr : ∀ ω x, Measurable (r ω x)) {f : ℕ → (ℕ → ℝ) → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) :
    (fun ω x => (A ω).indicator (fun x => W ω x *
        ∫⁻ ω', (fun y => ⨆ n, f n y) (r ω x ω') ∂P') x) =
      fun ω x => ⨆ n, (A ω).indicator (fun x => W ω x * ∫⁻ ω', f n (r ω x ω') ∂P') x := by
  funext ω x
  by_cases hx : x ∈ A ω
  · simp only [indicator_of_mem hx]
    rw [← ENNReal.mul_iSup]
    congr 1
    exact lintegral_iSup (fun n => (hf n).comp (hr ω x)) (fun a b hab ω' => hmono hab _)
  · simp [hx]

theorem indPhiR_mono {f g : (ℕ → ℝ) → ℝ≥0∞} (hfg : f ≤ g) (ω : Ω) (x : ℝ) :
    (A ω).indicator (fun x => W ω x * ∫⁻ ω', f (r ω x ω') ∂P') x ≤
      (A ω).indicator (fun x => W ω x * ∫⁻ ω', g (r ω x ω') ∂P') x := by
  by_cases hx : x ∈ A ω
  · simp only [indicator_of_mem hx]
    gcongr
    exact hfg _
  · simp [hx]

end Forms

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X' : Ω' → FieldSample}

/-- **E4 with the a.e.-measurability, all measurable `Ψ, Φ`, `δ > 0`**, given `hL3i`. -/
theorem e4good_all (hS : E5.Setup κ T P B X ϖ) (hX' : IsFreeGFFModConstH X' P')
    (hL : L3iHyp P κ T B ϖ P' X') {δ : ℝ} (hδ : 0 < δ) (ψ : CfgE → ℝ≥0∞) (hψ : Measurable ψ)
    (Φ : (ℕ → ℝ) → ℝ≥0∞) (hΦ : Measurable Φ) : E4Good P κ T B X ϖ P' X' δ ψ Φ := by
  set A : Ω → Set ℝ := fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T} with hA
  set q : Ω → ℝ → CfgE := fun ω x =>
    (x, (Vstop κ T (realHitTime (Vr κ T B ω) x).toReal B ω, W0p κ T B ω)) with hq
  set φ : Ω → ℝ → ℕ → ℝ := fun ω x => coordsFull (addConst
    (Yf κ T (realHitTime (Vr κ T B ω) x).toReal B X ω) (-(mReg κ T B X ϖ ω))) with hφ
  set r : Ω → ℝ → Ω' → ℕ → ℝ := fun ω x ω' => coordsFull (targetColl κ (Vr κ T B ω)
    (realHitTime (Vr κ T B ω) x).toReal ϖ (X' ω')) with hr
  have hrm : ∀ ω x, Measurable (r ω x) := fun ω x =>
    measurable_coordsFull_targetColl hX' κ _ _ ϖ
  -- S4: all measurable `ψ`, `Φ = 1_C`
  have h4 : ∀ C : Set (ℕ → ℝ), MeasurableSet C → ∀ ψ : CfgE → ℝ≥0∞, Measurable ψ →
      E4Good P κ T B X ϖ P' X' δ ψ (C.indicator 1) := fun C hC =>
    goodEq_induction (β := CfgE)
      (fun ψ ω x => (A ω).indicator (fun x => ψ (q ω x) * C.indicator 1 (φ ω x)) x)
      (fun ψ ω x => (A ω).indicator (fun x => ψ (q ω x) *
        ∫⁻ ω', C.indicator 1 (r ω x ω') ∂P') x)
      (fun c s _ => indPsi_const A q _ c s) (fun c s _ => indPsi_const A q _ c s)
      (fun f g _ _ => indPsi_add A q _ f g) (fun f g _ _ => indPsi_add A q _ f g)
      (fun f _ _ => indPsi_iSup A q _ f) (fun f _ _ => indPsi_iSup A q _ f)
      (fun f g _ _ hfg => indPsi_mono A q _ hfg) (fun f g _ _ hfg => indPsi_mono A q _ hfg)
      (fun s hs => e4good_S3 hS hX' hL hδ s hs C hC)
  -- S5: all measurable `Φ`
  exact goodEq_induction (β := ℕ → ℝ)
    (fun Φ ω x => (A ω).indicator (fun x => ψ (q ω x) * Φ (φ ω x)) x)
    (fun Φ ω x => (A ω).indicator (fun x => ψ (q ω x) * ∫⁻ ω', Φ (r ω x ω') ∂P') x)
    (fun c s _ => indPhiL_const A _ φ c s) (fun c s hs => indPhiR_const A _ P' r hrm c hs)
    (fun f g _ _ => indPhiL_add A _ φ f g) (fun f g hf _ => indPhiR_add A _ P' r hrm hf)
    (fun f _ _ => indPhiL_iSup A _ φ f) (fun f hf hm => indPhiR_iSup A _ P' r hrm hf hm)
    (fun f g _ _ hfg => indPhiL_mono A _ φ hfg) (fun f g _ _ hfg => indPhiR_mono A _ P' r hfg)
    (fun s hs => h4 s hs ψ hψ) Φ hΦ

/-- The interior law continuity `hL3i` (open; `handoff/E4.md`), for every setup. -/
def L3iStmt : Prop :=
  ∀ (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X' : Ω' → FieldSample),
    E5.Setup κ T P B X ϖ → IsFreeGFFModConstH X' P' → L3iHyp P κ T B ϖ P' X'

/-- **E4** (`Thm13Asm.E4Stmt`), conditional on the interior law continuity `L3iStmt`. -/
theorem e4_of_L3i (hL3 : L3iStmt) : Thm13Asm.E4Stmt := by
  intro κ T Ω _ P _ B X ϖ Ω' _ P' _ X' _ hS hX' δ Ψ Φ hΨ hΦ
  dsimp only
  rcases le_or_gt δ 0 with hδ | hδ
  · obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := hS
    have h0 : ∀ᵐ ω ∂P, nuPalm κ T B X ϖ ω (Icc (-δ) 0) = 0 := by
      filter_upwards [ae_nuPalm_singleton_zero RevCouplingReg.revCouplingBoundaryMeasureRegular
        hκ hκ4 hT hB hX hind ϖ] with ω h
      refine measure_mono_null (fun y hy => ?_) h
      exact mem_singleton_iff.2 (le_antisymm hy.2 (by linarith [hy.1]))
    have hz : ∀ F : Ω → ℝ → ℝ≥0∞,
        ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, F ω x ∂nuPalm κ T B X ϖ ω ∂P = 0 := fun F => by
      rw [lintegral_congr_ae (h0.mono fun ω h => setLIntegral_measure_zero _ (F ω) h),
        lintegral_zero]
    exact (hz _).trans (hz _).symm
  · exact (e4good_all hS hX' (hL3 κ T P B X ϖ P' X' hS hX') hδ (Function.uncurry Ψ) hΨ
      Φ hΦ).1

end E4Grid
end QuantumZipper
