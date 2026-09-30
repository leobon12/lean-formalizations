import QuantumZipper.Proofs.Thm11.AddendumLeftLimit2Path

/-!
# THM11-AD3: orthogonality of the frozen fields at two levels

For levels `0 < δ' ≤ δ ≤ Im a`, the frozen field at level `δ` is the frozen field at level `δ'`
sampled at the freezing time of level `δ` (`AddendumLeftLimit2Path`). Optional sampling
(`ItoLite.integral_mul_stoppedValue_eq_of_le`) then gives `E[X_δ X_δ'] = E[X_δ²]`, i.e. the
martingale increments are orthogonal: `E[(X_δ' − X_δ)²] = E[X_δ'²] − E[X_δ²]`.

Source: the standard orthogonality of martingale increments (Revuz–Yor, *Continuous
Martingales and Brownian Motion*, Ch. II §3, optional stopping); the bookkeeping here is own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm11Add

open FrozenMart

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- `E[X_δ X_δ'] = E[X_δ²]` for the frozen fields at levels `δ' ≤ δ` (value at time `T`). -/
theorem integral_mul_frozenField_eq (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) {κ δ δ' : ℝ} (hκ : 0 < κ) (hδ' : 0 < δ') (hδδ' : δ' ≤ δ)
    {a : ℂ} (hδa : δ ≤ a.im) (T : ℝ≥0) :
    ∫ ω, frozenField κ δ δ T B a T ω * frozenField κ δ' δ' T B a T ω ∂P =
      ∫ ω, frozenField κ δ δ T B a T ω * frozenField κ δ δ T B a T ω ∂P := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set 𝓕 := NonSwallow.bmFilt hBm
  have hBad := NonSwallow.bmFilt_adapted hBm
  have hpast := NonSwallow.bmFilt_le_past hBm
  have hδ0 : 0 < δ := hδ'.trans_le hδδ'
  have hδ'a : δ' ≤ a.im := hδδ'.trans hδa
  set M := frozenField κ δ' δ' T B a with hM_def
  have hM : Martingale M 𝓕 P :=
    frozenField_martingale hB hBc 𝓕 hBad hpast hκ hδ' le_rfl hδ'a T
  have hMc : ∀ ω, Continuous (M · ω) := continuous_frozenField hBc hδ' le_rfl hδ'a T
  have hMb : ∀ t ω, |M t ω| ≤ fzBound κ δ' T := fun t ω =>
    abs_frozenField_le hBc hδ' hδ'a T t ω
  have hUad : Adapted 𝓕 (fzU κ δ' B a) := fun t =>
    Dynkin.measurable_of_integralEq 𝓕 hBad hBc (lipschitzWith_fzDrift hδ')
      (norm_fzDrift_le hδ') (fzU_eq hBc hδ' a) (continuous_fzU hBc hδ' a) t
  set σ : Ω → WithTop ℝ≥0 := fun ω =>
    ((hittingBtwn (fzU κ δ' B a) {x : ℂ × ℝ | x.1.im ≤ δ} 0 T ω : ℝ≥0) : WithTop ℝ≥0)
  have hσ : IsStoppingTime 𝓕 σ :=
    ItoLite.isStoppingTime_hittingBtwn_of_isClosed hUad (continuous_fzU hBc hδ' a)
      (isClosed_fzCl δ) T
  have hle : ∀ ω, σ ω ≤ T := fun ω => WithTop.coe_le_coe.2 (hittingBtwn_le ω)
  have hprog := hM.stronglyAdapted.isStronglyProgressive_of_continuous hMc
  have hYm : Measurable[hσ.measurableSpace] (stoppedValue M σ) :=
    measurable_stoppedValue hprog hσ
  have key := ItoLite.integral_mul_stoppedValue_eq_of_le hM hMc hMb hσ hle hYm
    (fun ω => hMb _ ω)
  have hid : ∀ ω, stoppedValue M σ ω = frozenField κ δ δ T B a T ω := by
    intro ω
    have hs : stoppedValue M σ ω = M (frozenTime κ δ' δ T B a ω) ω := by
      simp only [stoppedValue, σ, hittingBtwn_fzU]; rfl
    have hanti : frozenTime κ δ' δ T B a ω ≤ frozenTime κ δ' δ' T B a ω :=
      hittingBtwn_apply_anti (fzZ κ δ' B a) 0 T ω (fun z (hz : z.im ≤ δ') => hz.trans hδδ')
    rw [hs, hM_def, frozenField_eq_fieldAt hBc hδ' le_rfl hδ'a, min_eq_left hanti,
      frozenField_eq_fieldAt hBc hδ0 le_rfl hδa, min_eq_right (hittingBtwn_le ω),
      frozenTime_congr hBc hδ0 le_rfl hδ' hδδ' hδa T ω]
  simp only [hid] at key
  rw [key]

/-- Orthogonal increments: `E[(X_δ' − X_δ)²] = E[X_δ'²] − E[X_δ²]`. -/
theorem integral_sq_sub_frozenField (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) {κ δ δ' : ℝ} (hκ : 0 < κ) (hδ' : 0 < δ') (hδδ' : δ' ≤ δ)
    {a : ℂ} (hδa : δ ≤ a.im) (T : ℝ≥0) :
    ∫ ω, (frozenField κ δ' δ' T B a T ω - frozenField κ δ δ T B a T ω) ^ 2 ∂P =
      ∫ ω, frozenField κ δ' δ' T B a T ω ^ 2 ∂P - ∫ ω, frozenField κ δ δ T B a T ω ^ 2 ∂P := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set 𝓕 := NonSwallow.bmFilt hBm
  have hBad := NonSwallow.bmFilt_adapted hBm
  have hpast := NonSwallow.bmFilt_le_past hBm
  have hδ0 : 0 < δ := hδ'.trans_le hδδ'
  have hδ'a : δ' ≤ a.im := hδδ'.trans hδa
  set X := frozenField κ δ δ T B a T
  set Y := frozenField κ δ' δ' T B a T
  have hXm : StronglyMeasurable X :=
    ((frozenField_martingale hB hBc 𝓕 hBad hpast hκ hδ0 le_rfl hδa T).stronglyMeasurable
      T).mono (𝓕.le T)
  have hYm : StronglyMeasurable Y :=
    ((frozenField_martingale hB hBc 𝓕 hBad hpast hκ hδ' le_rfl hδ'a T).stronglyMeasurable
      T).mono (𝓕.le T)
  have hXb : ∀ ω, |X ω| ≤ fzBound κ δ T := fun ω => abs_frozenField_le hBc hδ0 hδa T T ω
  have hYb : ∀ ω, |Y ω| ≤ fzBound κ δ' T := fun ω => abs_frozenField_le hBc hδ' hδ'a T T ω
  have iXX : Integrable (fun ω => X ω * X ω) P :=
    ItoLite.integrable_of_bound_abs (hXm.mul hXm) fun ω => ItoLite.abs_mul_le_of_le (hXb ω) (hXb ω)
  have iXY : Integrable (fun ω => X ω * Y ω) P :=
    ItoLite.integrable_of_bound_abs (hXm.mul hYm) fun ω => ItoLite.abs_mul_le_of_le (hXb ω) (hYb ω)
  have iYY : Integrable (fun ω => Y ω * Y ω) P :=
    ItoLite.integrable_of_bound_abs (hYm.mul hYm) fun ω => ItoLite.abs_mul_le_of_le (hYb ω) (hYb ω)
  have hk := integral_mul_frozenField_eq (P := P) hB hBm hBc hκ hδ' hδδ' hδa T
  have e : (fun ω => (Y ω - X ω) ^ 2) = fun ω => Y ω * Y ω - 2 * (X ω * Y ω) + X ω * X ω := by
    funext ω; ring
  have e2 : ∀ Z : Ω → ℝ, (fun ω => Z ω ^ 2) = fun ω => Z ω * Z ω := fun Z => by funext ω; ring
  have i1 : Integrable (fun ω => Y ω * Y ω - 2 * (X ω * Y ω)) P := iYY.sub (iXY.const_mul 2)
  rw [e, integral_add (f := fun ω => Y ω * Y ω - 2 * (X ω * Y ω)) i1 iXX,
    integral_sub (f := fun ω => Y ω * Y ω) iYY (iXY.const_mul 2), integral_const_mul, e2 X, e2 Y]
  rw [show (∫ ω, X ω * Y ω ∂P) = ∫ ω, X ω * X ω ∂P from hk]
  ring

end Thm11Add
end QuantumZipper
