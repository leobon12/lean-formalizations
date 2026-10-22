import HigherDimLQGContinuity.ConvTransfer.LowerModel
import HigherDimLQGContinuity.ConvTransfer.LawMoments
import HigherDimLQGContinuity.Core.Interfaces

/-! Moment calculus for inverse crossings. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric.DGZ
open HigherDimLFPP (Rd WN)

/-- Median comparison and a deterministic crossing lower bound give a ratio
inverse bound. All scalar manipulations are kept in `ℝ` before coercion. -/
theorem convCross_ratio_inverse_bound
    {r m a C M t : ℝ} {D : ℝ≥0∞}
    (hr : 0 < r) (hm : 0 < m) (ha : 0 < a)
    (hC : 0 < C) (hM : 0 < M)
    (hmed : a ≤ C * r * m)
    (hD : ENNReal.ofReal (r * Real.exp (-t) * M) ≤ D) :
    ((ENNReal.ofReal a)⁻¹ * D)⁻¹ ≤
      ENNReal.ofReal (C * Real.exp t) *
        (ENNReal.ofReal (M / m))⁻¹ := by
  have he : 0 < Real.exp t := Real.exp_pos _
  have hen : 0 < Real.exp (-t) := Real.exp_pos _
  have hcm : 0 < C * r * m := by positivity
  have hZ : 0 < M / m := div_pos hM hm
  have hnum : 0 ≤ r * Real.exp (-t) * M := by positivity
  have hreal : (M / m) / (C * Real.exp t) ≤
      (r * Real.exp (-t) * M) / a := by
    have heq : (M / m) / (C * Real.exp t) =
        (r * Real.exp (-t) * M) / (C * r * m) := by
      rw [Real.exp_neg]
      field_simp
    rw [heq]
    apply (div_le_div_iff₀ hcm ha).2
    nlinarith [mul_nonneg hnum (sub_nonneg.2 hmed)]
  have hnorm : ENNReal.ofReal ((M / m) / (C * Real.exp t)) ≤
      (ENNReal.ofReal a)⁻¹ * D := by
    calc
      _ ≤ ENNReal.ofReal ((r * Real.exp (-t) * M) / a) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = (ENNReal.ofReal a)⁻¹ *
          ENNReal.ofReal (r * Real.exp (-t) * M) := by
            rw [ENNReal.ofReal_div_of_pos ha, div_eq_mul_inv]
            ac_rfl
      _ ≤ (ENNReal.ofReal a)⁻¹ * D := by gcongr
  have hleft : 0 < (M / m) / (C * Real.exp t) :=
    div_pos hZ (mul_pos hC he)
  calc
    ((ENNReal.ofReal a)⁻¹ * D)⁻¹ ≤
        (ENNReal.ofReal ((M / m) / (C * Real.exp t)))⁻¹ :=
      ENNReal.inv_le_inv' hnorm
    _ = ENNReal.ofReal (((M / m) / (C * Real.exp t))⁻¹) :=
      (ENNReal.ofReal_inv_of_pos hleft).symm
    _ = ENNReal.ofReal ((C * Real.exp t) * (M / m)⁻¹) := by
      congr 1
      field_simp
    _ = ENNReal.ofReal (C * Real.exp t) *
          (ENNReal.ofReal (M / m))⁻¹ := by
      rw [ENNReal.ofReal_mul (mul_pos hC he).le,
        ENNReal.ofReal_inv_of_pos hZ]

/-- A two-factor estimate in `ENNReal`, with no independence assumption. -/
theorem convCross_lintegral_mul_le_sq_sum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ≥0∞}
    (hX : AEMeasurable X P) :
    ∫⁻ ω, X ω * Y ω ∂P ≤
      (∫⁻ ω, (X ω) ^ 2 ∂P) + ∫⁻ ω, (Y ω) ^ 2 ∂P := by
  have hm : AEMeasurable (fun ω => (X ω) ^ 2) P := hX.pow_const 2
  calc
    ∫⁻ ω, X ω * Y ω ∂P ≤
        ∫⁻ ω, (X ω) ^ 2 + (Y ω) ^ 2 ∂P := by
          apply lintegral_mono
          intro ω
          rcases le_total (X ω) (Y ω) with h | h
          · calc
              X ω * Y ω ≤ Y ω * Y ω := by
                simpa only [mul_comm] using (mul_le_mul_left h (Y ω))
              _ = (Y ω) ^ 2 := by ring
              _ ≤ (X ω) ^ 2 + (Y ω) ^ 2 := le_add_of_nonneg_left bot_le
          · calc
              X ω * Y ω ≤ X ω * X ω := mul_le_mul_right h (X ω)
              _ = (X ω) ^ 2 := by ring
              _ ≤ (X ω) ^ 2 + (Y ω) ^ 2 := le_add_of_nonneg_right bot_le
    _ = (∫⁻ ω, (X ω) ^ 2 ∂P) + ∫⁻ ω, (Y ω) ^ 2 ∂P :=
      lintegral_add_left' hm _

/-- Holder's two-factor step for a nonnegative extended ratio. -/
theorem convCross_lintegral_product_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z X Y : Ω → ℝ≥0∞} {q C BX BY : ℝ}
    (hq : 0 < q) (hC : 0 ≤ C) (hBX : 0 ≤ BX) (hBY : 0 ≤ BY)
    (hX : AEMeasurable X P)
    (hpoint : ∀ᵐ ω ∂P, Z ω ≤ ENNReal.ofReal C * X ω * Y ω)
    (hXmom : ∫⁻ ω, X ω ^ (2 * q) ∂P ≤ ENNReal.ofReal BX)
    (hYmom : ∫⁻ ω, Y ω ^ (2 * q) ∂P ≤ ENNReal.ofReal BY) :
    ∫⁻ ω, Z ω ^ q ∂P ≤ ENNReal.ofReal (C ^ q * (BX + BY)) := by
  have h2q : 2 * q = q * 2 := by ring
  have hXq : AEMeasurable (fun ω => X ω ^ q) P := hX.pow_const q
  have hstep : ∀ᵐ ω ∂P,
      Z ω ^ q ≤ ENNReal.ofReal (C ^ q) * (X ω ^ q * Y ω ^ q) := by
    filter_upwards [hpoint] with ω hω
    have hh := ENNReal.rpow_le_rpow hω hq.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le,
      ENNReal.mul_rpow_of_nonneg _ _ hq.le,
      ENNReal.ofReal_rpow_of_nonneg hC hq.le] at hh
    simpa only [mul_assoc] using hh
  calc
    ∫⁻ ω, Z ω ^ q ∂P ≤
        ∫⁻ ω, ENNReal.ofReal (C ^ q) * (X ω ^ q * Y ω ^ q) ∂P :=
      lintegral_mono_ae hstep
    _ = ENNReal.ofReal (C ^ q) *
          ∫⁻ ω, X ω ^ q * Y ω ^ q ∂P := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (C ^ q) *
          ((∫⁻ ω, (X ω ^ q) ^ 2 ∂P) +
            ∫⁻ ω, (Y ω ^ q) ^ 2 ∂P) := by
              gcongr
              exact convCross_lintegral_mul_le_sq_sum hXq
    _ ≤ ENNReal.ofReal (C ^ q) *
          (ENNReal.ofReal BX + ENNReal.ofReal BY) := by
            simp_rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
            have hsum : (∫⁻ ω, X ω ^ (q * 2) ∂P) +
                ∫⁻ ω, Y ω ^ (q * 2) ∂P ≤
                ENNReal.ofReal BX + ENNReal.ofReal BY := by
              simpa only [h2q] using add_le_add hXmom hYmom
            exact mul_le_mul_of_nonneg_left hsum
              (zero_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (C ^ q))
    _ = ENNReal.ofReal (C ^ q * (BX + BY)) := by
      rw [← ENNReal.ofReal_add hBX hBY,
        ENNReal.ofReal_mul (Real.rpow_nonneg hC _)]

/-- W2 at each of finitely many deterministic centers controls the inverse
moment of their minimum crossing. -/
theorem convCross_finite_min_moment {d : ℕ} {κ : Rd d → ℝ}
    (hW2 : WNInvCrossShape d κ)
    {b μ ρ q : ℝ} (hb : 0 < b) (hμ : 0 < μ)
    (hρ : 0 < ρ) (hq : 0 < q)
    (Y : Finset (Rd d)) (hYne : Y.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        IsDyadicRealization κ P W H → ∀ N : ℕ,
        ∫⁻ ω, (ENNReal.ofReal
          (Y.inf' hYne (fun v => acrossDist ξ (fun z => H N z ω) v (2 * ρ) ρ) /
            aQ P H ξ N 2⁻¹))⁻¹ ^ q ∂P ≤ ENNReal.ofReal C := by
  classical
  let C₀ : Rd d → ℝ := fun v =>
    Classical.choose (hW2 b μ hb hμ v (2 * ρ) ρ hρ (by linarith) q hq)
  let C : ℝ := ∑ v ∈ Y, max 0 (C₀ v)
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => le_max_left _ _
  refine ⟨C, hC, ?_⟩
  intro ξ hU Ω _ P W H hH N
  have haQ : 0 < aQ P H ξ N 2⁻¹ :=
    tight_aQ_pos (by have hd := hU.base.dim; omega : 0 < d)
      hH ξ N (by norm_num) (by norm_num)
  let D : Rd d → Ω → ℝ := fun v ω => acrossDist ξ (fun z => H N z ω) v (2 * ρ) ρ
  let M : Ω → ℝ := fun ω => Y.inf' hYne (fun v => D v ω)
  have hMpos (ω : Ω) : 0 < M ω := by
    obtain ⟨v, hv, hvM⟩ := Finset.exists_mem_eq_inf' hYne (fun v => D v ω)
    rw [show M ω = D v ω from hvM]
    exact acrossDist_pos (by have hd := hU.base.dim; omega : 0 < d)
      ((hH.band N).continuous ω) hρ.le (by linarith)
  have hsingle (v : Rd d) (hv : v ∈ Y) :
      ∫⁻ ω, (ENNReal.ofReal (D v ω / aQ P H ξ N 2⁻¹))⁻¹ ^ q ∂P ≤
        ENNReal.ofReal (max 0 (C₀ v)) := by
    have hvW := Classical.choose_spec
      (hW2 b μ hb hμ v (2 * ρ) ρ hρ (by linarith) q hq)
    have hh := hvW ξ hU Ω P W H hH N
    exact hh.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  have hmeas (v : Rd d) (hv : v ∈ Y) :
      AEMeasurable (fun ω =>
        (ENNReal.ofReal (D v ω / aQ P H ξ N 2⁻¹))⁻¹ ^ q) P := by
    have hD : Measurable (D v) :=
      measurable_acrossDist ((hH.band N).continuous)
        ((hH.band N).measurable) ξ v (2 * ρ) ρ
    exact (((hD.div_const _).ennreal_ofReal).inv.pow_const q).aemeasurable
  have hpoint (ω : Ω) :
      (ENNReal.ofReal (M ω / aQ P H ξ N 2⁻¹))⁻¹ ^ q ≤
        ∑ v ∈ Y, (ENNReal.ofReal (D v ω / aQ P H ξ N 2⁻¹))⁻¹ ^ q := by
    obtain ⟨v, hv, hvM⟩ := Finset.exists_mem_eq_inf' hYne (fun v => D v ω)
    rw [show M ω = D v ω from hvM]
    exact Finset.single_le_sum (fun w _ =>
      (zero_le : (0 : ℝ≥0∞) ≤
        (ENNReal.ofReal (D w ω / aQ P H ξ N 2⁻¹))⁻¹ ^ q)) hv
  calc
    ∫⁻ ω, (ENNReal.ofReal (M ω / aQ P H ξ N 2⁻¹))⁻¹ ^ q ∂P ≤
        ∫⁻ ω, ∑ v ∈ Y,
          (ENNReal.ofReal (D v ω / aQ P H ξ N 2⁻¹))⁻¹ ^ q ∂P :=
            lintegral_mono hpoint
    _ = ∑ v ∈ Y, ∫⁻ ω,
          (ENNReal.ofReal (D v ω / aQ P H ξ N 2⁻¹))⁻¹ ^ q ∂P :=
            lintegral_finsetSum' Y hmeas
    _ ≤ ∑ v ∈ Y, ENNReal.ofReal (max 0 (C₀ v)) :=
      Finset.sum_le_sum fun v hv => hsingle v hv
    _ = ENNReal.ofReal C :=
      (ENNReal.ofReal_sum_of_nonneg
        (fun v hv => le_max_left (0 : ℝ) (C₀ v))).symm

end HigherDimLQGContinuity
