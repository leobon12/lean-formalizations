import QuantumZipper.Proofs.Section5.Prop16D4WProb
import QuantumZipper.Proofs.Section5.Prop16AreaEval

/-!
# Proposition 1.6, D4⁺ʷ clause (2) in abstract form (with `locArea`)

Decision D24 (`DECISIONS.md`). `tendsto_pairing_locArea_close` is clause (2) of
`Prop16TVWeakStmt` for abstract random fields: the actual field `Y` (locally good, with the same
local area measure on `U` as `ofFun φ + x`), the unperturbed field `x`, the witness
`Z = canonicalOn γ x U`. Inputs: the three inputs of `tendsto_canonical_pairing_close` (scale
ratio → 1, `φ(a·) → 0`, tightness) and `hdom` (the canonical domain of `x` contains `hball R`
with probability → 1).

* `exists_vague_rescale_of_locallyGood`, `isVagueLimitOn_qAreaMeasureOn`: the local area limit
  of a rescaled locally good sample exists and is `qAreaMeasureOn`;
* `integral_canonicalOn_eq_locArea`: `∫ f dμ_{canon x} = locArea γ R f (canon x)` when the
  canonical domain contains `hball R` (via `Prop16Area.integral_eq_locArea`);
* `integral_canonicalOn_congr`: the canonical pairing only depends on the local area measure.

Own elementary arguments (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area.G GoodSample RegClosure LocalRule

/-- An existing local area limit is `qAreaMeasureOn`. -/
theorem isVagueLimitOn_qAreaMeasureOn {γ : ℝ} {x : FieldSample} {U : Set ℂ}
    (h : ∃ μ, IsVagueLimitOn U (areaApprox γ x) μ) :
    IsVagueLimitOn U (areaApprox γ x) (qAreaMeasureOn γ x U) := by
  unfold qAreaMeasureOn
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

theorem preimage_mul_subset_H {U : Set ℂ} (hUH : U ⊆ H) {s : ℝ} (hs : 0 < s) :
    (fun z => (s : ℂ) * z) ⁻¹' U ⊆ H := fun z hz => by
  have h1 : (0 : ℝ) < ((s : ℂ) * z).im := hUH hz
  rw [Complex.im_ofReal_mul] at h1
  exact pos_of_mul_pos_right h1 hs.le

/-- The local area limit of a rescaled locally good sample exists. -/
theorem exists_vague_rescale_of_locallyGood {γ : ℝ} (hγ : 0 < γ) {V U : Set ℂ}
    {x : FieldSample} (hx : IsLocallyGoodOn γ V x) (hU : IsOpen U) (hUH : U ⊆ H) (hUV : U ⊆ V)
    {s : ℝ} (hs : 0 < s) :
    ∃ μ, IsVagueLimitOn ((fun z => (s : ℂ) * z) ⁻¹' U) (areaApprox γ (rescale x (Qc γ) s)) μ := by
  obtain ⟨W, hWo, hWV, y, ψ, hy, hψ, h⟩ := hx
  rw [← hWV] at hUV hψ
  have hUW : U ⊆ W := fun z hz => (hUV hz).1
  have hmul : Continuous fun z : ℂ => (s : ℂ) * z := continuous_const.mul continuous_id
  have hU' : IsOpen ((fun z => (s : ℂ) * z) ⁻¹' U) := hU.preimage hmul
  have hW' : IsOpen ((fun z => (s : ℂ) * z) ⁻¹' W) := hWo.preimage hmul
  have hψ' : ContinuousOn (fun u => ψ ((s : ℂ) * u)) ((fun z => (s : ℂ) * z) ⁻¹' W ∩ Hbar) :=
    hψ.comp hmul.continuousOn fun u hu => ⟨hu.1, mapsTo_mul_pos hs hu.2⟩
  have hag := ((fcAgree_rescale hWo h (Qc γ) hs).trans
      (fcAgree_rescale_add_ofFun hy.1 hWo hψ (Qc γ) hs)).circAgree
  have hU'H := preimage_mul_subset_H hUH hs
  have hU'W : (fun z => (s : ℂ) * z) ⁻¹' U ⊆ (fun z => (s : ℂ) * z) ⁻¹' W := fun z hz => hUW hz
  exact ⟨_, isVagueLimitOn_of_circAgree hW' hag hU'H hU'W
    (isVagueLimitOn_add_ofFun (hy.rescale hγ hs).1 hU' hU'H
      (isVagueLimitOn_restrict_sub hU' hU'H (isVagueLimitOn_H_of_good (hy.rescale hγ hs)))
      hW' hU'W hψ')⟩

/-- **Evaluation of the canonical pairing by `locArea`.** -/
theorem integral_canonicalOn_eq_locArea {γ : ℝ} (hγ : 0 < γ) {V U : Set ℂ} {x : FieldSample}
    (hx : IsLocallyGoodOn γ V x) (hU : IsOpen U) (hUH : U ⊆ H) (hUV : U ⊆ V)
    (ha : 0 < scaleParamOn γ x U) {R : ℕ} (hB : Prop16Area.hball R ⊆ canonicalDomainOn γ x U)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfR : ∀ z, f z ≠ 0 → z ∈ Metric.ball (0 : ℂ) R) :
    ∫ z, f z ∂qAreaMeasureOn γ (canonicalOn γ x U) (canonicalDomainOn γ x U) =
      Prop16Area.locArea γ R f (canonicalOn γ x U) :=
  Prop16Area.integral_eq_locArea (preimage_mul_subset_H hUH ha) hB
    (isVagueLimitOn_qAreaMeasureOn (exists_vague_rescale_of_locallyGood hγ hx hU hUH hUV ha))
    hf hfc hfR

/-- The canonical pairing only depends on the local area measure. -/
theorem integral_canonicalOn_congr {γ : ℝ} (hγ : 0 < γ) {V U : Set ℂ} {x x' : FieldSample}
    (hx : IsLocallyGoodOn γ V x) (hx' : IsLocallyGoodOn γ V x') (hU : IsOpen U) (hUH : U ⊆ H)
    (hUV : U ⊆ V) (heq : qAreaMeasureOn γ x U = qAreaMeasureOn γ x' U)
    (ha : 0 < scaleParamOn γ x U) {f : ℂ → ℝ} (hf : Continuous f) :
    ∫ z, f z ∂qAreaMeasureOn γ (canonicalOn γ x U) (canonicalDomainOn γ x U) =
      ∫ z, f z ∂qAreaMeasureOn γ (canonicalOn γ x' U) (canonicalDomainOn γ x' U) := by
  have hs : scaleParamOn γ x U = scaleParamOn γ x' U := by unfold scaleParamOn; rw [heq]
  rw [integral_canonicalOn_of_locallyGood hγ hx hU hUH hUV ha hf,
    integral_canonicalOn_of_locallyGood hγ hx' hU hUH hUV (hs ▸ ha) hf, hs, heq]

/-- **Clause (2) of D4⁺ʷ, abstract form.** The actual field `Y` has the local area measure of
`ofFun φ + x`; the witness is `Z = canonicalOn γ x U`. -/
theorem tendsto_pairing_locArea_close {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    {γ : ℝ} (hγ : 0 < γ) (Y x : ℝ → Ω → FieldSample) (φ : ℝ → Ω → ℂ → ℝ)
    (U V : ℝ → Ω → Set ℂ)
    (hloc : ∀ C, ∀ᵐ ω ∂Q, (IsLocallyGoodOn γ (V C ω) (x C ω) ∧ IsOpen (U C ω) ∧ U C ω ⊆ H ∧
      U C ω ⊆ V C ω ∧ ContinuousOn (φ C ω) (V C ω)) ∧ IsLocallyGoodOn γ (V C ω) (Y C ω) ∧
      qAreaMeasureOn γ (Y C ω) (U C ω) = qAreaMeasureOn γ (ofFun (φ C ω) + x C ω) (U C ω))
    (hscale : ∀ κ > 0, Tendsto (fun C => Q {ω | ¬ (0 < scaleParamOn γ (x C ω) (U C ω) ∧
      0 < scaleParamOn γ (ofFun (φ C ω) + x C ω) (U C ω) ∧
      |scaleParamOn γ (ofFun (φ C ω) + x C ω) (U C ω) - scaleParamOn γ (x C ω) (U C ω)| ≤
        κ * scaleParamOn γ (x C ω) (U C ω))}) atTop (𝓝 0))
    (hφ : ∀ ρ > 0, ∀ ε > 0, Tendsto (fun C => Q {ω | ¬ ∀ z ∈ U C ω,
      ‖z‖ < ρ * scaleParamOn γ (x C ω) (U C ω) → |φ C ω z| ≤ ε}) atTop (𝓝 0))
    (htight : ∀ ρ > 0, ∀ θ > 0, ∃ M : ℝ, ∀ᶠ C in atTop, Q {ω | ¬ qAreaMeasureOn γ (x C ω) (U C ω)
      (ball 0 (ρ * scaleParamOn γ (x C ω) (U C ω))) ≤ ENNReal.ofReal M} ≤ θ)
    (R : ℕ) (hdom : Tendsto (fun C => Q {ω |
      ¬ Prop16Area.hball R ⊆ canonicalDomainOn γ (x C ω) (U C ω)}) atTop (𝓝 0))
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfR : ∀ z, f z ≠ 0 → z ∈ Metric.ball (0 : ℂ) R) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun C => Q {ω | δ <
      |∫ z, f z ∂qAreaMeasureOn γ (canonicalOn γ (Y C ω) (U C ω))
          (canonicalDomainOn γ (Y C ω) (U C ω)) -
        Prop16Area.locArea γ R f (canonicalOn γ (x C ω) (U C ω))|}) atTop (𝓝 0) := by
  have hmain := tendsto_canonical_pairing_close Q hγ x φ U V (fun C => (hloc C).mono
    fun ω h => h.1) hscale hφ htight hf hfc hδ
  have hsum := (hmain.add hdom).add (hscale 1 one_pos)
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) (fun C => ?_)
  set N := {ω | ¬ ((IsLocallyGoodOn γ (V C ω) (x C ω) ∧ IsOpen (U C ω) ∧ U C ω ⊆ H ∧
      U C ω ⊆ V C ω ∧ ContinuousOn (φ C ω) (V C ω)) ∧ IsLocallyGoodOn γ (V C ω) (Y C ω) ∧
      qAreaMeasureOn γ (Y C ω) (U C ω) = qAreaMeasureOn γ (ofFun (φ C ω) + x C ω) (U C ω))}
  have hN : Q N = 0 := ae_iff.1 (hloc C)
  refine (measure_mono (fun ω hω => ?_ : _ ⊆ ((_ ∪ _) ∪ _) ∪ N)).trans
    (((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
      (add_le_add (measure_union_le _ _) le_rfl)) hN.le)).trans (le_of_eq (add_zero _)))
  simp only [mem_ofPred_eq] at hω
  by_contra hc
  simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_lt, N] at hc
  obtain ⟨⟨⟨hΔ, hB⟩, ha, ha', -⟩, ⟨hx, hU, hUH, hUV, hφc⟩, hY, heq⟩ := hc
  have hsY : scaleParamOn γ (Y C ω) (U C ω) = scaleParamOn γ (ofFun (φ C ω) + x C ω) (U C ω) := by
    unfold scaleParamOn; rw [heq]
  rw [integral_canonicalOn_congr hγ hY (isLocallyGoodOn_ofFun_add hx hφc) hU hUH hUV heq
      (hsY ▸ ha') hf,
    ← integral_canonicalOn_eq_locArea hγ hx hU hUH hUV ha hB hf hfc hfR] at hω
  linarith

end Prop16Asm

end QuantumZipper
