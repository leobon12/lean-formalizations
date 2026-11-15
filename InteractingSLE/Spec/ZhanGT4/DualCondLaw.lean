/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualCond

/-!
# The conditional laws of the stopped dual coupling on one rectangle

Packet PROVE-ZHAN-GT4-A17. Source: Astra, *Follow-up proofs*, §A.1 (`source/external/AstraIG1/ig1_followup_proofs.txt`
L160–L166, L344–L357, R38): "conditionally on any stopping-time prefix of curve `k`, curve `j`, mapped by the
hydrodynamic map of that prefix and stopped on first contact with it, has the corresponding force-point law, after its
capacity time change", proved inside a rectangle by (D10), the time change and uniqueness in law.

For one rectangle `i`:

* `DualHyp.dualCoupling_rect_eq`: `dualCoupling (A ×ˢ B) = ∫_B Q_{ω₂}(A) · Ñ_t(0, S₂ i)/Ñ_t(0, 0) dP₂` for `A` an event
  of curve `1` stopped at `S₁ i` and `B` an event of curve `2` stopped at `S₂ i`, where
  `Q_{ω₂} = (Ñ(S₁ i, y)/Ñ(0, y)) · P₁`, `y = S₂ i (ω₂)` (`condMeasure₁`): conditionally on the curve-`2` prefix, curve `1`
  up to `S₁ i` has the law `Q_{ω₂}`;
* **`DualHyp.exists_condLaw₁`**: for every curve-`2` path, under `Q_{ω₂}` the image of curve `1` in the chart of the
  frozen hull `K₂(y)` is an integrated `SLE_κ(ρ)` evolution of the image word (the other tip `W₂(y)` with weight `−κ/2`,
  the images `g_y(p_m)` with weights `κ r_m`) up to `a(S₁ i)`, with the killed laws of every such evolution (A12's
  `FrzD10Hyp.exists_isIntegratedSLEEvolution_img_law`, with the (D9) constants of `exists_twoCurveD9_family`).
-/

set_option autoImplicit false

noncomputable section

open Finset Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull drive)

section CondLaw

variable {Ω₁ Ω₂ : Type*} {ι : Type*} [Fintype ι] {n : ℕ}

/-- **The conditional law of curve `1` on rectangle `i` given the curve-`2` path `ω₂`**:
`(Ñ(S₁ i, y)/Ñ(0, y)) · P₁` with `y = S₂ i (ω₂)` (A12's tilted measure with the frozen hull `K₂(y)`). -/
def condMeasure₁ {mΩ₁ : MeasurableSpace Ω₁} (κ : ℝ) (rr p : Fin n → ℝ) (P₁ : Measure Ω₁) (B₁ : ℝ≥0 → Ω₁ → ℝ)
    (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ) (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (i : ι) (ω₂ : Ω₂) : Measure Ω₁ :=
  P₁.withDensity fun ω₁ => ENNReal.ofReal (Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ (S₁ i ω₁) (S₂ i ω₂) -
    pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 (S₂ i ω₂)))

/-- The rectangle density factors as the conditional density of curve `1` times the marginal factor of curve `2`. -/
theorem rectDens_eq (κ : ℝ) (rr p : Fin n → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ)
    (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (i : ι) (ω : Ω₁ × Ω₂) :
    rectDens κ rr p B₁ B₂ x₂ S₁ S₂ i ω =
      Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 (S₁ i ω.1) (S₂ i ω.2) -
        pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 0 (S₂ i ω.2)) *
      Real.exp (pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 0 (S₂ i ω.2) - pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 0 0) := by
  unfold rectDens normLog
  simp only [← Real.exp_add]
  congr 1; ring

/-- The curve-`2` path `x₂ + √(16/κ) B₂`. -/
def path₂ (κ : ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ) (ω₂ : Ω₂) : ℝ → ℝ := fun u => drive (16 / κ) B₂ ω₂ u + x₂

/-- The canonical image clock of curve `1` in the chart of the frozen hull `K₂(S₂ i)` (`s`-view selection). -/
def condA (κ : ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ) (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0)
    (i : ι) (ω₂ : Ω₂) (ω₁ : Ω₁) : ℝ → ℝ :=
  sSelA (drive κ B₁ ω₁) (path₂ κ B₂ x₂ ω₂) (fun j => (S₁ j ω₁ : ℝ)) (fun j => (S₂ j ω₂ : ℝ)) (S₂ i ω₂)

/-- The canonical image driver of curve `1` in the chart of the frozen hull `K₂(S₂ i)`. -/
def condW (κ : ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ) (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0)
    (i : ι) (ω₂ : Ω₂) (ω₁ : Ω₁) : ℝ → ℝ :=
  sSelW (drive κ B₁ ω₁) (path₂ κ B₂ x₂ ω₂) (fun j => (S₁ j ω₁ : ℝ)) (fun j => (S₂ j ω₂ : ℝ)) (S₂ i ω₂)

/-- The width of that selection (the staircase width at height `S₂ i`). -/
def condT (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (i : ι) (ω₂ : Ω₂) (ω₁ : Ω₁) : ℝ :=
  stairH (fun j => (S₂ j ω₂ : ℝ)) (fun j => (S₁ j ω₁ : ℝ)) (S₂ i ω₂)

variable {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂} {κ : ℝ} {P₁ : Measure Ω₁}
  {𝓕₁ : Filtration ℝ≥0 mΩ₁} {B₁ : ℝ≥0 → Ω₁ → ℝ} {P₂ : Measure Ω₂} {𝓕₂ : Filtration ℝ≥0 mΩ₂}
  {B₂ : ℝ≥0 → Ω₂ → ℝ} {x₂ : ℝ} {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ} {p : Fin n → ℝ} {Tm : ℝ}
  {S₁ : ι → Ω₁ → ℝ≥0} {S₂ : ι → Ω₂ → ℝ≥0}

namespace DualHyp

variable (h : DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ H₁ H₂ δ q d p Tm S₁ S₂)
include h

/-- The curve-`2` marginal exponent at curve-`1` height `0` does not depend on the curve-`1` path. -/
theorem pairT_zero_congr (rr : Fin n → ℝ) (ω₁ ω₁' : Ω₁) (ω₂ : Ω₂) (y : ℝ) :
    pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 y = pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω₁' ω₂ 0 y := by
  have hE := h.twoEncl ω₁ ω₂
  have hE' := h.twoEncl ω₁' ω₂
  exact tEll_zero_congr κ rr p hE.cont₁ hE'.cont₁ (hE.zero₁.trans hE'.zero₁.symm) _
    (fun j => (S₁ j ω₁).coe_nonneg) (fun j => (S₁ j ω₁').coe_nonneg) _ y

/-- **The stopped dual coupling on rectangle `i`, disintegrated over curve `2`**: for an event `A` of curve `1`
stopped at `S₁ i` and an event `B` of curve `2` stopped at `S₂ i`,
`dualCoupling (A ×ˢ B) = ∫_B Q_{ω₂}(A) · Ñ_t(0, S₂ i)/Ñ_t(0, 0) dP₂` (`condMeasure₁`). -/
theorem dualCoupling_rect_eq [Nonempty ι] (rr : Fin n → ℝ) (i : ι) {A : Set Ω₁} {B : Set Ω₂}
    (hA : MeasurableSet[(h.stop₁ i).measurableSpace] A) (hB : MeasurableSet[(h.stop₂ i).measurableSpace] B) :
    dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm (A ×ˢ B) =
      ∫⁻ ω₂ in B, condMeasure₁ κ rr p P₁ B₁ B₂ x₂ S₁ S₂ i ω₂ A *
        ENNReal.ofReal (Real.exp (pairT κ rr p B₁ B₂ x₂ S₁ S₂ (nonempty_of_isFilteredBrownianReal h.bm₁).some ω₂ 0
          (S₂ i ω₂) - pairT κ rr p B₁ B₂ x₂ S₁ S₂ (nonempty_of_isFilteredBrownianReal h.bm₁).some ω₂ 0 0)) ∂P₂ := by
  have := h.isProbabilityMeasure₁
  have := h.isProbabilityMeasure₂
  have hAm : MeasurableSet A := (h.stop₁ i).measurableSpace_le _ hA
  have hR : Measurable (rectDens κ rr p B₁ B₂ x₂ S₁ S₂ i) := (h.measurable_condDens rr i).2
  set ω₁₀ := (nonempty_of_isFilteredBrownianReal h.bm₁).some
  rw [h.dualCoupling_rect rr i hA hB, ← Measure.prod_restrict, lintegral_prod_symm _ hR.ennreal_ofReal.aemeasurable]
  refine lintegral_congr fun ω₂ => ?_
  rw [condMeasure₁, withDensity_apply _ hAm, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ω₁ => ?_
  rw [rectDens_eq, ENNReal.ofReal_mul (Real.exp_pos _).le, h.pairT_zero_congr rr ω₁ ω₁₀ ω₂,
    h.pairT_zero_congr rr ω₁ ω₁₀ ω₂ 0]

/-- **The frozen-hull hypotheses of A12 at the frozen height `S₂ i (ω₂)`** for curve `1` stopped at `S₁ i` (the (D9)
constants of `exists_twoCurveD9_family`, uniform over the rectangle attaining the staircase width). -/
theorem exists_frzD10Hyp_cond (rr : Fin n → ℝ) (i : ι) (ω₂ : Ω₂) : ∃ r a₀ γ Γ lam L : ℝ,
    FrzD10Hyp κ B₁ (condW κ B₁ B₂ x₂ S₁ S₂ i ω₂) (condA κ B₁ B₂ x₂ S₁ S₂ i ω₂)
      (fwdHull (path₂ κ B₂ x₂ ω₂) (S₂ i ω₂)) (frzChart (path₂ κ B₂ x₂ ω₂) (S₂ i ω₂)) rr
      (path₂ κ B₂ x₂ ω₂ (S₂ i ω₂)) (frzMarks (path₂ κ B₂ x₂ ω₂) p (S₂ i ω₂)) (S₁ i) (condT S₁ S₂ i ω₂)
      r a₀ γ Γ lam L Tm := by
  obtain ⟨r, a₀, γ, Γ, lam, hr, ha, hg, hmain⟩ := exists_twoCurveD9_family h.hull₁ h.hull₂ h.δpos h.sep h.dpos
    h.qpos h.qH h.pH h.pinj Tm
  obtain ⟨L, hL⟩ := exists_scaleOK hr ha hg Γ lam Tm
  have hy : (S₂ i ω₂ : ℝ) ∈ Icc (0 : ℝ) (S₂ i ω₂) := ⟨(S₂ i ω₂).coe_nonneg, le_rfl⟩
  have hj : ∀ ω₁, ∃ j, (S₂ i ω₂ : ℝ) ≤ S₂ j ω₂ ∧ condT S₁ S₂ i ω₂ ω₁ = S₁ j ω₁ := fun ω₁ =>
    exists_eq_stairH (S₁ := fun j => (S₂ j ω₂ : ℝ)) (S₂ := fun j => (S₁ j ω₁ : ℝ)) (fun j => (S₁ j ω₁).coe_nonneg)
      (le_rfl : (S₂ i ω₂ : ℝ) ≤ S₂ i ω₂)
  have hD : ∀ ω₁, TwoCurveD9 (frzDataOf κ B₁ (condW κ B₁ B₂ x₂ S₁ S₂ i ω₂) (condA κ B₁ B₂ x₂ S₁ S₂ i ω₂)
      (frzChart (path₂ κ B₂ x₂ ω₂) (S₂ i ω₂)) rr (path₂ κ B₂ x₂ ω₂ (S₂ i ω₂))
      (frzMarks (path₂ κ B₂ x₂ ω₂) p (S₂ i ω₂)) ω₁) (fwdHull (path₂ κ B₂ x₂ ω₂) (S₂ i ω₂))
      (condT S₁ S₂ i ω₂ ω₁) r a₀ γ Γ lam := fun ω₁ => by
    have hE := h.twoEncl ω₁ ω₂
    obtain ⟨-, hown, -, -⟩ := hE.sView_encl i hy
    obtain ⟨j, hyj, hjT⟩ := hj ω₁
    exact hmain j (drive κ B₁ ω₁) (path₂ κ B₂ x₂ ω₂) (S₂ i ω₂) (condT S₁ S₂ i ω₂ ω₁) (condA κ B₁ B₂ x₂ S₁ S₂ i ω₂ ω₁)
      (condW κ B₁ B₂ x₂ S₁ S₂ i ω₂ ω₁) κ rr hown hE.cont₂ (hE.start₂ j) (hE.qW j) (S₂ i ω₂).coe_nonneg (h.le₂ i ω₂)
      (by rw [hjT]; exact h.le₁ j ω₁) (by rw [hjT]; exact h.K₁ j ω₁)
      (((QuantumZipper.fwdHull_mono).1 hyj).trans (h.K₂ j ω₂))
  obtain ⟨ω₁₀⟩ := nonempty_of_isFilteredBrownianReal h.bm₁
  refine ⟨r, a₀, γ, Γ, lam, L, ⟨⟨fun ω₁ => ((h.twoEncl ω₁ ω₂).sView_encl i hy).2.1,
    fun ω₁ => ((h.twoEncl ω₁ ω₂).sView_encl i hy).1, fun ω₁ => ?_, fun ω₁ => (hD ω₁).alive₀,
    fun ω₁ m => (hD ω₁).alive m, (hD ω₁₀).ne, (hD ω₁₀).inj, fun ω₁ => (hD ω₁).d9, hL⟩,
    fun ω₁ t ht => (hD ω₁).drv t ht⟩⟩
  obtain ⟨j, -, hjT⟩ := hj ω₁
  rw [hjT]; exact h.le₁ j ω₁

omit h in
/-- **A12's tilted measure at the frozen height `S₂ i (ω₂)` is the conditional law `condMeasure₁`.** -/
theorem girsMeasure_cond_eq (rr : Fin n → ℝ) (i : ι) (ω₂ : Ω₂) :
    girsMeasure P₁ (Real.sqrt κ) B₁ (S₁ i) (fun ω₁ => (frzDataOf κ B₁ (condW κ B₁ B₂ x₂ S₁ S₂ i ω₂)
      (condA κ B₁ B₂ x₂ S₁ S₂ i ω₂) (frzChart (path₂ κ B₂ x₂ ω₂) (S₂ i ω₂)) rr (path₂ κ B₂ x₂ ω₂ (S₂ i ω₂))
      (frzMarks (path₂ κ B₂ x₂ ω₂) p (S₂ i ω₂)) ω₁).ell) = condMeasure₁ κ rr p P₁ B₁ B₂ x₂ S₁ S₂ i ω₂ := by
  unfold girsMeasure condMeasure₁
  congr 1
  funext ω₁
  have hd : ∀ s : ℝ≥0, drive κ B₁ ω₁ (s : ℝ) = Real.sqrt κ * B₁ s ω₁ := fun s => by
    simp only [drive, Real.toNNReal_coe]
  unfold girsDensity pairS sEll
  rw [hd, ← NNReal.coe_zero, hd]
  rfl

/-- **(D10): the conditional law of curve `1` given the curve-`2` prefix, inside rectangle `i`** (§A.1, "conditionally on
any stopping-time prefix of curve `k`, curve `j`, mapped by the hydrodynamic map of that prefix …, has the corresponding
force-point law, after its capacity time change"). For every curve-`2` path `ω₂`, under `Q_{ω₂}` (`condMeasure₁`, the
conditional law of curve `1` on `F¹_{S₁ i}` given the curve-`2` prefix up to `y = S₂ i (ω₂)`, `dualCoupling_rect_eq`),
the image of curve `1` in the chart `g_y` of the frozen hull `K₂(y)` — capacity clock `condA`, image driver `condW` —
together with the image marks (the frozen tip `W₂(y)` with weight `−κ/2`, the images `g_y(p_m)` with weights `κ r_m`,
sorted by `e` around `w₀`) is, up to `a(S₁ i)`, an integrated `SLE_κ(ρ)` evolution of the image word, and its killed
laws are those of every integrated evolution of that word (A12's `exists_isIntegratedSLEEvolution_img_law`). -/
theorem exists_condLaw₁ [Nonempty ι] (rr : Fin n → ℝ) (i : ι) (ω₂ : Ω₂) :
    ∃ (nL nR : ℕ) (e : Fin nL ⊕ Fin nR ≃ Option (Fin n)) (w₀ : ℝ),
      (∀ k, markPos (path₂ κ B₂ x₂ ω₂ (S₂ i ω₂)) (frzMarks (path₂ κ B₂ x₂ ω₂) p (S₂ i ω₂)) (e (Sum.inl k)) < w₀) ∧
      (∀ k, w₀ < markPos (path₂ κ B₂ x₂ ω₂ (S₂ i ω₂)) (frzMarks (path₂ κ B₂ x₂ ω₂) p (S₂ i ω₂)) (e (Sum.inr k))) ∧
      ∃ (𝓗 : Filtration ℝ≥0 mΩ₁) (Bh gW : ℝ≥0 → Ω₁ → ℝ) (gL : Fin nL → ℝ≥0 → Ω₁ → ℝ)
        (gR : Fin nR → ℝ≥0 → Ω₁ → ℝ) (ζG : Ω₁ → ℝ≥0∞),
        IsIntegratedSLEEvolution κ
          (fun k => markPos (path₂ κ B₂ x₂ ω₂ (S₂ i ω₂)) (frzMarks (path₂ κ B₂ x₂ ω₂) p (S₂ i ω₂)) (e (Sum.inl k)) - w₀)
          (fun k => markPos (path₂ κ B₂ x₂ ω₂ (S₂ i ω₂)) (frzMarks (path₂ κ B₂ x₂ ω₂) p (S₂ i ω₂)) (e (Sum.inr k)) - w₀)
          (fun k => markWt κ rr (e (Sum.inl k))) (fun k => markWt κ rr (e (Sum.inr k)))
          (condMeasure₁ κ rr p P₁ B₁ B₂ x₂ S₁ S₂ i ω₂) 𝓗 gW gL gR Bh ζG ∧
        (∀ ω₁, ENNReal.ofReal (condA κ B₁ B₂ x₂ S₁ S₂ i ω₂ ω₁ (S₁ i ω₁)) ≤ ζG ω₁ ∧ ∀ t : ℝ≥0,
          (t : ℝ) < condA κ B₁ B₂ x₂ S₁ S₂ i ω₂ ω₁ (S₁ i ω₁) →
            gW t ω₁ = condW κ B₁ B₂ x₂ S₁ S₂ i ω₂ ω₁ t - w₀ ∧
            (∀ k, gL k t ω₁ = imgV (condW κ B₁ B₂ x₂ S₁ S₂ i ω₂ ω₁) (markPos (path₂ κ B₂ x₂ ω₂ (S₂ i ω₂))
              (frzMarks (path₂ κ B₂ x₂ ω₂) p (S₂ i ω₂)) (e (Sum.inl k))) t - w₀) ∧
            ∀ k, gR k t ω₁ = imgV (condW κ B₁ B₂ x₂ S₁ S₂ i ω₂ ω₁) (markPos (path₂ κ B₂ x₂ ω₂ (S₂ i ω₂))
              (frzMarks (path₂ κ B₂ x₂ ω₂) p (S₂ i ω₂)) (e (Sum.inr k))) t - w₀) ∧
        ∀ {Ω₃ : Type*} {m₃ : MeasurableSpace Ω₃} {P₃ : Measure Ω₃} [IsProbabilityMeasure P₃]
          {𝓕₃ : Filtration ℝ≥0 m₃} {W₃ : ℝ≥0 → Ω₃ → ℝ} {VL₃ : Fin nL → ℝ≥0 → Ω₃ → ℝ}
          {VR₃ : Fin nR → ℝ≥0 → Ω₃ → ℝ} {B₃ : ℝ≥0 → Ω₃ → ℝ} {ζ₃ : Ω₃ → ℝ≥0∞},
          IsIntegratedSLEEvolution κ
            (fun k => markPos (path₂ κ B₂ x₂ ω₂ (S₂ i ω₂)) (frzMarks (path₂ κ B₂ x₂ ω₂) p (S₂ i ω₂)) (e (Sum.inl k)) -
              w₀)
            (fun k => markPos (path₂ κ B₂ x₂ ω₂ (S₂ i ω₂)) (frzMarks (path₂ κ B₂ x₂ ω₂) p (S₂ i ω₂)) (e (Sum.inr k)) -
              w₀)
            (fun k => markWt κ rr (e (Sum.inl k))) (fun k => markWt κ rr (e (Sum.inr k))) P₃ 𝓕₃ W₃ VL₃ VR₃ B₃ ζ₃ →
          ∀ (m : ℕ) (ts : Fin m → ℝ≥0) (Asets : Fin m → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
            (∀ j, MeasurableSet (Asets j)) →
            condMeasure₁ κ rr p P₁ B₁ B₂ x₂ S₁ S₂ i ω₂
                {ω | ∀ j, (ts j : ℝ≥0∞) < ζG ω ∧ (gW (ts j) ω, (fun k => gL k (ts j) ω),
                  (fun k => gR k (ts j) ω), Bh (ts j) ω) ∈ Asets j} =
              P₃ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₃ ω ∧
                (W₃ (ts j) ω, (fun k => VL₃ k (ts j) ω), (fun k => VR₃ k (ts j) ω), B₃ (ts j) ω) ∈ Asets j} := by
  obtain ⟨r, a₀, γ, Γ, lam, L, hH⟩ := h.exists_frzD10Hyp_cond rr i ω₂
  obtain ⟨C, hC⟩ := (Bornology.isBounded_iUnion.2 fun j => (h.hull₁ j).2.1).exists_norm_le
  have hK : ∀ ω₁, fwdHull (drive κ B₁ ω₁) (condT S₁ S₂ i ω₂ ω₁) ⊆ Metric.closedBall (0 : ℂ) (max C 1) :=
      fun ω₁ z hz => by
    obtain ⟨j, -, hjT⟩ := exists_eq_stairH (S₁ := fun j => (S₂ j ω₂ : ℝ)) (S₂ := fun j => (S₁ j ω₁ : ℝ))
      (fun j => (S₁ j ω₁).coe_nonneg) (le_rfl : (S₂ i ω₂ : ℝ) ≤ S₂ i ω₂)
    have hz' : z ∈ fwdHull (drive κ B₁ ω₁) (S₁ j ω₁) := by
      have e : condT S₁ S₂ i ω₂ ω₁ = S₁ j ω₁ := hjT
      rwa [e] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hC z (Set.mem_iUnion.2 ⟨j, h.K₁ j ω₁ hz'⟩)).trans (le_max_left _ _)
  have hBb := hH.abs_B_le h.κpos h.cont₁ (lt_of_lt_of_le one_pos (le_max_right C 1)) hK
  obtain ⟨ω₀⟩ := nonempty_of_isFilteredBrownianReal h.bm₁
  have : Nonempty Ω₁ := ⟨ω₀⟩
  have hF := hH.toFrzMartHyp
  obtain ⟨w₀, hw₀⟩ := hF.exists_W'_zero_eq
  obtain ⟨nL, nR, e, hL, hR, hLa, hRm⟩ := exists_sort_marks (markPos_injective hF.ne hF.inj) (w₀ := w₀)
    fun o => by have h1 := hF.markPos_ne ω₀ o; rwa [hw₀ ω₀] at h1
  obtain ⟨gW, gL, gR, ζG, hE, hagree, huniq⟩ := hH.exists_isIntegratedSLEEvolution_img_law h.κpos h.bm₁ h.cont₁
    (h.stop₁ i) (h.pos₁ i) hBb e hw₀ hL hR hLa hRm
  rw [girsMeasure_cond_eq rr i ω₂] at hE huniq
  exact ⟨nL, nR, e, w₀, hL, hR, _, _, gW, gL, gR, ζG, hE, hagree, huniq⟩

end DualHyp

end CondLaw

end InteractingSLE.ZhanGT4
