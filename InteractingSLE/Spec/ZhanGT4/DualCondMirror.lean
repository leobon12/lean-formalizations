/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualCondLaw

/-!
# The mirror conditional law of the stopped dual coupling on one rectangle

Packet PROVE-ZHAN-GT4-A18. Source: Astra, *Follow-up proofs*, §A.1 (`source/external/AstraIG1/ig1_followup_proofs.txt`
L160–L166, L344–L357, L401–L403, R38): "conditionally on any stopping-time prefix of curve `k`, curve `j`, mapped by the
hydrodynamic map of that prefix …, has the corresponding force-point law" — here `j = 2`, `k = 1` (A17's
`DualHyp.exists_condLaw₁` is `j = 1`), and "Reflection of the construction proves the corresponding martingale in the
other coordinate".

For one rectangle `i`, in coordinates translated by `−x₂` (curve `2` is `√(16/κ) B₂`, curve `1` is `√κ B₁ − x₂`):

* `DualHyp.rectDens_eq₂`: by (D6) on the staircase (`normLog_sEll_eq_tEll`), the rectangle density factors as
  `Ñ_t(S₁ i, S₂ i)/Ñ_t(S₁ i, 0) · Ñ(S₁ i, 0)/Ñ(0, 0)`;
* `DualHyp.dualCoupling_rect_eq₂`: `dualCoupling (A ×ˢ B) = ∫_A Q'_{ω₁}(B) · Ñ(S₁ i, 0)/Ñ(0, 0) dP₁`, with
  `Q'_{ω₁} = (Ñ_t(x, S₂ i)/Ñ_t(x, 0)) · P₂`, `x = S₁ i (ω₁)` (`condMeasure₂`);
* **`DualHyp.exists_condLaw₂`**: for every curve-`1` path, under `Q'_{ω₁}` the image of curve `2` in the chart of the
  frozen hull `K₁(x)` is an integrated `SLE_{16/κ}(ρ)` evolution of the image word (the frozen tip `W₁(x) − x₂` with
  weight `−8/κ`, the images `g_x(p_m − x₂)` with weights `(16/κ)(−κ/4) r_m`) up to `a(S₂ i)`, with the killed laws of
  every such evolution.
-/

set_option autoImplicit false

noncomputable section

open Finset Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull drive)

section CondMirror

variable {Ω₁ Ω₂ : Type*} {ι : Type*} [Fintype ι] {n : ℕ}

/-- **The conditional law of curve `2` on rectangle `i` given the curve-`1` path `ω₁`**:
`(Ñ_t(x, S₂ i)/Ñ_t(x, 0)) · P₂` with `x = S₁ i (ω₁)` (A12's tilted measure for curve `2` with the frozen hull
`K₁(x)`). -/
def condMeasure₂ {mΩ₂ : MeasurableSpace Ω₂} (κ : ℝ) (rr p : Fin n → ℝ) (P₂ : Measure Ω₂) (B₁ : ℝ≥0 → Ω₁ → ℝ)
    (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ) (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (i : ι) (ω₁ : Ω₁) : Measure Ω₂ :=
  P₂.withDensity fun ω₂ => ENNReal.ofReal (Real.exp (pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ (S₁ i ω₁) (S₂ i ω₂) -
    pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ (S₁ i ω₁) 0))

/-- The curve-`1` path in coordinates translated by `−x₂`: `√κ B₁ − x₂`. -/
def path₁ (κ : ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (x₂ : ℝ) (ω₁ : Ω₁) : ℝ → ℝ := fun u => drive κ B₁ ω₁ u - x₂

/-- The width of the curve-`2` selection at the frozen height `S₁ i` (the staircase width). -/
def condT₂ (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (i : ι) (ω₁ : Ω₁) (ω₂ : Ω₂) : ℝ :=
  stairH (fun j => (S₁ j ω₁ : ℝ)) (fun j => (S₂ j ω₂ : ℝ)) (S₁ i ω₁)

/-- The canonical image clock of curve `2` in the chart of the frozen hull `K₁(S₁ i)` (`t`-view selection, translated
coordinates). -/
def condA₂ (κ : ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ) (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0)
    (i : ι) (ω₁ : Ω₁) (ω₂ : Ω₂) : ℝ → ℝ :=
  (imgSelD (drive (16 / κ) B₂ ω₂) (path₁ κ B₁ x₂ ω₁) (condT₂ S₁ S₂ i ω₁ ω₂) (S₁ i ω₁)).1

/-- The canonical image driver of curve `2` in the chart of the frozen hull `K₁(S₁ i)`. -/
def condW₂ (κ : ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ) (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0)
    (i : ι) (ω₁ : Ω₁) (ω₂ : Ω₂) : ℝ → ℝ :=
  (imgSelD (drive (16 / κ) B₂ ω₂) (path₁ κ B₁ x₂ ω₁) (condT₂ S₁ S₂ i ω₁ ω₂) (S₁ i ω₁)).2

/-- The image marks of the mirror word: the frozen tip `W₁(x) − x₂` (`none`) and the images `g_x(p_m − x₂)`,
`x = S₁ i (ω₁)`. -/
def condMark₂ (κ : ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (x₂ : ℝ) (p : Fin n → ℝ) (S₁ : ι → Ω₁ → ℝ≥0) (i : ι) (ω₁ : Ω₁) :
    Option (Fin n) → ℝ :=
  markPos (path₁ κ B₁ x₂ ω₁ (S₁ i ω₁)) (frzMarks (path₁ κ B₁ x₂ ω₁) (fun m => p m - x₂) (S₁ i ω₁))

variable {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂} {κ : ℝ} {P₁ : Measure Ω₁}
  {𝓕₁ : Filtration ℝ≥0 mΩ₁} {B₁ : ℝ≥0 → Ω₁ → ℝ} {P₂ : Measure Ω₂} {𝓕₂ : Filtration ℝ≥0 mΩ₂}
  {B₂ : ℝ≥0 → Ω₂ → ℝ} {x₂ : ℝ} {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ} {p : Fin n → ℝ} {Tm : ℝ}
  {S₁ : ι → Ω₁ → ℝ≥0} {S₂ : ι → Ω₂ → ℝ≥0}

namespace DualHyp

variable (h : DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ H₁ H₂ δ q d p Tm S₁ S₂)
include h

/-- **The rectangle density in the mirror factorization**: by (D6) on the staircase, `M(S₁ i, S₂ i)` is also the
normalised `t`-view density, so the rectangle density is `Ñ_t(x, y)/Ñ_t(x, 0) · Ñ(x, 0)/Ñ(0, 0)`,
`(x, y) = (S₁ i, S₂ i)`. -/
theorem rectDens_eq₂ (rr : Fin n → ℝ) (i : ι) (ω : Ω₁ × Ω₂) :
    rectDens κ rr p B₁ B₂ x₂ S₁ S₂ i ω =
      Real.exp (pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 (S₁ i ω.1) (S₂ i ω.2) -
        pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 (S₁ i ω.1) 0) *
      Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 (S₁ i ω.1) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 0 0) := by
  have hE := h.twoEncl ω.1 ω.2
  have hN : normLog (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2) (S₁ i ω.1) (S₂ i ω.2) =
      normLog (pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2) (S₁ i ω.1) (S₂ i ω.2) :=
    normLog_sEll_eq_tEll h.κpos.ne' hE.cont₁ hE.cont₂ hE.twoViewRect hE.twoViewMarks (S₁ i ω.1).coe_nonneg
      (S₂ i ω.2).coe_nonneg ⟨i, le_rfl, le_rfl⟩
  unfold rectDens
  rw [hN]
  unfold normLog
  simp only [← Real.exp_add]
  congr 1; ring

/-- **The stopped dual coupling on rectangle `i`, disintegrated over curve `1`**: for an event `A` of curve `1`
stopped at `S₁ i` and an event `B` of curve `2` stopped at `S₂ i`,
`dualCoupling (A ×ˢ B) = ∫_A Q'_{ω₁}(B) · Ñ(S₁ i, 0)/Ñ(0, 0) dP₁` (`condMeasure₂`). -/
theorem dualCoupling_rect_eq₂ [Nonempty ι] (rr : Fin n → ℝ) (i : ι) {A : Set Ω₁} {B : Set Ω₂}
    (hA : MeasurableSet[(h.stop₁ i).measurableSpace] A) (hB : MeasurableSet[(h.stop₂ i).measurableSpace] B) :
    dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm (A ×ˢ B) =
      ∫⁻ ω₁ in A, condMeasure₂ κ rr p P₂ B₁ B₂ x₂ S₁ S₂ i ω₁ B *
        ENNReal.ofReal (Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ (nonempty_of_isFilteredBrownianReal h.bm₂).some
          (S₁ i ω₁) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ (nonempty_of_isFilteredBrownianReal h.bm₂).some 0 0)) ∂P₁ := by
  have := h.isProbabilityMeasure₁
  have := h.isProbabilityMeasure₂
  have hBm : MeasurableSet B := (h.stop₂ i).measurableSpace_le _ hB
  have hR : Measurable (rectDens κ rr p B₁ B₂ x₂ S₁ S₂ i) := (h.measurable_condDens rr i).2
  set ω₂₀ := (nonempty_of_isFilteredBrownianReal h.bm₂).some
  rw [h.dualCoupling_rect rr i hA hB, ← Measure.prod_restrict, lintegral_prod _ hR.ennreal_ofReal.aemeasurable]
  refine lintegral_congr fun ω₁ => ?_
  rw [condMeasure₂, withDensity_apply _ hBm, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ω₂ => ?_
  rw [h.rectDens_eq₂, ENNReal.ofReal_mul (Real.exp_pos _).le, h.pairS_zero_congr rr ω₁ ω₂ ω₂₀,
    h.pairS_zero_congr rr ω₁ ω₂ ω₂₀ 0]

omit [Fintype ι] in
/-- The curve-`2` path at time `0` is `x₂`. -/
theorem drive₂_zero_add (ω₂ : Ω₂) : drive (16 / κ) B₂ ω₂ 0 + x₂ = x₂ := by
  rw [QuantumZipper.drive_zero (h.zero₂ ω₂), zero_add]

/-- **The `t`-view data of rectangle `i` at the frozen height `S₁ i (ω₁)`, in the variables of A12**: the image data
`(condA₂, condW₂)` of curve `2` (`√(16/κ) B₂`) in the chart of the frozen translated hull `K₁(S₁ i) − x₂`
(`TwoEncl.tView_encl`). -/
theorem ownData_cond₂ (i : ι) (ω₁ : Ω₁) (ω₂ : Ω₂) :
    OwnData (drive (16 / κ) B₂ ω₂) (fwdHull (path₁ κ B₁ x₂ ω₁) (S₁ i ω₁)) (frzChart (path₁ κ B₁ x₂ ω₁) (S₁ i ω₁))
      (condT₂ S₁ S₂ i ω₁ ω₂) (condA₂ κ B₁ B₂ x₂ S₁ S₂ i ω₁ ω₂) (condW₂ κ B₁ B₂ x₂ S₁ S₂ i ω₁ ω₂) := by
  have hE := h.twoEncl ω₁ ω₂
  have hu : (S₁ i ω₁ : ℝ) ∈ Icc (0 : ℝ) (S₁ i ω₁) := ⟨(S₁ i ω₁).coe_nonneg, le_rfl⟩
  obtain ⟨-, hown, -, -⟩ := hE.tView_encl i hu
  unfold tSelA tSelW at hown
  simp only [h.drive₂_zero_add ω₂, add_sub_cancel_right] at hown
  exact hown

/-- **The frozen-hull hypotheses of A12 for curve `2` at the frozen height `S₁ i (ω₁)`**, curve `2` stopped at `S₂ i`
(the (D9) constants of `exists_twoCurveD9_left_family` for the translated enclosures, uniform over the rectangle
attaining the staircase width). -/
theorem exists_frzD10Hyp_cond₂ (rr : Fin n → ℝ) (i : ι) (ω₁ : Ω₁) : ∃ r a₀ γ Γ lam L : ℝ,
    FrzD10Hyp (16 / κ) B₂ (condW₂ κ B₁ B₂ x₂ S₁ S₂ i ω₁) (condA₂ κ B₁ B₂ x₂ S₁ S₂ i ω₁)
      (fwdHull (path₁ κ B₁ x₂ ω₁) (S₁ i ω₁)) (frzChart (path₁ κ B₁ x₂ ω₁) (S₁ i ω₁)) (fun m => -(κ / 4) * rr m)
      (path₁ κ B₁ x₂ ω₁ (S₁ i ω₁)) (frzMarks (path₁ κ B₁ x₂ ω₁) (fun m => p m - x₂) (S₁ i ω₁)) (S₂ i)
      (condT₂ S₁ S₂ i ω₁) r a₀ γ Γ lam L Tm := by
  set G : ι → Set ℂ := fun j => transl (-x₂) (H₂ j) with hG
  set F : ι → Set ℂ := fun j => transl (-x₂) (H₁ j) with hF
  have hsep' : ∀ j, ∀ a ∈ F j, ∀ z ∈ G j, 2 * δ j ≤ ‖a - z‖ := fun j =>
    sep_transl (fun a ha z hz => by rw [norm_sub_rev]; exact h.sep j z hz a ha) (-x₂)
  have hunion : ∀ j, transl (-x₂) (H₁ j ∪ H₂ j) = G j ∪ F j := fun j => by
    simp only [hG, hF, transl, Set.image_union, Set.union_comm]
  have hpH' : ∀ j m, Disjoint (Metric.ball (((fun m => p m - x₂) m : ℝ) : ℂ) (2 * d j)) (G j ∪ F j) := fun j m => by
    have := disjoint_ball_transl (h.pH j m) (-x₂)
    rw [hunion j] at this
    simpa [sub_eq_add_neg] using this
  have hqH' : ∀ j, Disjoint (Metric.ball ((q j - x₂ : ℝ) : ℂ) (2 * d j)) (G j ∪ F j) := fun j => by
    have := disjoint_ball_transl (h.qH j) (-x₂)
    rw [hunion j] at this
    simpa [sub_eq_add_neg] using this
  have hpinj' : Function.Injective (fun m => p m - x₂) := fun m k hmk => h.pinj (by simpa using hmk)
  obtain ⟨ω₂₀⟩ := nonempty_of_isFilteredBrownianReal h.bm₂
  have hc₁ : Continuous (path₁ κ B₁ x₂ ω₁) := (h.twoEncl ω₁ ω₂₀).cont₁.sub continuous_const
  have hV0F : ∀ j, ((path₁ κ B₁ x₂ ω₁ 0 : ℝ) : ℂ) ∈ closure (F j) := fun j => by
    have := mem_closure_transl ((h.twoEncl ω₁ ω₂₀).zero_mem_closure j) (-x₂)
    have e : path₁ κ B₁ x₂ ω₁ 0 = -x₂ := by
      simp only [path₁, (h.twoEncl ω₁ ω₂₀).zero₁, zero_sub]
    rw [e]
    simpa using this
  have hV0q : ∀ j, path₁ κ B₁ x₂ ω₁ 0 < q j - x₂ := fun j => by
    simp only [path₁, (h.twoEncl ω₁ ω₂₀).zero₁]
    linarith [h.qpos j]
  obtain ⟨r, a₀, γ, Γ, lam, hr, ha, hg, hmain⟩ := exists_twoCurveD9_left_family
    (fun j => isHPHull_transl (h.hull₂ j) (-x₂)) (fun j => isHPHull_transl (h.hull₁ j) (-x₂)) h.δpos hsep' h.dpos
    (fun j => by linarith [h.qx j] : ∀ j, q j - x₂ < 0) hqH' hpH' hpinj' Tm
  obtain ⟨L, hL⟩ := exists_scaleOK hr ha hg Γ lam Tm
  have hj : ∀ ω₂, ∃ j, (S₁ i ω₁ : ℝ) ≤ S₁ j ω₁ ∧ condT₂ S₁ S₂ i ω₁ ω₂ = S₂ j ω₂ := fun ω₂ =>
    exists_eq_stairH (S₁ := fun j => (S₁ j ω₁ : ℝ)) (S₂ := fun j => (S₂ j ω₂ : ℝ)) (fun j => (S₂ j ω₂).coe_nonneg)
      (le_rfl : (S₁ i ω₁ : ℝ) ≤ S₁ i ω₁)
  have hD : ∀ ω₂, TwoCurveD9 (frzDataOf (16 / κ) B₂ (condW₂ κ B₁ B₂ x₂ S₁ S₂ i ω₁) (condA₂ κ B₁ B₂ x₂ S₁ S₂ i ω₁)
      (frzChart (path₁ κ B₁ x₂ ω₁) (S₁ i ω₁)) (fun m => -(κ / 4) * rr m) (path₁ κ B₁ x₂ ω₁ (S₁ i ω₁))
      (frzMarks (path₁ κ B₁ x₂ ω₁) (fun m => p m - x₂) (S₁ i ω₁)) ω₂) (fwdHull (path₁ κ B₁ x₂ ω₁) (S₁ i ω₁))
      (condT₂ S₁ S₂ i ω₁ ω₂) r a₀ γ Γ lam := fun ω₂ => by
    obtain ⟨j, hij, hjT⟩ := hj ω₂
    have hK₂ : fwdHull (drive (16 / κ) B₂ ω₂) (condT₂ S₁ S₂ i ω₁ ω₂) ⊆ G j := by
      have := fwdHull_sub_const_subset (c := x₂) (h.K₂ j ω₂)
      rwa [drive₂_sub ω₂, ← hjT] at this
    have hK₁ : fwdHull (path₁ κ B₁ x₂ ω₁) (S₁ i ω₁) ⊆ F j := by
      have := fwdHull_sub_const_subset (c := x₂) (((QuantumZipper.fwdHull_mono).1 hij).trans (h.K₁ j ω₁))
      exact this
    exact hmain j (drive (16 / κ) B₂ ω₂) (path₁ κ B₁ x₂ ω₁) (S₁ i ω₁) (condT₂ S₁ S₂ i ω₁ ω₂)
      (condA₂ κ B₁ B₂ x₂ S₁ S₂ i ω₁ ω₂) (condW₂ κ B₁ B₂ x₂ S₁ S₂ i ω₁ ω₂) (16 / κ) (fun m => -(κ / 4) * rr m)
      (h.ownData_cond₂ i ω₁ ω₂) hc₁ (hV0F j) (hV0q j) (S₁ i ω₁).coe_nonneg (h.le₁ i ω₁)
      (by rw [hjT]; exact h.le₂ j ω₂) hK₂ hK₁
  refine ⟨r, a₀, γ, Γ, lam, L, ⟨⟨fun ω₂ => h.ownData_cond₂ i ω₁ ω₂,
    fun ω₂ => ((h.twoEncl ω₁ ω₂).tView_encl i ⟨(S₁ i ω₁).coe_nonneg, le_rfl⟩).1, fun ω₂ => ?_,
    fun ω₂ => (hD ω₂).alive₀, fun ω₂ m => (hD ω₂).alive m, (hD ω₂₀).ne, (hD ω₂₀).inj, fun ω₂ => (hD ω₂).d9, hL⟩,
    fun ω₂ t ht => (hD ω₂).drv t ht⟩⟩
  obtain ⟨j, -, hjT⟩ := hj ω₂
  rw [hjT]; exact h.le₂ j ω₂

omit h in
/-- **A12's tilted measure for curve `2` at the frozen height `S₁ i (ω₁)` is the conditional law `condMeasure₂`.** -/
theorem girsMeasure_cond₂_eq (hB₂0 : ∀ ω₂, B₂ 0 ω₂ = 0) (rr : Fin n → ℝ) (i : ι) (ω₁ : Ω₁) :
    girsMeasure P₂ (Real.sqrt (16 / κ)) B₂ (S₂ i) (fun ω₂ => (frzDataOf (16 / κ) B₂ (condW₂ κ B₁ B₂ x₂ S₁ S₂ i ω₁)
      (condA₂ κ B₁ B₂ x₂ S₁ S₂ i ω₁) (frzChart (path₁ κ B₁ x₂ ω₁) (S₁ i ω₁)) (fun m => -(κ / 4) * rr m)
      (path₁ κ B₁ x₂ ω₁ (S₁ i ω₁)) (frzMarks (path₁ κ B₁ x₂ ω₁) (fun m => p m - x₂) (S₁ i ω₁)) ω₂).ell) =
      condMeasure₂ κ rr p P₂ B₁ B₂ x₂ S₁ S₂ i ω₁ := by
  unfold girsMeasure condMeasure₂
  congr 1
  funext ω₂
  have hd : ∀ s : ℝ≥0, drive (16 / κ) B₂ ω₂ (s : ℝ) = Real.sqrt (16 / κ) * B₂ s ω₂ := fun s => by
    simp only [drive, Real.toNNReal_coe]
  have hc : drive (16 / κ) B₂ ω₂ 0 + x₂ = x₂ := by rw [QuantumZipper.drive_zero (hB₂0 ω₂), zero_add]
  unfold girsDensity pairT tEll tView tSelA tSelW
  simp only [hc, add_sub_cancel_right, sub_self]
  rw [hd, hB₂0 ω₂, mul_zero]
  rfl

/-- **(D10), mirror: the conditional law of curve `2` given the curve-`1` prefix, inside rectangle `i`** (§A.1 with
`j = 2`, `k = 1`). For every curve-`1` path `ω₁`, under `Q'_{ω₁}` (`condMeasure₂`, the conditional law of curve `2` on
`F²_{S₂ i}` given the curve-`1` prefix up to `x = S₁ i (ω₁)`, `dualCoupling_rect_eq₂`), the image of curve `2`
(translated by `−x₂`) in the chart `g_x` of the frozen translated hull `K₁(x) − x₂` — capacity clock `condA₂`, image
driver `condW₂` — together with the image marks (the frozen tip `W₁(x) − x₂` with weight `−8/κ`, the images
`g_x(p_m − x₂)` with weights `(16/κ)(−κ/4) r_m`, sorted by `e` around `w₀`) is, up to `a(S₂ i)`, an integrated
`SLE_{16/κ}(ρ)` evolution of the image word, and its killed laws are those of every integrated evolution of that word
(A12's `exists_isIntegratedSLEEvolution_img_law`). -/
theorem exists_condLaw₂ [Nonempty ι] (rr : Fin n → ℝ) (i : ι) (ω₁ : Ω₁) :
    ∃ (nL nR : ℕ) (e : Fin nL ⊕ Fin nR ≃ Option (Fin n)) (w₀ : ℝ),
      (∀ k, condMark₂ κ B₁ x₂ p S₁ i ω₁ (e (Sum.inl k)) < w₀) ∧
      (∀ k, w₀ < condMark₂ κ B₁ x₂ p S₁ i ω₁ (e (Sum.inr k))) ∧
      ∃ (𝓗 : Filtration ℝ≥0 mΩ₂) (Bh gW : ℝ≥0 → Ω₂ → ℝ) (gL : Fin nL → ℝ≥0 → Ω₂ → ℝ)
        (gR : Fin nR → ℝ≥0 → Ω₂ → ℝ) (ζG : Ω₂ → ℝ≥0∞),
        IsIntegratedSLEEvolution (16 / κ) (fun k => condMark₂ κ B₁ x₂ p S₁ i ω₁ (e (Sum.inl k)) - w₀)
          (fun k => condMark₂ κ B₁ x₂ p S₁ i ω₁ (e (Sum.inr k)) - w₀)
          (fun k => markWt (16 / κ) (fun m => -(κ / 4) * rr m) (e (Sum.inl k)))
          (fun k => markWt (16 / κ) (fun m => -(κ / 4) * rr m) (e (Sum.inr k)))
          (condMeasure₂ κ rr p P₂ B₁ B₂ x₂ S₁ S₂ i ω₁) 𝓗 gW gL gR Bh ζG ∧
        (∀ ω₂, ENNReal.ofReal (condA₂ κ B₁ B₂ x₂ S₁ S₂ i ω₁ ω₂ (S₂ i ω₂)) ≤ ζG ω₂ ∧ ∀ t : ℝ≥0,
          (t : ℝ) < condA₂ κ B₁ B₂ x₂ S₁ S₂ i ω₁ ω₂ (S₂ i ω₂) →
            gW t ω₂ = condW₂ κ B₁ B₂ x₂ S₁ S₂ i ω₁ ω₂ t - w₀ ∧
            (∀ k, gL k t ω₂ = imgV (condW₂ κ B₁ B₂ x₂ S₁ S₂ i ω₁ ω₂) (condMark₂ κ B₁ x₂ p S₁ i ω₁ (e (Sum.inl k))) t -
              w₀) ∧
            ∀ k, gR k t ω₂ = imgV (condW₂ κ B₁ B₂ x₂ S₁ S₂ i ω₁ ω₂) (condMark₂ κ B₁ x₂ p S₁ i ω₁ (e (Sum.inr k))) t -
              w₀) ∧
        ∀ {Ω₃ : Type*} {m₃ : MeasurableSpace Ω₃} {P₃ : Measure Ω₃} [IsProbabilityMeasure P₃]
          {𝓕₃ : Filtration ℝ≥0 m₃} {W₃ : ℝ≥0 → Ω₃ → ℝ} {VL₃ : Fin nL → ℝ≥0 → Ω₃ → ℝ}
          {VR₃ : Fin nR → ℝ≥0 → Ω₃ → ℝ} {B₃ : ℝ≥0 → Ω₃ → ℝ} {ζ₃ : Ω₃ → ℝ≥0∞},
          IsIntegratedSLEEvolution (16 / κ) (fun k => condMark₂ κ B₁ x₂ p S₁ i ω₁ (e (Sum.inl k)) - w₀)
          (fun k => condMark₂ κ B₁ x₂ p S₁ i ω₁ (e (Sum.inr k)) - w₀)
            (fun k => markWt (16 / κ) (fun m => -(κ / 4) * rr m) (e (Sum.inl k)))
            (fun k => markWt (16 / κ) (fun m => -(κ / 4) * rr m) (e (Sum.inr k))) P₃ 𝓕₃ W₃ VL₃ VR₃ B₃ ζ₃ →
          ∀ (m : ℕ) (ts : Fin m → ℝ≥0) (Asets : Fin m → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
            (∀ j, MeasurableSet (Asets j)) →
            condMeasure₂ κ rr p P₂ B₁ B₂ x₂ S₁ S₂ i ω₁
                {ω | ∀ j, (ts j : ℝ≥0∞) < ζG ω ∧ (gW (ts j) ω, (fun k => gL k (ts j) ω),
                  (fun k => gR k (ts j) ω), Bh (ts j) ω) ∈ Asets j} =
              P₃ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₃ ω ∧
                (W₃ (ts j) ω, (fun k => VL₃ k (ts j) ω), (fun k => VR₃ k (ts j) ω), B₃ (ts j) ω) ∈ Asets j} := by
  obtain ⟨r, a₀, γ, Γ, lam, L, hH⟩ := h.exists_frzD10Hyp_cond₂ rr i ω₁
  obtain ⟨C, hC⟩ := (Bornology.isBounded_iUnion.2 fun j => (h.hull₂ j).2.1).exists_norm_le
  have hK : ∀ ω₂, fwdHull (drive (16 / κ) B₂ ω₂) (condT₂ S₁ S₂ i ω₁ ω₂) ⊆
      Metric.closedBall (0 : ℂ) (max (C + |x₂|) 1) := fun ω₂ z hz => by
    obtain ⟨j, -, hjT⟩ := exists_eq_stairH (S₁ := fun j => (S₁ j ω₁ : ℝ)) (S₂ := fun j => (S₂ j ω₂ : ℝ))
      (fun j => (S₂ j ω₂).coe_nonneg) (le_rfl : (S₁ i ω₁ : ℝ) ≤ S₁ i ω₁)
    have e : condT₂ S₁ S₂ i ω₁ ω₂ = S₂ j ω₂ := hjT
    rw [e] at hz
    have hz' := fwdHull_sub_const_subset (c := x₂) (h.K₂ j ω₂) (by rwa [drive₂_sub ω₂])
    rw [mem_transl_iff] at hz'
    have h1 := hC _ (Set.mem_iUnion.2 ⟨j, hz'⟩)
    rw [Metric.mem_closedBall, dist_zero_right]
    have e2 : z = (z - ((-x₂ : ℝ) : ℂ)) + ((-x₂ : ℝ) : ℂ) := by ring
    calc ‖z‖ ≤ ‖z - ((-x₂ : ℝ) : ℂ)‖ + ‖((-x₂ : ℝ) : ℂ)‖ := by
          conv_lhs => rw [e2]
          exact norm_add_le _ _
      _ ≤ C + |x₂| := by rw [Complex.norm_real, Real.norm_eq_abs, abs_neg]; linarith
      _ ≤ _ := le_max_left _ _
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) h.κpos
  have hBb := hH.abs_B_le hκ' h.cont₂ (lt_of_lt_of_le one_pos (le_max_right (C + |x₂|) 1)) hK
  obtain ⟨ω₀⟩ := nonempty_of_isFilteredBrownianReal h.bm₂
  have : Nonempty Ω₂ := ⟨ω₀⟩
  have hF := hH.toFrzMartHyp
  obtain ⟨w₀, hw₀⟩ := hF.exists_W'_zero_eq
  obtain ⟨nL, nR, e, hL, hR, hLa, hRm⟩ := exists_sort_marks (markPos_injective hF.ne hF.inj) (w₀ := w₀)
    fun o => by have h1 := hF.markPos_ne ω₀ o; rwa [hw₀ ω₀] at h1
  obtain ⟨gW, gL, gR, ζG, hE, hagree, huniq⟩ := hH.exists_isIntegratedSLEEvolution_img_law hκ' h.bm₂ h.cont₂
    (h.stop₂ i) (h.pos₂ i) hBb e hw₀ hL hR hLa hRm
  rw [girsMeasure_cond₂_eq h.zero₂ rr i ω₁] at hE huniq
  exact ⟨nL, nR, e, w₀, hL, hR, _, _, gW, gL, gR, ζG, hE, hagree, huniq⟩

end DualHyp

end CondMirror

end InteractingSLE.ZhanGT4
