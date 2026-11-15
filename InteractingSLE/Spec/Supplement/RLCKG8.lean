/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCFG8
import InteractingSLE.Spec.Supplement.FlowDilateChart
import InteractingSLE.Spec.Supplement.FlowDilateFlow

/-!
# Lemma G8 at chart coordinates and its affine normalization

Packet PROVE-RLC-K. Source: Lemma G8 and the last paragraph of its proof (supplement §7.7, pp. 499–501,
`source/spec/p481-528.md` L437–L493): "Choose one datum in this positive-probability set where all those conditional
assertions hold. Normalize it affinely so that the current tip coordinates become the prescribed `w₂, w₁`. The
original-real junction then lies in `(w₁, w₁ + ε(w₁ − w₂))`. Choose `ε < dist(J, w₁)/(w₁ − w₂)`. The interval `J`
lies beyond the junction and has height `C`, while the two seed collars retain their canonical heights under this
positive affine map."

The retained datum of G8's proof lives in the chart of the retained pair at the higher-angle tip: the seeds are `0`
(angle `θ₂`) and `w > 0` (angle `θ₁`), and the untouched original-real interval `(v, ∞)` beyond the right junction
`v` has the height `C`. This file states that datum-level form and proves that it implies the frame of the statement:

* `RefCompletable K α₁ ζ₁ α₂ ζ₂`: every pair of prefixes strictly before the lifetimes, whose real points after time
  `0` lie in `K` and which have a common point after time `0`, is completable (the conclusion of `G8FrameStatement`);
* `SeedCollars`, `IsRefFrame`: the canonical seed germs, and the reference property for every coupling;
* `G8ChartRefStatement` (**named**): Lemma G8 with G9 at chart coordinates, the junction within `ε w` of `w`;
* **`g8FrameStatement_of_chartRef`**: `G8FrameStatement` from it, by the affine normalization
  `z ↦ ((w₁ − w₂)/w) z + w₂` (`IsGFFWithBoundaryData.affine_finset`, `IsFlowLine.affine` and
  `IsChartCompletable.affine` of PROVE-RLC-J).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open FlowDilate

/-! ### The reference property -/

/-- **The reference completion property** (the conclusion of `G8FrameStatement`): every pair of prefixes strictly
before the lifetimes, whose real points after time `0` lie in `K` and which have a common point after time `0`, is
completable. -/
def RefCompletable (K : Set ℝ) (α₁ : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (α₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) : Prop :=
  ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) < ζ₁ → (s₂ : ℝ≥0∞) < ζ₂ →
    (∀ t : ℝ≥0, 0 < t → t ≤ s₁ → α₁ t ∈ H ∨ ((α₁ t).im = 0 ∧ (α₁ t).re ∈ K)) →
    (∀ t : ℝ≥0, 0 < t → t ≤ s₂ → α₂ t ∈ H ∨ ((α₂ t).im = 0 ∧ (α₂ t).re ∈ K)) →
    (∃ t₁ t₂ : ℝ≥0, 0 < t₁ ∧ t₁ ≤ s₁ ∧ 0 < t₂ ∧ t₂ ≤ s₂ ∧ α₁ t₁ = α₂ t₂) →
    IsChartCompletable α₁ s₁ α₂ s₂

/-- The reference property for a set `K'` implies it for every smaller set. -/
theorem RefCompletable.mono {K K' : Set ℝ} (hK : K ⊆ K') {α₁ α₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    (h : RefCompletable K' α₁ ζ₁ α₂ ζ₂) : RefCompletable K α₁ ζ₁ α₂ ζ₂ := by
  intro s₁ s₂ hs₁ hs₂ hp₁ hp₂ hc
  refine h s₁ s₂ hs₁ hs₂ (fun t ht hts => ?_) (fun t ht hts => ?_) hc
  · rcases hp₁ t ht hts with h' | ⟨h0, hk⟩
    · exact Or.inl h'
    · exact Or.inr ⟨h0, hK hk⟩
  · rcases hp₂ t ht hts with h' | ⟨h0, hk⟩
    · exact Or.inl h'
    · exact Or.inr ⟨h0, hK hk⟩

/-- **The canonical seed collars of a reference word** (G8 item 1): on the collars of radius `ε` the word has the
canonical germs `−λ − θᵢχ` and `λ − θᵢχ` at `wᵢ`, and no jump candidate in a collar other than its seed. -/
def SeedCollars (κ θ₁ θ₂ : ℝ) (c : ℝ → ℝ) (Ĵ : Finset ℝ) (w₂ w₁ ε : ℝ) : Prop :=
  (∀ x, w₂ - ε < x → x < w₂ → c x = -sleLambda κ - θ₂ * QuantumZipper.chiC κ) ∧
    (∀ x, w₂ < x → x < w₂ + ε → c x = sleLambda κ - θ₂ * QuantumZipper.chiC κ) ∧
    (∀ x, w₁ - ε < x → x < w₁ → c x = -sleLambda κ - θ₁ * QuantumZipper.chiC κ) ∧
    (∀ x, w₁ < x → x < w₁ + ε → c x = sleLambda κ - θ₁ * QuantumZipper.chiC κ) ∧
    (∀ x ∈ Ĵ, |x - w₂| < ε → x = w₂) ∧ (∀ x ∈ Ĵ, |x - w₁| < ε → x = w₁)

/-- **The reference frame property of a word** (G8 items 3–4 with G9): for every GFF with data `c` (jump candidates
`Ĵ`), its angle-`θ₁` flow from `w₁` and its angle-`θ₂` flow from `w₂`, almost surely `RefCompletable K`. -/
def IsRefFrame (κ θ₁ θ₂ : ℝ) (c : ℝ → ℝ) (Ĵ : Finset ℝ) (w₁ w₂ : ℝ) (K : Set ℝ) : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (Ĥ : S → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q Ĥ c Ĵ →
  ∀ (α₁ α₂ : S → ℝ≥0 → ℂ) (ζ₁ ζ₂ : S → ℝ≥0∞),
    IsFlowLine κ c Ĵ w₁ θ₁ Q Ĥ α₁ ζ₁ → IsFlowLine κ c Ĵ w₂ θ₂ Q Ĥ α₂ ζ₂ →
    ∀ᵐ x ∂Q, RefCompletable K (α₁ x) (ζ₁ x) (α₂ x) (ζ₂ x)

/-- **Named statement: Lemma G8 with Lemma G9 at chart coordinates** (supplement pp. 499–501, before the affine
normalization). For `0 < κ < 4`, `θ₁ < θ₂`, a height `C` with `−2 < (C + θ₁χ)/λ − 1 < κ/2 − 2` and every `ε > 0`,
there is a retained datum in the chart of the retained pair at its higher-angle tip: a word `c` with jump candidates
`Ĵ`, the seeds `0` (angle `θ₂`) and `w > 0` (angle `θ₁`) with canonical collars of some radius `δ > 0`, and the right
junction `v` with `w < v < w + εw`, beyond which the word is the untouched original height `C` with no jump; and for
every coupling of its GFF with the two flows, almost surely every pair of prefixes with real points (after time `0`)
beyond the junction and a common point is completable. -/
def G8ChartRefStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ C ε : ℝ, θ₁ < θ₂ → 0 < ε →
    -2 < Sec4.cumWeightRight κ (C + θ₁ * QuantumZipper.chiC κ) →
    Sec4.cumWeightRight κ (C + θ₁ * QuantumZipper.chiC κ) < κ / 2 - 2 →
    ∃ (c : ℝ → ℝ) (Ĵ : Finset ℝ) (w v δ : ℝ), 0 < w ∧ w < v ∧ v < w + ε * w ∧ 0 < δ ∧
      IsPiecewiseConstantBoundaryData c Ĵ ∧ SeedCollars κ θ₁ θ₂ c Ĵ 0 w δ ∧
      (∀ x, v < x → c x = C ∧ x ∉ Ĵ) ∧ IsRefFrame.{u} κ θ₁ θ₂ c Ĵ w 0 (Ioi v)

/-! ### The affine normalization -/

/-- `(x − m)/k` lies strictly between `p` and `q` if `x` lies strictly between `k p + m` and `k q + m`. -/
theorem div_mem_Ioo_of_mem {k m p q x : ℝ} (hk : 0 < k) (h1 : k * p + m < x) (h2 : x < k * q + m) :
    p < (x - m) / k ∧ (x - m) / k < q := by
  constructor
  · rw [lt_div_iff₀ hk]; linarith
  · rw [div_lt_iff₀ hk]; linarith

/-- The affine pull-back of a frame: if `|x − (k w + m)| < k δ` then `|(x − m)/k − w| < δ`. -/
theorem abs_div_sub_lt {k m w δ x : ℝ} (hk : 0 < k) (h : |x - (k * w + m)| < k * δ) : |(x - m) / k - w| < δ := by
  have e : (x - m) / k - w = (x - (k * w + m)) / k := by field_simp; ring
  rw [e, abs_div, abs_of_pos hk, div_lt_iff₀ hk]
  linarith

/-- **Lemma G8 (with G9) from its chart-coordinate form, by the affine normalization** (proof of G8, p. 501). -/
theorem g8FrameStatement_of_chartRef (hR : G8ChartRefStatement.{u}) : G8FrameStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ w₂ w₁ C a b hθ hw ha hab hr₁ hr₂
  have hd : 0 < w₁ - w₂ := sub_pos.2 hw
  obtain ⟨c, Ĵ, w, v, δ, hw0, hwv, hvε, hδ, hc, ⟨gL₂, gR₂, gL₁, gR₁, hJ₂, hJ₁⟩, hC, hRef⟩ :=
    hR κ hκ hκ4 θ₁ θ₂ C ((a - w₁) / (w₁ - w₂)) hθ (div_pos (sub_pos.2 ha) hd) hr₁ hr₂
  set k : ℝ := (w₁ - w₂) / w with hk
  have hk0 : 0 < k := div_pos hd hw0
  have hkw : k * w + w₂ = w₁ := by rw [hk]; field_simp; ring
  have hkv : k * v + w₂ < a := by
    have h1 : k * v < k * (w + (a - w₁) / (w₁ - w₂) * w) := mul_lt_mul_of_pos_left hvε hk0
    have h2 : k * (w + (a - w₁) / (w₁ - w₂) * w) = (w₁ - w₂) + (a - w₁) := by
      rw [hk]; field_simp
    linarith
  have hmemJ : ∀ x, x ∈ affJumps k w₂ Ĵ ↔ (x - w₂) / k ∈ Ĵ := fun x => mem_affJumps hk0.ne'
  refine ⟨affData k w₂ c, affJumps k w₂ Ĵ, k * δ, mul_pos hk0 hδ,
    isPiecewiseConstantBoundaryData_affData hk0 hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x h1 h2
    have := div_mem_Ioo_of_mem (m := w₂) (x := x) (p := -δ) (q := 0) hk0 (by linarith) (by linarith)
    exact gL₂ _ (by linarith [this.1]) this.2
  · intro x h1 h2
    have := div_mem_Ioo_of_mem (m := w₂) (x := x) (p := 0) (q := δ) hk0 (by linarith) (by linarith)
    exact gR₂ _ this.1 (by linarith [this.2])
  · intro x h1 h2
    have := div_mem_Ioo_of_mem (m := w₂) (x := x) (p := w - δ) (q := w) hk0 (by nlinarith) (by linarith)
    exact gL₁ _ this.1 this.2
  · intro x h1 h2
    have := div_mem_Ioo_of_mem (m := w₂) (x := x) (p := w) (q := w + δ) hk0 (by linarith) (by nlinarith)
    exact gR₁ _ this.1 this.2
  · intro x hx hxd
    have h0 := hJ₂ _ ((hmemJ x).1 hx) (abs_div_sub_lt (w := 0) hk0 (by simpa using hxd))
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · linarith
    · exact absurd h0 hk0.ne'
  · intro x hx hxd
    have h0 := hJ₁ _ ((hmemJ x).1 hx) (abs_div_sub_lt (w := w) hk0 (by rw [hkw]; exact hxd))
    rw [div_eq_iff hk0.ne'] at h0
    linarith
  · intro x hx
    have hv : v < (x - w₂) / k := by rw [lt_div_iff₀ hk0]; linarith [hx.1]
    exact ⟨(hC _ hv).1, fun h => (hC _ hv).2 ((hmemJ x).1 h)⟩
  -- the reference property, pulled back by the inverse affine map
  intro S _ Q _ Ĥ hĤ α₁ α₂ ζ₁ ζ₂ h₁ h₂
  have hk' : 0 < k⁻¹ := inv_pos.2 hk0
  have hcR := isPiecewiseConstantBoundaryData_affData (m := w₂) hk0 hc
  have hĤ' := hĤ.affine_finset (a := k⁻¹) (m := -w₂ / k) hk'
  rw [affData_inv hk0.ne', affJumps_inv hk0.ne'] at hĤ'
  have h₁' := h₁.affine (a := k⁻¹) (m := -w₂ / k) hk' hcR
  have h₂' := h₂.affine (a := k⁻¹) (m := -w₂ / k) hk' hcR
  rw [affData_inv hk0.ne', affJumps_inv hk0.ne'] at h₁' h₂'
  have e1 : raff k⁻¹ (-w₂ / k) w₁ = w := by rw [← hkw]; exact raff_inv hk0.ne' w
  have e2 : raff k⁻¹ (-w₂ / k) w₂ = 0 := by
    have := raff_inv (m := w₂) hk0.ne' 0
    simpa [raff] using this
  rw [e1] at h₁'
  rw [e2] at h₂'
  set e : ℝ≥0 := cDil k⁻¹ with he
  have he0 : e ≠ 0 := cDil_ne_zero hk'
  have hek : e * cDil k = 1 := by rw [he, mul_comm]; exact cDil_mul_cDil_inv hk0
  filter_upwards [hRef Q _ hĤ' _ _ _ _ h₁' h₂', Supp9.ae_apply_zero_of_isFlowLine h₁] with x hx hx0
  intro s₁ s₂ hs₁ hs₂ hp₁ hp₂ hcom
  -- the pulled-back times
  have hlt : ∀ (s : ℝ≥0) (ζ : ℝ≥0∞), (s : ℝ≥0∞) < ζ → ((s / e : ℝ≥0) : ℝ≥0∞) < ζ / e := fun s ζ hs => by
    rw [ENNReal.coe_div he0]
    exact ENNReal.div_lt_div_right (ENNReal.coe_ne_zero.2 he0) ENNReal.coe_ne_top hs
  have hmul : ∀ (s t : ℝ≥0), t ≤ s / e → e * t ≤ s := fun s t ht => by
    rw [le_div_iff₀ (pos_iff_ne_zero.2 he0)] at ht
    rwa [mul_comm]
  have hpull : ∀ (g : ℝ≥0 → ℂ) (s : ℝ≥0),
      (∀ t : ℝ≥0, 0 < t → t ≤ s → g t ∈ H ∨ ((g t).im = 0 ∧ (g t).re ∈ Icc a b)) →
      ∀ t : ℝ≥0, 0 < t → t ≤ s / e → aff k⁻¹ (-w₂ / k) (g (e * t)) ∈ H ∨
        ((aff k⁻¹ (-w₂ / k) (g (e * t))).im = 0 ∧ (aff k⁻¹ (-w₂ / k) (g (e * t))).re ∈ Ioi v) := by
    intro g s hp t ht hts
    rcases hp (e * t) (mul_pos (pos_iff_ne_zero.2 he0) ht) (hmul s t hts) with h' | ⟨h0, hre⟩
    · exact Or.inl ((aff_mem_H_iff hk').2 h')
    · refine Or.inr ⟨by simp [h0], ?_⟩
      simp only [aff_re, mem_Ioi]
      have : v < ((g (e * t)).re - w₂) / k := by rw [lt_div_iff₀ hk0]; linarith [hre.1]
      have e3 : k⁻¹ * (g (e * t)).re + -w₂ / k = ((g (e * t)).re - w₂) / k := by field_simp; ring
      rw [e3]; exact this
  have hcomp : IsChartCompletable (fun t => aff k⁻¹ (-w₂ / k) (α₁ x (e * t))) (s₁ / e)
      (fun t => aff k⁻¹ (-w₂ / k) (α₂ x (e * t))) (s₂ / e) := by
    refine hx (s₁ / e) (s₂ / e) (hlt s₁ (ζ₁ x) hs₁) (hlt s₂ (ζ₂ x) hs₂) (hpull (α₁ x) s₁ hp₁)
      (hpull (α₂ x) s₂ hp₂) ?_
    obtain ⟨t₁, t₂, h1, h2, h3, h4, heq⟩ := hcom
    refine ⟨t₁ / e, t₂ / e, div_pos h1 (pos_iff_ne_zero.2 he0), div_le_div_of_nonneg_right h2 (zero_le),
      div_pos h3 (pos_iff_ne_zero.2 he0), div_le_div_of_nonneg_right h4 (zero_le), ?_⟩
    simp only [c_mul_div he0, heq]
  have h10 : ((fun t => aff k⁻¹ (-w₂ / k) (α₁ x (e * t))) 0).im = 0 := by
    simp only [mul_zero, hx0, aff_im, ofReal_im, mul_zero]
  have hA := hcomp.affine (a := k) (m := w₂) (c := cDil k) hk0 (cDil_ne_zero hk0) h10
  have hback : ∀ (g : ℝ≥0 → ℂ),
      (fun t => aff k w₂ ((fun t => aff k⁻¹ (-w₂ / k) (g (e * t))) (cDil k * t))) = g := by
    intro g
    funext t
    simp only
    rw [← mul_assoc, hek, one_mul]
    exact aff_affInv hk0.ne' (g t)
  have hs : ∀ s : ℝ≥0, s / e / cDil k = s := fun s => by rw [div_div, hek, div_one]
  rw [hback, hback, hs, hs] at hA
  exact hA

end RLC

end InteractingSLE
