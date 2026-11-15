/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59NodesSub
import InteractingSLE.Spec.ZhanGT4.CrosscutA3Scale

/-!
# Dilated candidate pieces

Packet PROVE-PROP59-NODETREE. Specification §5.2, proof of Proposition 5.9 (p. 143): "Rescale it so that the marked
points `z₋, z₊` in Figure 5.7 satisfy `z₋ ≤ −3` and `z₊ ≥ 3`." A node experiment uses the joint chart of the root,
dilated by a factor `c > 0` chosen from the marks at the node tip. Brownian scaling of the Loewner equation turns a
piece `(W, V, B, ζ, clk)` of the chart into the piece `(c W(·/c²), c V(·/c²), c B(·/c²), c² ζ, clk(·/c²))` of the
dilated chart; this file defines that piece and proves that it inherits regularity and gap-free chain data:

* `scalePiece`, `scaleFam`;
* **`IsRegFam.scaleFam`**;
* `isLoewnerTraceLT_scale`: `t ↦ c η(t/c²)` is a Loewner trace of `t ↦ c W(t/c²)` (QuantumZipper's hull scaling
  `mem_fwdHull_scale_iff`, hull filling commutes with dilations `fillH_image_affHomeo`);
* **`IsChainAll.scale`**: the dilated family has chain data with the start `c² · start` and the image set `c · C`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59NodeTree

open Prop59System Prop59Stage Prop59Pieces Prop59Nodes

/-! ### Dilated pieces -/

section Piece

variable {Ω : Type*}

/-- **The dilated piece**: Brownian scaling by the factor `c ω`. -/
def scalePiece {nL nR : ℕ} (c : Ω → ℝ≥0) (p : Piece Ω nL nR) : Piece Ω nL nR where
  W u ω := (c ω : ℝ) * p.W (u / c ω ^ 2) ω
  VL i u ω := (c ω : ℝ) * p.VL i (u / c ω ^ 2) ω
  VR k u ω := (c ω : ℝ) * p.VR k (u / c ω ^ 2) ω
  B u ω := (c ω : ℝ) * p.B (u / c ω ^ 2) ω
  ζ ω := ((c ω ^ 2 : ℝ≥0) : ℝ≥0∞) * p.ζ ω
  clk ω u := p.clk ω (u / c ω ^ 2)

/-- **The dilated candidate family.** -/
def scaleFam {nL₀ nR₀ : ℕ} (c : Ω → ℝ≥0) (cand : CandFam Ω nL₀ nR₀) : CandFam Ω nL₀ nR₀ :=
  fun j t => scalePiece c (cand j t)

theorem coe_lt_scale_iff {c : ℝ≥0} (hc : 0 < c) {u : ℝ≥0} {ζ : ℝ≥0∞} :
    (u : ℝ≥0∞) < ((c ^ 2 : ℝ≥0) : ℝ≥0∞) * ζ ↔ ((u / c ^ 2 : ℝ≥0) : ℝ≥0∞) < ζ := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc.ne'
  rw [ENNReal.coe_div hc2, ENNReal.div_lt_iff (Or.inl (ENNReal.coe_ne_zero.2 hc2)) (Or.inl ENNReal.coe_ne_top),
    mul_comm]

theorem div_sq_mul {c : ℝ≥0} (hc : 0 < c) (u : ℝ≥0) : (c : ℝ) ^ 2 * ((u / c ^ 2 : ℝ≥0) : ℝ) = u := by
  have hc' : (c : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hc.ne'
  rw [NNReal.coe_div, NNReal.coe_pow]
  field_simp

variable [MeasurableSpace Ω]

theorem measurable_div_sq {c : Ω → ℝ≥0} (hc : Measurable c) :
    Measurable fun x : ℝ≥0 × Ω => (x.1 / c x.2 ^ 2, x.2) :=
  (measurable_fst.div ((hc.comp measurable_snd).pow_const 2)).prodMk measurable_snd

theorem measurable_uncurry_scale {c : Ω → ℝ≥0} (hc : Measurable c) {X : ℝ≥0 → Ω → ℝ}
    (hX : Measurable (uncurry X)) : Measurable (uncurry fun u ω => (c ω : ℝ) * X (u / c ω ^ 2) ω) :=
  ((measurable_coe_nnreal_real.comp hc).comp measurable_snd).mul (hX.comp (measurable_div_sq hc))

theorem continuousOn_scale {c : ℝ≥0} (hc : 0 < c) {X : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hX : ContinuousOn X {u | (u : ℝ≥0∞) < ζ}) :
    ContinuousOn (fun u => (c : ℝ) * X (u / c ^ 2)) {u | (u : ℝ≥0∞) < ((c ^ 2 : ℝ≥0) : ℝ≥0∞) * ζ} :=
  continuousOn_const.mul (hX.comp (continuous_id.div_const _).continuousOn fun _ hu => (coe_lt_scale_iff hc).1 hu)

/-- **A dilated regular piece is regular.** -/
theorem isRegPiece_scalePiece {nL nR : ℕ} {c : Ω → ℝ≥0} (hc : Measurable c) (hpos : ∀ ω, 0 < c ω)
    {p : Piece Ω nL nR} (hp : IsRegPiece p) : IsRegPiece (scalePiece c p) where
  W := measurable_uncurry_scale hc hp.W
  VL i := measurable_uncurry_scale hc (hp.VL i)
  VR k := measurable_uncurry_scale hc (hp.VR k)
  ζ := (measurable_coe_nnreal_ennreal.comp (hc.pow_const 2)).mul hp.ζ
  clk s := by
    have hj : Measurable (uncurry fun (u : ℝ≥0) (ω : Ω) => p.clk ω u) :=
      measurable_uncurry_of_continuous_of_measurable (fun ω => hp.clk_cont ω) hp.clk
    exact hj.comp ((measurable_const.div (hc.pow_const 2)).prodMk measurable_id)
  clk_cont ω := (hp.clk_cont ω).comp (continuous_id.div_const _)
  clk_mono ω := fun a b hab => hp.clk_mono ω ((div_lt_div_iff_of_pos_right (pow_pos (hpos ω) 2)).2 hab)
  W_cont ω := continuousOn_scale (hpos ω) (hp.W_cont ω)
  VL_cont ω i := continuousOn_scale (hpos ω) (hp.VL_cont ω i)
  VR_cont ω k := continuousOn_scale (hpos ω) (hp.VR_cont ω k)

/-- **A dilated regular family is regular.** -/
theorem IsRegFam.scaleFam {nL₀ nR₀ : ℕ} {c : Ω → ℝ≥0} (hc : Measurable c) (hpos : ∀ ω, 0 < c ω)
    {cand : CandFam Ω nL₀ nR₀} (h : IsRegFam cand) : IsRegFam (Prop59NodeTree.scaleFam c cand) :=
  fun j t => isRegPiece_scalePiece hc hpos (h j t)

end Piece

/-! ### Dilated Loewner traces -/

section Trace

/-- **Brownian scaling of a Loewner trace**: `t ↦ a η(t/a²)` is a Loewner trace of `t ↦ a W(t/a²)` before `a² T`. -/
theorem isLoewnerTraceLT_scale {W : ℝ → ℝ} {T : ℝ} {η : ℝ → ℂ} (h : IsLoewnerTraceLT W T η) {a : ℝ} (ha : 0 < a) :
    IsLoewnerTraceLT (fun r => a * W (r / a ^ 2)) (a ^ 2 * T) (fun r => (a : ℂ) * η (r / a ^ 2)) := by
  have ha2 : 0 < a ^ 2 := by positivity
  refine ⟨by simp only [zero_div, h.1, mul_zero], ?_, fun t ht0 htT => ?_⟩
  · refine continuousOn_const.mul (h.2.1.comp (continuous_id.div_const _).continuousOn fun r hr => ?_)
    refine ⟨div_nonneg hr.1 ha2.le, ?_⟩
    rw [div_lt_iff₀ ha2, mul_comm]
    exact hr.2
  · set σ := t / a ^ 2 with hσ
    have hσ0 : 0 ≤ σ := div_nonneg ht0 ha2.le
    have hσT : σ < T := by rw [hσ, div_lt_iff₀ ha2, mul_comm]; exact htT
    have ht : t = a ^ 2 * σ := by rw [hσ]; field_simp
    have hW : (fun s => (fun r => a * W (r / a ^ 2)) (a ^ 2 * s) / a) = W := by
      funext s
      have : a ^ 2 * s / a ^ 2 = s := by field_simp
      simp only [this]
      field_simp
    have hmul : ∀ X : Set ℂ, ZhanGT4.A34.mulHomeo ha '' X = affHomeo a ha 0 '' X := fun X => by
      congr 1
      funext z
      rw [ZhanGT4.A34.mulHomeo_apply, coe_affHomeo]
      simp
    have himg : ZhanGT4.A34.mulHomeo ha '' (η '' Icc 0 σ) =
        (fun r => (a : ℂ) * η (r / a ^ 2)) '' Icc 0 t := by
      ext z
      constructor
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        refine ⟨a ^ 2 * u, ⟨mul_nonneg ha2.le hu.1, ?_⟩, ?_⟩
        · rw [ht]; exact mul_le_mul_of_nonneg_left hu.2 ha2.le
        · simp only [ZhanGT4.A34.mulHomeo_apply]
          congr 2
          field_simp
      · rintro ⟨r, hr, rfl⟩
        refine ⟨η (r / a ^ 2), ⟨r / a ^ 2, ⟨div_nonneg hr.1 ha2.le, ?_⟩, rfl⟩, rfl⟩
        rw [hσ]
        exact div_le_div_of_nonneg_right hr.2 ha2.le
    rw [ht, ZhanGT4.A34.fwdHull_eq_image_of_scale ha hσ0, hW, h.2.2 σ hσ0 hσT, ← ht, ← himg, hmul, hmul,
      fillH_image_affHomeo]

end Trace

/-! ### Dilated chain data -/

section Chain

variable {Ω : Type*} [MeasurableSpace Ω] {nL₀ nR₀ : ℕ}

/-- **Dilated gap-free chain data**: the dilated family has chain data with the start `c² · start` and the image set
`c · C`. -/
theorem IsChainAll.scale {P : Measure Ω} {cand : CandFam Ω nL₀ nR₀} {C : Ω → Set ℂ}
    {start : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ} (h : IsChainAll P cand C start) (c : Ω → ℝ≥0)
    (hpos : ∀ ω, 0 < c ω) :
    IsChainAll P (Prop59NodeTree.scaleFam c cand) (fun ω => (fun z => ((c ω : ℝ) : ℂ) * z) '' C ω)
      (fun j t ω => (c ω : ℝ) ^ 2 * start j t ω) where
  start_zero := h.start_zero.mono fun ω hω => by simp only [hω, mul_zero]
  step j t q := (h.step j t q).mono fun ω hω s hs hsζ => by
    have e := hω (s / c ω ^ 2) hs ((coe_lt_scale_iff (hpos ω)).1 hsζ)
    rw [e, mul_add, div_sq_mul (hpos ω)]
  trace j t := (h.trace j t).mono fun ω hω s hs => by
    have ha : (0 : ℝ) < c ω := NNReal.coe_pos.2 (hpos ω)
    obtain ⟨W', η, T, hc, hW0, hη, hT, himg⟩ := hω (s / c ω ^ 2) ((coe_lt_scale_iff (hpos ω)).1 hs)
    have hs' : (c ω : ℝ) ^ 2 * start j t ω + s = (c ω : ℝ) ^ 2 * (start j t ω + ((s / c ω ^ 2 : ℝ≥0) : ℝ)) := by
      rw [mul_add, div_sq_mul (hpos ω)]
    refine ⟨fun r => (c ω : ℝ) * W' (r / (c ω : ℝ) ^ 2), fun r => ((c ω : ℝ) : ℂ) * η (r / (c ω : ℝ) ^ 2),
      (c ω : ℝ) ^ 2 * T, (continuous_const.mul (hc.comp (continuous_id.div_const _))),
      by simp only [zero_div, hW0, mul_zero], isLoewnerTraceLT_scale hη ha, ?_, ?_⟩
    · rw [hs']
      exact mul_lt_mul_of_pos_left hT (by positivity)
    · rintro _ ⟨r, hr, rfl⟩
      have hr' : r / (c ω : ℝ) ^ 2 ∈ Icc 0 (start j t ω + ((s / c ω ^ 2 : ℝ≥0) : ℝ)) := by
        refine ⟨div_nonneg hr.1 (by positivity), ?_⟩
        rw [div_le_iff₀ (by positivity), mul_comm, ← hs']
        exact hr.2
      have hmem := himg ⟨_, hr', rfl⟩
      have hcl : (fun z => ((c ω : ℝ) : ℂ) * z) '' closure (C ω) =
          closure ((fun z => ((c ω : ℝ) : ℂ) * z) '' C ω) :=
        (ZhanGT4.A34.mulHomeo ha).image_closure (C ω)
      rw [← hcl]
      exact ⟨_, hmem, rfl⟩

end Chain

end InteractingSLE.Sec5.Prop59NodeTree
