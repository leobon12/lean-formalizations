import QuantumZipper.Proofs.Section5.Prop17Point
import QuantumZipper.Statements.Prop16
import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.LQG.AllOffsets
import QuantumZipper.Proofs.Abstract.PalmShift

/-!
# Proposition 1.7: the length-`L` point of a canonical zoom is a Palm shift (S5-PLAN node D5-b)

Sheffield, arXiv:1012.4797, proof of Proposition 1.7 (§1.6): in the pre-limit of Proposition 1.6
(zoom `h(· + x) + C/γ` at a quantum-typical point `x`), moving to the point at quantum length `L`
to the right of the origin of the zoomed surface is the same as moving the Palm point `x` to the
right by quantum length `ℓ = L e^{−C/2}` in the unzoomed field (blueprint SECTION5 D5: "adding
`C/γ` turns this shift into the shift by `L`, and canonicalization commutes with it").

This file proves the point-level identity, deterministically, for a good sample `h`
(`IsLQGGood`, so that `translate`, `addConst` and `rescale` act on `ν_h` exactly: M4-T1/T2/T3):

* `qBoundaryMeasure_canonical_zoomField`: `ν_{canonical(h(·+x)+C/γ)} = e^{C/2} · φ_* ν_h` with
  `φ t = (t − x)/a`, `a = scaleParam γ (h(·+x)+C/γ)`;
* `wedgeLengthPoint_canonical_zoomField`: `wedgeLengthPoint γ L (canonical γ (zoomField γ C h x))
  = (z − x)/a`, where `z = x + lenPoint (ν_h.map (· − x)) ℓ` is the unique point with
  `ν_h[x, z] = ℓ`;
* `palmShiftRight_eq`: `z = palmShiftRight ν_h ℓ x`, the right Palm shift of blueprint A6
  (`Abstract/PalmShift.lean`), so A6's TV bound applies.

Regularity of `ν_h` (atomless, positive on intervals, `ν_h[x,∞) = ∞`) is a hypothesis; for the
free field it holds a.s. (`AtomlessUncond`, positivity, `InfiniteMass`). Own elementary proof
(affine change of variables and the uniqueness clause of `lenPoint_spec`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace S5

section Affine

variable {x a : ℝ}

theorem measurable_affineInv (x a : ℝ) : Measurable fun t : ℝ => (t - x) / a :=
  (measurable_id.sub_const x).div_const a

theorem preimage_affineInv_Icc (ha : 0 < a) (y : ℝ) :
    (fun t : ℝ => (t - x) / a) ⁻¹' Icc 0 y = Icc x (x + a * y) := by
  ext t
  simp only [mem_preimage, mem_Icc]
  rw [le_div_iff₀ ha, div_le_iff₀ ha, zero_mul]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith [mul_comm a y]⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith [mul_comm a y]⟩

theorem preimage_affineInv_Ioo (ha : 0 < a) (u v : ℝ) :
    (fun t : ℝ => (t - x) / a) ⁻¹' Ioo u v = Ioo (x + a * u) (x + a * v) := by
  ext t
  simp only [mem_preimage, mem_Ioo]
  rw [lt_div_iff₀ ha, div_lt_iff₀ ha]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith [mul_comm a u], by linarith [mul_comm a v]⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith [mul_comm a u], by linarith [mul_comm a v]⟩

theorem preimage_affineInv_singleton (ha : 0 < a) (s : ℝ) :
    (fun t : ℝ => (t - x) / a) ⁻¹' {s} = {x + a * s} := by
  ext t
  simp only [mem_preimage, mem_singleton_iff]
  rw [div_eq_iff ha.ne']
  constructor
  · intro h; linarith [mul_comm a s]
  · intro h; linarith [mul_comm a s]

theorem preimage_affineInv_Ici (ha : 0 < a) :
    (fun t : ℝ => (t - x) / a) ⁻¹' Ici 0 = Ici x := by
  ext t
  simp only [mem_preimage, mem_Ici]
  rw [le_div_iff₀ ha, zero_mul, sub_nonneg]

end Affine

section Regular

variable {ν : Measure ℝ}

/-- Regularity of `ν` transfers to `c • ν.map φ`, `φ t = (t − x)/a`, `0 < c < ⊤`. -/
theorem regular_smul_map_affineInv {x a : ℝ} (ha : 0 < a) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hatom : ∀ t : ℝ, ν {t} = 0) (hpos : ∀ u v : ℝ, u < v → 0 < ν (Ioo u v))
    (hinf : ν (Ici x) = ⊤) :
    (∀ t : ℝ, (c • ν.map fun t => (t - x) / a) {t} = 0) ∧
      (∀ u v : ℝ, u < v → 0 < (c • ν.map fun t => (t - x) / a) (Ioo u v)) ∧
      (c • ν.map fun t => (t - x) / a) (Ici 0) = ⊤ := by
  have hm := measurable_affineInv x a
  refine ⟨fun t => ?_, fun u v huv => ?_, ?_⟩
  · rw [Measure.smul_apply, Measure.map_apply hm (measurableSet_singleton t),
      preimage_affineInv_singleton ha, hatom, smul_zero]
  · rw [Measure.smul_apply, Measure.map_apply hm measurableSet_Ioo, preimage_affineInv_Ioo ha,
      smul_eq_mul]
    exact ENNReal.mul_pos hc0 (hpos _ _ (by nlinarith)).ne'
  · rw [Measure.smul_apply, Measure.map_apply hm measurableSet_Ici, preimage_affineInv_Ici ha,
      hinf, smul_eq_mul, ENNReal.mul_top hc0]

/-- The Palm point: `z = x + lenPoint (ν.map (· − x)) ℓ` has `ν[x, z] = ℓ`, `z > x`, and it is
the only `z' > x` with `ν[x, z'] = ℓ`. -/
theorem palmPoint_spec {x ℓ : ℝ} (hℓ : 0 < ℓ) (hatom : ∀ t : ℝ, ν {t} = 0)
    (hpos : ∀ u v : ℝ, u < v → 0 < ν (Ioo u v)) (hfin : ∀ y : ℝ, ν (Icc x y) ≠ ⊤)
    (hinf : ν (Ici x) = ⊤) :
    0 < lenPoint (ν.map (· - x)) ℓ ∧
      ν (Icc x (x + lenPoint (ν.map (· - x)) ℓ)) = ENNReal.ofReal ℓ ∧
      ∀ z' : ℝ, x < z' → ν (Icc x z') = ENNReal.ofReal ℓ →
        z' = x + lenPoint (ν.map (· - x)) ℓ := by
  have key : ν.map (· - x) = (1 : ℝ≥0∞) • ν.map fun t => (t - x) / 1 := by
    simp only [one_smul, div_one]
  have hIcc : ∀ y : ℝ, (ν.map (· - x)) (Icc 0 y) = ν (Icc x (x + y)) := by
    intro y
    rw [key, one_smul, Measure.map_apply (measurable_affineInv x 1) measurableSet_Icc,
      preimage_affineInv_Icc one_pos, one_mul]
  obtain ⟨h1, h2, h3⟩ := regular_smul_map_affineInv (x := x) one_pos one_ne_zero hatom hpos hinf
  rw [← key] at h1 h2 h3
  obtain ⟨hp, he, hu⟩ := lenPoint_spec hℓ h1 h2 (fun y => by rw [hIcc]; exact hfin _) h3
  refine ⟨hp, by rw [← hIcc]; exact he, fun z' hz' hz'e => ?_⟩
  have := hu (z' - x) (sub_pos.2 hz') (by rw [hIcc, add_sub_cancel]; exact hz'e)
  linarith

/-- The Palm point is the right Palm shift `palmShiftRight ν ℓ x` of blueprint A6. -/
theorem palmShiftRight_eq {x : ℝ} {ℓ : ℝ≥0} (hℓ : 0 < ℓ) (hatom : ∀ t : ℝ, ν {t} = 0)
    (hpos : ∀ u v : ℝ, u < v → 0 < ν (Ioo u v)) (hfin : ∀ y : ℝ, ν (Icc x y) ≠ ⊤)
    (hinf : ν (Ici x) = ⊤) :
    PalmShift.palmShiftRight ν ℓ x = x + lenPoint (ν.map (· - x)) ℓ := by
  obtain ⟨hp, he, -⟩ := palmPoint_spec (x := x) (ℓ := (ℓ : ℝ)) (NNReal.coe_pos.2 hℓ) hatom hpos
    hfin hinf
  set z := x + lenPoint (ν.map (· - x)) ℓ with hz
  have hxz : x < z := by rw [hz]; linarith
  -- strict monotonicity of `y ↦ ν[x, y]` on `[x, ∞)`
  have hsplit : ∀ {y y' : ℝ}, x ≤ y → y ≤ y' → ν (Icc x y') = ν (Icc x y) + ν (Ioc y y') :=
    fun hy hyy' => by
      rw [← Icc_union_Ioc_eq_Icc hy hyy']
      exact measure_union (Set.disjoint_left.2 fun t ht ht' => (not_lt.2 ht.2) ht'.1)
        measurableSet_Ioc
  have hlt : ∀ {y y' : ℝ}, x ≤ y → y < y' → ν (Icc x y) < ν (Icc x y') := fun hy hyy' => by
    rw [hsplit hy hyy'.le]
    exact ENNReal.lt_add_right (hfin _)
      ((hpos _ _ hyy').trans_le (measure_mono Ioo_subset_Ioc_self)).ne'
  have hℓe : ((ℓ : ℝ≥0∞)) = ENNReal.ofReal (ℓ : ℝ) := by simp
  unfold PalmShift.palmShiftRight
  apply le_antisymm
  · refine csSup_le ⟨x, le_rfl, ?_⟩ fun y ⟨hxy, hy⟩ => ?_
    · rw [hℓe, ← he]; exact measure_mono (Icc_subset_Icc_right hxz.le)
    · by_contra hzy
      push Not at hzy
      have := hlt hxz.le hzy
      rw [he, ← hℓe] at this
      exact absurd hy (not_le.2 this)
  · refine le_csSup ⟨z, fun y ⟨_, hy⟩ => ?_⟩ ⟨hxz.le, by rw [hℓe, he]⟩
    by_contra hzy
    push Not at hzy
    have := hlt hxz.le hzy
    rw [he, ← hℓe] at this
    exact absurd hy (not_le.2 this)

end Regular

section Zoom

variable {γ : ℝ} {h : FieldSample}

/-- **M4-T1/T2/T3 composed.** For a good sample, the boundary measure of the canonical zoom
`canonical γ (h(· + x) + C/γ)` is `e^{C/2} · φ_* ν_h`, `φ t = (t − x)/a`,
`a = scaleParam γ (zoomField γ C h x)`. -/
theorem qBoundaryMeasure_canonical_zoomField (hγ : 0 < γ) (hg : IsLQGGood γ h) (x C : ℝ)
    (ha : 0 < scaleParam γ (zoomField γ C h x)) :
    qBoundaryMeasure γ (canonical γ (zoomField γ C h x)) =
      ENNReal.ofReal (Real.exp (C / 2)) •
        (qBoundaryMeasure γ h).map fun t => (t - x) / scaleParam γ (zoomField γ C h x) := by
  set a := scaleParam γ (zoomField γ C h x) with haDef
  have hZ : IsLQGGood γ (zoomField γ C h x) := (hg.translate x).addConst (C / γ)
  have hexp : γ * (C / γ) / 2 = C / 2 := by field_simp
  rw [canonical, ← haDef, GoodTransforms.qBoundaryMeasure_rescale hZ hγ ha, zoomField,
    GoodSample.qBoundaryMeasure_addConst (hg.translate x), AllOffsets.qBoundaryMeasure_translate hg,
    hexp, Measure.map_smul, Measure.map_map (f := fun t : ℝ => t - x) (g := fun u : ℝ => u / a)
      (measurable_id.div_const a) (measurable_id.sub_const x)]
  · rfl
  · exact (measurable_id.div_const a).aemeasurable

/-- **D5-b (point identity).** For a good sample `h` whose boundary measure is atomless, positive
on intervals, finite on `[x, y]` and infinite on `[x, ∞)`, the length-`L` point of the canonical
zoom `canonical γ (h(·+x)+C/γ)` is `(z − x)/a` with `z = palmShiftRight ν_h ℓ x`,
`ℓ = L e^{−C/2}` and `a = scaleParam γ (zoomField γ C h x)`. -/
theorem wedgeLengthPoint_canonical_zoomField (hγ : 0 < γ) (hg : IsLQGGood γ h) {x C L : ℝ}
    (hL : 0 < L) (ha : 0 < scaleParam γ (zoomField γ C h x))
    (hatom : ∀ t : ℝ, qBoundaryMeasure γ h {t} = 0)
    (hpos : ∀ u v : ℝ, u < v → 0 < qBoundaryMeasure γ h (Ioo u v))
    (hinf : qBoundaryMeasure γ h (Ici x) = ⊤) :
    wedgeLengthPoint γ L (canonical γ (zoomField γ C h x)) =
      (PalmShift.palmShiftRight (qBoundaryMeasure γ h) (Real.toNNReal (L * Real.exp (-C / 2))) x
        - x) / scaleParam γ (zoomField γ C h x) := by
  set ν := qBoundaryMeasure γ h with hν
  set a := scaleParam γ (zoomField γ C h x) with haDef
  have hne : ν ≠ 0 := by
    intro h0
    have h1 := hpos 0 1 one_pos
    rw [h0] at h1
    simp at h1
  have := isLocallyFiniteMeasure_qBoundaryMeasure hne
  have hfin : ∀ y : ℝ, ν (Icc x y) ≠ ⊤ := fun _ => measure_Icc_lt_top.ne
  set ℓ : ℝ := L * Real.exp (-C / 2) with hℓ
  have hℓ0 : 0 < ℓ := mul_pos hL (Real.exp_pos _)
  obtain ⟨hp, he, -⟩ := palmPoint_spec (x := x) hℓ0 hatom hpos hfin hinf
  have hshift := palmShiftRight_eq (ν := ν) (x := x) (ℓ := Real.toNNReal ℓ)
    (Real.toNNReal_pos.2 hℓ0) hatom hpos hfin hinf
  rw [Real.coe_toNNReal _ hℓ0.le] at hshift
  rw [hshift, add_sub_cancel_left]
  -- the canonical zoom's boundary measure and its regularity
  have hc0 : ENNReal.ofReal (Real.exp (C / 2)) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hmeas := qBoundaryMeasure_canonical_zoomField hγ hg x C ha
  rw [← hν, ← haDef] at hmeas
  obtain ⟨r1, r2, r3⟩ := regular_smul_map_affineInv (ν := ν) (x := x) ha hc0 hatom hpos hinf
  rw [← hmeas] at r1 r2 r3
  obtain ⟨-, -, hu⟩ := wedgeLengthPoint_spec hL r1 r2 r3
  refine (hu _ (div_pos hp ha) ?_).symm
  rw [hmeas, Measure.smul_apply, Measure.map_apply (measurable_affineInv x a) measurableSet_Icc,
    preimage_affineInv_Icc ha, mul_div_cancel₀ _ ha.ne', he, smul_eq_mul,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, hℓ, ← mul_assoc, mul_comm (Real.exp (C / 2)) L,
    mul_assoc, ← Real.exp_add]
  congr 1
  rw [show C / 2 + -C / 2 = 0 by ring, Real.exp_zero, mul_one]

end Zoom

end S5
end QuantumZipper
