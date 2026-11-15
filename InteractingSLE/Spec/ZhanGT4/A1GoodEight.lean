/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1GoodTime
import InteractingSLE.Spec.ZhanGT4.A1ELawFst
import InteractingSLE.Spec.ZhanGT4.A2Part3PCFinLife
import InteractingSLE.Spec.ZhanGT4.A1SeedGeomLocal

/-!
# Zhan's A.1, (Eight): the rectangle exits are good times

Packet PROVE-A1-GOODTIME. For the patched Eight marginals (regular, continuous Brownian paths, `GoodSmallEight` at every
sample) and a frozen small time `σ` protected by the small exit (`σ ≤ S₁ᵐ(x₀)`), the large exit `S₂ᵐ(y₀)` is a good
time (`A1Ref.IsGoodTime`) of the large curve's image chain against the frozen small hull, in the frame of
`EightRectLawFstC`'s canonical data (large curve at `0`, small curve at `x < 0`):

* **`eightFst_isGoodTime_drive`**: for the continuous replacement driver `drive κ B₂ y₀` (`√κ B₂`, lifetime `⊤`);
* **`eightFst_isGoodTime`**: for the large curve's own driver `extPath W₂` with the canonical lifetime `lifeEnd` (the
  end of the strip life of its inner mark `x`): the mark is protected by the enclosure, so it stays strictly left of
  the driver up to the exit (`eightFst_lt_lifeEnd`).

Both follow from `A1Good.isGoodTime_of_sep`: the two hulls lie in the translated enclosures, `2δ` apart
(`A1ELaw.eightFst_frame`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Good

open QuantumZipper (H fwdHull drive)
open A2X A1Ref A1Common A1EightSeed A1ELaw A1SeedField A1Asm A1Marg A1EightFin

/-- A path continuous before its lifetime is continuous on `[0, T']` for some `T'` beyond any pre-lifetime time. -/
theorem exists_gt_continuousOn_extPath {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) : ∃ T' : ℝ, (T : ℝ) < T' ∧ ContinuousOn (Strip.extPath w) (Icc 0 T') := by
  obtain ⟨r, -, hTr, hrζ⟩ := ENNReal.lt_iff_exists_real_btwn.1 hT
  refine ⟨r, ?_, A1Ref.continuousOn_extPath_Icc hw hrζ⟩
  rw [← ENNReal.ofReal_coe_nnreal] at hTr
  exact (ENNReal.ofReal_lt_ofReal_iff'.1 hTr).1

section Eight

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ}
  {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ}
  {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

/-- **The frozen small hull at a protected time lies in the translated small enclosure.** -/
theorem eight_small_physHull_subset (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) {σ : ℝ≥0} (hσ : σ ≤ eightS₁ x W₁ ζ₁ m x₀) :
    physHull x (Strip.extPath (W₁ · x₀)) σ ⊆ transl (-(-x)) (cofH₁ (-x) ![] m) := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  obtain ⟨-, hgood₁, -⟩ := eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hlt : (eightS₁ x W₁ ζ₁ m x₀ : ℝ≥0∞) < ζ₁ x₀ := (hgood₁ m x₀).1
  obtain ⟨-, -, -, -, -, -, -, hK₁⟩ :=
    eightFst_frame hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ (s := σ) (NNReal.coe_le_coe.2 hσ)
  obtain ⟨T', hT', hcT'⟩ := exists_gt_continuousOn_extPath (h₁.path x₀).2.2.2.1 hlt
  have hdc : Continuous (eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀) :=
    continuous_eightDrv (h₁.path x₀).2.2.2.1 hlt
  have heq : EqOn (Strip.extPath (W₁ · x₀)) (eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀) (Icc 0 (σ : ℝ)) :=
    fun u hu => (A1Ref.stopDrv_eqOn _ _ ⟨hu.1, hu.2.trans (NNReal.coe_le_coe.2 hσ)⟩).symm
  rw [A1SeedGeom.physHull_congr_of_continuousOn hcT' hdc.continuousOn σ.coe_nonneg
    ((NNReal.coe_le_coe.2 hσ).trans_lt hT') heq]
  have e := A1G3Row.fwdHull_sub_const_eq_physHull (eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀) (-x) σ
  rw [neg_neg] at e
  rw [← e]
  exact hK₁

/-- **(Eight, large direction) the large exit is a good time for the continuous replacement driver** `√κ B₂`
(lifetime `⊤`), at every frozen small time protected by the small exit. -/
theorem eightFst_isGoodTime_drive (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) (y₀ : Y) {σ : ℝ≥0} (hσ : σ ≤ eightS₁ x W₁ ζ₁ m x₀) :
    IsGoodTime 0 (drive κ B₂ y₀) ⊤ x (Strip.extPath (W₁ · x₀)) σ (eightS₂ x W₂ ζ₂ m y₀) := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  obtain ⟨hdc, -, hS₂pos, -, hsep, -, hK₂, -⟩ :=
    eightFst_frame hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ (s := σ) (NNReal.coe_le_coe.2 hσ)
  refine isGoodTime_of_sep (A := transl (-(-x)) (cofH₂ (-x) ![] m)) (T' := eightS₂ x W₂ ζ₂ m y₀ + 1) (by linarith)
    (hdc y₀).continuousOn (hS₂pos y₀)
    ENNReal.ofReal_lt_top (mul_pos two_pos (hF.pp m).sep_pos) ?_
    (eight_small_physHull_subset hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ hσ) fun a ha b hb => ?_
  · rw [A1Ref.physHull_zero]; exact hK₂ y₀
  · rw [norm_sub_rev]; exact hsep b hb a ha

/-- **(Eight, large direction) the large exit is strictly inside the strip life of the inner mark**: the mark `x`
(the small curve's source) is protected by the enclosure, so it stays strictly left of the driver up to the exit. -/
theorem eightFst_lt_lifeEnd (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) (y₀ : Y) :
    (eightS₂ x W₂ ζ₂ m y₀ : ℝ≥0∞) < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀) := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  obtain ⟨-, -, -, hc₂, -, -, -, hlt₂⟩ := eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  obtain ⟨hdc, -, -, -, -, hdrive, hK₂, -⟩ := eightFst_frame hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀
    (s := 0) (NNReal.coe_nonneg _)
  set S := eightS₂ x W₂ ζ₂ m y₀ with hS
  obtain ⟨hw0, -, -, hcw, hcvL, -, -, -, -, -, -, -, -, hvLeq, -⟩ := id (h₂.path y₀)
  have hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₂ y₀ →
      VL₂ 0 t y₀ = x + ∫ s in (0 : ℝ)..t, 2 / (VL₂ 0 s.toNNReal y₀ - W₂ s.toNNReal y₀) := fun t ht => by
    simpa using hvLeq t ht 0
  have hρ : 0 < cofδ (-x) ![] m := (hF.pp m).sep_pos
  have hxE : Disjoint (ball (x : ℂ) (cofδ (-x) ![] m)) (transl (-(-x)) (cofH₂ (-x) ![] m)) := by
    have h := hF.disjoint_ball_neg_src m
    simpa only [neg_neg] using h
  obtain ⟨c, hc, hgap⟩ := protected_mark_bounds (h₂.path y₀) (hcvL 0) hveq hx.ne (hF.hull₂ m)
    (hF.zero_mem_closure₂ m) hρ hxE
  obtain ⟨T', hT', hcT'⟩ := exists_gt_continuousOn_extPath hcw (hlt₂ m y₀)
  have hK : fwdHull (Strip.extPath (W₂ · y₀)) S ⊆ transl (-(-x)) (cofH₂ (-x) ![] m) := by
    have e := A1SeedGeom.physHull_congr_of_continuousOn (x := 0) hcT' (hdc y₀).continuousOn S.coe_nonneg hT'
      (fun u hu => (hdrive y₀ u hu).symm)
    rw [A1Ref.physHull_zero, A1Ref.physHull_zero] at e
    rw [e]; exact hK₂ y₀
  have hgS := (hgap S (hlt₂ m y₀) hK).1
  refine A2X.P3.lt_lifeEnd_of_isStripLife hcw (hcvL 0) ⟨hlt₂ m y₀, fun r hr => ?_⟩
  have hrζ : (r : ℝ≥0∞) < ζ₂ y₀ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) (hlt₂ m y₀)
  have hle := A1G3Calc.vL_le_of_path (h₂.path y₀) 0 hrζ (W := Strip.extPath (W₂ · y₀)) (fun _ _ => rfl) r
    ⟨r.coe_nonneg, le_rfl⟩
  simp only [extPath_coe] at hle
  refine lt_of_le_of_ne hle fun hEq => ?_
  have := hgS r hr
  rw [hEq, sub_self, abs_zero] at this
  linarith

/-- **(Eight, large direction) the large exit is a good time for the large curve's own driver** with the canonical
lifetime `lifeEnd`, at every frozen small time protected by the small exit. -/
theorem eightFst_isGoodTime (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) (y₀ : Y) {σ : ℝ≥0} (hσ : σ ≤ eightS₁ x W₁ ζ₁ m x₀) :
    IsGoodTime 0 (Strip.extPath (W₂ · y₀)) (lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀)) x
      (Strip.extPath (W₁ · x₀)) σ (eightS₂ x W₂ ζ₂ m y₀) := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  obtain ⟨-, -, -, -, -, -, -, hlt₂⟩ := eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  obtain ⟨hdc, -, hS₂pos, -, hsep, hdrive, hK₂, -⟩ :=
    eightFst_frame hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ (s := σ) (NNReal.coe_le_coe.2 hσ)
  set S := eightS₂ x W₂ ζ₂ m y₀ with hS
  obtain ⟨T', hT', hcT'⟩ := exists_gt_continuousOn_extPath (h₂.path y₀).2.2.2.1 (hlt₂ m y₀)
  have hlife := eightFst_lt_lifeEnd hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ y₀
  refine isGoodTime_of_sep (A := transl (-(-x)) (cofH₂ (-x) ![] m)) hT' hcT' (hS₂pos y₀)
    (by rwa [ENNReal.ofReal_coe_nnreal])
    (mul_pos two_pos (hF.pp m).sep_pos) ?_ (eight_small_physHull_subset hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ hσ)
    fun a ha b hb => ?_
  · show physHull 0 (Strip.extPath (W₂ · y₀)) (S : ℝ) ⊆ transl (-(-x)) (cofH₂ (-x) ![] m)
    rw [A1SeedGeom.physHull_congr_of_continuousOn (x := 0) hcT' (hdc y₀).continuousOn S.coe_nonneg hT'
      (fun u hu => (hdrive y₀ u hu).symm), A1Ref.physHull_zero]
    exact hK₂ y₀
  · rw [norm_sub_rev]; exact hsep b hb a ha

end Eight

end InteractingSLE.ZhanGT4.A1Good
