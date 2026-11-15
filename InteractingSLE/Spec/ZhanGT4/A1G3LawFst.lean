/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LawRect
import InteractingSLE.Foundations.Loewner.YuanCorollary13Slit
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# Zhan's A.1 under R83, (G3), large-curve direction: uniform force gaps of the large curve

Packet PROVE-A1-G3LAW (R83). The large G3 curve (`SLE_κ(κ − 4, −4)` with marks `x`, `y`) has its two force points
uniformly away from its driver up to the rectangle exit, with one gap `δ₂ > 0` and one bound `R` for all large samples
(A1-G3RECTROW's step 5, inside `g3_row`, exposed as a lemma):

* **`g3_large_gaps`**: `PathOn … y (S₂ y) δ₂` at every large sample and `|W₂ − VL₂ i| ≤ R` on `[0, S₂]`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Law

open QuantumZipper (IsForwardSol fwdMap fwdHull)
open A2X A1SeedField A1EightSeed A1EightFin A1G3Calc A1G3Id G3Field A1Common A1G3RR

variable {Y : Type*} [mY : MeasurableSpace Y]

/-- **Uniform force gaps of the large G3 curve** up to a protected exit `S₂` (A1-G3RECTROW's step 5): there are
`δ₂ > 0` and `R` with `PathOn … y (S₂ y) δ₂` and `|W₂ − VL₂ i| ≤ R` on `[0, S₂ y]` at every large sample `y`. -/
theorem g3_large_gaps {P₂ : Measure Y} {κ p : ℝ} {xR : Fin 3 → ℝ} {H₁ H₂ : Set ℂ} {δ q dd Tm : ℝ}
    (hpp : IsProtectedPairG H₁ H₂ δ p q dd) (hxO : 0 < xR 1) (hxOq : xR 1 ≤ q)
    (h0H₁ : ((0 : ℝ) : ℂ) ∈ closure H₁) {𝓕₂ : Filtration ℝ≥0 mY} {xL₂ : Fin 2 → ℝ} {xR₂ ρR₂ : Fin 0 → ℝ}
    {W₂ B₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₂ : A1Marg.IsRegMarginal κ xL₂ xR₂ ![κ - 4, -4] ρR₂ P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hx₂ : xL₂ 0 = xR 1 - p) (hy₂ : xL₂ 1 = -p) {S₂ : Y → ℝ≥0} (hS₂ζ : ∀ y, (S₂ y : ℝ≥0∞) < ζ₂ y)
    (hgood₂ : ∀ y, (S₂ y : ℝ) ≤ Tm ∧ fwdHull (frzPath W₂ p (S₂ y) y) (S₂ y) ⊆ H₂)
    (hK₂ : ∀ y, fwdHull (Strip.extPath (W₂ · y)) (S₂ y) ⊆ transl (-p) H₂) :
    ∃ δ₂ R : ℝ, 0 < δ₂ ∧ ∀ y, PathOn κ xL₂ xR₂ ρR₂ W₂ VL₂ VR₂ B₂ ζ₂ y (S₂ y) δ₂ ∧
      ∀ r : ℝ≥0, r ≤ S₂ y → ∀ i, |W₂ r y - VL₂ i r y| ≤ R := by
  have hpq : xR 1 < p := hxOq.trans_lt hpp.pair.prot_lt
  have hc₂ : ∀ y, ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 (S₂ y : ℝ)) := fun y =>
    A1Ref.continuousOn_extPath_Icc (h₂.path y).2.2.2.1 (by rw [ENNReal.ofReal_coe_nnreal]; exact hS₂ζ y)
  have h0₂ : ∀ y, W₂ 0 y = 0 := fun y => (h₂.path y).1
  set E := transl (-p) H₂ with hEdef
  have hE : IsHPHull E := isHPHull_transl hpp.pair.hull₂ (-p)
  have h0E : (0 : ℂ) ∈ closure E := by
    have := mem_closure_transl hpp.pair.src (-p)
    simpa using this
  have hxneg : ∀ i, xL₂ i < 0 := fun i => by
    fin_cases i
    · show xL₂ 0 < 0
      rw [hx₂]; linarith
    · show xL₂ 1 < 0
      rw [hy₂]; linarith [hxO.trans hpq]
  have hball : ∀ i, Disjoint (ball ((xL₂ i : ℝ) : ℂ) δ) E := fun i => by
    fin_cases i
    · show Disjoint (ball ((xL₂ 0 : ℝ) : ℂ) δ) E
      rw [hx₂]; exact disjoint_ball_mark hpp hxO hxOq
    · show Disjoint (ball ((xL₂ 1 : ℝ) : ℂ) δ) E
      rw [hy₂]; exact disjoint_ball_neg_src hpp.pair h0H₁
  choose c C hc hC hb using fun i => exists_gap_bounds_left hE hpp.pair.sep_pos (hxneg i) (hball i) h0E Tm
  have hWdc : ∀ y, Continuous (A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S₂ y)) := fun y =>
    A1Ref.continuous_stopDrv (hc₂ y) (S₂ y).coe_nonneg
  have hWd0 : ∀ y, A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S₂ y) 0 = 0 := fun y => by
    rw [A1Ref.stopDrv_eqOn _ _ ⟨le_rfl, (S₂ y).coe_nonneg⟩]
    simp [Strip.extPath, h0₂ y]
  have hKd : ∀ y, fwdHull (A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S₂ y)) (S₂ y) ⊆ E := fun y => by
    have h := fwdHull_sub_const_subset (c := p) (hgood₂ y).2
    have e : (fun u => frzPath W₂ p (S₂ y) y u - p) = A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S₂ y) := by
      funext u; simp only [frzPath, add_sub_cancel_right]
    rwa [e] at h
  have hgap : ∀ y (r : ℝ≥0), r ≤ S₂ y → ∀ i, c i ≤ |W₂ r y - VL₂ i r y| ∧ |W₂ r y - VL₂ i r y| ≤ C i := by
    intro y r hr i
    obtain ⟨-, -, -, hcw, hcvL, -, -, -, -, -, -, -, -, hvLeq, -⟩ := id (h₂.path y)
    have hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₂ y →
        VL₂ i t y = xL₂ i + ∫ u in (0 : ℝ)..t, 2 / (VL₂ i u.toNNReal y - W₂ u.toNNReal y) := fun t ht =>
      hvLeq t ht i
    obtain ⟨cy, hcy, hgy⟩ := protected_mark_bounds (h₂.path y) (hcvL i) hveq (hxneg i).ne hE h0E
      hpp.pair.sep_pos (hball i)
    have hsep : ∀ r' ≤ S₂ y, VL₂ i r' y ≠ W₂ r' y := fun r' hr' he => by
      have := (hgy (S₂ y) (hS₂ζ y) (hK₂ y)).1 r' hr'
      simp only at this
      rw [he, sub_self, abs_zero] at this
      linarith
    have hid := fwdMap_stopDrv_add_eq hcw (hcvL i) hveq (hS₂ζ y) hsep hr
    have hWr : A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S₂ y) r = W₂ r y := by
      rw [A1Ref.stopDrv_eqOn _ _ ⟨r.coe_nonneg, NNReal.coe_le_coe.2 hr⟩]
      simp [Strip.extPath]
    have hbd := hb i _ (hWdc y) (hWd0 y) (S₂ y) (S₂ y).coe_nonneg (hgood₂ y).1 (hKd y) r
      ⟨r.coe_nonneg, NNReal.coe_le_coe.2 hr⟩
    have e : W₂ r y - VL₂ i r y =
        -(fwdMap (A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S₂ y)) r (xL₂ i)).re := by
      simp only at hid
      linarith
    rw [e, abs_neg]
    exact hbd
  refine ⟨min (c 0) (c 1), max (C 0) (C 1), lt_min (hc 0) (hc 1), fun y => ⟨⟨h₂.path y, hS₂ζ y,
    lt_min (hc 0) (hc 1), fun r hr i => ?_⟩, fun r hr i => ?_⟩⟩
  · refine le_trans ?_ (hgap y r hr i).1
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  · refine (hgap y r hr i).2.trans ?_
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _

/-- **An image chain transfers to any continuous driver agreeing on `[0, T]`**: `OwnData` reads the driver only through
its hulls, maps and values at times `≤ T` (and its global continuity). -/
theorem ownData_congr_drv {W W₂ : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ}
    (h : OwnData W A φ T a W') (hW₂ : Continuous W₂) (heq : ∀ r ∈ Icc (0 : ℝ) T, W r = W₂ r) :
    OwnData W₂ A φ T a W' := by
  have hH : ∀ t ∈ Icc (0 : ℝ) T, fwdHull W t = fwdHull W₂ t := fun t ht =>
    YuanCorollary13.fwdHull_eq_of_eqOn_Icc h.cont hW₂ ht.1 fun r hr => heq r ⟨hr.1, hr.2.trans ht.2⟩
  have hM : ∀ t ∈ Icc (0 : ℝ) T, fwdMap W t = fwdMap W₂ t := fun t ht => funext fun z =>
    InteractingSLE.fwdMap_eq_of_eqOn ht.1 fun r hr => heq r ⟨hr.1, hr.2.trans ht.2⟩
  have hT : T ∈ Icc (0 : ℝ) T := ⟨h.pos.le, le_rfl⟩
  have h0 : W₂ 0 = 0 := by rw [← heq 0 ⟨le_rfl, h.pos.le⟩]; exact h.zero
  refine ⟨hW₂, h0, h.pos, h.hull, h.mapOut, ?_, h.contW', h.a0, h.mono, h.contA, fun t ht => ?_,
    fun t ht R hR => ?_⟩
  · rw [← hH T hT]; exact h.disj
  · rw [← hH t ht]; exact h.img t ht
  · have hWt := heq t ht
    have hR' : IsMapOut ((fun z => fwdMap W t z + W t) '' A) R := by rw [hM t ht, hWt]; exact hR
    have := h.rate t ht R hR'
    rw [hM t ht, hH t ht, hWt] at this
    exact this

end InteractingSLE.ZhanGT4.A1G3Law
