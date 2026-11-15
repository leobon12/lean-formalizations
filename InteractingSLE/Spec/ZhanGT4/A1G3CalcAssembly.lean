/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3CalcG3Rec
import InteractingSLE.Spec.ZhanGT4.A1G3CalcStatement
import InteractingSLE.Spec.ZhanGT4.A1EightSeedAssembly

/-!
# Zhan's A.1, G3: the rectangle-wise seeded input from the concrete G3 records

Packet PROVE-A1-G3CALC (R48, R80). A1-EIGHTSEED's `seedFieldInputM_of_eight` for G3: with `d = g3Rec` (the small
curve's two seeds and its ordinary mark `x`), every record clause of `SeedFieldInputG` (mixed source records at
positive heights, the identity chart at height zero, compatibility across rectangles) is discharged; the stochastic
half of every column, the row martingales, the measurability on the rectangles and the law input (I2) are explicit
hypotheses, exactly as in the Eight assembly.

## Main results

* `isSourceColumnG_of_stoch`: a mixed source column from its records, its stopping time and its stochastic half
  (A1-EIGHTSEED's `IsColumnStoch`);
* **`drift_fromSource_eq_three`**: the drift of a three-mark source record is the path drift (G3: `y⁻`, `y⁺`, `x`,
  the other source carrying `−κ̂/2 = smallG3RhoR κ 2`);
* **`seedFieldInputG_of_g3`**: `SeedFieldInputG` from the concrete G3 records.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Calc

open QuantumZipper (H fwdMap fwdHull)
open InteractingSLE.ZhanGT4 A1SeedField A1EightSeed A2X A1Patch A1Law

/-! ### Columns and drifts -/

section Column

variable {X : Type*} {mX : MeasurableSpace X} {n : ℕ}

/-- A mixed source column from its records, its stopping time and its stochastic half. -/
theorem isSourceColumnG_of_stoch {H₁ H₂ : Set ℂ} {p q Tm κ : ℝ} {rr : Fin n → ℝ} {𝓕 : Filtration ℝ≥0 mX}
    {P : Measure X} {t₂ : ℝ} {sdata : X → SeedData n} {T : X → ℝ≥0} {W₂ : ℝ → ℝ} {Vlo Vhi : X → ℝ → ℝ}
    {B D : ℝ≥0 → X → ℝ} (hrec : ∀ x, IsSourceRecordG H₁ H₂ p q Tm κ rr W₂ t₂ (sdata x) (Vlo x) (Vhi x) (T x))
    (hT : IsStoppingTime 𝓕 fun x => (T x : WithTop ℝ≥0)) (hst : IsColumnStoch 𝓕 P κ sdata T B D) :
    IsSourceColumnG H₁ H₂ p q Tm κ rr 𝓕 P t₂ sdata T :=
  ⟨W₂, Vlo, Vhi, B, D, hrec, hT, hst⟩

end Column

/-- **The drift of a three-mark source record is the path drift**: with marks `![V₀', V₁', V₂']`, reduced charges
`![ρ₀/κ, ρ₁/κ, ρ₂/κ]` (`κ ≠ 0`) and the other source carrying `−κ/2`,
`drift = ρ₀/(W − V₀') + ρ₁/(W − V₁') + ρ₂/(W − V₂') + (−κ/2)/(W − V⁰)` (G3's small curve: `ρ₀ = 3κ̂/2 − 4`,
`ρ₁ = 2 − κ̂/2`, `ρ₂ = κ̂ − 4`, other source `−κ̂/2`). -/
theorem drift_fromSource_eq_three (W W' a : ℝ → ℝ) (φ : ℂ → ℂ) {κ : ℝ} (hκ : κ ≠ 0) (ρ₀ ρ₁ ρ₂ ζ₀ p : ℝ)
    (V₀' V₁' V₂' : ℝ → ℝ) (t : ℝ) :
    (SeedData.fromSource W W' a φ κ ![ρ₀ / κ, ρ₁ / κ, ρ₂ / κ] ζ₀ p ![V₀', V₁', V₂']).drift t =
      ρ₀ / (W t - V₀' t) + ρ₁ / (W t - V₁' t) + ρ₂ / (W t - V₂' t)
        + -(κ / 2) / (W t - ((fwdMap W t p).re + W t)) := by
  rw [SeedData.drift_eq]
  simp only [SeedData.fromSource, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  field_simp
  ring

/-! ### The assembly -/

section Assembly

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The rectangle-wise mixed seeded input from the concrete G3 records** (`d = g3Rec`). Given the rectangle data
(protected pairs whose segment `(0, q m]` contains the ordinary mark's start `x_R(1)` and is far from `H₂ m`), the
pathwise conditions at every sample, the stochastic half of every source column, the row martingales, the
measurability on the rectangles and the law input (I2), all record clauses of `SeedFieldInputG` hold: the mixed source
records at every positive height (`isSourceRecordG_g3Rec`), the identity chart at height zero (`normEll_g3Rec_zero`),
and the compatibility across rectangles (`recCompat_g3Rec`). -/
theorem seedFieldInputG_of_g3 {P₁ : Measure X} {P₂ : Measure Y} {κ p a : ℝ} {xL : Fin 1 → ℝ} {xR : Fin 3 → ℝ}
    {ρL : Fin 1 → ℝ} {ρR : Fin 3 → ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ}
    {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {Law : Measure (X × Y) → Prop}
    (𝓕₁ : Filtration ℝ≥0 mX) (𝓕₂ : Filtration ℝ≥0 mY) (S₁ : ℕ → X → ℝ≥0) (S₂ : ℕ → Y → ℝ≥0)
    (H₁ H₂ : ℕ → Set ℂ) (δ q dd Tm : ℕ → ℝ)
    (h₁ : ∀ m, IsStoppingTime 𝓕₁ fun x => (S₁ m x : WithTop ℝ≥0))
    (h₂ : ∀ m, IsStoppingTime 𝓕₂ fun y => (S₂ m y : WithTop ℝ≥0))
    (hpp : ∀ m, IsProtectedPairG (H₁ m) (H₂ m) (δ m) p (q m) (dd m))
    (hU : ∀ m, ∃ U : ℝ≥0, (∀ x, S₁ m x ≤ U) ∧ ∀ y, S₂ m y ≤ U)
    (hP : ∀ x, IsIntegratedSLEPath a xL xR ρL ρR (W₁ · x) (fun i s => VL₁ i s x) (fun i s => VR₁ i s x) (B₁ · x)
      (ζ₁ x))
    (hxL : xL 0 = 0) (hxR : xR 0 = 0) (hxO : 0 < xR 1) (hxOq : ∀ m, xR 1 ≤ q m)
    (hgood₁ : ∀ m x, (S₁ m x : ℝ≥0∞) < ζ₁ x ∧ 0 < (S₁ m x : ℝ) ∧ (S₁ m x : ℝ) ≤ Tm m ∧
      fwdHull (eightDrv W₁ S₁ m x) (S₁ m x) ⊆ H₁ m)
    (hsep₁ : ∀ x (s : ℝ≥0), 0 < s → (s : ℝ≥0∞) < ζ₁ x → VL₁ 0 s x ≠ W₁ s x ∧ VR₁ 0 s x ≠ W₁ s x)
    (hsepO : ∀ x (s : ℝ≥0), (s : ℝ≥0∞) < ζ₁ x → VR₁ 1 s x ≠ W₁ s x)
    (hc₂ : ∀ m y, ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 (S₂ m y))) (h0₂ : ∀ y, W₂ 0 y = 0)
    (hgood₂ : ∀ m y, (S₂ m y : ℝ) ≤ Tm m ∧ fwdHull (frzPath W₂ p (S₂ m y) y) (S₂ m y) ⊆ H₂ m)
    (hstoch : ∀ m y, 0 < (S₂ m y : ℝ) → ∃ B D : ℝ≥0 → X → ℝ,
      IsColumnStoch 𝓕₁ P₁ (kh κ) (fun x => g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m (S₂ m y) (x, y)) (S₁ m) B D)
    (hrow : ∀ m x (a : ℝ), 0 ≤ a → a ≤ S₁ m x →
      Martingale (fun (t : ℝ≥0) y => seedHeightField (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) a
        (min (t : ℝ) (S₂ m y))) 𝓕₂ P₂)
    (hrowc : ∀ m x y (a : ℝ), 0 ≤ a → a ≤ S₁ m x →
      Continuous fun t : ℝ≥0 => seedHeightField (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) a (min (t : ℝ) (S₂ m y)))
    (hmeas : ∀ m, IsFieldMeas (seedHeightField (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m)) (fun _ : Unit => S₁ m)
      (fun _ : Unit => S₂ m))
    (hlaw : ∀ μ : Measure (X × Y), IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
      (∀ m, RectDens (h₁ m).measurableSpace (h₂ m).measurableSpace P₁ P₂ μ
        fun ω => ENNReal.ofReal (seedHeightField (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m) ω (S₁ m ω.1) (S₂ m ω.2))) →
      Law μ) :
    SeedFieldInputG P₁ P₂ (kh κ) Law := by
  have hK₂ : ∀ m y (t : ℝ), 0 ≤ t → t ≤ S₂ m y → fwdHull (frzPath W₂ p t y) t ⊆ H₂ m := fun m y t ht htS =>
    fwdHull_frzPath_subset (hc₂ m y) ht htS (hgood₂ m y).2
  have hc₂t : ∀ m y (t : ℝ), t ≤ S₂ m y → ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 t) := fun m y t htS =>
    (hc₂ m y).mono (Icc_subset_Icc_right htS)
  have hex : ∀ m x y (t : ℝ), 0 ≤ t → t ≤ S₂ m y → ∃ a W', OwnData (eightDrv W₁ S₁ m x)
      (fwdHull (frzPath W₂ p t y) t) (frzChart (frzPath W₂ p t y) t) (S₁ m x) a W' := fun m x y t ht htS =>
    exists_ownData_of_encl (continuous_eightDrv (hP x).2.2.2.1 (hgood₁ m x).1) (eightDrv_zero (hP x).1)
      (hgood₁ m x).2.1 (continuous_frzPath (hc₂t m y t htS) ht) ht (hpp m).pair.sep_pos (hpp m).pair.sep
      (hgood₁ m x).2.2.2 (hK₂ m y t ht htS)
  have hrec : ∀ m x y (t : ℝ), 0 < t → t ≤ S₂ m y → IsSourceRecordG (H₁ m) (H₂ m) p (q m) (Tm m) (kh κ) (g3RR κ)
      (frzPath W₂ p t y) t (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m t (x, y)) (Strip.extPath (VL₁ 0 · x))
      (Strip.extPath (VR₁ 0 · x)) (S₁ m x) := fun m x y t ht htS => by
    have hlt : ∀ s : ℝ≥0, s ≤ S₁ m x → (s : ℝ≥0∞) < ζ₁ x := fun s hsS =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 hsS) (hgood₁ m x).1
    have h2d : 0 < 2 * dd m := by have := (hpp m).pair.rad_pos; positivity
    exact isSourceRecordG_g3Rec (hP x) hxL hxR hxO (hxOq m) (hgood₁ m x).1 (hgood₁ m x).2.1
      (fun s hs hsS => (hsep₁ x s hs (hlt s hsS)).1) (fun s hs hsS => (hsep₁ x s hs (hlt s hsS)).2)
      (fun s hsS => hsepO x s (hlt s hsS)) h2d ((hpp m).pair.prot.mono_right subset_union_left)
      (hc₂t m y t htS) (h0₂ y) ht (htS.trans (hgood₂ m y).1) (hgood₁ m x).2.2.1 (hpp m).pair.sep_pos
      (hpp m).pair.sep (hgood₁ m x).2.2.2 (hK₂ m y t ht.le htS)
  refine ⟨3, g3RR κ, 𝓕₁, 𝓕₂, S₁, S₂, g3Rec κ p W₁ VL₁ VR₁ W₂ S₁, H₁, H₂, δ, q, dd, Tm, p, h₁, h₂, hpp, hU,
    ?_, ?_, ?_, recCompat_g3Rec hex, hrow, hrowc, hmeas, hlaw⟩
  · intro m y hS
    obtain ⟨B, D, hst⟩ := hstoch m y hS
    exact isSourceColumnG_of_stoch (fun x => hrec m x y _ hS le_rfl) (h₁ m) hst
  · intro m x y t ht htS
    exact ⟨_, _, _, hrec m x y t ht htS⟩
  · intro m x y s hs hsS
    exact normEll_g3Rec_zero (hc₂t m y 0 (S₂ m y).coe_nonneg) (h0₂ y)
      (hex m x y 0 le_rfl (S₂ m y).coe_nonneg) hs hsS

end Assembly

end InteractingSLE.ZhanGT4.A1G3Calc
