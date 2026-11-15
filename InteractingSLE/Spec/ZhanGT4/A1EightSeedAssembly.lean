/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1EightSeedRecord

/-!
# Zhan's A.1 (R80): the rectangle-wise seeded input from the concrete Eight records

Packet PROVE-A1-EIGHTSEED. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.5 (`ig1_followup_proofs.txt` L300–L425).

For the concrete Eight records `eightRec` (`A1EightSeedRecord`) the record clauses of `SeedFieldInputM` are proved
here: the source records at every positive height of each rectangle, the identity chart at height zero, the
compatibility across rectangles, and the record half of each source column. What is left is stated as hypotheses
of `seedFieldInputM_of_eight`:

* the rectangle data (stopping times, bounds, protected enclosure pairs);
* the pathwise conditions at **every** sample (the exit precedes the small curve's lifetime and is positive, the
  small curve's seeds stay off its driver at positive times, the large curve is continuous up to its exit, both hulls
  lie in their enclosures) — these hold almost surely and must be arranged at every sample (null-set patching);
* `IsColumnStoch`: the stochastic half of each source column (the Brownian motion, the continuous adapted drift with
  the force-point rate, the adapted force coordinates);
* the row martingales, the measurability on the rectangles and the law input (I2) (other packets).

## Main results

* `IsColumnStoch`: the stochastic half of `A1SeedField.IsSourceColumn`; `isSourceColumn_of_stoch`;
* `fwdHull_frzPath_subset`: the frozen hull at a lower height lies in the enclosure of the exit height;
* **`seedFieldInputM_of_eight`**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1EightSeed

open QuantumZipper (H fwdMap fwdHull)
open A1SeedField A2X A1Patch A1Law

/-! ### The stochastic half of a source column -/

section Column

variable {X : Type*} {mX : MeasurableSpace X} {n : ℕ}

/-- **The stochastic half of a source column** (`IsSourceColumn` without its records and stopping time): `B` is an
`𝓕`-Brownian motion with continuous paths, `D` is adapted and continuous, the records' drivers are `√κ B + D`, `D` has
the records' force-point drift as derivative before the horizon, and the masked force coordinates are adapted. -/
def IsColumnStoch (𝓕 : Filtration ℝ≥0 mX) (P : Measure X) (κ : ℝ) (sdata : X → SeedData n) (T : X → ℝ≥0)
    (B D : ℝ≥0 → X → ℝ) : Prop :=
  IsFilteredBrownianReal 𝓕 B P ∧ (∀ x, Continuous (B · x)) ∧
    (∀ u, Measurable[𝓕 u] (D u)) ∧ (∀ x, Continuous (D · x)) ∧
    (∀ x, (sdata x).W = driftDriver (Real.sqrt κ) B D x) ∧
    (∀ x t, t ∈ Ioc (0 : ℝ) (T x) →
      HasDerivWithinAt (fun u : ℝ => D u.toNNReal x) ((sdata x).drift t) (Ioc 0 (T x)) t) ∧
    (∀ (u : ℝ≥0) m, Measurable[𝓕 u] ({x | u ≤ T x}.indicator fun x => (sdata x).V m u)) ∧
    (∀ u : ℝ≥0, Measurable[𝓕 u] ({x | u ≤ T x}.indicator fun x => (sdata x).V₀ u)) ∧
    (∀ u : ℝ≥0, Measurable[𝓕 u] ({x | u ≤ T x}.indicator fun x => (sdata x).G₀ u))

/-- A source column from its records, its stopping time and its stochastic half. -/
theorem isSourceColumn_of_stoch {H₁ H₂ : Set ℂ} {p Tm κ : ℝ} {rr : Fin n → ℝ} {𝓕 : Filtration ℝ≥0 mX}
    {P : Measure X} {t₂ : ℝ} {sdata : X → SeedData n} {T : X → ℝ≥0} {W₂ : ℝ → ℝ} {Vlo Vhi : X → ℝ → ℝ}
    {B D : ℝ≥0 → X → ℝ} (hrec : ∀ x, IsSourceRecord H₁ H₂ p Tm κ rr W₂ t₂ (sdata x) (Vlo x) (Vhi x) (T x))
    (hT : IsStoppingTime 𝓕 fun x => (T x : WithTop ℝ≥0)) (hst : IsColumnStoch 𝓕 P κ sdata T B D) :
    IsSourceColumn H₁ H₂ p Tm κ rr 𝓕 P t₂ sdata T :=
  ⟨W₂, Vlo, Vhi, B, D, hrec, hT, hst⟩

end Column

/-! ### The frozen hull at lower heights -/

section Frozen

variable {Y : Type*}

/-- **The frozen hull at a height `t ≤ t₂` lies in the enclosure of the height `t₂`**: the frozen paths stopped at `t`
and `t₂` agree up to `t` (same hull at `t`), and hulls grow. -/
theorem fwdHull_frzPath_subset {W₂ : ℝ≥0 → Y → ℝ} {p t t₂ : ℝ} {y : Y} {E : Set ℂ}
    (hc : ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 t₂)) (ht : 0 ≤ t) (htt : t ≤ t₂)
    (hK : fwdHull (frzPath W₂ p t₂ y) t₂ ⊆ E) : fwdHull (frzPath W₂ p t y) t ⊆ E := by
  rcases htt.eq_or_lt with rfl | hlt
  · exact hK
  have hc₁ : Continuous (frzPath W₂ p t y) := continuous_frzPath (hc.mono (Icc_subset_Icc_right htt)) ht
  have hc₂ : Continuous (frzPath W₂ p t₂ y) := continuous_frzPath hc (ht.trans htt)
  have he : fwdHull (frzPath W₂ p t y) t = fwdHull (frzPath W₂ p t₂ y) t :=
    LocalExt.fwdHull_congr_of_continuousOn hc₁.continuousOn hc₂.continuousOn ht hlt fun s hs => by
      simp only [frzPath, A1Ref.stopDrv_eqOn _ t hs, A1Ref.stopDrv_eqOn _ t₂ ⟨hs.1, hs.2.trans htt⟩]
  rw [he]
  exact ((QuantumZipper.fwdHull_mono.1 htt).trans hK)

end Frozen

/-! ### The assembly -/

section Assembly

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The rectangle-wise seeded input from the concrete Eight records** (`d = eightRec`). Given the rectangle data,
the pathwise conditions at every sample, the stochastic half of every source column, the row martingales, the
measurability on the rectangles and the law input (I2), all record clauses of `SeedFieldInputM` hold: the source
records at every positive height (`isSourceRecord_eightRec`), the identity chart at height zero
(`normEll_eightRec_zero`), and the compatibility across rectangles (`recCompat_eightRec`). -/
theorem seedFieldInputM_of_eight {P₁ : Measure X} {P₂ : Measure Y} {κ p a : ℝ} {xL : Fin 1 → ℝ} {xR : Fin 2 → ℝ}
    {ρL : Fin 1 → ℝ} {ρR : Fin 2 → ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ}
    {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {Law : Measure (X × Y) → Prop}
    (𝓕₁ : Filtration ℝ≥0 mX) (𝓕₂ : Filtration ℝ≥0 mY) (S₁ : ℕ → X → ℝ≥0) (S₂ : ℕ → Y → ℝ≥0)
    (H₁ H₂ : ℕ → Set ℂ) (δ q dd Tm : ℕ → ℝ)
    (h₁ : ∀ m, IsStoppingTime 𝓕₁ fun x => (S₁ m x : WithTop ℝ≥0))
    (h₂ : ∀ m, IsStoppingTime 𝓕₂ fun y => (S₂ m y : WithTop ℝ≥0))
    (hpp : ∀ m, IsProtectedPair (H₁ m) (H₂ m) (δ m) p (q m) (dd m))
    (hU : ∀ m, ∃ U : ℝ≥0, (∀ x, S₁ m x ≤ U) ∧ ∀ y, S₂ m y ≤ U)
    (hP : ∀ x, IsIntegratedSLEPath a xL xR ρL ρR (W₁ · x) (fun i s => VL₁ i s x) (fun i s => VR₁ i s x) (B₁ · x)
      (ζ₁ x))
    (hxL : xL 0 = 0) (hxR : xR 0 = 0)
    (hgood₁ : ∀ m x, (S₁ m x : ℝ≥0∞) < ζ₁ x ∧ 0 < (S₁ m x : ℝ) ∧ (S₁ m x : ℝ) ≤ Tm m ∧
      fwdHull (eightDrv W₁ S₁ m x) (S₁ m x) ⊆ H₁ m)
    (hsep₁ : ∀ x (s : ℝ≥0), 0 < s → (s : ℝ≥0∞) < ζ₁ x → VL₁ 0 s x ≠ W₁ s x ∧ VR₁ 0 s x ≠ W₁ s x)
    (hc₂ : ∀ m y, ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 (S₂ m y))) (h0₂ : ∀ y, W₂ 0 y = 0)
    (hgood₂ : ∀ m y, (S₂ m y : ℝ) ≤ Tm m ∧ fwdHull (frzPath W₂ p (S₂ m y) y) (S₂ m y) ⊆ H₂ m)
    (hstoch : ∀ m y, 0 < (S₂ m y : ℝ) → ∃ B D : ℝ≥0 → X → ℝ,
      IsColumnStoch 𝓕₁ P₁ (kh κ) (fun x => eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m (S₂ m y) (x, y)) (S₁ m) B D)
    (hrow : ∀ m x (a : ℝ), 0 ≤ a → a ≤ S₁ m x →
      Martingale (fun (t : ℝ≥0) y => seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) a
        (min (t : ℝ) (S₂ m y))) 𝓕₂ P₂)
    (hrowc : ∀ m x y (a : ℝ), 0 ≤ a → a ≤ S₁ m x →
      Continuous fun t : ℝ≥0 => seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) a (min (t : ℝ) (S₂ m y)))
    (hmeas : ∀ m, IsFieldMeas (seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m)) (fun _ : Unit => S₁ m)
      (fun _ : Unit => S₂ m))
    (hlaw : ∀ μ : Measure (X × Y), IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
      (∀ m, RectDens (h₁ m).measurableSpace (h₂ m).measurableSpace P₁ P₂ μ
        fun ω => ENNReal.ofReal (seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) ω (S₁ m ω.1) (S₂ m ω.2))) →
      Law μ) :
    SeedFieldInputM P₁ P₂ (kh κ) Law := by
  -- the pathwise ingredients at a sample, a rectangle and a height `0 ≤ t ≤ S₂ m y`
  have hK₂ : ∀ m y (t : ℝ), 0 ≤ t → t ≤ S₂ m y → fwdHull (frzPath W₂ p t y) t ⊆ H₂ m := fun m y t ht htS =>
    fwdHull_frzPath_subset (hc₂ m y) ht htS (hgood₂ m y).2
  have hc₂t : ∀ m y (t : ℝ), t ≤ S₂ m y → ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 t) := fun m y t htS =>
    (hc₂ m y).mono (Icc_subset_Icc_right htS)
  have hex : ∀ m x y (t : ℝ), 0 ≤ t → t ≤ S₂ m y → ∃ a W', OwnData (eightDrv W₁ S₁ m x)
      (fwdHull (frzPath W₂ p t y) t) (frzChart (frzPath W₂ p t y) t) (S₁ m x) a W' := fun m x y t ht htS =>
    exists_ownData_of_encl (continuous_eightDrv (hP x).2.2.2.1 (hgood₁ m x).1) (eightDrv_zero (hP x).1)
      (hgood₁ m x).2.1 (continuous_frzPath (hc₂t m y t htS) ht) ht (hpp m).sep_pos (hpp m).sep (hgood₁ m x).2.2.2
      (hK₂ m y t ht htS)
  have hrec : ∀ m x y (t : ℝ), 0 < t → t ≤ S₂ m y → IsSourceRecord (H₁ m) (H₂ m) p (Tm m) (kh κ) (eightRR κ)
      (frzPath W₂ p t y) t (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m t (x, y)) (Strip.extPath (VL₁ 0 · x))
      (Strip.extPath (VR₁ 0 · x)) (S₁ m x) := fun m x y t ht htS => by
    have hne : ∀ s : ℝ≥0, 0 < s → s ≤ S₁ m x → VL₁ 0 s x ≠ W₁ s x ∧ VR₁ 0 s x ≠ W₁ s x := fun s hs hsS =>
      hsep₁ x s hs (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hsS) (hgood₁ m x).1)
    exact isSourceRecord_eightRec (hP x) hxL hxR (hgood₁ m x).1 (hgood₁ m x).2.1 (fun s hs hsS => (hne s hs hsS).1)
      (fun s hs hsS => (hne s hs hsS).2) (hc₂t m y t htS) (h0₂ y) ht (htS.trans (hgood₂ m y).1)
      (hgood₁ m x).2.2.1 (hpp m).sep_pos (hpp m).sep (hgood₁ m x).2.2.2 (hK₂ m y t ht.le htS)
  refine ⟨2, eightRR κ, 𝓕₁, 𝓕₂, S₁, S₂, eightRec κ p W₁ VL₁ VR₁ W₂ S₁, H₁, H₂, δ, q, dd, Tm, p, h₁, h₂, hpp, hU,
    ?_, ?_, ?_, recCompat_eightRec hex, hrow, hrowc, hmeas, hlaw⟩
  · intro m y hS
    obtain ⟨B, D, hst⟩ := hstoch m y hS
    exact isSourceColumn_of_stoch (fun x => hrec m x y _ hS le_rfl) (h₁ m) hst
  · intro m x y t ht htS
    exact ⟨_, _, _, hrec m x y t ht htS⟩
  · intro m x y s hs hsS
    exact normEll_eightRec_zero (hc₂t m y 0 (S₂ m y).coe_nonneg) (h0₂ y)
      (hex m x y 0 le_rfl (S₂ m y).coe_nonneg) hs hsS

end Assembly

end InteractingSLE.ZhanGT4.A1EightSeed
