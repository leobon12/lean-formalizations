/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ERecStop

/-!
# Zhan's A.1 (Eight), large direction: the record measurability facts for regular good marginals

Packet PROVE-A1-EIGHTREC. For the regular Eight marginals with continuous Brownian paths and `GoodSmallEight` small
paths at every sample (the patched marginals of `EightRectLawFstC`), at a stop `τ` of the small curve and the records
`𝓐 m = 𝓕¹_{τ ∧ S₁ᵐ}`, `𝓑 m = 𝓕²_{S₂ᵐ}`:

* **`eightRec_loc`**: at a protected sample (`ρ ≤ S₁ᵐ`) the replacement data — the large driver stopped at its exit
  `S₂ᵐ`, the small driver stopped at `ρ`, both with infinite lifetime — satisfy the locality premises of FORCES's and
  SEEDGEOM's stopped-record lemmas (good exit for both data, agreement on the record intervals);
* **`measurable_capFst_gated`**: the cap at any record-measurable own time `U` that is positive only where the frozen
  small hull is protected (`τ ≤ S₁ᵐ`) and is below `S₂ᵐ` is record-measurable;
* the record facts `hSm` (**`eightRec_hSm`**), `hgS` (**`eightRec_hgS`**), `hgW` (**`eightRec_hgW`**) and `hgVL`
  (**`eightRec_hgVL`**) of A1-RECTLAW2's `eightFstResStop`, for the raw caps `eightFstCap` of the regular data
  (`hstop` follows from `hSm` by MULTIMARK's `measurableSet_fst_inter_cap`, see `A1ERecWire`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ERec

open QuantumZipper (H fwdHull)
open A2X A1Ref A1Canon A1Core A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin A1ELaw
  A1Good A1LargeDens A1Asm A1Forces A1MultiMark A1Family A1RLaw A1Frozen A1SeedGeom A1RectLaw

/-! ### Stopped drivers -/

section Stopped

variable {Ω : Type*}

/-- A path continuous before its lifetime, stopped at a time before the lifetime, is continuous. -/
theorem continuous_stoppedAt_of_lt {w : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {c : Ω → ℝ≥0} {ω : Ω}
    (hw : ContinuousOn (w · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hc : (c ω : ℝ≥0∞) < ζ ω) :
    Continuous (stoppedAt w c · ω) := by
  have h : ContinuousOn (w · ω) (Icc 0 (c ω)) :=
    hw.mono fun t (ht : t ∈ Icc 0 (c ω)) => lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) hc
  exact h.comp_continuous (continuous_id.min continuous_const) fun _ => ⟨bot_le, min_le_right _ _⟩

/-- The real-time reading of a continuous path is continuous. -/
theorem continuous_extPath {f : ℝ≥0 → ℝ} (hf : Continuous f) : Continuous (Strip.extPath f) :=
  hf.comp continuous_real_toNNReal

/-- The stopped path read in real time agrees with the path on the stopping interval. -/
theorem extPath_stoppedAt_eqOn (w : ℝ≥0 → Ω → ℝ) (c : Ω → ℝ≥0) (ω : Ω) :
    EqOn (Strip.extPath (stoppedAt w c · ω)) (Strip.extPath (w · ω)) (Icc 0 (c ω : ℝ)) := fun u hu => by
  simp only [Strip.extPath, stoppedAt]
  rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hu.2)]

end Stopped

/-! ### The Eight records -/

section Eight

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ}
  {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ}
  {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

/-- **The exits of the regular Eight rectangles**: the small exits are before the small lifetime, the large exits are
positive and before the large lifetime. -/
theorem eightRec_exits (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω)) :
    (∀ m x₀, (eightS₁ x W₁ ζ₁ m x₀ : ℝ≥0∞) < ζ₁ x₀) ∧ (∀ m y₀, (eightS₂ x W₂ ζ₂ m y₀ : ℝ≥0∞) < ζ₂ y₀) ∧
      ∀ m y₀, 0 < (eightS₂ x W₂ ζ₂ m y₀ : ℝ) := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  obtain ⟨-, hgood₁, -, -, -, -, hS₂pos, hlt₂⟩ :=
    eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cof hne)
  exact ⟨fun m x₀ => (hgood₁ m x₀).1, hlt₂, hS₂pos⟩

/-- **The record replacement data at a protected sample.** For a frozen time `ρ ≤ S₁ᵐ`, the large driver stopped at
its exit `S₂ᵐ` and the small driver stopped at `ρ` (infinite lifetimes) agree with the actual drivers on the record
intervals, and the exit is a good own time for both the actual and the replacement data. -/
theorem eightRec_loc (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω)) (m : ℕ)
    {ρ : X → ℝ≥0} (z : X × Y) (hρ : ρ z.1 ≤ eightS₁ x W₁ ζ₁ m z.1) :
    (ρ z.1 : ℝ≥0∞) < ζ₁ z.1 ∧
    (∀ T : ℝ, ENNReal.ofReal T < lifeEnd (W₂ · z.2) (VL₂ 0 · z.2) (ζ₂ z.2) →
      ContinuousOn (Strip.extPath (W₂ · z.2)) (Icc 0 T)) ∧ W₂ 0 z.2 = 0 ∧
    (∃ τ', ((ρ z.1 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₁ · z.1)) (Icc 0 τ')) ∧ W₁ 0 z.1 = 0 ∧
    IsGoodTime 0 (Strip.extPath (W₂ · z.2)) (lifeEnd (W₂ · z.2) (VL₂ 0 · z.2) (ζ₂ z.2)) x
      (Strip.extPath (W₁ · z.1)) (ρ z.1) (eightS₂ x W₂ ζ₂ m z.2) ∧
    IsGoodTime 0 (Strip.extPath (stoppedAt W₂ (eightS₂ x W₂ ζ₂ m) · z.2)) ⊤ x
      (Strip.extPath (stoppedAt W₁ ρ · z.1)) (ρ z.1) (eightS₂ x W₂ ζ₂ m z.2) ∧
    (∀ t : ℝ≥0, (t : ℝ) ≤ eightS₂ x W₂ ζ₂ m z.2 → stoppedAt W₂ (eightS₂ x W₂ ζ₂ m) t z.2 = W₂ t z.2) ∧
    (∀ t ≤ ρ z.1, stoppedAt W₁ ρ t z.1 = W₁ t z.1) ∧
    (eightS₂ x W₂ ζ₂ m z.2 : ℝ≥0∞) < lifeEnd (W₂ · z.2) (VL₂ 0 · z.2) (ζ₂ z.2) := by
  obtain ⟨hlt₁, hlt₂, hS₂pos⟩ := eightRec_exits hκ8 hx h₁ hB₁ hg₁ h₂ hB₂
  have hρζ : (ρ z.1 : ℝ≥0∞) < ζ₁ z.1 := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hρ) (hlt₁ m z.1)
  have hgood := eightFst_isGoodTime hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m z.1 z.2 hρ
  obtain ⟨T₂, hT₂, hcT₂⟩ := exists_gt_continuousOn_extPath (h₂.path z.2).2.2.2.1 (hlt₂ m z.2)
  obtain ⟨T₁, hT₁, hcT₁⟩ := exists_gt_continuousOn_extPath (h₁.path z.1).2.2.2.1 hρζ
  have hc₂' : Continuous (Strip.extPath (stoppedAt W₂ (eightS₂ x W₂ ζ₂ m) · z.2)) :=
    continuous_extPath (continuous_stoppedAt_of_lt (h₂.path z.2).2.2.2.1 (hlt₂ m z.2))
  have hc₁' : Continuous (Strip.extPath (stoppedAt W₁ ρ · z.1)) :=
    continuous_extPath (continuous_stoppedAt_of_lt (h₁.path z.1).2.2.2.1 hρζ)
  have e₂ : physHull 0 (Strip.extPath (stoppedAt W₂ (eightS₂ x W₂ ζ₂ m) · z.2)) (eightS₂ x W₂ ζ₂ m z.2) =
      physHull 0 (Strip.extPath (W₂ · z.2)) (eightS₂ x W₂ ζ₂ m z.2) :=
    physHull_congr_of_continuousOn hc₂'.continuousOn hcT₂ (NNReal.coe_nonneg _) hT₂
      (extPath_stoppedAt_eqOn W₂ (eightS₂ x W₂ ζ₂ m) z.2)
  have e₁ : physHull x (Strip.extPath (stoppedAt W₁ ρ · z.1)) (ρ z.1) =
      physHull x (Strip.extPath (W₁ · z.1)) (ρ z.1) :=
    physHull_congr_of_continuousOn hc₁'.continuousOn hcT₁ (NNReal.coe_nonneg _) hT₁
      (extPath_stoppedAt_eqOn W₁ ρ z.1)
  refine ⟨hρζ, fun T hT => A1Ref.continuousOn_extPath_Icc (h₂.path z.2).2.2.2.1
      (hT.trans_le (A2X.P3.lifeEnd_le_lifetime _ _ _)), (h₂.path z.2).1, ⟨T₁, hT₁, hcT₁⟩, (h₁.path z.1).1,
    hgood, ?_, fun t ht => ?_, fun t ht => ?_, eightFst_lt_lifeEnd hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m z.1 z.2⟩
  · refine isGoodTime_of_disjoint_loc (T' := (eightS₂ x W₂ ζ₂ m z.2 : ℝ) + 1) (by linarith)
      hc₂'.continuousOn (hS₂pos m z.2) ENNReal.ofReal_lt_top ?_
    rw [e₂, e₁]
    exact (disjoint_of_isGoodTime hgood).symm
  · simp only [stoppedAt]
    rw [min_eq_left (NNReal.coe_le_coe.1 ht)]
  · simp only [stoppedAt]
    rw [min_eq_left ht]

omit mX mY in
/-- **The gate of the raw own time**: a positive own time forces the protection `σ ≤ S₁ᵏ`, and then it is the large
exit. -/
theorem eightFstOwn_pos {σ : ℝ≥0} {k : ℕ} {z : X × Y} (h : 0 < eightFstOwn x W₁ ζ₁ W₂ ζ₂ σ k z) :
    σ ≤ eightS₁ x W₁ ζ₁ k z.1 ∧ eightFstOwn x W₁ ζ₁ W₂ ζ₂ σ k z = eightS₂ x W₂ ζ₂ k z.2 := by
  unfold eightFstOwn at h ⊢
  by_cases hg : σ ≤ eightS₁ x W₁ ζ₁ k z.1
  · simp only [hg, ↓reduceIte, and_self]
  · simp only [hg, ↓reduceIte, lt_irrefl] at h

omit mX mY in
/-- The raw cap at the stop is FORCES's cap at the gated own time. -/
theorem eightFstCap_stop (τ : X → ℝ≥0) (k : ℕ) :
    (fun z => eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ (τ z.1) k z) =
      capFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁ τ
        (fun z => eightFstOwn x W₁ ζ₁ W₂ ζ₂ (τ z.1) k z) :=
  funext fun z => capFst_at _ 0 W₂ _ x W₁ τ (fun σ => eightFstOwn x W₁ ζ₁ W₂ ζ₂ σ k) z

omit mX mY in
/-- **A positive raw cap at the stop forces the protection** `τ ≤ S₁ᵏ`, and its own time is the large exit. -/
theorem eightFstCap_pos {τ : X → ℝ≥0} {k : ℕ} {z : X × Y}
    (h : 0 < eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ (τ z.1) k z) :
    τ z.1 ≤ eightS₁ x W₁ ζ₁ k z.1 ∧ eightFstOwn x W₁ ζ₁ W₂ ζ₂ (τ z.1) k z = eightS₂ x W₂ ζ₂ k z.2 := by
  have h' := congrFun (eightFstCap_stop (x := x) (W₁ := W₁) (ζ₁ := ζ₁) (W₂ := W₂) (VL₂ := VL₂) (ζ₂ := ζ₂) τ k) z
  rw [h'] at h
  refine eightFstOwn_pos (lt_of_not_ge fun h0 => ?_)
  rw [capFst_of_nonpos (T := fun z => eightFstOwn x W₁ ζ₁ W₂ ζ₂ (τ z.1) k z) h0] at h
  exact lt_irrefl _ h

section Records

variable (hκ8 : 8 ≤ κ) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
  (hs₁ : ∀ m, IsStoppingTime 𝓖₁ fun ω => (eightS₁ x W₁ ζ₁ m ω : WithTop ℝ≥0))
  (hs₂ : ∀ m, IsStoppingTime 𝓖₂ fun ω => (eightS₂ x W₂ ζ₂ m ω : WithTop ℝ≥0))
  {τ : X → ℝ≥0} (hτ : IsStoppingTime 𝓖₁ fun x₀ => (τ x₀ : WithTop ℝ≥0))
include hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ

/-- **The cap at a gated own time is record-measurable**: for an own time `U` measurable for the records
`𝓕¹_{τ ∧ S₁ᵐ} ⊗ 𝓕²_{S₂ᵐ}`, positive only where `τ ≤ S₁ᵐ` and bounded by `S₂ᵐ`, the cap `capFst … τ U` is
record-measurable (FORCES's `measurable_capFst_of_stopped` at the stop `τ ∧ S₁ᵐ`, with the drivers stopped at the
record stops). -/
theorem measurable_capFst_gated (m : ℕ) {U : X × Y → ℝ}
    (hU : Measurable[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace] U)
    (hUg : ∀ z, 0 < U z → τ z.1 ≤ eightS₁ x W₁ ζ₁ m z.1 ∧ U z ≤ eightS₂ x W₂ ζ₂ m z.2) :
    Measurable[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace]
      (capFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁ τ U) := by
  obtain ⟨hlt₁, hlt₂, -⟩ := eightRec_exits hκ8 hx h₁ hB₁ hg₁ h₂ hB₂
  have hρ := isStoppingTime_min_nnreal hτ (hs₁ m)
  have hρm : Measurable[(hτ.min (hs₁ m)).measurableSpace] fun x₀ => min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀) := by
    have h := measurable_stop_nnreal hρ
    rwa [measurableSpace_min_nnreal hτ (hs₁ m)] at h
  have e : capFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁ τ U =
      capFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun x₀ => min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀)) U := funext fun z => by
    rcases le_or_gt (U z) 0 with h0 | h0
    · rw [capFst_of_nonpos h0, capFst_of_nonpos h0]
    · exact capFst_congr_stop (min_eq_left (hUg z h0).1).symm U
  rw [e]
  have hkm : ∀ t, Measurable[(hτ.min (hs₁ m)).measurableSpace]
      (stoppedAt W₁ (fun x₀ => min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀)) t) := fun t => by
    have h := measurable_stopped_at h₁.progW hρ t
    rwa [measurableSpace_min_nnreal hτ (hs₁ m)] at h
  refine measurable_capFst_of_stopped (𝓐 := (hτ.min (hs₁ m)).measurableSpace) (𝓑 := (hs₂ m).measurableSpace)
    (live' := fun _ _ => True) (Wj' := stoppedAt W₂ (eightS₂ x W₂ ζ₂ m)) (ζj' := fun _ => ⊤)
    (Wk' := stoppedAt W₁ (fun x₀ => min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀))) (ζk' := fun _ => ⊤) hρm
    (by simp only [ofPred_true]; exact MeasurableSet.univ) (fun _ _ _ => ENNReal.coe_lt_top)
    (fun y => (continuous_stoppedAt_of_lt (h₂.path y).2.2.2.1 (hlt₂ m y)).continuousOn)
    (fun y => by simp only [stoppedAt, min_eq_left (_root_.zero_le : (0 : ℝ≥0) ≤ _)]; exact (h₂.path y).1)
    (fun x₀ => (continuous_stoppedAt_of_lt (h₁.path x₀).2.2.2.1
      (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) (hlt₁ m x₀))).continuousOn)
    (fun x₀ => by simp only [stoppedAt, min_eq_left (_root_.zero_le : (0 : ℝ≥0) ≤ _)]; exact (h₁.path x₀).1)
    (fun t => measurable_stopped_at h₂.progW (hs₂ m) t) hkm measurable_const measurable_const hU
    (fun z hz => ?_)
  obtain ⟨hlive, hj, -, hk, -, -, -, hagj, hagk, hlife⟩ :=
    eightRec_loc hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m (ρ := fun x₀ => min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀)) z (min_le_right _ _)
  refine ⟨iff_of_true hlive trivial, fun _ => ⟨hj, hk, ?_, le_top, fun t ht => hagj t ?_, hagk⟩⟩
  · refine (ENNReal.ofReal_le_ofReal (hUg z hz).2).trans ?_
    rw [ENNReal.ofReal_coe_nnreal]
    exact hlife.le
  · exact ht.le.trans (hUg z hz).2

omit hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ in
/-- The protection gate `{τ ≤ S₁ᵐ}`, read on the product, is an event of the records. -/
theorem measurableSet_gate (m : ℕ) :
    MeasurableSet[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace]
      {z : X × Y | τ z.1 ≤ eightS₁ x W₁ ζ₁ m z.1} :=
  (@measurable_fst X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace)
    (measurableSet_le_min_nnreal hτ (hs₁ m))

/-- **`hSm`: the raw cap at the stop is record-measurable.** -/
theorem eightRec_hSm (m : ℕ) :
    Measurable[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace]
      fun z => eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ (τ z.1) m z := by
  rw [eightFstCap_stop]
  refine measurable_capFst_gated hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ m ?_ fun z hz => ?_
  · have hS₂m : Measurable[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
        (hs₂ m).measurableSpace] fun z : X × Y => (eightS₂ x W₂ ζ₂ m z.2 : ℝ) :=
      measurable_coe_nnreal_real.comp ((measurable_stop_nnreal (hs₂ m)).comp
        (@measurable_snd X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace))
    exact Measurable.ite (measurableSet_gate hs₁ hs₂ hτ m) hS₂m measurable_const
  · obtain ⟨hg, he⟩ := eightFstOwn_pos hz
    exact ⟨hg, he.le⟩

omit hs₁ hs₂ hτ in
/-- The clock up to the raw own time is finite (the large exit is a good own time when the small hull is protected,
and the own time vanishes otherwise). -/
theorem eightRec_hfin (k : ℕ) (z : X × Y) :
    clkSup 0 (Strip.extPath (W₂ · z.2)) (lifeEnd (W₂ · z.2) (VL₂ 0 · z.2) (ζ₂ z.2)) x
      (Strip.extPath (W₁ · z.1)) (τ z.1) (eightFstOwn x W₁ ζ₁ W₂ ζ₂ (τ z.1) k z) ≠ ∞ := by
  rcases le_or_gt (eightFstOwn x W₁ ζ₁ W₂ ζ₂ (τ z.1) k z) 0 with h0 | h0
  · rw [clkSup_of_nonpos h0]; exact ENNReal.zero_ne_top
  obtain ⟨hg, he⟩ := eightFstOwn_pos h0
  obtain ⟨-, hj, hj0, hk, hk0, hgood, -⟩ := eightRec_loc hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k (ρ := τ) z hg
  rw [he, clkSup_eq_of_isGoodTime hj (by simp only [Strip.extPath, Real.toNNReal_zero, hj0]) hk
    (by simp only [Strip.extPath, Real.toNNReal_zero, hk0]) (NNReal.coe_nonneg _) hgood]
  exact ENNReal.ofReal_ne_top

/-- **`hgS`: the cap comparisons are events of the records.** -/
theorem eightRec_hgS (m k : ℕ) (r : ℝ≥0) :
    MeasurableSet[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace]
      ({z | eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ (τ z.1) k z ≤ r} ∩
        {z | r < eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ (τ z.1) m z}) := by
  have ek := congrFun (eightFstCap_stop (x := x) (W₁ := W₁) (ζ₁ := ζ₁) (W₂ := W₂) (VL₂ := VL₂) (ζ₂ := ζ₂) τ k)
  have em := congrFun (eightFstCap_stop (x := x) (W₁ := W₁) (ζ₁ := ζ₁) (W₂ := W₂) (VL₂ := VL₂) (ζ₂ := ζ₂) τ m)
  simp only [ek, em]
  set Tk : X × Y → ℝ := fun z => eightFstOwn x W₁ ζ₁ W₂ ζ₂ (τ z.1) k z with hTk
  set Tm : X × Y → ℝ := fun z => eightFstOwn x W₁ ζ₁ W₂ ζ₂ (τ z.1) m z with hTm
  -- the own time `min Tk Tm` as a record-measurable function
  have emin : (fun z => min (Tk z) (Tm z)) = fun z =>
      if τ z.1 ≤ eightS₁ x W₁ ζ₁ k z.1 ∧ τ z.1 ≤ eightS₁ x W₁ ζ₁ m z.1 then
        ((min (eightS₂ x W₂ ζ₂ k z.2) (eightS₂ x W₂ ζ₂ m z.2) : ℝ≥0) : ℝ) else 0 := funext fun z => by
    simp only [hTk, hTm, eightFstOwn]
    by_cases hk : τ z.1 ≤ eightS₁ x W₁ ζ₁ k z.1 <;> by_cases hm : τ z.1 ≤ eightS₁ x W₁ ζ₁ m z.1 <;>
      simp only [hk, hm, ↓reduceIte, and_self, and_true, and_false, NNReal.coe_min,
        min_self, NNReal.coe_nonneg, min_eq_right, min_eq_left]
  have hgate : MeasurableSet[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
      (hs₂ m).measurableSpace] {z : X × Y | τ z.1 ≤ eightS₁ x W₁ ζ₁ k z.1 ∧ τ z.1 ≤ eightS₁ x W₁ ζ₁ m z.1} := by
    have e : {z : X × Y | τ z.1 ≤ eightS₁ x W₁ ζ₁ k z.1 ∧ τ z.1 ≤ eightS₁ x W₁ ζ₁ m z.1} =
        Prod.fst ⁻¹' ({x₀ | min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀) ≤ eightS₁ x W₁ ζ₁ k x₀} ∩
          {x₀ | τ x₀ ≤ eightS₁ x W₁ ζ₁ m x₀}) := by
      ext z
      simp only [mem_ofPred_eq, mem_preimage, mem_inter_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by rw [min_eq_left h2]; exact h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨by rw [min_eq_left h2] at h1; exact h1, h2⟩
    rw [e]
    exact (@measurable_fst X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace)
      ((measurableSet_min_le_nnreal hτ (hs₁ m) (hs₁ k)).inter (measurableSet_le_min_nnreal hτ (hs₁ m)))
  have hS₂min : Measurable[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
      (hs₂ m).measurableSpace] fun z : X × Y => ((min (eightS₂ x W₂ ζ₂ k z.2) (eightS₂ x W₂ ζ₂ m z.2) : ℝ≥0) : ℝ) := by
    have hmin := isStoppingTime_min_nnreal (hs₂ k) (hs₂ m)
    have hle : hmin.measurableSpace ≤ (hs₂ m).measurableSpace :=
      IsStoppingTime.measurableSpace_mono hmin (hs₂ m) fun ω => WithTop.coe_le_coe.2 (min_le_right _ _)
    exact measurable_coe_nnreal_real.comp (((measurable_stop_nnreal hmin).mono hle le_rfl).comp
      (@measurable_snd X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace))
  have hUmin := measurable_capFst_gated hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ m
    (U := fun z => min (Tk z) (Tm z)) (by rw [emin]; exact Measurable.ite hgate hS₂min measurable_const)
    fun z hz => by
      obtain ⟨hg, he⟩ := eightFstOwn_pos (lt_of_lt_of_le hz (min_le_right _ _))
      exact ⟨hg, (min_le_right _ _).trans he.le⟩
  have hUm := eightRec_hSm hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ m
  rw [eightFstCap_stop] at hUm
  exact measurableSet_capFst_le_inter (𝓜 := @Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
    (hs₂ m).measurableSpace) hUmin hUm
    (fun z _ => eightRec_hfin hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k z) r

/-- **The record replacement data**: the protected stop `τ ∧ S₁ᵐ` is measurable for `𝓕¹_{τ ∧ S₁ᵐ}`; the large driver
stopped at `S₂ᵐ` and the small driver stopped at `τ ∧ S₁ᵐ` are continuous, start at `0` and are measurable for the
records. -/
theorem eightRec_repl (m : ℕ) :
    Measurable[(hτ.min (hs₁ m)).measurableSpace] (fun x₀ => min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀)) ∧
    (∀ y, ContinuousOn (stoppedAt W₂ (eightS₂ x W₂ ζ₂ m) · y) {t | (t : ℝ≥0∞) < (fun _ : Y => (⊤ : ℝ≥0∞)) y}) ∧
    (∀ y, stoppedAt W₂ (eightS₂ x W₂ ζ₂ m) 0 y = 0) ∧
    (∀ x₀, ContinuousOn (stoppedAt W₁ (fun x₀ => min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀)) · x₀)
      {t | (t : ℝ≥0∞) < (fun _ : X => (⊤ : ℝ≥0∞)) x₀}) ∧
    (∀ x₀, stoppedAt W₁ (fun x₀ => min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀)) 0 x₀ = 0) ∧
    (∀ t, Measurable[(hs₂ m).measurableSpace] (stoppedAt W₂ (eightS₂ x W₂ ζ₂ m) t)) ∧
    ∀ t, Measurable[(hτ.min (hs₁ m)).measurableSpace]
      (stoppedAt W₁ (fun x₀ => min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀)) t) := by
  obtain ⟨hlt₁, hlt₂, -⟩ := eightRec_exits hκ8 hx h₁ hB₁ hg₁ h₂ hB₂
  have hρ := isStoppingTime_min_nnreal hτ (hs₁ m)
  refine ⟨?_, fun y => (continuous_stoppedAt_of_lt (h₂.path y).2.2.2.1 (hlt₂ m y)).continuousOn,
    fun y => ?_, fun x₀ => (continuous_stoppedAt_of_lt (h₁.path x₀).2.2.2.1
      (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) (hlt₁ m x₀))).continuousOn, fun x₀ => ?_,
    fun t => measurable_stopped_at h₂.progW (hs₂ m) t, fun t => ?_⟩
  · have h := measurable_stop_nnreal hρ
    rwa [measurableSpace_min_nnreal hτ (hs₁ m)] at h
  · simp only [stoppedAt, min_eq_left (_root_.zero_le : (0 : ℝ≥0) ≤ _)]; exact (h₂.path y).1
  · simp only [stoppedAt, min_eq_left (_root_.zero_le : (0 : ℝ≥0) ≤ _)]; exact (h₁.path x₀).1
  · have h := measurable_stopped_at h₁.progW hρ t
    rwa [measurableSpace_min_nnreal hτ (hs₁ m)] at h

omit hs₁ hs₂ hτ in
/-- **The locality premises of SEEDGEOM's/FORCES's stopped-record lemmas** before a positive raw cap, for the stop
`τ ∧ S₁ᵐ` and the replacement data of `eightRec_repl`. -/
theorem eightRec_hloc (m : ℕ) (r : ℝ≥0) (z : X × Y)
    (hz : r < eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ (τ z.1) m z) :
    ((min (τ z.1) (eightS₁ x W₁ ζ₁ m z.1) : ℝ≥0) : ℝ≥0∞) < ζ₁ z.1 ∧ True ∧
    (∀ T : ℝ, ENNReal.ofReal T < lifeEnd (W₂ · z.2) (VL₂ 0 · z.2) (ζ₂ z.2) →
      ContinuousOn (Strip.extPath (W₂ · z.2)) (Icc 0 T)) ∧ W₂ 0 z.2 = 0 ∧
    (∃ τ', ((min (τ z.1) (eightS₁ x W₁ ζ₁ m z.1) : ℝ≥0) : ℝ) < τ' ∧
      ContinuousOn (Strip.extPath (W₁ · z.1)) (Icc 0 τ')) ∧ W₁ 0 z.1 = 0 ∧
    IsGoodTime 0 (Strip.extPath (W₂ · z.2)) (lifeEnd (W₂ · z.2) (VL₂ 0 · z.2) (ζ₂ z.2)) x
      (Strip.extPath (W₁ · z.1)) ((min (τ z.1) (eightS₁ x W₁ ζ₁ m z.1) : ℝ≥0) : ℝ) (eightS₂ x W₂ ζ₂ m z.2) ∧
    IsGoodTime 0 (Strip.extPath (stoppedAt W₂ (eightS₂ x W₂ ζ₂ m) · z.2)) ⊤ x
      (Strip.extPath (stoppedAt W₁ (fun x₀ => min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀)) · z.1))
      ((min (τ z.1) (eightS₁ x W₁ ζ₁ m z.1) : ℝ≥0) : ℝ) (eightS₂ x W₂ ζ₂ m z.2) ∧
    (∀ t : ℝ≥0, (t : ℝ) ≤ eightS₂ x W₂ ζ₂ m z.2 → stoppedAt W₂ (eightS₂ x W₂ ζ₂ m) t z.2 = W₂ t z.2) ∧
    (∀ t ≤ min (τ z.1) (eightS₁ x W₁ ζ₁ m z.1),
      stoppedAt W₁ (fun x₀ => min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀)) t z.1 = W₁ t z.1) ∧
    (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ (τ z.1) m z : ℝ) ≤
      A1Ref.imgClk 0 (Strip.extPath (W₂ · z.2)) x (Strip.extPath (W₁ · z.1))
        ((min (τ z.1) (eightS₁ x W₁ ζ₁ m z.1) : ℝ≥0) : ℝ) (eightS₂ x W₂ ζ₂ m z.2) := by
  obtain ⟨hg, he⟩ := eightFstCap_pos (lt_of_le_of_lt (_root_.zero_le : (0 : ℝ≥0) ≤ r) hz)
  obtain ⟨hlive, hj, hj0, hk, hk0, hgood, hgood', hagj, hagk, -⟩ :=
    eightRec_loc hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m (ρ := fun x₀ => min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀)) z (min_le_right _ _)
  refine ⟨hlive, trivial, hj, hj0, hk, hk0, hgood, hgood', hagj, hagk, ?_⟩
  have hcap : eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ (τ z.1) m z =
      (A1Ref.imgClk 0 (Strip.extPath (W₂ · z.2)) x (Strip.extPath (W₁ · z.1))
        ((min (τ z.1) (eightS₁ x W₁ ζ₁ m z.1) : ℝ≥0) : ℝ) (eightS₂ x W₂ ζ₂ m z.2)).toNNReal := by
    rw [congrFun (eightFstCap_stop (x := x) (W₁ := W₁) (ζ₁ := ζ₁) (W₂ := W₂) (VL₂ := VL₂) (ζ₂ := ζ₂) τ m) z,
      capFst_congr_stop (τ' := fun x₀ => min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀)) (min_eq_left hg).symm,
      capFst_congr_pt (T := fun z => eightFstOwn x W₁ ζ₁ W₂ ζ₂ (τ z.1) m z)
        (T' := fun z => (eightS₂ x W₂ ζ₂ m z.2 : ℝ)) he]
    exact capFst_eq_of_isGoodTime hlive hj hj0 hk hk0 hgood
  have hpos : 0 < (A1Ref.imgClk 0 (Strip.extPath (W₂ · z.2)) x (Strip.extPath (W₁ · z.1))
      ((min (τ z.1) (eightS₁ x W₁ ζ₁ m z.1) : ℝ≥0) : ℝ) (eightS₂ x W₂ ζ₂ m z.2)).toNNReal := by
    rw [← hcap]; exact lt_of_le_of_lt (_root_.zero_le : (0 : ℝ≥0) ≤ r) hz
  rw [hcap, Real.coe_toNNReal _ (Real.toNNReal_pos.1 hpos).le]

/-- **`hgW`: before the cap the canonical image driver agrees with a record-measurable function.** -/
theorem eightRec_hgW (m : ℕ) (r : ℝ≥0) :
    ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
        (hs₂ m).measurableSpace] f ∧ ∀ z, r < eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ (τ z.1) m z →
      rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁ τ r z =
        f z := by
  obtain ⟨hρm, hjc, hj0', hkc, hk0', hjm, hkm⟩ := eightRec_repl hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ m
  obtain ⟨f, hf, hfe⟩ := exists_measurable_rDrvFst_of_stopped (𝓐 := (hτ.min (hs₁ m)).measurableSpace)
    (𝓑 := (hs₂ m).measurableSpace) (live := fun t ω => (t : ℝ≥0∞) < ζ₁ ω) (live' := fun _ _ => True)
    (xj := 0) (xk := x) (Wj := W₂) (ζj := fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) (Wk := W₁)
    (Wj' := stoppedAt W₂ (eightS₂ x W₂ ζ₂ m)) (ζj' := fun _ => ⊤)
    (Wk' := stoppedAt W₁ (fun x₀ => min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀))) (ζk' := fun _ => ⊤) hρm
    (by simp only [ofPred_true]; exact MeasurableSet.univ) (fun _ _ _ => ENNReal.coe_lt_top) hjc hj0' hkc hk0'
    hjm hkm measurable_const measurable_const (cap := fun z => eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ (τ z.1) m z)
    (T := fun z => (eightS₂ x W₂ ζ₂ m z.2 : ℝ)) r
    (fun z hz => eightRec_hloc hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m r z hz)
  refine ⟨f, hf, fun z hz => ?_⟩
  have hg := (eightFstCap_pos (lt_of_le_of_lt (_root_.zero_le : (0 : ℝ≥0) ≤ r) hz)).1
  rw [rDrvFst_congr_stop (τ' := fun x₀ => min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀)) (min_eq_left hg).symm]
  exact hfe z hz

/-- **`hgVL`: before the cap the image forces agree with record-measurable functions** (the initial word at `r = 0`,
FORCES's canonical forces of the frozen-chart marks afterwards). -/
theorem eightRec_hgVL (m : ℕ) (i : Fin 3) (r : ℝ≥0) :
    ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
        (hs₂ m).measurableSpace] f ∧ ∀ z, r < eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ (τ z.1) m z →
      eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ (τ z.1) i r z = f z := by
  obtain ⟨hρm, hjc, hj0', hkc, hk0', hjm, hkm⟩ := eightRec_repl hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ m
  have hρ := isStoppingTime_min_nnreal hτ (hs₁ m)
  have hst : ∀ {u : ℝ≥0 → X → ℝ}, IsStronglyProgressive 𝓖₁ u →
      Measurable[(hτ.min (hs₁ m)).measurableSpace] fun x₀ => u (min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀)) x₀ :=
    fun hu => by
      have h := measurable_stoppedValue_nnreal hu hρ
      rwa [measurableSpace_min_nnreal hτ (hs₁ m)] at h
  have hgate : ∀ z, r < eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ (τ z.1) m z →
      min (τ z.1) (eightS₁ x W₁ ζ₁ m z.1) = τ z.1 := fun z hz =>
    min_eq_left (eightFstCap_pos (lt_of_le_of_lt (_root_.zero_le : (0 : ℝ≥0) ≤ r) hz)).1
  have hfst := @measurable_fst X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace
  rcases eq_or_ne r 0 with rfl | hr
  · -- the initial word, read at the protected stop
    refine ⟨fun z => eightFstWord W₁ VL₁ VR₁ (min (τ z.1) (eightS₁ x W₁ ζ₁ m z.1)) z.1 i, ?_, fun z hz => ?_⟩
    · have hw : Measurable[(hτ.min (hs₁ m)).measurableSpace]
          fun x₀ => eightFstWord W₁ VL₁ VR₁ (min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀)) x₀ i := by
        fin_cases i
        · exact (hst (h₁.progVR 0)).sub (hst (h₁.progVR 1))
        · exact (hst h₁.progW).sub (hst (h₁.progVR 1))
        · exact (hst (h₁.progVL 0)).sub (hst (h₁.progVR 1))
      exact hw.comp hfst
    · show _ = eightFstWord W₁ VL₁ VR₁ (min (τ z.1) (eightS₁ x W₁ ζ₁ m z.1)) z.1 i
      rw [eightFstVL_zero, hgate z hz]
  · -- the canonical forces of the frozen-chart marks
    have hp' : Measurable[(hτ.min (hs₁ m)).measurableSpace] fun x₀ => largeEightMarks (x - 0) (W₁ · x₀)
        (fun i t => VL₁ i t x₀) (fun j t => VR₁ j t x₀) (min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀)) i := by
      fin_cases i
      · exact measurable_const.add (hst (h₁.progVR 0))
      · exact measurable_const.add (hst h₁.progW)
      · exact measurable_const.add (hst (h₁.progVL 0))
    obtain ⟨f, hf, hfe⟩ := exists_measurable_rForceFst_of_stopped (𝓐 := (hτ.min (hs₁ m)).measurableSpace)
      (𝓑 := (hs₂ m).measurableSpace) (live := fun t ω => (t : ℝ≥0∞) < ζ₁ ω) (live' := fun _ _ => True)
      (xj := 0) (xk := x) (Wj := W₂) (ζj := fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) (Wk := W₁)
      (Wj' := stoppedAt W₂ (eightS₂ x W₂ ζ₂ m)) (ζj' := fun _ => ⊤)
      (Wk' := stoppedAt W₁ (fun x₀ => min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀))) (ζk' := fun _ => ⊤) hρm
      (by simp only [ofPred_true]; exact MeasurableSet.univ) (fun _ _ _ => ENNReal.coe_lt_top) hjc hj0' hkc hk0'
      hjm hkm measurable_const measurable_const
      (p := fun x₀ => largeEightMarks (x - 0) (W₁ · x₀) (fun i t => VL₁ i t x₀) (fun j t => VR₁ j t x₀) (τ x₀) i)
      hp' (cap := fun z => eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ (τ z.1) m z)
      (T := fun z => (eightS₂ x W₂ ζ₂ m z.2 : ℝ)) r
      (fun z hz => eightRec_hloc hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m r z hz)
      (fun z hz => by simp only [hgate z hz])
    refine ⟨f, hf, fun z hz => ?_⟩
    simp only [eightFstVL, hr, ↓reduceIte]
    have e₁ := rForceFst_at (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x
      W₁ τ (fun σ x₀ => largeEightMarks (x - 0) (W₁ · x₀) (fun i t => VL₁ i t x₀) (fun j t => VR₁ j t x₀) σ i) r z
    have e₂ := rForceFst_congr_stop (live := fun t ω => (t : ℝ≥0∞) < ζ₁ ω) (xj := 0)
      (Wj := W₂) (ζj := fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) (xk := x) (Wk := W₁)
      (τ' := fun x₀ => min (τ x₀) (eightS₁ x W₁ ζ₁ m x₀)) (hgate z hz).symm
      (fun x₀ => largeEightMarks (x - 0) (W₁ · x₀) (fun i t => VL₁ i t x₀) (fun j t => VR₁ j t x₀) (τ x₀) i) r
    exact e₁.trans (e₂.trans (hfe z hz))

end Records

end Eight

end InteractingSLE.ZhanGT4.A1ERec
