/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1CommonCof
import InteractingSLE.Spec.ZhanGT4.A1G3CalcDrift

/-!
# Zhan's A.1: the adapted clauses of the source columns

Packet PROVE-A1-COMMON. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L300–L355: the column
martingale is run in the small curve's filtration, with the curve stopped at its exit).

A1-EIGHTSEED's `IsColumnStoch` (and A1-G3CALC's `isColumnStoch_g3Rec`) ask for the adaptedness of the stopped drift part
`D u = W(u ∧ S) − √κ̂ B u` and of the force coordinates masked by `{u ≤ S}`. For a strongly progressive driver and
force points (a regular marginal, also after `IsRegMarginal.exists_patch`) and a stopping time `S`:

* `stopDrv_extPath_coe`, **`measurable_stopDrv_of_progressive`**: the stopped driver is adapted (Mathlib's
  `IsStronglyProgressive.stronglyAdapted_stoppedProcess`);
* **`measurable_g3ColD`**: A1-G3CALC's drift part `g3ColD` is adapted (`hDm`);
* **`measurable_mask_of_progressive`**: a progressive coordinate masked by `{u ≤ S}` is adapted;
* **`fwdMap_stopDrv_add_eq`**: on the rectangle the record's source coordinate `V₀ = Re g_u(p) + W_u` is the path's
  force
  point started at `p` (A1-SEEDFIELD's `fwdMap_add_eq_force`), so the masked `V₀` is adapted;
* **`measurable_mask_g3Rec_V`**, **`measurable_mask_g3Rec_V₀`**: the clauses `hVm`, `hV₀m` of `isColumnStoch_g3Rec`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Common

open QuantumZipper (fwdMap)
open A2X A1EightSeed A1SeedField A1G3Calc

/-- The stopped extended path at a nonnegative time reads the path at the minimum. -/
theorem stopDrv_extPath_coe (w : ℝ≥0 → ℝ) (S u : ℝ≥0) : A1Ref.stopDrv (Strip.extPath w) S u = w (min u S) := by
  simp only [A1Ref.stopDrv, Strip.extPath]
  congr 1
  rw [max_eq_right (le_min u.coe_nonneg S.coe_nonneg), ← NNReal.coe_min, Real.toNNReal_coe]

section Adapted

variable {X : Type*} {mX : MeasurableSpace X} {𝓕 : Filtration ℝ≥0 mX}

/-- **The stopped driver is adapted**: for a strongly progressive `W` and a stopping time `S`,
`x ↦ W(u ∧ S x) x` is `𝓕_u`-measurable. -/
theorem measurable_stopDrv_of_progressive {W : ℝ≥0 → X → ℝ} (hW : IsStronglyProgressive 𝓕 W) {S : X → ℝ≥0}
    (hS : IsStoppingTime 𝓕 fun x => (S x : WithTop ℝ≥0)) (u : ℝ≥0) :
    Measurable[𝓕 u] fun x => A1Ref.stopDrv (Strip.extPath (W · x)) (S x) u := by
  have h := (hW.stronglyAdapted_stoppedProcess hS u).measurable
  have e : stoppedProcess W (fun x => (S x : WithTop ℝ≥0)) u =
      fun x => A1Ref.stopDrv (Strip.extPath (W · x)) (S x) u := by
    funext x
    rw [stopDrv_extPath_coe, stoppedProcess, ← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top,
      WithTop.untop_coe]
  rwa [e] at h

/-- **A1-G3CALC's drift part is adapted** (`hDm` of `isColumnStoch_g3Rec`). -/
theorem measurable_g3ColD {κ : ℝ} {W₁ B₁ : ℝ≥0 → X → ℝ} (hW : IsStronglyProgressive 𝓕 W₁)
    (hB : Adapted 𝓕 B₁) {S₁ : ℕ → X → ℝ≥0} {m : ℕ} (hS : IsStoppingTime 𝓕 fun x => (S₁ m x : WithTop ℝ≥0))
    (u : ℝ≥0) : Measurable[𝓕 u] (g3ColD κ W₁ B₁ S₁ m u) :=
  (measurable_stopDrv_of_progressive hW hS u).sub (measurable_const.mul (hB u))

/-- The event `{u ≤ S}` of a stopping time is in `𝓕_u`. -/
theorem measurableSet_le_stop {S : X → ℝ≥0} (hS : IsStoppingTime 𝓕 fun x => (S x : WithTop ℝ≥0)) (u : ℝ≥0) :
    MeasurableSet[𝓕 u] {x | u ≤ S x} := by
  have h := (hS.measurableSet_lt u).compl
  convert h using 1
  ext x
  simp only [mem_ofPred_eq, mem_compl_iff, not_lt, WithTop.coe_le_coe]

/-- **A progressive coordinate masked by `{u ≤ S}` is adapted.** -/
theorem measurable_mask_of_progressive {V : ℝ≥0 → X → ℝ} (hV : IsStronglyProgressive 𝓕 V) {S : X → ℝ≥0}
    (hS : IsStoppingTime 𝓕 fun x => (S x : WithTop ℝ≥0)) (u : ℝ≥0) :
    Measurable[𝓕 u] ({x | u ≤ S x}.indicator fun x => V u x) :=
  (hV.stronglyAdapted u).measurable.indicator (measurableSet_le_stop hS u)

/-- Masked functions that agree on the mask have the same measurability. -/
theorem measurable_mask_congr {S : X → ℝ≥0} {u : ℝ≥0} {f g : X → ℝ} (hfg : ∀ x, u ≤ S x → f x = g x)
    (hg : Measurable[𝓕 u] ({x | u ≤ S x}.indicator g)) : Measurable[𝓕 u] ({x | u ≤ S x}.indicator f) := by
  have e : {x | u ≤ S x}.indicator f = {x | u ≤ S x}.indicator g :=
    indicator_congr fun x hx => hfg x hx
  rwa [e]

end Adapted

/-! ### The record's source coordinate on the rectangle -/

section Source

/-- **The record's source coordinate is the path's force point** on the rectangle: for a path force point `v` started
at `p` that stays off the driver up to `S < ζ`, `Re g_u(p) + W_u = v u` for the driver stopped at `S` and `u ≤ S`. -/
theorem fwdMap_stopDrv_add_eq {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hvc : ContinuousOn v {t | (t : ℝ≥0∞) < ζ}) {p : ℝ}
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v t = p + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    {S : ℝ≥0} (hS : (S : ℝ≥0∞) < ζ) (hsep : ∀ r ≤ S, v r ≠ w r) {u : ℝ≥0} (hu : u ≤ S) :
    (fwdMap (A1Ref.stopDrv (Strip.extPath w) S) u p).re + A1Ref.stopDrv (Strip.extPath w) S u = v u := by
  have hc : ContinuousOn (Strip.extPath w) (Icc 0 (S : ℝ)) :=
    A1Ref.continuousOn_extPath_Icc hwc (by rw [ENNReal.ofReal_coe_nnreal]; exact hS)
  have h := fwdMap_add_eq_force hvc hveq hS hsep
    (A1Ref.continuous_stopDrv hc S.coe_nonneg).continuousOn (A1Ref.stopDrv_eqOn _ _)
    (t := u) ⟨u.coe_nonneg, NNReal.coe_le_coe.2 hu⟩
  rw [h, Strip.extPath, Real.toNNReal_coe]

end Source

/-! ### The (G3) column clauses -/

section G3

variable {X Y : Type*} {mX : MeasurableSpace X} {𝓕 : Filtration ℝ≥0 mX} {κ x y : ℝ}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {W₂ : ℝ≥0 → Y → ℝ}
  {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {t₂ : ℝ} {y₀ : Y}

/-- **(G3) The masked marks are adapted** (`hVm` of `isColumnStoch_g3Rec`). -/
theorem measurable_mask_g3Rec_V (hVL : ∀ i, IsStronglyProgressive 𝓕 (VL₁ i))
    (hVR : ∀ i, IsStronglyProgressive 𝓕 (VR₁ i)) (hS : IsStoppingTime 𝓕 fun x => (S₁ m x : WithTop ℝ≥0))
    (u : ℝ≥0) (k : Fin 3) :
    Measurable[𝓕 u] ({x | u ≤ S₁ m x}.indicator fun x => (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y₀)).V k u) := by
  have e : ∀ x, (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y₀)).V k u =
      (![VL₁ 0, VR₁ 0, VR₁ 1] : Fin 3 → ℝ≥0 → X → ℝ) k u x := fun x => by
    show g3Marks VL₁ VR₁ x k u = _
    fin_cases k <;> simp [g3Marks, Strip.extPath]
  simp_rw [e]
  fin_cases k
  · exact measurable_mask_of_progressive (hVL 0) hS u
  · exact measurable_mask_of_progressive (hVR 0) hS u
  · exact measurable_mask_of_progressive (hVR 1) hS u

/-- **(G3) The masked source coordinate is adapted** (`hV₀m` of `isColumnStoch_g3Rec`): on the rectangle it is the
path's force point `V_R(2)` started at `p = −y`. -/
theorem measurable_mask_g3Rec_V₀ {ζ₁ : X → ℝ≥0∞} {B₁ : ℝ≥0 → X → ℝ}
    (hP : ∀ ω, IsIntegratedSLEPath (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) (W₁ · ω)
      (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (hVR : ∀ i, IsStronglyProgressive 𝓕 (VR₁ i)) (hS : IsStoppingTime 𝓕 fun x => (S₁ m x : WithTop ℝ≥0))
    (hT : ∀ ω, (S₁ m ω : ℝ≥0∞) < ζ₁ ω) (hneP : ∀ ω (s : ℝ≥0), s ≤ S₁ m ω → VR₁ 2 s ω ≠ W₁ s ω) (u : ℝ≥0) :
    Measurable[𝓕 u] ({x | u ≤ S₁ m x}.indicator fun x => (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y₀)).V₀ u) := by
  refine measurable_mask_congr (g := fun x => VR₁ 2 u x) (fun ω hu => ?_)
    (measurable_mask_of_progressive (hVR 2) hS u)
  have hp := hP ω
  show (fwdMap (eightDrv W₁ S₁ m ω) u ((-y : ℝ) : ℂ)).re + eightDrv W₁ S₁ m ω u = VR₁ 2 u ω
  exact fwdMap_stopDrv_add_eq hp.2.2.2.1 (hp.2.2.2.2.2.1 2)
    (fun t ht => by simpa using hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t ht 2)
    (hT ω) (hneP ω) hu

end G3

/-! ### The (Eight) column clauses -/

section Eight

variable {X Y : Type*} {mX : MeasurableSpace X} {𝓕 : Filtration ℝ≥0 mX} {κ x : ℝ}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {W₂ : ℝ≥0 → Y → ℝ}
  {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {t₂ : ℝ} {y₀ : Y}

/-- **(Eight) The masked seeds are adapted** (the `V` clause of `IsColumnStoch` for `eightRec`). -/
theorem measurable_mask_eightRec_V (hVL : ∀ i, IsStronglyProgressive 𝓕 (VL₁ i))
    (hVR : ∀ i, IsStronglyProgressive 𝓕 (VR₁ i)) (hS : IsStoppingTime 𝓕 fun x => (S₁ m x : WithTop ℝ≥0))
    (u : ℝ≥0) (k : Fin 2) :
    Measurable[𝓕 u] ({ω | u ≤ S₁ m ω}.indicator fun ω => (eightRec κ (-x) W₁ VL₁ VR₁ W₂ S₁ m t₂ (ω, y₀)).V k u) := by
  have e : ∀ ω, (eightRec κ (-x) W₁ VL₁ VR₁ W₂ S₁ m t₂ (ω, y₀)).V k u =
      (![VL₁ 0, VR₁ 0] : Fin 2 → ℝ≥0 → X → ℝ) k u ω := fun ω => by
    show eightMarks VL₁ VR₁ ω k u = _
    fin_cases k <;> simp [eightMarks, Strip.extPath]
  simp_rw [e]
  fin_cases k
  · exact measurable_mask_of_progressive (hVL 0) hS u
  · exact measurable_mask_of_progressive (hVR 0) hS u

/-- **(Eight) The masked source coordinate is adapted** (the `V₀` clause of `IsColumnStoch` for `eightRec`): on the
rectangle it is the path's force point `V_R(1)` started at `p = −x`. -/
theorem measurable_mask_eightRec_V₀ {ζ₁ : X → ℝ≥0∞} {B₁ : ℝ≥0 → X → ℝ}
    (hP : ∀ ω, IsIntegratedSLEPath (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) (W₁ · ω)
      (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (hVR : ∀ i, IsStronglyProgressive 𝓕 (VR₁ i)) (hS : IsStoppingTime 𝓕 fun x => (S₁ m x : WithTop ℝ≥0))
    (hT : ∀ ω, (S₁ m ω : ℝ≥0∞) < ζ₁ ω) (hneP : ∀ ω (s : ℝ≥0), s ≤ S₁ m ω → VR₁ 1 s ω ≠ W₁ s ω) (u : ℝ≥0) :
    Measurable[𝓕 u] ({ω | u ≤ S₁ m ω}.indicator fun ω => (eightRec κ (-x) W₁ VL₁ VR₁ W₂ S₁ m t₂ (ω, y₀)).V₀ u) := by
  refine measurable_mask_congr (g := fun ω => VR₁ 1 u ω) (fun ω hu => ?_)
    (measurable_mask_of_progressive (hVR 1) hS u)
  have hp := hP ω
  show (fwdMap (eightDrv W₁ S₁ m ω) u ((-x : ℝ) : ℂ)).re + eightDrv W₁ S₁ m ω u = VR₁ 1 u ω
  exact fwdMap_stopDrv_add_eq hp.2.2.2.1 (hp.2.2.2.2.2.1 1)
    (fun t ht => by simpa using hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t ht 1)
    (hT ω) (hneP ω) hu

/-- **(Eight, small) The other source is off the driver before the lifetime** at a good sample (the `hneP` input of
`measurable_mask_eightRec_V₀`): at `0` it is `−x ≠ 0`, later `w < v_R(0) ≤ v_R(1)`. -/
theorem smallEight_sepP_of_good (hx : x < 0) {w : ℝ≥0 → ℝ} {vL : Fin 1 → ℝ≥0 → ℝ} {vR : Fin 2 → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hP : IsIntegratedSLEPath (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) w vL vR b ζ)
    (hg : GoodSmallEight w vL vR b ζ) (s : ℝ≥0) (hsζ : (s : ℝ≥0∞) < ζ) : vR 1 s ≠ w s := by
  rcases eq_zero_or_pos s with rfl | hs
  · rw [hP.2.2.1 1, hP.1]; simp; linarith
  · have h1 := (hg s hs hsζ).2
    have h2 : vR 0 s ≤ vR 1 s := hP.2.2.2.2.2.2.2.2.2.1 s hsζ (show (0 : Fin 2) ≤ 1 by decide)
    exact (h1.trans_le h2).ne'

end Eight

end InteractingSLE.ZhanGT4.A1Common
