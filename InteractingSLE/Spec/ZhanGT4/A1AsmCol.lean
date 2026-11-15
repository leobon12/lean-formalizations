/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1AsmG0

/-!
# Zhan's A.1: the stochastic half of the source columns, for both cases

Packet PROVE-A1-ASSEMBLE. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L300–L355).

A1-EIGHTSEED's `IsColumnStoch` for the Eight records `eightRec` (A1-COMMON "What remains" 3), mirroring A1-G3CALC's
`isColumnStoch_g3Rec`, with `B = B₁` and the word-agnostic drift part `D = g3ColD` (`W^{stop} − √κ̂ B₁`):

* `eightRec_W_eq_driftDriver`: the record's driver is `√κ̂ B₁ + D`;
* **`hasDerivWithinAt_eightRec_drift`**: on `(0, S]`, `D` has the Eight record's drift as derivative (the path drift
  of `hasDerivWithinAt_pathDrift` is the record's drift: SEEDFIELD's `drift_fromSource_eq`, the other source's
  own-chart coordinate is its force point, `smallEightRhoR κ 1 = −κ̂/2`);
* `isColumnStoch_eightRec`: `IsColumnStoch` from the Brownian and measurability inputs;
* **`isColumnStoch_eightRec_of_reg`**, **`isColumnStoch_g3Rec_of_reg`**: `IsColumnStoch` for both cases from a regular
  small marginal with continuous Brownian paths at every sample, a stopping time before the lifetime and the pathwise
  separations only — every measurability clause is discharged (A1-COMMON's masks and `measurable_g3ColD`, and the
  masked `G₀` of `A1AsmG0`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Asm

open QuantumZipper (fwdMap fwdHull)
open A2X A1EightSeed A1SeedField A1G3Calc A1Common

section Eight

variable {X Y : Type*}

/-- **The Eight record's driver is `√κ̂ B₁ + D`** (`IsColumnStoch`'s driver clause, `D = g3ColD`). -/
theorem eightRec_W_eq_driftDriver (κ p : ℝ) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ)
    (VR₁ : Fin 2 → ℝ≥0 → X → ℝ) (W₂ : ℝ≥0 → Y → ℝ) (B₁ : ℝ≥0 → X → ℝ) (S₁ : ℕ → X → ℝ≥0) (m : ℕ) (t₂ : ℝ) (x : X)
    (y : Y) :
    (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y)).W = driftDriver (Real.sqrt (kh κ)) B₁ (g3ColD κ W₁ B₁ S₁ m) x := by
  funext t
  show eightDrv W₁ S₁ m x t = driftDriver (Real.sqrt (kh κ)) B₁ (g3ColD κ W₁ B₁ S₁ m) x t
  simp only [driftDriver, g3ColD]
  rw [eightDrv_toNNReal]
  ring

/-- **`D` has the Eight record's drift as derivative on `(0, S]`**: at a sample where the small curve's path relation
holds (parameter `κ̂`, the Eight weights, the other source at `x_R(1) = p`), the exit is before the lifetime, the seeds
are off the driver at positive times up to the exit, and the other source is off the driver up to the exit. -/
theorem hasDerivWithinAt_eightRec_drift {κ p : ℝ} {xL : Fin 1 → ℝ} {xR : Fin 2 → ℝ} {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {t₂ : ℝ} {x : X} {y : Y}
    (hP : IsIntegratedSLEPath (kh κ) xL xR (smallEightRhoL κ) (smallEightRhoR κ) (W₁ · x) (fun i s => VL₁ i s x)
      (fun i s => VR₁ i s x) (B₁ · x) (ζ₁ x))
    (hk : kh κ ≠ 0) (hxp : xR 1 = p) (hT : (S₁ m x : ℝ≥0∞) < ζ₁ x)
    (hneL : ∀ s : ℝ≥0, 0 < s → s ≤ S₁ m x → VL₁ 0 s x ≠ W₁ s x)
    (hneR : ∀ s : ℝ≥0, 0 < s → s ≤ S₁ m x → VR₁ 0 s x ≠ W₁ s x)
    (hneP : ∀ s : ℝ≥0, s ≤ S₁ m x → VR₁ 1 s x ≠ W₁ s x) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) (S₁ m x)) :
    HasDerivWithinAt (fun u : ℝ => g3ColD κ W₁ B₁ S₁ m u.toNNReal x)
      ((eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y)).drift t) (Ioc 0 (S₁ m x : ℝ)) t := by
  have hWc := continuous_eightDrv (S₁ := S₁) (m := m) hP.2.2.2.1 hT
  have hEq := eightDrv_eqOn W₁ S₁ m x
  have hD : ∀ u ∈ Icc (0 : ℝ) (S₁ m x), g3ColD κ W₁ B₁ S₁ m u.toNNReal x =
      W₁ u.toNNReal x - Real.sqrt (kh κ) * B₁ u.toNNReal x := by
    intro u hu
    simp only [g3ColD]
    rw [eightDrv_toNNReal, hEq hu]
    rfl
  have hd := hasDerivWithinAt_pathDrift hP hT
    (fun i s hs hsS => by fin_cases i; exact hneL s hs hsS)
    (fun j s hs hsS => by
      fin_cases j
      · exact hneR s hs hsS
      · exact hneP s hsS)
    (D := fun u : ℝ => g3ColD κ W₁ B₁ S₁ m u.toNNReal x) hD ht
  refine hd.congr_deriv ?_
  obtain ⟨-, -, -, -, -, hcR, -, -, -, -, -, -, -, -, hReq, -⟩ := id hP
  have hV0 : (fwdMap (eightDrv W₁ S₁ m x) t p).re + eightDrv W₁ S₁ m x t = VR₁ 1 t.toNNReal x := by
    have h := fwdMap_add_eq_force (hcR 1) (fun s hs => hReq s hs 1) hT hneP hWc.continuousOn hEq
      (Ioc_subset_Icc_self ht)
    rw [hxp] at h
    exact h
  have hWt : eightDrv W₁ S₁ m x t = W₁ t.toNNReal x := hEq (Ioc_subset_Icc_self ht)
  have hdr : (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y)).drift t =
      smallEightRhoL κ 0 / (eightDrv W₁ S₁ m x t - Strip.extPath (VL₁ 0 · x) t)
        + smallEightRhoR κ 0 / (eightDrv W₁ S₁ m x t - Strip.extPath (VR₁ 0 · x) t)
        + -(kh κ / 2) / (eightDrv W₁ S₁ m x t - ((fwdMap (eightDrv W₁ S₁ m x) t p).re + eightDrv W₁ S₁ m x t)) :=
    drift_fromSource_eq (eightDrv W₁ S₁ m x) _ _ _ hk (smallEightRhoL κ 0) (smallEightRhoR κ 0) _ p
      (Strip.extPath (VL₁ 0 · x)) (Strip.extPath (VR₁ 0 · x)) t
  rw [hdr, hV0, hWt]
  have h2 : smallEightRhoR κ 1 = -(kh κ / 2) := rfl
  simp only [Fin.sum_univ_one, Fin.sum_univ_two, Strip.extPath, h2]
  ring

/-- **The stochastic half of an Eight column from its Brownian and measurability inputs** (`B = B₁`, `D = g3ColD`). -/
theorem isColumnStoch_eightRec {mX : MeasurableSpace X} {𝓕 : Filtration ℝ≥0 mX} {P : Measure X} {κ p : ℝ}
    {xL : Fin 1 → ℝ} {xR : Fin 2 → ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0}
    {m : ℕ} {t₂ : ℝ} {y : Y}
    (hB : IsFilteredBrownianReal 𝓕 B₁ P) (hBc : ∀ x, Continuous (B₁ · x))
    (hDm : ∀ u, Measurable[𝓕 u] (g3ColD κ W₁ B₁ S₁ m u))
    (hP : ∀ x, IsIntegratedSLEPath (kh κ) xL xR (smallEightRhoL κ) (smallEightRhoR κ) (W₁ · x)
      (fun i s => VL₁ i s x) (fun i s => VR₁ i s x) (B₁ · x) (ζ₁ x))
    (hk : kh κ ≠ 0) (hxp : xR 1 = p) (hT : ∀ x, (S₁ m x : ℝ≥0∞) < ζ₁ x)
    (hneL : ∀ x (s : ℝ≥0), 0 < s → s ≤ S₁ m x → VL₁ 0 s x ≠ W₁ s x)
    (hneR : ∀ x (s : ℝ≥0), 0 < s → s ≤ S₁ m x → VR₁ 0 s x ≠ W₁ s x)
    (hneP : ∀ x (s : ℝ≥0), s ≤ S₁ m x → VR₁ 1 s x ≠ W₁ s x)
    (hVm : ∀ (u : ℝ≥0) k, Measurable[𝓕 u] ({x | u ≤ S₁ m x}.indicator fun x =>
      (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y)).V k u))
    (hV₀m : ∀ u : ℝ≥0, Measurable[𝓕 u] ({x | u ≤ S₁ m x}.indicator fun x =>
      (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y)).V₀ u))
    (hG₀m : ∀ u : ℝ≥0, Measurable[𝓕 u] ({x | u ≤ S₁ m x}.indicator fun x =>
      (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y)).G₀ u)) :
    IsColumnStoch 𝓕 P (kh κ) (fun x => eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y)) (S₁ m) B₁
      (g3ColD κ W₁ B₁ S₁ m) :=
  ⟨hB, hBc, hDm, fun x => continuous_g3ColD (hP x).2.2.2.1 (hT x) (hBc x),
    fun x => eightRec_W_eq_driftDriver κ p W₁ VL₁ VR₁ W₂ B₁ S₁ m t₂ x y,
    fun x _ ht => hasDerivWithinAt_eightRec_drift (hP x) hk hxp (hT x) (hneL x) (hneR x) (hneP x) ht,
    hVm, hV₀m, hG₀m⟩

end Eight

/-! ### From a regular small marginal -/

section Reg

variable {X Y : Type*} {mX : MeasurableSpace X} {𝓕 : Filtration ℝ≥0 mX} {P : Measure X} {κ x y : ℝ}
  {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {t₂ : ℝ} {y₀ : Y} {ζ₁ : X → ℝ≥0∞} {B₁ : ℝ≥0 → X → ℝ}

/-- **(Eight) `IsColumnStoch` from a regular small marginal.** For a regular small Eight marginal (parameter `κ̂`) whose
Brownian paths are continuous at every sample, a stopping time `S₁ m` before the lifetime at every sample, the seeds off
the driver at positive times up to it, and the other source off the driver up to it, every clause of `IsColumnStoch`
holds for the Eight records of rectangle `m` (`B = B₁`, `D = g3ColD`). -/
theorem isColumnStoch_eightRec_of_reg (hκ : 0 < kh κ) {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → X → ℝ}
    (h : A1Marg.IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P 𝓕 W₁ VL₁ VR₁ B₁ ζ₁)
    (hBc : ∀ ω, Continuous (B₁ · ω)) (hS : IsStoppingTime 𝓕 fun x => (S₁ m x : WithTop ℝ≥0))
    (hT : ∀ ω, (S₁ m ω : ℝ≥0∞) < ζ₁ ω)
    (hneL : ∀ ω (s : ℝ≥0), 0 < s → s ≤ S₁ m ω → VL₁ 0 s ω ≠ W₁ s ω)
    (hneR : ∀ ω (s : ℝ≥0), 0 < s → s ≤ S₁ m ω → VR₁ 0 s ω ≠ W₁ s ω)
    (hneP : ∀ ω (s : ℝ≥0), s ≤ S₁ m ω → VR₁ 1 s ω ≠ W₁ s ω) :
    IsColumnStoch 𝓕 P (kh κ) (fun ω => eightRec κ (-x) W₁ VL₁ VR₁ W₂ S₁ m t₂ (ω, y₀)) (S₁ m) B₁
      (g3ColD κ W₁ B₁ S₁ m) :=
  isColumnStoch_eightRec h.evol.1 hBc (measurable_g3ColD h.progW h.evol.1.2.1 hS) h.path hκ.ne'
    (by simp) hT hneL hneR hneP (measurable_mask_eightRec_V h.progVL h.progVR hS)
    (measurable_mask_eightRec_V₀ h.path h.progVR hS hT hneP)
    (measurable_mask_eightRec_G₀ h.path h.progW h.progVR hS hT hneP)

/-- **(G3) `IsColumnStoch` from a regular small marginal** (`isColumnStoch_g3Rec` with every measurability clause
discharged). -/
theorem isColumnStoch_g3Rec_of_reg (hκ : 0 < kh κ) {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → X → ℝ}
    (h : A1Marg.IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P 𝓕 W₁ VL₁ VR₁ B₁ ζ₁)
    (hBc : ∀ ω, Continuous (B₁ · ω)) (hS : IsStoppingTime 𝓕 fun x => (S₁ m x : WithTop ℝ≥0))
    (hT : ∀ ω, (S₁ m ω : ℝ≥0∞) < ζ₁ ω)
    (hneL : ∀ ω (s : ℝ≥0), 0 < s → s ≤ S₁ m ω → VL₁ 0 s ω ≠ W₁ s ω)
    (hneR : ∀ ω j (s : ℝ≥0), 0 < s → s ≤ S₁ m ω → VR₁ j s ω ≠ W₁ s ω)
    (hneP : ∀ ω (s : ℝ≥0), s ≤ S₁ m ω → VR₁ 2 s ω ≠ W₁ s ω) :
    IsColumnStoch 𝓕 P (kh κ) (fun ω => g3Rec κ (-y) W₁ VL₁ VR₁ W₂ S₁ m t₂ (ω, y₀)) (S₁ m) B₁
      (g3ColD κ W₁ B₁ S₁ m) :=
  isColumnStoch_g3Rec h.evol.1 hBc (measurable_g3ColD h.progW h.evol.1.2.1 hS) h.path hκ.ne'
    (by simp) hT hneL hneR hneP (measurable_mask_g3Rec_V h.progVL h.progVR hS)
    (measurable_mask_g3Rec_V₀ h.path h.progVR hS hT hneP)
    (measurable_mask_g3Rec_G₀ h.path h.progW h.progVR hS hT hneP)

end Reg

end InteractingSLE.ZhanGT4.A1Asm
