/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1CommonStoch
import InteractingSLE.Spec.ZhanGT4.TwoTime2Other

/-!
# Zhan's A.1: the masked derivative factor `G₀` of a source column is adapted

Packet PROVE-A1-ASSEMBLE. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L300–L355: the column
martingale is run in the small curve's filtration, with the curve stopped at its exit).

A1-EIGHTSEED's `IsColumnStoch` (and A1-G3CALC's `isColumnStoch_g3Rec`) ask that the record's derivative factor
`G₀ u = Re g_u'(p)` of the other source `p`, masked by `{u ≤ S}`, be `𝓕_u`-measurable. On the rectangle the other
source is the path's force point `v` started at `p`, so

`G₀ u = exp(−∫₀ᵘ 2/(v − w)²)`   (`re_deriv_fwdMap_stopDrv_eq`),

the boundary form of `g_u' = exp(log g_u')` on the alive disc of `p` (`deriv_fwdMap_aliveDisc`). A parametric integral
of a progressive integrand over `[0, u]` is `𝓕_u`-measurable (`measurable_integral_of_progressive`; Fubini's
measurability `StronglyMeasurable.integral_prod_right` on `Iic u × X`). Hence:

* **`measurable_mask_g3Rec_G₀`**: the clause `hG₀m` of `isColumnStoch_g3Rec`;
* **`measurable_mask_eightRec_G₀`**: the same clause for `eightRec`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Asm

open QuantumZipper (fwdMap logDerivFwd)
open A2X A1EightSeed A1SeedField A1G3Calc A1Common

/-! ### The derivative factor on the rectangle -/

section Deriv

/-- **The derivative factor of the other source on the rectangle.** For a path force point `v` started at `p` that
stays off the driver up to `S < ζ`, the derivative at `p` of the Loewner map of the driver stopped at `S` is, for
`u ≤ S`, `Re g_u'(p) = exp(−∫₀ᵘ 2/(v − w)²)`. -/
theorem re_deriv_fwdMap_stopDrv_eq {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hvc : ContinuousOn v {t | (t : ℝ≥0∞) < ζ}) {p : ℝ}
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v t = p + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    {S : ℝ≥0} (hS : (S : ℝ≥0∞) < ζ) (hsep : ∀ r ≤ S, v r ≠ w r) {u : ℝ≥0} (hu : u ≤ S) :
    (deriv (fwdMap (A1Ref.stopDrv (Strip.extPath w) S) u) p).re =
      Real.exp (-∫ s in (0 : ℝ)..u, 2 / (v s.toNNReal - w s.toNNReal) ^ 2) := by
  set W := A1Ref.stopDrv (Strip.extPath w) S with hWdef
  have hc : ContinuousOn (Strip.extPath w) (Icc 0 (S : ℝ)) :=
    A1Ref.continuousOn_extPath_Icc hwc (by rw [ENNReal.ofReal_coe_nnreal]; exact hS)
  have hW : Continuous W := A1Ref.continuous_stopDrv hc S.coe_nonneg
  have hEq : EqOn W (Strip.extPath w) (Icc 0 (S : ℝ)) := A1Ref.stopDrv_eqOn _ _
  have hsol := A1G3Calc.isForwardSol_of_force hvc hveq hS hsep hW.continuousOn hEq
  obtain ⟨δ, hδ, hlow, hpp⟩ := exists_aliveDisc_self hsol S.coe_nonneg
  have hu' : (u : ℝ) ∈ Icc (0 : ℝ) S := ⟨u.coe_nonneg, NNReal.coe_le_coe.2 hu⟩
  rw [deriv_fwdMap_aliveDisc hW hsol hδ hlow hpp hu', logDerivFwd]
  have e : ∫ s in (0 : ℝ)..u, (2 : ℂ) / (fwdMap W s (p : ℂ)) ^ 2 =
      ((∫ s in (0 : ℝ)..u, 2 / (v s.toNNReal - w s.toNNReal) ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le u.coe_nonneg] at hs
    have hsS : s ∈ Icc (0 : ℝ) S := ⟨hs.1, hs.2.trans hu'.2⟩
    rw [InteractingSLE.fwdMap_eq_of_isForwardSol hW hsol hsS, hEq hsS]
    simp only [Strip.extPath]
    push_cast
    ring
  rw [e, ← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_re]

end Deriv

/-! ### Parametric integrals of progressive processes -/

section Integral

/-- **A parametric integral over `[0, u]` of a jointly measurable function on `Iic u × X` is measurable.** -/
theorem measurable_integral_Iic {X : Type*} [MeasurableSpace X] {u : ℝ≥0} {F : Set.Iic u × X → ℝ}
    (hF : Measurable F) :
    Measurable fun x => ∫ s in (0 : ℝ)..u, F (⟨min s.toNNReal u, Set.mem_Iic.2 (min_le_right _ _)⟩, x) := by
  have hφ : Measurable fun q : X × ℝ =>
      ((⟨min q.2.toNNReal u, Set.mem_Iic.2 (min_le_right _ _)⟩ : Set.Iic u), q.1) := by
    refine Measurable.prodMk ?_ measurable_fst
    exact (measurable_real_toNNReal.comp measurable_snd).min measurable_const |>.subtype_mk
  have hG : StronglyMeasurable fun q : X × ℝ => F (⟨min q.2.toNNReal u, Set.mem_Iic.2 (min_le_right _ _)⟩, q.1) :=
    (hF.comp hφ).stronglyMeasurable
  have h := hG.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) u))
  have e : (fun x => ∫ s in (0 : ℝ)..u, F (⟨min s.toNNReal u, Set.mem_Iic.2 (min_le_right _ _)⟩, x)) =
      fun x => ∫ s, F (⟨min (x, s).2.toNNReal u, Set.mem_Iic.2 (min_le_right _ _)⟩, (x, s).1)
        ∂(volume.restrict (Ioc (0 : ℝ) u)) := by
    funext x
    rw [intervalIntegral.integral_of_le u.coe_nonneg]
  rw [e]
  exact h.measurable

variable {X : Type*} {mX : MeasurableSpace X} {𝓕 : Filtration ℝ≥0 mX}

/-- **A parametric integral of a progressive process over `[0, u]` is `𝓕_u`-measurable.** -/
theorem measurable_integral_of_progressive {f : ℝ≥0 → X → ℝ} (hf : IsStronglyProgressive 𝓕 f) (u : ℝ≥0) :
    Measurable[𝓕 u] fun x => ∫ s in (0 : ℝ)..u, f s.toNNReal x := by
  have h := @measurable_integral_Iic X (𝓕 u) u (fun q => f q.1 q.2) (hf u).measurable
  convert h using 2 with x
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le u.coe_nonneg] at hs
  have hle : s.toNNReal ≤ u := Real.toNNReal_le_iff_le_coe.2 hs.2
  simp only [min_eq_left hle]

/-- **The masked derivative factor is adapted**: if on `{u ≤ S}` a function equals `exp(−∫₀ᵘ 2/(V − W)²)` for
progressive `V`, `W`, its mask by `{u ≤ S}` is `𝓕_u`-measurable. -/
theorem measurable_mask_of_exp_integral {V W : ℝ≥0 → X → ℝ} (hV : IsStronglyProgressive 𝓕 V)
    (hW : IsStronglyProgressive 𝓕 W) {S : X → ℝ≥0} (hS : IsStoppingTime 𝓕 fun x => (S x : WithTop ℝ≥0))
    {u : ℝ≥0} {G : X → ℝ}
    (hG : ∀ x, u ≤ S x → G x = Real.exp (-∫ s in (0 : ℝ)..u, 2 / (V s.toNNReal x - W s.toNNReal x) ^ 2)) :
    Measurable[𝓕 u] ({x | u ≤ S x}.indicator G) := by
  have hpr : IsStronglyProgressive 𝓕 fun t x => 2 / (V t x - W t x) ^ 2 := fun i => by
    have h1 := (hV i).measurable
    have h2 := (hW i).measurable
    exact (measurable_const.div ((h1.sub h2).pow_const 2)).stronglyMeasurable
  have hI := measurable_integral_of_progressive hpr u
  refine measurable_mask_congr (fun x hx => hG x hx) ?_
  exact (Real.measurable_exp.comp hI.neg).indicator (measurableSet_le_stop hS u)

end Integral

/-! ### The two cases -/

section Cases

variable {X Y : Type*} {mX : MeasurableSpace X} {𝓕 : Filtration ℝ≥0 mX} {κ x y : ℝ}
  {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {t₂ : ℝ} {y₀ : Y} {ζ₁ : X → ℝ≥0∞} {B₁ : ℝ≥0 → X → ℝ}

/-- **(G3) The masked derivative factor is adapted** (`hG₀m` of `isColumnStoch_g3Rec`): on the rectangle
`G₀ u = exp(−∫₀ᵘ 2/(V_R(2) − W)²)`, a parametric integral of progressive processes. -/
theorem measurable_mask_g3Rec_G₀ {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ}
    (hP : ∀ ω, IsIntegratedSLEPath (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) (W₁ · ω)
      (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (hW : IsStronglyProgressive 𝓕 W₁) (hVR : ∀ i, IsStronglyProgressive 𝓕 (VR₁ i))
    (hS : IsStoppingTime 𝓕 fun x => (S₁ m x : WithTop ℝ≥0)) (hT : ∀ ω, (S₁ m ω : ℝ≥0∞) < ζ₁ ω)
    (hneP : ∀ ω (s : ℝ≥0), s ≤ S₁ m ω → VR₁ 2 s ω ≠ W₁ s ω) (u : ℝ≥0) :
    Measurable[𝓕 u] ({x | u ≤ S₁ m x}.indicator fun x => (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y₀)).G₀ u) := by
  refine measurable_mask_of_exp_integral (hVR 2) hW hS fun ω hu => ?_
  have hp := hP ω
  show (deriv (fwdMap (eightDrv W₁ S₁ m ω) u) ((-y : ℝ) : ℂ)).re = _
  exact re_deriv_fwdMap_stopDrv_eq hp.2.2.2.1 (hp.2.2.2.2.2.1 2)
    (fun t ht => by simpa using hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t ht 2) (hT ω) (hneP ω) hu

/-- **(Eight) The masked derivative factor is adapted** (the `G₀` clause of `IsColumnStoch` for `eightRec`): on the
rectangle `G₀ u = exp(−∫₀ᵘ 2/(V_R(1) − W)²)`. -/
theorem measurable_mask_eightRec_G₀ {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ}
    (hP : ∀ ω, IsIntegratedSLEPath (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) (W₁ · ω)
      (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (hW : IsStronglyProgressive 𝓕 W₁) (hVR : ∀ i, IsStronglyProgressive 𝓕 (VR₁ i))
    (hS : IsStoppingTime 𝓕 fun x => (S₁ m x : WithTop ℝ≥0)) (hT : ∀ ω, (S₁ m ω : ℝ≥0∞) < ζ₁ ω)
    (hneP : ∀ ω (s : ℝ≥0), s ≤ S₁ m ω → VR₁ 1 s ω ≠ W₁ s ω) (u : ℝ≥0) :
    Measurable[𝓕 u] ({ω | u ≤ S₁ m ω}.indicator fun ω =>
      (eightRec κ (-x) W₁ VL₁ VR₁ W₂ S₁ m t₂ (ω, y₀)).G₀ u) := by
  refine measurable_mask_of_exp_integral (hVR 1) hW hS fun ω hu => ?_
  have hp := hP ω
  show (deriv (fwdMap (eightDrv W₁ S₁ m ω) u) ((-x : ℝ) : ℂ)).re = _
  exact re_deriv_fwdMap_stopDrv_eq hp.2.2.2.1 (hp.2.2.2.2.2.1 1)
    (fun t ht => by simpa using hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t ht 1) (hT ω) (hneP ω) hu

end Cases

end InteractingSLE.ZhanGT4.A1Asm
