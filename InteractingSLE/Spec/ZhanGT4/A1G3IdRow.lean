/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3IdDoleans
import InteractingSLE.Spec.ZhanGT4.A1G3RowLarge

/-!
# Zhan's A.1 (G3): the G3 row identity and the large direction's one-sample law under the patch density

Packet PROVE-A1-G3ROW2. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.5 (`ig1_followup_proofs.txt` L300–L425) and the
specification's proof of Theorem 2.2 (L488).

PROVE-A1-G3ROW reduced the large-curve direction of A.1 (G3) to the **G3 row identity** (its "What remains" 1): the
patch density equals, `P₂`-almost everywhere, the Girsanov density `Z_{T₀+1}` of the change to ordinary `SLE_κ` times
the frozen-curve density `M̃_S/M̃_0` of A1-LARGEDENS. This file proves it:

* **`seedHeightField_g3Rec_ae_eq_mul`** (the G3 row identity): the deterministic corner identity
  (`seedHeightField_g3Rec_eq`, with the Brownian path `B⁰ = B₂ + ∫θ` of the Girsanov change, whose driver is the
  large curve up to the exit, `drive_girsanov_removeAll_eq`) and the Doléans identification
  (`doleansDensity_removeAll_g3_ae_eq`);
* **`isSeedSampleLaw_g3Rec_of_girs`**: hence A1-LARGEDENS's one-sample law under the Girsanov measure transfers to the
  patch density `P₂.withDensity (fun y => ofReal (seedHeightField (g3Rec …) (x, y) s (S₂ m y)))` — the form
  `FrozenFamilyFst` asks for — given the measurability of the frozen-curve density.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Id

open QuantumZipper (H IsForwardSol fwdMap fwdHull drive)
open Girsanov G3Field A1SeedField A1EightSeed A1EightFin A1G3Calc A2X A1LargeDens A1G3Row A1Family

variable {X Y : Type*} [mY : MeasurableSpace Y]

/-- **The G3 row identity.** For A1-G3CALC's records `g3Rec` (other source `p`), one rectangle `m` and one small sample
`ω₁` at which the small rectangle data hold, and a large `SLE_κ(κ − 4, −4)` evolution (marks starting at the images
`xR 1 − p` of the ordinary mark and `−p` of the small source) whose rectangle data and force gaps in `[δ, R]` up to the
exit `S₂ m ≤ T₀` hold at every large sample: with `θ` the cut drift removing both marks up to `S₂ m`,
`B⁰ = B₂ + ∫ θ`, and any image chains `(a, W')` of `√κ B⁰` against the small hull frozen at `s ∈ (0, S₁ m ω₁]`,
`P₂`-almost surely

`ofReal (seedHeightField (g3Rec …) (ω₁, y) s (S₂ m y))
  = ofReal (Z_{T₀+1}(y)) · ofReal (girsDensity (√κ) B⁰ (S₂ m) ℓ⁰ y)`,

`ℓ⁰` the logarithm of A1-LARGEDENS's `frzDataOf` with the G3 large charges and the marks `x`, `y⁺`, `y⁻`. -/
theorem seedHeightField_g3Rec_ae_eq_mul {κ p a₀ δ R : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) {xL : Fin 1 → ℝ}
    {xR : Fin 3 → ℝ} {ρL : Fin 1 → ℝ} {ρR : Fin 3 → ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {S₁ : ℕ → X → ℝ≥0} {H₁ H₂ : Set ℂ}
    {δ' q dd Tm : ℝ} {m : ℕ} {ω₁ : X} (hpp : IsProtectedPairG H₁ H₂ δ' p q dd)
    (hP : IsIntegratedSLEPath a₀ xL xR ρL ρR (W₁ · ω₁) (fun i s => VL₁ i s ω₁) (fun i s => VR₁ i s ω₁) (B₁ · ω₁)
      (ζ₁ ω₁))
    (hxL : xL 0 = 0) (hxR : xR 0 = 0) (hxO : 0 < xR 1) (hxOq : xR 1 ≤ q)
    (hgood₁ : (S₁ m ω₁ : ℝ≥0∞) < ζ₁ ω₁ ∧ 0 < (S₁ m ω₁ : ℝ) ∧ (S₁ m ω₁ : ℝ) ≤ Tm ∧
      fwdHull (eightDrv W₁ S₁ m ω₁) (S₁ m ω₁) ⊆ H₁)
    (hsep₁ : ∀ s : ℝ≥0, 0 < s → (s : ℝ≥0∞) < ζ₁ ω₁ → VL₁ 0 s ω₁ ≠ W₁ s ω₁ ∧ VR₁ 0 s ω₁ ≠ W₁ s ω₁)
    (hsepO : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ₁ ω₁ → VR₁ 1 s ω₁ ≠ W₁ s ω₁)
    {P₂ : Measure Y} [IsProbabilityMeasure P₂] {𝓕₂ : Filtration ℝ≥0 mY} {xL₂ : Fin 2 → ℝ} {xR₂ ρR₂ : Fin 0 → ℝ}
    {W₂ B₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (hE₂ : IsIntegratedSLEEvolution κ xL₂ xR₂ ![κ - 4, -4] ρR₂ P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hB₂c : ∀ y, Continuous (B₂ · y)) {S₂ : ℕ → Y → ℝ≥0} {T₀ : ℝ≥0}
    (hp₂ : ∀ y, PathOn κ xL₂ xR₂ ρR₂ W₂ VL₂ VR₂ B₂ ζ₂ y (S₂ m y) δ)
    (hR₂ : ∀ y (r : ℝ≥0), r ≤ S₂ m y → ∀ i, |W₂ r y - VL₂ i r y| ≤ R) (hST : ∀ y, S₂ m y ≤ T₀)
    (hW₂p : IsStronglyProgressive 𝓕₂ W₂) (hVL₂p : ∀ i, IsStronglyProgressive 𝓕₂ (VL₂ i))
    (hS₂ : IsStoppingTime 𝓕₂ fun y => (S₂ m y : WithTop ℝ≥0)) (hx₂ : xL₂ 0 = xR 1 - p) (hy₂ : xL₂ 1 = -p)
    (hc₂ : ∀ y, ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 (S₂ m y))) (h0₂ : ∀ y, W₂ 0 y = 0)
    (hgood₂ : ∀ y, (S₂ m y : ℝ) ≤ Tm ∧ fwdHull (frzPath W₂ p (S₂ m y) y) (S₂ m y) ⊆ H₂)
    (hS₂pos : ∀ y, 0 < (S₂ m y : ℝ)) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (S₁ m ω₁)) {W' a : Y → ℝ → ℝ} {T : Y → ℝ}
    (hown : ∀ y, OwnData (drive κ (girsanovProcess B₂ (removeAllDrift κ δ ![κ - 4, -4] ρR₂
        (fun y => (S₂ m y : ℝ≥0∞)) ζ₂ W₂ VL₂ VR₂)) y) (fwdHull (fun u => eightDrv W₁ S₁ m ω₁ u - p) s)
      (frzChart (fun u => eightDrv W₁ S₁ m ω₁ u - p) s) (T y) (a y) (W' y))
    (hYT : ∀ y, (S₂ m y : ℝ) ≤ T y) :
    (fun y => ENNReal.ofReal (seedHeightField (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m) (ω₁, y) s (S₂ m y))) =ᵐ[P₂]
      fun y => ENNReal.ofReal (doleansDensity P₂ 𝓕₂ B₂ (removeAllDrift κ δ ![κ - 4, -4] ρR₂
          (fun y => (S₂ m y : ℝ≥0∞)) ζ₂ W₂ VL₂ VR₂) (T₀ + 1) y) *
        ENNReal.ofReal (girsDensity (Real.sqrt κ) (girsanovProcess B₂ (removeAllDrift κ δ ![κ - 4, -4] ρR₂
          (fun y => (S₂ m y : ℝ≥0∞)) ζ₂ W₂ VL₂ VR₂)) (S₂ m) (fun y' => (frzDataOf κ (girsanovProcess B₂
            (removeAllDrift κ δ ![κ - 4, -4] ρR₂ (fun y => (S₂ m y : ℝ≥0∞)) ζ₂ W₂ VL₂ VR₂)) W' a
          (frzChart (fun u => eightDrv W₁ S₁ m ω₁ u - p) s) (largeG3RR κ) (eightDrv W₁ S₁ m ω₁ s - p)
          ![Strip.extPath (VR₁ 1 · ω₁) s - p, Strip.extPath (VR₁ 0 · ω₁) s - p,
            Strip.extPath (VL₁ 0 · ω₁) s - p] y').ell) y) := by
  have hpq : xR 1 < p := hxOq.trans_lt hpp.pair.prot_lt
  have hxy₂ : xL₂ 0 ≠ xL₂ 1 := by rw [hx₂, hy₂]; intro he; linarith
  have hZ := doleansDensity_removeAll_g3_ae_eq hκ hδ hE₂ hB₂c hp₂ hxy₂ hR₂ hST hW₂p hVL₂p hS₂
  filter_upwards [hZ] with y hy
  have h := hp₂ y
  -- the gaps of the large marks up to `S₂`
  have hne : ∀ r ≤ S₂ m y, ∀ i, VL₂ i r y ≠ W₂ r y := fun r hr i he => by
    have := h.gap r hr i
    rw [he, sub_self, abs_zero] at this
    linarith [h.pos]
  -- the two force points never meet
  have hode := sub_eq_mul_exp_of_force h.path.2.2.2.1 (h.path.2.2.2.2.1 0) (h.path.2.2.2.2.1 1)
    (fun t ht => h.path.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t ht 0) (fun t ht => h.path.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t ht 1)
    h.lt (fun r hr => hne r hr 0) (fun r hr => hne r hr 1) (le_refl (S₂ m y))
  have hxy : VL₂ 0 (S₂ m y) y ≠ VL₂ 1 (S₂ m y) y := by
    intro he
    have h0 := hode
    simp only at h0
    rw [he, sub_self] at h0
    exact (mul_ne_zero (sub_ne_zero.2 hxy₂) (Real.exp_pos _).ne') h0.symm
  -- the new Brownian path drives the large curve up to the exit
  have hB : ∀ u ∈ Icc (0 : ℝ) (S₂ m y), drive κ (girsanovProcess B₂ (removeAllDrift κ δ ![κ - 4, -4] ρR₂
      (fun y => (S₂ m y : ℝ≥0∞)) ζ₂ W₂ VL₂ VR₂)) y u = Strip.extPath (W₂ · y) u := by
    intro u hu
    have hle : u.toNNReal ≤ S₂ m y := Real.toNNReal_le_iff_le_coe.2 hu.2
    exact drive_girsanov_removeAll_eq hκ hδ h.path h.lt.le
      (fun t ht i => h.gap t (ENNReal.coe_le_coe.1 ht.le) i) (fun t _ j => j.elim0)
      (ENNReal.coe_le_coe.2 hle) (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hle) h.lt)
  rw [seedHeightField_g3Rec_eq hκ hpp hP hxL hxR hxO hxOq hgood₁ hsep₁ hsepO (hc₂ y) (h0₂ y) (hgood₂ y)
    (hS₂pos y) h.path hx₂ hy₂ h.lt (fun r hr => hne r hr 0) (fun r hr => hne r hr 1) hxy hB hs (hown y) (hYT y),
    hy, mul_comm, ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- **The large direction's one-sample law under the G3 patch density.** If A1-LARGEDENS's one-sample law holds under
the tilted Girsanov measure `girsMeasure (girsanovMeasure P₂ 𝓕₂ B₂ θ (T₀ + 1)) (√κ) B⁰ (S₂ m) ℓ⁰` (e.g. by
`isSeedSampleLaw_largeG3_of_removeAll`), the frozen-curve density is a.e.-measurable, and the G3 row identity holds
(`seedHeightField_g3Rec_ae_eq_mul`), then the same law holds under
`P₂.withDensity (fun y => ofReal (seedHeightField (g3Rec …) (ω₁, y) s (S₂ m y)))` — the form `FrozenFamilyFst` asks
for. -/
theorem isSeedSampleLaw_g3Rec_of_girs {κ p : ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {ω₁ : X} {s : ℝ}
    {P₂ : Measure Y} [IsProbabilityMeasure P₂] {𝓕₂ : Filtration ℝ≥0 mY} {B₂ : ℝ≥0 → Y → ℝ} {θ : ℝ≥0 → Y → ℝ}
    {T₀ : ℝ≥0} {S₂ : ℕ → Y → ℝ≥0} {ℓ : Y → ℝ → ℝ → ℝ} {nL nR : ℕ} {Wi : ℝ≥0 → Y → ℝ} {ζi : Y → ℝ≥0∞}
    {VL : Fin nL → ℝ≥0 → Y → ℝ} {VR : Fin nR → ℝ≥0 → Y → ℝ} {N : ℝ≥0 → Y → ℝ} {Scap : ℕ → Y → ℝ≥0} {m' : ℕ}
    (hB₂ : IsFilteredBrownianReal 𝓕₂ B₂ P₂) (hθp : IsStronglyProgressive 𝓕₂ θ) {C : ℝ}
    (hθb : ∀ t y, |θ t y| ≤ C) (hθreg : IsRiemannRegular P₂ θ)
    (hlaw : IsSeedSampleLaw (girsMeasure (girsanovMeasure P₂ 𝓕₂ B₂ θ (T₀ + 1)) (Real.sqrt κ)
      (girsanovProcess B₂ θ) (S₂ m) ℓ) Wi ζi VL VR N Scap m')
    (hg : AEMeasurable (fun y => ENNReal.ofReal (girsDensity (Real.sqrt κ) (girsanovProcess B₂ θ) (S₂ m) ℓ y)) P₂)
    (hid : (fun y => ENNReal.ofReal (seedHeightField (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m) (ω₁, y) s (S₂ m y))) =ᵐ[P₂]
      fun y => ENNReal.ofReal (doleansDensity P₂ 𝓕₂ B₂ θ (T₀ + 1) y) *
        ENNReal.ofReal (girsDensity (Real.sqrt κ) (girsanovProcess B₂ θ) (S₂ m) ℓ y)) :
    IsSeedSampleLaw (P₂.withDensity fun y =>
        ENNReal.ofReal (seedHeightField (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m) (ω₁, y) s (S₂ m y)))
      Wi ζi VL VR N Scap m' := by
  have hpre := isFilteredPreBrownian_of_isFilteredBrownianReal hB₂
  have hZ : AEMeasurable (fun y => ENNReal.ofReal (doleansDensity P₂ 𝓕₂ B₂ θ (T₀ + 1) y)) P₂ :=
    ((stronglyMeasurable_doleansDensity (hB := hpre) hθp hθb hθreg (T₀ + 1)).measurable.mono (𝓕₂.le _) le_rfl
      |>.ennreal_ofReal).aemeasurable
  exact isSeedSampleLaw_withDensity_of_ae_eq_mul hlaw hZ hg hid

end InteractingSLE.ZhanGT4.A1G3Id
