/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LgGood
import InteractingSLE.Spec.ZhanGT4.A1G3LgD9
import InteractingSLE.Spec.ZhanGT4.A1G3LawFstRect
import InteractingSLE.Spec.ZhanGT4.A1G3LawCol
import InteractingSLE.Spec.ZhanGT4.A1ELawSample

/-!
# G3 large direction: the law under the rectangle density

The two original force points are removed by the landed Girsanov theorem.
The G3 row identity then identifies the resulting frozen-curve law with the
rectangle tilt. No determination or trace-existence theorem is used.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Lg

open QuantumZipper (fwdHull fwdMap drive IsForwardSol)
open A2X A1Ref A1Marg A1SeedField A1EightSeed A1EightFin A1G3Calc A1Common A1Asm
  A1G3Law A1ELaw A1G3RR A1G3Id Girsanov A1G3Row A1LargeDens A1MultiMark A1Family

/-- A positive finite measurable factor can be divided out of a measurable density. -/
theorem aemeasurable_of_ae_eq_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D Z g : Ω → ℝ≥0∞} (hD : AEMeasurable D P) (hZ : AEMeasurable Z P)
    (hZ0 : ∀ ω, Z ω ≠ 0) (hZtop : ∀ ω, Z ω ≠ ⊤)
    (h : D =ᵐ[P] fun ω => Z ω * g ω) : AEMeasurable g P := by
  have he : (fun ω => D ω / Z ω) =ᵐ[P] g := h.mono fun ω hω => by
    change D ω / Z ω = g ω
    change D ω = Z ω * g ω at hω
    rw [hω, mul_comm, ENNReal.mul_div_cancel_right (hZ0 ω) (hZtop ω)]
  exact (hD.div hZ).congr he

variable {X Y : Type} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y}
  {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
  {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ}
  {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable [StandardBorelSpace X] [StandardBorelSpace Y]
  [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
  [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous]

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y]
    (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω)
    (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂)
  (hB₂ : ∀ ω, Continuous (B₂ · ω))

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂

/-- The large image law under the G3 rectangle tilt, in seeded capacity coordinates. -/
theorem g3Fst_isSeedSampleLaw (k : ℕ) (x₀ : X) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ g3S₁ x y W₁ ζ₁ k x₀) {a W' : Y → ℝ → ℝ}
    (hown₁ : ∀ y₀, OwnData (eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀)
      (fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
      (frzChart (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
      (g3S₂ x y W₂ ζ₂ k y₀) (a y₀) (W' y₀))
    {n' : ℕ} {d : Y → SeedData n'} {A' : Y → Set ℂ}
    (hown : ∀ y₀, OwnData (d y₀).W (A' y₀) (d y₀).φ
      (g3S₂ x y W₂ ζ₂ k y₀) (d y₀).a (d y₀).W')
    (hda : ∀ y₀, (d y₀).a = a y₀) (hdW' : ∀ y₀, (d y₀).W' = W' y₀)
    {Wi N : ℝ≥0 → Y → ℝ} {ζi : Y → ℝ≥0∞}
    {VL : Fin 4 → ℝ≥0 → Y → ℝ} {VR : Fin 0 → ℝ≥0 → Y → ℝ}
    {Scap : ℕ → Y → ℝ≥0} {m : ℕ}
    (hSm : ∀ y₀, Scap m y₀ = seedCapacityHorizon d (g3S₂ x y W₂ ζ₂ k) y₀)
    (hW : ∀ y₀ t, t ≤ Scap m y₀ → Wi t y₀ = seedCapacityDriver d (g3S₂ x y W₂ ζ₂ k) t y₀)
    (hVL : ∀ y₀ i t, t ≤ Scap m y₀ → VL i t y₀ = capForce d (g3S₂ x y W₂ ζ₂ k)
      (fun y₀ => frzImg (d y₀).W' (d y₀).a
        (![VR₁ 1 σ x₀ - -y, VR₁ 0 σ x₀ - -y,
          eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ σ - -y, VL₁ 0 σ x₀ - -y] i)) t y₀)
    (hN : ∀ y₀ t, t ≤ Scap m y₀ → N t y₀ = seedCapacityNoise κ (largeG3ImgRhoL κ) ![]
      (Wi · y₀) (fun i t => VL i t y₀) (fun j t => VR j t y₀) t)
    (hζ : ∀ y₀, (Scap m y₀ : ℝ≥0∞) ≤ ζi y₀)
    (Tk : ℕ → Y → ℝ≥0) (hTk : ∀ m', IsStoppingTime 𝓖₂ fun y₀ => (Tk m' y₀ : WithTop ℝ≥0))
    (hcap₁ : ∀ m' y₀, Tk m' y₀ ≤ g3S₂ x y W₂ ζ₂ k y₀ →
      (Scap m' y₀ : ℝ) = (d y₀).a (Tk m' y₀))
    (hcap₂ : ∀ m' y₀, g3S₂ x y W₂ ζ₂ k y₀ ≤ Tk m' y₀ → Scap m y₀ ≤ Scap m' y₀) :
    IsSeedSampleLaw (P₂.withDensity fun y₀ => g3FstD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀))
      Wi ζi VL VR N Scap m := by
  have hκ : 0 < κ := by linarith
  have hqlo : 0 < x - y := sub_pos.2 hyx
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun i => by fin_cases i; simp; linarith)
      (fun i => by fin_cases i; simp; linarith)
  have hF := isEnclFamily_cofG hne
  have hpp := isProtectedPairG_cofG hne k
  obtain ⟨hU, hgood₁, hsep₁, hsepO, -, hc₂, h0₂, hgood₂, hpos₂, hlt₂⟩ :=
    g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  obtain ⟨U, -, hSU⟩ := hU k
  have hS : IsStoppingTime 𝓖₂ fun y₀ => (g3S₂ x y W₂ ζ₂ k y₀ : WithTop ℝ≥0) :=
    isStoppingTime_rect₂ (fun y₀ => (h₂.path y₀).2.2.2.1) h₂.evol.2.1
      (fun m => (hF.pp m).hull₂) (cofGN (-y) (x - y) ![x - y]) (-y) k
  obtain ⟨-, -, -, -, -, hKs, -⟩ :=
    g3Fst_frame hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ (NNReal.coe_le_coe.2 hσS)
  obtain ⟨δ, R, hδ, hpR⟩ := g3Fst_gaps hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀
  have hp := fun y₀ => (hpR y₀).1
  have hτ : ∀ r : ℝ≥0, MeasurableSet[𝓖₂ r]
      {y₀ | (g3S₂ x y W₂ ζ₂ k y₀ : ℝ≥0∞) ≤ r} := fun r => by
    convert hS.measurableSet_le r using 2 with y₀
    simp only [ENNReal.coe_le_coe, WithTop.coe_le_coe]
  have hgap : ∀ y₀ (r : ℝ≥0), (r : ℝ≥0∞) < (g3S₂ x y W₂ ζ₂ k y₀ : ℝ≥0∞) →
      ∀ i, δ ≤ |W₂ r y₀ - VL₂ i r y₀| :=
    fun y₀ r hr i => (hp y₀).gap r (ENNReal.coe_le_coe.1 hr.le) i
  let θ := removeAllDrift κ δ ![κ - 4, -4] ![]
    (fun y₀ => (g3S₂ x y W₂ ζ₂ k y₀ : ℝ≥0∞)) ζ₂ W₂ VL₂ VR₂
  let B0 := girsanovProcess B₂ θ
  obtain ⟨-, hB0, hB0c, -⟩ := girsanov_removeAll_pathwise hκ h₂.evol h₂.path hB₂ hτ
    (fun y₀ => (hlt₂ k y₀).le) (fun y₀ => ENNReal.coe_le_coe.2 (hSU y₀)) hδ hgap
    (fun _ _ _ j => j.elim0)
  have hdc : ∀ y₀, Continuous (drive κ B0 y₀) := fun y₀ =>
    continuous_const.mul ((hB0c y₀).comp continuous_real_toNNReal)
  have hdrive : ∀ y₀, EqOn (drive κ B0 y₀) (Strip.extPath (W₂ · y₀))
      (Icc 0 (g3S₂ x y W₂ ζ₂ k y₀ : ℝ)) := by
    intro y₀ u hu
    have huS := Real.toNNReal_le_iff_le_coe.2 hu.2
    exact drive_girsanov_removeAll_eq hκ hδ (h₂.path y₀) (hlt₂ k y₀).le
      (hgap y₀) (fun _ _ j => j.elim0) (ENNReal.coe_le_coe.2 huS)
      (lt_of_le_of_lt (ENNReal.coe_le_coe.2 huS) (hlt₂ k y₀))
  have hown0 : ∀ y₀, OwnData (drive κ B0 y₀)
      (fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
      (frzChart (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
      (g3S₂ x y W₂ ζ₂ k y₀) (a y₀) (W' y₀) := fun y₀ =>
    ownData_congr_drv (hown₁ y₀) (hdc y₀)
      (fun u hu => (eightDrv_eqOn W₂ (g3S₂ x y W₂ ζ₂) k y₀ hu).trans ((hdrive y₀ hu).symm))
  have hK0 : ∀ y₀, fwdHull (drive κ B0 y₀) (g3S₂ x y W₂ ζ₂ k y₀) ⊆
      transl (-(-y)) (cofGH₂ (-y) (x - y) ![x - y] k) := by
    intro y₀
    rw [← YuanCorollary13.fwdHull_eq_of_eqOn_Icc (hown₁ y₀).cont (hdc y₀)
      (NNReal.coe_nonneg _) (fun u hu =>
        (eightDrv_eqOn W₂ (g3S₂ x y W₂ ζ₂) k y₀ hu).trans ((hdrive y₀ hu).symm))]
    exact hKs y₀
  obtain ⟨r, a₀, γ, Γ, lam, L, hH⟩ :=
    g3Fst_d10Hyp hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown0 hdrive
  obtain ⟨NB, hNB⟩ := exists_abs_B_le hH hκ hB0c (hF.hull₂ k) hK0
  have hlaw := isSeedSampleLaw_largeG3_of_frzD10Hyp hH hκ hB0 hB0c hS hNB
    hown hda hdW' hSm hW hVL hN hζ Tk hTk hcap₁ hcap₂
  have hs : (σ : ℝ) ∈ Ioc (0 : ℝ) (g3S₁ x y W₁ ζ₁ k x₀) :=
    ⟨by exact_mod_cast hσ, NNReal.coe_le_coe.2 hσS⟩
  have hid := seedHeightField_g3Rec_ae_eq_mul hκ hδ hpp (h₁.path x₀) rfl rfl
    (by simpa using hqlo) (by simpa using qlo_le_cofGq hne k) (hgood₁ k x₀)
    (hsep₁ x₀) (hsepO x₀) h₂.evol hB₂ hp (fun y₀ => (hpR y₀).2) hSU h₂.progW h₂.progVL
    hS (by simp) (by simp) (hc₂ k) h0₂ (hgood₂ k) (hpos₂ k) hs hown0 (fun _ => le_rfl)
  simp only [Strip.extPath, Real.toNNReal_coe] at hid
  have hUad : ∀ j, AdaptedBefore 𝓖₂ ζ₂ (allMarks VL₂ VR₂ j) := fun j => by
    cases j using Fin.addCases with
    | left i =>
      rw [show allMarks VL₂ VR₂ (Fin.castAdd 0 i) = VL₂ i from
        Fin.addCases_left (motive := fun _ => ℝ≥0 → Y → ℝ) i]
      exact h₂.evol.2.2.1 i
    | right i => exact i.elim0
  have hθp : IsStronglyProgressive 𝓖₂ θ :=
    isStronglyProgressive_cutDrift (continuous_shiftIntegrand_removeAll hδ) h₂.evol.2.1 hUad hτ
  have hθb := abs_cutDrift_le (τ := fun y₀ => (g3S₂ x y W₂ ζ₂ k y₀ : ℝ≥0∞))
    (ζ := ζ₂) (W := W₂) (U := allMarks VL₂ VR₂)
    (abs_shiftIntegrand_removeAll_le (κ := κ) (ρL := ![κ - 4, -4]) (ρR := (![] : Fin 0 → ℝ)) hδ)
  have hθreg : IsRiemannRegular P₂ θ := by
    refine isRiemannRegular_cutDrift (P := P₂)
      (τ := fun y₀ => (g3S₂ x y W₂ ζ₂ k y₀ : ℝ≥0∞)) (ζ := ζ₂)
      (W := W₂) (U := allMarks VL₂ VR₂) (continuous_shiftIntegrand_removeAll
        (κ := κ) (ρL := ![κ - 4, -4]) (ρR := (![] : Fin 0 → ℝ)) hδ)
      (fun y₀ => (hlt₂ k y₀).le) (Eventually.of_forall fun y₀ => ⟨(h₂.path y₀).2.2.2.1, fun j => ?_⟩)
    cases j using Fin.addCases with
    | left i =>
      rw [show allMarks VL₂ VR₂ (Fin.castAdd 0 i) = VL₂ i from
        Fin.addCases_left (motive := fun _ => ℝ≥0 → Y → ℝ) i]
      exact (h₂.path y₀).2.2.2.2.1 i
    | right i => exact i.elim0
  have hZ : AEMeasurable (fun y₀ => ENNReal.ofReal (doleansDensity P₂ 𝓖₂ B₂ θ (U + 1) y₀)) P₂ :=
    ((stronglyMeasurable_doleansDensity
    (hB := isFilteredPreBrownian_of_isFilteredBrownianReal h₂.evol.1) hθp hθb hθreg (U + 1)).measurable.mono
      (𝓖₂.le _) le_rfl |>.ennreal_ofReal).aemeasurable
  let Dfam : ℝ≥0 × (X × Y) → ℝ≥0∞ := fun p =>
    g3FstD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ p.1 k p.2
  have hDj : Measurable Dfam := measurable_g3FstD hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k
  have hπ : Measurable (fun y₀ : Y => (σ, (x₀, y₀))) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hD : Measurable (Dfam ∘ fun y₀ : Y => (σ, (x₀, y₀))) :=
    hDj.comp hπ
  change Measurable (fun y₀ => g3FstD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀)) at hD
  have hidD := hid
  simp only [g3FstD, min_eq_left hσS] at hD ⊢
  have hg : AEMeasurable (fun y₀ => ENNReal.ofReal (girsDensity (Real.sqrt κ) B0
      (g3S₂ x y W₂ ζ₂ k) (fun y₀ => (frzDataOf κ B0 W' a
        (frzChart (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
        (largeG3RR κ) (eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ σ - -y)
        ![VR₁ 1 σ x₀ - -y, VR₁ 0 σ x₀ - -y, VL₁ 0 σ x₀ - -y] y₀).ell) y₀)) P₂ := by
    exact aemeasurable_of_ae_eq_mul hD.aemeasurable hZ
      (fun y₀ => (ENNReal.ofReal_pos.2 (doleansDensity_pos
        (P := P₂) (𝓕 := 𝓖₂) (B := B₂) (θ := θ) (U + 1) y₀)).ne')
      (fun _ => ENNReal.ofReal_ne_top) hidD
  exact isSeedSampleLaw_g3Rec_of_girs h₂.evol.1 hθp hθb hθreg hlaw hg hid

end InteractingSLE.ZhanGT4.A1G3Lg

