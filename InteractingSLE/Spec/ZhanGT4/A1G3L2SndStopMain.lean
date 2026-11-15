/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndStopCov
import InteractingSLE.Spec.ZhanGT4.A1RLawStmt

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: `G3RectLawSndC`

Packet PROVE-A1-G3LAW2.

* **`g3Stop_hcov`**: the record fact `hcov` of `ResStopInput` (a.e. on the good pairs, `g3_cover`);
* **`hasFamilyLawC_g3_sndC`**: `G3RectLawSndC`'s conclusion for regular marginals with patches — the per-stop input
  `hstop` of `hasFamilyLawC_g3_of_stop` is PROVED (PROVE-A1-G3LAW's `g3SndResStop` with the record facts of
  `A1G3L2SndStopFacts`, `A1G3L2SndStopDrv`, G3LAW's `g3Snd_hgζ` and `g3Stop_hcov`);
* **`g3RectLawSndC_holds`**: **`G3RectLawSndC κ`** for every `κ`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1G3Law A1LargeDens A1SeedGeom

section Cov

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
  {W₁o : ℝ≥0 → X → ℝ} {ζ₁o : X → ℝ≥0∞} {W₂o : ℝ≥0 → Y → ℝ} {VL₂o : Fin 2 → ℝ≥0 → Y → ℝ} {ζ₂o : Y → ℝ≥0∞}
  {G₁ : Set X} {G₂ : Set Y}

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ (usualAugmentation 𝓕₁ P₁)
    W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ (usualAugmentation 𝓕₂ P₂) W₂ VL₂ VR₂ B₂ ζ₂)
  (hB₂ : ∀ ω, Continuous (B₂ · ω))
  (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₁0 : P₁ G₁ᶜ = 0) (hG₂0 : P₂ G₂ᶜ = 0)
  (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁o t x' = W₁ t x') ∧ ζ₁o x' = ζ₁ x')
  (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂o t y' = W₂ t y') ∧ (∀ i t, VL₂o i t y' = VL₂ i t y') ∧ ζ₂o y' = ζ₂ y')

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂

/-- **`hcov`**: the masked caps exhaust the canonical clock before contact, a.e. under a coupling of the marginals. -/
theorem g3Stop_hcov (τ : Y → ℝ≥0) {μ : Measure (X × Y)} (hμ₁ : μ.map Prod.fst = P₁)
    (hμ₂ : μ.map Prod.snd = P₂) :
    ∀ᵐ z ∂μ, g3SndLive W₂o VL₂o ζ₂o (τ z.2) z.2 → ∀ s : ℝ≥0, (s : ℝ≥0∞) < A2X.contactTime y
        (Strip.extPath (W₁o · z.1)) (ζ₁o z.1) 0 (Strip.extPath (W₂o · z.2)) (τ z.2) →
      ∃ m, A1Ref.imgClk y (Strip.extPath (W₁o · z.1)) 0 (Strip.extPath (W₂o · z.2)) (τ z.2) s ≤
        maskCap G₁ G₂ (g3SndCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) (τ z.2) m z := by
  have hae₁ : ∀ᵐ z ∂μ, z.1 ∈ G₁ := by
    rw [ae_iff]
    have h : μ (Prod.fst ⁻¹' G₁ᶜ) = 0 := by
      rw [← Measure.map_apply measurable_fst hG₁.compl, hμ₁]
      exact hG₁0
    exact h
  have hae₂ : ∀ᵐ z ∂μ, z.2 ∈ G₂ := by
    rw [ae_iff]
    have h : μ (Prod.snd ⁻¹' G₂ᶜ) = 0 := by
      rw [← Measure.map_apply measurable_snd hG₂.compl, hμ₂]
      exact hG₂0
    exact h
  filter_upwards [hae₁, hae₂] with z h1 h2 hlo s hs
  obtain ⟨hW₁a, hζ₁a⟩ := hag₁ z.1 h1
  obtain ⟨hW₂a, hV₂a, hζ₂a⟩ := hag₂ z.2 h2
  have eW₁ : (W₁o · z.1) = (W₁ · z.1) := funext hW₁a
  have eW₂ : (W₂o · z.2) = (W₂ · z.2) := funext hW₂a
  have eV₂ : (VL₂o 0 · z.2) = (VL₂ 0 · z.2) := funext (hV₂a 0)
  have hl : g3SndLive W₂ VL₂ ζ₂ (τ z.2) z.2 := by
    have h := hlo
    simp only [g3SndLive, eW₂, eV₂, hζ₂a] at h
    exact h
  rw [eW₁, hζ₁a, eW₂] at hs
  rw [eW₁, eW₂]
  have hj : ∀ T : ℝ, ENNReal.ofReal T < ζ₁ z.1 → ContinuousOn (Strip.extPath (W₁ · z.1)) (Icc 0 T) :=
    fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path z.1).2.2.2.1 hT
  have hk : ∃ τ' : ℝ, ((τ z.2 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₂ · z.2)) (Icc 0 τ') :=
    A1Ref.exists_continuousOn_extPath_beyond (h₂.path z.2).2.2.2.1 hl.1
  obtain ⟨m, hm⟩ := cover_capSnd (z := z) (τ := fun _ => τ z.2) (live := g3SndLive W₂ VL₂ ζ₂) (xj := y)
    (Wj := W₁) (ζj := ζ₁) (xk := 0) (Wk := W₂) (Tm := fun m => g3SndOwn x y W₁ ζ₁ W₂ ζ₂ (τ z.2) m) hl hj
    (h₁.path z.1).1 hk (h₂.path z.2).1 (fun s' hs' => g3_cover hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ z.2 z.1 hl s' hs')
    (fun m => g3Stop_fin hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ m hl) s hs
  refine ⟨m, hm.trans_eq ?_⟩
  rw [g3Stop_mask_eq hag₁ hag₂ m h1 h2]
  rfl

end Cov

/-- **`G3RectLawSndC`'s conclusion for regular marginals with patches** (the binders of `hasFamilyLawC_g3_of_stop`
without `hstop`, with the patched exits as stopping times and (1.7) on the exit records). -/
theorem hasFamilyLawC_g3_sndC {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
    {X Y : Type} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] [StandardBorelSpace X] [StandardBorelSpace Y]
    {P₁ : Measure X} {P₂ : Measure Y} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {μ : Measure (X × Y)}
    [IsProbabilityMeasure μ] {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
    {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ}
    {ζ₂ : Y → ℝ≥0∞} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ}
    {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {W₂' : ℝ≥0 → Y → ℝ} {VL₂' : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂' : Fin 0 → ℝ≥0 → Y → ℝ} {B₂' : ℝ≥0 → Y → ℝ}
    {ζ₂' : Y → ℝ≥0∞} {W₁' : ℝ≥0 → X → ℝ} {VL₁' : Fin 1 → ℝ≥0 → X → ℝ} {VR₁' : Fin 3 → ℝ≥0 → X → ℝ}
    {B₁' : ℝ≥0 → X → ℝ} {ζ₁' : X → ℝ≥0∞}
    (h₂' : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ (usualAugmentation 𝓕₂ P₂) W₂' VL₂' VR₂' B₂' ζ₂')
    (hB₂' : ∀ ω, Continuous (B₂' · ω))
    (h₁' : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ (usualAugmentation 𝓕₁ P₁)
      W₁' VL₁' VR₁' B₁' ζ₁')
    (hB₁' : ∀ ω, Continuous (B₁' · ω))
    (hg₁' : ∀ ω, GoodSmallG3 (W₁' · ω) (fun i t => VL₁' i t ω) (fun i t => VR₁' i t ω) (B₁' · ω) (ζ₁' ω))
    {G₁ : Set X} {G₂ : Set Y} (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₁0 : P₁ G₁ᶜ = 0)
    (hG₂0 : P₂ G₂ᶜ = 0)
    (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁ t x' = W₁' t x') ∧ ζ₁ x' = ζ₁' x')
    (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂ t y' = W₂' t y') ∧ (∀ i t, VL₂ i t y' = VL₂' i t y') ∧ ζ₂ y' = ζ₂' y')
    (hs₁ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun ω => (g3S₁ x y W₁' ζ₁' m ω : WithTop ℝ≥0))
    (hs₂ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun ω => (g3S₂ x y W₂' ζ₂' m ω : WithTop ℝ≥0))
    (hμ₁ : μ.map Prod.fst = P₁) (hμ₂ : μ.map Prod.snd = P₂)
    (hd : ∀ m, RectDens (hs₁ m).measurableSpace (hs₂ m).measurableSpace P₁ P₂ μ fun ω =>
      ENNReal.ofReal (seedHeightField (g3Rec κ (-y) W₁' VL₁' VR₁' W₂' (g3S₁ x y W₁' ζ₁') m) ω
        (g3S₁ x y W₁' ζ₁' m ω.1) (g3S₂ x y W₂' ζ₂' m ω.2))) :
    HasFamilyLawC (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
      W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
      (smallG3RhoR κ) := by
  refine hasFamilyLawC_g3_of_stop hκ4 hκ8 hyx hx h₂ h₁ h₂' hB₂' h₁' hB₁' hg₁' hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂
    fun τ hτ => ⟨g3SndResStop hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hd hτ
      (g3Stop_hSm hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂)
      (g3Stop_hstop hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂)
      (g3Stop_hgW hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hτ hag₁ hag₂)
      (g3Stop_hgVL hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hτ hag₁ hag₂)
      (g3Stop_hgVR hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hτ hag₁ hag₂)
      (g3Stop_hgS hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂)
      (fun m z => g3Snd_hgζ x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' G₁ G₂ τ m z)
      (g3Stop_hcov hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂ τ hμ₁ hμ₂)⟩

/-- **`G3RectLawSndC κ` holds** (Zhan's A.1 under R83, (G3), the small-curve direction). -/
theorem g3RectLawSndC_holds (κ : ℝ) : G3RectLawSndC κ := by
  intro hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
    W₂' VL₂' VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd
  obtain ⟨G₂, hG₂, hG₂0, h₂', hB₂', -, hag₂⟩ := hp₂
  obtain ⟨G₁, hG₁, hG₁0, h₁', hB₁', hg₁', hag₁⟩ := hp₁
  exact hasFamilyLawC_g3_sndC hκ4 hκ8 hyx hx h₂ h₁ h₂' hB₂' h₁' hB₁' hg₁' hG₁ hG₂ hG₁0 hG₂0
    (fun x' hx' => ⟨fun t => ((hag₁ x' hx').1 t).symm, (hag₁ x' hx').2.2.2.2.symm⟩)
    (fun y' hy' => ⟨fun t => ((hag₂ y' hy').1 t).symm, fun i t => ((hag₂ y' hy').2.1 i t).symm,
      (hag₂ y' hy').2.2.2.2.symm⟩) hs₁ hs₂ hμ₁ hμ₂ hd

end InteractingSLE.ZhanGT4.A1G3L2
