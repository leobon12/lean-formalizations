/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndZeroLaw
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndMain

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: the family law from the record facts alone

Packet PROVE-A1-G3LAW2. The frozen time `σ = 0` for the original data with masked caps (**`g3Snd_hlaw_zero`**,
**`g3Snd_hgeo_zero`**), and **`hasFamilyLawC_g3_of_stop`**: `G3RectLawSndC`'s conclusion for regular marginals with
patches from the single named input `hstop` (the per-stop record facts `ResStopInput` for the corrected forces and the
masked caps).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1G3Law A1LargeDens A1SeedGeom

section Zero

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
  {W₁o : ℝ≥0 → X → ℝ} {ζ₁o : X → ℝ≥0∞} {W₂o : ℝ≥0 → Y → ℝ} {VL₂o : Fin 2 → ℝ≥0 → Y → ℝ} {ζ₂o : Y → ℝ≥0∞}
  {G₁ : Set X} {G₂ : Set Y}

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
  (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁o t x' = W₁ t x') ∧ ζ₁o x' = ζ₁ x')
  (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂o t y' = W₂ t y') ∧ (∀ i t, VL₂o i t y' = VL₂ i t y') ∧ ζ₂o y' = ζ₂ y')

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hag₁ hag₂

/-- **The small direction's one-sample law at the frozen time `0`, masked caps** (original canonical data). -/
theorem g3Snd_hlaw_zero [𝓖₁.IsRightContinuous] (hG₁ : MeasurableSet G₁) (hG₁0 : P₁ G₁ᶜ = 0) (k : ℕ) {y' : Y}
    (hy' : y' ∈ G₂) :
    IsSeedSampleLaw (P₁.withDensity fun x' => g3SndD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ 0 k (x', y'))
      (fun t x' => rDrv (g3SndLive W₂o VL₂o ζ₂o) y W₁o ζ₁o 0 W₂o (fun _ => 0) t (x', y'))
      (fun x' => rLife (g3SndLive W₂o VL₂o ζ₂o) y W₁o ζ₁o 0 W₂o (fun _ => 0) (x', y'))
      (fun i t x' => g3SndVL y W₁o ζ₁o W₂o VL₂o ζ₂o 0 i t (x', y'))
      (fun j t x' => g3SndVRc y W₁o ζ₁o W₂o VL₂o ζ₂o 0 j t (x', y'))
      (fun t x' => seedCapacityNoise (kh κ) (smallG3RhoL κ) (smallG3RhoR κ)
        (fun s => rDrv (g3SndLive W₂o VL₂o ζ₂o) y W₁o ζ₁o 0 W₂o (fun _ => 0) s (x', y'))
        (fun i s => g3SndVL y W₁o ζ₁o W₂o VL₂o ζ₂o 0 i s (x', y'))
        (fun j s => g3SndVRc y W₁o ζ₁o W₂o VL₂o ζ₂o 0 j s (x', y')) t)
      (fun k' x' => maskCap G₁ G₂ (g3SndCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) 0 k' (x', y')) k := by
  have hE0 : (P₁.withDensity fun x' => g3SndD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ 0 k (x', y')) G₁ᶜ = 0 :=
    withDensity_absolutelyContinuous _ _ hG₁0
  obtain ⟨hW₂a, hV₂a, hζ₂a⟩ := hag₂ y' hy'
  have hlaw := g3Snd_isSeedSampleLaw_zero hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y'
  have hcg := fun x' (hx : x' ∉ G₁ᶜ) =>
    g3Snd_data_congr (x := x) (y := y) (W₁g := W₁) (ζ₁g := ζ₁) (W₂g := W₂) (ζ₂g := ζ₂)
      (hag₁ x' (not_not.1 hx)).1 (hag₁ x' (not_not.1 hx)).2 hW₂a hV₂a hζ₂a 0
  refine IsSeedSampleLaw.congr_off hlaw hG₁.compl hE0
    (fun x' hx => maskCap_of_not_mem (z := (x', y')) fun h => hx h.1)
    (fun x' hx t => (hcg x' hx).1 t) (fun x' hx => (hcg x' hx).2.1) (fun x' hx i t => (hcg x' hx).2.2.1 i t)
    (fun x' hx j t => (hcg x' hx).2.2.2.1 j t) (fun x' hx t => ?_)
    (fun x' hx k' => (maskCap_of_mem (z := (x', y')) (not_not.1 hx) hy').trans ((hcg x' hx).2.2.2.2 k'))
  have e1 : (fun s => rDrv (g3SndLive W₂o VL₂o ζ₂o) y W₁o ζ₁o 0 W₂o (fun _ => 0) s (x', y')) =
      fun s => rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => 0) s (x', y') := funext fun s => (hcg x' hx).1 s
  have e2 : (fun i s => g3SndVL y W₁o ζ₁o W₂o VL₂o ζ₂o 0 i s (x', y')) =
      fun i s => g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ 0 i s (x', y') :=
    funext fun i => funext fun s => (hcg x' hx).2.2.1 i s
  have e3 : (fun j s => g3SndVRc y W₁o ζ₁o W₂o VL₂o ζ₂o 0 j s (x', y')) =
      fun j s => g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ 0 j s (x', y') :=
    funext fun j => funext fun s => (hcg x' hx).2.2.2.1 j s
  simp only [e1, e2, e3]

/-- **The geometry of the canonical data stopped at a positive raw cap at the frozen time `0`** (good samples). -/
theorem g3Snd_hgeo_zero (k : ℕ) {z : X × Y} (hz1 : z.1 ∈ G₁) (hz2 : z.2 ∈ G₂)
    (hpos : 0 < g3SndCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ 0 k z) :
    SeedImageGeometry (![0] : Fin 1 → ℝ) (g3SndWordR W₂o VL₂o 0 z.2) (smallG3RhoL κ) (smallG3RhoR κ)
      (fun t => rDrv (g3SndLive W₂o VL₂o ζ₂o) y W₁o ζ₁o 0 W₂o (fun _ => 0)
        (min t (g3SndCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ 0 k z)) z)
      (fun i t => g3SndVL y W₁o ζ₁o W₂o VL₂o ζ₂o 0 i (min t (g3SndCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ 0 k z)) z)
      (fun j t => g3SndVRc y W₁o ζ₁o W₂o VL₂o ζ₂o 0 j (min t (g3SndCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ 0 k z)) z)
      (g3SndCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ 0 k z) := by
  rcases z with ⟨x₀, y₀⟩
  obtain ⟨hW₂a, hV₂a, hζ₂a⟩ := hag₂ y₀ hz2
  have hcg := g3Snd_data_congr (x := x) (y := y) (W₁g := W₁) (ζ₁g := ζ₁) (W₂g := W₂) (ζ₂g := ζ₂)
    (hag₁ x₀ hz1).1 (hag₁ x₀ hz1).2 hW₂a hV₂a hζ₂a 0
  have hcap : g3SndCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ 0 k (x₀, y₀) = g3S₁ x y W₁ ζ₁ k x₀ :=
    (hcg.2.2.2.2 k).trans (g3Snd0_cap hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀)
  have hword : g3SndWordR W₂o VL₂o 0 y₀ = (![0, x - y, -y] : Fin 3 → ℝ) := by
    obtain ⟨hW0₂, hL0₂, -⟩ := h₂.path y₀
    have h0 : VL₂ 0 0 y₀ = x := hL0₂ 0
    have h1 : VL₂ 1 0 y₀ = y := hL0₂ 1
    have hw : W₂ 0 y₀ = 0 := hW0₂
    funext j
    fin_cases j <;> simp [g3SndWordR, hW₂a, hV₂a, h0, h1, hw]
  rw [hcap, hword]
  have hG := g3Small_geometry hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  refine hG.stop_of_eqOn
    (w' := fun t => rDrv (g3SndLive W₂o VL₂o ζ₂o) y W₁o ζ₁o 0 W₂o (fun _ => 0) t (x₀, y₀))
    (vL' := fun i t => g3SndVL y W₁o ζ₁o W₂o VL₂o ζ₂o 0 i t (x₀, y₀))
    (vR' := fun j t => g3SndVRc y W₁o ζ₁o W₂o VL₂o ζ₂o 0 j t (x₀, y₀)) (fun t ht => ?_) (fun i t ht => ?_)
    (fun j t ht => ?_)
  · rw [hcg.1 t, g3Snd0_rDrv hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀ ht, min_eq_left ht]
  · rw [hcg.2.2.1 i t, g3Snd0_VL hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀ i ht, min_eq_left ht]
  · rw [hcg.2.2.2.1 j t, g3Snd0_VR hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀ j ht, min_eq_left ht]

end Zero

/-- **`G3RectLawSndC`'s conclusion from the record facts alone** (the frozen time `0` and every positive frozen time
proved): binders of `hasFamilyLawC_g3_of_zero_stop` without `hgeo0`, `hlaw0`. -/
theorem hasFamilyLawC_g3_of_stop {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
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
    (hstop : ∀ (τ : Y → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun y' => (τ y' : WithTop ℝ≥0)),
      Nonempty (ResStopInput P₁ P₂ μ (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂)
        (g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂) (maskCap G₁ G₂ (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂'))
        (g3SndD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂') τ {B | MeasurableSet[hτ.measurableSpace] B})) :
    HasFamilyLawC (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
      W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
      (smallG3RhoR κ) :=
  hasFamilyLawC_g3_of_zero_stop hκ4 hκ8 hyx hx h₂ h₁ h₂' hB₂' h₁' hB₁' hg₁' hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂
    (fun k _ hz1 hz2 hpos => g3Snd_hgeo_zero hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hag₁ hag₂ k hz1 hz2 hpos)
    (fun k => Eventually.of_forall fun _ hy' =>
      g3Snd_hlaw_zero hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hag₁ hag₂ hG₁ hG₁0 k hy')
    hstop

end InteractingSLE.ZhanGT4.A1G3L2
