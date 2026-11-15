/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndId

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: the protected live one-sample law in canonical coordinates

Packet PROVE-A1-G3LAW2. For the patched G3 marginals, at a frozen sample `y₀` live at a protected frozen time
`σ ∈ (0, S₂ᵏ(y₀)]`, given

* `hgeoS`: the seeded capacity coordinates of the column `g3Col … k σ y₀` form a `SeedImageGeometry` with the initial
  image word `(![0], g3SndWordR …)` (the small image word), and
* `hstart`: the column's image start in the physical frame is the image `V_y(σ)` of the small source (`W'(0) + y`),

the canonical family data (`rDrv`, `g3SndVL`, the corrected `g3SndVRc`, the raw caps `g3SndCap`) are the seeded
capacity coordinates up to the cap (**`g3Snd_VL_eq`**, **`g3Snd_VR_eq`**), and the one-sample law holds for them
(**`g3Snd_isSeedSampleLaw_live`**, from PROVE-A1-G3LAW's `g3_isSeedSampleLaw`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull fwdMap IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1G3Law A1LargeDens A1SeedGeom

section Law

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂

/-- **The canonical left seed force is the seeded capacity coordinate** up to the cap. -/
theorem g3Snd_VL_eq [IsProbabilityMeasure P₁] (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ g3S₂ x y W₂ ζ₂ k y₀) (hlive : g3SndLive W₂ VL₂ ζ₂ σ y₀) (x₀ : X)
    (hgeoS : SeedImageGeometry (![0] : Fin 1 → ℝ) (g3SndWordR W₂ VL₂ σ y₀) (smallG3RhoL κ) (smallG3RhoR κ)
      (seedCapacityDriver (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k) · x₀)
      (fun i u => seedCapacityForce (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k)
        (g3ChargeEquiv (.inl i)) u x₀)
      (fun j u => seedCapacityForce (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k)
        (g3ChargeEquiv (.inr j)) u x₀)
      (seedCapacityHorizon (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k) x₀))
    (i : Fin 1) {t : ℝ≥0}
    (ht : t ≤ seedCapacityHorizon (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k) x₀) :
    g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y₀) =
      seedCapacityForce (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k) (g3ChargeEquiv (.inl i)) t x₀ := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  by_cases ht0 : t = 0
  · subst ht0
    rw [g3SndVL_zero]
    exact (hgeoS.left_zero 0).symm
  obtain ⟨hown, hWj, hgood, hk⟩ := g3Col_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS x₀
  obtain ⟨hpp, hrec, hcol⟩ := g3_isSourceColumnG hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ (σ := (σ : ℝ))
    (by exact_mod_cast hσ) (by exact_mod_cast hσS)
  obtain ⟨hCc, hCs, c, hc, hClb⟩ := clock_facts_of_column hpp hcol
  rw [g3SndVL_of_ne y W₁ ζ₁ W₂ VL₂ ζ₂ σ 0 ht0]
  exact canonSeed_eq_of_geometry_left (L := {z : X × Y | g3SndLive W₂ VL₂ ζ₂ ((fun _ => σ) z.2) z.2})
    (wj := fun z t => W₁ t z.1) (ζj := fun z => ζ₁ z.1) (wk := fun z t => W₂ t z.2) (τ := fun z => σ)
    (ω := (x₀, y₀)) hown hWj (fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT)
    (A1Ref.extPath_zero_of (h₁.path x₀).1) hk (A1Ref.extPath_zero_of (h₂.path y₀).1) hgood hgeoS
    (coe_seedCapacityHorizon (fun ω => (hrec ω).own) x₀).le
    (fun s hs => seedCapacityDriver_eq_sub (fun ω => (hrec ω).own) hCc hCs hc hClb x₀ hs) hlive 0 rfl ht

/-- **The canonical right forces (corrected frame) are the seeded capacity coordinates** up to the cap. -/
theorem g3Snd_VR_eq [IsProbabilityMeasure P₁] (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ g3S₂ x y W₂ ζ₂ k y₀) (hlive : g3SndLive W₂ VL₂ ζ₂ σ y₀) (x₀ : X)
    (hgeoS : SeedImageGeometry (![0] : Fin 1 → ℝ) (g3SndWordR W₂ VL₂ σ y₀) (smallG3RhoL κ) (smallG3RhoR κ)
      (seedCapacityDriver (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k) · x₀)
      (fun i u => seedCapacityForce (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k)
        (g3ChargeEquiv (.inl i)) u x₀)
      (fun j u => seedCapacityForce (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k)
        (g3ChargeEquiv (.inr j)) u x₀)
      (seedCapacityHorizon (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k) x₀))
    (hstart : (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W' 0 + y = VL₂ 1 σ y₀)
    (j : Fin 3) {t : ℝ≥0}
    (ht : t ≤ seedCapacityHorizon (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k) x₀) :
    g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ σ j t (x₀, y₀) =
      seedCapacityForce (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k) (g3ChargeEquiv (.inr j)) t x₀ := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [g3SndVRc_zero]
    exact (hgeoS.right_zero j).symm
  obtain ⟨hown, hWj, hgood, hk⟩ := g3Col_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS x₀
  obtain ⟨hpp, hrec, hcol⟩ := g3_isSourceColumnG hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ (σ := (σ : ℝ))
    (by exact_mod_cast hσ) (by exact_mod_cast hσS)
  obtain ⟨hCc, hCs, c, hc, hClb⟩ := clock_facts_of_column hpp hcol
  have hword := smallG3_isSeedWord hκ4 hκ8 hyx (h₂.path y₀) hlive
  have hw' : IsSeedWord (![0] : Fin 1 → ℝ) (g3SndWordR W₂ VL₂ σ y₀) (smallG3RhoL κ) (smallG3RhoR κ) := hword
  have h00 : g3SndWordR W₂ VL₂ σ y₀ 0 = 0 := rfl
  have hne : ∀ j' : Fin 3, j' ≠ 0 → g3SndWordR W₂ VL₂ σ y₀ j' ≠ 0 := fun j' hj' h0 =>
    hj' (hw'.2.2.1 j' 0 (h0.trans h00.symm) h0)
  have hTa := (coe_seedCapacityHorizon (fun ω => (hrec ω).own) x₀).le
  have hw : ∀ s : ℝ≥0, s ≤ seedCapacityHorizon (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k) x₀ →
      seedCapacityDriver (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k) s x₀ =
        (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W' s - (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W' 0 :=
    fun s hs => seedCapacityDriver_eq_sub (fun ω => (hrec ω).own) hCc hCs hc hClb x₀ hs
  have hj : ∀ T : ℝ, ENNReal.ofReal T < ζ₁ x₀ → ContinuousOn (Strip.extPath (W₁ · x₀)) (Icc 0 T) :=
    fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT
  have hj0 : Strip.extPath (W₁ · x₀) 0 = 0 := A1Ref.extPath_zero_of (h₁.path x₀).1
  have hk0 : Strip.extPath (W₂ · y₀) 0 = 0 := A1Ref.extPath_zero_of (h₂.path y₀).1
  rw [g3SndVRc_of_ne y W₁ ζ₁ W₂ VL₂ ζ₂ σ j ht0]
  fin_cases j
  · exact canonSeed_eq_of_geometry_right (L := {z : X × Y | g3SndLive W₂ VL₂ ζ₂ ((fun _ => σ) z.2) z.2})
      (wj := fun z t => W₁ t z.1) (ζj := fun z => ζ₁ z.1) (wk := fun z t => W₂ t z.2) (τ := fun z => σ)
      (ω := (x₀, y₀)) hown hWj hj hj0 hk hk0 hgood hgeoS hTa hw hlive 0 rfl ht
  · refine canonForce_eq_of_geometry_right (L := {z : X × Y | g3SndLive W₂ VL₂ ζ₂ ((fun _ => σ) z.2) z.2})
      (wj := fun z t => W₁ t z.1) (ζj := fun z => ζ₁ z.1) (wk := fun z t => W₂ t z.2) (τ := fun z => σ)
      (ω := (x₀, y₀)) hown hWj hj hj0 hk hk0 hgood hgeoS hTa hw hlive (p := fun z => VL₂ 0 σ z.2) 1
      (hne 1 (by decide)) ?_ ht
    show VL₂ 0 σ y₀ = (VL₂ 0 σ y₀ - VL₂ 1 σ y₀) + _ + y
    linarith only [hstart]
  · refine canonForce_eq_of_geometry_right (L := {z : X × Y | g3SndLive W₂ VL₂ ζ₂ ((fun _ => σ) z.2) z.2})
      (wj := fun z t => W₁ t z.1) (ζj := fun z => ζ₁ z.1) (wk := fun z t => W₂ t z.2) (τ := fun z => σ)
      (ω := (x₀, y₀)) hown hWj hj hj0 hk hk0 hgood hgeoS hTa hw hlive (p := fun z => W₂ σ z.2) 2
      (hne 2 (by decide)) ?_ ht
    show W₂ σ y₀ = (W₂ σ y₀ - VL₂ 1 σ y₀) + _ + y
    linarith only [hstart]

omit mY [𝓖₂.IsRightContinuous] hκ4 hκ8 hB₁ hg₁ h₂ hB₂ in
/-- The own times of the raw caps are stopping times of the small filtration. -/
theorem isStoppingTime_g3SndTk (y₀ : Y) (σ : ℝ≥0) (k' : ℕ) :
    IsStoppingTime 𝓖₁ fun x' => (g3SndTk x y W₁ ζ₁ W₂ ζ₂ σ y₀ k' x' : WithTop ℝ≥0) := by
  have hqlo : 0 < x - y := by linarith
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun m => by fin_cases m; simp; linarith) (fun m => by fin_cases m; simp; linarith)
  have hF := isEnclFamily_cofG hne
  by_cases hg : σ ≤ g3S₂ x y W₂ ζ₂ k' y₀
  · have e : (fun x' => (g3SndTk x y W₁ ζ₁ W₂ ζ₂ σ y₀ k' x' : WithTop ℝ≥0)) =
        fun x' => (g3S₁ x y W₁ ζ₁ k' x' : WithTop ℝ≥0) := funext fun x' => by
      simp only [g3SndTk, hg, ↓reduceIte]
    rw [e]
    exact isStoppingTime_rect₁ (fun ω => (h₁.path ω).2.2.2.1) h₁.evol.2.1 (fun m => (hF.pp m).hull₁)
      (cofGN (-y) (x - y) ![x - y]) k'
  · have e : (fun x' => (g3SndTk x y W₁ ζ₁ W₂ ζ₂ σ y₀ k' x' : WithTop ℝ≥0)) = fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0) :=
      funext fun x' => by simp only [g3SndTk, hg, ↓reduceIte]
    rw [e]
    exact isStoppingTime_const 𝓖₁ _

/-- **The protected live one-sample law of the small direction** (patched data, raw caps, corrected right forces),
given the seeded capacity geometry of the column with the small image word and the image-start identity. -/
theorem g3Snd_isSeedSampleLaw_live [IsProbabilityMeasure P₁] (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ g3S₂ x y W₂ ζ₂ k y₀) (hlive : g3SndLive W₂ VL₂ ζ₂ σ y₀)
    (hgeoS : ∀ x₀, SeedImageGeometry (![0] : Fin 1 → ℝ) (g3SndWordR W₂ VL₂ σ y₀) (smallG3RhoL κ) (smallG3RhoR κ)
      (seedCapacityDriver (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k) · x₀)
      (fun i u => seedCapacityForce (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k)
        (g3ChargeEquiv (.inl i)) u x₀)
      (fun j u => seedCapacityForce (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k)
        (g3ChargeEquiv (.inr j)) u x₀)
      (seedCapacityHorizon (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k) x₀))
    (hstart : ∀ x₀, (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W' 0 + y = VL₂ 1 σ y₀) :
    IsSeedSampleLaw (P₁.withDensity fun x' => g3SndD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x', y₀))
      (fun t x' => rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) t (x', y₀))
      (fun x' => rLife (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) (x', y₀))
      (fun i t x' => g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x', y₀))
      (fun j t x' => g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ σ j t (x', y₀))
      (fun t x' => seedCapacityNoise (kh κ) (smallG3RhoL κ) (smallG3RhoR κ)
        (fun s => rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) s (x', y₀))
        (fun i s => g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ σ i s (x', y₀))
        (fun j s => g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ σ j s (x', y₀)) t)
      (fun k' x' => g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k' (x', y₀)) k := by
  have hD : (fun x' => g3SndD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x', y₀)) =
      fun x' => ENNReal.ofReal (g3M κ x y W₁ VL₁ VR₁ ζ₁ W₂ k (x', y₀) (g3S₁ x y W₁ ζ₁ k x') σ) := by
    funext x'
    simp only [g3SndD, g3M, min_eq_left hσS]
  rw [hD]
  have hcap := fun x₀ => g3Snd_cap_eq hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀
  exact g3_isSeedSampleLaw hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ (σ := (σ : ℝ)) (by exact_mod_cast hσ)
    (by exact_mod_cast hσS) hcap
    (fun x₀ t ht => g3Snd_rDrv_eq hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀ (by rwa [hcap x₀] at ht))
    (fun x₀ i t ht => g3Snd_VL_eq hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀ (hgeoS x₀) i
      (by rwa [hcap x₀] at ht))
    (fun x₀ j t ht => g3Snd_VR_eq hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀ (hgeoS x₀) (hstart x₀) j
      (by rwa [hcap x₀] at ht))
    (fun x₀ t _ => rfl) (fun x₀ => by unfold g3SndCap; exact capSnd_le_rLife _ _)
    (g3SndTk x y W₁ ζ₁ W₂ ζ₂ σ y₀) (isStoppingTime_g3SndTk hyx hx h₁ y₀ σ)
    (fun k' x₀ hle => g3Snd_cap_eq_clk hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive k' x₀ hle)
    (fun k' x₀ hle => g3Snd_cap_le_cap hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive k' x₀ hle)

end Law

end InteractingSLE.ZhanGT4.A1G3L2
