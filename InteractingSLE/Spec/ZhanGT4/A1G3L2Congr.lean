/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndFam

/-!
# Zhan's A.1 under R83: the canonical family data are pointwise in the two samples

Packet PROVE-A1-G3LAW2. The canonical image driver, lifetime, forces, seed forces and caps of A.1's families at a
pair of samples `(x₀, y₀)` read the image curve only at `x₀` and the conditioning curve only at `y₀`. So two families
whose drivers (and lifetimes, live events) agree at `x₀` and `y₀` have the same canonical data there (used to pass from
the patched marginals to the original ones off a null set):

* `rDrv_congr_pt`, `rLife_congr_pt`, `canonForce_congr_pt`, `canonSeed_congr_pt`, `capSnd_congr_pt'`;
* **`g3Snd_data_congr`**: the small direction's data (`rDrv`, `rLife`, `g3SndVL`, `g3SndVRc`, `g3SndCap`) at
  `(x₀, y₀)` are those of any other pair of G3 families agreeing at `x₀` (small driver, lifetime) and `y₀` (large
  driver, marks, lifetime).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open A1Ref A1Core A1Forces A1LargeDens A1G3Law

section Pt

variable {Ω : Type*}

/-- The masked canonical force reads only the sample's own data. -/
theorem canonForce_congr_pt {L L' : Set Ω} {xj xk : ℝ} {wj wj' : Ω → ℝ≥0 → ℝ} {ζj ζj' : Ω → ℝ≥0∞}
    {wk wk' : Ω → ℝ≥0 → ℝ} {τ τ' : Ω → ℝ≥0} {p p' : Ω → ℝ} {ω : Ω} (hL : ω ∈ L ↔ ω ∈ L')
    (hwj : wj ω = wj' ω) (hζ : ζj ω = ζj' ω) (hwk : wk ω = wk' ω) (hτ : τ ω = τ' ω) (hp : p ω = p' ω) (t : ℝ≥0) :
    canonForce L xj xk wj ζj wk τ p t ω = canonForce L' xj xk wj' ζj' wk' τ' p' t ω := by
  simp only [canonForce]
  rw [hwj, hζ, hwk, hτ, hp]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd ⟨hL.1 h1.1, h1.2⟩ h2 | exact absurd ⟨hL.2 h2.1, h2.2⟩ h1

/-- The canonical seed force reads only the sample's own data. -/
theorem canonSeed_congr_pt {L L' : Set Ω} {xj xk : ℝ} {wj wj' : Ω → ℝ≥0 → ℝ} {ζj ζj' : Ω → ℝ≥0∞}
    {wk wk' : Ω → ℝ≥0 → ℝ} {τ τ' : Ω → ℝ≥0} {ω : Ω} (hL : ω ∈ L ↔ ω ∈ L')
    (hwj : wj ω = wj' ω) (hζ : ζj ω = ζj' ω) (hwk : wk ω = wk' ω) (hτ : τ ω = τ' ω) (sgn : ℝ) (t : ℝ≥0) :
    canonSeed L xj xk wj ζj wk τ sgn t ω = canonSeed L' xj xk wj' ζj' wk' τ' sgn t ω := by
  unfold canonSeed
  congr 1
  funext n
  refine canonForce_congr_pt hL hwj hζ hwk hτ ?_ t
  classical
  simp only [seedPt, Set.indicator, hL, hwj, hζ, hwk, hτ]

end Pt

section Prod

variable {X Y : Type*}

theorem rDrv_congr_pt {live live' : ℝ≥0 → Y → Prop} {xj xk : ℝ} {Wj Wj' : ℝ≥0 → X → ℝ} {ζj ζj' : X → ℝ≥0∞}
    {Wk Wk' : ℝ≥0 → Y → ℝ} {τ : Y → ℝ≥0} {z : X × Y} (hl : live (τ z.2) z.2 ↔ live' (τ z.2) z.2)
    (hWj : (Wj · z.1) = (Wj' · z.1)) (hζ : ζj z.1 = ζj' z.1) (hWk : (Wk · z.2) = (Wk' · z.2)) (t : ℝ≥0) :
    rDrv live xj Wj ζj xk Wk τ t z = rDrv live' xj Wj' ζj' xk Wk' τ t z := by
  simp only [rDrv, cImgDrvM, cImgDrv, cImgSrc, hWj, hζ, hWk]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd (hl.1 h1) h2 | exact absurd (hl.2 h2) h1

theorem rLife_congr_pt {live live' : ℝ≥0 → Y → Prop} {xj xk : ℝ} {Wj Wj' : ℝ≥0 → X → ℝ} {ζj ζj' : X → ℝ≥0∞}
    {Wk Wk' : ℝ≥0 → Y → ℝ} {τ : Y → ℝ≥0} {z : X × Y} (hl : live (τ z.2) z.2 ↔ live' (τ z.2) z.2)
    (hWj : (Wj · z.1) = (Wj' · z.1)) (hζ : ζj z.1 = ζj' z.1) (hWk : (Wk · z.2) = (Wk' · z.2)) :
    rLife live xj Wj ζj xk Wk τ z = rLife live' xj Wj' ζj' xk Wk' τ z := by
  simp only [rLife, cImgLifeM, cImgLife, hWj, hζ, hWk]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd (hl.1 h1) h2 | exact absurd (hl.2 h2) h1

theorem capSnd_congr_pt' {live live' : ℝ≥0 → Y → Prop} {xj xk : ℝ} {Wj Wj' : ℝ≥0 → X → ℝ} {ζj ζj' : X → ℝ≥0∞}
    {Wk Wk' : ℝ≥0 → Y → ℝ} {τ : Y → ℝ≥0} {T : X × Y → ℝ} {z : X × Y} (hl : live (τ z.2) z.2 ↔ live' (τ z.2) z.2)
    (hWj : (Wj · z.1) = (Wj' · z.1)) (hζ : ζj z.1 = ζj' z.1) (hWk : (Wk · z.2) = (Wk' · z.2)) :
    capSnd live xj Wj ζj xk Wk τ T z = capSnd live' xj Wj' ζj' xk Wk' τ T z := by
  classical
  simp only [capSnd, Set.indicator, Set.mem_ofPred_eq, hWj, hζ, hWk]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd (hl.1 h1) h2 | exact absurd (hl.2 h2) h1

/-- **The small direction's family data at `(x₀, y₀)` only read the small curve at `x₀` and the large curve at
`y₀`.** -/
theorem g3Snd_data_congr {x y : ℝ} {W₁ W₁' : ℝ≥0 → X → ℝ} {ζ₁ ζ₁' : X → ℝ≥0∞} {W₂ W₂' : ℝ≥0 → Y → ℝ}
    {VL₂ VL₂' : Fin 2 → ℝ≥0 → Y → ℝ} {ζ₂ ζ₂' : Y → ℝ≥0∞} {W₁g : ℝ≥0 → X → ℝ} {ζ₁g : X → ℝ≥0∞}
    {W₂g : ℝ≥0 → Y → ℝ} {ζ₂g : Y → ℝ≥0∞} {x₀ : X} {y₀ : Y}
    (hW₁ : ∀ t, W₁ t x₀ = W₁' t x₀) (hζ₁ : ζ₁ x₀ = ζ₁' x₀) (hW₂ : ∀ t, W₂ t y₀ = W₂' t y₀)
    (hVL₂ : ∀ i t, VL₂ i t y₀ = VL₂' i t y₀) (hζ₂ : ζ₂ y₀ = ζ₂' y₀) (σ : ℝ≥0) :
    (∀ t, rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) t (x₀, y₀) =
      rDrv (g3SndLive W₂' VL₂' ζ₂') y W₁' ζ₁' 0 W₂' (fun _ => σ) t (x₀, y₀)) ∧
    rLife (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) (x₀, y₀) =
      rLife (g3SndLive W₂' VL₂' ζ₂') y W₁' ζ₁' 0 W₂' (fun _ => σ) (x₀, y₀) ∧
    (∀ i t, g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y₀) = g3SndVL y W₁' ζ₁' W₂' VL₂' ζ₂' σ i t (x₀, y₀)) ∧
    (∀ j t, g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ σ j t (x₀, y₀) = g3SndVRc y W₁' ζ₁' W₂' VL₂' ζ₂' σ j t (x₀, y₀)) ∧
    ∀ k, g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁g ζ₁g W₂g ζ₂g σ k (x₀, y₀) =
      g3SndCap x y W₁' ζ₁' W₂' VL₂' ζ₂' W₁g ζ₁g W₂g ζ₂g σ k (x₀, y₀) := by
  have eW₁ : (W₁ · x₀) = (W₁' · x₀) := funext hW₁
  have eW₂ : (W₂ · y₀) = (W₂' · y₀) := funext hW₂
  have eV₂ : ∀ i, (VL₂ i · y₀) = (VL₂' i · y₀) := fun i => funext (hVL₂ i)
  have hl : ∀ s, g3SndLive W₂ VL₂ ζ₂ s y₀ ↔ g3SndLive W₂' VL₂' ζ₂' s y₀ := fun s => by
    simp only [g3SndLive, eW₂, eV₂ 0, hζ₂]
  have hfW₁ : (fun z : X × Y => fun t => W₁ t z.1) (x₀, y₀) = (fun z : X × Y => fun t => W₁' t z.1) (x₀, y₀) := eW₁
  have hfW₂ : (fun z : X × Y => fun t => W₂ t z.2) (x₀, y₀) = (fun z : X × Y => fun t => W₂' t z.2) (x₀, y₀) := eW₂
  have hseed : ∀ sgn t, rSeedSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) sgn t (x₀, y₀) =
      rSeedSnd (g3SndLive W₂' VL₂' ζ₂') y W₁' ζ₁' 0 W₂' (fun _ => σ) sgn t (x₀, y₀) := fun sgn t =>
    canonSeed_congr_pt (L := {z : X × Y | g3SndLive W₂ VL₂ ζ₂ ((fun _ => σ) z.2) z.2})
      (L' := {z : X × Y | g3SndLive W₂' VL₂' ζ₂' ((fun _ => σ) z.2) z.2}) (xj := y) (xk := 0)
      (wj := fun z t => W₁ t z.1) (wj' := fun z t => W₁' t z.1) (ζj := fun z => ζ₁ z.1) (ζj' := fun z => ζ₁' z.1)
      (wk := fun z t => W₂ t z.2) (wk' := fun z t => W₂' t z.2) (τ := fun z => σ) (τ' := fun z => σ)
      (ω := (x₀, y₀)) (hl σ) hfW₁ hζ₁ hfW₂ rfl sgn t
  have hforce : ∀ (p p' : Y → ℝ), p y₀ = p' y₀ → ∀ t,
      rForceSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) p t (x₀, y₀) =
        rForceSnd (g3SndLive W₂' VL₂' ζ₂') y W₁' ζ₁' 0 W₂' (fun _ => σ) p' t (x₀, y₀) := fun p p' hp t =>
    canonForce_congr_pt (L := {z : X × Y | g3SndLive W₂ VL₂ ζ₂ ((fun _ => σ) z.2) z.2})
      (L' := {z : X × Y | g3SndLive W₂' VL₂' ζ₂' ((fun _ => σ) z.2) z.2}) (xj := y) (xk := 0)
      (wj := fun z t => W₁ t z.1) (wj' := fun z t => W₁' t z.1) (ζj := fun z => ζ₁ z.1) (ζj' := fun z => ζ₁' z.1)
      (wk := fun z t => W₂ t z.2) (wk' := fun z t => W₂' t z.2) (τ := fun z => σ) (τ' := fun z => σ)
      (p := fun z => p z.2) (p' := fun z => p' z.2) (ω := (x₀, y₀)) (hl σ) hfW₁ hζ₁ hfW₂ rfl hp t
  refine ⟨fun t => rDrv_congr_pt (hl σ) eW₁ hζ₁ eW₂ t, rLife_congr_pt (hl σ) eW₁ hζ₁ eW₂, fun i t => ?_,
    fun j t => ?_, fun k => capSnd_congr_pt' (hl σ) eW₁ hζ₁ eW₂⟩
  · by_cases ht : t = 0
    · subst ht
      rw [g3SndVL_zero, g3SndVL_zero]
    · rw [g3SndVL_of_ne y W₁ ζ₁ W₂ VL₂ ζ₂ σ i ht, g3SndVL_of_ne y W₁' ζ₁' W₂' VL₂' ζ₂' σ i ht]
      exact hseed (-1) t
  · by_cases ht : t = 0
    · subst ht
      rw [g3SndVRc_zero, g3SndVRc_zero]
      simp only [g3SndWordR, hW₂ σ, hVL₂ 0 σ, hVL₂ 1 σ]
    · rw [g3SndVRc_of_ne y W₁ ζ₁ W₂ VL₂ ζ₂ σ j ht, g3SndVRc_of_ne y W₁' ζ₁' W₂' VL₂' ζ₂' σ j ht]
      fin_cases j
      · exact hseed 1 t
      · exact hforce (fun y' => VL₂ 0 σ y') (fun y' => VL₂' 0 σ y') (hVL₂ 0 σ) t
      · exact hforce (fun y' => W₂ σ y') (fun y' => W₂' σ y') (hW₂ σ) t

end Prod

end InteractingSLE.ZhanGT4.A1G3L2
