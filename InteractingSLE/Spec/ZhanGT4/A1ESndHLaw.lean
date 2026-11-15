/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ESndLaw

/-!
# Zhan's A.1 under R83, (Eight), small-curve direction: `hlaw` and `hgeo` at positive frozen times

Packet PROVE-A1-EIGHTSND (mirror of PROVE-A1-G3LAW2's `A1G3L2SndHLaw`). The inputs `hlaw` and `hgeo` of
`hasFamilyLawC_eight_of_inputs` at every positive frozen time `σ > 0`, for the original marginals (canonical data) and
their patches (densities, gates):

* **`eightSnd_hlaw_pos`**: the one-sample law with the masked caps at every good large sample `y₀ ∈ G₂` — past the
  large exit (cap `0`, the Brownian motion of the column at the exit height), at a protected but not live `σ` (cap `0`,
  the column's Brownian motion), and at a protected live `σ` (`eightSnd_isSeedSampleLaw_live`, transferred to the
  original data off `G₁` by `IsSeedSampleLaw.congr_off`);
* `eightSnd_live_gate_of_pos`: a positive raw cap forces the live event and an open gate;
* **`eightSnd_hgeo_pos`**: the geometry of the canonical data stopped at a positive raw cap at good samples.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ESnd

open QuantumZipper (H fwdHull fwdMap IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1LargeDens A1ELaw A1G3L2 A1SeedGeom

section HLaw

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  [𝓖₁.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ}
  {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ}
  {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
  {W₁o : ℝ≥0 → X → ℝ} {ζ₁o : X → ℝ≥0∞} {W₂o : ℝ≥0 → Y → ℝ} {VL₂o : Fin 1 → ℝ≥0 → Y → ℝ} {ζ₂o : Y → ℝ≥0∞}
  {G₁ : Set X} {G₂ : Set Y}

variable (hκ8 : 8 ≤ κ) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
  (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁o t x' = W₁ t x') ∧ ζ₁o x' = ζ₁ x')
  (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂o t y' = W₂ t y') ∧ (∀ i t, VL₂o i t y' = VL₂ i t y') ∧ ζ₂o y' = ζ₂ y')

include hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hag₁ hag₂

/-- **The small direction's one-sample laws at positive frozen times, masked caps** (original canonical data,
patched densities and gates), at every good large sample. -/
theorem eightSnd_hlaw_pos [IsProbabilityMeasure P₁] (hG₁ : MeasurableSet G₁) (hG₁0 : P₁ G₁ᶜ = 0) (k : ℕ) {y' : Y}
    (hy' : y' ∈ G₂) {σ : ℝ≥0} (hσ : 0 < σ) :
    IsSeedSampleLaw (P₁.withDensity fun x' => eightSndD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x', y'))
      (fun t x' => rDrv (eightSndLive W₂o VL₂o ζ₂o) x W₁o ζ₁o 0 W₂o (fun _ => σ) t (x', y'))
      (fun x' => rLife (eightSndLive W₂o VL₂o ζ₂o) x W₁o ζ₁o 0 W₂o (fun _ => σ) (x', y'))
      (fun i t x' => eightSndVL x W₁o ζ₁o W₂o VL₂o ζ₂o σ i t (x', y'))
      (fun j t x' => eightSndVR x W₁o ζ₁o W₂o VL₂o ζ₂o σ j t (x', y'))
      (fun t x' => seedCapacityNoise (kh κ) (smallEightRhoL κ) (smallEightRhoR κ)
        (fun s => rDrv (eightSndLive W₂o VL₂o ζ₂o) x W₁o ζ₁o 0 W₂o (fun _ => σ) s (x', y'))
        (fun i s => eightSndVL x W₁o ζ₁o W₂o VL₂o ζ₂o σ i s (x', y'))
        (fun j s => eightSndVR x W₁o ζ₁o W₂o VL₂o ζ₂o σ j s (x', y')) t)
      (fun k' x' => maskCap G₁ G₂ (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) σ k' (x', y')) k := by
  have hE0 : (P₁.withDensity fun x' => eightSndD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x', y')) G₁ᶜ = 0 :=
    withDensity_absolutelyContinuous _ _ hG₁0
  have hmask0 : ∀ x' ∈ G₁ᶜ, ∀ k',
      maskCap G₁ G₂ (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) σ k' (x', y') = 0 :=
    fun x' hx k' => maskCap_of_not_mem (z := (x', y')) fun h => hx h.1
  have hmask1 : ∀ x' ∉ G₁ᶜ, ∀ k', maskCap G₁ G₂ (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) σ k' (x', y') =
      eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ σ k' (x', y') :=
    fun x' hx k' => maskCap_of_mem (z := (x', y')) (not_not.1 hx) hy'
  obtain ⟨hW₂a, hV₂a, hζ₂a⟩ := hag₂ y' hy'
  have hN0 : ∀ x', seedCapacityNoise (kh κ) (smallEightRhoL κ) (smallEightRhoR κ)
      (fun s => rDrv (eightSndLive W₂o VL₂o ζ₂o) x W₁o ζ₁o 0 W₂o (fun _ => σ) s (x', y'))
      (fun i s => eightSndVL x W₁o ζ₁o W₂o VL₂o ζ₂o σ i s (x', y'))
      (fun j s => eightSndVR x W₁o ζ₁o W₂o VL₂o ζ₂o σ j s (x', y')) 0 = 0 := fun x' => by
    rw [A1RLaw.seedCapacityNoise_zero]
    have h0 := A1RLaw.cImgDrvM_zero (fun t (z : X × Y) => eightSndLive W₂o VL₂o ζ₂o t z.2) x
      (fun t (z : X × Y) => W₁o t z.1) (fun z : X × Y => ζ₁o z.1) 0 (fun t (z : X × Y) => W₂o t z.2) (fun _ => σ)
      (x', y')
    simp only [rDrv, h0, zero_div]
  have hcap0 : ∀ x', eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ σ k (x', y') = 0 →
      maskCap G₁ G₂ (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) σ k (x', y') = 0 := fun x' h0 => by
    by_cases hx' : x' ∈ G₁
    · rw [maskCap_of_mem (z := (x', y')) hx' hy', h0]
    · exact maskCap_of_not_mem (z := (x', y')) fun h => hx' h.1
  rcases lt_or_ge (eightS₂ x W₂ ζ₂ k y') σ with hσS | hσS
  · -- past the large exit: the cap vanishes
    obtain ⟨-, -, -, hS₂pos⟩ := eight_rect_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂
    obtain ⟨𝓗, Bq, hBq, hBqc⟩ := exists_brownian_eightCol hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y'
      (σ := (eightS₂ x W₂ ζ₂ k y' : ℝ)) (hS₂pos k y') le_rfl
    have hQ : (P₁.withDensity fun x' => eightSndD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x', y')) =
        seedMeasure P₁ (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k (eightS₂ x W₂ ζ₂ k y') y') (eightS₁ x W₁ ζ₁ k) := by
      rw [seedMeasure_eightCol]
      congr 1
      funext x'
      simp only [eightSndD, eightM, min_eq_right hσS.le]
    rw [hQ]
    refine isSeedSampleLaw_of_cap_zero hBq hBqc hN0 fun x' => hcap0 x' ?_
    unfold eightSndCap
    exact capSnd_of_nonpos (by simp only [eightSndOwn, not_le.2 hσS, ↓reduceIte, le_refl])
  have hll : eightSndLive W₂o VL₂o ζ₂o σ y' ↔ eightSndLive W₂ VL₂ ζ₂ σ y' := by
    have eW : (W₂o · y') = (W₂ · y') := funext hW₂a
    have eV : (VL₂o 0 · y') = (VL₂ 0 · y') := funext (hV₂a 0)
    simp only [eightSndLive, eW, eV, hζ₂a]
  by_cases hlive : eightSndLive W₂ VL₂ ζ₂ σ y'
  · -- protected and live: the identified law, transferred off `G₁`
    have hlaw := eightSnd_isSeedSampleLaw_live hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y' hσ hσS hlive
    have hcg := fun x' (hx : x' ∉ G₁ᶜ) =>
      eightSnd_data_congr (x := x) (W₁g := W₁) (ζ₁g := ζ₁) (W₂g := W₂) (ζ₂g := ζ₂)
        (hag₁ x' (not_not.1 hx)).1 (hag₁ x' (not_not.1 hx)).2 hW₂a hV₂a hζ₂a σ
    refine IsSeedSampleLaw.congr_off hlaw hG₁.compl hE0 (fun x' hx => hmask0 x' hx k)
      (fun x' hx t => (hcg x' hx).1 t) (fun x' hx => (hcg x' hx).2.1) (fun x' hx i t => (hcg x' hx).2.2.1 i t)
      (fun x' hx j t => (hcg x' hx).2.2.2.1 j t) (fun x' hx t => ?_)
      (fun x' hx k' => (hmask1 x' hx k').trans ((hcg x' hx).2.2.2.2 k'))
    have e1 : (fun s => rDrv (eightSndLive W₂o VL₂o ζ₂o) x W₁o ζ₁o 0 W₂o (fun _ => σ) s (x', y')) =
        fun s => rDrv (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) s (x', y') :=
      funext fun s => (hcg x' hx).1 s
    have e2 : (fun i s => eightSndVL x W₁o ζ₁o W₂o VL₂o ζ₂o σ i s (x', y')) =
        fun i s => eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ σ i s (x', y') :=
      funext fun i => funext fun s => (hcg x' hx).2.2.1 i s
    have e3 : (fun j s => eightSndVR x W₁o ζ₁o W₂o VL₂o ζ₂o σ j s (x', y')) =
        fun j s => eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ σ j s (x', y') :=
      funext fun j => funext fun s => (hcg x' hx).2.2.2.1 j s
    simp only [e1, e2, e3]
  · -- protected but not live: the cap vanishes
    obtain ⟨𝓗, Bq, hBq, hBqc⟩ := exists_brownian_eightCol hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y' (σ := (σ : ℝ))
      (by exact_mod_cast hσ) (by exact_mod_cast hσS)
    have hQ : (P₁.withDensity fun x' => eightSndD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x', y')) =
        seedMeasure P₁ (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y') (eightS₁ x W₁ ζ₁ k) := by
      rw [seedMeasure_eightCol]
      congr 1
      funext x'
      simp only [eightSndD, eightM, min_eq_left hσS]
    rw [hQ]
    refine isSeedSampleLaw_of_cap_zero hBq hBqc hN0 fun x' => hcap0 x' ?_
    unfold eightSndCap capSnd
    have hnl : ¬ eightSndLive W₂o VL₂o ζ₂o σ y' := fun h => hlive (hll.1 h)
    rw [Set.indicator_of_notMem (show (x', y') ∉ {z : X × Y | eightSndLive W₂o VL₂o ζ₂o ((fun _ => σ) z.2) z.2}
      from hnl)]
    simp

omit mX mY [𝓖₁.IsRightContinuous] hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hag₁ hag₂ in
/-- A positive raw cap forces the live event and an open gate (patched data). -/
theorem eightSnd_live_gate_of_pos {σ : ℝ≥0} (k : ℕ) {x₀ : X} {y₀ : Y}
    (hpos : 0 < eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀)) :
    eightSndLive W₂ VL₂ ζ₂ σ y₀ ∧ σ ≤ eightS₂ x W₂ ζ₂ k y₀ := by
  constructor
  · by_contra hnl
    unfold eightSndCap capSnd at hpos
    rw [Set.indicator_of_notMem (show (x₀, y₀) ∉ {z : X × Y | eightSndLive W₂ VL₂ ζ₂ ((fun _ => σ) z.2) z.2}
      from hnl)] at hpos
    simp at hpos
  · by_contra hg
    have h0 : eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀) = 0 := by
      unfold eightSndCap
      exact capSnd_of_nonpos (by simp only [eightSndOwn, hg, ↓reduceIte, le_refl])
    rw [h0] at hpos
    exact lt_irrefl 0 hpos

/-- **The geometry of the canonical data stopped at a positive raw cap** (good samples, positive frozen time). -/
theorem eightSnd_hgeo_pos [IsProbabilityMeasure P₁] {σ : ℝ≥0} (hσ : 0 < σ) (k : ℕ) {z : X × Y} (hz1 : z.1 ∈ G₁)
    (hz2 : z.2 ∈ G₂) (hpos : 0 < eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ σ k z) :
    SeedImageGeometry (![0] : Fin 1 → ℝ) (eightSndWordR W₂o VL₂o σ z.2) (smallEightRhoL κ) (smallEightRhoR κ)
      (fun t => rDrv (eightSndLive W₂o VL₂o ζ₂o) x W₁o ζ₁o 0 W₂o (fun _ => σ)
        (min t (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ σ k z)) z)
      (fun i t => eightSndVL x W₁o ζ₁o W₂o VL₂o ζ₂o σ i
        (min t (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ σ k z)) z)
      (fun j t => eightSndVR x W₁o ζ₁o W₂o VL₂o ζ₂o σ j
        (min t (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ σ k z)) z)
      (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ σ k z) := by
  rcases z with ⟨x₀, y₀⟩
  obtain ⟨hW₂a, hV₂a, hζ₂a⟩ := hag₂ y₀ hz2
  have hcg := eightSnd_data_congr (x := x) (W₁g := W₁) (ζ₁g := ζ₁) (W₂g := W₂) (ζ₂g := ζ₂)
    (hag₁ x₀ hz1).1 (hag₁ x₀ hz1).2 hW₂a hV₂a hζ₂a σ
  have hcap : eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀) =
      eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀) := hcg.2.2.2.2 k
  rw [hcap] at hpos ⊢
  obtain ⟨hlive, hσS⟩ := eightSnd_live_gate_of_pos k hpos
  have hword : eightSndWordR W₂o VL₂o σ y₀ = eightSndWordR W₂ VL₂ σ y₀ := by
    funext j
    simp only [eightSndWordR, hW₂a σ, hV₂a 0 σ]
  rw [hword]
  have hcapH := eightSnd_cap_eq hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀
  have hG := eightCol_geometry hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀
  rw [← hcapH] at hG
  refine hG.stop_of_eqOn
    (w' := fun t => rDrv (eightSndLive W₂o VL₂o ζ₂o) x W₁o ζ₁o 0 W₂o (fun _ => σ) t (x₀, y₀))
    (vL' := fun i t => eightSndVL x W₁o ζ₁o W₂o VL₂o ζ₂o σ i t (x₀, y₀))
    (vR' := fun j t => eightSndVR x W₁o ζ₁o W₂o VL₂o ζ₂o σ j t (x₀, y₀)) (fun t ht => ?_) (fun i t ht => ?_)
    (fun j t ht => ?_)
  · rw [hcg.1 t]
    exact eightSnd_rDrv_eq hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀ (hcapH ▸ ht)
  · rw [hcg.2.2.1 i t]
    exact eightSnd_VL_eq hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀ i (hcapH ▸ ht)
  · rw [hcg.2.2.2.1 j t]
    exact eightSnd_VR_eq hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀ j (hcapH ▸ ht)

end HLaw

end InteractingSLE.ZhanGT4.A1ESnd
