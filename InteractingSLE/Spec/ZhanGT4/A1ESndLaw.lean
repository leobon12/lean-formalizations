/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ESndGeo
import InteractingSLE.Spec.ZhanGT4.A1G3L2Congr

/-!
# Zhan's A.1 under R83, (Eight), small-curve direction: the one-sample laws and the geometry at positive frozen times

Packet PROVE-A1-EIGHTSND (mirror of PROVE-A1-G3LAW2's `A1G3L2SndLaw`, `A1G3L2Congr`, `A1G3L2SndHLaw`):

* **`eightSnd_VL_eq`**, **`eightSnd_VR_eq`**: the canonical forces (physical frame) are the seeded capacity coordinates
  up to the cap (PROVE-A1-G3LAW2's `canonSeed_eq_of_geometry_*`, `canonForce_eq_of_geometry_right`);
* **`eightSnd_isSeedSampleLaw_live`**: the protected live one-sample law of the canonical data (A1-EIGHTLAW's
  `eight_isSeedSampleLaw`);
* `exists_brownian_eightCol`: a continuous Brownian motion under the seeded measure of a column (zero-cap laws);
* **`eightSnd_data_congr`**: the family data at `(x₀, y₀)` only read the two sample paths;
* **`eightSnd_hlaw_pos`**: the one-sample law with the masked caps at every good large sample and every positive frozen
  time (past the large exit and protected-not-live: zero cap; protected live: the identified law, transferred off `G₁`
  by `IsSeedSampleLaw.congr_off`);
* **`eightSnd_hgeo_pos`**: the geometry of the canonical data stopped at a positive raw cap at good samples.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ESnd

open QuantumZipper (H fwdHull fwdMap IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1LargeDens A1ELaw A1G3L2 A1SeedGeom Girsanov

/-! ### The forces and the live law -/

section Law

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  [𝓖₁.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ}
  {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ}
  {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable (hκ8 : 8 ≤ κ) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))

include hκ8 hx h₁ hB₁ hg₁ h₂ hB₂

/-- **The canonical left seed force is the seeded capacity coordinate** up to the cap. -/
theorem eightSnd_VL_eq [IsProbabilityMeasure P₁] (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ eightS₂ x W₂ ζ₂ k y₀) (hlive : eightSndLive W₂ VL₂ ζ₂ σ y₀) (x₀ : X) (i : Fin 1) {t : ℝ≥0}
    (ht : t ≤ seedCapacityHorizon (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (eightS₁ x W₁ ζ₁ k) x₀) :
    eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y₀) = seedCapacityForce (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀)
      (eightS₁ x W₁ ζ₁ k) (eightChargeEquiv (.inl i)) t x₀ := by
  have hgeoS := eightCol_geometry hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  by_cases ht0 : t = 0
  · subst ht0
    rw [eightSndVL_zero]
    exact (hgeoS.left_zero 0).symm
  obtain ⟨hown, hWj, hgood, hk⟩ := eightCol_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS x₀
  have hrec := fun ω => eight_isSourceRecord hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ (σ := (σ : ℝ)) (by exact_mod_cast hσ)
    (by exact_mod_cast hσS) ω
  obtain ⟨hCc, hCs, c, hc, hClb⟩ := eightCol_clock hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS
  rw [eightSndVL_of_ne x W₁ ζ₁ W₂ VL₂ ζ₂ σ 0 ht0]
  exact canonSeed_eq_of_geometry_left (L := {z : X × Y | eightSndLive W₂ VL₂ ζ₂ ((fun _ => σ) z.2) z.2})
    (wj := fun z t => W₁ t z.1) (ζj := fun z => ζ₁ z.1) (wk := fun z t => W₂ t z.2) (τ := fun z => σ)
    (ω := (x₀, y₀)) hown hWj (fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT)
    (A1Ref.extPath_zero_of (h₁.path x₀).1) hk (A1Ref.extPath_zero_of (h₂.path y₀).1) hgood hgeoS
    (coe_seedCapacityHorizon (fun ω => (hrec ω).own) x₀).le
    (fun s hs => seedCapacityDriver_eq_sub (fun ω => (hrec ω).own) hCc hCs hc hClb x₀ hs) hlive 0 rfl ht

/-- **The canonical right forces (physical frame) are the seeded capacity coordinates** up to the cap. -/
theorem eightSnd_VR_eq [IsProbabilityMeasure P₁] (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ eightS₂ x W₂ ζ₂ k y₀) (hlive : eightSndLive W₂ VL₂ ζ₂ σ y₀) (x₀ : X) (j : Fin 2) {t : ℝ≥0}
    (ht : t ≤ seedCapacityHorizon (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (eightS₁ x W₁ ζ₁ k) x₀) :
    eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ σ j t (x₀, y₀) = seedCapacityForce (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀)
      (eightS₁ x W₁ ζ₁ k) (eightChargeEquiv (.inr j)) t x₀ := by
  have hgeoS := eightCol_geometry hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀
  by_cases ht0 : t = 0
  · subst ht0
    rw [eightSndVR_zero]
    exact (hgeoS.right_zero j).symm
  obtain ⟨hown, hWj, hgood, hk⟩ := eightCol_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS x₀
  have hrec := fun ω => eight_isSourceRecord hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ (σ := (σ : ℝ)) (by exact_mod_cast hσ)
    (by exact_mod_cast hσS) ω
  obtain ⟨hCc, hCs, c, hc, hClb⟩ := eightCol_clock hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS
  have hstart := eightCol_hstart hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀
  have hTa := (coe_seedCapacityHorizon (fun ω => (hrec ω).own) x₀).le
  have hw : ∀ s : ℝ≥0, s ≤ seedCapacityHorizon (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (eightS₁ x W₁ ζ₁ k) x₀ →
      seedCapacityDriver (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (eightS₁ x W₁ ζ₁ k) s x₀ =
        (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W' s - (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W' 0 :=
    fun s hs => seedCapacityDriver_eq_sub (fun ω => (hrec ω).own) hCc hCs hc hClb x₀ hs
  have hj : ∀ T : ℝ, ENNReal.ofReal T < ζ₁ x₀ → ContinuousOn (Strip.extPath (W₁ · x₀)) (Icc 0 T) :=
    fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT
  have hj0 : Strip.extPath (W₁ · x₀) 0 = 0 := A1Ref.extPath_zero_of (h₁.path x₀).1
  have hk0 : Strip.extPath (W₂ · y₀) 0 = 0 := A1Ref.extPath_zero_of (h₂.path y₀).1
  have hpos : 0 < W₂ σ y₀ - VL₂ 0 σ y₀ := by linarith [hlive.2 σ le_rfl]
  rw [eightSndVR_of_ne x W₁ ζ₁ W₂ VL₂ ζ₂ σ j ht0]
  fin_cases j
  · exact canonSeed_eq_of_geometry_right (L := {z : X × Y | eightSndLive W₂ VL₂ ζ₂ ((fun _ => σ) z.2) z.2})
      (wj := fun z t => W₁ t z.1) (ζj := fun z => ζ₁ z.1) (wk := fun z t => W₂ t z.2) (τ := fun z => σ)
      (ω := (x₀, y₀)) hown hWj hj hj0 hk hk0 hgood hgeoS hTa hw hlive 0 rfl ht
  · refine canonForce_eq_of_geometry_right (L := {z : X × Y | eightSndLive W₂ VL₂ ζ₂ ((fun _ => σ) z.2) z.2})
      (wj := fun z t => W₁ t z.1) (ζj := fun z => ζ₁ z.1) (wk := fun z t => W₂ t z.2) (τ := fun z => σ)
      (ω := (x₀, y₀)) hown hWj hj hj0 hk hk0 hgood hgeoS hTa hw hlive (p := fun z => W₂ σ z.2) 1
      hpos.ne' ?_ ht
    show W₂ σ y₀ = (W₂ σ y₀ - VL₂ 0 σ y₀) + _ + x
    linarith only [hstart]

omit mY hκ8 hB₁ hg₁ h₂ hB₂ in
/-- The own times of the raw caps are stopping times of the small filtration. -/
theorem isStoppingTime_eightSndTk (y₀ : Y) (σ : ℝ≥0) (k' : ℕ) :
    IsStoppingTime 𝓖₁ fun x' => (eightSndTk x W₁ ζ₁ W₂ ζ₂ σ y₀ k' x' : WithTop ℝ≥0) := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  by_cases hg : σ ≤ eightS₂ x W₂ ζ₂ k' y₀
  · have e : (fun x' => (eightSndTk x W₁ ζ₁ W₂ ζ₂ σ y₀ k' x' : WithTop ℝ≥0)) =
        fun x' => (eightS₁ x W₁ ζ₁ k' x' : WithTop ℝ≥0) := funext fun x' => by
      simp only [eightSndTk, hg, ↓reduceIte]
    rw [e]
    exact isStoppingTime_rect₁ (fun ω => (h₁.path ω).2.2.2.1) h₁.evol.2.1 (fun m => (hF.pp m).hull₁)
      (fun m => (goodSeq (-x) (![] : Fin 0 → ℝ) m).cap) k'
  · have e : (fun x' => (eightSndTk x W₁ ζ₁ W₂ ζ₂ σ y₀ k' x' : WithTop ℝ≥0)) = fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0) :=
      funext fun x' => by simp only [eightSndTk, hg, ↓reduceIte]
    rw [e]
    exact isStoppingTime_const 𝓖₁ _

/-- **The protected live one-sample law of the small direction** (patched data, raw caps). -/
theorem eightSnd_isSeedSampleLaw_live [IsProbabilityMeasure P₁] (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ eightS₂ x W₂ ζ₂ k y₀) (hlive : eightSndLive W₂ VL₂ ζ₂ σ y₀) :
    IsSeedSampleLaw (P₁.withDensity fun x' => eightSndD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x', y₀))
      (fun t x' => rDrv (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) t (x', y₀))
      (fun x' => rLife (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) (x', y₀))
      (fun i t x' => eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x', y₀))
      (fun j t x' => eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ σ j t (x', y₀))
      (fun t x' => seedCapacityNoise (kh κ) (smallEightRhoL κ) (smallEightRhoR κ)
        (fun s => rDrv (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) s (x', y₀))
        (fun i s => eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ σ i s (x', y₀))
        (fun j s => eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ σ j s (x', y₀)) t)
      (fun k' x' => eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k' (x', y₀)) k := by
  have hD : (fun x' => eightSndD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x', y₀)) =
      fun x' => ENNReal.ofReal (eightM κ x W₁ VL₁ VR₁ ζ₁ W₂ k (x', y₀) (eightS₁ x W₁ ζ₁ k x') σ) := by
    funext x'
    simp only [eightSndD, eightM, min_eq_left hσS]
  rw [hD]
  have hcap := fun x₀ => eightSnd_cap_eq hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀
  exact eight_isSeedSampleLaw hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ (σ := (σ : ℝ)) (by exact_mod_cast hσ)
    (by exact_mod_cast hσS) hcap
    (fun x₀ t ht => eightSnd_rDrv_eq hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀ (by rwa [hcap x₀] at ht))
    (fun x₀ i t ht => eightSnd_VL_eq hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀ i (by rwa [hcap x₀] at ht))
    (fun x₀ j t ht => eightSnd_VR_eq hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀ j (by rwa [hcap x₀] at ht))
    (fun x₀ t _ => rfl) (fun x₀ => by unfold eightSndCap; exact capSnd_le_rLife _ _)
    (eightSndTk x W₁ ζ₁ W₂ ζ₂ σ y₀) (isStoppingTime_eightSndTk hx h₁ y₀ σ)
    (fun k' x₀ hle => eightSnd_cap_eq_clk hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive k' x₀ hle)
    (fun k' x₀ hle => eightSnd_cap_le_cap hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive k' x₀ hle)

/-- **A continuous Brownian motion under the seeded measure of a column** (the capacity Brownian motion of
A1-EIGHTLAW's seed-column (D10)). -/
theorem exists_brownian_eightCol [IsProbabilityMeasure P₁] (k : ℕ) (y₀ : Y) {σ : ℝ} (hσ : 0 < σ)
    (hσS : σ ≤ eightS₂ x W₂ ζ₂ k y₀) :
    ∃ (𝓗 : Filtration ℝ≥0 mX) (B : ℝ≥0 → X → ℝ),
      IsFilteredBrownianReal 𝓗 B (seedMeasure P₁ (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (eightS₁ x W₁ ζ₁ k)) ∧
        ∀ ω, Continuous (B · ω) := by
  obtain ⟨hpp, hcol⟩ := eight_isSourceColumn hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  obtain ⟨W₂', Vlo, Vhi, B, D, hrec, -⟩ := id hcol
  have hκd : ∀ ω, (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ ω).κ = kh κ := fun ω =>
    congrArg SeedData.κ (hrec ω).source
  have hrd : ∀ ω, (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ ω).r = eightRR κ := fun ω =>
    congrArg SeedData.r (hrec ω).source
  obtain ⟨Bh, hCc, hCm, hcm, hcap, hcont⟩ := exists_seedCapacityBrownian_of_seedColumn hpp hk hcol eightChargeEquiv
    (fun ω i => imageCharge_eight_left (by linarith) (hκd ω) (hrd ω) i)
    (fun ω j => imageCharge_eight_right (by linarith) (hκd ω) (hrd ω) j)
  exact ⟨_, _, hcap.1, hcont⟩

end Law

/-! ### Pointwise congruence of the family data -/

section Congr

variable {X Y : Type*}

/-- **The small direction's family data at `(x₀, y₀)` only read the small curve at `x₀` and the large curve at
`y₀`.** -/
theorem eightSnd_data_congr {x : ℝ} {W₁ W₁' : ℝ≥0 → X → ℝ} {ζ₁ ζ₁' : X → ℝ≥0∞} {W₂ W₂' : ℝ≥0 → Y → ℝ}
    {VL₂ VL₂' : Fin 1 → ℝ≥0 → Y → ℝ} {ζ₂ ζ₂' : Y → ℝ≥0∞} {W₁g : ℝ≥0 → X → ℝ} {ζ₁g : X → ℝ≥0∞}
    {W₂g : ℝ≥0 → Y → ℝ} {ζ₂g : Y → ℝ≥0∞} {x₀ : X} {y₀ : Y}
    (hW₁ : ∀ t, W₁ t x₀ = W₁' t x₀) (hζ₁ : ζ₁ x₀ = ζ₁' x₀) (hW₂ : ∀ t, W₂ t y₀ = W₂' t y₀)
    (hVL₂ : ∀ i t, VL₂ i t y₀ = VL₂' i t y₀) (hζ₂ : ζ₂ y₀ = ζ₂' y₀) (σ : ℝ≥0) :
    (∀ t, rDrv (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) t (x₀, y₀) =
      rDrv (eightSndLive W₂' VL₂' ζ₂') x W₁' ζ₁' 0 W₂' (fun _ => σ) t (x₀, y₀)) ∧
    rLife (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) (x₀, y₀) =
      rLife (eightSndLive W₂' VL₂' ζ₂') x W₁' ζ₁' 0 W₂' (fun _ => σ) (x₀, y₀) ∧
    (∀ i t, eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y₀) = eightSndVL x W₁' ζ₁' W₂' VL₂' ζ₂' σ i t (x₀, y₀)) ∧
    (∀ j t, eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ σ j t (x₀, y₀) = eightSndVR x W₁' ζ₁' W₂' VL₂' ζ₂' σ j t (x₀, y₀)) ∧
    ∀ k, eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁g ζ₁g W₂g ζ₂g σ k (x₀, y₀) =
      eightSndCap x W₁' ζ₁' W₂' VL₂' ζ₂' W₁g ζ₁g W₂g ζ₂g σ k (x₀, y₀) := by
  have eW₁ : (W₁ · x₀) = (W₁' · x₀) := funext hW₁
  have eW₂ : (W₂ · y₀) = (W₂' · y₀) := funext hW₂
  have eV₂ : ∀ i, (VL₂ i · y₀) = (VL₂' i · y₀) := fun i => funext (hVL₂ i)
  have hl : ∀ s, eightSndLive W₂ VL₂ ζ₂ s y₀ ↔ eightSndLive W₂' VL₂' ζ₂' s y₀ := fun s => by
    simp only [eightSndLive, eW₂, eV₂ 0, hζ₂]
  have hfW₁ : (fun z : X × Y => fun t => W₁ t z.1) (x₀, y₀) = (fun z : X × Y => fun t => W₁' t z.1) (x₀, y₀) :=
    eW₁
  have hfW₂ : (fun z : X × Y => fun t => W₂ t z.2) (x₀, y₀) = (fun z : X × Y => fun t => W₂' t z.2) (x₀, y₀) :=
    eW₂
  have hseed : ∀ sgn t, rSeedSnd (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) sgn t (x₀, y₀) =
      rSeedSnd (eightSndLive W₂' VL₂' ζ₂') x W₁' ζ₁' 0 W₂' (fun _ => σ) sgn t (x₀, y₀) := fun sgn t =>
    canonSeed_congr_pt (L := {z : X × Y | eightSndLive W₂ VL₂ ζ₂ ((fun _ => σ) z.2) z.2})
      (L' := {z : X × Y | eightSndLive W₂' VL₂' ζ₂' ((fun _ => σ) z.2) z.2}) (xj := x) (xk := 0)
      (wj := fun z t => W₁ t z.1) (wj' := fun z t => W₁' t z.1) (ζj := fun z => ζ₁ z.1) (ζj' := fun z => ζ₁' z.1)
      (wk := fun z t => W₂ t z.2) (wk' := fun z t => W₂' t z.2) (τ := fun z => σ) (τ' := fun z => σ)
      (ω := (x₀, y₀)) (hl σ) hfW₁ hζ₁ hfW₂ rfl sgn t
  have hforce : ∀ (p p' : Y → ℝ), p y₀ = p' y₀ → ∀ t,
      rForceSnd (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) p t (x₀, y₀) =
        rForceSnd (eightSndLive W₂' VL₂' ζ₂') x W₁' ζ₁' 0 W₂' (fun _ => σ) p' t (x₀, y₀) := fun p p' hp t =>
    canonForce_congr_pt (L := {z : X × Y | eightSndLive W₂ VL₂ ζ₂ ((fun _ => σ) z.2) z.2})
      (L' := {z : X × Y | eightSndLive W₂' VL₂' ζ₂' ((fun _ => σ) z.2) z.2}) (xj := x) (xk := 0)
      (wj := fun z t => W₁ t z.1) (wj' := fun z t => W₁' t z.1) (ζj := fun z => ζ₁ z.1) (ζj' := fun z => ζ₁' z.1)
      (wk := fun z t => W₂ t z.2) (wk' := fun z t => W₂' t z.2) (τ := fun z => σ) (τ' := fun z => σ)
      (p := fun z => p z.2) (p' := fun z => p' z.2) (ω := (x₀, y₀)) (hl σ) hfW₁ hζ₁ hfW₂ rfl hp t
  refine ⟨fun t => rDrv_congr_pt (hl σ) eW₁ hζ₁ eW₂ t, rLife_congr_pt (hl σ) eW₁ hζ₁ eW₂, fun i t => ?_,
    fun j t => ?_, fun k => capSnd_congr_pt' (hl σ) eW₁ hζ₁ eW₂⟩
  · by_cases ht : t = 0
    · subst ht
      rw [eightSndVL_zero, eightSndVL_zero]
    · rw [eightSndVL_of_ne x W₁ ζ₁ W₂ VL₂ ζ₂ σ i ht, eightSndVL_of_ne x W₁' ζ₁' W₂' VL₂' ζ₂' σ i ht]
      exact hseed (-1) t
  · by_cases ht : t = 0
    · subst ht
      rw [eightSndVR_zero, eightSndVR_zero]
      simp only [eightSndWordR, hW₂ σ, hVL₂ 0 σ]
    · rw [eightSndVR_of_ne x W₁ ζ₁ W₂ VL₂ ζ₂ σ j ht, eightSndVR_of_ne x W₁' ζ₁' W₂' VL₂' ζ₂' σ j ht]
      fin_cases j
      · exact hseed 1 t
      · exact hforce (fun y' => W₂ σ y') (fun y' => W₂' σ y') (hW₂ σ) t

end Congr

end InteractingSLE.ZhanGT4.A1ESnd
