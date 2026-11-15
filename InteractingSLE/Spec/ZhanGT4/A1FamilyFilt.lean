/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1FrozenPath
import InteractingSLE.Spec.ZhanGT4.DualSeedCloseAssembly

/-!
# A.1's seeded frozen-sample families, I: the capacity-time filtration of the seeded line

Packet PROVE-A1-FAMILY (R76). Source: Astra, *Follow-up proofs* §A.1.3 (`ig1_followup_proofs.txt` L341–L353, R38):
"the time change `du = A²_{j,1} dt_j`, Lévy's characterization, and uniqueness in law of the integrated force system
identify the claimed conditional image law"; follow-up 4 §2.5 (R71: seeds); follow-up 5 §1.3 (R73).

A22's seeded line constructs the capacity Brownian motion of the actual seeded image coordinates
(`exists_SeedCapacityBrownian_actual_coordinates`) but hides its filtration in an existential. The frozen-sample law
of A1-FROZEN (`A1Frozen.IsFrozenSampleLaw`) needs that filtration to see the image data before the cap. This file
exposes it — it is the time change `𝓗_u = 𝓕_{τ_u}` of the own filtration by the inverse `τ_u` of the own-time quadratic
clock of the continued capacity coefficient — and proves the measurability of the seeded image data in it:

* **`seedFilt`**, `seedBh`: the capacity-time filtration and the capacity Brownian motion;
* **`seedCapacityBrownian_seedFilt`**: A22's capacity Brownian motion in the exposed filtration (same premises as
  `exists_SeedCapacityBrownian_actual_coordinates`, in particular A22's named `SeedOwnD10Integral`);
* `clock_props`: the clock facts (continuity, strict monotonicity, linear lower bound, adaptedness) from the protected
  coefficient bounds;
* **`measurableSet_lt_seedCapacityHorizon`**: the cap event `{s < a(S)}` is an event of `𝓗_s`;
* **`measurable_seedCapacityDriver`**, **`measurable_seedCapacityForce`**: the capacity-time image driver and forces
  are adapted to `𝓗` (own-time progressive data read at the inverse clock);
* **`measurableSet_cap_le_inter`**: a further cap — the image capacity at another own-time stopping time `T'` —
  satisfies `{cap ≤ r} ∩ {s < a(S)} ∈ 𝓗_s` for `r ≤ s`;
* `seedCapacityNoise_congr`: the residual at `t` reads the image data on `[0, t]` only;
* **`IsSeedSampleLaw`**: the one-sample image law (A1-FROZEN's frozen-sample law with the image data written as
  functions of the image sample), and **`isSeedSampleLaw_of_seed`**: the one-sample law from A22's seeded line — every
  generator clause of the image-data filtration is proved in `seedFilt`;
* `preimage_mem_imageGen`, **`IsSeedSampleLaw.isFrozenSampleLaw`**, **`IsSeedSampleLaw.isFrozenSampleLawFst`**: the
  frozen-sample laws of A1-FROZEN are the one-sample laws of the sections.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Family

open Girsanov

section Filt

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ} {d : Ω → SeedData n}
  {S : Ω → ℝ≥0}

/-- **The capacity-time filtration of the seeded line**: `𝓗_u = 𝓕_{τ_u}`, `τ_u` the inverse of the own-time clock
(the filtration of A22's capacity Brownian motion, `isFilteredBrownianReal_timeChange`). -/
def seedFilt (𝓕 : Filtration ℝ≥0 mΩ) (d : Ω → SeedData n) (S : Ω → ℝ≥0)
    (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
    (hCm : ∀ ω, Monotone (seedQuadClock (seedCapacityCoeff d S) ω))
    (hmeas : ∀ r : ℝ≥0, Measurable[𝓕 r] fun ω => seedQuadClock (seedCapacityCoeff d S) ω r) : Filtration ℝ≥0 mΩ :=
  Zhan.Retarget.timeChangeFilt 𝓕 (isStoppingTime_invClock hCc hCm hmeas) (invClock_mono hCc hCm)

/-- **The capacity Brownian motion of the seeded line**: the spliced own-time mapped noise read at the inverse
clock. -/
def seedBh (κ : ℝ) (d : Ω → SeedData n) (S : Ω → ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  seedOwnMappedNoise κ d S B (invClockT (seedQuadClock (seedCapacityCoeff d S)) u ω) ω

/-- **The clock facts** from the protected coefficient bounds (A22's premises of
`exists_SeedCapacityBrownian_actual_coordinates`). -/
theorem clock_props (hm : ∀ u, Measurable[𝓕 u] ({ω | u ≤ S ω}.indicator fun ω => (d ω).A 1 u - 1))
    (hcA : ∀ ω, ContinuousOn (fun u : ℝ≥0 => (d ω).A 1 u) (Ioc 0 (S ω)))
    {C a₀ : ℝ} (ha : 0 < a₀)
    (hb : ∀ ω u, 0 < u → u ≤ S ω → |(d ω).A 1 u| ≤ C)
    (hlb : ∀ ω u, 0 < u → u ≤ S ω → a₀ ≤ (d ω).A 1 u) :
    (∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω)) ∧
      (∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff d S) ω)) ∧
      (∀ r : ℝ≥0, Measurable[𝓕 r] fun ω => seedQuadClock (seedCapacityCoeff d S) ω r) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ ω r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) ω r := by
  have hprog := (seedCapacityCoeff_predictable 𝓕 hm hcA).isStronglyProgressive
  have hbound := abs_seedCapacityCoeff_le hb
  have hlow := seedCapacityCoeff_sq_ge ha hlb
  have hpos : 0 < min (a₀ ^ 2) 1 := lt_min (sq_pos_of_pos ha) zero_lt_one
  exact ⟨continuous_seedQuadClock hprog hbound, strictMono_seedQuadClock hprog hbound hpos hlow,
    measurable_seedQuadClock hprog, _, hpos, seedQuadClock_ge hprog hbound hlow⟩

/-- `𝓗_u` is the stopped σ-algebra of `τ_u`. -/
theorem seedFilt_apply (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
    (hCm : ∀ ω, Monotone (seedQuadClock (seedCapacityCoeff d S) ω))
    (hmeas : ∀ r : ℝ≥0, Measurable[𝓕 r] fun ω => seedQuadClock (seedCapacityCoeff d S) ω r) (u : ℝ≥0) :
    seedFilt 𝓕 d S hCc hCm hmeas u = (isStoppingTime_invClock hCc hCm hmeas u).measurableSpace := rfl

/-- **A22's capacity Brownian motion in the exposed capacity-time filtration** (the premises of
`exists_SeedCapacityBrownian_actual_coordinates`, in particular A22's named stochastic (D10) input
`SeedOwnD10Integral`): the capacity Brownian motion `seedBh` is a Brownian motion of `seedFilt` under `Q`, equal to the
residual of the actual capacity-time image coordinates up to the capacity horizon, and continuous. -/
theorem seedCapacityBrownian_seedFilt {Q : Measure Ω} {nL nR : ℕ} {A : Ω → Set ℂ} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (e : Fin nL ⊕ Fin nR ≃ Fin (n + 1))
    (hB : IsFilteredBrownianReal 𝓕 B Q) (hBc : ∀ ω, Continuous (B · ω))
    (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hm : ∀ u, Measurable[𝓕 u] ({ω | u ≤ S ω}.indicator fun ω => (d ω).A 1 u - 1))
    (hcA : ∀ ω, ContinuousOn (fun u : ℝ≥0 => (d ω).A 1 u) (Ioc 0 (S ω)))
    {C a₀ : ℝ} (ha : 0 < a₀)
    (hb : ∀ ω u, 0 < u → u ≤ S ω → |(d ω).A 1 u| ≤ C)
    (hlb : ∀ ω u, 0 < u → u ≤ S ω → a₀ ≤ (d ω).A 1 u)
    (hκ : ∀ ω, (d ω).κ = κ)
    (hρL : ∀ ω i, (d ω).imageCharge (e (.inl i)) = ρL i)
    (hρR : ∀ ω j, (d ω).imageCharge (e (.inr j)) = ρR j)
    (h20 : ∀ ω, ContinuousOn (d ω).A20 (Icc 0 (S ω)))
    (hsep : ∀ ω t, t ∈ Icc (0 : ℝ) (S ω) → (d ω).A 0 t ≠ (d ω).A20 t)
    (hseed : ∀ ω, (d ω).ImageEntranceIntegrable (S ω))
    (hYm : ∀ u, Measurable[𝓕 u] (seedOwnMappedNoise κ d S B u))
    (hD10 : SeedOwnD10Integral Q 𝓕 B κ d S)
    (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
    (hCm : ∀ ω, Monotone (seedQuadClock (seedCapacityCoeff d S) ω))
    (hmeas : ∀ r : ℝ≥0, Measurable[𝓕 r] fun ω => seedQuadClock (seedCapacityCoeff d S) ω r) :
    SeedCapacityBrownian κ ρL ρR Q (seedFilt 𝓕 d S hCc hCm hmeas) (seedCapacityDriver d S)
        (fun i => seedCapacityForce d S (e (.inl i))) (fun j => seedCapacityForce d S (e (.inr j)))
        (seedCapacityHorizon d S) (seedBh κ d S B) ∧
      ∀ ω, Continuous (seedBh κ d S B · ω) := by
  have hprog := (seedCapacityCoeff_predictable 𝓕 hm hcA).isStronglyProgressive
  have hbound := abs_seedCapacityCoeff_le hb
  have hlow := seedCapacityCoeff_sq_ge ha hlb
  have hpos : 0 < min (a₀ ^ 2) 1 := lt_min (sq_pos_of_pos ha) zero_lt_one
  have hCs := strictMono_seedQuadClock hprog hbound hpos hlow
  have hClb := seedQuadClock_ge hprog hbound hlow
  have hi (ω : Ω) (i : Fin (n + 1)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (S ω)) :=
    (d ω).imageWeightedGap_integrable (hown ω) (h20 ω) (hsep ω) (hseed ω) i ht
  have hYc := continuous_seedOwnMappedNoise (κ := κ) hown hBc
    (fun ω i => hi ω i (S ω) ⟨(S ω).coe_nonneg, le_rfl⟩)
  have : IsProbabilityMeasure Q := hB.isProbabilityMeasure'
  have hZ := seed_martingale_wald_of_integral (isFilteredPreBrownian_of_isFilteredBrownianReal hB) hprog hbound
    (seedCapacityCoeff_riemannRegular Q hcA) hYm hD10
  refine ⟨⟨isFilteredBrownianReal_timeChange hYc hYm (seedOwnMappedNoise_zero κ d S B) hCc hCs
      (seedQuadClock_zero _) hpos hClb hmeas hZ, ?_⟩,
    fun ω => (hYc ω).comp (continuous_invClockT hCc hCs (seedQuadClock_zero _) hpos hClb ω)⟩
  intro ω u hu
  have hW (ω : Ω) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (S ω)) :
      seedCapacityDriver d S ((d ω).a u).toNNReal ω = (d ω).A 0 u - (d ω).A 0 0 := by
    have hule : u.toNNReal ≤ S ω := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hu.2
    simpa only [Real.coe_toNNReal _ hu.1] using
      seedCapacityDriver_at_capacity hown hCc hCs hpos hClb ω hule
  have hV (ω : Ω) (i : Fin (n + 1)) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (S ω)) :
      seedCapacityForce d S i ((d ω).a u).toNNReal ω = (d ω).imageForce u i - (d ω).A 0 0 := by
    have hule : u.toNNReal ≤ S ω := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hu.2
    simpa only [Real.coe_toNNReal _ hu.1] using
      seedCapacityForce_at_capacity hown hCc hCs hpos hClb ω i hule
  have hval := invClock_eq_coe hCc (seedQuadClock_zero _) hpos hClb u ω
  have hS0 : 0 ≤ (d ω).a (S ω) := by
    rw [← (hown ω).a0]
    exact (hown ω).mono.monotoneOn ⟨le_rfl, (hown ω).pos.le⟩ ⟨(S ω).coe_nonneg, le_rfl⟩ (S ω).coe_nonneg
  have hCS : seedQuadClock (seedCapacityCoeff d S) ω (S ω) = (d ω).a (S ω) := seedCapacityCoeff_clock_eq hown ω le_rfl
  have hu' : (u : ℝ) ≤ seedQuadClock (seedCapacityCoeff d S) ω (S ω) := by
    have hh : (u : ℝ) ≤ (seedCapacityHorizon d S ω : ℝ) := hu
    rwa [seedCapacityHorizon, Real.coe_toNNReal _ hS0, ← hCS] at hh
  have hτ : invClockT (seedQuadClock (seedCapacityCoeff d S)) u ω ≤ S ω := (hCs ω).le_iff_le.1 (hval.2.1.trans_le hu')
  have he := seed_capacityNoise_eq_ownMappedNoise (κ := κ) (B := B) (ρL := ρL) (ρR := ρR) e hown hκ hρL hρR
    hW hV hi ω _ hτ
  rw [← seedCapacityCoeff_clock_eq hown ω hτ, show seedQuadClock (seedCapacityCoeff d S) ω
    (invClockT (seedQuadClock (seedCapacityCoeff d S)) u ω) = u from hval.2.1, Real.toNNReal_coe] at he
  exact he.symm

section Gen

variable {A : Ω → Set ℂ} (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
  (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
  (hCm : ∀ ω, Monotone (seedQuadClock (seedCapacityCoeff d S) ω))
  (hmeas : ∀ r : ℝ≥0, Measurable[𝓕 r] fun ω => seedQuadClock (seedCapacityCoeff d S) ω r)
  (hCs : ∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff d S) ω)) {c : ℝ} (hc : 0 < c)
  (hClb : ∀ ω r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) ω r)

include hown hCc hCs hc hClb in
/-- Before the capacity horizon in capacity time is before the own horizon in own time. -/
theorem lt_seedCapacityHorizon_iff (ω : Ω) (s : ℝ≥0) :
    s < seedCapacityHorizon d S ω ↔ invClockT (seedQuadClock (seedCapacityCoeff d S)) s ω < S ω := by
  have hval := invClock_eq_coe hCc (seedQuadClock_zero _) hc hClb s ω
  have hCS : seedQuadClock (seedCapacityCoeff d S) ω (S ω) = (d ω).a (S ω) := seedCapacityCoeff_clock_eq hown ω le_rfl
  rw [seedCapacityHorizon, Real.lt_toNNReal_iff_coe_lt, ← hCS, ← hval.2.1, (hCs ω).lt_iff_lt]

include hown hCs hc hClb in
/-- **The cap event is an event of the capacity-time filtration**: `{s < a(S)} ∈ 𝓗_s`. -/
theorem measurableSet_lt_seedCapacityHorizon (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (s : ℝ≥0) :
    MeasurableSet[seedFilt 𝓕 d S hCc hCm hmeas s] {ω | s < seedCapacityHorizon d S ω} := by
  have e : {ω | s < seedCapacityHorizon d S ω} =
      {ω | (S ω : WithTop ℝ≥0) ≤ invClock (seedQuadClock (seedCapacityCoeff d S)) s ω}ᶜ := by
    ext ω
    rw [mem_ofPred_eq, mem_compl_iff, mem_ofPred_eq, (invClock_eq_coe hCc (seedQuadClock_zero _) hc hClb s ω).1,
      WithTop.coe_le_coe, not_le]
    exact lt_seedCapacityHorizon_iff hown hCc hCs hc hClb ω s
  rw [e, seedFilt_apply]
  exact (hS.measurableSet_stopping_time_le (isStoppingTime_invClock hCc hCm hmeas s)).compl

/-- **The capacity-time image driver is adapted to the capacity-time filtration** (own-time progressive driver read
at the inverse clock). -/
theorem measurable_seedCapacityDriver
    (hWp : IsStronglyProgressive 𝓕 fun u ω => (d ω).A 0 ((min u (S ω) : ℝ≥0) : ℝ) - (d ω).A 0 0) (u : ℝ≥0) :
    Measurable[seedFilt 𝓕 d S hCc hCm hmeas u] (seedCapacityDriver d S u) :=
  A1Frozen.measurable_timeChangeFilt_of_progressive hCc hCm hmeas hWp u

/-- **The capacity-time image forces are adapted to the capacity-time filtration.** -/
theorem measurable_seedCapacityForce (i : Fin (n + 1))
    (hVp : IsStronglyProgressive 𝓕 fun u ω => (d ω).imageForce ((min u (S ω) : ℝ≥0) : ℝ) i - (d ω).A 0 0)
    (u : ℝ≥0) :
    Measurable[seedFilt 𝓕 d S hCc hCm hmeas u] (seedCapacityForce d S i u) :=
  A1Frozen.measurable_timeChangeFilt_of_progressive hCc hCm hmeas hVp u

include hown hCs hc hClb in
/-- **A further cap before the horizon**: if `cap` is the image capacity `a(T')` at an own-time stopping time `T'`
whenever `T' ≤ S` (and is beyond the capacity horizon when `S ≤ T'`), then `{cap ≤ r} ∩ {s < a(S)} ∈ 𝓗_s` for `r ≤ s`
— before the horizon, `{cap ≤ r} = {T' ≤ τ_r}`. -/
theorem measurableSet_cap_le_inter (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) {T' : Ω → ℝ≥0}
    (hT' : IsStoppingTime 𝓕 fun ω => (T' ω : WithTop ℝ≥0)) {cap : Ω → ℝ≥0}
    (hcap₁ : ∀ ω, T' ω ≤ S ω → (cap ω : ℝ) = (d ω).a (T' ω))
    (hcap₂ : ∀ ω, S ω ≤ T' ω → seedCapacityHorizon d S ω ≤ cap ω) {r s : ℝ≥0} (hrs : r ≤ s) :
    MeasurableSet[seedFilt 𝓕 d S hCc hCm hmeas s]
      ({ω | cap ω ≤ r} ∩ {ω | s < seedCapacityHorizon d S ω}) := by
  have e : {ω | cap ω ≤ r} ∩ {ω | s < seedCapacityHorizon d S ω} =
      {ω | (T' ω : WithTop ℝ≥0) ≤ invClock (seedQuadClock (seedCapacityCoeff d S)) r ω} ∩
        {ω | s < seedCapacityHorizon d S ω} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    refine and_congr_left fun hs => ?_
    have hvr := invClock_eq_coe hCc (seedQuadClock_zero _) hc hClb r ω
    have hvs := invClock_eq_coe hCc (seedQuadClock_zero _) hc hClb s ω
    have hrsT : invClockT (seedQuadClock (seedCapacityCoeff d S)) r ω ≤
        invClockT (seedQuadClock (seedCapacityCoeff d S)) s ω := by
      have h := invClock_mono hCc hCm r s hrs ω
      rwa [hvr.1, hvs.1, WithTop.coe_le_coe] at h
    have hsS := (lt_seedCapacityHorizon_iff hown hCc hCs hc hClb ω s).1 hs
    have hCr : seedQuadClock (seedCapacityCoeff d S) ω (invClockT (seedQuadClock (seedCapacityCoeff d S)) r ω) = r :=
      hvr.2.1
    rw [hvr.1, WithTop.coe_le_coe]
    constructor
    · intro hcr
      rcases le_total (T' ω) (S ω) with hTS | hST
      · have h1 : seedQuadClock (seedCapacityCoeff d S) ω (T' ω) ≤
            seedQuadClock (seedCapacityCoeff d S) ω (invClockT (seedQuadClock (seedCapacityCoeff d S)) r ω) := by
          rw [hCr, seedCapacityCoeff_clock_eq hown ω hTS, ← hcap₁ ω hTS]
          exact_mod_cast hcr
        exact (hCs ω).le_iff_le.1 h1
      · exact absurd ((hcap₂ ω hST).trans (hcr.trans hrs)) (not_le.2 hs)
    · intro hT
      have hTS : T' ω ≤ S ω := (hT.trans hrsT).trans hsS.le
      have h1 := (hCs ω).monotone hT
      rw [hCr, seedCapacityCoeff_clock_eq hown ω hTS, ← hcap₁ ω hTS] at h1
      exact_mod_cast h1
  rw [e]
  refine MeasurableSet.inter ?_ (measurableSet_lt_seedCapacityHorizon hown hCc hCm hmeas hCs hc hClb hS s)
  have h := hT'.measurableSet_stopping_time_le (isStoppingTime_invClock hCc hCm hmeas r)
  exact (seedFilt 𝓕 d S hCc hCm hmeas).mono hrs _ h

end Gen

end Filt

/-! ### The frozen-sample law from the seeded line -/

section Noise

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The residual at `t` reads the image data on `[0, t]` only.** -/
theorem seedCapacityNoise_congr {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ}
    {t : ℝ≥0} (hw : ∀ u ≤ t, w' u = w u) (hvL : ∀ i, ∀ u ≤ t, vL' i u = vL i u)
    (hvR : ∀ j, ∀ u ≤ t, vR' j u = vR j u) :
    seedCapacityNoise κ ρL ρR w' vL' vR' t = seedCapacityNoise κ ρL ρR w vL vR t := by
  have hle : ∀ s ∈ uIcc (0 : ℝ) t, s.toNNReal ≤ t := fun s hs => by
    rw [uIcc_of_le t.coe_nonneg] at hs
    exact Real.toNNReal_le_iff_le_coe.2 hs.2
  have h1 : (∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w' s.toNNReal - vL' i s.toNNReal)) =
      ∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal) :=
    Finset.sum_congr rfl fun i _ => intervalIntegral.integral_congr fun s hs => by
      simp only [hw _ (hle s hs), hvL i _ (hle s hs)]
  have h2 : (∑ j, ∫ s in (0 : ℝ)..t, ρR j / (w' s.toNNReal - vR' j s.toNNReal)) =
      ∑ j, ∫ s in (0 : ℝ)..t, ρR j / (w s.toNNReal - vR j s.toNNReal) :=
    Finset.sum_congr rfl fun j _ => intervalIntegral.integral_congr fun s hs => by
      simp only [hw _ (hle s hs), hvR j _ (hle s hs)]
  unfold seedCapacityNoise
  rw [hw t le_rfl, h1, h2]

end Noise

section Sample

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {N : ℝ≥0 → Ω → ℝ} {Scap : ℕ → Ω → ℝ≥0} {m : ℕ}

/-- **The one-sample image law** (the content of `A1Frozen.IsFrozenSampleLaw` with the image data written as
functions of the image sample): under `Q`, a continuous Brownian motion `B` of a filtration `𝓗` agrees with the image
noise up to the cap `Scap m`, and `𝓗` sees the cap event and, before the cap, the generators of the image-data
filtration. -/
def IsSeedSampleLaw (Q : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (N : ℝ≥0 → Ω → ℝ) (Scap : ℕ → Ω → ℝ≥0) (m : ℕ) : Prop :=
  ∃ (𝓗 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ),
    IsFilteredBrownianReal 𝓗 B Q ∧ (∀ ω, Continuous (B · ω)) ∧
    (∀ s : ℝ≥0, MeasurableSet[𝓗 s] {ω | s < Scap m ω}) ∧
    (∀ s : ℝ≥0, ∀ g ∈ A1Frozen.imageGen W ζ VL VR N Scap s, MeasurableSet[𝓗 s] (g ∩ {ω | s < Scap m ω})) ∧
    ∀ᵐ ω ∂Q, ∀ t, t ≤ Scap m ω → B t ω = N t ω

omit mΩ in
/-- Agreement on an event transfers measurability of preimages intersected with it. -/
theorem measurableSet_preimage_inter_of_eqOn {𝓜 : Set (Set Ω)} {f g : Ω → ℝ} {E : Set Ω}
    (h : ∀ ω ∈ E, f ω = g ω) {U : Set ℝ} (hg : g ⁻¹' U ∩ E ∈ 𝓜) : f ⁻¹' U ∩ E ∈ 𝓜 := by
  convert hg using 1
  ext ω
  simp only [mem_inter_iff, mem_preimage]
  exact ⟨fun hω => ⟨h ω hω.2 ▸ hω.1, hω.2⟩, fun hω => ⟨(h ω hω.2).symm ▸ hω.1, hω.2⟩⟩

/-- **The one-sample image law from A22's seeded line**: A22's premises of
`exists_SeedCapacityBrownian_actual_coordinates` for seeded data `d` with own horizon `S` (an `𝓕`-stopping time), in
particular the named stochastic (D10) input `SeedOwnD10Integral`; progressive own-time image coordinates; image data
equal to the seeded capacity coordinates up to the cap `Scap m`, which is the capacity horizon `a(S)`, before the image
lifetime; the other caps `Scap k` the image capacities at own-time stopping times `T k` (beyond the horizon when
`S ≤ T k`). Then the one-sample law holds for the cap `m`, with the capacity-time filtration `seedFilt` and A22's
capacity Brownian motion. -/
theorem isSeedSampleLaw_of_seed {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ}
    {d : Ω → SeedData n} {S : Ω → ℝ≥0} {A : Ω → Set ℂ} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (e : Fin nL ⊕ Fin nR ≃ Fin (n + 1))
    (hB : IsFilteredBrownianReal 𝓕 B Q) (hBc : ∀ ω, Continuous (B · ω))
    (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hm : ∀ u, Measurable[𝓕 u] ({ω | u ≤ S ω}.indicator fun ω => (d ω).A 1 u - 1))
    (hcA : ∀ ω, ContinuousOn (fun u : ℝ≥0 => (d ω).A 1 u) (Ioc 0 (S ω)))
    {C a₀ : ℝ} (ha : 0 < a₀)
    (hb : ∀ ω u, 0 < u → u ≤ S ω → |(d ω).A 1 u| ≤ C)
    (hlb : ∀ ω u, 0 < u → u ≤ S ω → a₀ ≤ (d ω).A 1 u)
    (hκ : ∀ ω, (d ω).κ = κ)
    (hρL : ∀ ω i, (d ω).imageCharge (e (.inl i)) = ρL i)
    (hρR : ∀ ω j, (d ω).imageCharge (e (.inr j)) = ρR j)
    (h20 : ∀ ω, ContinuousOn (d ω).A20 (Icc 0 (S ω)))
    (hsep : ∀ ω t, t ∈ Icc (0 : ℝ) (S ω) → (d ω).A 0 t ≠ (d ω).A20 t)
    (hseed : ∀ ω, (d ω).ImageEntranceIntegrable (S ω))
    (hYm : ∀ u, Measurable[𝓕 u] (seedOwnMappedNoise κ d S B u))
    (hD10 : SeedOwnD10Integral Q 𝓕 B κ d S)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hWp : IsStronglyProgressive 𝓕 fun u ω => (d ω).A 0 ((min u (S ω) : ℝ≥0) : ℝ) - (d ω).A 0 0)
    (hVp : ∀ i, IsStronglyProgressive 𝓕 fun u ω => (d ω).imageForce ((min u (S ω) : ℝ≥0) : ℝ) i - (d ω).A 0 0)
    (hSm : ∀ ω, Scap m ω = seedCapacityHorizon d S ω)
    (hW : ∀ ω t, t ≤ Scap m ω → W t ω = seedCapacityDriver d S t ω)
    (hVL : ∀ ω i t, t ≤ Scap m ω → VL i t ω = seedCapacityForce d S (e (.inl i)) t ω)
    (hVR : ∀ ω j t, t ≤ Scap m ω → VR j t ω = seedCapacityForce d S (e (.inr j)) t ω)
    (hN : ∀ ω t, t ≤ Scap m ω → N t ω = seedCapacityNoise κ ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) t)
    (hζ : ∀ ω, (Scap m ω : ℝ≥0∞) ≤ ζ ω)
    (T : ℕ → Ω → ℝ≥0) (hT : ∀ k, IsStoppingTime 𝓕 fun ω => (T k ω : WithTop ℝ≥0))
    (hcap₁ : ∀ k ω, T k ω ≤ S ω → (Scap k ω : ℝ) = (d ω).a (T k ω))
    (hcap₂ : ∀ k ω, S ω ≤ T k ω → Scap m ω ≤ Scap k ω) :
    IsSeedSampleLaw Q W ζ VL VR N Scap m := by
  obtain ⟨hCc, hCs, hmeas, c, hc, hClb⟩ := clock_props hm hcA ha hb hlb
  have hCm : ∀ ω, Monotone (seedQuadClock (seedCapacityCoeff d S) ω) := fun ω => (hCs ω).monotone
  obtain ⟨hBh, hBhc⟩ := seedCapacityBrownian_seedFilt (ρL := ρL) (ρR := ρR) e hB hBc hown hm hcA ha hb hlb hκ hρL
    hρR h20 hsep hseed hYm hD10 hCc hCm hmeas
  set 𝓗 := seedFilt 𝓕 d S hCc hCm hmeas with h𝓗
  have hagree : ∀ ω t, t ≤ Scap m ω → seedBh κ d S B t ω = seedCapacityNoise κ ρL ρR
      (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) t := by
    intro ω t ht
    rw [hBh.2 ω t (hSm ω ▸ ht)]
    exact (seedCapacityNoise_congr (fun u hu => hW ω u (hu.trans ht))
      (fun i u hu => hVL ω i u (hu.trans ht)) (fun j u hu => hVR ω j u (hu.trans ht))).symm
  have hE : ∀ s : ℝ≥0, MeasurableSet[𝓗 s] {ω | s < Scap m ω} := fun s => by
    simp only [hSm]
    exact measurableSet_lt_seedCapacityHorizon hown hCc hCm hmeas hCs hc hClb hS s
  refine ⟨𝓗, seedBh κ d S B, hBh.1, hBhc, hE, fun s => ?_,
    ae_of_all _ fun ω t ht => by rw [hagree ω t ht, hN ω t ht]⟩
  have hlt : ∀ {r : ℝ≥0}, r ≤ s → ∀ ω ∈ {ω | s < Scap m ω}, r ≤ Scap m ω :=
    fun hr ω hω => hr.trans (le_of_lt hω)
  refine A1Frozen.forall_imageGen (p := fun g => MeasurableSet[𝓗 s] (g ∩ {ω | s < Scap m ω}))
    (fun r hr U hU => ?_) (fun r hr U hU i => ?_) (fun r hr U hU j => ?_)
    (fun r hr U hU => ?_) (fun r hr k => ?_) (fun r hr => ?_)
  · refine measurableSet_preimage_inter_of_eqOn (𝓜 := {E | MeasurableSet[𝓗 s] E})
      (g := seedCapacityDriver d S r) (fun ω hω => hW ω r (hlt hr ω hω)) ?_
    exact (𝓗.mono hr _ (measurable_seedCapacityDriver hCc hCm hmeas hWp r hU)).inter (hE s)
  · refine measurableSet_preimage_inter_of_eqOn (𝓜 := {E | MeasurableSet[𝓗 s] E})
      (g := seedCapacityForce d S (e (.inl i)) r) (fun ω hω => hVL ω i r (hlt hr ω hω)) ?_
    exact (𝓗.mono hr _ (measurable_seedCapacityForce hCc hCm hmeas _ (hVp _) r hU)).inter (hE s)
  · refine measurableSet_preimage_inter_of_eqOn (𝓜 := {E | MeasurableSet[𝓗 s] E})
      (g := seedCapacityForce d S (e (.inr j)) r) (fun ω hω => hVR ω j r (hlt hr ω hω)) ?_
    exact (𝓗.mono hr _ (measurable_seedCapacityForce hCc hCm hmeas _ (hVp _) r hU)).inter (hE s)
  · refine measurableSet_preimage_inter_of_eqOn (𝓜 := {E | MeasurableSet[𝓗 s] E})
      (g := seedBh κ d S B r) (fun ω hω => by rw [hN ω r (hlt hr ω hω), hagree ω r (hlt hr ω hω)]) ?_
    exact (𝓗.mono hr _ (hBh.1.2.1 r hU)).inter (hE s)
  · have h := measurableSet_cap_le_inter hown hCc hCm hmeas hCs hc hClb hS (hT k) (cap := Scap k)
      (hcap₁ k) (fun ω hω => (hSm ω) ▸ hcap₂ k ω hω) hr
    simp only [← hSm] at h
    exact h
  · have e : {ω | (r : ℝ≥0∞) < ζ ω} ∩ {ω | s < Scap m ω} = {ω | s < Scap m ω} := by
      refine inter_eq_right.2 fun ω hω => ?_
      exact lt_of_lt_of_le (by exact_mod_cast hr.trans_lt hω) (hζ ω)
    rw [e]
    exact hE s

end Sample

/-! ### Sections: the frozen-sample laws -/

section Sections

variable {Z Z' : Type*} {nL nR : ℕ} {W : ℝ≥0 → Z → ℝ} {ζ : Z → ℝ≥0∞} {VL : Fin nL → ℝ≥0 → Z → ℝ}
  {VR : Fin nR → ℝ≥0 → Z → ℝ} {N : ℝ≥0 → Z → ℝ} {Scap : ℕ → Z → ℝ≥0}

/-- **The preimage of a generator of the image-data filtration is a generator for the pulled-back data.** -/
theorem preimage_mem_imageGen (ι : Z' → Z) {s : ℝ≥0} {g : Set Z}
    (hg : g ∈ A1Frozen.imageGen W ζ VL VR N Scap s) :
    ι ⁻¹' g ∈ A1Frozen.imageGen (fun t => W t ∘ ι) (ζ ∘ ι) (fun i t => VL i t ∘ ι) (fun j t => VR j t ∘ ι)
      (fun t => N t ∘ ι) (fun k => Scap k ∘ ι) s := by
  rcases hg with ⟨r, hr, ⟨U, hU, rfl | ⟨i, rfl⟩ | ⟨j, rfl⟩ | rfl⟩ | ⟨k, rfl⟩ | rfl⟩
  exacts [⟨r, hr, Or.inl ⟨U, hU, Or.inl rfl⟩⟩, ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inl ⟨i, rfl⟩)⟩⟩,
    ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))⟩⟩,
    ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inr (Or.inr rfl))⟩⟩, ⟨r, hr, Or.inr (Or.inl ⟨k, rfl⟩)⟩,
    ⟨r, hr, Or.inr (Or.inr rfl)⟩]

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

omit mY in
/-- **The frozen-sample law at `y` is the one-sample law of the sections at `y`.** -/
theorem IsSeedSampleLaw.isFrozenSampleLaw {W : ℝ≥0 → X × Y → ℝ} {ζ : X × Y → ℝ≥0∞}
    {VL : Fin nL → ℝ≥0 → X × Y → ℝ} {VR : Fin nR → ℝ≥0 → X × Y → ℝ} {N : ℝ≥0 → X × Y → ℝ}
    {Scap : ℕ → X × Y → ℝ≥0} {Q : Measure X} {m : ℕ} {y : Y}
    (h : IsSeedSampleLaw Q (fun t x => W t (x, y)) (fun x => ζ (x, y)) (fun i t x => VL i t (x, y))
      (fun j t x => VR j t (x, y)) (fun t x => N t (x, y)) (fun k x => Scap k (x, y)) m) :
    A1Frozen.IsFrozenSampleLaw Q W ζ VL VR N Scap m y := by
  obtain ⟨𝓗, B, hB, hBc, hC, hG, heq⟩ := h
  exact ⟨𝓗, B, hB, hBc, hC, fun s g hg => hG s _ (preimage_mem_imageGen (fun x => (x, y)) hg), heq⟩

omit mX in
/-- **The frozen-sample law at `x` (mirror) is the one-sample law of the sections at `x`.** -/
theorem IsSeedSampleLaw.isFrozenSampleLawFst {W : ℝ≥0 → X × Y → ℝ} {ζ : X × Y → ℝ≥0∞}
    {VL : Fin nL → ℝ≥0 → X × Y → ℝ} {VR : Fin nR → ℝ≥0 → X × Y → ℝ} {N : ℝ≥0 → X × Y → ℝ}
    {Scap : ℕ → X × Y → ℝ≥0} {Q : Measure Y} {m : ℕ} {x : X}
    (h : IsSeedSampleLaw Q (fun t y => W t (x, y)) (fun y => ζ (x, y)) (fun i t y => VL i t (x, y))
      (fun j t y => VR j t (x, y)) (fun t y => N t (x, y)) (fun k y => Scap k (x, y)) m) :
    A1Frozen.IsFrozenSampleLawFst Q W ζ VL VR N Scap m x := by
  obtain ⟨𝓗, B, hB, hBc, hC, hG, heq⟩ := h
  exact ⟨𝓗, B, hB, hBc, hC, fun s g hg => hG s _ (preimage_mem_imageGen (fun y => (x, y)) hg), heq⟩

end Sections

end InteractingSLE.ZhanGT4.A1Family
