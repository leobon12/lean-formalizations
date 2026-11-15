/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12Loc
import InteractingSLE.Spec.Sec2.AddMarksPath
import BrownianMotion.StochasticIntegral.DoobLp

/-!
# Lemma G12: the exponential maximal inequality for the mark observable

Packet PROVE-G12. Along an integrated `SLE_κ(ρ)` evolution of any force word and a right mark `j₀` with
`x_{j₀} > 0`, the mark observable `Φ` (`G12Obs.lean`) and its clock `T` satisfy, for every `λ` and `c`,

  `P(∃ t ≤ σ_n : λ(Φ_t − Φ_0) − (λ²κ/2) T_t ≥ c) ≤ e^{−c}`

(`measureReal_crossG_le`), uniformly in the localization level `n`. The proof: the exponential observable
`Z_λ = exp(λΦ − λ²κT/2)` stopped at `σ_n` is a nonnegative martingale (`martingale_expProc`: localized Itô formula of
`G12Loc.lean` and the vanishing generator `itoGen_g12ExpObs_dens` off the Lebesgue-null collisions), and Doob's maximal
inequality (vendored `ProbabilityTheory.maximal_ineq`) bounds the probability that it exceeds `Z_0 e^c` by `e^{−c}`.
This replaces the unbounded-clock and strip-Brownian-motion steps of PROVE-G11-G4 (`G11Clock*`, `G11Strip`): no time
change is needed.

* `eq_of_forceEq_right`: marks of one group coincide pathwise;
* `ae_not_collisionG`: off a Lebesgue-null set no mark meets the driver;
* `martingale_expProc`, `measureReal_crossG_le`, `locG_mono`, `measure_iUnion_crossG_le`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

namespace G12

open Supp8.GB5 (IsGBGood isFilteredBrownianReal_brownG_gb continuous_brownG_gb isStoppingTime_hit_gb
  measurableSet_good_usual' nonneg_of_le_hitBelow abs_le_norm_state hitBelow_mono_fun')

variable {nL nR : ℕ}

/-! ### Pathwise facts -/

section Path

variable {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **Marks of one group coincide**: two right marks started at the same point are equal before `ζ`. -/
theorem eq_of_forceEq_right (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {j k : Fin nR} (hjk : xR j = xR k)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : vR j t = vR k t := by
  have key : ∀ j k : Fin nR, xR j = xR k → vR j t ≤ vR k t := fun j k hjk =>
    Sec2.le_of_forceEq_right (τ := ζ) (w := w) (u := vR k) (v := vR j) (x := xR j) (y := xR k) hjk.le
      (h.continuousOn_vR k) (h.continuousOn_vR j) (fun ht => h.vR_eq ht k) (fun ht => h.vR_eq ht j)
      (fun ht => h.intervalIntegrable_forceR ht k) (fun ht => h.intervalIntegrable_forceR ht j)
      (fun ht => h.w_le_vR ht k) (h.volume_collisionR k) ht
  exact le_antisymm (key j k hjk) (key k j hjk.symm)

/-- Off a Lebesgue-null set of times no mark meets the driver. -/
theorem ae_not_collisionG (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    ∀ᵐ s ∂volume, s ∈ Ioc 0 (t : ℝ) →
      (∀ i, vL i s.toNNReal ≠ w s.toNNReal) ∧ ∀ j, vR j s.toNNReal ≠ w s.toNNReal := by
  have hL : ∀ i, ∀ᵐ s ∂volume, s ∉ {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧
      w s.toNNReal = vL i s.toNNReal} := fun i => by
    rw [ae_iff]; simpa using h.volume_collisionL i
  have hR : ∀ j, ∀ᵐ s ∂volume, s ∉ {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧
      w s.toNNReal = vR j s.toNNReal} := fun j => by
    rw [ae_iff]; simpa using h.volume_collisionR j
  filter_upwards [ae_all_iff.2 hL, ae_all_iff.2 hR] with s hsL hsR hs
  have hsζ : (s.toNNReal : ℝ≥0∞) < ζ := Sec2.toNNReal_lt_of_mem_Icc ht ⟨hs.1.le, hs.2⟩
  exact ⟨fun i heq => hsL i ⟨hs.1.le, hsζ, heq.symm⟩, fun j heq => hsR j ⟨hs.1.le, hsζ, heq.symm⟩⟩

end Path

/-! ### The exponential martingale and the maximal inequality -/

section Max

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {j₀ : Fin nR}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0}

/-- The exponential observable `Z_λ` along the coordinates stopped at `σ_n`. -/
def expProc (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (j₀ : Fin nR)
    (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (T : ℕ → Ω → ℝ≥0) (lam : ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  g12ExpObs κ xL xR ρL ρR j₀ lam (coordG xL xR G W VL VR j₀ (min t (locG xR j₀ G W VL VR B ζ T n ω)) ω,
    Sec2.TwoSeed.brownG G B (min t (locG xR j₀ G W VL VR B ζ T n ω)) ω)

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0))
  (hTn : ∀ n ω, T n ω ≤ n) (hy : 0 < xR j₀) (hxL : ∀ i, xL i ≤ 0)

include hgood hTn hy hxL in
/-- The drift integral of `Z_λ` vanishes up to `σ_n`. -/
theorem integral_itoGen_expObs_eq_zero (hκ : 0 ≤ κ) (lam : ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    ∫ s in (0 : ℝ)..(min t (locG xR j₀ G W VL VR B ζ T n ω) : ℝ≥0),
      Ito.itoGen (g12ExpObs κ xL xR ρL ρR j₀ lam) (coordG xL xR G W VL VR j₀ s.toNNReal ω,
        Sec2.TwoSeed.brownG G B s.toNNReal ω) (densG G W VL VR j₀ s ω) = 0 := by
  by_cases hωG : ω ∈ G
  swap
  · rw [locG_of_not_mem hωG, min_eq_right (zero_le (a := t)), NNReal.coe_zero, intervalIntegral.integral_same]
  have hω := hgood ω hωG
  have hF := hω.1.isForcePath
  have hmin : (min t (locG xR j₀ G W VL VR B ζ T n ω) : ℝ≥0) ≤ locG xR j₀ G W VL VR B ζ T n ω :=
    min_le_right _ _
  have hlt : ((min t (locG xR j₀ G W VL VR B ζ T n ω) : ℝ≥0) : ℝ≥0∞) < ζ ω :=
    lt_of_le_of_lt (by exact_mod_cast hmin) (locG_lt_lifetime hω)
  refine intervalIntegral.integral_zero_ae ?_
  filter_upwards [ae_not_collisionG hF hlt] with s hs hsI
  rw [uIoc_of_le (NNReal.coe_nonneg _)] at hsI
  obtain ⟨hL, hR⟩ := hs hsI
  have hsσ : s.toNNReal ≤ locG xR j₀ G W VL VR B ζ T n ω :=
    (Sec2.toNNReal_le_of_mem_Icc ⟨hsI.1.le, hsI.2⟩).trans hmin
  have hsζ : (s.toNNReal : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hsσ) (locG_lt_lifetime hω)
  have hK := mem_kcG_of_le_locG (κ := κ) (ρL := ρL) (ρR := ρR) hgood hTn hy hsσ
  have hreg := kcG_subset_region κ xL xR ρL ρR j₀ hxL hy n hK
  simp only [coordG, densG, Sec2.TwoSeed.brownG, hωG, ↓reduceIte] at hreg ⊢
  exact itoGen_g12ExpObs_dens κ xL xR ρL ρR j₀ hκ lam (w_eq_gDriftLin hω.1 hsζ) hreg hL
    (fun j _ => hR j) fun j hj => eq_of_forceEq_right hF (by simpa [onY] using hj) hsζ

include hE hGm hGc hgood hT hTn hy hxL in
/-- **`Z_λ` stopped at `σ_n` is a martingale.** -/
theorem martingale_expProc (hκ : 0 ≤ κ) (lam : ℝ) (n : ℕ) :
    Martingale (expProc κ xL xR ρL ρR j₀ G W VL VR B ζ T lam n) (usualAugmentation 𝓕 P) P := by
  have h := martingale_locG hE hGm hGc hgood hT hTn hy hxL
    ((contDiffOn_g12ExpObs κ xL xR ρL ρR j₀ lam (n := 3))) n
  have e : (fun t ω => g12ExpObs κ xL xR ρL ρR j₀ lam
        (coordG xL xR G W VL VR j₀ (min t (locG xR j₀ G W VL VR B ζ T n ω)) ω,
          Sec2.TwoSeed.brownG G B (min t (locG xR j₀ G W VL VR B ζ T n ω)) ω) -
      ∫ s in (0 : ℝ)..(min t (locG xR j₀ G W VL VR B ζ T n ω) : ℝ≥0),
        Ito.itoGen (g12ExpObs κ xL xR ρL ρR j₀ lam) (coordG xL xR G W VL VR j₀ s.toNNReal ω,
          Sec2.TwoSeed.brownG G B s.toNNReal ω) (densG G W VL VR j₀ s ω)) =
      expProc κ xL xR ρL ρR j₀ G W VL VR B ζ T lam n := by
    funext t ω
    rw [integral_itoGen_expObs_eq_zero hgood hTn hy hxL hκ lam n t ω, sub_zero]
    rfl
  rwa [e] at h

/-- The value `Φ_0` of the mark observable at the initial point. -/
def phi0 (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (j₀ : Fin nR) : ℝ :=
  g12Obs κ xL xR ρL ρR j₀ (initG xL xR)

/-- **The crossing event** at level `n`: `λ(Φ_t − Φ_0) − (λ²κ/2) T_t ≥ c` for some `t ≤ σ_n`. -/
def crossG (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (j₀ : Fin nR)
    (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (T : ℕ → Ω → ℝ≥0) (lam c : ℝ) (n : ℕ) : Set Ω :=
  {ω | ω ∈ G ∧ ∃ t : ℝ≥0, t ≤ locG xR j₀ G W VL VR B ζ T n ω ∧
    c ≤ lam * (g12Obs κ xL xR ρL ρR j₀ (coordG xL xR G W VL VR j₀ t ω, Sec2.TwoSeed.brownG G B t ω) -
      phi0 κ xL xR ρL ρR j₀) - lam ^ 2 * κ / 2 * (coordG xL xR G W VL VR j₀ t ω).2.2}

include hgood hTn hy hxL in
/-- The stopped exponential process is continuous in time. -/
theorem continuous_expProc (lam : ℝ) (n : ℕ) (ω : Ω) :
    Continuous fun t => expProc κ xL xR ρL ρR j₀ G W VL VR B ζ T lam n t ω := by
  set σ := locG xR j₀ G W VL VR B ζ T n ω with hσ
  have hpath : ContinuousOn (fun t => (coordG xL xR G W VL VR j₀ t ω, Sec2.TwoSeed.brownG G B t ω)) (Iic σ) := by
    by_cases hωG : ω ∈ G
    · have hω := hgood ω hωG
      have hF := hω.1.isForcePath
      have hlife := isMarkLife_locG hω hωG hy (n := n)
      have hsub : Iic σ ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs => (isMarkLife_mono hlife hs).1
      have hTc : ContinuousOn (fun s : ℝ≥0 => clockAt (W · ω) (VR j₀ · ω) s) (Iic σ) := by
        have hc := intervalIntegral.continuousOn_primitive_interval'
          (intervalIntegrable_clockRate hF hlife) (left_mem_uIcc (a := (0 : ℝ)) (b := σ))
        refine hc.comp NNReal.continuous_coe.continuousOn fun s hs => ?_
        rw [uIcc_of_le σ.coe_nonneg]
        exact ⟨s.coe_nonneg, by exact_mod_cast hs⟩
      simp only [coordG, Sec2.TwoSeed.brownG, hωG, ↓reduceIte]
      exact ((continuousOn_pi.2 fun i => (hF.continuousOn_vL i).mono hsub).prodMk
        ((continuousOn_pi.2 fun j => (hF.continuousOn_vR j).mono hsub).prodMk hTc)).prodMk
        hω.2.1.continuousOn
    · simp only [coordG, Sec2.TwoSeed.brownG, hωG, ↓reduceIte]; exact continuousOn_const
  have hreg : MapsTo (fun t => (coordG xL xR G W VL VR j₀ t ω, Sec2.TwoSeed.brownG G B t ω)) (Iic σ)
      (g12Region κ xL xR ρL ρR j₀) := fun t ht =>
    kcG_subset_region κ xL xR ρL ρR j₀ hxL hy n (mem_kcG_of_le_locG hgood hTn hy ht)
  have hc := ((contDiffOn_g12ExpObs κ xL xR ρL ρR j₀ lam (n := 0)).continuousOn.comp hpath hreg).comp_continuous
    (continuous_id.min continuous_const) (fun t => mem_Iic.2 (min_le_right t σ))
  exact hc

include hE hGm hGc hgood hT hTn hy hxL in
/-- **The crossing inequality**: `P(∃ t ≤ σ_n, λ(Φ_t − Φ_0) − (λ²κ/2) T_t ≥ c) ≤ e^{−c}`. -/
theorem measureReal_crossG_le [IsProbabilityMeasure P] (hκ : 0 ≤ κ) (lam c : ℝ) (n : ℕ) :
    P.real (crossG κ xL xR ρL ρR j₀ G W VL VR B ζ T lam c n) ≤ Real.exp (-c) := by
  set Y := expProc κ xL xR ρL ρR j₀ G W VL VR B ζ T lam n with hYdef
  have hY := martingale_expProc hE hGm hGc hgood hT hTn hy hxL hκ lam n
  set Φ0 := phi0 κ xL xR ρL ρR j₀ with hΦ0
  set ε := Real.exp (lam * Φ0 + c) with hε
  have hεpos : 0 < ε := Real.exp_pos _
  have hY0 : ∀ ω, Y 0 ω = Real.exp (lam * Φ0) := by
    intro ω
    have hc0 : coordG xL xR G W VL VR j₀ 0 ω = (xL, xR, 0) := by
      by_cases hωG : ω ∈ G
      · have hF := (hgood ω hωG).1.isForcePath
        simp only [coordG, hωG, ↓reduceIte, coordAtG, clockAt, NNReal.coe_zero,
          intervalIntegral.integral_same]
        rw [funext hF.vL_zero, funext hF.vR_zero]
      · simp only [coordG, hωG, ↓reduceIte]
    have hb0 : Sec2.TwoSeed.brownG G B 0 ω = 0 := by
      by_cases hωG : ω ∈ G
      · simp only [Sec2.TwoSeed.brownG, hωG, ↓reduceIte]; exact (hgood ω hωG).2.2.1
      · simp only [Sec2.TwoSeed.brownG, hωG, ↓reduceIte]
    simp only [hYdef, expProc, zero_min, hc0, hb0, g12ExpObs, hΦ0, phi0, initG, mul_zero, add_zero]
  have hnonneg : 0 ≤ Y := fun t ω => Real.exp_nonneg _
  have hRC : ∀ ω, IsRightContinuous fun t => Y t ω := fun ω =>
    (continuous_expProc hgood hTn hy hxL lam n ω).isRightContinuous
  have hdoob := ProbabilityTheory.maximal_ineq hY.submartingale hnonneg ε (n : ℝ≥0) hRC
  set S := {ω | ε ≤ ⨆ i : Set.Iic (n : ℝ≥0), Y i ω} with hS
  have hint : ∫ ω in S, Y n ω ∂P ≤ Real.exp (lam * Φ0) := by
    have h1 : ∫ ω in S, Y n ω ∂P ≤ ∫ ω, Y n ω ∂P :=
      setIntegral_le_integral (hY.integrable n) (Eventually.of_forall fun ω => hnonneg n ω)
    have h2 : ∫ ω, Y n ω ∂P = ∫ ω, Y 0 ω ∂P := by
      have := hY.setIntegral_eq (zero_le (a := (n : ℝ≥0))) (s := univ) MeasurableSet.univ
      simpa only [setIntegral_univ] using this.symm
    rw [h2] at h1
    simpa only [hY0, integral_const, probReal_univ, smul_eq_mul, one_mul] using h1
  have hPS : P.real S ≤ Real.exp (-c) := by
    have h3 : ε * P.real S ≤ Real.exp (lam * Φ0) := hdoob.trans hint
    rw [← le_div_iff₀' hεpos] at h3
    refine h3.trans (le_of_eq ?_)
    rw [hε, ← Real.exp_sub]
    ring_nf
  refine (measureReal_mono (fun ω hω => ?_)).trans hPS
  obtain ⟨hωG, t, htσ, hcross⟩ := hω
  have htn : t ≤ (n : ℝ≥0) := htσ.trans ((locG_le_T ω).trans (hTn n ω))
  have hYt : ε ≤ Y t ω := by
    simp only [hYdef, expProc, min_eq_left htσ, g12ExpObs, hε]
    refine Real.exp_le_exp.2 ?_
    nlinarith [hcross]
  have hbdd : BddAbove (Set.range fun i : Set.Iic (n : ℝ≥0) => Y i ω) := by
    obtain ⟨M, hM⟩ := ((isCompact_Icc (a := (0 : ℝ≥0)) (b := (n : ℝ≥0))).image
      (continuous_expProc hgood hTn hy hxL lam n ω)).isBounded.bddAbove
    exact ⟨M, by rintro _ ⟨i, rfl⟩; exact hM ⟨i, ⟨zero_le, i.2⟩, rfl⟩⟩
  exact hYt.trans (le_ciSup hbdd ⟨t, htn⟩)

end Max

/-! ### Monotonicity in the level and the almost sure bound -/

section Mono

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {j₀ : Fin nR}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0}

theorem dlt_anti {n m : ℕ} (h : n ≤ m) : dlt m ≤ dlt n := by
  unfold dlt
  have : (n : ℝ) ≤ m := by exact_mod_cast h
  gcongr

theorem levG_mono (xR : Fin nR → ℝ) (j₀ : Fin nR) {n m : ℕ} (h : n ≤ m)
    (st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : levG xR j₀ n st ≤ levG xR j₀ m st := by
  have hd := dlt_anti h
  have hnm : (n : ℝ) ≤ m := by exact_mod_cast h
  unfold levG
  refine min_le_min (min_le_min (by linarith) (by linarith)) (neg_le_neg (add_le_add ?_ ?_))
  · exact sum_le_sum fun i _ => max_le_max le_rfl (by linarith)
  · exact sum_le_sum fun j _ => max_le_max le_rfl (by linarith)

theorem exitTime_mono (hBc : ∀ ω, Continuous (B · ω)) {n m : ℕ} (h : n ≤ m) (ω : Ω) :
    MathFin.exitTime B n ω ≤ MathFin.exitTime B m ω := by
  induction h' : MathFin.exitTime B m ω using WithTop.recTopCoe with
  | top => exact le_top
  | coe i =>
    have hi := h'
    obtain ⟨s, hs, hsB⟩ := (MathFin.exitTime_le_iff hBc m i ω).1 (le_of_eq hi)
    refine (MathFin.exitTime_le_iff hBc n i ω).2 ⟨s, hs, le_trans ?_ hsB⟩
    exact_mod_cast h

theorem locG_mono (hTm : ∀ ω, Monotone fun n => T n ω) (hBc : ∀ ω, Continuous (Sec2.TwoSeed.brownG G B · ω))
    {n m : ℕ} (h : n ≤ m) (ω : Ω) : locG xR j₀ G W VL VR B ζ T n ω ≤ locG xR j₀ G W VL VR B ζ T m ω := by
  have e : ∀ k, (locG xR j₀ G W VL VR B ζ T k ω : WithTop ℝ≥0) = min (T k ω : WithTop ℝ≥0)
      (min (hitG xR j₀ G W VL VR ζ k ω) (MathFin.exitTime (Sec2.TwoSeed.brownG G B) k ω)) := fun k =>
    Sec2.TwoSeed.coe_capTime _ _ ω
  have hh : hitG xR j₀ G W VL VR ζ n ω ≤ hitG xR j₀ G W VL VR ζ m ω := by
    by_cases hωG : ω ∈ G
    · simp only [hitG, hωG, ↓reduceIte]
      exact hitBelow_mono_fun' fun s => levG_mono xR j₀ h _
    · simp only [hitG, hωG, ↓reduceIte, le_refl]
  have hc : (locG xR j₀ G W VL VR B ζ T n ω : WithTop ℝ≥0) ≤ locG xR j₀ G W VL VR B ζ T m ω := by
    rw [e n, e m]
    exact min_le_min (by exact_mod_cast hTm ω h) (min_le_min hh (exitTime_mono hBc h ω))
  exact_mod_cast hc

theorem crossG_mono (hTm : ∀ ω, Monotone fun n => T n ω)
    (hBc : ∀ ω, Continuous (Sec2.TwoSeed.brownG G B · ω)) (lam c : ℝ) :
    Monotone (crossG κ xL xR ρL ρR j₀ G W VL VR B ζ T lam c) := by
  intro n m h ω ⟨hωG, t, ht, hc⟩
  exact ⟨hωG, t, ht.trans (locG_mono hTm hBc h ω), hc⟩

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0))
  (hTm : ∀ ω, Monotone fun n => T n ω) (hTn : ∀ n ω, T n ω ≤ n) (hy : 0 < xR j₀) (hxL : ∀ i, xL i ≤ 0)

include hE hGm hGc hgood hT hTm hTn hy hxL in
/-- The crossing at some level has probability at most `e^{−c}`. -/
theorem measure_iUnion_crossG_le [IsProbabilityMeasure P] (hκ : 0 ≤ κ) (lam c : ℝ) :
    P (⋃ n, crossG κ xL xR ρL ρR j₀ G W VL VR B ζ T lam c n) ≤ ENNReal.ofReal (Real.exp (-c)) := by
  rw [Monotone.measure_iUnion (crossG_mono hTm (continuous_brownG_gb hgood) lam c)]
  refine iSup_le fun n => ?_
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (measureReal_crossG_le hE hGm hGc hgood hT hTn hy hxL hκ lam c n)

include hE hGm hGc hgood hT hTm hTn hy hxL in
/-- **The almost sure linear bound on the mark observable**: for `α > 0`, almost surely on the good event there is
`a ∈ ℕ` with `|Φ_t − Φ_0| < a + α T_t` for every `t ≤ σ_n` and every `n`. -/
theorem ae_abs_phi_lt [IsProbabilityMeasure P] (hκ : 0 < κ) {α : ℝ} (hα : 0 < α) :
    ∀ᵐ ω ∂P, ω ∈ G → ∃ a : ℕ, ∀ n : ℕ, ∀ t : ℝ≥0, t ≤ locG xR j₀ G W VL VR B ζ T n ω →
      |g12Obs κ xL xR ρL ρR j₀ (coordG xL xR G W VL VR j₀ t ω, Sec2.TwoSeed.brownG G B t ω) -
        phi0 κ xL xR ρL ρR j₀| < a + α * (coordG xL xR G W VL VR j₀ t ω).2.2 := by
  set lam := 2 * α / κ with hlam
  have hlpos : 0 < lam := by positivity
  set S : ℕ → Set Ω := fun a => (⋃ n, crossG κ xL xR ρL ρR j₀ G W VL VR B ζ T lam (lam * a) n) ∪
    ⋃ n, crossG κ xL xR ρL ρR j₀ G W VL VR B ζ T (-lam) (lam * a) n with hS
  have hSle : ∀ a : ℕ, P (S a) ≤ ENNReal.ofReal (2 * Real.exp (-(lam * a))) := by
    intro a
    refine (measure_union_le _ _).trans ?_
    rw [two_mul, ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
    exact add_le_add (measure_iUnion_crossG_le hE hGm hGc hgood hT hTm hTn hy hxL hκ.le lam _)
      (measure_iUnion_crossG_le hE hGm hGc hgood hT hTm hTn hy hxL hκ.le (-lam) _)
  have hnull : P (⋂ a : ℕ, S a) = 0 := by
    have hlim : Tendsto (fun a : ℕ => ENNReal.ofReal (2 * Real.exp (-(lam * a)))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal ?_
      have h1 : Tendsto (fun a : ℕ => lam * (a : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.const_mul_atTop hlpos
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul 2
      simpa using h2
    exact le_antisymm (ge_of_tendsto' hlim fun a =>
      (measure_mono (iInter_subset (fun a : ℕ => S a) a)).trans (hSle a)) bot_le
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω hωG
  rw [mem_iInter, not_forall] at hω
  obtain ⟨a, ha⟩ := hω
  refine ⟨a, fun n t ht => ?_⟩
  simp only [hS, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at ha
  set d := g12Obs κ xL xR ρL ρR j₀ (coordG xL xR G W VL VR j₀ t ω, Sec2.TwoSeed.brownG G B t ω) -
    phi0 κ xL xR ρL ρR j₀ with hd
  set Tt := (coordG xL xR G W VL VR j₀ t ω).2.2 with hTt
  have hk : lam ^ 2 * κ / 2 = lam * α := by rw [hlam]; field_simp
  have h1 : ¬ (lam * a ≤ lam * d - lam ^ 2 * κ / 2 * Tt) := fun hc => ha.1 n ⟨hωG, t, ht, hc⟩
  have h2 : ¬ (lam * a ≤ -lam * d - (-lam) ^ 2 * κ / 2 * Tt) := fun hc => ha.2 n ⟨hωG, t, ht, hc⟩
  rw [hk, not_le] at h1
  rw [neg_sq, hk, not_le] at h2
  rw [abs_lt]
  constructor
  · nlinarith
  · nlinarith

end Mono

end G12

end Supp7

end InteractingSLE
