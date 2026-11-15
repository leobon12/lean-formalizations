/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownianGood
import InteractingSLE.Spec.Zhan.StripTimeMart

/-!
# `b̃` is a Brownian motion, part 3: the localized martingales in the original time

Packet PROVE-SEC7-C9. On the good event the retargeting coordinates `Λ = (V^L, V^R, α, β, S)` (`rCoord`, the
initial point off the good event) stopped at `σ_n` are adapted to the usual augmentation: `α, β, S` are running
integrals of continuous functions of the stopped gap `V_k − W` (`measurable_rCoord_stopped`). The localized Itô
formula (`Ito.martingale_itoLocalized`) on the compact `rKc` then makes every observable `F` with vanishing drift
(off collisions) a martingale when stopped at `σ_n` (`martingale_rObs_stopped`). The three observables used are

* `Ψ` (`obs`, PROVE-SEC7-C8: drift `0`),
* `(Ψ − c)² − κ S` (`obs2`: drift `(∂_b Ψ)² − κ S' = 0`),
* `Z_a = exp(aΨ/√κ − a²S/2)` (`expObs`, PROVE-SEC7-C8: drift `0`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

namespace Retarget

/-! ### Running integrals of two progressive processes -/

section Integral₂

theorem stronglyMeasurable_integral_comp₂_aux {Ω : Type*} [MeasurableSpace Ω] (t : ℝ≥0) {f₁ f₂ : ℝ≥0 → Ω → ℝ}
    (hf₁ : StronglyMeasurable fun p : Set.Iic t × Ω => f₁ p.1 p.2)
    (hf₂ : StronglyMeasurable fun p : Set.Iic t × Ω => f₂ p.1 p.2) {g : ℝ × ℝ → ℝ} (hg : Measurable g) :
    StronglyMeasurable fun ω => ∫ u in (0 : ℝ)..(t : ℝ), g (f₁ u.toNNReal ω, f₂ u.toNNReal ω) := by
  let φ : Ω × ℝ → Set.Iic t × Ω := fun p =>
    (⟨min p.2.toNNReal t, Set.mem_Iic.2 (min_le_right _ _)⟩, p.1)
  have hφ : Measurable φ :=
    (((measurable_real_toNNReal.min measurable_const).comp measurable_snd).subtype_mk).prodMk
      measurable_fst
  have hF : StronglyMeasurable fun p : Ω × ℝ =>
      g (f₁ (min p.2.toNNReal t) p.1, f₂ (min p.2.toNNReal t) p.1) :=
    (hg.comp ((hf₁.measurable.comp hφ).prodMk (hf₂.measurable.comp hφ))).stronglyMeasurable
  have h := hF.integral_prod_right' (ν := (volume : Measure ℝ).restrict (Set.Ioc 0 (t : ℝ)))
  convert h using 1
  funext ω
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  simp only
  rw [min_eq_left]
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1.le]
  exact hu.2

/-- The running integral `∫₀ᵗ g(θ¹_u, θ²_u) du` of two progressive processes is `𝓕 t`-measurable. -/
theorem stronglyMeasurable_integral_comp₂ {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {θ₁ θ₂ : ℝ≥0 → Ω → ℝ} (h₁ : IsStronglyProgressive 𝓕 θ₁) (h₂ : IsStronglyProgressive 𝓕 θ₂)
    {g : ℝ × ℝ → ℝ} (hg : Measurable g) (t : ℝ≥0) :
    StronglyMeasurable[𝓕 t] fun ω => ∫ u in (0 : ℝ)..(t : ℝ), g (θ₁ u.toNNReal ω, θ₂ u.toNNReal ω) :=
  @stronglyMeasurable_integral_comp₂_aux Ω (𝓕 t) t θ₁ θ₂ (h₁ t) (h₂ t) g hg

end Integral₂

/-! ### The coordinates as processes -/

section Process

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ}

open scoped Classical in
/-- The retargeting coordinates on the good event (the initial coordinates off it). -/
def rCoord (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (xk : ℝ) (k : Fin nR) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : RCoord nL nR :=
  if ω ∈ G then rCoordAt xk k (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) t else (xL, xR, xk, -1, 0)

open scoped Classical in
/-- Their density on the good event (`0` off it). -/
def rDens (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (k : Fin nR)
    (xk : ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (s : ℝ) (ω : Ω) : RCoord nL nR :=
  if ω ∈ G then rDensAt κ xL xR ρL ρR k xk (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) s else 0

open scoped Classical in
/-- The gap `V_k − W` stopped at `σ`, on the good event (`1` off it). -/
def gapStopR (k : Fin nR) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0)
    (r : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ G then VR k (min r (σ ω)) ω - W (min r (σ ω)) ω else 1

/-- `α` from a gap process. -/
def alphaK (xk : ℝ) (g : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  xk * Real.exp (-2 * ∫ u in (0 : ℝ)..s, (g u.toNNReal ω ^ 2)⁻¹)

/-- `β` from a gap process. -/
def betaK (xk : ℝ) (g : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  -1 - 2 * ∫ u in (0 : ℝ)..s, alphaK xk g u.toNNReal ω / g u.toNNReal ω ^ 3

/-- `S` from a gap process. -/
def clkK (xk : ℝ) (g : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ u in (0 : ℝ)..s, alphaK xk g u.toNNReal ω ^ 2 / g u.toNNReal ω ^ 4

end Process

/-! ### Continuity of the running integrals -/

section Cont

variable {Ω : Type*} {xk : ℝ} {g : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem continuous_running {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous fun s : ℝ≥0 => ∫ u in (0 : ℝ)..(s : ℝ), f u :=
  (intervalIntegral.continuous_primitive (fun a b => hf.intervalIntegrable a b) 0).comp NNReal.continuous_coe

theorem continuous_alphaK (hg : Continuous (g · ω)) (hg0 : ∀ r, g r ω ≠ 0) :
    Continuous fun s => alphaK xk g s ω := by
  have hc : Continuous fun u : ℝ => (g u.toNNReal ω ^ 2)⁻¹ :=
    ((hg.comp continuous_real_toNNReal).pow 2).inv₀ fun u => pow_ne_zero 2 (hg0 _)
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (continuous_running hc)))

theorem continuous_betaK (hg : Continuous (g · ω)) (hg0 : ∀ r, g r ω ≠ 0) :
    Continuous fun s => betaK xk g s ω := by
  have hc : Continuous fun u : ℝ => alphaK xk g u.toNNReal ω / g u.toNNReal ω ^ 3 :=
    ((continuous_alphaK hg hg0).comp continuous_real_toNNReal).div ((hg.comp continuous_real_toNNReal).pow 3)
      fun u => pow_ne_zero 3 (hg0 _)
  exact continuous_const.sub (continuous_const.mul (continuous_running hc))

theorem continuous_clkK (hg : Continuous (g · ω)) (hg0 : ∀ r, g r ω ≠ 0) :
    Continuous fun s => clkK xk g s ω := by
  have hc : Continuous fun u : ℝ => alphaK xk g u.toNNReal ω ^ 2 / g u.toNNReal ω ^ 4 :=
    (((continuous_alphaK hg hg0).comp continuous_real_toNNReal).pow 2).div
      ((hg.comp continuous_real_toNNReal).pow 4) fun u => pow_ne_zero 4 (hg0 _)
  exact continuous_running hc

end Cont

/-! ### The bracket observable -/

section Obs2

variable {nL nR : ℕ} (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
  (k : Fin nR)

/-- The bracket observable `(Ψ − c)² − κ S`. -/
def obs2 (c : ℝ) (p : RCoord nL nR × ℝ) : ℝ := (obs κ xL xR ρL ρR k p - c) ^ 2 - κ * p.1.2.2.2.2

theorem contDiffOn_obs2 (c : ℝ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (obs2 κ xL xR ρL ρR k c) (obsRegion κ xL xR ρL ρR k) :=
  (((contDiffOn_obs κ xL xR ρL ρR k).sub contDiffOn_const).pow 2).sub
    ((by fun_prop : ContDiff ℝ n fun p : RCoord nL nR × ℝ => κ * p.1.2.2.2.2).contDiffOn)

variable {κ xL xR ρL ρR k}

/-- **The bracket observable has no drift** along the coordinate density, off collisions. -/
theorem itoGen_obs2_eq_zero (hκ : 0 ≤ κ) (c : ℝ) {p : RCoord nL nR × ℝ} (hp : p ∈ obsRegion κ xL xR ρL ρR k)
    (hL : ∀ i, p.1.1 i ≠ drv κ xL xR ρL ρR p) (hR : ∀ i, p.1.2.1 i ≠ drv κ xL xR ρL ρR p) :
    Ito.itoGen (obs2 κ xL xR ρL ρR k c) p (dens κ xL xR ρL ρR k p) = 0 := by
  have hU := isOpen_obsRegion κ xL xR ρL ρR k
  have hΦ : ContDiffAt ℝ 2 (obs κ xL xR ρL ρR k) p :=
    (contDiffOn_obs κ xL xR ρL ρR k).contDiffAt (hU.mem_nhds hp)
  have h1 : ContDiffAt ℝ 2 (fun q => (obs κ xL xR ρL ρR k q - c) ^ 2) p := (hΦ.sub contDiffAt_const).pow 2
  have h2 : ContDiffAt ℝ 2 (fun q : RCoord nL nR × ℝ => κ * q.1.2.2.2.2) p := by fun_prop
  have e : obs2 κ xL xR ρL ρR k c = fun q => (fun q => (obs κ xL xR ρL ρR k q - c) ^ 2) q -
      (fun q : RCoord nL nR × ℝ => κ * q.1.2.2.2.2) q := rfl
  have hφ : ContDiff ℝ 2 fun x : ℝ => (x - c) ^ 2 := by fun_prop
  rw [e, itoGen_sub h1 h2, itoGen_clock_coord,
    itoGen_comp_of_hasDerivAt (φ := fun x => (x - c) ^ 2) (φ' := fun x => 2 * (x - c)) (d2 := 2)
      hφ.contDiffAt hΦ (Eventually.of_forall fun x => by
        exact (((hasDerivAt_id x).sub_const c).fun_pow 2).congr_deriv (by simp))
      (by
        exact (((hasDerivAt_id (obs κ xL xR ρL ρR k p)).sub_const c).const_mul 2).congr_deriv (by simp)),
    itoGen_obs_eq_zero hκ hp hL hR, partialSnd_obs_sq hκ hp]
  ring

end Obs2

/-! ### Adaptedness of the stopped coordinates -/

section Adapted

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {nL j m : ℕ}
  {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T)
  (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)

include hE hGm hGc hgood hT in
theorem measurable_gapStopR (n : ℕ) (r : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P r]
      (gapStopR (LP.retargetIdx j m) G W VR (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n) r) := by
  obtain ⟨-, hWa, -, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hσ := isStoppingTime_rLoc hE hGm hGc hgood hT n (k := LP.retargetIdx j m)
  have hK : ∀ s, Measurable[usualAugmentation 𝓕 P s] fun ω =>
      killedAt ζ (VR (LP.retargetIdx j m)) s ω - killedAt ζ W s ω := fun s =>
    (Sec2.TwoSeed.measurable_killed (hVRa _) s).sub (Sec2.TwoSeed.measurable_killed hWa s)
  have h := Ito.measurable_stopped_of_agree (X := fun s ω => VR (LP.retargetIdx j m) s ω - W s ω) hσ hK hG0
    (1 : ℝ) (fun ω hω s hs => ?_) (fun ω hω => ?_) r
  · exact h
  · have hsζ : (s : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hs) (rLoc_lt_lifetime (hgood ω hω))
    simp only [killedAt, hsζ, ↓reduceIte]
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} :=
      fun s hs => lt_of_le_of_lt (by exact_mod_cast hs) (rLoc_lt_lifetime (hgood ω hω))
    exact ((hF.continuousOn_vR _).sub hF.continuousOn_w).mono hsub

include hgood in
theorem continuous_gapStopR (n : ℕ) (ω : Ω) :
    Continuous fun r => gapStopR (LP.retargetIdx j m) G W VR (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n) r ω := by
  by_cases hω : ω ∈ G
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} :=
      fun s hs => lt_of_le_of_lt (by exact_mod_cast hs) (rLoc_lt_lifetime (hgood ω hω))
    have hc := ((hF.continuousOn_vR (LP.retargetIdx j m)).sub hF.continuousOn_w).mono hsub
    simp only [gapStopR, hω, ↓reduceIte]
    exact hc.comp_continuous (continuous_id.min continuous_const) fun r => mem_Iic.2 (min_le_right _ _)
  · simp only [gapStopR, hω, ↓reduceIte]; exact continuous_const

include hgood hD hj in
theorem gapStopR_pos (n : ℕ) (r : ℝ≥0) (ω : Ω) :
    0 < gapStopR (LP.retargetIdx j m) G W VR (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n) r ω := by
  by_cases hω : ω ∈ G
  · simp only [gapStopR, hω, ↓reduceIte]
    exact sub_pos.2 (lt_of_lt_sepTime (lt_sepTime_of_le_rLoc (hgood ω hω) hω hD hj (min_le_right _ _)))
  · simp only [gapStopR, hω, ↓reduceIte]; exact one_pos

/-- On the good event, before `σ_n`, the stopped gap is the gap. -/
theorem gapStopR_eq {n : ℕ} {ω : Ω} (hω : ω ∈ G) {s : ℝ≥0}
    (hs : s ≤ rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) {u : ℝ} (hu : u ∈ uIcc (0 : ℝ) s) :
    gapStopR (LP.retargetIdx j m) G W VR (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n) u.toNNReal ω =
      gap (W · ω) (VR (LP.retargetIdx j m) · ω) u := by
  rw [uIcc_of_le s.coe_nonneg] at hu
  simp only [gapStopR, hω, ↓reduceIte, gap]
  rw [min_eq_left ((Sec2.toNNReal_le_of_mem_Icc hu).trans hs)]

theorem alphaK_eq {n : ℕ} {ω : Ω} (hω : ω ∈ G) {s : ℝ≥0}
    (hs : s ≤ rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) :
    alphaK (LP.retargetPos xR) (gapStopR (LP.retargetIdx j m) G W VR (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n)) s ω
      = alpha (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω) s := by
  unfold alphaK alpha
  congr 3
  exact intervalIntegral.integral_congr fun u hu => by rw [gapStopR_eq hω hs hu]

theorem betaK_eq {n : ℕ} {ω : Ω} (hω : ω ∈ G) {s : ℝ≥0}
    (hs : s ≤ rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) :
    betaK (LP.retargetPos xR) (gapStopR (LP.retargetIdx j m) G W VR (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n)) s ω
      = beta (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω) s := by
  unfold betaK beta
  congr 2
  refine intervalIntegral.integral_congr fun u hu => ?_
  have hu' := hu
  rw [uIcc_of_le s.coe_nonneg] at hu'
  rw [gapStopR_eq hω hs hu, alphaK_eq hω ((Sec2.toNNReal_le_of_mem_Icc hu').trans hs),
    Real.coe_toNNReal _ hu'.1]

theorem clkK_eq {n : ℕ} {ω : Ω} (hω : ω ∈ G) {s : ℝ≥0}
    (hs : s ≤ rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) :
    clkK (LP.retargetPos xR) (gapStopR (LP.retargetIdx j m) G W VR (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n)) s ω
      = clk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)) s := by
  unfold clkK clk
  refine intervalIntegral.integral_congr fun u hu => ?_
  have hu' := hu
  rw [uIcc_of_le s.coe_nonneg] at hu'
  simp only [rate]
  rw [gapStopR_eq hω hs hu, alphaK_eq hω ((Sec2.toNNReal_le_of_mem_Icc hu').trans hs),
    Real.coe_toNNReal _ hu'.1]

include hE hGm hGc hgood hT hD hj in
/-- **The stopped coordinates are adapted.** -/
theorem measurable_rCoord_stopped (n : ℕ) (t : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P t] fun ω => rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
      (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω := by
  obtain ⟨-, -, hVLa, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  set σ := rLoc (LP.retargetIdx j m) G T W VL VR B ζ n with hσdef
  set gS := gapStopR (LP.retargetIdx j m) G W VR σ with hgS
  have hpos : 0 < LP.retargetPos xR := LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hσ := isStoppingTime_rLoc hE hGm hGc hgood hT n (k := LP.retargetIdx j m)
  have hgc : ∀ ω, Continuous fun r => gS r ω := continuous_gapStopR hgood n
  have hg0 : ∀ ω r, gS r ω ≠ 0 := fun ω r => (gapStopR_pos hgood hD hj n r ω).ne'
  have hprogG : IsStronglyProgressive 𝓖 gS :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun r => (measurable_gapStopR hE hGm hGc hgood hT n r).stronglyMeasurable) hgc
  have hαm : ∀ s, Measurable[𝓖 s] (alphaK (LP.retargetPos xR) gS s) := fun s => by
    have hI := (Girsanov.stronglyMeasurable_integral_comp hprogG (g := fun x : ℝ => (x ^ 2)⁻¹)
      (by fun_prop) s).measurable
    exact (Real.measurable_exp.comp (hI.const_mul (-2))).const_mul _
  have hprogα : IsStronglyProgressive 𝓖 (alphaK (LP.retargetPos xR) gS) :=
    StronglyAdapted.isStronglyProgressive_of_continuous (fun s => (hαm s).stronglyMeasurable)
      fun ω => continuous_alphaK (hgc ω) (hg0 ω)
  have hβm : ∀ s, Measurable[𝓖 s] (betaK (LP.retargetPos xR) gS s) := fun s => by
    have hI := (stronglyMeasurable_integral_comp₂ hprogα hprogG (g := fun p : ℝ × ℝ => p.1 / p.2 ^ 3)
      (by fun_prop) s).measurable
    exact measurable_const.sub (hI.const_mul 2)
  have hSm : ∀ s, Measurable[𝓖 s] (clkK (LP.retargetPos xR) gS s) := fun s =>
    (stronglyMeasurable_integral_comp₂ hprogα hprogG (g := fun p : ℝ × ℝ => p.1 ^ 2 / p.2 ^ 4)
      (by fun_prop) s).measurable
  set K : ℝ≥0 → Ω → RCoord nL (j + 1 + m) := fun s ω => ((fun i => killedAt ζ (VL i) s ω),
    (fun i => killedAt ζ (VR i) s ω), alphaK (LP.retargetPos xR) gS s ω, betaK (LP.retargetPos xR) gS s ω,
    clkK (LP.retargetPos xR) gS s ω) with hKdef
  have hK : ∀ s, Measurable[𝓖 s] (K s) := fun s => by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ((hαm s).prodMk ((hβm s).prodMk (hSm s))))
    · exact @Measurable.of_eval Ω (Fin nL) (fun _ => ℝ) (𝓖 s) _ _ fun i =>
        Sec2.TwoSeed.measurable_killed (hVLa i) s
    · exact @Measurable.of_eval Ω (Fin (j + 1 + m)) (fun _ => ℝ) (𝓖 s) _ _ fun i =>
        Sec2.TwoSeed.measurable_killed (hVRa i) s
  have h := Ito.measurable_stopped_of_agree
    (X := fun s ω => rCoordAt (LP.retargetPos xR) (LP.retargetIdx j m) (W · ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) s) hσ hK hG0
    ((xL, xR, LP.retargetPos xR, -1, 0) : RCoord nL (j + 1 + m)) (fun ω hω s hs => ?_) (fun ω hω => ?_) t
  · exact h
  · have hsζ : (s : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hs) (rLoc_lt_lifetime (hgood ω hω))
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_) (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · simp only [hKdef, killedAt, hsζ, ↓reduceIte, rCoordAt]
    · simp only [hKdef, killedAt, hsζ, ↓reduceIte, rCoordAt]
    · exact alphaK_eq hω hs
    · exact betaK_eq hω hs
    · exact clkK_eq hω hs
  · have hω' := hgood ω hω
    have hF := hω'.1.isForcePath
    have hσs : ((σ ω : ℝ≥0) : ℝ≥0∞) < sepTime (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω) :=
      lt_sepTime_of_le_rLoc hω' hω hD hj le_rfl
    have hp := hω'.1.isSLEPathUpTo (sepTime_le (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω))
    have hd := retargetData_of_isSLEPathUpTo hp hD hj fun t ht => lt_of_lt_sepTime ht
    have hS := hd.sep.isSep_of_lt hσs
    have hsub : Iic (σ ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} :=
      fun s hs => lt_of_le_of_lt (by exact_mod_cast hs) (rLoc_lt_lifetime hω')
    have hmaps : MapsTo (fun s : ℝ≥0 => (s : ℝ)) (Iic (σ ω)) (Icc 0 (σ ω : ℝ)) :=
      fun s hs => ⟨s.coe_nonneg, by exact_mod_cast hs⟩
    have hα := (hS.continuousOn_alpha (xk := LP.retargetPos xR)).comp NNReal.continuous_coe.continuousOn hmaps
    have hβ := (hS.continuousOn_beta (xk := LP.retargetPos xR)).comp NNReal.continuous_coe.continuousOn hmaps
    have hc := ((hS.isRate hpos).continuousOn_clk).comp NNReal.continuous_coe.continuousOn hmaps
    exact (continuousOn_pi.2 fun i => (hF.continuousOn_vL i).mono hsub).prodMk
      ((continuousOn_pi.2 fun i => (hF.continuousOn_vR i).mono hsub).prodMk (hα.prodMk (hβ.prodMk hc)))

theorem rKb_nonneg {nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {xk : ℝ} (hxk : 0 ≤ xk) (n : ℕ) :
    0 ≤ rKb xL xR xk n := by
  unfold rKb
  have h1 : 0 ≤ ∑ i, (|xL i| + (n : ℝ)) := Finset.sum_nonneg fun i _ => by positivity
  have h2 : 0 ≤ ∑ i, (|xR i| + (n : ℝ)) := Finset.sum_nonneg fun i _ => by positivity
  positivity

include hE hGm hGc hgood hT hD hj in
/-- **A localized observable with vanishing drift is a martingale**: for every `C³` function `F` on the
observable's region whose generator vanishes at the coordinate density off collisions, `F(Λ, b)` stopped at `σ_n`
is a martingale of the usual augmentation. -/
theorem martingale_rObs_stopped {F : RCoord nL (j + 1 + m) × ℝ → ℝ}
    (hF : ContDiffOn ℝ 3 F (obsRegion κ xL xR ρL ρR (LP.retargetIdx j m)))
    (hgen : ∀ p ∈ obsRegion κ xL xR ρL ρR (LP.retargetIdx j m), (∀ i, p.1.1 i ≠ drv κ xL xR ρL ρR p) →
      (∀ i, p.1.2.1 i ≠ drv κ xL xR ρL ρR p) → Ito.itoGen F p (dens κ xL xR ρL ρR (LP.retargetIdx j m) p) = 0)
    (n : ℕ) :
    Martingale (fun t ω => F (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
      (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω))
      (usualAugmentation 𝓕 P) P := by
  set σ := rLoc (LP.retargetIdx j m) G T W VL VR B ζ n with hσdef
  have hpos : 0 < LP.retargetPos xR := LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj
  have hB' := isFilteredBrownianReal_brownG_r hE hGm hGc hgood
  -- the path facts on the good event
  have hpath : ∀ ω ∈ G, ∃ (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (B · ω) (sepTime (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω))),
      RetargetData xL xR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
        (sepTime (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω)) := fun ω hω => by
    have hp := (hgood ω hω).1.isSLEPathUpTo (sepTime_le (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω))
    exact ⟨hp, retargetData_of_isSLEPathUpTo hp hD hj fun t ht => lt_of_lt_sepTime ht⟩
  have hσs : ∀ ω ∈ G, ∀ t ≤ σ ω, ((t : ℝ≥0) : ℝ≥0∞) < sepTime (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω) :=
    fun ω hω t ht => lt_sepTime_of_le_rLoc (hgood ω hω) hω hD hj ht
  have hlam : ∀ ω, IntervalIntegrable (rDens κ xL xR ρL ρR (LP.retargetIdx j m) (LP.retargetPos xR) G W VL VR B
      · ω) volume 0 (σ ω) := fun ω => by
    by_cases hω : ω ∈ G
    · obtain ⟨hp, hd⟩ := hpath ω hω
      simpa only [rDens, hω, ↓reduceIte] using intervalIntegrable_rDensAt hp hd (hσs ω hω _ le_rfl)
    · simp only [rDens, hω, ↓reduceIte]; exact intervalIntegrable_const
  have hΛ : ∀ ω (t : ℝ≥0), t ≤ σ ω → rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR t ω =
      rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR 0 ω +
        ∫ s in (0 : ℝ)..t, rDens κ xL xR ρL ρR (LP.retargetIdx j m) (LP.retargetPos xR) G W VL VR B s ω := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · obtain ⟨hp, hd⟩ := hpath ω hω
      simp only [rCoord, rDens, hω, ↓reduceIte]
      exact rCoordAt_eq_add_integral hp hd (hσs ω hω t ht)
    · simp only [rCoord, rDens, hω, ↓reduceIte, intervalIntegral.integral_zero, add_zero]
  have hKb : ∀ ω, ∫ s in (0 : ℝ)..(σ ω), ‖rDens κ xL xR ρL ρR (LP.retargetIdx j m) (LP.retargetPos xR) G W VL VR B
      s ω‖ ≤ rKb xL xR (LP.retargetPos xR) n := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [rDens, hω, ↓reduceIte] using integral_norm_rDensAt_le (hgood ω hω) hω hD hj
    · simp only [rDens, hω, ↓reduceIte, norm_zero, intervalIntegral.integral_zero]
      exact rKb_nonneg xL xR hpos.le n
  have hK : ∀ ω (t : ℝ≥0), t ≤ σ ω → (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR t ω,
      Sec2.TwoSeed.brownG G B t ω) ∈ rKc κ xL xR ρL ρR (LP.retargetIdx j m) (LP.retargetPos xR) n := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · simpa only [rCoord, Sec2.TwoSeed.brownG, hω, ↓reduceIte] using
        mem_rKc_of_le_rLoc (hgood ω hω) hω hD hj hgood ht
    · simp only [rCoord, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
      exact mem_insert _ _
  have hM := Ito.martingale_itoLocalized hB' (continuous_brownG_r hgood)
    (isOpen_obsRegion κ xL xR ρL ρR (LP.retargetIdx j m)) hF (isCompact_rKc κ xL xR ρL ρR _ _ n)
    (rKc_subset_obsRegion κ xL xR ρL ρR _ _ (rInit_mem_obsRegion hD hj _) n)
    (isStoppingTime_rLoc hE hGm hGc hgood hT n) (measurable_rCoord_stopped hE hGm hGc hgood hT hD hj n)
    hlam hΛ hKb hK
  have hzero : ∀ (t : ℝ≥0) ω, ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
      Ito.itoGen F (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR s.toNNReal ω,
        Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (rDens κ xL xR ρL ρR (LP.retargetIdx j m) (LP.retargetPos xR) G W VL VR B s ω) = 0 := by
    intro t ω
    by_cases hω : ω ∈ G
    · obtain ⟨hp, hd⟩ := hpath ω hω
      simp only [rCoord, rDens, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
      refine intervalIntegral.integral_zero_ae ?_
      filter_upwards [ae_itoGen_eq_zero hp hd hgen (hσs ω hω _ le_rfl)] with s hs hsI
      rw [uIoc_of_le (min t (σ ω)).coe_nonneg] at hsI
      exact hs ⟨hsI.1, hsI.2.trans (by exact_mod_cast min_le_right t (σ ω))⟩
    · have h0' : σ ω = 0 := rLoc_of_not_mem hω n
      rw [h0', min_eq_right (zero_le (a := t)), NNReal.coe_zero, intervalIntegral.integral_same]
  have e : (fun t ω => F (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR (min t (σ ω)) ω,
      Sec2.TwoSeed.brownG G B (min t (σ ω)) ω) -
      ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), Ito.itoGen F (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W
        VL VR s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (rDens κ xL xR ρL ρR (LP.retargetIdx j m) (LP.retargetPos xR) G W VL VR B s ω)) =
      fun t ω => F (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR (min t (σ ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (σ ω)) ω) := by
    funext t ω; rw [hzero t ω, sub_zero]
  rw [e] at hM
  exact hM

include hE hGm hGc hgood hT hD hj in
/-- **`Ψ` stopped at `σ_n` is a martingale.** -/
theorem martingale_obs_stopped (hκ : 0 ≤ κ) (n : ℕ) :
    Martingale (fun t ω => obs κ xL xR ρL ρR (LP.retargetIdx j m)
      (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
        (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω))
      (usualAugmentation 𝓕 P) P :=
  martingale_rObs_stopped hE hGm hGc hgood hT hD hj (contDiffOn_obs (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR)
      (k := LP.retargetIdx j m))
    (fun _ hp hL hR => itoGen_obs_eq_zero hκ hp hL hR) n

include hE hGm hGc hgood hT hD hj in
/-- **`(Ψ − c)² − κ S` stopped at `σ_n` is a martingale.** -/
theorem martingale_obs2_stopped (hκ : 0 ≤ κ) (c : ℝ) (n : ℕ) :
    Martingale (fun t ω => obs2 κ xL xR ρL ρR (LP.retargetIdx j m) c
      (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
        (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω))
      (usualAugmentation 𝓕 P) P :=
  martingale_rObs_stopped hE hGm hGc hgood hT hD hj (contDiffOn_obs2 κ xL xR ρL ρR _ c)
    (fun _ hp hL hR => itoGen_obs2_eq_zero hκ c hp hL hR) n

include hE hGm hGc hgood hT hD hj in
/-- **`Z_a = exp(aΨ/√κ − a²S/2)` stopped at `σ_n` is a martingale.** -/
theorem martingale_expObs_stopped (hκ : 0 < κ) (a : ℝ) (n : ℕ) :
    Martingale (fun t ω => expObs κ xL xR ρL ρR (LP.retargetIdx j m) a
      (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
        (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω))
      (usualAugmentation 𝓕 P) P :=
  martingale_rObs_stopped hE hGm hGc hgood hT hD hj (contDiffOn_expObs (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR)
      (k := LP.retargetIdx j m) a)
    (fun _ hp hL hR => itoGen_expObs_eq_zero hκ a hp hL hR) n

end Adapted

end Retarget

end Zhan

end InteractingSLE
