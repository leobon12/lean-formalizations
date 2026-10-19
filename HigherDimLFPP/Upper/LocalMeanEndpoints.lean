import HigherDimLFPP.Upper.LocalMeanCompact

/-!
# Lemma 4.3, Step 2: varying endpoints

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.2, proof of Lemma 4.3, Step 2 ((4.14) and
the comparison with `√(1+u) Z + C √(1+u⁻¹) B`), as completed by the planning audit HA3
(`planning/audits/HA3-section-4.md`), Details D5, Steps 2a–2c (fixes F2, F11, F16); packet P-U4.

Configurations `c = ([x, y], Q)` with `x` within `ρδ` of `0` and `y` within `ρδ` of `e₁`
(`ρ = 4√d`), `Q ∈ G_K(x, y)`, are written as `c = T_c(I, Q₀(c))` with the similarity
`T_c = simOf x y` (`T_c 0 = x`, `T_c e₁ = y`) and the shape `Q₀(c) = T_c⁻¹ Q ∈ G_K(0, e₁)`
(Step 2a).  Then (Step 2b), with `V(c)` the all-scale white-noise vector of `ν_{[x,y]} - ν_Q`:

* changing the shape at fixed endpoints is an isometry: `‖V(T Q₀) - V(T Q₀')‖ = ‖Z(Q₀) - Z(Q₀')‖`
  (exact similarity invariance, `scaleCov_map_simAffine_Ioi`);
* changing the endpoints at fixed shape costs `δ⁻¹ E(…)² ≤ C' Σ_j |p_j - p'_j|` where
  `p = (x/δ, (y - e₁)/δ) ∈ ℝ^{2d}` (Lemma 3.1 with the couplings `(T_c, T_{c'})_* μ` and (4.14),
  `norm_simOf_sub_le`); `C'` depends only on `d` and the kernel;
* `|v + w|² ≤ (1+u)|v|² + (1+u⁻¹)|w|²`.

Step 2c: the comparison process `√(1+u) Z(Q₀) + √((1+u⁻¹)C') B(p)`, with `B` the Brownian kernel
`bmCov` of `LocalMeanSetup`, dominates the canonical metric, so `gEM_le_add_of_dist` splits the
expected maximum into Step 1 (`step1`) and the expected maximum of `B` over a box
(`gEM_bmCov_le`); this gives `step2`, Lemma 4.3 for normalized endpoints.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

open LQGDimension (gaussianExpectedMax vecExpectedMax PSDOn)

variable {d : ℕ}

/-! ## Measure-theoretic helpers -/

section Helpers

/-- Same-point coupling of two pushforwards of one measure. -/
theorem coupledWithin_map_map {μ : Measure (Rd d)} {T T' : Rd d → Rd d} (hT : Measurable T)
    (hT' : Measurable T') {u : ℝ} (h : ∀ᵐ z ∂μ, ‖T z - T' z‖ ≤ u) :
    HigherDimLFPP.CoupledWithin (μ.map T) (μ.map T') u := by
  have hp : Measurable fun z => (T z, T' z) := hT.prodMk hT'
  refine ⟨μ.map fun z => (T z, T' z), ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hp]; rfl
  · rw [Measure.map_map measurable_snd hp]; rfl
  · rw [ae_map_iff hp.aemeasurable (measurableSet_le (by fun_prop) measurable_const)]
    exact h

theorem segMeasure_unit_ae_norm_le (hd : 0 < d) : ∀ᵐ z ∂(segMeasure 0 (e₁ d)), ‖z‖ ≤ 2 := by
  rw [segMeasure_eq, ae_map_iff (measurable_lin _ _).aemeasurable
    (measurableSet_le continuous_norm.measurable measurable_const)]
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  rw [lin, zero_add, sub_zero, norm_smul, Lower.norm_e₁ hd, mul_one, Real.norm_eq_abs,
    abs_of_nonneg hs.1]
  linarith [hs.2]

theorem unitGood_ae_norm_le (hd : 0 < d) {K : ℕ} {a₀ : ℝ} (ha₀ : a₀ ≤ 1 / 2) {Q : List (Rd d)}
    (hQ : Q ∈ goodFamily K a₀ 0 (e₁ d)) : ∀ᵐ z ∂(polyMeasure Q), ‖z‖ ≤ 2 := by
  obtain ⟨-, hQV, -, -, -, -, -, -, hball, -⟩ := unitGood_facts hd ha₀ hQ
  rw [hQV, polyMeasure_range_map]
  exact ae_norm_le_segSum hball

theorem growthBound_mono_scale {μ : Measure (Rd d)} {B R R' : ℝ} (h : HigherDimLFPP.GrowthBound μ B R)
    (hB : 0 ≤ B) (hR' : 0 < R') (hRR : R' ≤ R) : HigherDimLFPP.GrowthBound μ B R' := by
  intro z t ht
  refine (h z t ht).trans (mul_le_mul_of_nonneg_left (min_le_min le_rfl ?_) hB)
  exact div_le_div_of_nonneg_left ht.le hR' hRR

end Helpers

/-! ## Normalized configurations -/

section Normalized

/-- The endpoints of a configuration `([x, y], Q)`. -/
def cx (c : Config d) : Rd d := c.1.getD 0 0

def cy (c : Config d) : Rd d := c.1.getD 1 0

theorem cx_pair (x y : Rd d) (Q : List (Rd d)) : cx (([x, y], Q) : Config d) = x := rfl

theorem cy_pair (x y : Rd d) (Q : List (Rd d)) : cy (([x, y], Q) : Config d) = y := rfl

/-- The shape `Q₀(c) = T_c⁻¹ Q ∈ G_K(0, e₁)` of a configuration (HA3 D5, Step 2a). -/
def shapeOf (c : Config d) : List (Rd d) := c.2.map (simInv (cx c) (cy c))

/-- The rescaled endpoint parameters `p(c) = (x/δ, (y - e₁)/δ) ∈ ℝ^{2d}` (HA3 D5, Step 2a). -/
def eparam (δ : ℝ) (c : Config d) : Fin (d + d) → ℝ :=
  Fin.append (fun j => (cx c).ofLp j / δ) (fun j => (cy c - e₁ d).ofLp j / δ)

/-- The geometry of a normalized chord (HA3 D5, Step 2a): if `|x|, |y - e₁| ≤ 1/8`, then
`|y - x| ∈ [3/4, 5/4]`, the direction `u` of `y - x` satisfies `|e₁ + u| ≥ 1`, and the similarity
`simOf x y` carries `e₁` to `y`. -/
theorem normChord_facts (hd : 0 < d) {x y : Rd d} (hx : ‖x‖ ≤ 1 / 8) (hy : ‖y - e₁ d‖ ≤ 1 / 8) :
    x ≠ y ∧ 3 / 4 ≤ ‖y - x‖ ∧ ‖y - x‖ ≤ 5 / 4 ∧
      1 ≤ ‖e₁ d + ‖y - x‖⁻¹ • (y - x)‖ ∧ simOf x y (e₁ d) = y := by
  have he : ‖e₁ d‖ = 1 := Lower.norm_e₁ hd
  have h1 : ‖(y - x) - e₁ d‖ ≤ 1 / 4 := by
    calc ‖(y - x) - e₁ d‖ = ‖(y - e₁ d) - x‖ := by congr 1; abel
      _ ≤ ‖y - e₁ d‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ 1 / 4 := by linarith
  have h2 : 3 / 4 ≤ ‖y - x‖ := by
    have := norm_sub_norm_le (e₁ d) (e₁ d - (y - x))
    rw [sub_sub_cancel, he, norm_sub_rev] at this
    linarith
  have h3 : ‖y - x‖ ≤ 5 / 4 := by
    have := norm_le_insert' (y - x) (e₁ d)
    linarith
  have hxy : x ≠ y := fun h => by rw [h, sub_self, norm_zero] at h2; linarith
  have hv : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  have h4 : ‖e₁ d - ‖y - x‖⁻¹ • (y - x)‖ ≤ 1 / 2 := by
    have := norm_normalize_sub_le (w := e₁ d) (by
      intro h; rw [h, norm_zero] at he; exact zero_ne_one he) (y - x)
    rw [he, inv_one, one_smul, div_one] at this
    have h1' : ‖e₁ d - (y - x)‖ ≤ 1 / 4 := by rw [norm_sub_rev]; exact h1
    linarith
  have h5 : 1 ≤ ‖e₁ d + ‖y - x‖⁻¹ • (y - x)‖ := by
    have e : e₁ d + ‖y - x‖⁻¹ • (y - x) = (2 : ℝ) • e₁ d - (e₁ d - ‖y - x‖⁻¹ • (y - x)) := by
      module
    rw [e]
    have := norm_sub_norm_le ((2 : ℝ) • e₁ d) (e₁ d - ‖y - x‖⁻¹ • (y - x))
    rw [norm_smul, he, Real.norm_two, mul_one] at this
    linarith
  refine ⟨hxy, h2, h3, h5, simOf_e₁ hd hxy fun h => ?_⟩
  rw [h, norm_zero] at h5
  linarith

end Normalized

/-! ## Step 2b: the split of the canonical metric -/

section Split

variable {κ : Rd d → ℝ}

theorem bandVecM_sub_right_common (hκ : IsLFPPKernel κ) {S : Set ℝ} {μ ν ν' : Measure (Rd d)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ν'] (h : IsPairable κ S μ ν)
    (h' : IsPairable κ S μ ν') : bandVecM κ S μ ν - bandVecM κ S μ ν' = bandVecM κ S ν' ν := by
  rw [bandVecM_sub_bandVecM hκ h h', add_comm μ ν', bandVecM_add_right hκ]

theorem bandVecM_sub_eq_add (hκ : IsLFPPKernel κ) {S : Set ℝ} {μ ν μ' ν' : Measure (Rd d)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    (h1 : IsPairable κ S μ ν) (h2 : IsPairable κ S μ' ν') (h3 : IsPairable κ S μ μ')
    (h4 : IsPairable κ S ν' ν) :
    bandVecM κ S μ ν - bandVecM κ S μ' ν' = bandVecM κ S μ μ' + bandVecM κ S ν' ν := by
  rw [bandVecM_sub_bandVecM hκ h1 h2, ← bandVecM_add hκ h3 h4, add_comm ν μ']

/-- `|v + w|² ≤ (1 + u)|v|² + (1 + u⁻¹)|w|²` for `u > 0`. -/
theorem norm_add_sq_le_weighted {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E) {u : ℝ} (hu : 0 < u) :
    ‖v + w‖ ^ 2 ≤ (1 + u) * ‖v‖ ^ 2 + (1 + u⁻¹) * ‖w‖ ^ 2 := by
  have h1 : ‖v + w‖ ≤ ‖v‖ + ‖w‖ := norm_add_le v w
  have h2 : ‖v + w‖ ^ 2 ≤ (‖v‖ + ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : 2 * ‖v‖ * ‖w‖ ≤ u * ‖v‖ ^ 2 + u⁻¹ * ‖w‖ ^ 2 := by
    have h4 : 0 ≤ (u * ‖v‖ - ‖w‖) ^ 2 := sq_nonneg _
    have h5 : u⁻¹ * (u * ‖v‖ - ‖w‖) ^ 2 = u * ‖v‖ ^ 2 - 2 * ‖v‖ * ‖w‖ + u⁻¹ * ‖w‖ ^ 2 := by
      field_simp
      ring
    have h6 : 0 ≤ u⁻¹ * (u * ‖v‖ - ‖w‖) ^ 2 := mul_nonneg (inv_nonneg.2 hu.le) h4
    linarith
  nlinarith

/-- The white-noise vector of `⟨h, ν_{P₁} - ν_{P₂}⟩` of a configuration `(P₁, P₂)`. -/
def cfgV (κ : Rd d → ℝ) (c : Config d) : WN d :=
  bandVecM κ (Ioi 0) (polyMeasure c.1) (polyMeasure c.2)

/-- The normalized configurations of Step 2: `c = ([x, y], Q)` with `|x|, |y - e₁| ≤ ρ` and
`Q ∈ G_K(x, y)`. -/
def NormCfg (n : ℕ) (ρ : ℝ) (c : Config d) : Prop :=
  ∃ x y : Rd d, c.1 = [x, y] ∧ ‖x‖ ≤ ρ ∧ ‖y - e₁ d‖ ≤ ρ ∧ c.2 ∈ goodFamily (2 ^ n) (a0 n) x y

/-- The data of a normalized configuration (HA3 D5, Step 2a): `c = T(I, Q₀)` with `T = simOf x y`
and `Q₀ = shapeOf c ∈ G_K(0, e₁)`. -/
theorem NormCfg.facts (hd : 0 < d) {n : ℕ} {ρ : ℝ} (hρ : ρ ≤ 1 / 8) {c : Config d}
    (hc : NormCfg n ρ c) :
    ∃ x y : Rd d, c.1 = [x, y] ∧ cx c = x ∧ cy c = y ∧ ‖x‖ ≤ ρ ∧ ‖y - e₁ d‖ ≤ ρ ∧ x ≠ y ∧
      3 / 4 ≤ ‖y - x‖ ∧ ‖y - x‖ ≤ 5 / 4 ∧ 1 ≤ ‖e₁ d + ‖y - x‖⁻¹ • (y - x)‖ ∧
      simOf x y (e₁ d) = y ∧ c.2 ∈ goodFamily (2 ^ n) (a0 n) x y ∧
      shapeOf c ∈ goodFamily (2 ^ n) (a0 n) 0 (e₁ d) ∧ (shapeOf c).map (simOf x y) = c.2 := by
  obtain ⟨x, y, h1, hx, hy, hQ⟩ := hc
  obtain ⟨hxy, h2, h3, h4, h5⟩ := normChord_facts hd (hx.trans hρ) (hy.trans hρ)
  have hcx : cx c = x := by rw [cx, h1]; rfl
  have hcy : cy c = y := by rw [cy, h1]; rfl
  obtain ⟨hs, hs'⟩ := goodFamily_simInv hQ hxy h5
  refine ⟨x, y, h1, hcx, hcy, hx, hy, hxy, h2, h3, h4, h5, hQ, ?_, ?_⟩
  · rw [shapeOf, hcx, hcy]; exact hs
  · rw [shapeOf, hcx, hcy]; exact hs'

end Split

/-! ## Step 2b: the estimate -/

section Estimate

variable {κ : Rd d → ℝ}

theorem simOf_eq (x y : Rd d) :
    simOf x y = simAffine x ‖y - x‖ (rotE (‖y - x‖⁻¹ • (y - x))) := rfl

theorem segMeasure_eq_map_simOf {x y : Rd d} (hT : simOf x y (e₁ d) = y) :
    segMeasure x y = (segMeasure 0 (e₁ d)).map (simOf x y) := by
  have h := segMeasure_map_simAffine x ‖y - x‖ (rotE (‖y - x‖⁻¹ • (y - x))) 0 (e₁ d)
  rw [← simOf_eq, simOf_zero, hT] at h
  exact h

/-- **Step 2b of HA3 D5**: for normalized configurations `c, c'` (`ρ ≤ 1/8`) and `u > 0`,
`‖V(c) - V(c')‖² ≤ (1+u) ‖Z(Q₀(c)) - Z(Q₀(c'))‖² + (1+u⁻¹) 1600 C (|x - x'| + |y - y'|)`, where `C`
is the transport constant of `κ` for growth constant `3`. -/
theorem norm_cfgV_sub_sq_le (hd : 0 < d) (hκ : IsLFPPKernel κ) {C : ℝ}
    (hC : TransportVar3 κ C) {n : ℕ} {ρ u : ℝ} (hρ : ρ ≤ 1 / 8) (hu : 0 < u) {c c' : Config d}
    (hc : NormCfg n ρ c) (hc' : NormCfg n ρ c') :
    ‖cfgV κ c - cfgV κ c'‖ ^ 2 ≤
      (1 + u) * ‖shapeV κ (shapeOf c) - shapeV κ (shapeOf c')‖ ^ 2 +
        (1 + u⁻¹) * (1600 * C * (‖cx c - cx c'‖ + ‖cy c - cy c'‖)) := by
  obtain ⟨x, y, h1, hcx, hcy, hx, hy, hxy, hr1, hr2, hu1, hT1, hQ, hQ₀, hQmap⟩ := hc.facts hd hρ
  obtain ⟨x', y', h1', hcx', hcy', hx', hy', hxy', hr1', hr2', hu1', hT1', hQ', hQ₀', hQmap'⟩ :=
    hc'.facts hd hρ
  rw [hcx, hcy, hcx', hcy']
  have ha₀ : a0 n ≤ 1 / 2 := a0_le_half n
  set Q₀ := shapeOf c with hQ₀def
  set Q₀' := shapeOf c' with hQ₀'def
  have hTm : Measurable (simOf x y) := measurable_simAffine _ _ _
  have hT'm : Measurable (simOf x' y') := measurable_simAffine _ _ _
  have hr : 0 < ‖y - x‖ := by linarith
  have hr' : 0 < ‖y' - x'‖ := by linarith
  -- the auxiliary polygon `Q̃ = T Q₀'` with the endpoints of `c` and the shape of `c'`
  obtain ⟨Qt, hQtdef⟩ : ∃ Qt, Qt = Q₀'.map (simOf x y) := ⟨_, rfl⟩
  have hQt : Qt ∈ goodFamily (2 ^ n) (a0 n) x y := by
    have h := goodFamily_map_simAffine x hr (rotE (‖y - x‖⁻¹ • (y - x))) hQ₀'
    rw [← simOf_eq, simOf_zero, hT1] at h
    rw [hQtdef]
    exact h
  -- the measures
  have eI : polyMeasure c.1 = segMeasure x y := by rw [h1, polyMeasure_pair hxy]
  have eI' : polyMeasure c'.1 = segMeasure x' y' := by rw [h1', polyMeasure_pair hxy']
  have eIT : segMeasure x y = (segMeasure 0 (e₁ d)).map (simOf x y) :=
    segMeasure_eq_map_simOf hT1
  have eIT' : segMeasure x' y' = (segMeasure 0 (e₁ d)).map (simOf x' y') :=
    segMeasure_eq_map_simOf hT1'
  have eQT : polyMeasure c.2 = (polyMeasure Q₀).map (simOf x y) := by
    rw [← hQmap, simOf_eq, polyMeasure_map_simAffine x hr]
  have eQT' : polyMeasure c'.2 = (polyMeasure Q₀').map (simOf x' y') := by
    rw [← hQmap', simOf_eq, polyMeasure_map_simAffine x' hr']
  have eQtT : polyMeasure Qt = (polyMeasure Q₀').map (simOf x y) := by
    rw [hQtdef, simOf_eq, polyMeasure_map_simAffine x hr]
  -- probability, growth at scale `1/2`, couplings
  have := goodFamily_isProbabilityMeasure hQ hxy
  have := goodFamily_isProbabilityMeasure hQ' hxy'
  have := goodFamily_isProbabilityMeasure hQt hxy
  have := goodFamily_isProbabilityMeasure hQ₀ (zero_ne_e₁ hd)
  have := goodFamily_isProbabilityMeasure hQ₀' (zero_ne_e₁ hd)
  have gI : HigherDimLFPP.GrowthBound (segMeasure x y) 3 (1 / 2) :=
    growthBound_mono_scale (HigherDimLFPP.GrowthBound.mono_const (μ := segMeasure x y)
      (segMeasure_growthBound hxy) hr (by norm_num)) (by norm_num) (by norm_num) (by linarith)
  have gI' : HigherDimLFPP.GrowthBound (segMeasure x' y') 3 (1 / 2) :=
    growthBound_mono_scale (HigherDimLFPP.GrowthBound.mono_const (μ := segMeasure x' y')
      (segMeasure_growthBound hxy') (by linarith) (by norm_num)) (by norm_num) (by norm_num)
      (by linarith)
  have gQ : HigherDimLFPP.GrowthBound (polyMeasure c.2) 3 (1 / 2) :=
    growthBound_mono_scale (goodFamily_growthBound hQ hxy) (by norm_num) (by norm_num)
      (by linarith)
  have gQ' : HigherDimLFPP.GrowthBound (polyMeasure c'.2) 3 (1 / 2) :=
    growthBound_mono_scale (goodFamily_growthBound hQ' hxy') (by norm_num) (by norm_num)
      (by linarith)
  have gQt : HigherDimLFPP.GrowthBound (polyMeasure Qt) 3 (1 / 2) :=
    growthBound_mono_scale (goodFamily_growthBound hQt hxy) (by norm_num) (by norm_num)
      (by linarith)
  have hpair : ∀ (μ ν : Measure (Rd d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (w : ℝ),
      0 ≤ w → HigherDimLFPP.GrowthBound μ 3 (1 / 2) → HigherDimLFPP.GrowthBound ν 3 (1 / 2) →
      HigherDimLFPP.CoupledWithin μ ν w → IsPairable κ (Ioi 0) μ ν ∧
        scaleCov κ (Ioi 0) μ ν μ ν ≤ 2 * C * w := by
    intro μ ν _ _ w hw g1 g2 cpl
    have h := hC (Ioi 0) measurableSet_Ioi subset_rfl μ ν (1 / 2) w (by norm_num) hw g1 g2 cpl
    refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
    field_simp
  have hsq : ∀ P : List (Rd d), 0 ≤ 2 * ‖y - x‖ * Real.sqrt (Real.log (polyLen P / ‖y - x‖)) :=
    fun P => by positivity
  have p1 := (hpair _ _ _ (hsq _) gI gQ (goodFamily_coupled hQ hxy (a0_le_one n))).1
  have p2 := (hpair _ _ _ (hsq _) gI gQt (goodFamily_coupled hQt hxy (a0_le_one n))).1
  have p3 := (hpair _ _ _ (by positivity) gI' gQ' (goodFamily_coupled hQ' hxy' (a0_le_one n))).1
  -- the endpoint couplings
  set Δ := ‖x - x'‖ + ‖y - y'‖ with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  have hTT : ∀ z : Rd d, ‖z‖ ≤ 2 → ‖simOf x y z - simOf x' y' z‖ ≤ 200 * Δ := fun z hz =>
    norm_simOf_sub_le (by linarith) (by linarith) hu1 hu1' hz
  have hT'T : ∀ z : Rd d, ‖z‖ ≤ 2 → ‖simOf x' y' z - simOf x y z‖ ≤ 200 * Δ := by
    intro z hz
    have h := norm_simOf_sub_le (x := x') (y := y') (x' := x) (y' := y) (by linarith)
      (by linarith) hu1' hu1 hz
    rw [norm_sub_rev x' x, norm_sub_rev y' y] at h
    exact h
  have cII' : HigherDimLFPP.CoupledWithin (segMeasure x y) (segMeasure x' y') (200 * Δ) := by
    rw [eIT, eIT']
    exact coupledWithin_map_map hTm hT'm ((segMeasure_unit_ae_norm_le hd).mono fun z hz => hTT z hz)
  have cQ'Qt : HigherDimLFPP.CoupledWithin (polyMeasure c'.2) (polyMeasure Qt) (200 * Δ) := by
    rw [eQT', eQtT]
    exact coupledWithin_map_map hT'm hTm ((unitGood_ae_norm_le hd ha₀ hQ₀').mono
      fun z hz => hT'T z hz)
  obtain ⟨p4, v4⟩ := hpair _ _ _ (by positivity) gI gI' cII'
  obtain ⟨p5, v5⟩ := hpair _ _ _ (by positivity) gQ' gQt cQ'Qt
  -- the decomposition `V(c) - V(c') = A + B`
  have hdec : cfgV κ c - cfgV κ c' =
      bandVecM κ (Ioi 0) (polyMeasure Qt) (polyMeasure c.2) +
        (bandVecM κ (Ioi 0) (segMeasure x y) (segMeasure x' y') +
          bandVecM κ (Ioi 0) (polyMeasure c'.2) (polyMeasure Qt)) := by
    rw [cfgV, cfgV, eI, eI']
    have e1 := bandVecM_sub_right_common hκ p1 p2
    have e2 := bandVecM_sub_eq_add hκ p2 p3 p4 p5
    rw [← e1, ← e2]
    abel
  -- the shape part is an isometry image
  have hA : ‖bandVecM κ (Ioi 0) (polyMeasure Qt) (polyMeasure c.2)‖ ^ 2 =
      ‖shapeV κ Q₀ - shapeV κ Q₀'‖ ^ 2 := by
    have hC3 : TransportVar3 κ C := hC
    rw [shapeV_sub hκ (isPairable_shape hd hC3 ha₀ hQ₀) (isPairable_shape hd hC3 ha₀ hQ₀'),
      ← scaleCov_self, ← scaleCov_self, eQtT, eQT, simOf_eq,
      scaleCov_map_simAffine_Ioi hκ x hr]
  -- the endpoint part
  have hB : ‖bandVecM κ (Ioi 0) (segMeasure x y) (segMeasure x' y') +
      bandVecM κ (Ioi 0) (polyMeasure c'.2) (polyMeasure Qt)‖ ^ 2 ≤ 1600 * C * Δ := by
    have h1 := norm_add_sq_le_weighted (bandVecM κ (Ioi 0) (segMeasure x y) (segMeasure x' y'))
      (bandVecM κ (Ioi 0) (polyMeasure c'.2) (polyMeasure Qt)) one_pos
    rw [← scaleCov_self, ← scaleCov_self] at h1
    norm_num at h1
    nlinarith
  rw [hdec]
  refine (norm_add_sq_le_weighted _ _ hu).trans ?_
  rw [hA]
  have h1u : 0 ≤ 1 + u⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hB h1u]

end Estimate

/-! ## Step 2c and Lemma 4.3 for normalized endpoints -/

section Step2

variable {κ : Rd d → ℝ}

theorem sum_abs_eparam_sub_ge {δ : ℝ} (hδ : 0 < δ) (c c' : Config d) :
    δ⁻¹ * (‖cx c - cx c'‖ + ‖cy c - cy c'‖) ≤ ∑ k, |eparam δ c k - eparam δ c' k| := by
  rw [Fin.sum_univ_add]
  simp only [eparam, Fin.append_left, Fin.append_right]
  have h1 : ‖cx c - cx c'‖ ≤ ∑ j : Fin d, |(cx c).ofLp j - (cx c').ofLp j| := by
    have := HigherDimLFPP.Var.norm_le_sum_abs (cx c - cx c')
    simpa using this
  have h2 : ‖cy c - cy c'‖ ≤ ∑ j : Fin d, |(cy c - e₁ d).ofLp j - (cy c' - e₁ d).ofLp j| := by
    have := HigherDimLFPP.Var.norm_le_sum_abs (cy c - cy c')
    have e : ∀ j : Fin d, (cy c - e₁ d).ofLp j - (cy c' - e₁ d).ofLp j =
        (cy c - cy c').ofLp j := fun j => by simp
    simp only [e]
    exact this
  have e1 : ∀ j : Fin d, |(cx c).ofLp j / δ - (cx c').ofLp j / δ| =
      δ⁻¹ * |(cx c).ofLp j - (cx c').ofLp j| := fun j => by
    rw [← sub_div, abs_div, abs_of_pos hδ, div_eq_inv_mul]
  have e2 : ∀ j : Fin d, |(cy c - e₁ d).ofLp j / δ - (cy c' - e₁ d).ofLp j / δ| =
      δ⁻¹ * |(cy c - e₁ d).ofLp j - (cy c' - e₁ d).ofLp j| := fun j => by
    rw [← sub_div, abs_div, abs_of_pos hδ, div_eq_inv_mul]
  rw [Finset.sum_congr rfl fun j _ => e1 j, Finset.sum_congr rfl fun j _ => e2 j,
    ← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
  exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) (inv_nonneg.2 hδ.le)

theorem norm_eparam_sub_le {δ ρ : ℝ} (hδ : 0 < δ) {c c' : Config d} (hcx : ‖cx c‖ ≤ ρ * δ)
    (hcy : ‖cy c - e₁ d‖ ≤ ρ * δ) (hcx' : ‖cx c'‖ ≤ ρ * δ) (hcy' : ‖cy c' - e₁ d‖ ≤ ρ * δ) :
    ‖eparam δ c - eparam δ c'‖ ≤ 2 * ρ := by
  have hρ : 0 ≤ ρ := by
    have := (norm_nonneg _).trans hcx
    exact nonneg_of_mul_nonneg_left this hδ
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  rw [Real.norm_eq_abs, Pi.sub_apply]
  have hb : ∀ v w : Rd d, ‖v‖ ≤ ρ * δ → ‖w‖ ≤ ρ * δ → ∀ j : Fin d,
      |v.ofLp j / δ - w.ofLp j / δ| ≤ 2 * ρ := by
    intro v w hv hw j
    rw [← sub_div, abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
    have h1 : |v.ofLp j| ≤ ‖v‖ := by
      have := PiLp.norm_apply_le v j
      rwa [Real.norm_eq_abs] at this
    have h2 : |w.ofLp j| ≤ ‖w‖ := by
      have := PiLp.norm_apply_le w j
      rwa [Real.norm_eq_abs] at this
    have := abs_sub (v.ofLp j) (w.ofLp j)
    linarith
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp only [eparam, Fin.append_left]
    exact hb _ _ hcx hcx' j
  · simp only [eparam, Fin.append_right]
    exact hb _ _ hcy hcy' j

/-- **Lemma 4.3 for normalized endpoints** (HA3 D5, Steps 1–2): there is `C_* = C_*(d, κ)` such
that for all `n`, `τ, u ∈ (0,1)` and `η > 0` there is `δ₀ > 0` with: for `0 < δ < δ₀` and every
finite family `F` of configurations `([x, y], Q)` with `|x|, |y - e₁| ≤ 4√d δ` and
`Q ∈ G_K(x, y)`, `E max_F (Y - (1-τ)E_δ) ≤ (1+u)^{2/3}(1-τ)^{-1/3} A_{n,d} + C_* u^{-1/2} + η`
for the all-scale covariance `δ⁻¹ Λ`. -/
theorem step2 (hd2 : 2 ≤ d) (hκ : IsLFPPKernel κ) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ n : ℕ, ∀ τ ∈ Ioo (0 : ℝ) 1, ∀ u ∈ Ioo (0 : ℝ) 1, ∀ η > 0,
      ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ F : Finset (Config d),
        (∀ c ∈ F, NormCfg n (4 * Real.sqrt d * δ) c) →
        gaussianExpectedMax F (fun c c' => δ⁻¹ * scaleCov κ (Ioi 0) (polyMeasure c.1)
            (polyMeasure c.2) (polyMeasure c'.1) (polyMeasure c'.2))
          (fun c => -((1 - τ) * (δ ^ 2)⁻¹ * Real.log (polyLen c.2 / polyLen c.1))) ≤
          (1 + u) ^ (2 / 3 : ℝ) * (1 - τ) ^ (-(1 / 3) : ℝ) * (A n d).toReal +
            Cs * u ^ (-(1 / 2) : ℝ) + η := by
  classical
  have hd : 0 < d := by omega
  obtain ⟨C, hC0, hC⟩ := transport_var_bound hκ 3
  set ρd : ℝ := 4 * Real.sqrt d with hρd
  have hρd0 : 0 < ρd := by positivity
  set CB : ℝ := 20 * Real.sqrt 5 * Real.sqrt ((d + d : ℕ) : ℝ) *
    Real.sqrt ((((d + d : ℕ) : ℝ) + 1) * (2 * ρd)) with hCB
  have hCB0 : 0 ≤ CB := by positivity
  refine ⟨Real.sqrt (2 * (1600 * C)) * CB, by positivity, fun n τ hτ u hu η hη => ?_⟩
  have hα : 0 < Real.sqrt (1 + u) := Real.sqrt_pos.2 (by linarith [hu.1])
  have hβ : 0 < 1 - τ := by linarith [hτ.2]
  obtain ⟨δ₁, hδ₁, hS1⟩ := step1 hd2 hκ n hα hβ hη
  refine ⟨min δ₁ (1 / (8 * ρd)), lt_min hδ₁ (by positivity), fun δ hδ F hF => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδρ : ρd * δ ≤ 1 / 8 := by
    have h := hδ.2.le.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hF' : ∀ c ∈ F, NormCfg n (ρd * δ) c := fun c hc => hF c hc
  -- the three kernels
  set CX : Config d → Config d → ℝ := fun c c' => δ⁻¹ * scaleCov κ (Ioi 0) (polyMeasure c.1)
    (polyMeasure c.2) (polyMeasure c'.1) (polyMeasure c'.2) with hCX
  set C₁ : Config d → Config d → ℝ := fun c c' =>
    zKer κ (Real.sqrt (1 + u)) δ (shapeOf c) (shapeOf c') with hC₁
  set C₂ : Config d → Config d → ℝ := fun c c' =>
    (1 + u⁻¹) * (1600 * C) * bmCov (eparam δ c) (eparam δ c') with hC₂
  have hPX : PSDOn F CX :=
    HigherDimLFPP.Var.psdOn_const_mul (show PSDOn F (fun c c' => ⟪cfgV κ c, cfgV κ c'⟫) from
      LQGDimension.posSemidef_gramOn F (cfgV κ)) (inv_nonneg.2 hδ0.le)
  have hP₁ : PSDOn F C₁ := psdOn_comp shapeOf (psdOn_zKer (F.image shapeOf) _ hδ0.le)
  have hP₂ : PSDOn F C₂ := HigherDimLFPP.Var.psdOn_const_mul (psdOn_bmCov F (eparam δ))
    (by have := hu.1; positivity)
  -- the comparison of canonical distances (Step 2b)
  have hdist : ∀ c ∈ F, ∀ c' ∈ F, CX c c + CX c' c' - 2 * CX c c' ≤
      (C₁ c c + C₁ c' c' - 2 * C₁ c c') + (C₂ c c + C₂ c' c' - 2 * C₂ c c') := by
    intro c hc c' hc'
    have e1 : CX c c + CX c' c' - 2 * CX c c' = δ⁻¹ * ‖cfgV κ c - cfgV κ c'‖ ^ 2 := by
      have g1 : CX c c = δ⁻¹ * ⟪cfgV κ c, cfgV κ c⟫ := rfl
      have g2 : CX c' c' = δ⁻¹ * ⟪cfgV κ c', cfgV κ c'⟫ := rfl
      have g3 : CX c c' = δ⁻¹ * ⟪cfgV κ c, cfgV κ c'⟫ := rfl
      rw [g1, g2, g3, norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      ring
    have e2 : C₁ c c + C₁ c' c' - 2 * C₁ c c' = (1 + u) * (δ⁻¹ *
        ‖shapeV κ (shapeOf c) - shapeV κ (shapeOf c')‖ ^ 2) := by
      simp only [hC₁]
      rw [zKer_dist, Real.sq_sqrt (by linarith [hu.1])]
    have e3 : C₂ c c + C₂ c' c' - 2 * C₂ c c' =
        (1 + u⁻¹) * (1600 * C) * ∑ k, |eparam δ c k - eparam δ c' k| := by
      simp only [hC₂]
      rw [← bmCov_dist]
      ring
    rw [e1, e2, e3]
    have h := norm_cfgV_sub_sq_le hd hκ hC (hρ := hδρ) hu.1 (hF' c hc) (hF' c' hc')
    have hs := sum_abs_eparam_sub_ge hδ0 c c'
    have hu0 : 0 ≤ (1 + u⁻¹) * (1600 * C) := by have := hu.1; positivity
    calc δ⁻¹ * ‖cfgV κ c - cfgV κ c'‖ ^ 2
        ≤ δ⁻¹ * ((1 + u) * ‖shapeV κ (shapeOf c) - shapeV κ (shapeOf c')‖ ^ 2 +
          (1 + u⁻¹) * (1600 * C * (‖cx c - cx c'‖ + ‖cy c - cy c'‖))) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.2 hδ0.le)
      _ = (1 + u) * (δ⁻¹ * ‖shapeV κ (shapeOf c) - shapeV κ (shapeOf c')‖ ^ 2) +
          (1 + u⁻¹) * (1600 * C) * (δ⁻¹ * (‖cx c - cx c'‖ + ‖cy c - cy c'‖)) := by ring
      _ ≤ _ := by gcongr
  -- the drift is the penalty of the shape
  have hdrift : ∀ c ∈ F, -((1 - τ) * (δ ^ 2)⁻¹ * Real.log (polyLen c.2 / polyLen c.1)) =
      -((1 - τ) * eDelta δ (shapeOf c)) + 0 := by
    intro c hc
    obtain ⟨x, y, h1, -, -, -, -, hxy, hr1, -, -, -, -, -, hQmap⟩ := (hF' c hc).facts hd hδρ
    have hr : 0 < ‖y - x‖ := by linarith
    have hlen : polyLen c.2 = ‖y - x‖ * polyLen (shapeOf c) := by
      rw [← hQmap, simOf_eq, polyLen_map_simAffine x hr]
    rw [hlen, h1, polyLen_pair, mul_div_cancel_left₀ _ hr.ne', eDelta, add_zero]
    ring
  rw [gEM_congr_drift F _ hdrift]
  have hsplit := gEM_le_add_of_dist F hPX hP₁ hP₂ (fun c => -((1 - τ) * eDelta δ (shapeOf c)))
    (fun _ => 0) hdist
  -- the shape part (Step 1)
  have hshape : gaussianExpectedMax F C₁ (fun c => -((1 - τ) * eDelta δ (shapeOf c))) ≤
      Real.sqrt (1 + u) ^ (4 / 3 : ℝ) * (1 - τ) ^ (-1 / 3 : ℝ) * (A n d).toReal + η := by
    rw [hC₁, ← HigherDimLFPP.Var.gEM_image F shapeOf (zKer κ (Real.sqrt (1 + u)) δ)
      (fun Q => -((1 - τ) * eDelta δ Q)) (psdOn_zKer _ _ hδ0.le)]
    refine hS1 δ ⟨hδ0, hδ.2.trans_le (min_le_left _ _)⟩ _ fun Q hQ => ?_
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hQ
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hQ₀, -⟩ := (hF' c hc).facts hd hδρ
    exact hQ₀
  -- the endpoint part (the Brownian process)
  have hend : gaussianExpectedMax F C₂ (fun _ => 0) ≤
      Real.sqrt (2 * (1600 * C)) * CB * u ^ (-(1 / 2) : ℝ) := by
    set s := Real.sqrt ((1 + u⁻¹) * (1600 * C)) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hss : s ^ 2 = (1 + u⁻¹) * (1600 * C) := Real.sq_sqrt (by have := hu.1; positivity)
    have e1 : gaussianExpectedMax F C₂ (fun _ => 0) =
        s * gaussianExpectedMax (F.image (eparam δ)) (fun p q => bmCov p q) (fun _ => 0) := by
      have hpsd : PSDOn (F.image (eparam δ)) (fun p q => bmCov p q) :=
        psdOn_bmCov _ (fun p => p)
      rw [HigherDimLFPP.Var.gEM_image F (eparam δ) (fun p q => bmCov p q) (fun _ => 0) hpsd,
        ← HigherDimLFPP.Var.gEM_smul F _ (psdOn_comp (eparam δ) hpsd) _ hs0]
      refine LQGDimension.Subadd.gEM_congr F (fun c _ c' _ => ?_) (fun c _ => ?_)
      · simp only [hC₂, hss]
      · simp only [mul_zero]
    have hdiam : ∀ p ∈ F.image (eparam δ), ∀ q ∈ F.image (eparam δ), ‖p - q‖ ≤ 2 * ρd := by
      intro p hp q hq
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hq
      obtain ⟨x, y, -, hcx, hcy, hx, hy, -⟩ := (hF' c hc).facts hd hδρ
      obtain ⟨x', y', -, hcx', hcy', hx', hy', -⟩ := (hF' c' hc').facts hd hδρ
      exact norm_eparam_sub_le hδ0 (by rw [hcx]; exact hx) (by rw [hcy]; exact hy)
        (by rw [hcx']; exact hx') (by rw [hcy']; exact hy')
    have hB := gEM_bmCov_le (F.image (eparam δ)) id hdiam
    rw [e1]
    have hsle : s ≤ Real.sqrt (2 * (1600 * C)) * u ^ (-(1 / 2) : ℝ) := by
      have hu0 := hu.1
      have h1 : (1 + u⁻¹) * (1600 * C) ≤ 2 * (1600 * C) * u⁻¹ := by
        have : 1 + u⁻¹ ≤ 2 * u⁻¹ := by
          have : 1 ≤ u⁻¹ := one_le_inv_iff₀.2 ⟨hu0, hu.2.le⟩
          linarith
        nlinarith
      calc s ≤ Real.sqrt (2 * (1600 * C) * u⁻¹) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt (2 * (1600 * C)) * u ^ (-(1 / 2) : ℝ) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_inv, Real.rpow_neg hu0.le,
            Real.sqrt_eq_rpow u]
    calc s * gaussianExpectedMax (F.image (eparam δ)) (fun p q => bmCov p q) (fun _ => 0)
        ≤ s * CB := mul_le_mul_of_nonneg_left hB hs0
      _ ≤ (Real.sqrt (2 * (1600 * C)) * u ^ (-(1 / 2) : ℝ)) * CB :=
          mul_le_mul_of_nonneg_right hsle hCB0
      _ = Real.sqrt (2 * (1600 * C)) * CB * u ^ (-(1 / 2) : ℝ) := by ring
  -- exponents
  have hexp : Real.sqrt (1 + u) ^ (4 / 3 : ℝ) = (1 + u) ^ (2 / 3 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith [hu.1])]
    norm_num
  have hexp' : (1 - τ) ^ (-1 / 3 : ℝ) = (1 - τ) ^ (-(1 / 3) : ℝ) := by norm_num
  rw [hexp, hexp'] at hshape
  linarith

end Step2

end HigherDimLFPP.Upper
