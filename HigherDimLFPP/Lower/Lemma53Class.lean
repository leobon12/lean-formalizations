import HigherDimLFPP.Lower.Lemma53Core

/-!
# Lemma 5.3 (ii): the normalized tilted replacement stays in `C_δ` (source §5.2, Step 2)

Packet P-L3, target T3 (audit HA4, "Details for later use" D3, D6 Step 2; findings HA4-3,
HA4-5, HA4-10).

For any good `LParams` `P` (in particular P-L4's construction `D.lp δ N`) and a finitely
supported probability `μ`, writing `S = √(2 log 2(J+1))` and `ε = (J+1)(e^{ζ² log(1/q)/2} - 1)`:

* `LParams.abs_integral_tiltH_sub_le`: for a weight `0 ≤ h ≤ 1` (`h = 1` or the prefix weight
  `1_{z₁ ≤ x}`), `|E ∫ h e^{ζH} dν_{I,μ} - E ν_{I,μ}(h)| ≤ ζσS + ε` as soon as all
  `⟨H, h ν_{j,μ}⟩` have standard deviation `≤ σ` (the prefix estimate (K5) is the case
  `σ² = C ρ` of (3.16)); no supremum over `x` (finding HA4-5) or over a box (HA4-4).
* `LParams.tmap_props`: if `ζσS + ε ≤ 1/3`, then `T μ` (P-L2a's `Tmap`, (5.14)) is a finitely
  supported probability carried by `⋃ T_i^j(supp μ)`, and its horizontal distribution function
  is within `3(ζσS + ε)` of the mixture `Σ_j P(I = j) F_{(ν_{j,μ})_x}` (the normalization (5.20);
  P-L1's `abs_div_sub_le`).  This is the input of P-L1's `inCDelta_of_hCDF_close`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

open LQGDimension (gaussianExpectedMax)

variable {d : ℕ} {κ : Rd d → ℝ}

namespace LParams

variable {P : LParams d}

/-- The tilted weights are integrable on the white-noise space (dominated by the total mass). -/
theorem integrable_tiltW_wn (hP : P.Good) {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    {W : WN d → Ω → ℝ} (hW : IsWhiteNoise Pr W) {Sμ : Finset (Rd d)} {w : Rd d → ℝ}
    (hw : ∀ z ∈ Sμ, 0 ≤ w z) (p : Rd d) :
    Integrable (fun ω => P.tiltW Sμ w (fun t => W (triVec κ t) ω) p) Pr := by
  refine Integrable.mono' (integrable_tiltH (κ := κ) hP hW hw (h := fun _ => 1)
    (fun _ => zero_le_one) fun _ => le_rfl) ?_ (Eventually.of_forall fun ω => ?_)
  · exact ((hP.measurable_tiltW Sμ w p).comp
      (LParams.measurable_wnField (κ := κ) hW)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (tiltW_nonneg hw _ p), P.tiltH_one]
    by_cases hp : p ∈ P.stepPts Sμ
    · rw [← sum_tiltW]
      exact Finset.single_le_sum (f := fun p => P.tiltW Sμ w (fun t => W (triVec κ t) ω) p)
        (fun p _ => tiltW_nonneg hw _ p) hp
    · rw [tiltW_eq_zero_of_not_mem w _ hp]
      exact tiltMass_nonneg hw _

/-- **The exponential weighting changes `E ν_{I,μ}(h)` by
`≤ ζσ√(2 log 2(J+1)) + (J+1)(q^{-ζ²/2} - 1)`** (HA4 D6 Step 2): for `0 ≤ h ≤ 1` such that all
pairings `⟨H, h ν_{j,μ}⟩` have standard deviation `≤ σ`. -/
theorem abs_integral_tiltH_sub_le (hP : P.Good) (hκ : IsLFPPKernel κ) {Sμ : Finset (Rd d)}
    {w : Rd d → ℝ} (hμ : IsFinProb Sμ w) {h : Rd d → ℝ} (hh : ∀ p, 0 ≤ h p)
    (hh1 : ∀ p, h p ≤ 1) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : ∀ j, ‖bandVecM κ (Ioo (P.ρ * P.q) P.ρ) (P.replM Sμ w h j) 0‖ ≤ σ) (hζ : 0 ≤ P.ζ) :
    |∫ ω, P.tiltH Sμ w h (fun t => W₀ d (triVec κ t) ω) ∂LQGDimension.ExistAsm.stdP -
        ∫ ω, P.cdfW Sμ w h (P.sel (fun t => W₀ d (triVec κ t) ω)) ∂LQGDimension.ExistAsm.stdP| ≤
      P.ζ * (σ * Real.sqrt (2 * Real.log (2 * ((P.J : ℝ) + 1)))) +
        ((P.J : ℝ) + 1) * (Real.exp (P.ζ ^ 2 * Real.log (1 / P.q) / 2) - 1) := by
  have hW := isWhiteNoise_W₀ d
  have := hW.isProbabilityMeasure
  have hρq : 0 < P.ρ * P.q := mul_pos hP.ρ_pos hP.q_pos
  set v : Fin (P.J + 1) → WN d := fun j => bandVecM κ (Ioo (P.ρ * P.q) P.ρ) (P.replM Sμ w h j) 0
    with hv
  have hlin : ∀ᵐ ω ∂LQGDimension.ExistAsm.stdP, ∀ j,
      P.linW Sμ w h j (fun t => W₀ d (triVec κ t) ω) = W₀ d (v j) ω :=
    ae_all_iff.2 fun j => P.ae_linW_eq hκ hW hρq hμ.1 hh j
  set B : (ℕ → ℝ) → ℝ := fun ω => P.ζ * (⨆ j, |W₀ d (v j) ω|) +
    ∑ j, P.remW Sμ w (fun _ => 1) j (fun t => W₀ d (triVec κ t) ω) with hB
  have iT := integrable_tiltH (κ := κ) hP hW hμ.1 hh hh1
  have iC := integrable_of_sel (κ := κ) hP hW (fun j => P.cdfW Sμ w h j)
  have iB : Integrable B LQGDimension.ExistAsm.stdP :=
    ((integrable_iSup_abs_W₀ v).const_mul _).fun_add
      (integrable_finsetSum _ fun j _ => P.integrable_remW Sμ w hW _ j)
  have hpt : ∀ᵐ ω ∂LQGDimension.ExistAsm.stdP,
      |P.tiltH Sμ w h (fun t => W₀ d (triVec κ t) ω) -
        P.cdfW Sμ w h (P.sel (fun t => W₀ d (triVec κ t) ω))| ≤ B ω := by
    filter_upwards [hlin] with ω hω
    set Y := fun t => W₀ d (triVec κ t) ω
    rw [P.tiltH_eq, add_assoc, add_sub_cancel_left]
    have h1 : |P.linW Sμ w h (P.sel Y) Y| ≤ ⨆ j, |W₀ d (v j) ω| := by
      rw [hω]
      exact le_ciSup (f := fun j => |W₀ d (v j) ω|) (Finite.bddAbove_range _) _
    have h2 := P.remW_sel_le hμ.1 hh1 Y
    have h3 := P.remW_nonneg hμ.1 hh (P.sel Y) Y
    calc |P.ζ * P.linW Sμ w h (P.sel Y) Y + P.remW Sμ w h (P.sel Y) Y|
        ≤ |P.ζ * P.linW Sμ w h (P.sel Y) Y| + |P.remW Sμ w h (P.sel Y) Y| := abs_add_le _ _
      _ = P.ζ * |P.linW Sμ w h (P.sel Y) Y| + P.remW Sμ w h (P.sel Y) Y := by
          rw [abs_mul, abs_of_nonneg hζ, abs_of_nonneg h3]
      _ ≤ B ω := add_le_add (mul_le_mul_of_nonneg_left h1 hζ) h2
  rw [← integral_sub iT iC]
  refine (abs_integral_le_integral_abs).trans ((integral_mono_ae (iT.sub iC).abs iB hpt).trans ?_)
  rw [hB, integral_add ((integrable_iSup_abs_W₀ v).const_mul _)
      (integrable_finsetSum _ fun j _ => P.integrable_remW Sμ w hW _ j),
    integral_const_mul, integral_finsetSum _ fun j _ => P.integrable_remW Sμ w hW _ j,
    Finset.sum_congr rfl fun j _ => P.integral_remW_one hκ hW hμ hP.K_pos hP.ρ_pos hP.q_pos
      hP.q_le_one j, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have habs := integral_iSup_abs_W_le hW v hσ0 hσ
  rw [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at habs
  push_cast
  exact add_le_add (mul_le_mul_of_nonneg_left habs hζ) le_rfl

end LParams

theorem replCDF_nonneg {K : ℕ} {q : ℝ} {v : ℕ → Rd d} {S : Finset (Rd d)} {w : Rd d → ℝ}
    (hw : ∀ z ∈ S, 0 ≤ w z) (x : ℝ) : 0 ≤ replCDF K q v S w x := by
  unfold replCDF
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
  rw [pushCDF_eq_sum_ite]
  exact Finset.sum_nonneg fun z hz => by split_ifs <;> [exact hw z hz; exact le_rfl]

theorem replCDF_le_one {K : ℕ} (hK : 0 < K) {q : ℝ} {v : ℕ → Rd d} {S : Finset (Rd d)}
    {w : Rd d → ℝ} (hμ : IsFinProb S w) (x : ℝ) : replCDF K q v S w x ≤ 1 := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  unfold replCDF
  have h : ∀ i ∈ Finset.range K, pushCDF S w (edgeSim q v i).app x ≤ 1 := fun i _ => by
    rw [pushCDF_eq_sum_ite, ← hμ.2]
    exact Finset.sum_le_sum fun z hz => by split_ifs <;> [exact le_rfl; exact hμ.1 z hz]
  calc 1 / (K : ℝ) * ∑ i ∈ Finset.range K, pushCDF S w (edgeSim q v i).app x
      ≤ 1 / (K : ℝ) * ∑ _i ∈ Finset.range K, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) (by positivity)
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        field_simp

namespace LParams

variable {P : LParams d}

/-- **Lemma 5.3 (ii), the probabilistic part** (HA4 D6 Step 2, (5.20)): `T μ` is a finitely
supported probability carried by `⋃_{j, i} T_i^j(supp μ)`, and with `p_j = P(I = j)` its
horizontal distribution function is within `3 η` of `Σ_j p_j F_{(ν_{j,μ})_x}`,
`η = ζσ√(2 log 2(J+1)) + (J+1)(e^{ζ² log(1/q)/2} - 1)`, whenever all prefix pairings
`⟨H, ν_{j,μ}|_{z₁ ≤ x}⟩` and `⟨H, ν_{j,μ}⟩` have standard deviation `≤ σ` and `η ≤ 1/3`. -/
theorem tmap_props (hP : P.Good) (hκ : IsLFPPKernel κ) {Sμ : Finset (Rd d)} {w : Rd d → ℝ}
    (hμ : IsFinProb Sμ w) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσx : ∀ x : ℝ, ∀ j, ‖bandVecM κ (Ioo (P.ρ * P.q) P.ρ) (P.replM Sμ w (preW x) j) 0‖ ≤ σ)
    (hσ1 : ∀ j, ‖bandVecM κ (Ioo (P.ρ * P.q) P.ρ) (P.replM Sμ w (fun _ => 1) j) 0‖ ≤ σ)
    (hζ : 0 ≤ P.ζ)
    (hsmall : P.ζ * (σ * Real.sqrt (2 * Real.log (2 * ((P.J : ℝ) + 1)))) +
      ((P.J : ℝ) + 1) * (Real.exp (P.ζ ^ 2 * Real.log (1 / P.q) / 2) - 1) ≤ 1 / 3) :
    IsFinProb (P.stepPts Sμ) (P.Tmap κ Sμ w) ∧
      (∀ z' ∈ P.stepPts Sμ, P.Tmap κ Sμ w z' ≠ 0 →
        ∃ j, ∃ i < P.K, ∃ z ∈ Sμ, w z ≠ 0 ∧ z' = (edgeSim P.q (P.v j) i).app z) ∧
      ∃ p : Fin (P.J + 1) → ℝ, (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1 ∧
        ∀ x, |hCDF (P.stepPts Sμ) (P.Tmap κ Sμ w) x -
            ∑ j, p j * replCDF P.K P.q (P.v j) Sμ w x| ≤
          3 * (P.ζ * (σ * Real.sqrt (2 * Real.log (2 * ((P.J : ℝ) + 1)))) +
            ((P.J : ℝ) + 1) * (Real.exp (P.ζ ^ 2 * Real.log (1 / P.q) / 2) - 1)) := by
  classical
  have hW := isWhiteNoise_W₀ d
  have := hW.isProbabilityMeasure
  set η := P.ζ * (σ * Real.sqrt (2 * Real.log (2 * ((P.J : ℝ) + 1)))) +
    ((P.J : ℝ) + 1) * (Real.exp (P.ζ ^ 2 * Real.log (1 / P.q) / 2) - 1) with hη
  set m := ∫ Y, P.tiltMass Sμ w Y ∂gLawD κ (P.stepTris Sμ) with hm
  have hm_wn : m = ∫ ω, P.tiltMass Sμ w (fun t => W₀ d (triVec κ t) ω)
      ∂LQGDimension.ExistAsm.stdP := hP.integral_tiltMass_eq_whiteNoise κ hκ hW Sμ w
  -- the total mass
  have hm1 : |m - 1| ≤ η := by
    have h := P.abs_integral_tiltH_sub_le hP hκ hμ (h := fun _ => 1) (fun _ => zero_le_one)
      (fun _ => le_rfl) hσ0 hσ1 hζ
    have e1 : ∫ ω, P.tiltH Sμ w (fun _ => 1) (fun t => W₀ d (triVec κ t) ω)
        ∂LQGDimension.ExistAsm.stdP = m := by
      rw [hm_wn]
      simp only [P.tiltH_one]
    have e2 : ∫ ω, P.cdfW Sμ w (fun _ => 1) (P.sel (fun t => W₀ d (triVec κ t) ω))
        ∂LQGDimension.ExistAsm.stdP = 1 := by
      simp only [P.cdfW_one hμ hP.K_pos]
      rw [integral_const, probReal_univ, one_smul]
    rwa [e1, e2] at h
  have hm23 : 2 / 3 ≤ m := by linarith [(abs_le.1 hm1).1]
  have hmpos : 0 < m := by linarith
  -- the law of the selector
  set p : Fin (P.J + 1) → ℝ := fun j => ∫ ω, (if P.sel (fun t => W₀ d (triVec κ t) ω) = j
    then (1 : ℝ) else 0) ∂LQGDimension.ExistAsm.stdP with hp
  have ip : ∀ j, Integrable (fun ω => if P.sel (fun t => W₀ d (triVec κ t) ω) = j
      then (1 : ℝ) else 0) LQGDimension.ExistAsm.stdP := fun j =>
    integrable_of_sel (κ := κ) hP hW (fun i => if i = j then (1 : ℝ) else 0)
  have hp0 : ∀ j, 0 ≤ p j := fun j => integral_nonneg fun ω => by split_ifs <;> norm_num
  have hp1 : ∑ j, p j = 1 := by
    rw [hp, ← integral_finsetSum _ fun j _ => ip j]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [integral_const, probReal_univ, one_smul]
  have hcdf : ∀ x, ∫ ω, P.cdfW Sμ w (preW x) (P.sel (fun t => W₀ d (triVec κ t) ω))
      ∂LQGDimension.ExistAsm.stdP = ∑ j, p j * replCDF P.K P.q (P.v j) Sμ w x := by
    intro x
    have e : ∀ ω, P.cdfW Sμ w (preW x) (P.sel (fun t => W₀ d (triVec κ t) ω)) =
        ∑ j, (if P.sel (fun t => W₀ d (triVec κ t) ω) = j then (1 : ℝ) else 0) *
          P.cdfW Sμ w (preW x) j := fun ω => by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [e]
    rw [integral_finsetSum _ fun j _ => (ip j).mul_const _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const, P.cdfW_prefix]
  -- IsFinProb
  have htW0 : ∀ q, 0 ≤ ∫ Y, P.tiltW Sμ w Y q ∂gLawD κ (P.stepTris Sμ) := fun q =>
    integral_nonneg fun Y => tiltW_nonneg hμ.1 Y q
  have hfin : IsFinProb (P.stepPts Sμ) (P.Tmap κ Sμ w) := by
    refine ⟨fun q _ => div_nonneg (htW0 q) hmpos.le, ?_⟩
    unfold Tmap
    rw [← Finset.sum_div, ← integral_finsetSum _ fun q _ =>
      hP.integrable_tiltW κ hκ (hP.stepTris_pos Sμ) Sμ subset_rfl w q]
    simp only [sum_tiltW]
    exact div_self hmpos.ne'
  -- support
  have hsupp : ∀ z' ∈ P.stepPts Sμ, P.Tmap κ Sμ w z' ≠ 0 →
      ∃ j, ∃ i < P.K, ∃ z ∈ Sμ, w z ≠ 0 ∧ z' = (edgeSim P.q (P.v j) i).app z := by
    intro z' _ hz'
    have hne : ∫ Y, P.tiltW Sμ w Y z' ∂gLawD κ (P.stepTris Sμ) ≠ 0 := by
      intro h0
      apply hz'
      unfold Tmap
      rw [h0, zero_div]
    obtain ⟨Y, hY⟩ : ∃ Y, P.tiltW Sμ w Y z' ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hne
      simp only [hcon, integral_zero]
    unfold tiltW at hY
    have hY' := right_ne_zero_of_mul hY
    obtain ⟨i, hi, hi'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hY'
    obtain ⟨z, hz, hz'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi'
    by_cases hT : (P.T (P.sel Y) i).app z = z'
    · simp only [hT, ite_true] at hz'
      exact ⟨P.sel Y, i, Finset.mem_range.1 hi, z, hz, left_ne_zero_of_mul hz', hT.symm⟩
    · simp only [hT, ite_false] at hz'
      exact absurd rfl hz'
  refine ⟨hfin, hsupp, p, hp0, hp1, fun x => ?_⟩
  -- the prefix
  have hpre : hCDF (P.stepPts Sμ) (P.Tmap κ Sμ w) x =
      (∫ ω, P.tiltH Sμ w (preW x) (fun t => W₀ d (triVec κ t) ω) ∂LQGDimension.ExistAsm.stdP) /
        m := by
    unfold hCDF Tmap
    rw [← Finset.sum_div]
    congr 1
    simp only [P.tiltH_prefix]
    rw [integral_finsetSum _ fun q _ => integrable_tiltW_wn hP hW hμ.1 q]
    refine Finset.sum_congr rfl fun q _ => ?_
    exact hP.integral_tiltW_eq_whiteNoise κ hκ hW Sμ w q
  have hclose := P.abs_integral_tiltH_sub_le hP hκ hμ (h := preW x) (preW_nonneg x)
    (preW_le_one x) hσ0 (hσx x) hζ
  rw [hcdf x] at hclose
  have hF0 : 0 ≤ ∑ j, p j * replCDF P.K P.q (P.v j) Sμ w x :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hp0 j) (replCDF_nonneg hμ.1 x)
  have hF1 : ∑ j, p j * replCDF P.K P.q (P.v j) Sμ w x ≤ 1 := by
    rw [← hp1]
    exact Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (hp0 j)
      (replCDF_le_one hP.K_pos hμ x)
  rw [hpre]
  exact abs_div_sub_le hclose hm1 hF0 hF1 hm23

end LParams

end HigherDimLFPP.Lower
