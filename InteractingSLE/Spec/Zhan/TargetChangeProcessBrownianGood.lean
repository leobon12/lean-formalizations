/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownianLoc

/-!
# `b̃` is a Brownian motion, part 2: pathwise facts on good paths

Packet PROVE-SEC7-C9. On a good path (`IsRGood`) of a retargeted distinct word:

* the localizing times `σ_n` (`rLoc`) increase with `n` (`rLoc_mono`), are before the lifetime and before the
  separation time (`lt_sepTime_of_le_rLoc`), and exhaust `[0, τ_sep)` (`exists_forall_le_rLoc`);
* up to `σ_n` the coordinates and the Brownian path lie in the compact `rKc` (`mem_rKc_of_le_rLoc`), and
  `∫₀^{σ_n} ‖λ‖ ≤ rKb` (`integral_norm_rDensAt_le`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

namespace Retarget

/-! ### The separation time -/

/-- **A time before which the target stays strictly right of the driver is before the separation time** (the
gap is continuous before `ζ`). -/
theorem lt_sepTime_of_forall {w vk : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hc : ContinuousOn (fun s => vk s - w s) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ}) {r : ℝ≥0} (hr : (r : ℝ≥0∞) < ζ)
    (h : ∀ s ≤ r, w s < vk s) : (r : ℝ≥0∞) < sepTime w vk ζ := by
  have hopen := Coupling.isOpen_setOf_coe_lt ζ
  have hca : ContinuousAt (fun s => vk s - w s) r := hc.continuousAt (hopen.mem_nhds hr)
  have hev : ∀ᶠ s in 𝓝 r, 0 < vk s - w s ∧ (s : ℝ≥0∞) < ζ :=
    (hca.eventually (lt_mem_nhds (sub_pos.2 (h r le_rfl)))).and (hopen.mem_nhds hr)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set r' : ℝ≥0 := r + (ε / 2).toNNReal with hr'
  have hεpos : (0 : ℝ≥0) < (ε / 2).toNNReal := Real.toNNReal_pos.2 (by linarith)
  have hrr' : r < r' := lt_add_of_pos_right r hεpos
  have hinf : (r' : ℝ≥0∞) ≤ ⨅ (s : ℝ≥0) (_ : (s : ℝ≥0∞) < ζ ∧ vk s ≤ w s), (s : ℝ≥0∞) := by
    refine le_iInf₂ fun s hs => ?_
    by_contra hlt
    rw [not_le, ENNReal.coe_lt_coe] at hlt
    rcases le_or_gt s r with hsr | hsr
    · exact absurd hs.2 (not_le.2 (h s hsr))
    · have hd : dist s r < ε := by
        rw [NNReal.dist_eq]
        have h1 : (s : ℝ) - r < ε / 2 := by
          have : (s : ℝ) < r + (ε / 2).toNNReal := by exact_mod_cast hlt
          rw [Real.coe_toNNReal _ (by linarith)] at this
          linarith
        have h2 : (0 : ℝ) ≤ s - r := by have : (r : ℝ) < s := hsr; linarith
        rw [abs_of_nonneg h2]
        linarith
      have := (hball hd).1
      linarith [hs.2]
  refine lt_min hr (lt_of_lt_of_le ?_ hinf)
  exact_mod_cast hrr'

section Good

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ}
  {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

/-! ### Monotonicity in the level -/

theorem rLev_mono {nR : ℕ} {k : Fin nR} {m' n : ℕ} (hmn : m' ≤ n) (st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :
    rLev k m' st ≤ rLev k n st := by
  have hc : ((m' : ℝ)) ≤ n := by exact_mod_cast hmn
  have hδ : 1 / ((n : ℝ) + 1) ≤ 1 / ((m' : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  unfold rLev
  refine min_le_min (min_le_min (by linarith) (by linarith)) (neg_le_neg (Finset.sum_le_sum fun i _ => ?_))
  exact max_le_max le_rfl (by linarith)

theorem rLoc_mono (hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω) (hTm : ∀ ω, Monotone (T · ω))
    (ω : Ω) : Monotone fun n => rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω := by
  intro m' n hmn
  have h := Sec2.TwoSeed.coe_capTime (fun ω => min (m' : ℝ≥0) (T m' ω))
    (fun ω => min (rHit (LP.retargetIdx j m) G W VL VR ζ m' ω)
      (MathFin.exitTime (Sec2.TwoSeed.brownG G B) m' ω)) ω
  have h' := Sec2.TwoSeed.coe_capTime (fun ω => min (n : ℝ≥0) (T n ω))
    (fun ω => min (rHit (LP.retargetIdx j m) G W VL VR ζ n ω)
      (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) ω
  show rLoc (LP.retargetIdx j m) G T W VL VR B ζ m' ω ≤ rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω
  rw [← WithTop.coe_le_coe]
  unfold rLoc
  rw [h, h']
  have hhit : rHit (LP.retargetIdx j m) G W VL VR ζ m' ω ≤ rHit (LP.retargetIdx j m) G W VL VR ζ n ω := by
    by_cases hω : ω ∈ G
    · simp only [rHit, hω, ↓reduceIte]
      exact hitBelow_mono_fun fun s => rLev_mono hmn _
    · simp only [rHit, hω, ↓reduceIte, le_refl]
  refine min_le_min ?_ (min_le_min hhit (MathFin.exitTime_mono (continuous_brownG_r hgood) hmn ω))
  exact WithTop.coe_le_coe.2 (min_le_min (by exact_mod_cast hmn) (hTm ω hmn))

/-! ### Facts on one good path -/

section GoodFacts

variable {ω : Ω} {n : ℕ} (hω : IsRGood κ xL xR ρL ρR W VL VR B ζ T ω) (hωG : ω ∈ G)
include hω

theorem rLoc_lt_lifetime : (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω : ℝ≥0∞) < ζ ω :=
  lt_of_le_of_lt (by exact_mod_cast rLoc_le_T n ω) (hω.2.2.2.1 n)

include hωG in
theorem rLev_nonneg_of_lt_rLoc {r : ℝ≥0} (hr : r < rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) :
    0 ≤ rLev (LP.retargetIdx j m) n (Coupling.stateAt W VL VR r ω) := by
  by_contra hneg
  push Not at hneg
  have hrζ : (r : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hr.le) (rLoc_lt_lifetime hω)
  have h1 := Coupling.hitBelow_le (f := fun s => rLev (LP.retargetIdx j m) n (Coupling.stateAt W VL VR s ω))
    hrζ hneg
  have h2 := rLoc_le_rHit (k := LP.retargetIdx j m) (G := G) (T := T) (W := W) (VL := VL) (VR := VR) (B := B)
    (ζ := ζ) n ω
  simp only [rHit, hωG, ↓reduceIte] at h2
  exact absurd (WithTop.coe_le_coe.1 (h2.trans h1)) (not_le.2 hr)

include hωG in
/-- On `[0, σ_n]` the state is in the level-`n` box, if `σ_n > 0`. -/
theorem rLev_nonneg_of_le_rLoc (hσ0 : 0 < rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) {r : ℝ≥0}
    (hr : r ≤ rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) :
    0 ≤ rLev (LP.retargetIdx j m) n (Coupling.stateAt W VL VR r ω) := by
  set σ := rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω with hσ
  have hσζ : (σ : ℝ≥0∞) < ζ ω := rLoc_lt_lifetime hω
  rcases hr.lt_or_eq with hlt | heq
  · exact rLev_nonneg_of_lt_rLoc hω hωG hlt
  · subst heq
    have hF := hω.1.isForcePath
    have hcont : ContinuousOn (fun s => rLev (LP.retargetIdx j m) n (Coupling.stateAt W VL VR s ω))
        {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} :=
      (continuous_rLev _ n).comp_continuousOn (hF.continuousOn_w.prodMk
        ((continuousOn_pi.2 hF.continuousOn_vL).prodMk (continuousOn_pi.2 hF.continuousOn_vR)))
    have hat := hcont.continuousAt ((Coupling.isOpen_setOf_coe_lt (ζ ω)).mem_nhds hσζ)
    have : (𝓝[<] σ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hσ0⟩
    refine ge_of_tendsto (hat.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio σ))) ?_
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    exact rLev_nonneg_of_lt_rLoc hω hωG hr'

omit hω in
include hωG in
theorem abs_B_le_of_le_rLoc (hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω) {r : ℝ≥0}
    (hr0 : 0 < r) (hr : r ≤ rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) : |B r ω| ≤ n := by
  have h := MathFin.abs_le_N_of_le_exitTime (continuous_brownG_r hgood) hr0
    ((WithTop.coe_le_coe.2 hr).trans (rLoc_le_exitTime n ω))
  simpa only [Sec2.TwoSeed.brownG, hωG, ↓reduceIte] using h

include hωG in
/-- Up to `σ_n` the target is at distance `≥ δ_n` right of the driver (or `σ_n = 0`). -/
theorem le_gap_of_le_rLoc (hσ0 : 0 < rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) {r : ℝ≥0}
    (hr : r ≤ rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) :
    1 / ((n : ℝ) + 1) ≤ VR (LP.retargetIdx j m) r ω - W r ω :=
  (rLev_nonneg_iff.1 (rLev_nonneg_of_le_rLoc hω hωG hσ0 hr)).2.1

include hωG in
/-- **`σ_n` is before the separation time.** -/
theorem lt_sepTime_of_le_rLoc (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j) {r : ℝ≥0}
    (hr : r ≤ rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) :
    (r : ℝ≥0∞) < sepTime (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω) := by
  have hF := hω.1.isForcePath
  have hrζ : (r : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hr) (rLoc_lt_lifetime hω)
  refine lt_sepTime_of_forall ((hF.continuousOn_vR _).sub hF.continuousOn_w) hrζ fun s hs => ?_
  rcases (zero_le (a := rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)).lt_or_eq with hσ0 | hσ0
  · have := le_gap_of_le_rLoc hω hωG hσ0 (hs.trans hr)
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · have hs0 : s = 0 := le_antisymm (hs.trans (hr.trans hσ0.symm.le)) bot_le
    subst hs0
    obtain ⟨⟨-, -, -, hR0⟩, -, hmono⟩ := hD
    have hpos := LP.retargetPos_pos hmono hR0 hj
    rw [hF.w_zero, hF.vR_zero]
    exact hpos

end GoodFacts

/-! ### Bounds on `α`, `β`, `S` -/

section Bounds

variable {xk : ℝ} {w vk : ℝ≥0 → ℝ}

theorem abs_alpha_le (hxk : 0 < xk) {s : ℝ} (hs : 0 ≤ s) : |alpha xk w vk s| ≤ xk := by
  unfold alpha
  have hI : 0 ≤ ∫ u in (0 : ℝ)..s, (gap w vk u ^ 2)⁻¹ :=
    intervalIntegral.integral_nonneg hs fun u _ => inv_nonneg.2 (sq_nonneg _)
  rw [abs_of_pos (mul_pos hxk (Real.exp_pos _))]
  calc xk * Real.exp (-2 * ∫ u in (0 : ℝ)..s, (gap w vk u ^ 2)⁻¹) ≤ xk * 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by linarith)) hxk.le
    _ = xk := mul_one xk

theorem abs_beta_le (hxk : 0 < xk) {s c : ℝ} (hs : 0 ≤ s)
    (hc : ∀ u ∈ Icc 0 s, 0 < gap w vk u ∧ (gap w vk u)⁻¹ ≤ c) :
    |beta xk w vk s| ≤ 1 + 2 * s * xk * c ^ 3 := by
  have hb : ‖∫ u in (0 : ℝ)..s, alpha xk w vk u / gap w vk u ^ 3‖ ≤ xk * c ^ 3 * |s - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
    rw [uIoc_of_le hs] at hu
    obtain ⟨hq, hqc⟩ := hc u ⟨hu.1.le, hu.2⟩
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hq, div_eq_mul_inv, ← inv_pow]
    exact mul_le_mul (abs_alpha_le hxk hu.1.le) (pow_le_pow_left₀ (inv_nonneg.2 hq.le) hqc 3)
      (by positivity) hxk.le
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs] at hb
  unfold beta
  calc |-1 - 2 * ∫ u in (0 : ℝ)..s, alpha xk w vk u / gap w vk u ^ 3|
      ≤ |(-1 : ℝ)| + |2 * ∫ u in (0 : ℝ)..s, alpha xk w vk u / gap w vk u ^ 3| := abs_sub _ _
    _ ≤ 1 + 2 * (xk * c ^ 3 * s) := by
        rw [abs_neg, abs_one, abs_mul, abs_two]; linarith
    _ = 1 + 2 * s * xk * c ^ 3 := by ring

theorem abs_clk_le (hxk : 0 < xk) {s c : ℝ} (hs : 0 ≤ s)
    (hc : ∀ u ∈ Icc 0 s, 0 < gap w vk u ∧ (gap w vk u)⁻¹ ≤ c) :
    |clk (rate xk w vk) s| ≤ s * xk ^ 2 * c ^ 4 := by
  have hb : ‖∫ u in (0 : ℝ)..s, rate xk w vk u‖ ≤ xk ^ 2 * c ^ 4 * |s - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
    rw [uIoc_of_le hs] at hu
    obtain ⟨hq, hqc⟩ := hc u ⟨hu.1.le, hu.2⟩
    rw [Real.norm_eq_abs, rate, abs_div, abs_pow, abs_pow, abs_of_pos hq, div_eq_mul_inv, ← inv_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (abs_alpha_le hxk hu.1.le) 2)
      (pow_le_pow_left₀ (inv_nonneg.2 hq.le) hqc 4) (by positivity) (by positivity)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs] at hb
  unfold clk
  linarith

end Bounds

/-- The left force velocity is nonpositive, so its absolute integral is the displacement. -/
theorem integral_abs_two_div_L {nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {T : ℝ≥0∞}
    (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) (i : Fin nL) :
    ∫ s in (0 : ℝ)..t, |2 / (vL i s.toNNReal - w s.toNNReal)| = xL i - vL i t := by
  have heq : ∫ s in (0 : ℝ)..t, |2 / (vL i s.toNNReal - w s.toNNReal)| =
      ∫ s in (0 : ℝ)..t, -(2 / (vL i s.toNNReal - w s.toNNReal)) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    have hle := hp.vL_le_w (Sec2.toNNReal_lt_of_mem_Icc ht hs) i
    exact abs_of_nonpos (div_nonpos_of_nonneg_of_nonpos zero_le_two (sub_nonpos.2 hle))
  rw [heq, intervalIntegral.integral_neg, hp.vL_eq ht i]
  ring

/-- The right force velocity is nonnegative, so its absolute integral is the displacement. -/
theorem integral_abs_two_div_R {nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {T : ℝ≥0∞}
    (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) (i : Fin nR) :
    ∫ s in (0 : ℝ)..t, |2 / (vR i s.toNNReal - w s.toNNReal)| = vR i t - xR i := by
  have heq : ∫ s in (0 : ℝ)..t, |2 / (vR i s.toNNReal - w s.toNNReal)| =
      ∫ s in (0 : ℝ)..t, 2 / (vR i s.toNNReal - w s.toNNReal) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    have hle := hp.w_le_vR (Sec2.toNNReal_lt_of_mem_Icc ht hs) i
    exact abs_of_nonneg (div_nonneg zero_le_two (sub_nonneg.2 hle))
  rw [heq, hp.vR_eq ht i]
  ring

/-! ### The box and the density bound along a good path -/

/-- The bound on `∫₀^{σ_n} ‖λ‖`. -/
def rKb {nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (xk : ℝ) (n : ℕ) : ℝ :=
  (∑ i, (|xL i| + n)) + (∑ i, (|xR i| + n)) +
    n * (2 * xk * ((n : ℝ) + 1) ^ 2 + 2 * xk * ((n : ℝ) + 1) ^ 3 + xk ^ 2 * ((n : ℝ) + 1) ^ 4)

section GoodBox

variable {ω : Ω} {n : ℕ} (hω : IsRGood κ xL xR ρL ρR W VL VR B ζ T ω) (hωG : ω ∈ G)
  (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)
include hω hωG hD hj

omit hD hj in
/-- Up to `σ_n > 0`, `0 < q` and `q⁻¹ ≤ n + 1` on every `[0, r]`. -/
theorem gap_bounds_of_le_rLoc (hσ0 : 0 < rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) {r : ℝ≥0}
    (hr : r ≤ rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) :
    ∀ u ∈ Icc (0 : ℝ) r, 0 < gap (W · ω) (VR (LP.retargetIdx j m) · ω) u ∧
      (gap (W · ω) (VR (LP.retargetIdx j m) · ω) u)⁻¹ ≤ (n : ℝ) + 1 := by
  intro u hu
  have hur : u.toNNReal ≤ r := Sec2.toNNReal_le_of_mem_Icc hu
  have h := le_gap_of_le_rLoc hω hωG hσ0 (hur.trans hr)
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hq : 0 < gap (W · ω) (VR (LP.retargetIdx j m) · ω) u := hδ.trans_le h
  refine ⟨hq, ?_⟩
  rw [inv_le_comm₀ hq (by positivity)]
  have h' : 1 / ((n : ℝ) + 1) ≤ gap (W · ω) (VR (LP.retargetIdx j m) · ω) u := h
  rwa [one_div] at h'

/-- **Up to `σ_n` the coordinates and the Brownian path stay in the compact `rKc`.** -/
theorem mem_rKc_of_le_rLoc (hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω) {r : ℝ≥0}
    (hr : r ≤ rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) :
    (rCoordAt (LP.retargetPos xR) (LP.retargetIdx j m) (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) r,
      B r ω) ∈ rKc κ xL xR ρL ρR (LP.retargetIdx j m) (LP.retargetPos xR) n := by
  have hF := hω.1.isForcePath
  have hpos : 0 < LP.retargetPos xR := LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj
  rcases (zero_le (a := rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)).lt_or_eq with hσ0 | hσ0
  · right
    have hrζ : (r : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hr) (rLoc_lt_lifetime hω)
    have hlev := rLev_nonneg_iff.1 (rLev_nonneg_of_le_rLoc hω hωG hσ0 hr)
    simp only [Coupling.stateAt] at hlev
    have hp := hω.1.isSLEPathUpTo le_rfl
    have hdrv := drv_rCoordAt hp hrζ (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR)
    have hnorm : ‖((fun i => VL i r ω), fun i => VR i r ω)‖ ≤ n := hlev.1
    have hgb := gap_bounds_of_le_rLoc hω hωG hσ0 hr
    refine ⟨(norm_fst_le (((fun i => VL i r ω), fun i => VR i r ω) :
        (Fin nL → ℝ) × (Fin (j + 1 + m) → ℝ))).trans hnorm,
      (norm_snd_le (((fun i => VL i r ω), fun i => VR i r ω) :
        (Fin nL → ℝ) × (Fin (j + 1 + m) → ℝ))).trans hnorm, ?_, ?_, fun i => ?_, hlev.2.2, ?_, ?_, ?_⟩
    · rcases (zero_le (a := r)).lt_or_eq with hr0 | hr0
      · exact abs_B_le_of_le_rLoc hωG hgood hr0 hr
      · rw [← hr0, hω.2.2.1, abs_zero]; positivity
    · simp only [qOf]
      rw [hdrv]
      exact hlev.2.1
    · have h1 := hlev.2.1
      have h2 := hF.vL_le_w hrζ i
      simp only [rCoordAt]
      rw [abs_of_pos (by linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity])]
      linarith
    · exact abs_alpha_le hpos r.coe_nonneg
    · have := abs_beta_le hpos r.coe_nonneg hgb
      have hrn : (r : ℝ) ≤ n := by exact_mod_cast hr.trans (rLoc_le_n n ω)
      refine this.trans ?_
      simp only [betaBd]
      gcongr
    · have := abs_clk_le hpos r.coe_nonneg hgb
      have hrn : (r : ℝ) ≤ n := by exact_mod_cast hr.trans (rLoc_le_n n ω)
      refine this.trans ?_
      simp only [clkBd]
      gcongr
  · left
    have hr0 : r = 0 := le_antisymm (hr.trans hσ0.symm.le) bot_le
    subst hr0
    rw [rCoordAt_zero hF.vL_zero hF.vR_zero, hω.2.2.1]
    rfl

/-- **The density integral bound**: `∫₀^{σ_n} ‖λ‖ ≤ rKb`. -/
theorem integral_norm_rDensAt_le :
    ∫ s in (0 : ℝ)..(rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω : ℝ),
      ‖rDensAt κ xL xR ρL ρR (LP.retargetIdx j m) (LP.retargetPos xR) (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (B · ω) s‖ ≤ rKb xL xR (LP.retargetPos xR) n := by
  set σ := rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω with hσ
  have hpos : 0 < LP.retargetPos xR := LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj
  have hKb0 : 0 ≤ rKb xL xR (LP.retargetPos xR) n := by
    unfold rKb
    have h1 : 0 ≤ ∑ i, (|xL i| + (n : ℝ)) := Finset.sum_nonneg fun i _ => by positivity
    have h2 : 0 ≤ ∑ i, (|xR i| + (n : ℝ)) := Finset.sum_nonneg fun i _ => by positivity
    positivity
  rcases (zero_le (a := σ)).lt_or_eq with hσ0 | hσ0
  swap
  · rw [← hσ0, NNReal.coe_zero, intervalIntegral.integral_same]; exact hKb0
  have hσζ : (σ : ℝ≥0∞) < ζ ω := rLoc_lt_lifetime hω
  have hp := hω.1.isSLEPathUpTo le_rfl
  set C : ℝ := 2 * LP.retargetPos xR * ((n : ℝ) + 1) ^ 2 + 2 * LP.retargetPos xR * ((n : ℝ) + 1) ^ 3 +
    LP.retargetPos xR ^ 2 * ((n : ℝ) + 1) ^ 4 with hC
  set fL : Fin nL → ℝ → ℝ := fun i s => |2 / (VL i s.toNNReal ω - W s.toNNReal ω)| with hfL
  set fR : Fin (j + 1 + m) → ℝ → ℝ := fun i s => |2 / (VR i s.toNNReal ω - W s.toNNReal ω)| with hfR
  have hiL : ∀ i, IntervalIntegrable (fL i) volume 0 σ := fun i => by
    have := ((hp.integrable_gapL hσζ i).const_mul (-2)).abs
    refine this.congr fun s _ => ?_
    simp only [hfL]
    rw [div_eq_mul_inv, ← neg_sub (W s.toNNReal ω), inv_neg]
    congr 1; ring
  have hiR : ∀ i, IntervalIntegrable (fR i) volume 0 σ := fun i => by
    have := ((hp.integrable_gapR hσζ i).const_mul (-2)).abs
    refine this.congr fun s _ => ?_
    simp only [hfR]
    rw [div_eq_mul_inv, ← neg_sub (W s.toNNReal ω), inv_neg]
    congr 1; ring
  have hbound : ∀ s ∈ Icc (0 : ℝ) σ, ‖rDensAt κ xL xR ρL ρR (LP.retargetIdx j m) (LP.retargetPos xR) (W · ω)
      (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) s‖ ≤ (∑ i, fL i s) + (∑ i, fR i s) + C := by
    intro s hs
    have hsσ : s.toNNReal ≤ σ := Sec2.toNNReal_le_of_mem_Icc hs
    have hsζ : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (by exact_mod_cast hsσ) hσζ
    have hgb := gap_bounds_of_le_rLoc hω hωG hσ0 le_rfl s hs
    have hdrv := drv_rCoordAt hp hsζ (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR)
    have hq : qOf κ xL xR ρL ρR (LP.retargetIdx j m)
        (rCoordAt (LP.retargetPos xR) (LP.retargetIdx j m) (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
          s.toNNReal, B s.toNNReal ω) = gap (W · ω) (VR (LP.retargetIdx j m) · ω) s := by
      simp only [qOf, hdrv, gap]; rfl
    have hα := abs_alpha_le (w := (W · ω)) (vk := (VR (LP.retargetIdx j m) · ω)) hpos
      (s.toNNReal).coe_nonneg
    set a := alpha (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω) (s.toNNReal : ℝ) with ha
    set q := gap (W · ω) (VR (LP.retargetIdx j m) · ω) s with hqdef
    have hqi : |q⁻¹| ≤ (n : ℝ) + 1 := by rw [abs_of_pos (inv_pos.2 hgb.1)]; exact hgb.2
    have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have e1 : |(-2) * a / q ^ 2| ≤ 2 * LP.retargetPos xR * ((n : ℝ) + 1) ^ 2 := by
      rw [div_eq_mul_inv, ← inv_pow, abs_mul, abs_mul, abs_pow]
      have := pow_le_pow_left₀ (abs_nonneg _) hqi 2
      rw [abs_neg, abs_two]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hα (by norm_num)) this (by positivity) (by positivity)
    have e2 : |(-2) * a / q ^ 3| ≤ 2 * LP.retargetPos xR * ((n : ℝ) + 1) ^ 3 := by
      rw [div_eq_mul_inv, ← inv_pow, abs_mul, abs_mul, abs_pow]
      have := pow_le_pow_left₀ (abs_nonneg _) hqi 3
      rw [abs_neg, abs_two]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hα (by norm_num)) this (by positivity) (by positivity)
    have e3 : |a ^ 2 / q ^ 4| ≤ LP.retargetPos xR ^ 2 * ((n : ℝ) + 1) ^ 4 := by
      rw [div_eq_mul_inv, ← inv_pow, abs_mul, abs_pow, abs_pow]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hα 2) (pow_le_pow_left₀ (abs_nonneg _) hqi 4)
        (by positivity) (by positivity)
    refine (norm_rcoord_le _).trans ?_
    simp only [rDensAt, dens]
    rw [hq, hdrv]
    simp only [rCoordAt, hfL, hfR]
    linarith
  have hsL : IntervalIntegrable (fun s => ∑ i, fL i s) volume 0 σ :=
    (IntervalIntegrable.sum Finset.univ fun i _ => hiL i).congr fun s _ => Finset.sum_apply s _ _
  have hsR : IntervalIntegrable (fun s => ∑ i, fR i s) volume 0 σ :=
    (IntervalIntegrable.sum Finset.univ fun i _ => hiR i).congr fun s _ => Finset.sum_apply s _ _
  have hiS : IntervalIntegrable (fun s => (∑ i, fL i s) + (∑ i, fR i s) + C) volume 0 σ :=
    (hsL.add hsR).add intervalIntegrable_const
  have hnormi : IntervalIntegrable (fun s => ‖rDensAt κ xL xR ρL ρR (LP.retargetIdx j m) (LP.retargetPos xR)
      (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) s‖) volume 0 σ :=
    (intervalIntegrable_rDensAt (hω.1.isSLEPathUpTo (sepTime_le _ _ _))
      (retargetData_of_isSLEPathUpTo (hω.1.isSLEPathUpTo (sepTime_le _ _ _)) hD hj
        fun t ht => lt_of_lt_sepTime ht) (lt_sepTime_of_le_rLoc hω hωG hD hj le_rfl)).norm
  refine (intervalIntegral.integral_mono_on σ.coe_nonneg hnormi hiS hbound).trans ?_
  rw [intervalIntegral.integral_add (hsL.add hsR) intervalIntegrable_const,
    intervalIntegral.integral_add hsL hsR,
    intervalIntegral.integral_finsetSum fun i _ => hiL i, intervalIntegral.integral_finsetSum fun i _ => hiR i,
    intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hσn : (σ : ℝ) ≤ n := by exact_mod_cast rLoc_le_n n ω
  have hlev := rLev_nonneg_iff.1 (rLev_nonneg_of_le_rLoc hω hωG hσ0 le_rfl)
  simp only [Coupling.stateAt] at hlev
  have hnorm : ‖((fun i => VL i σ ω), fun i => VR i σ ω)‖ ≤ n := hlev.1
  have hL : ∀ i, ∫ s in (0 : ℝ)..σ, fL i s ≤ |xL i| + n := fun i => by
    rw [integral_abs_two_div_L hp hσζ i]
    have h1 := (norm_le_pi_norm (fun i => VL i σ ω) i).trans ((norm_fst_le _).trans hnorm)
    rw [Real.norm_eq_abs] at h1
    linarith [le_abs_self (xL i), neg_abs_le (VL i σ ω)]
  have hR : ∀ i, ∫ s in (0 : ℝ)..σ, fR i s ≤ |xR i| + n := fun i => by
    rw [integral_abs_two_div_R hp hσζ i]
    have h1 := (norm_le_pi_norm (fun i => VR i σ ω) i).trans ((norm_snd_le _).trans hnorm)
    rw [Real.norm_eq_abs] at h1
    linarith [neg_abs_le (xR i), le_abs_self (VR i σ ω)]
  have hC0 : 0 ≤ C := by positivity
  unfold rKb
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hL i
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hR i
  nlinarith

/-- **Exhaustion**: every time before the separation time is eventually below `σ_n`. -/
theorem exists_forall_le_rLoc (hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω)
    (hTm : Monotone (T · ω)) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < sepTime (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω)) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → s ≤ rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω := by
  set k := LP.retargetIdx j m with hk
  have hF := hω.1.isForcePath
  have hsζ : (s : ℝ≥0∞) < ζ ω := hs.trans_le (sepTime_le _ _ _)
  have hp := hω.1.isSLEPathUpTo (sepTime_le (W · ω) (VR k · ω) (ζ ω))
  have hd := retargetData_of_isSLEPathUpTo hp hD hj fun t ht => lt_of_lt_sepTime ht
  have hsub : Icc (0 : ℝ≥0) s ⊆ {r : ℝ≥0 | (r : ℝ≥0∞) < ζ ω} := fun r hr =>
    lt_of_le_of_lt (by exact_mod_cast hr.2) hsζ
  have hsep : ∀ r ∈ Icc (0 : ℝ≥0) s, (r : ℝ≥0∞) < sepTime (W · ω) (VR k · ω) (ζ ω) := fun r hr =>
    lt_of_le_of_lt (by exact_mod_cast hr.2) hs
  have hne : (Icc (0 : ℝ≥0) s).Nonempty := ⟨0, le_rfl, bot_le⟩
  have hstc : ContinuousOn (fun r => ‖(Coupling.stateAt W VL VR r ω).2‖) (Icc 0 s) :=
    ((continuousOn_pi.2 hF.continuousOn_vL).prodMk (continuousOn_pi.2 hF.continuousOn_vR)).norm.mono hsub
  -- the reciprocal gaps
  set ψ : ℝ≥0 → ℝ := fun r => (VR k r ω - W r ω)⁻¹ +
    ∑ i ∈ Finset.univ.erase k, |VR k r ω - VR i r ω|⁻¹ with hψ
  have hψc : ContinuousOn ψ (Icc 0 s) := by
    refine ((((hF.continuousOn_vR k).sub hF.continuousOn_w).mono hsub).inv₀ fun r hr => ?_).add
      (continuousOn_finsetSum _ fun i hi => ((((hF.continuousOn_vR k).sub
        (hF.continuousOn_vR i)).mono hsub).abs.inv₀ fun r hr => ?_))
    · exact (sub_pos.2 (lt_of_lt_sepTime (hsep r hr))).ne'
    · exact abs_ne_zero.2 (hd.vR_ne (hsep r hr) i (Finset.ne_of_mem_erase hi))
  obtain ⟨r₂, hr₂, hmax₂⟩ := isCompact_Icc.exists_isMaxOn hne hstc
  obtain ⟨r₃, hr₃, hmax₃⟩ := isCompact_Icc.exists_isMaxOn hne (hω.2.1.abs.continuousOn (s := Icc 0 s))
  obtain ⟨r₄, hr₄, hmax₄⟩ := isCompact_Icc.exists_isMaxOn hne hψc
  obtain ⟨m₀, hm₀⟩ := hω.2.2.2.2 s hsζ
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt (max (s : ℝ) (max (‖(Coupling.stateAt W VL VR r₂ ω).2‖ + |B r₃ ω| + 1)
    (ψ r₄)))
  refine ⟨max m₀ n₁, fun n hn => ?_⟩
  have hn1 : n₁ ≤ n := (le_max_right _ _).trans hn
  have hnR : max (s : ℝ) (max (‖(Coupling.stateAt W VL VR r₂ ω).2‖ + |B r₃ ω| + 1) (ψ r₄)) < n :=
    hn₁.trans_le (by exact_mod_cast hn1)
  have hns : (s : ℝ) < n := (le_max_left _ _).trans_lt hnR
  have hnS : ‖(Coupling.stateAt W VL VR r₂ ω).2‖ + |B r₃ ω| + 1 < n :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hnR
  have hnψ : ψ r₄ < n := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hnR
  have hsT : s ≤ T n ω := hm₀.trans (hTm ((le_max_left _ _).trans hn))
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- a reciprocal below `n + 1` gives a gap above `δ_n`
  have hrecip : ∀ {x : ℝ}, 0 < x → x⁻¹ ≤ ψ r₄ → 1 / ((n : ℝ) + 1) ≤ x := by
    intro x hx hle
    rw [one_div, inv_le_comm₀ hn0 hx]
    linarith
  have hhit : (s : WithTop ℝ≥0) ≤ rHit k G W VL VR ζ n ω := by
    simp only [rHit, hωG, ↓reduceIte]
    refine Coupling.le_hitBelow fun r hrζ hr => ?_
    by_contra hlt
    push Not at hlt
    have hrI : r ∈ Icc (0 : ℝ≥0) s := ⟨bot_le, hlt.le⟩
    have hψr : (VR k r ω - W r ω)⁻¹ + ∑ i ∈ Finset.univ.erase k, |VR k r ω - VR i r ω|⁻¹ ≤ ψ r₄ :=
      isMaxOn_iff.1 hmax₄ r hrI
    have hq : 0 < VR k r ω - W r ω := sub_pos.2 (lt_of_lt_sepTime (hsep r hrI))
    have hterms : ∀ i ∈ Finset.univ.erase k, 0 ≤ |VR k r ω - VR i r ω|⁻¹ := fun i _ =>
      inv_nonneg.2 (abs_nonneg _)
    have hsum := Finset.sum_nonneg hterms
    refine absurd (rLev_nonneg_iff.2 ⟨?_, ?_, fun i hi => ?_⟩) (not_le.2 hr)
    · have := isMaxOn_iff.1 hmax₂ r hrI
      have h3 := abs_nonneg (B r₃ ω)
      linarith
    · show 1 / ((n : ℝ) + 1) ≤ VR k r ω - W r ω
      refine hrecip hq ?_
      linarith
    · have hi' : i ∈ Finset.univ.erase k := Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩
      have hpos : 0 < |VR k r ω - VR i r ω| := abs_pos.2 (hd.vR_ne (hsep r hrI) i hi)
      show 1 / ((n : ℝ) + 1) ≤ |VR k r ω - VR i r ω|
      refine hrecip hpos ?_
      have h1 := Finset.single_le_sum hterms hi'
      have h2 : 0 ≤ (VR k r ω - W r ω)⁻¹ := inv_nonneg.2 hq.le
      linarith
  have hexit : (s : WithTop ℝ≥0) ≤ MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω := by
    by_contra hlt
    push Not at hlt
    obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    obtain ⟨r, hr, hBr⟩ := (MathFin.exitTime_le_iff (continuous_brownG_r hgood) n u ω).1 hu.symm.le
    have hus : u < s := by rw [← hu] at hlt; exact WithTop.coe_lt_coe.1 hlt
    have hrs : r ∈ Icc (0 : ℝ≥0) s := ⟨bot_le, hr.2.trans hus.le⟩
    have := isMaxOn_iff.1 hmax₃ r hrs
    simp only [Sec2.TwoSeed.brownG, hωG, ↓reduceIte] at hBr
    have h2 := norm_nonneg (Coupling.stateAt W VL VR r₂ ω).2
    linarith
  have hsn : s ≤ min (n : ℝ≥0) (T n ω) := le_min (by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast]; exact hns.le) hsT
  have h := le_min (WithTop.coe_le_coe.2 hsn) (le_min hhit hexit)
  have hc := Sec2.TwoSeed.coe_capTime (fun ω => min (n : ℝ≥0) (T n ω))
    (fun ω => min (rHit k G W VL VR ζ n ω) (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) ω
  have h' : (s : WithTop ℝ≥0) ≤ (rLoc k G T W VL VR B ζ n ω : WithTop ℝ≥0) := by
    unfold rLoc; rw [hc]; exact h
  exact WithTop.coe_le_coe.1 h'

end GoodBox

end Good

end Retarget

end Zhan

end InteractingSLE
