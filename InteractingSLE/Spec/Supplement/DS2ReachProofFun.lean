/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS2ReachProofTight

/-!
# DS2 in reach form, VII: continuous functionals of the stopped state path

Packet PROVE-T14-DS (identification of subsequential limits, spec p. 553: "For a fixed reciprocal cutoff, the drift
integrands are bounded continuous functions of the converging gaps. Their integrals converge. DS1 bounds the
difference from the genuine reciprocal integrals uniformly in `L¹`; then send the reciprocal cutoff to zero").

* `hcut δ x = 1/max(x, δ)`: the bounded continuous reciprocal cutoff, increasing to `Ginv x` (`1/x` for `x > 0`, `∞`
  otherwise) as `δ ↓ 0`;
* `intH δ gp q f = ∫₀^q hcut δ (gp (f s)) ds`, continuous in the path `f`;
* `upSet q`: the open set of paths that stay in the outer open buffer up to time `q`;
* for one good evolution, on `upSet q`: the force-coordinate equation gives
  `0 ≤ (v(q) − v(0)) − 2 intH ≤ 2 I_δ` (`EvolData.intH_le`, `EvolData.sub_intH_le`) and the driver satisfies the
  linear identity (`EvolData.linear_at`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Finset ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace DSReach

open DS2
open scoped PathMeas

/-! ### The reciprocal cutoff -/

/-- The bounded continuous reciprocal cutoff `1/max(x, δ)`. -/
def hcut (δ x : ℝ) : ℝ := 1 / max x δ

/-- The reciprocal with value `∞` at nonpositive arguments. -/
def Ginv (x : ℝ) : ℝ≥0∞ := if 0 < x then ENNReal.ofReal (1 / x) else ⊤

theorem continuous_hcut {δ : ℝ} (hδ : 0 < δ) : Continuous (hcut δ) :=
  continuous_const.div (continuous_id.max continuous_const) fun _ => (lt_max_of_lt_right hδ).ne'

theorem hcut_nonneg {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : 0 ≤ hcut δ x :=
  one_div_nonneg.2 (lt_max_of_lt_right hδ).le

theorem hcut_le_inv {δ x : ℝ} (hx : 0 < x) : hcut δ x ≤ 1 / x :=
  one_div_le_one_div_of_le hx (le_max_left _ _)

theorem hcut_anti {δ δ' : ℝ} (hδ' : 0 < δ') (h : δ' ≤ δ) (x : ℝ) : hcut δ x ≤ hcut δ' x :=
  one_div_le_one_div_of_le (lt_max_of_lt_right hδ') (max_le_max le_rfl h)

/-- `1/x − hcut δ x ≤ invCut δ y` when `0 < y ≤ x`. -/
theorem inv_sub_hcut_le {δ x y : ℝ} (hδ : 0 < δ) (hy : 0 < y) (hyx : y ≤ x) :
    1 / x - hcut δ x ≤ invCut δ y := by
  have hx : 0 < x := hy.trans_le hyx
  unfold hcut invCut
  by_cases hxδ : x < δ
  · have hyδ : y < δ := hyx.trans_lt hxδ
    rw [Set.indicator_of_mem (show y ∈ {z : ℝ | 0 < z ∧ z < δ} from ⟨hy, hyδ⟩), max_eq_right hxδ.le]
    have h1 : 1 / x ≤ 1 / y := one_div_le_one_div_of_le hy hyx
    have h2 : 0 ≤ 1 / δ := one_div_nonneg.2 hδ.le
    linarith
  · push Not at hxδ
    rw [max_eq_left hxδ, sub_self]
    exact invCut_nonneg _ _

/-- As `δ ↓ 0` along `δ_n`, `ofReal (hcut δ_n x)` increases to `Ginv x`. -/
theorem tendsto_ofReal_hcut {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n => ENNReal.ofReal (hcut (δ n) x)) atTop (𝓝 (Ginv x)) := by
  unfold Ginv
  by_cases hx : 0 < x
  · simp only [hx, ↓reduceIte]
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    have hev : ∀ᶠ n in atTop, hcut (δ n) x = 1 / x := by
      filter_upwards [hlim.eventually (gt_mem_nhds hx)] with n hn
      unfold hcut
      rw [max_eq_left hn.le]
    exact tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm)
  · simp only [hx, ↓reduceIte]
    push Not at hx
    have heq : ∀ n, hcut (δ n) x = 1 / δ n := fun n => by
      unfold hcut; rw [max_eq_right (hx.trans (hδ n).le)]
    simp only [heq]
    rw [ENNReal.tendsto_nhds_top_iff_nnreal]
    intro M
    have h1 : Tendsto (fun n => 1 / δ n) atTop atTop := by
      simp only [one_div]
      exact (tendsto_inv_nhdsGT_zero).comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hδ⟩)
    filter_upwards [h1.eventually (Filter.eventually_gt_atTop ((M : ℝ)))] with n hn
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt M.coe_nonneg hn)).2 hn

/-! ### Functionals of paths -/

section Functionals

variable {nL nR : ℕ} {T : ℝ≥0}

/-- `∫₀^q hcut δ (gp (f s)) ds` for a path `f` and a functional `gp` of the state. -/
def intH (δ : ℝ) (gp : SState nL nR → ℝ) (q : ℝ≥0) (f : C(Set.Icc (0 : ℝ≥0) T, SState nL nR)) : ℝ :=
  ∫ s in (0 : ℝ)..q, hcut δ (gp (pathAt f s.toNNReal))

theorem continuous_intH {δ : ℝ} (hδ : 0 < δ) {gp : SState nL nR → ℝ} (hgp : Continuous gp) (q : ℝ≥0) :
    Continuous (intH (T := T) δ gp q) := by
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0) ?_ continuous_const
  exact (continuous_hcut hδ).comp (hgp.comp (continuous_pathAt_uncurry.comp
    (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))))

/-- The paths that stay in the outer open buffer up to time `q`. -/
def upSet (mL mR : ℕ) (R g : ℝ) (q : ℝ≥0) : Set C(Set.Icc (0 : ℝ≥0) T, SState nL nR) :=
  {f | ∀ s : Set.Icc (0 : ℝ≥0) T, (s : ℝ≥0) ≤ q → f s ∈ oBuf mL mR R g}

theorem isOpen_upSet (mL mR : ℕ) (R g : ℝ) (q : ℝ≥0) :
    IsOpen (upSet (T := T) (nL := nL) (nR := nR) mL mR R g q) :=
  isOpen_setOf_forall_le_mem q (isOpen_oBuf mL mR R g)

/-- The right gap `v^R_j − w` of a state. -/
def gapR (j : Fin nR) (p : SState nL nR) : ℝ := p.2.2 j - p.1

/-- The left gap `w − v^L_i` of a state. -/
def gapL (i : Fin nL) (p : SState nL nR) : ℝ := p.1 - p.2.1 i

theorem continuous_gapR (j : Fin nR) : Continuous (gapR (nL := nL) j) :=
  ((continuous_apply _).comp (continuous_snd.comp continuous_snd)).sub continuous_fst

theorem continuous_gapL (i : Fin nL) : Continuous (gapL (nR := nR) i) :=
  continuous_fst.sub ((continuous_apply _).comp (continuous_fst.comp continuous_snd))

end Functionals

/-! ### One evolution on `upSet q` -/

namespace EvolData

variable {κ : ℝ} {nL nR : ℕ} {mL mR : ℕ} {Rw ε R g : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  (D : EvolData κ mL mR Rw ε R g xL xR ρL ρR P W VL VR ζ)

/-- On `upSet q` the stopped path has not exited by time `q`. -/
theorem le_τR_of_mem_upSet (hε : 0 < ε) (hg : 0 < g) {T q : ℝ≥0} (hqT : q ≤ T) {ω : Ω} (hω : ω ∈ D.G)
    (hf : fR mL mR R g T W VL VR ζ ω ∈ upSet mL mR R g q) : q ≤ τR mL mR R g T W VL VR ζ ω :=
  le_exitTime_of_forall_mem (t := ⟨q, zero_le, hqT⟩) ((D.good ω hω).stop hε hg) 0
    (oBuf_subset_interior_cBuf mL mR R g) fun u hu => hf u hu

theorem pathAt_fR_of_mem_upSet (hε : 0 < ε) (hg : 0 < g) {T q : ℝ≥0} (hqT : q ≤ T) {ω : Ω}
    (hω : ω ∈ D.G) (hf : fR mL mR R g T W VL VR ζ ω ∈ upSet mL mR R g q) {s : ℝ≥0} (hs : s ≤ q) :
    pathAt (fR mL mR R g T W VL VR ζ ω) s =
      stOf (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s :=
  D.pathAt_fR_of_le hε hg hω (hs.trans (D.le_τR_of_mem_upSet hε hg hqT hω hf))

theorem lt_ζ_of_mem_upSet (hε : 0 < ε) (hg : 0 < g) {T q : ℝ≥0} (hqT : q ≤ T) {ω : Ω} (hω : ω ∈ D.G)
    (hf : fR mL mR R g T W VL VR ζ ω ∈ upSet mL mR R g q) : (q : ℝ≥0∞) < ζ ω :=
  lt_of_le_of_lt (by exact_mod_cast D.le_τR_of_mem_upSet hε hg hqT hω hf)
    ((D.good ω hω).stop (T := T) hε hg).2

/-- **The force-coordinate equation dominates the cutoff integral** (right labels):
`2 ∫₀^q hcut δ (v_j − w) ≤ v_j(q) − v_j(0)` and the difference is at most `2 I^R_δ`. -/
theorem intH_bounds_R (hε : 0 < ε) (hg : 0 < g) (hnR : 0 < nR) {T q : ℝ≥0} (hqT : q ≤ T) {ω : Ω}
    (hω : ω ∈ D.G) (hf : fR mL mR R g T W VL VR ζ ω ∈ upSet mL mR R g q) (j : Fin nR) {δ : ℝ} (hδ : 0 < δ) :
    2 * intH δ (gapR j) q (fR mL mR R g T W VL VR ζ ω) ≤
        (pathAt (fR mL mR R g T W VL VR ζ ω) q).2.2 j - (pathAt (fR mL mR R g T W VL VR ζ ω) 0).2.2 j ∧
      (pathAt (fR mL mR R g T W VL VR ζ ω) q).2.2 j - (pathAt (fR mL mR R g T W VL VR ζ ω) 0).2.2 j -
        2 * intH δ (gapR j) q (fR mL mR R g T W VL VR ζ ω) ≤ 2 * (D.good ω hω).iR hnR T δ := by
  set f := fR mL mR R g T W VL VR ζ ω
  have hgood := D.good ω hω
  have hup := hgood.upTo
  have hqζ := D.lt_ζ_of_mem_upSet hε hg hqT hω hf
  have hqτ := D.le_τR_of_mem_upSet hε hg hqT hω hf
  have hτζ := (hgood.stop (T := T) hε hg).2
  set w : ℝ≥0 → ℝ := fun t => W t ω
  set vR : Fin nR → ℝ≥0 → ℝ := fun j t => VR j t ω
  have hpath : ∀ s : ℝ, s ∈ Set.uIcc (0 : ℝ) q → pathAt f s.toNNReal =
      stOf (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s.toNNReal := by
    intro s hs
    rw [Set.uIcc_of_le q.coe_nonneg] at hs
    exact D.pathAt_fR_of_mem_upSet hε hg hqT hω hf (Real.toNNReal_le_iff_le_coe.2 hs.2)
  have hq' := D.pathAt_fR_of_mem_upSet hε hg hqT hω hf (le_refl q)
  have h0' := D.pathAt_fR_of_mem_upSet hε hg hqT hω hf (zero_le : (0 : ℝ≥0) ≤ q)
  -- the equation
  have heq : (pathAt f q).2.2 j - (pathAt f 0).2.2 j =
      ∫ s in (0 : ℝ)..q, 2 / (vR j s.toNNReal - w s.toNNReal) := by
    rw [hq', h0']
    exact hup.vR_sub (zero_le : (0 : ℝ≥0) ≤ q) hqζ j
  have hH : intH δ (gapR j) q f = ∫ s in (0 : ℝ)..q, hcut δ (vR j s.toNNReal - w s.toNNReal) := by
    unfold intH
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [hpath s hs, gapR, stOf]
    rfl
  rw [heq, hH]
  have hq0 : (0 : ℝ) ≤ q := q.coe_nonneg
  have hint1 : IntervalIntegrable (fun s : ℝ => 2 / (vR j s.toNNReal - w s.toNNReal)) volume 0 q :=
    hup.intervalIntegrable_forceR hqζ j
  have hcontq : ContinuousOn (fun s : ℝ => vR j s.toNNReal - w s.toNNReal) (Set.uIcc 0 (q : ℝ)) := by
    have hlt : ∀ s ∈ Set.uIcc (0 : ℝ) q, (s.toNNReal : ℝ≥0∞) < ζ ω := fun s hs => by
      rw [Set.uIcc_of_le hq0] at hs
      exact lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) hqζ
    exact ((hup.continuousOn_vR j).comp continuous_real_toNNReal.continuousOn hlt).sub
      (hup.continuousOn_w.comp continuous_real_toNNReal.continuousOn hlt)
  have hint2 : IntervalIntegrable (fun s : ℝ => hcut δ (vR j s.toNNReal - w s.toNNReal)) volume 0 q :=
    ((continuous_hcut hδ).comp_continuousOn hcontq).intervalIntegrable
  -- a.e. positivity of the gaps
  have hpos : ∀ᵐ s ∂volume, s ∈ Set.Ioc (0 : ℝ) q →
      0 < vR ⟨0, hnR⟩ s.toNNReal - w s.toNNReal ∧
        vR ⟨0, hnR⟩ s.toNNReal - w s.toNNReal ≤ vR j s.toNNReal - w s.toNNReal := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hup.volume_collisionR ⟨0, hnR⟩)] with s hs hsI
    have hsζ : (s.toNNReal : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hsI.2) hqζ
    have hne : w s.toNNReal ≠ vR ⟨0, hnR⟩ s.toNNReal := fun he => hs ⟨hsI.1.le, hsζ, he⟩
    refine ⟨sub_pos.2 (lt_of_le_of_ne (hup.w_le_vR hsζ _) hne), ?_⟩
    exact sub_le_sub_right (hup.monotone_vR hsζ (Fin.le_def.2 (Nat.zero_le _))) _
  constructor
  · rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_ae_restrict hq0 (hint2.const_mul 2) hint1 ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hpos, Measure.ae_ne volume (0 : ℝ)] with s hs hs0 hsI
    have h := hs ⟨lt_of_le_of_ne hsI.1 (Ne.symm hs0), hsI.2⟩
    have := hcut_le_inv (δ := δ) (h.1.trans_le h.2)
    have e : 2 / (vR j s.toNNReal - w s.toNNReal) = 2 * (1 / (vR j s.toNNReal - w s.toNNReal)) := by ring
    show 2 * hcut δ (vR j s.toNNReal - w s.toNNReal) ≤ 2 / (vR j s.toNNReal - w s.toNNReal)
    rw [e]
    linarith
  · -- the difference is at most the truncated integral of the nearest gap
    have hτ0 : (0 : ℝ) ≤ (τR mL mR R g T W VL VR ζ ω : ℝ) := NNReal.coe_nonneg _
    have hcut0 : IntervalIntegrable (fun s : ℝ => invCut δ (vR ⟨0, hnR⟩ s.toNNReal - w s.toNNReal)) volume 0
        (τR mL mR R g T W VL VR ζ ω) := by
      have hlt : ∀ s ∈ Set.uIoc (0 : ℝ) (τR mL mR R g T W VL VR ζ ω), (s.toNNReal : ℝ≥0∞) < ζ ω :=
        fun s hs => by
          rw [Set.uIoc_of_le hτ0] at hs
          exact lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) hτζ
      have hg0 := hup.integrable_gapR hτζ ⟨0, hnR⟩
      have hmeas : AEStronglyMeasurable (fun s : ℝ => vR ⟨0, hnR⟩ s.toNNReal - w s.toNNReal)
          (volume.restrict (Set.uIoc 0 (τR mL mR R g T W VL VR ζ ω : ℝ))) := by
        have hc : ContinuousOn (fun s : ℝ => vR ⟨0, hnR⟩ s.toNNReal - w s.toNNReal)
            (Set.uIoc 0 (τR mL mR R g T W VL VR ζ ω : ℝ)) :=
          ((hup.continuousOn_vR _).comp continuous_real_toNNReal.continuousOn hlt).sub
            (hup.continuousOn_w.comp continuous_real_toNNReal.continuousOn hlt)
        exact hc.aestronglyMeasurable measurableSet_uIoc
      refine intervalIntegrable_iff.2 (Integrable.mono' (intervalIntegrable_iff.1 hg0).norm
        ((measurable_invCut δ).comp_aemeasurable hmeas.aemeasurable).aestronglyMeasurable
        (Eventually.of_forall fun s => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (invCut_nonneg _ _), Real.norm_eq_abs, ← abs_neg, neg_inv, neg_sub]
      exact invCut_le _ _
    have hsub : Set.uIcc (0 : ℝ) q ⊆ Set.uIcc 0 (τR mL mR R g T W VL VR ζ ω : ℝ) := by
      rw [Set.uIcc_of_le hq0, Set.uIcc_of_le hτ0]
      exact Set.Icc_subset_Icc le_rfl (by exact_mod_cast hqτ)
    have hcutq := hcut0.mono_set hsub
    have hdiff : (∫ s in (0 : ℝ)..q, 2 / (vR j s.toNNReal - w s.toNNReal)) -
        2 * ∫ s in (0 : ℝ)..q, hcut δ (vR j s.toNNReal - w s.toNNReal) ≤
        2 * ∫ s in (0 : ℝ)..q, invCut δ (vR ⟨0, hnR⟩ s.toNNReal - w s.toNNReal) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hint1 (hint2.const_mul 2),
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_ae_restrict hq0 (hint1.sub (hint2.const_mul 2))
        (hcutq.const_mul 2) ?_
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hpos, Measure.ae_ne volume (0 : ℝ)] with s hs hs0 hsI
      have h := hs ⟨lt_of_le_of_ne hsI.1 (Ne.symm hs0), hsI.2⟩
      have := inv_sub_hcut_le hδ h.1 h.2
      have e : 2 / (vR j s.toNNReal - w s.toNNReal) = 2 * (1 / (vR j s.toNNReal - w s.toNNReal)) := by ring
      show 2 / (vR j s.toNNReal - w s.toNNReal) - 2 * hcut δ (vR j s.toNNReal - w s.toNNReal) ≤
        2 * invCut δ (vR ⟨0, hnR⟩ s.toNNReal - w s.toNNReal)
      rw [e]
      linarith
    have hmono : ∫ s in (0 : ℝ)..q, invCut δ (vR ⟨0, hnR⟩ s.toNNReal - w s.toNNReal) ≤
        (D.good ω hω).iR hnR T δ :=
      intervalIntegral.integral_mono_interval le_rfl hq0 (by exact_mod_cast hqτ)
        (Eventually.of_forall fun _ => invCut_nonneg _ _) hcut0
    linarith

/-- **The force-coordinate equation dominates the cutoff integral** (left labels):
`2 ∫₀^q hcut δ (w − v_i) ≤ v_i(0) − v_i(q)` and the difference is at most `2 I^L_δ`. -/
theorem intH_bounds_L (hε : 0 < ε) (hg : 0 < g) (hnL : 0 < nL) {T q : ℝ≥0} (hqT : q ≤ T) {ω : Ω}
    (hω : ω ∈ D.G) (hf : fR mL mR R g T W VL VR ζ ω ∈ upSet mL mR R g q) (j : Fin nL) {δ : ℝ} (hδ : 0 < δ) :
    2 * intH δ (gapL j) q (fR mL mR R g T W VL VR ζ ω) ≤
        (pathAt (fR mL mR R g T W VL VR ζ ω) 0).2.1 j - (pathAt (fR mL mR R g T W VL VR ζ ω) q).2.1 j ∧
      (pathAt (fR mL mR R g T W VL VR ζ ω) 0).2.1 j - (pathAt (fR mL mR R g T W VL VR ζ ω) q).2.1 j -
        2 * intH δ (gapL j) q (fR mL mR R g T W VL VR ζ ω) ≤ 2 * (D.good ω hω).iL hnL T δ := by
  set f := fR mL mR R g T W VL VR ζ ω
  have hgood := D.good ω hω
  have hup := hgood.upTo
  have hqζ := D.lt_ζ_of_mem_upSet hε hg hqT hω hf
  have hqτ := D.le_τR_of_mem_upSet hε hg hqT hω hf
  have hτζ := (hgood.stop (T := T) hε hg).2
  set w : ℝ≥0 → ℝ := fun t => W t ω
  set vL : Fin nL → ℝ≥0 → ℝ := fun j t => VL j t ω
  have hpath : ∀ s : ℝ, s ∈ Set.uIcc (0 : ℝ) q → pathAt f s.toNNReal =
      stOf (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s.toNNReal := by
    intro s hs
    rw [Set.uIcc_of_le q.coe_nonneg] at hs
    exact D.pathAt_fR_of_mem_upSet hε hg hqT hω hf (Real.toNNReal_le_iff_le_coe.2 hs.2)
  have hq' := D.pathAt_fR_of_mem_upSet hε hg hqT hω hf (le_refl q)
  have h0' := D.pathAt_fR_of_mem_upSet hε hg hqT hω hf (zero_le : (0 : ℝ≥0) ≤ q)
  -- the equation
  have hneg : ∀ s : ℝ, 2 / (w s.toNNReal - vL j s.toNNReal) = -(2 / (vL j s.toNNReal - w s.toNNReal)) :=
    fun s => by rw [← neg_sub, div_neg]
  have heq : (pathAt f 0).2.1 j - (pathAt f q).2.1 j =
      ∫ s in (0 : ℝ)..q, 2 / (w s.toNNReal - vL j s.toNNReal) := by
    rw [hq', h0']
    simp_rw [hneg]
    rw [intervalIntegral.integral_neg]
    have hv := hup.vL_sub (zero_le : (0 : ℝ≥0) ≤ q) hqζ j
    rw [NNReal.coe_zero] at hv
    simp only [stOf]
    linarith
  have hH : intH δ (gapL j) q f = ∫ s in (0 : ℝ)..q, hcut δ (w s.toNNReal - vL j s.toNNReal) := by
    unfold intH
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [hpath s hs, gapL, stOf]
    rfl
  rw [heq, hH]
  have hq0 : (0 : ℝ) ≤ q := q.coe_nonneg
  have hint1 : IntervalIntegrable (fun s : ℝ => 2 / (w s.toNNReal - vL j s.toNNReal)) volume 0 q := by
    simp_rw [hneg]
    exact (hup.intervalIntegrable_forceL hqζ j).neg
  have hcontq : ContinuousOn (fun s : ℝ => w s.toNNReal - vL j s.toNNReal) (Set.uIcc 0 (q : ℝ)) := by
    have hlt : ∀ s ∈ Set.uIcc (0 : ℝ) q, (s.toNNReal : ℝ≥0∞) < ζ ω := fun s hs => by
      rw [Set.uIcc_of_le hq0] at hs
      exact lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) hqζ
    exact (hup.continuousOn_w.comp continuous_real_toNNReal.continuousOn hlt).sub
      ((hup.continuousOn_vL j).comp continuous_real_toNNReal.continuousOn hlt)
  have hint2 : IntervalIntegrable (fun s : ℝ => hcut δ (w s.toNNReal - vL j s.toNNReal)) volume 0 q :=
    ((continuous_hcut hδ).comp_continuousOn hcontq).intervalIntegrable
  -- a.e. positivity of the gaps
  have hpos : ∀ᵐ s ∂volume, s ∈ Set.Ioc (0 : ℝ) q →
      0 < w s.toNNReal - vL ⟨0, hnL⟩ s.toNNReal ∧
        w s.toNNReal - vL ⟨0, hnL⟩ s.toNNReal ≤ w s.toNNReal - vL j s.toNNReal := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hup.volume_collisionL ⟨0, hnL⟩)] with s hs hsI
    have hsζ : (s.toNNReal : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hsI.2) hqζ
    have hne : w s.toNNReal ≠ vL ⟨0, hnL⟩ s.toNNReal := fun he => hs ⟨hsI.1.le, hsζ, he⟩
    refine ⟨sub_pos.2 (lt_of_le_of_ne (hup.vL_le_w hsζ _) (Ne.symm hne)), ?_⟩
    exact sub_le_sub_left (hup.antitone_vL hsζ (Fin.le_def.2 (Nat.zero_le _))) _
  constructor
  · rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_ae_restrict hq0 (hint2.const_mul 2) hint1 ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hpos, Measure.ae_ne volume (0 : ℝ)] with s hs hs0 hsI
    have h := hs ⟨lt_of_le_of_ne hsI.1 (Ne.symm hs0), hsI.2⟩
    have := hcut_le_inv (δ := δ) (h.1.trans_le h.2)
    have e : 2 / (w s.toNNReal - vL j s.toNNReal) = 2 * (1 / (w s.toNNReal - vL j s.toNNReal)) := by ring
    show 2 * hcut δ (w s.toNNReal - vL j s.toNNReal) ≤ 2 / (w s.toNNReal - vL j s.toNNReal)
    rw [e]
    linarith
  · -- the difference is at most the truncated integral of the nearest gap
    have hτ0 : (0 : ℝ) ≤ (τR mL mR R g T W VL VR ζ ω : ℝ) := NNReal.coe_nonneg _
    have hcut0 : IntervalIntegrable (fun s : ℝ => invCut δ (w s.toNNReal - vL ⟨0, hnL⟩ s.toNNReal)) volume 0
        (τR mL mR R g T W VL VR ζ ω) := by
      have hlt : ∀ s ∈ Set.uIoc (0 : ℝ) (τR mL mR R g T W VL VR ζ ω), (s.toNNReal : ℝ≥0∞) < ζ ω :=
        fun s hs => by
          rw [Set.uIoc_of_le hτ0] at hs
          exact lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) hτζ
      have hg0 := hup.integrable_gapL hτζ ⟨0, hnL⟩
      have hmeas : AEStronglyMeasurable (fun s : ℝ => w s.toNNReal - vL ⟨0, hnL⟩ s.toNNReal)
          (volume.restrict (Set.uIoc 0 (τR mL mR R g T W VL VR ζ ω : ℝ))) := by
        have hc : ContinuousOn (fun s : ℝ => w s.toNNReal - vL ⟨0, hnL⟩ s.toNNReal)
            (Set.uIoc 0 (τR mL mR R g T W VL VR ζ ω : ℝ)) :=
          (hup.continuousOn_w.comp continuous_real_toNNReal.continuousOn hlt).sub
            ((hup.continuousOn_vL _).comp continuous_real_toNNReal.continuousOn hlt)
        exact hc.aestronglyMeasurable measurableSet_uIoc
      refine intervalIntegrable_iff.2 (Integrable.mono' (intervalIntegrable_iff.1 hg0).norm
        ((measurable_invCut δ).comp_aemeasurable hmeas.aemeasurable).aestronglyMeasurable
        (Eventually.of_forall fun s => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (invCut_nonneg _ _), Real.norm_eq_abs]
      exact invCut_le _ _
    have hsub : Set.uIcc (0 : ℝ) q ⊆ Set.uIcc 0 (τR mL mR R g T W VL VR ζ ω : ℝ) := by
      rw [Set.uIcc_of_le hq0, Set.uIcc_of_le hτ0]
      exact Set.Icc_subset_Icc le_rfl (by exact_mod_cast hqτ)
    have hcutq := hcut0.mono_set hsub
    have hdiff : (∫ s in (0 : ℝ)..q, 2 / (w s.toNNReal - vL j s.toNNReal)) -
        2 * ∫ s in (0 : ℝ)..q, hcut δ (w s.toNNReal - vL j s.toNNReal) ≤
        2 * ∫ s in (0 : ℝ)..q, invCut δ (w s.toNNReal - vL ⟨0, hnL⟩ s.toNNReal) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hint1 (hint2.const_mul 2),
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_ae_restrict hq0 (hint1.sub (hint2.const_mul 2))
        (hcutq.const_mul 2) ?_
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hpos, Measure.ae_ne volume (0 : ℝ)] with s hs hs0 hsI
      have h := hs ⟨lt_of_le_of_ne hsI.1 (Ne.symm hs0), hsI.2⟩
      have := inv_sub_hcut_le hδ h.1 h.2
      have e : 2 / (w s.toNNReal - vL j s.toNNReal) = 2 * (1 / (w s.toNNReal - vL j s.toNNReal)) := by ring
      show 2 / (w s.toNNReal - vL j s.toNNReal) - 2 * hcut δ (w s.toNNReal - vL j s.toNNReal) ≤
        2 * invCut δ (w s.toNNReal - vL ⟨0, hnL⟩ s.toNNReal)
      rw [e]
      linarith
    have hmono : ∫ s in (0 : ℝ)..q, invCut δ (w s.toNNReal - vL ⟨0, hnL⟩ s.toNNReal) ≤
        (D.good ω hω).iL hnL T δ :=
      intervalIntegral.integral_mono_interval le_rfl hq0 (by exact_mod_cast hqτ)
        (Eventually.of_forall fun _ => invCut_nonneg _ _) hcut0
    linarith

/-- **The linear driver identity on `upSet q`**: `w(q) = √κ b(q) − ∑ (ρ/2)(v(q) − v(0))`. -/
theorem linear_at (hε : 0 < ε) (hg : 0 < g) {T q : ℝ≥0} (hqT : q ≤ T) {ω : Ω} (hω : ω ∈ D.G)
    (hf : fR mL mR R g T W VL VR ζ ω ∈ upSet mL mR R g q) :
    (pathAt (fR mL mR R g T W VL VR ζ ω) q).1 = Real.sqrt κ * pathAt (D.bP T ω) q -
      (∑ i, ρL i / 2 * ((pathAt (fR mL mR R g T W VL VR ζ ω) q).2.1 i -
        (pathAt (fR mL mR R g T W VL VR ζ ω) 0).2.1 i)) -
      ∑ j, ρR j / 2 * ((pathAt (fR mL mR R g T W VL VR ζ ω) q).2.2 j -
        (pathAt (fR mL mR R g T W VL VR ζ ω) 0).2.2 j) := by
  have hup := (D.good ω hω).upTo
  have hqζ := D.lt_ζ_of_mem_upSet hε hg hqT hω hf
  rw [D.pathAt_fR_of_mem_upSet hε hg hqT hω hf (le_refl q),
    D.pathAt_fR_of_mem_upSet hε hg hqT hω hf (zero_le : (0 : ℝ≥0) ≤ q), pathAt_of_le _ hqT]
  have hb : D.bP T ω ⟨q, zero_le, hqT⟩ = D.b q ω := rfl
  rw [hb]
  simp only [stOf]
  have := w_eq_linear hup hqζ
  simp only [hup.vL_zero, hup.vR_zero]
  exact this

end EvolData


end DSReach

end Supp12

end InteractingSLE
