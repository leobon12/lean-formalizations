import QuantumZipper.Proofs.Thm11.ForwardTamed
import QuantumZipper.Proofs.Thm11.FrozenLocalDynkin
import QuantumZipper.Proofs.Thm11.NonSwallowing
import QuantumZipper.Proofs.Thm12.CharFun
import Mathlib.Analysis.ODE.ExistUnique

/-!
# RS-RL: real points are never swallowed, `κ ≤ 4`

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §4, node RL.

`RS.ae_real_alive`: for a Brownian motion `B` and `κ ∈ (0,4]`, almost surely every real
`x ≠ 0` is alive for all times under the forward flow driven by `√κ B`.

Proof (following Kemppainen, *Schramm–Loewner Evolution* (2017), Prop. 5.1 and its proof,
pp. 78–80, footnote 9, and Prop. 5.2, p. 80; cf. Rohde–Schramm, *Basic properties of SLE*,
Lemma 6.2, pp. 23–24):

1. For `x > 0`, `Y_t = f_t(x)` solves `dY = 2/Y dt − √κ dB` (a scaled Bessel process of
   dimension `1 + 4/κ ≥ 2`). We use the *tamed* equation `dY = 2/max(Y,c) dt − √κ dB`
   (Kemppainen's footnote 9), a globally Lipschitz ODE solved pathwise by Picard–Lindelöf
   (`realTamed`); while `Y ≥ c` it is the forward flow (`isForwardSol_realTamed`).
2. The scale function `G(y) = y^{1−4/κ}` (`κ < 4`) or `log R − log y` (`κ = 4`) has zero
   generator (`dynkinGen_rpow`, `dynkinGen_log`). The project's local Dynkin formula
   (`FrozenMart.martingale_localDynkin_stopped`, replacing Itô's formula) stopped at the exit
   from `(δ,R)` gives `G(δ) P(exit at δ) ≤ G(x)` (`swallow_bound`).
3. No blow-up: the tamed flow is bounded by `max x 1 + 2 sup|W| + 3T`, uniformly in `c`
   (`realTamed_le`), so for `R` large the exit through `R` is impossible before `T`.
   Letting `δ → 0` gives `P(x swallowed before T) = 0` (`ae_alive_of_pos`).
4. Rational `x`, integer `T`, monotonicity in `x` (`exists_isForwardSol_of_lt`, Kemppainen
   p. 80: via backward ODE uniqueness) and the reflection `W ↦ −W` (`isForwardSol_neg`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace RS

open FwdHolo

/-! ## 1. The tamed real flow -/

/-- The tamed real drift `2 / max z c`. -/
def realDrift (c z : ℝ) : ℝ := 2 / max z c

lemma realDrift_of_le {c z : ℝ} (h : c ≤ z) : realDrift c z = 2 / z := by
  simp [realDrift, max_eq_left h]

lemma abs_realDrift_le {c : ℝ} (hc : 0 < c) (z : ℝ) : |realDrift c z| ≤ 2 / c := by
  have h : c ≤ max z c := le_max_right _ _
  have hp : 0 < max z c := hc.trans_le h
  rw [realDrift, abs_div, abs_two, abs_of_pos hp]
  exact div_le_div_of_nonneg_left (by norm_num) hc h

lemma realDrift_le_two {c z : ℝ} (hz : 1 ≤ z) : realDrift c z ≤ 2 := by
  have h : 1 ≤ max z c := hz.trans (le_max_left _ _)
  rw [realDrift, div_le_iff₀ (by linarith)]; linarith

lemma lipschitz_realDrift {c : ℝ} (hc : 0 < c) :
    LipschitzWith (Real.toNNReal (2 / c ^ 2)) (realDrift c) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  have ha : c ≤ max a c := le_max_right _ _
  have hb : c ≤ max b c := le_max_right _ _
  have hap : 0 < max a c := hc.trans_le ha
  have hbp : 0 < max b c := hc.trans_le hb
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity), realDrift, realDrift,
    div_sub_div _ _ hap.ne' hbp.ne', abs_div, abs_of_pos (mul_pos hap hbp)]
  have hm : |2 * max b c - max a c * 2| ≤ 2 * |a - b| := by
    have := abs_max_sub_max_le_abs a b c
    rw [show 2 * max b c - max a c * 2 = -(2 * (max a c - max b c)) by ring, abs_neg, abs_mul,
      abs_two]
    linarith
  rw [div_le_iff₀ (mul_pos hap hbp)]
  have hcc : c ^ 2 ≤ max a c * max b c := by rw [sq]; exact mul_le_mul ha hb hc.le hap.le
  calc _ ≤ 2 * |a - b| := hm
    _ = 2 / c ^ 2 * |a - b| * c ^ 2 := by field_simp
    _ ≤ 2 / c ^ 2 * |a - b| * (max a c * max b c) := by gcongr

/-- The un-centered tamed real vector field `z ↦ 2 / max (z - W t) c`. -/
def realVf (W : ℝ → ℝ) (c t z : ℝ) : ℝ := realDrift c (z - W t)

variable {W : ℝ → ℝ}

lemma lipschitz_realVf {c : ℝ} (hc : 0 < c) (W : ℝ → ℝ) (t : ℝ) :
    LipschitzWith (Real.toNNReal (2 / c ^ 2)) (realVf W c t) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    have := (lipschitz_realDrift hc).dist_le_mul (a - W t) (b - W t)
    rwa [dist_sub_right] at this

lemma continuous_realVf_time (hW : Continuous W) {c : ℝ} (hc : 0 < c) (z : ℝ) :
    Continuous fun t => realVf W c t z :=
  (lipschitz_realDrift hc).continuous.comp (continuous_const.sub hW)

/-- Global existence for the tamed real field on `[0,T]` (Picard–Lindelöf). -/
lemma exists_realVf_sol (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T) (x : ℝ) :
    ∃ v : ℝ → ℝ, v 0 = x ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt v (realVf W c t (v t)) (Icc 0 T) t := by
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_refl 0, hT⟩
  set t0 : Icc (0 : ℝ) T := ⟨0, h0mem⟩ with ht0_def
  have ht0_coe : (t0 : ℝ) = 0 := rfl
  have hf : IsPicardLindelof (realVf W c) t0 x (Real.toNNReal (2 / c * T)) 0
      (Real.toNNReal (2 / c)) (Real.toNNReal (2 / c ^ 2)) := by
    refine ⟨fun t _ => (lipschitz_realVf hc W t).lipschitzOnWith,
      fun z _ => (continuous_realVf_time hW hc z).continuousOn, ?_, ?_⟩
    · intro t _ z _
      rw [Real.coe_toNNReal _ (by positivity), Real.norm_eq_abs]
      exact abs_realDrift_le hc _
    · simp only [ht0_coe, sub_zero, NNReal.coe_zero, max_eq_left hT,
        Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 2 / c),
        Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 2 / c * T), le_refl]
  have hx : x ∈ Metric.closedBall x ((0 : ℝ≥0) : ℝ) := Metric.mem_closedBall_self (le_refl _)
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, ?_, ?_⟩
  · show α.compProj (t0 : ℝ) = x
    rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · intro t ht
    apply (ODE.hasDerivWithinAt_picard_Icc t0.2 hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn (fun _ ht' ↦ α.compProj_mem_closedBall hf.mul_max_le)
      x ht).congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

lemma hasDerivWithinAt_Ici_of_Icc {f : ℝ → ℝ} {f' : ℝ → ℝ} {T : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (f' t) (Icc 0 T) t) :
    ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt f (f' t) (Ici t) t := fun t ht =>
  (h t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))

/-- Uniqueness for the tamed real field (Lipschitz). -/
lemma realVf_sol_unique {c : ℝ} (hc : 0 < c) {T : ℝ} {V V' : ℝ → ℝ} (h0 : V 0 = V' 0)
    (hV : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt V (realVf W c t (V t)) (Icc 0 T) t)
    (hV' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt V' (realVf W c t (V' t)) (Icc 0 T) t) :
    EqOn V V' (Icc 0 T) :=
  ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
    (fun t _ => (lipschitz_realVf hc W t).lipschitzOnWith)
    (fun t ht => (hV t ht).continuousWithinAt)
    (hasDerivWithinAt_Ici_of_Icc (f' := fun t => realVf W c t (V t)) hV)
    (fun _ _ => mem_univ _)
    (fun t ht => (hV' t ht).continuousWithinAt)
    (hasDerivWithinAt_Ici_of_Icc (f' := fun t => realVf W c t (V' t)) hV')
    (fun _ _ => mem_univ _) h0

open Classical in
/-- The un-centered tamed real flow started at `x` (junk `0` unless `W` is continuous and
`c > 0`). -/
def realTamedUnc (W : ℝ → ℝ) (c x t : ℝ) : ℝ :=
  if h : Continuous W ∧ 0 < c then
    Classical.choose (exists_realVf_sol h.1 h.2 (le_max_right t 0) x) t else 0

/-- The centered tamed real flow `Y_t = x − W_t + ∫₀ᵗ 2 / max(Y_s, c) ds`. -/
def realTamed (W : ℝ → ℝ) (c x t : ℝ) : ℝ := realTamedUnc W c x t - W t

theorem realTamedUnc_eq_of_sol (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ}
    {V : ℝ → ℝ} {x : ℝ} (hV0 : V 0 = x)
    (hV : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt V (realVf W c t (V t)) (Icc 0 T) t) :
    ∀ t ∈ Icc (0 : ℝ) T, realTamedUnc W c x t = V t := by
  intro t ht
  rw [realTamedUnc, dif_pos ⟨hW, hc⟩]
  obtain ⟨hv0, hvd⟩ := Classical.choose_spec (exists_realVf_sol hW hc (le_max_right t 0) x)
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 (max t 0) := Icc_subset_Icc_right (le_max_left _ _)
  have hsubT : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  exact realVf_sol_unique hc (hv0.trans hV0.symm) (fun s hs => (hvd s (hsub hs)).mono hsub)
    (fun s hs => (hV s (hsubT hs)).mono hsubT) ⟨ht.1, le_rfl⟩

theorem realTamedUnc_zero (hW : Continuous W) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    realTamedUnc W c x 0 = x := by
  rw [realTamedUnc, dif_pos ⟨hW, hc⟩]
  exact (Classical.choose_spec (exists_realVf_sol hW hc (le_max_right 0 0) x)).1

theorem realTamedUnc_hasDerivWithinAt (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ}
    (hT : 0 ≤ T) (x : ℝ) :
    ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (realTamedUnc W c x) (realVf W c t (realTamedUnc W c x t)) (Icc 0 T) t := by
  obtain ⟨v, hv0, hvd⟩ := exists_realVf_sol hW hc hT x
  have heq := realTamedUnc_eq_of_sol hW hc hv0 hvd
  intro t ht
  rw [heq t ht]
  exact (hvd t ht).congr_of_mem heq ht

theorem continuousOn_realTamedUnc (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T)
    (x : ℝ) : ContinuousOn (realTamedUnc W c x) (Icc 0 T) := fun t ht =>
  (realTamedUnc_hasDerivWithinAt hW hc hT x t ht).continuousWithinAt

theorem continuousOn_realTamed (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T)
    (x : ℝ) : ContinuousOn (realTamed W c x) (Icc 0 T) :=
  (continuousOn_realTamedUnc hW hc hT x).sub hW.continuousOn

/-- Integral equation of the tamed real flow. -/
theorem realTamed_eq (hW : Continuous W) {c : ℝ} (hc : 0 < c) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    realTamed W c x t = x - W t + ∫ s in (0 : ℝ)..t, realDrift c (realTamed W c x s) := by
  have hcont : ContinuousOn (realTamedUnc W c x) (Icc 0 t) := continuousOn_realTamedUnc hW hc ht x
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) t,
      HasDerivAt (realTamedUnc W c x) (realDrift c (realTamed W c x s)) s := fun s hs =>
    (realTamedUnc_hasDerivWithinAt hW hc ht x s (Ioo_subset_Icc_self hs)).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)
  have hint : IntervalIntegrable (fun s => realDrift c (realTamed W c x s)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht]
    exact (lipschitz_realDrift hc).continuous.comp_continuousOn (continuousOn_realTamed hW hc ht x)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcont hderiv hint
  rw [realTamedUnc_zero hW hc] at key
  rw [key, realTamed]; ring

/-- While the tamed real flow stays `≥ c`, it is a forward solution. -/
theorem isForwardSol_realTamed (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ} (hge : ∀ t ∈ Icc (0 : ℝ) T, c ≤ realTamed W c x t) :
    IsForwardSol W (x : ℂ) T (fun t => (realTamed W c x t : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.comp_continuousOn (continuousOn_realTamed hW hc hT x),
    fun t ht => ⟨?_, ?_⟩⟩
  · show (realTamed W c x t : ℂ) ≠ 0
    exact_mod_cast (hc.trans_le (hge t ht)).ne'
  · have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
    have hcongr : ∫ s in (0 : ℝ)..t, (2 : ℂ) / (realTamed W c x s : ℂ) =
        ∫ s in (0 : ℝ)..t, ((realDrift c (realTamed W c x s) : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht.1] at hs
      rw [realDrift_of_le (hge s (hsub hs))]; push_cast; rfl
    show (realTamed W c x t : ℂ) = _
    rw [hcongr, intervalIntegral.integral_ofReal, realTamed_eq hW hc x ht.1]
    push_cast; ring

/-- Pathwise upper bound of the tamed real flow, uniform in `c` (no blow-up). -/
theorem realTamed_le (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T) (x : ℝ)
    {S : ℝ} (hS : ∀ r ∈ Icc (0 : ℝ) T, |W r| ≤ S) :
    ∀ t ∈ Icc (0 : ℝ) T, realTamed W c x t ≤ max x 1 + 2 * S + 3 * T := by
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS 0 ⟨le_rfl, hT⟩)
  have hd := realTamedUnc_hasDerivWithinAt hW hc hT x
  have key : ∀ t ∈ Icc (0 : ℝ) T, realTamedUnc W c x t ≤ max x 1 + S + 3 * t := by
    refine image_le_of_deriv_right_lt_deriv_boundary
      (f' := fun t => realVf W c t (realTamedUnc W c x t)) (B' := fun _ => 3)
      (continuousOn_realTamedUnc hW hc hT x)
      (hasDerivWithinAt_Ici_of_Icc (f' := fun t => realVf W c t (realTamedUnc W c x t)) hd)
      ?_ (fun t => ?_) ?_
    · rw [realTamedUnc_zero hW hc]; linarith [le_max_left x 1]
    · simpa using ((hasDerivAt_id t).const_mul (3 : ℝ)).const_add (max x 1 + S)
    · intro t ht heq
      have hWt := (abs_le.1 (hS t (Ico_subset_Icc_self ht))).2
      show realDrift c (realTamedUnc W c x t - W t) < 3
      have h1 : 1 ≤ realTamedUnc W c x t - W t := by
        rw [heq]; linarith [le_max_right x 1, ht.1]
      linarith [realDrift_le_two (c := c) h1]
  intro t ht
  have h1 := key t ht
  have hWt := (abs_le.1 (hS t ht)).1
  simp only [realTamed]; linarith [ht.2]

/-! ## 2. Monotonicity in the starting point, and reflection -/

/-- If `q > W 0` is alive on `[0,T]` and `y > q`, then `y` is alive on `[0,T]`
(Kemppainen, *SLE*, p. 80, before Prop. 5.2). -/
theorem exists_isForwardSol_of_lt (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {q y : ℝ}
    (hq : W 0 < q) (hqy : q < y) {u : ℝ → ℂ} (hu : IsForwardSol W (q : ℂ) T u) :
    ∃ v, IsForwardSol W (y : ℂ) T v := by
  have him := im_isForwardSol_real hW hT hu
  have hre := re_pos_isForwardSol_real hW hT hu hq
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT)
    (Complex.continuous_re.comp_continuousOn hu.1)
  set c := (u t₀).re with hc_def
  have hc : 0 < c := hre t₀ ht₀
  have hcle : ∀ t ∈ Icc (0 : ℝ) T, c ≤ (u t).re := fun t ht => hmin ht
  set V2 : ℝ → ℝ := fun s => (u s + (W s : ℂ)).re with hV2_def
  have hV2e : ∀ s, V2 s = (u s).re + W s := fun s => by simp [V2]
  have hV2 : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt V2 (realVf W c t (V2 t)) (Icc 0 T) t := by
    intro t ht
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t (hasDerivWithinAt_shift hu ht)
    have hval : realVf W c t (V2 t) = (2 / u t).re := by
      rw [realVf, hV2e, add_sub_cancel_right, realDrift_of_le (hcle t ht)]
      have : u t = ((u t).re : ℂ) := Complex.ext (by simp) (by simp [him t ht])
      rw [this, ← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.ofReal_re,
        Complex.ofReal_re]
    rw [hval]
    exact h
  set V1 := realTamedUnc W c y with hV1_def
  have hV1 := realTamedUnc_hasDerivWithinAt hW hc hT y
  have hV1c : ContinuousOn V1 (Icc 0 T) := continuousOn_realTamedUnc hW hc hT y
  have hV2c : ContinuousOn V2 (Icc 0 T) := fun t ht => (hV2 t ht).continuousWithinAt
  have hd0 : V2 0 < V1 0 := by
    rw [hV2e, sol_zero hu hT, hV1_def, realTamedUnc_zero hW hc]; simp; linarith
  have hclaim : ∀ t ∈ Icc (0 : ℝ) T, V2 t < V1 t := by
    intro t ht
    by_contra hcon'
    have hcon := not_lt.1 hcon'
    obtain ⟨t1, ht1, ht1eq⟩ : ∃ t1 ∈ Icc 0 t, (fun s => V1 s - V2 s) t1 = 0 := by
      have := intermediate_value_Icc' ht.1 ((hV1c.sub hV2c).mono (Icc_subset_Icc_right ht.2))
      exact this ⟨by show V1 t - V2 t ≤ 0; linarith, by show 0 ≤ V1 0 - V2 0; linarith⟩
    simp only at ht1eq
    have ht1pos : 0 < t1 := lt_of_le_of_ne ht1.1 (fun h => by rw [← h] at ht1eq; linarith)
    have hsub : Icc 0 t1 ⊆ Icc 0 T := Icc_subset_Icc_right (ht1.2.trans ht.2)
    have hIic : ∀ {f : ℝ → ℝ},
        (∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (realVf W c s (f s)) (Icc 0 T) s) →
        ∀ s ∈ Ioc (0 : ℝ) t1, HasDerivWithinAt f (realVf W c s (f s)) (Iic s) s :=
      fun h s hs => (h s (hsub (Ioc_subset_Icc_self hs))).mono_of_mem_nhdsWithin
        (mem_of_superset (Icc_mem_nhdsLE hs.1)
          (Icc_subset_Icc_right (hs.2.trans (ht1.2.trans ht.2))))
    have heq := ODE_solution_unique_of_mem_Icc_left (s := fun _ => univ)
      (fun s _ => (lipschitz_realVf hc W s).lipschitzOnWith)
      (hV1c.mono hsub) (hIic hV1) (fun _ _ => mem_univ _)
      (hV2c.mono hsub) (hIic hV2) (fun _ _ => mem_univ _) (by linarith : V1 t1 = V2 t1)
    have := heq ⟨le_rfl, ht1pos.le⟩
    linarith
  refine ⟨_, isForwardSol_realTamed hW hc hT fun t ht => ?_⟩
  have h1 := hclaim t ht
  rw [hV2e] at h1
  have h2 := hcle t ht
  show c ≤ realTamedUnc W c y t - W t
  linarith

/-- Reflection: a forward solution for `W` from `z` gives one for `-W` from `-z`. -/
theorem isForwardSol_neg {z : ℂ} {T : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W z T u) :
    IsForwardSol (fun t => -W t) (-z) T (fun t => -u t) := by
  refine ⟨hu.1.neg, fun t ht => ⟨neg_ne_zero.2 (hu.2 t ht).1, ?_⟩⟩
  have h : (∫ s in (0 : ℝ)..t, (2 : ℂ) / -u s) = -∫ s in (0 : ℝ)..t, 2 / u s := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext s; rw [div_neg]
  simp only
  rw [h, (hu.2 t ht).2]; push_cast; ring

/-! ## 3. The harmonic functions (scale functions of the Bessel process) -/

lemma dynkinGen_real {b : ℝ → ℝ} {e : ℝ} {F : ℝ → ℝ} {y F1 F2 : ℝ}
    (h1 : HasDerivAt F F1 y) (h2 : HasDerivAt (deriv F) F2 y) :
    dynkinGen b e F y = F1 * b y + 1 / 2 * (e * e * F2) := by
  have h2' : iteratedDeriv 2 F y = F2 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]; exact h2.deriv
  simp only [dynkinGen]
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, h2', h1.hasFDerivAt.fderiv]
  simp [Fin.prod_univ_two]
  ring

/-- `z ↦ z^{1-4/κ}` is harmonic for the generator `(2/z) d/dz + (κ/2) d²/dz²`. -/
lemma dynkinGen_rpow {κ c e y : ℝ} (hκ : 0 < κ) (he : e * e = κ) (hc : 0 < c) (hy : c ≤ y) :
    dynkinGen (realDrift c) e (fun z => z ^ (1 - 4 / κ)) y = 0 := by
  have hy0 : 0 < y := hc.trans_le hy
  set p := 1 - 4 / κ with hp_def
  have h1 : HasDerivAt (fun z : ℝ => z ^ p) (p * y ^ (p - 1)) y :=
    Real.hasDerivAt_rpow_const (Or.inl hy0.ne')
  have hev : deriv (fun z : ℝ => z ^ p) =ᶠ[𝓝 y] fun z => p * z ^ (p - 1) := by
    filter_upwards [lt_mem_nhds hy0] with z hz
    exact (Real.hasDerivAt_rpow_const (Or.inl hz.ne')).deriv
  have h2 : HasDerivAt (deriv fun z : ℝ => z ^ p) (p * ((p - 1) * y ^ (p - 1 - 1))) y :=
    ((Real.hasDerivAt_rpow_const (Or.inl hy0.ne')).const_mul p).congr_of_eventuallyEq hev
  rw [dynkinGen_real h1 h2, realDrift_of_le hy, he]
  have e1 : y ^ (p - 1) = y ^ (p - 1 - 1) * y := by
    rw [← Real.rpow_add_one hy0.ne']; congr 1; ring
  have hp : κ * (p - 1) = -4 := by rw [hp_def]; field_simp; ring
  have e2 : p * (y ^ (p - 1 - 1) * y) * (2 / y) = 2 * p * y ^ (p - 1 - 1) := by
    field_simp
  rw [e1, e2]
  linear_combination (1 / 2 * p * y ^ (p - 1 - 1)) * hp

/-- `z ↦ log R − log z` is harmonic for the generator `(2/z) d/dz + 2 d²/dz²` (`κ = 4`). -/
lemma dynkinGen_log {R c e y : ℝ} (he : e * e = 4) (hc : 0 < c) (hy : c ≤ y) :
    dynkinGen (realDrift c) e (fun z => Real.log R - Real.log z) y = 0 := by
  have hy0 : 0 < y := hc.trans_le hy
  have h1 : HasDerivAt (fun z => Real.log R - Real.log z) (-y⁻¹) y :=
    (Real.hasDerivAt_log hy0.ne').const_sub _
  have hev : deriv (fun z => Real.log R - Real.log z) =ᶠ[𝓝 y] fun z => -z⁻¹ := by
    filter_upwards [lt_mem_nhds hy0] with z hz
    exact ((Real.hasDerivAt_log hz.ne').const_sub _).deriv
  have h2 : HasDerivAt (deriv fun z => Real.log R - Real.log z) (-(-(y ^ 2)⁻¹)) y :=
    (hasDerivAt_inv hy0.ne').neg.congr_of_eventuallyEq hev
  rw [dynkinGen_real h1 h2, realDrift_of_le hy, he]
  field_simp
  ring

lemma eq_zero_of_mul_le_of_tendsto {g : ℝ → ℝ} {a b x : ℝ} (ha : 0 ≤ a) (hx : 0 < x)
    (hg : Tendsto g (𝓝[>] 0) atTop) (h : ∀ δ ∈ Ioo 0 x, g δ * a ≤ b) : a = 0 := by
  by_contra hne
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hne)
  obtain ⟨δ, h1, h2⟩ := ((hg.eventually_gt_atTop (b / a)).and (Ioo_mem_nhdsGT hx)).exists
  have := h δ h2
  rw [div_lt_iff₀ hapos] at h1
  linarith

/-! ## 4. The exit estimate -/

section Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit mΩ in
/-- The driver `t ↦ s · B_t` in real time. -/
def sDrive (s : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ → ℝ := fun t => s * B t.toNNReal ω

omit mΩ in
lemma continuous_sDrive (hBc : ∀ ω, Continuous (B · ω)) (s : ℝ) (ω : Ω) :
    Continuous (sDrive s B ω) :=
  continuous_const.mul ((hBc ω).comp continuous_real_toNNReal)

omit mΩ in
theorem hittingBtwn_mem_real {X : ℝ≥0 → Ω → ℝ} {S : Set ℝ} (hS : IsClosed S) {ω : Ω}
    (hc : Continuous (X · ω)) {T : ℝ≥0} (hex : ∃ j ∈ Icc 0 T, X j ω ∈ S) :
    X (hittingBtwn X S 0 T ω) ω ∈ S := by
  classical
  rw [hittingBtwn_def]
  simp only [if_pos hex]
  obtain ⟨j, hj, hjS⟩ := hex
  have hcl : IsClosed (Icc 0 T ∩ {i : ℝ≥0 | X i ω ∈ S}) :=
    isClosed_Icc.inter (hS.preimage hc)
  exact (hcl.csInf_mem ⟨j, hj, hjS⟩ ⟨0, fun _ h => h.1.1⟩).2

theorem mem_of_forall_lt_real {X : ℝ≥0 → ℝ} {K : Set ℝ} (hK : IsClosed K) (hc : Continuous X)
    {t : ℝ≥0} (h0 : X 0 ∈ K) (hlt : ∀ s < t, X s ∈ K) : X t ∈ K := by
  rcases eq_or_ne t 0 with h0' | hne
  · rw [h0']; exact h0
  have hsub : Ico 0 t ⊆ {r | X r ∈ K} := fun r hr => hlt r hr.2
  have hcl := closure_minimal hsub (hK.preimage hc)
  have : t ∈ closure (Ico 0 t) := by
    rw [closure_Ico (Ne.symm hne)]; exact ⟨zero_le, le_rfl⟩
  exact hcl this

/-- **Exit estimate.** Let `0 < c < δ < x < R`, let `G` be `C³` on `(0,∞)`, harmonic for the
tamed generator on `[δ,R]` and nonnegative there. On the event that `x` is swallowed before `T`
while `|s B| ≤ S` on `[0,T]` (with `max x 1 + 2S + 3T < R`), the tamed flow exits `(δ,R)`
through `δ`; optional stopping for `G(Y_{t ∧ τ})` gives `G(δ) P(event) ≤ G(x)`. -/
theorem swallow_bound (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) (s : ℝ) {x δ R c S : ℝ}
    (hc : 0 < c) (hcδ : c < δ) (hδx : δ < x) (hxR : x < R) (T : ℝ≥0)
    (hSR : max x 1 + 2 * S + 3 * T < R)
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ 3 G (Ioi 0))
    (hLG : ∀ y ∈ Icc δ R, dynkinGen (realDrift c) (-s) G y = 0)
    (hG0 : ∀ y ∈ Icc δ R, 0 ≤ G y) :
    G δ * P.real {ω | (¬ ∃ v, IsForwardSol (sDrive s B ω) (x : ℂ) T v) ∧
      ∀ r ∈ Icc (0 : ℝ) T, |sDrive s B ω r| ≤ S} ≤ G x := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hWc := continuous_sDrive hBc s
  set U : ℝ≥0 → Ω → ℝ := fun t ω => realTamed (sDrive s B ω) c x t with hU_def
  have hU : ∀ ω (t : ℝ≥0),
      U t ω = x + (∫ r in (0 : ℝ)..t, realDrift c (U r.toNNReal ω)) + B t ω • (-s) := by
    intro ω t
    simp only [hU_def]
    rw [realTamed_eq (hWc ω) hc x t.coe_nonneg]
    have hint : (∫ r in (0 : ℝ)..t, realDrift c (realTamed (sDrive s B ω) c x r)) =
        ∫ r in (0 : ℝ)..t, realDrift c (realTamed (sDrive s B ω) c x (r.toNNReal : ℝ)) := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le t.coe_nonneg] at hr
      simp only [Real.coe_toNNReal _ hr.1]
    rw [hint, smul_eq_mul]
    simp only [sDrive, Real.toNNReal_coe]
    ring
  set Cl : Set ℝ := Iic δ ∪ Ici R with hCl_def
  set K : Set ℝ := Icc δ R with hK_def
  have hCl : IsClosed Cl := isClosed_Iic.union isClosed_Ici
  have hK : IsClosed K := isClosed_Icc
  have hKO : K ⊆ Ioi 0 := fun y hy => (hc.trans hcδ).trans_le hy.1
  have hbc : Continuous (realDrift c) := (lipschitz_realDrift hc).continuous
  have hbM : ∀ y, ‖realDrift c y‖ ≤ 2 / c := fun y => by
    rw [Real.norm_eq_abs]; exact abs_realDrift_le hc y
  have hUc : ∀ ω, Continuous (U · ω) := Dynkin.continuous_of_integralEq hBc hbc hbM hU
  have hU0 : ∀ ω, U 0 ω = x := fun ω => by rw [hU ω 0]; simp [hB0 ω]
  have hUK : ∀ ω (t : ℝ≥0), t ≤ T → (∀ s < t, U s ω ∉ Cl) → U t ω ∈ K := by
    intro ω t _ ht
    refine mem_of_forall_lt_real hK (hUc ω) (by rw [hU0]; exact ⟨hδx.le, hxR.le⟩) fun q hq => ?_
    have := ht q hq
    simp only [hCl_def, mem_union, mem_Iic, mem_Ici, not_or, not_le] at this
    exact ⟨this.1.le, this.2.le⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hG.continuousOn.mono hKO)
  have hFM : ∀ y ∈ K, |G y| ≤ M := fun y hy => by rw [← Real.norm_eq_abs]; exact hM y hy
  have hmart := FrozenMart.martingale_localDynkin_stopped hB hBc (NonSwallow.bmFilt hBm)
    (NonSwallow.bmFilt_adapted hBm) (NonSwallow.bmFilt_le_past hBm) (lipschitz_realDrift hc) hbM
    hU isOpen_Ioi hCl hK hKO hG (fun y hy _ => hLG y hy) T hUK hFM
  set τ := hittingBtwn U Cl 0 T with hτ_def
  have hint := hmart.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
  simp only [setIntegral_univ] at hint
  have hleft : ∫ ω, G (U (min 0 (τ ω)) ω) ∂P = G x := by
    have : ∀ ω, G (U (min 0 (τ ω)) ω) = G x := fun ω => by rw [min_eq_left (zero_le), hU0]
    rw [integral_congr_ae (ae_of_all _ this)]
    simp
  have hτT : ∀ ω, τ ω ≤ T := fun ω => hittingBtwn_le ω
  have hfK : ∀ ω, U (min T (τ ω)) ω ∈ K := fun ω => by
    rw [min_eq_right (hτT ω)]
    exact hUK ω _ (hτT ω) fun q hq => notMem_of_lt_hittingBtwn hq (zero_le)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (f := fun ω => G (U (min T (τ ω)) ω))
    (ae_of_all _ fun ω => hG0 _ (hfK ω)) (hmart.integrable T) (G δ)
  rw [← hint, hleft] at hmarkov
  refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono ?_)
    (hG0 δ ⟨le_rfl, (hδx.trans hxR).le⟩)) hmarkov
  intro ω ⟨hsw, hbd⟩
  show G δ ≤ G (U (min T (τ ω)) ω)
  have hex : ∃ j ∈ Icc (0 : ℝ≥0) T, U j ω ∈ Cl := by
    by_contra hne
    apply hsw
    refine ⟨_, isForwardSol_realTamed (hWc ω) hc T.coe_nonneg fun t ht => ?_⟩
    have hj : t.toNNReal ∈ Icc (0 : ℝ≥0) T :=
      ⟨zero_le, (Real.toNNReal_le_iff_le_coe).2 ht.2⟩
    have hnot : U t.toNNReal ω ∉ Cl := fun h => hne ⟨_, hj, h⟩
    simp only [hCl_def, hU_def, mem_union, mem_Iic, mem_Ici, not_or, not_le,
      Real.coe_toNNReal _ ht.1] at hnot
    exact hcδ.le.trans hnot.1.le
  have hmem := hittingBtwn_mem_real hCl (hUc ω) hex
  have hle : U (τ ω) ω ≤ max x 1 + 2 * S + 3 * T :=
    realTamed_le (hWc ω) hc T.coe_nonneg x hbd (τ ω)
      ⟨(τ ω).coe_nonneg, by exact_mod_cast hτT ω⟩
  have hK' := hfK ω
  rw [min_eq_right (hτT ω)] at hK' ⊢
  have heq : U (τ ω) ω = δ := by
    rcases hmem with h | h
    · exact le_antisymm h hK'.1
    · exfalso; simp only [mem_Ici] at h; linarith
  rw [heq]

/-- **Per-point statement.** For `x > 0` and `T ≥ 0`, a.s. `x` is not swallowed before `T` by
the flow driven by `s B`, `s² = κ ≤ 4` (Kemppainen, *SLE*, Prop. 5.1 and its proof,
pp. 78–79; Rohde–Schramm, Lemma 6.2). -/
theorem ae_alive_of_pos (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) {κ s : ℝ} (hκ : 0 < κ)
    (hκ4 : κ ≤ 4) (hs : s * s = κ) {x : ℝ} (hx : 0 < x) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ v, IsForwardSol (sDrive s B ω) (x : ℂ) T v := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have he : -s * -s = κ := by rw [neg_mul_neg, hs]
  set A : ℕ → Set Ω := fun N => {ω | (¬ ∃ v, IsForwardSol (sDrive s B ω) (x : ℂ) T v) ∧
      ∀ r ∈ Icc (0 : ℝ) T, |sDrive s B ω r| ≤ N} with hA_def
  have hA : ∀ N : ℕ, P (A N) = 0 := by
    intro N
    set R : ℝ := max x 1 + 2 * N + 3 * T + 1 with hR_def
    have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
    have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
    have hxR : x < R := by linarith [le_max_left x 1]
    have hSR : max x 1 + 2 * (N : ℝ) + 3 * T < R := by linarith
    have key : ∀ G : ℝ → ℝ, ContDiffOn ℝ 3 G (Ioi 0) →
        (∀ c y, 0 < c → c ≤ y → dynkinGen (realDrift c) (-s) G y = 0) →
        (∀ y ∈ Ioc 0 R, 0 ≤ G y) → ∀ δ ∈ Ioo 0 x, G δ * P.real (A N) ≤ G x := by
      intro G hG hLG hG0 δ hδ
      exact swallow_bound hB hBm hBc hB0 s (c := δ / 2) (by linarith [hδ.1])
        (by linarith [hδ.1]) hδ.2 hxR T hSR hG
        (fun y hy => hLG _ y (by linarith [hδ.1]) (by linarith [hy.1, hδ.1]))
        (fun y hy => hG0 y ⟨by linarith [hy.1, hδ.1], hy.2⟩)
    have hreal : P.real (A N) = 0 := by
      rcases hκ4.lt_or_eq with hlt | heq
      · have hp : 1 - 4 / κ < 0 := by
          have : 1 < 4 / κ := (one_lt_div hκ).2 hlt
          linarith
        exact eq_zero_of_mul_le_of_tendsto measureReal_nonneg hx
          (tendsto_rpow_neg_nhdsGT_zero hp)
          (key (fun z => z ^ (1 - 4 / κ))
            (fun y hy => (Real.contDiffAt_rpow_const_of_ne (mem_Ioi.1 hy).ne').contDiffWithinAt)
            (fun c y hc hy => dynkinGen_rpow hκ he hc hy)
            (fun y hy => Real.rpow_nonneg hy.1.le _))
      · have he4 : -s * -s = 4 := he.trans heq
        have hg : Tendsto (fun δ => Real.log R - Real.log δ) (𝓝[>] 0) atTop := by
          have h := tendsto_atTop_add_const_left _ (Real.log R)
            (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
          refine h.congr fun δ => ?_
          simp [sub_eq_add_neg]
        exact eq_zero_of_mul_le_of_tendsto measureReal_nonneg hx hg
          (key (fun z => Real.log R - Real.log z)
            (contDiffOn_const.sub (Real.contDiffOn_log.mono fun y hy => (mem_Ioi.1 hy).ne'))
            (fun c y hc hy => dynkinGen_log he4 hc hy)
            (fun y hy => sub_nonneg.2 (Real.log_le_log hy.1 hy.2)))
    exact (measureReal_eq_zero_iff).1 hreal
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null hA)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_sDrive hBc s ω).continuousOn
  refine mem_iUnion.2 ⟨⌈C⌉₊, hω, fun r hr => ?_⟩
  rw [← Real.norm_eq_abs]
  exact (hC r hr).trans (Nat.le_ceil C)

end Prob

/-! ## 5. Main result -/

/-- **RS-RL. Real points are never swallowed for `κ ≤ 4`.** Almost surely, for every real
`x ≠ 0` and every `T ≥ 0`, the forward SLE_κ flow from `x` exists on `[0,T]`.

Sources: Rohde–Schramm, *Basic properties of SLE*, Lemma 6.2 (pp. 23–24); Kemppainen, *SLE*,
Prop. 5.1 (pp. 78–80) and Prop. 5.2 (p. 80). -/
theorem ae_real_alive {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) :
    ∀ᵐ ω ∂P, ∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 0 ≤ T →
      ∃ v, IsForwardSol (drive κ B ω) (x : ℂ) T v := by
  have hBpre := hB.toIsPreBrownianReal
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  set B'' : ℝ≥0 → Ω → ℝ := fun t ω => B' t ω - B' 0 ω with hB''_def
  have hB''m : ∀ t, Measurable (B'' t) := fun t => (hB'm t).sub (hB'm 0)
  have hB''c : ∀ ω, Continuous (B'' · ω) := fun ω => (hB'c ω).sub continuous_const
  have hB''0 : ∀ ω, B'' 0 ω = 0 := fun ω => sub_self _
  have hBB : ∀ᵐ ω ∂P, ∀ t, B'' t ω = B t ω := by
    filter_upwards [hB'eq, hBpre.eval_zero_ae_eq_zero] with ω h h0 t
    simp only [hB''_def, h t, h 0, h0, sub_zero]
  have hB'' : IsPreBrownianReal B'' P := hBpre.congr fun t => hBB.mono fun ω h => (h t).symm
  have hs1 : √κ * √κ = κ := Real.mul_self_sqrt hκ.le
  have hs2 : -√κ * -√κ = κ := by rw [neg_mul_neg, hs1]
  have hall : ∀ᵐ ω ∂P, ∀ q : ℚ, ∀ n : ℕ, 0 < (q : ℝ) →
      (∃ v, IsForwardSol (sDrive (√κ) B'' ω) ((q : ℝ) : ℂ) ((n : ℝ≥0) : ℝ) v) ∧
      (∃ v, IsForwardSol (sDrive (-√κ) B'' ω) ((q : ℝ) : ℂ) ((n : ℝ≥0) : ℝ) v) := by
    rw [ae_all_iff]; intro q; rw [ae_all_iff]; intro n
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [ae_alive_of_pos hB'' hB''m hB''c hB''0 hκ hκ4 hs1 hq (n : ℝ≥0),
        ae_alive_of_pos hB'' hB''m hB''c hB''0 hκ hκ4 hs2 hq (n : ℝ≥0)] with ω h1 h2 _
      exact ⟨h1, h2⟩
    · exact ae_of_all _ fun ω h => absurd h hq
  filter_upwards [hall, hBB] with ω hω hBω x hx T hT
  have hdrive : drive κ B ω = sDrive (√κ) B'' ω := funext fun t => by simp [drive, sDrive, hBω]
  have hW0 : ∀ s, sDrive s B'' ω 0 = 0 := fun s => by simp [sDrive, hB''0]
  have hTn : T ≤ ((⌈T⌉₊ : ℝ≥0) : ℝ) := by rw [NNReal.coe_natCast]; exact Nat.le_ceil T
  rcases hx.lt_or_gt with hneg | hpos
  · obtain ⟨q, hq0, hqx⟩ := exists_rat_btwn (neg_pos.2 hneg)
    obtain ⟨u, hu⟩ := (hω q ⌈T⌉₊ hq0).2
    have hu' := isForwardSol_restrict hu hT hTn
    obtain ⟨v, hv⟩ := exists_isForwardSol_of_lt (continuous_sDrive hB''c _ ω) hT
      (by rw [hW0]; exact hq0) hqx hu'
    refine ⟨fun t => -v t, ?_⟩
    have h := isForwardSol_neg hv
    have hf : (fun t => -sDrive (-√κ) B'' ω t) = drive κ B ω := by
      rw [hdrive]; funext t; simp [sDrive]
    have hz : -(((-x : ℝ)) : ℂ) = (x : ℂ) := by push_cast; ring
    rw [hf, hz] at h
    exact h
  · obtain ⟨q, hq0, hqx⟩ := exists_rat_btwn hpos
    obtain ⟨u, hu⟩ := (hω q ⌈T⌉₊ hq0).1
    have hu' := isForwardSol_restrict hu hT hTn
    rw [hdrive]
    exact exists_isForwardSol_of_lt (continuous_sDrive hB''c _ ω) hT
      (by rw [hW0]; exact hq0) hqx hu'

end RS
end QuantumZipper
