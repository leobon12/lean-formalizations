import QuantumZipper.Proofs.Thm11.ClockIntegrable
import QuantumZipper.Proofs.Thm12.CharFun
import QuantumZipper.Proofs.Loewner.RealLine

/-!
# E3 (i)–(ii): collision of real points under the reverse flow, Wiener measure

Blueprint `E_BRANCH_BLUEPRINT.md` §4 E3. Driving function `V = √κ B` (`drive κ B`), `κ ∈ (0,4)`.
For `x < 0` the real reverse flow `u_t = x − V_t − ∫₀ᵗ 2/u_s ds` hits `0` at
`τ_x = realHitTime V x`.

1. **Tamed reverse real flow.** `revField ε z = 2/max(−Re z, ε)` (Lipschitz, bounded) agrees with
   `−2/z` on `{Re z ≤ −ε}`; `revZ W ε x` solves `U = x − W + ∫ revField ε U`.
2. **Dynkin for `u²`.** Its generator on `{Re z ≤ −ε}` is `κ − 4`. Stopping at the exit of
   `[−M, −ε]` capped at `T` gives `(4 − κ) E τ ≤ δ²` (`integral_exitTime_le`).
3. **(i)** `P(τ_{−δ} > t) ≤ δ²/((4−κ)t)` (`prob_realHitTime_gt_le`) and
   `E τ_{−δ} ≤ δ²/(4−κ)` (`lintegral_realHitTime_le`, a lower Lebesgue integral: measurability
   of `realHitTime` is not needed).
4. **(ii)** `x ∈ [−δ, 0) ⇒ τ_x ≤ τ_{−δ}` (`realHitTime_anti`, deterministic, by comparison with
   the tamed flow, whose drift is monotone).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

noncomputable section

namespace QuantumZipper
namespace Collision

open ClockInt NonSwallow RealLine FwdClock

variable {W : ℝ → ℝ}

/-! ### 1. The tamed reverse real flow -/

theorem one_mul_one' : (1 : ℝ) * 1 = 1 := by norm_num

/-- The clamped reverse real field `2/max(−Re z, ε)`; equals `−2/z` on `{Re z ≤ −ε}`. -/
def revField (ε : ℝ) (z : ℂ) : ℂ := realField 1 ε (-z)

theorem revField_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal (2 / ε ^ 2)) (revField ε) :=
  LipschitzWith.of_dist_le_mul fun z w => by
    have := (realField_lipschitz one_mul_one' hε).dist_le_mul (-z) (-w)
    rwa [dist_neg_neg] at this

theorem norm_revField_le {ε : ℝ} (hε : 0 < ε) (z : ℂ) : ‖revField ε z‖ ≤ 2 / ε :=
  norm_realField_le one_mul_one' hε _

theorem revField_of_le {ε : ℝ} {z : ℂ} (h : ε ≤ -z.re) :
    revField ε z = ((-2 / z.re : ℝ) : ℂ) := by
  unfold revField
  rw [realField_of_le one_mul_one' (by simpa using h)]
  congr 1
  simp [div_neg, neg_div]

theorem revField_re (ε : ℝ) (z : ℂ) : (revField ε z).re = 2 / max (-z.re) ε := by
  simp [revField, realField]

theorem revField_re_mono {ε : ℝ} (hε : 0 < ε) {a b : ℂ} (h : a.re ≤ b.re) :
    (revField ε a).re ≤ (revField ε b).re := by
  rw [revField_re, revField_re]
  exact div_le_div_of_nonneg_left (by norm_num) (hε.trans_le (le_max_right _ _))
    (max_le_max (by linarith) le_rfl)

theorem lipschitz_revField_shift {ε : ℝ} (hε : 0 < ε) (c : ℂ) :
    LipschitzWith (Real.toNNReal (2 / ε ^ 2)) (fun v => revField ε (v - c)) :=
  LipschitzWith.of_dist_le_mul fun v u => by
    have := (revField_lipschitz hε).dist_le_mul (v - c) (u - c)
    rwa [dist_sub_right] at this

/-- Global existence for the (uncentered) tamed reverse real field on `[0,T]`. -/
theorem exists_revUnc_sol (hW : Continuous W) {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : 0 ≤ T)
    (w : ℂ) :
    ∃ v : ℝ → ℂ, v 0 = w ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt v (revField ε (v t - W t)) (Icc 0 T) t := by
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_refl 0, hT⟩
  set t0 : Icc (0 : ℝ) T := ⟨0, h0mem⟩ with ht0_def
  have ht0_coe : (t0 : ℝ) = 0 := rfl
  have hf : IsPicardLindelof (fun t v => revField ε (v - W t)) t0 w
      (Real.toNNReal (2 / ε * T)) 0 (Real.toNNReal (2 / ε)) (Real.toNNReal (2 / ε ^ 2)) := by
    refine ⟨fun t _ => (lipschitz_revField_shift hε _).lipschitzOnWith,
      fun x _ => ?_, ?_, ?_⟩
    · exact ((revField_lipschitz hε).continuous.comp
        (continuous_const.sub (Complex.continuous_ofReal.comp hW))).continuousOn
    · intro t _ x _
      rw [Real.coe_toNNReal _ (by positivity)]
      exact norm_revField_le hε _
    · simp only [ht0_coe, sub_zero, NNReal.coe_zero, max_eq_left hT,
        Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 2 / ε),
        Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 2 / ε * T), le_refl]
  have hx : w ∈ Metric.closedBall w ((0 : ℝ≥0) : ℝ) := Metric.mem_closedBall_self (le_refl _)
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, ?_, ?_⟩
  · show α.compProj (t0 : ℝ) = w
    rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · intro t ht
    apply (ODE.hasDerivWithinAt_picard_Icc t0.2 hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn (fun _ ht' ↦ α.compProj_mem_closedBall hf.mul_max_le)
      w ht).congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

open Classical in
/-- The un-centered tamed reverse real flow (junk `0` unless `W` is continuous and `ε > 0`). -/
def revUnc (W : ℝ → ℝ) (ε : ℝ) (x : ℂ) (t : ℝ) : ℂ :=
  if h : Continuous W ∧ 0 < ε then
    Classical.choose (exists_revUnc_sol h.1 h.2 (le_max_right t 0) x) t else 0

/-- The centered tamed reverse real flow. -/
def revZ (W : ℝ → ℝ) (ε : ℝ) (x : ℂ) (t : ℝ) : ℂ := revUnc W ε x t - W t

theorem revUnc_eq_of_sol (hW : Continuous W) {ε : ℝ} (hε : 0 < ε) {T : ℝ}
    {V : ℝ → ℂ} {x : ℂ} (hV0 : V 0 = x)
    (hV : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt V (revField ε (V t - W t)) (Icc 0 T) t) :
    ∀ t ∈ Icc (0 : ℝ) T, revUnc W ε x t = V t := by
  intro t ht
  rw [revUnc, dif_pos ⟨hW, hε⟩]
  obtain ⟨hv0, hvd⟩ := Classical.choose_spec (exists_revUnc_sol hW hε (le_max_right t 0) x)
  set v := Classical.choose (exists_revUnc_sol hW hε (le_max_right t 0) x) with hvdef
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 (max t 0) := Icc_subset_Icc_right (le_max_left _ _)
  have hsubT : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have key := ODE_solution_unique (v := fun s v => revField ε (v - (W s : ℂ)))
    (fun s => lipschitz_revField_shift hε _) (f := v) (g := V) (a := 0) (b := t)
    (fun s hs => (hvd s (hsub hs)).continuousWithinAt.mono hsub)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc ((hvd s (hsub (Ico_subset_Icc_self hs))).mono hsub)
      hs)
    (fun s hs => (hV s (hsubT hs)).continuousWithinAt.mono hsubT)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc ((hV s (hsubT (Ico_subset_Icc_self hs))).mono hsubT)
      hs)
    (by rw [hv0, hV0])
  exact key ⟨ht.1, le_rfl⟩

theorem revUnc_zero (hW : Continuous W) {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    revUnc W ε x 0 = x := by
  rw [revUnc, dif_pos ⟨hW, hε⟩]
  exact (Classical.choose_spec (exists_revUnc_sol hW hε (le_max_right 0 0) x)).1

theorem revUnc_hasDerivWithinAt (hW : Continuous W) {ε : ℝ} (hε : 0 < ε)
    {T : ℝ} (hT : 0 ≤ T) (x : ℂ) :
    ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (revUnc W ε x) (revField ε (revZ W ε x t)) (Icc 0 T) t := by
  obtain ⟨v, hv0, hvd⟩ := exists_revUnc_sol hW hε hT x
  have heq := revUnc_eq_of_sol hW hε hv0 hvd
  intro t ht
  have e : revZ W ε x t = v t - W t := by rw [revZ, heq t ht]
  rw [e]
  exact (hvd t ht).congr_of_mem heq ht

theorem continuousOn_revZ (hW : Continuous W) {ε : ℝ} (hε : 0 < ε) {T : ℝ}
    (hT : 0 ≤ T) (x : ℂ) : ContinuousOn (revZ W ε x) (Icc 0 T) :=
  have h : ContinuousOn (revUnc W ε x) (Icc 0 T) := fun t ht =>
    (revUnc_hasDerivWithinAt hW hε hT x t ht).continuousWithinAt
  h.sub (Complex.continuous_ofReal.comp hW).continuousOn

/-- Integral equation of the tamed reverse real flow. -/
theorem revZ_eq (hW : Continuous W) {ε : ℝ} (hε : 0 < ε) (x : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    revZ W ε x t = x - W t + ∫ s in (0 : ℝ)..t, revField ε (revZ W ε x s) := by
  have hcont : ContinuousOn (revUnc W ε x) (Icc 0 t) := fun s hs =>
    (revUnc_hasDerivWithinAt hW hε ht x s hs).continuousWithinAt
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) t,
      HasDerivAt (revUnc W ε x) (revField ε (revZ W ε x s)) s := fun s hs =>
    (revUnc_hasDerivWithinAt hW hε ht x s (Ioo_subset_Icc_self hs)).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)
  have hint : IntervalIntegrable (fun s => revField ε (revZ W ε x s)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht]
    exact (revField_lipschitz hε).continuous.comp_continuousOn (continuousOn_revZ hW hε ht x)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcont hderiv hint
  rw [revUnc_zero hW hε] at key
  show revUnc W ε x t - W t = _
  rw [key]; ring

theorem integral_revField_eq (ε : ℝ) (f : ℝ → ℂ) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, revField ε (f s)) = ((∫ s in (0 : ℝ)..t, (revField ε (f s)).re : ℝ) : ℂ) := by
  rw [← intervalIntegral.integral_ofReal]
  congr 1

/-- The real part of the integral equation, for a real starting point. -/
theorem revZ_re_eq (hW : Continuous W) {ε : ℝ} (hε : 0 < ε) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (revZ W ε x t).re = x - W t + ∫ s in (0 : ℝ)..t, (revField ε (revZ W ε x s)).re := by
  rw [revZ_eq hW hε x ht, integral_revField_eq]
  simp

/-- The tamed reverse flow from a real point stays real. -/
theorem im_revZ (hW : Continuous W) {ε : ℝ} (hε : 0 < ε) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (revZ W ε x t).im = 0 := by
  rw [revZ_eq hW hε x ht, integral_revField_eq]
  simp

theorem revZ_integralEq {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous fun t => B t ω)
    {ε : ℝ} (hε : 0 < ε) (κ : ℝ) (x : ℂ) (ω : Ω) (t : ℝ≥0) :
    revZ (drive κ B ω) ε x t = x
      + (∫ r in (0 : ℝ)..t, revField ε (revZ (drive κ B ω) ε x (r.toNNReal : ℝ)))
      + B t ω • (-((Real.sqrt κ : ℝ) : ℂ)) := by
  rw [revZ_eq (continuous_drive_ns hBc κ ω) hε x t.coe_nonneg]
  have hint : ∫ s in (0 : ℝ)..t, revField ε (revZ (drive κ B ω) ε x s)
      = ∫ r in (0 : ℝ)..t, revField ε (revZ (drive κ B ω) ε x (r.toNNReal : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le t.coe_nonneg] at hr
    simp only [Real.coe_toNNReal r hr.1]
  rw [hint]
  simp only [drive, Real.toNNReal_coe, Complex.real_smul]
  push_cast
  ring

/-! ### 2. Deterministic comparison facts -/

/-- A real reverse solution staying in `{u ≤ −ε}` is the tamed flow. -/
theorem revZ_eq_of_isRealRevSol (hW : Continuous W) {ε : ℝ} (hε : 0 < ε) {x T : ℝ}
    {u : ℝ → ℝ} (h : IsRealRevSol W x T u) (hreg : ∀ t ∈ Icc (0 : ℝ) T, ε ≤ -u t) :
    ∀ t ∈ Icc (0 : ℝ) T, revZ W ε x t = u t := by
  intro t₁ ht₁
  have hT : 0 ≤ T := ht₁.1.trans ht₁.2
  set V : ℝ → ℂ := fun t => ((u t + W t : ℝ) : ℂ) with hVdef
  have hV0 : V 0 = x := by
    simp only [hVdef, isRealRevSol_zero h hT]; push_cast; ring
  have hV : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt V (revField ε (V t - W t)) (Icc 0 T) t := by
    intro t ht
    have hd := (isRealRevSol_hasDerivWithinAt h ht).ofReal_comp
    have e : V t - W t = ((u t : ℝ) : ℂ) := by simp only [hVdef]; push_cast; ring
    rw [e, revField_of_le (by simpa using hreg t ht), Complex.ofReal_re]
    exact hd
  rw [revZ, revUnc_eq_of_sol hW hε hV0 hV t₁ ht₁]
  simp only [hVdef]; push_cast; ring

theorem lt_zero_of_isRealRevSol {x T : ℝ} {u : ℝ → ℝ} (h : IsRealRevSol W x T u)
    (hx : x < W 0) : ∀ t ∈ Icc (0 : ℝ) T, u t < 0 := by
  intro t ht
  by_contra hcon
  push Not at hcon
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0 : u 0 < 0 := by rw [isRealRevSol_zero h hT]; linarith
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc ht.1 (h.1.mono (Icc_subset_Icc_right ht.2))
    (show (0 : ℝ) ∈ Icc (u 0) (u t) from ⟨h0.le, hcon⟩)
  exact (h.2 c ⟨hc.1, hc.2.trans ht.2⟩).1 hc0

/-- Quantitative bounds `c ≤ −u ≤ K` for a real reverse solution from `x < W 0`. -/
theorem exists_bounds_isRealRevSol {x T : ℝ} {u : ℝ → ℝ} (h : IsRealRevSol W x T u)
    (hT : 0 ≤ T) (hx : x < W 0) :
    ∃ c > 0, ∃ K, ∀ t ∈ Icc (0 : ℝ) T, c ≤ -u t ∧ -u t ≤ K := by
  obtain ⟨c, hc, hcu⟩ := exists_pos_le_abs_isRealRevSol h hT
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn h.1
  refine ⟨c, hc, K, fun t ht => ⟨?_, ?_⟩⟩
  · have := hcu t ht
    rwa [abs_of_neg (lt_zero_of_isRealRevSol h hx t ht)] at this
  · have := hK t ht
    rw [Real.norm_eq_abs] at this
    exact (neg_le_abs _).trans this

/-- **E3 (ii), deterministic.** Real points closer to `W 0` (from the left) are hit first:
`x₁ ≤ x₂ < W 0 ⇒ τ_{x₂} ≤ τ_{x₁}`. -/
theorem realHitTime_anti (hW : Continuous W) {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) (hx₂ : x₂ < W 0) :
    realHitTime W x₂ ≤ realHitTime W x₁ := by
  rcases hx.eq_or_lt with rfl | hlt
  · exact le_rfl
  show (⨆ (T : ℝ) (_ : 0 ≤ T) (_ : ∃ u, IsRealRevSol W x₂ T u), ENNReal.ofReal T) ≤ _
  refine iSup_le fun T => iSup_le fun hT => iSup_le fun ⟨u₂, h₂⟩ => ?_
  obtain ⟨c, hc, K, hcK⟩ := exists_bounds_isRealRevSol h₂ hT hx₂
  set Z : ℝ → ℂ := revZ W c x₁ with hZ
  set U : ℝ → ℝ := fun t => (Z t).re with hU
  have hZc : ContinuousOn Z (Icc 0 T) := continuousOn_revZ hW hc hT x₁
  have hUc : ContinuousOn U (Icc 0 T) := Complex.continuous_re.comp_continuousOn hZc
  have hfc : ContinuousOn (fun s => (revField c (Z s)).re) (Icc 0 T) :=
    Complex.continuous_re.comp_continuousOn ((revField_lipschitz hc).continuous.comp_continuousOn hZc)
  have hgc : ContinuousOn (fun s => -(2 / u₂ s)) (Icc 0 T) :=
    (continuousOn_const.div h₂.1 fun s hs => (h₂.2 s hs).1).neg
  -- comparison: `U < u₂` on `[0,T]`
  have hcomp : ∀ t ∈ Icc (0 : ℝ) T, U t < u₂ t := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t₀, ht₀, ht₀le⟩ := hcon
    set S : Set ℝ := Icc 0 T ∩ (fun t => u₂ t - U t) ⁻¹' Iic 0 with hS
    have hScl : IsClosed S := (h₂.1.sub hUc).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hSne : S.Nonempty := ⟨t₀, ht₀, (mem_Iic.2 (by linarith) : u₂ t₀ - U t₀ ∈ Iic 0)⟩
    have hSbdd : BddBelow S := ⟨0, fun _ h => h.1.1⟩
    set s := sInf S with hs
    have hsS : s ∈ S := hScl.csInf_mem hSne hSbdd
    have hsI : s ∈ Icc (0 : ℝ) T := hsS.1
    have hpos : ∀ r ∈ Icc (0 : ℝ) T, r < s → U r < u₂ r := by
      intro r hr hrs
      by_contra hh
      push Not at hh
      have : s ≤ r := csInf_le hSbdd ⟨hr, (mem_Iic.2 (by linarith) : u₂ r - U r ∈ Iic 0)⟩
      linarith
    have hsub : uIcc (0 : ℝ) s ⊆ Icc 0 T := by
      rw [uIcc_of_le hsI.1]; exact Icc_subset_Icc_right hsI.2
    have hmono : ∫ r in (0 : ℝ)..s, (revField c (Z r)).re ≤ ∫ r in (0 : ℝ)..s, -(2 / u₂ r) := by
      refine intervalIntegral.integral_mono_ae_restrict hsI.1 ((hfc.mono hsub).intervalIntegrable)
        ((hgc.mono hsub).intervalIntegrable) ?_
      have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ s := by
        rw [ae_iff]; simp
      filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem measurableSet_Icc] with r hr hrI
      have hrT : r ∈ Icc (0 : ℝ) T := ⟨hrI.1, hrI.2.trans hsI.2⟩
      have hlt := hpos r hrT (lt_of_le_of_ne hrI.2 hr)
      have h1 := revField_re_mono hc (a := Z r) (b := ((u₂ r : ℝ) : ℂ)) (by simpa [hU] using hlt.le)
      rw [revField_of_le (z := ((u₂ r : ℝ) : ℂ)) (by simpa using (hcK r hrT).1)] at h1
      simpa [neg_div] using h1
    have hUs : U s = x₁ - W s + ∫ r in (0 : ℝ)..s, (revField c (Z r)).re :=
      revZ_re_eq hW hc x₁ hsI.1
    have hus : u₂ s = x₂ - W s - ∫ r in (0 : ℝ)..s, 2 / u₂ r := (h₂.2 s hsI).2
    have hneg : (∫ r in (0 : ℝ)..s, -(2 / u₂ r)) = -∫ r in (0 : ℝ)..s, 2 / u₂ r :=
      intervalIntegral.integral_neg
    have hsle : u₂ s - U s ≤ 0 := hsS.2
    linarith
  have hsol : IsRealRevSol W x₁ T U := by
    refine ⟨hUc, fun t ht => ⟨?_, ?_⟩⟩
    · have := hcomp t ht
      have := (hcK t ht).1
      intro h0; linarith
    · have hreg : ∀ s ∈ Icc (0 : ℝ) T, c ≤ -(Z s).re := fun s hs => by
        have := hcomp s hs; have := (hcK s hs).1
        show c ≤ -U s
        linarith
      have hUt : U t = x₁ - W t + ∫ s in (0 : ℝ)..t, (revField c (Z s)).re :=
        revZ_re_eq hW hc x₁ ht.1
      rw [hUt]
      have hint : (∫ s in (0 : ℝ)..t, (revField c (Z s)).re) = -∫ s in (0 : ℝ)..t, 2 / U s := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ht.1] at hs
        simp only
        rw [revField_of_le (hreg s ⟨hs.1, hs.2.trans ht.2⟩)]
        simp [hU, neg_div]
      rw [hint]; ring
  exact ofReal_le_realHitTime hT hsol

/-! ### 3. Dynkin for `u²` -/

/-- `Φ(z) = (Re z)²`. -/
def sqRe (z : ℂ) : ℝ := z.re ^ 2

theorem contDiff_sqRe {n : WithTop ℕ∞} : ContDiff ℝ n sqRe :=
  (Complex.reCLM.contDiff (n := n)).pow 2

theorem hasFDerivAt_sqRe (z : ℂ) : HasFDerivAt sqRe ((2 * z.re) • Complex.reCLM) z := by
  have hre : HasFDerivAt (fun z : ℂ => z.re) Complex.reCLM z := Complex.reCLM.hasFDerivAt
  refine (hre.pow 2).congr_fderiv ?_
  ext w
  simp [smul_eq_mul]

theorem fderiv_sqRe_apply (z w : ℂ) : fderiv ℝ sqRe z w = 2 * z.re * w.re := by
  rw [(hasFDerivAt_sqRe z).fderiv]
  simp [smul_eq_mul]

/-- **Generator of `u²`** where the clamp is inactive: `L(u²) = κ − 4`. -/
theorem dynkinGen_sqRe {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) {z : ℂ} (hz : ε ≤ -z.re) :
    dynkinGen (revField ε) (-((Real.sqrt κ : ℝ) : ℂ)) sqRe z = κ - 4 := by
  have hz0 : z.re ≠ 0 := by intro h; rw [h] at hz; linarith
  have hqd : HasDerivAt (fun s : ℝ => z.re + s * (-Real.sqrt κ)) (-Real.sqrt κ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (-Real.sqrt κ)).const_add z.re
  have hφ := (hqd.const_mul 2).mul_const (-Real.sqrt κ)
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ),
      fderiv ℝ sqRe (z + ((s : ℝ) : ℂ) * (-((Real.sqrt κ : ℝ) : ℂ))) (-((Real.sqrt κ : ℝ) : ℂ)) =
      (fun s : ℝ => 2 * (z.re + s * (-Real.sqrt κ)) * (-Real.sqrt κ)) s :=
    Filter.Eventually.of_forall fun s => by
      rw [fderiv_sqRe_apply]; simp
  have hC2 : ContDiffAt ℝ 2 sqRe z := contDiff_sqRe.contDiffAt
  unfold dynkinGen
  rw [revField_of_le hz, fderiv_sqRe_apply, iteratedFDeriv_two_eq_of_line hC2 _ hev hφ]
  simp only [Complex.ofReal_re]
  have h1 : z.re * z.re⁻¹ = 1 := mul_inv_cancel₀ hz0
  have h2 : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ
  linear_combination (-4) * h1 + h2

/-- A `C³` function with bounded derivatives agreeing with `(Re z)²` near the real segment
`{ε ≤ −Re z ≤ M, Im z = 0}`. -/
theorem exists_sqRe_cutoff {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) :
    ∃ F : ℂ → ℝ, ∃ C : ℝ, ContDiff ℝ 3 F ∧
      (∀ x, |F x| ≤ C ∧ ‖fderiv ℝ F x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 F x‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 3 F x‖ ≤ C) ∧
      ∀ z ∈ rReg (-1) ε M 0, F =ᶠ[𝓝 z] sqRe := by
  have hσ : (-1 : ℝ) * (-1) = 1 := by norm_num
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
      (isOpen_rOpen (-1) (ε / 4) (4 * M) 1) (isClosed_rReg (-1) (ε / 2) (2 * M) (1 / 2))
      (rReg_subset_rOpen (by linarith) (by linarith) (by norm_num))
  have hts : tsupport χ ⊆ rReg (-1) (ε / 4) (4 * M) 1 := by
    rw [tsupport, hχs]; exact closure_minimal rOpen_subset_rReg (isClosed_rReg _ _ _ _)
  have hχc : HasCompactSupport χ :=
    (isCompact_rReg hσ _ _ _).of_isClosed_subset (isClosed_tsupport χ) hts
  set F : ℂ → ℝ := χ * sqRe with hFdef
  have hFs : ContDiff ℝ 3 F := (hχ.of_le three_le_smooth).mul contDiff_sqRe
  have hFc : HasCompactSupport F := hχc.mul_right
  obtain ⟨C0, h0⟩ := hFs.continuous.bounded_above_of_compact_support hFc
  obtain ⟨C1, h1⟩ := (hFs.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hFc.fderiv (𝕜 := ℝ))
  obtain ⟨C2, h2⟩ := (hFs.continuous_iteratedFDeriv (m := 2) (by norm_num)).bounded_above_of_compact_support
    (hFc.iteratedFDeriv 2)
  obtain ⟨C3, h3⟩ := (hFs.continuous_iteratedFDeriv (m := 3) le_rfl).bounded_above_of_compact_support
    (hFc.iteratedFDeriv 3)
  refine ⟨F, max (max C0 C1) (max C2 C3), hFs, fun x => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← Real.norm_eq_abs]
    exact (h0 x).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (h1 x).trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact (h2 x).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h3 x).trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro z hz
    have hmem : rOpen (-1) (ε / 2) (2 * M) (1 / 2) ∈ 𝓝 z :=
      (isOpen_rOpen _ _ _ _).mem_nhds
        (rReg_subset_rOpen (by linarith) (by linarith) (by norm_num) hz)
    filter_upwards [hmem] with y hy
    have : χ y = 1 := (hχ1 y).1 (rOpen_subset_rReg hy)
    simp [hFdef, this]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The exit time of the tamed reverse flow from `−δ` out of `(−M, −ε)`, capped at `T`. -/
def exitTime (B : ℝ≥0 → Ω → ℝ) (κ ε M δ : ℝ) (T : ℝ≥0) : Ω → ℝ≥0 :=
  hittingBtwn (fun t ω => revZ (drive κ B ω) ε ((-δ : ℝ) : ℂ) t) (rExit (-1) ε M) 0 T

/-- **Dynkin for `u²`.** `(4 − κ) E τ ≤ δ²` for the capped exit time `τ`. -/
theorem integral_exitTime_le (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {δ ε M : ℝ} (hε : 0 < ε) (hεδ : ε < δ) (hδM : δ < M) (T : ℝ≥0) :
    Measurable (exitTime B κ ε M δ T) ∧
      (4 - κ) * ∫ ω, (exitTime B κ ε M δ T ω : ℝ) ∂P ≤ δ ^ 2 := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hM : 0 < M := by linarith
  set e : ℂ := -((Real.sqrt κ : ℝ) : ℂ) with he
  set 𝓕 := bmFilt hBm with h𝓕
  set x : ℝ := -δ with hx
  set U : ℝ≥0 → Ω → ℂ := fun t ω => revZ (drive κ B ω) ε (x : ℂ) t with hUdef
  have hU : ∀ ω (t : ℝ≥0),
      U t ω = (x : ℂ) + (∫ r in (0 : ℝ)..t, revField ε (U r.toNNReal ω)) + B t ω • e :=
    fun ω t => revZ_integralEq hBc hε κ x ω t
  have hbM : ∀ z, ‖revField ε z‖ ≤ 2 / ε := norm_revField_le hε
  have hb := revField_lipschitz hε
  have hUc : ∀ ω, Continuous (U · ω) :=
    Dynkin.continuous_of_integralEq hBc hb.continuous hbM hU
  have hUm : ∀ t, Measurable[𝓕 t] (U t) :=
    Dynkin.measurable_of_integralEq 𝓕 (bmFilt_adapted hBm) hBc hb hbM hU hUc
  have hUim : ∀ ω (t : ℝ≥0), (U t ω).im = 0 := fun ω t =>
    im_revZ (continuous_drive_ns hBc κ ω) hε x t.coe_nonneg
  obtain ⟨F, C, hF, hFC, hFV⟩ := exists_sqRe_cutoff hε hM
  set E := rExit (-1) ε M with hE
  set τ : Ω → ℝ≥0 := hittingBtwn U E 0 T with hτdef
  have hτe : exitTime B κ ε M δ T = τ := rfl
  rw [hτe]
  have hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)) :=
    ItoLite.isStoppingTime_hittingBtwn_of_isClosed hUm hUc (isClosed_rExit (-1) ε M) T
  have hτT : ∀ ω, τ ω ≤ T := fun ω => hittingBtwn_le ω
  have hB0 := hB.eval_zero_ae_eq_zero
  have hU0' : ∀ ω, B 0 ω = 0 → U 0 ω = x := by
    intro ω hω; rw [hU ω 0]; simp [hω]
  have hU0 : ∀ᵐ ω ∂P, U 0 ω = x := by
    filter_upwards [hB0] with ω hω using hU0' ω hω
  obtain ⟨hint, hzero⟩ := dynkin_stopped hB hBc 𝓕 (bmFilt_adapted hBm) (bmFilt_le_past hBm)
    hb hbM hU hF (fun z => (hFC z).2) (fun z => (hFC z).1) hU0 hτ T hτT
  have hxK : (x : ℂ) ∈ rReg (-1) ε M 0 :=
    ⟨by simp only [Complex.ofReal_re, hx]; linarith, by simp only [Complex.ofReal_re, hx]; linarith,
      by simp⟩
  have hK : ∀ ω, B 0 ω = 0 → ∀ t ≤ τ ω, U t ω ∈ rReg (-1) ε M 0 := by
    intro ω hω
    refine mem_of_le_of_forall_lt (isClosed_rReg (-1) ε M 0) (hUc ω) ?_ ?_
    · rw [hU0' ω hω]; exact hxK
    · intro t ht
      have hnot : U t ω ∉ E := notMem_of_lt_hittingBtwn ht zero_le
      simp only [hE, rExit, mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
      exact ⟨hnot.1.le, hnot.2.le, by rw [hUim ω t, abs_zero]⟩
  -- the generator integral along the stopped path
  have hGint : ∀ ω, B 0 ω = 0 →
      ∫ r in (0 : ℝ)..(τ ω), dynkinGen (revField ε) e F (U r.toNNReal ω) = (τ ω : ℝ) * (κ - 4) := by
    intro ω hω
    have : ∫ r in (0 : ℝ)..(τ ω), dynkinGen (revField ε) e F (U r.toNNReal ω)
        = ∫ r in (0 : ℝ)..(τ ω), (κ - 4) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le (NNReal.coe_nonneg _)] at hr
      have hle : r.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.2 hr.2
      have hmem := hK ω hω _ hle
      simp only
      rw [dynkinGen_congr (hFV _ hmem), dynkinGen_sqRe hκ.le hε (by linarith [hmem.1])]
    rw [this, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hτm : Measurable τ := by
    refine measurable_of_Iic fun y => ?_
    have h := 𝓕.le y _ (hτ y)
    have e : τ ⁻¹' Iic y = {ω | ((τ ω : ℝ≥0) : WithTop ℝ≥0) ≤ (y : WithTop ℝ≥0)} := by
      ext ω; simp only [mem_preimage, mem_Iic]; exact WithTop.coe_le_coe.symm
    rw [e]; exact h
  refine ⟨hτm, ?_⟩
  have hτr : Measurable fun ω => (τ ω : ℝ) := measurable_coe_nnreal_real.comp hτm
  have hτi : Integrable (fun ω => (τ ω : ℝ)) P :=
    ItoLite.integrable_of_bound_abs hτr.stronglyMeasurable (K := T) fun ω => by
      rw [abs_of_nonneg (NNReal.coe_nonneg _)]; exact_mod_cast hτT ω
  have hFx : F x = δ ^ 2 := by
    rw [(hFV x hxK).eq_of_nhds]; simp [sqRe, hx]
  have hle : ∀ᵐ ω ∂P, (4 - κ) * (τ ω : ℝ) ≤ (F (U (τ ω) ω) - F x
      - ∫ r in (0 : ℝ)..(τ ω), dynkinGen (revField ε) e F (U r.toNNReal ω)) + F x := by
    filter_upwards [hB0] with ω hω
    rw [hGint ω hω]
    have hFU : 0 ≤ F (U (τ ω) ω) := by
      rw [(hFV _ (hK ω hω _ le_rfl)).eq_of_nhds]; exact sq_nonneg _
    linarith
  have hI : Integrable (fun ω => (F (U (τ ω) ω) - F x
      - ∫ r in (0 : ℝ)..(τ ω), dynkinGen (revField ε) e F (U r.toNNReal ω)) + F x) P :=
    hint.add (integrable_const (F x))
  have h1 := integral_mono_ae (hτi.const_mul (4 - κ)) hI hle
  rw [integral_add hint (integrable_const _), hzero, integral_const, integral_const_mul] at h1
  simpa [hFx] using h1

/-- The exit time is at least the lifetime of a real solution staying strictly inside. -/
theorem le_exitTime (hBc : ∀ ω, Continuous fun t => B t ω) {κ ε M δ : ℝ} (hε : 0 < ε)
    {T : ℝ≥0} {ω : Ω} {s : ℝ} {u : ℝ → ℝ} (h : IsRealRevSol (drive κ B ω) (-δ) s u)
    (hs : 0 ≤ s) (hsT : s ≤ T) (hreg : ∀ r ∈ Icc (0 : ℝ) s, ε < -u r ∧ -u r < M) :
    s.toNNReal ≤ exitTime B κ ε M δ T ω := by
  by_contra hlt
  push Not at hlt
  have hsT' : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hsT
  obtain ⟨j, hj, hjE⟩ := (hittingBtwn_lt_iff (s.toNNReal) hsT').1 hlt
  have hjs : (j : ℝ) ∈ Icc (0 : ℝ) s :=
    ⟨j.coe_nonneg, (Real.le_toNNReal_iff_coe_le hs).1 hj.2.le⟩
  have heq := revZ_eq_of_isRealRevSol (continuous_drive_ns hBc κ ω) hε h
    (fun r hr => (hreg r hr).1.le) j hjs
  have hjE' : revZ (drive κ B ω) ε ((-δ : ℝ) : ℂ) j ∈ rExit (-1) ε M := hjE
  rw [heq] at hjE'
  have := hreg j hjs
  simp only [rExit, mem_union, Set.mem_ofPred_eq, Complex.ofReal_re] at hjE'
  rcases hjE' with h1 | h1 <;> linarith

theorem lintegral_exitTime_le (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {δ ε M : ℝ} (hε : 0 < ε) (hεδ : ε < δ) (hδM : δ < M) (T : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (exitTime B κ ε M δ T ω : ℝ) ∂P ≤ ENNReal.ofReal (δ ^ 2 / (4 - κ)) := by
  obtain ⟨hm, hle⟩ := integral_exitTime_le hB hBm hBc hκ hκ4 hε hεδ hδM T (P := P)
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hτr : Measurable fun ω => (exitTime B κ ε M δ T ω : ℝ) := measurable_coe_nnreal_real.comp hm
  have hτi : Integrable (fun ω => (exitTime B κ ε M δ T ω : ℝ)) P :=
    ItoLite.integrable_of_bound_abs hτr.stronglyMeasurable (K := T) fun ω => by
      rw [abs_of_nonneg (NNReal.coe_nonneg _)]; exact NNReal.coe_le_coe.2 (hittingBtwn_le ω : exitTime B κ ε M δ T ω ≤ T)
  rw [← ofReal_integral_eq_lintegral_ofReal hτi (ae_of_all _ fun ω => NNReal.coe_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [le_div_iff₀ (by linarith)]
  linarith

/-! ### 4. E3 (i) -/

theorem nat_bounds {δ c K r : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → δ / (n + 2) < c ∧ K < (n + 2) * δ ∧ r ≤ n := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max (δ / c) (max (K / δ) r))
  refine ⟨N, fun n hn => ?_⟩
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : δ / c ≤ n := (le_max_left _ _).trans (hN.trans hn')
  have h2 : K / δ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans (hN.trans hn')
  have h3 : r ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans (hN.trans hn')
  have hn2 : (0 : ℝ) < n + 2 := by positivity
  refine ⟨?_, ?_, h3⟩
  · rw [div_lt_iff₀ hn2]
    rw [div_le_iff₀ hc] at h1
    nlinarith
  · rw [div_le_iff₀ hδ] at h2
    nlinarith

theorem prob_realHitTime_gt_le_of_good (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) :
    P {ω | ENNReal.ofReal t < realHitTime (drive κ B ω) (-δ)}
      ≤ ENNReal.ofReal (δ ^ 2 / ((4 - κ) * t)) := by
  set G : ℕ → Set Ω := fun n => {ω | ∃ u, IsRealRevSol (drive κ B ω) (-δ) t u ∧
    ∀ r ∈ Icc (0 : ℝ) t, δ / (n + 2) < -u r ∧ -u r < (n + 2) * δ} with hG
  have hGmono : Monotone G := by
    intro n m hnm ω ⟨u, hu, hb⟩
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    refine ⟨u, hu, fun r hr => ⟨?_, ?_⟩⟩
    · refine lt_of_le_of_lt ?_ (hb r hr).1
      exact div_le_div_of_nonneg_left hδ.le (by positivity) (by linarith)
    · refine (hb r hr).2.trans_le ?_
      nlinarith
  have hsub : {ω | ENNReal.ofReal t < realHitTime (drive κ B ω) (-δ)} ≤ᵐ[P] ⋃ n, G n := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω hmem
    have hmem' : ENNReal.ofReal t < realHitTime (drive κ B ω) (-δ) := hmem
    obtain ⟨u, hu⟩ := exists_isRealRevSol_of_lt_realHitTime hmem'
    have hW0 : drive κ B ω 0 = 0 := drive_zero_of hω
    obtain ⟨c, hc, K, hcK⟩ := exists_bounds_isRealRevSol hu ht.le (by rw [hW0]; linarith)
    obtain ⟨N, hN⟩ := nat_bounds (K := K) (r := 0) hδ hc
    obtain ⟨h1, h2, -⟩ := hN N le_rfl
    exact mem_iUnion.2 ⟨N, u, hu, fun r hr =>
      ⟨h1.trans_le (hcK r hr).1, (hcK r hr).2.trans_lt h2⟩⟩
  have hGle : ∀ n, P (G n) ≤ ENNReal.ofReal (δ ^ 2 / ((4 - κ) * t)) := by
    intro n
    have hε : (0 : ℝ) < δ / (n + 2) := by positivity
    have hεδ : δ / (n + 2) < δ := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    have hδM : δ < (n + 2) * δ := by nlinarith
    obtain ⟨hm, -⟩ := integral_exitTime_le hB hBm hBc hκ hκ4 hε hεδ hδM t.toNNReal (P := P)
    have hL := lintegral_exitTime_le hB hBm hBc hκ hκ4 hε hεδ hδM t.toNNReal (P := P)
    set f : Ω → ℝ≥0∞ := fun ω =>
      ENNReal.ofReal (exitTime B κ (δ / (n + 2)) ((n + 2) * δ) δ t.toNNReal ω : ℝ) with hf
    have hfm : Measurable f := ENNReal.measurable_ofReal.comp (measurable_coe_nnreal_real.comp hm)
    have hGf : G n ⊆ {ω | ENNReal.ofReal t ≤ f ω} := by
      rintro ω ⟨u, hu, hb⟩
      have := le_exitTime hBc hε hu ht.le (by rw [Real.coe_toNNReal _ ht.le]) hb (M := (n + 2) * δ)
        (T := t.toNNReal)
      show ENNReal.ofReal t ≤ ENNReal.ofReal _
      apply ENNReal.ofReal_le_ofReal
      have := NNReal.coe_le_coe.2 this
      rwa [Real.coe_toNNReal _ ht.le] at this
    have hMk := mul_meas_ge_le_lintegral₀ hfm.aemeasurable (ENNReal.ofReal t) (μ := P)
    have hA : ENNReal.ofReal t * P (G n) ≤ ENNReal.ofReal (δ ^ 2 / (4 - κ)) :=
      ((mul_le_mul' le_rfl (measure_mono hGf)).trans hMk).trans hL
    rw [← div_div, ENNReal.ofReal_div_of_pos ht,
      ENNReal.le_div_iff_mul_le (Or.inl (by simpa using ht)) (Or.inl ENNReal.ofReal_ne_top),
      mul_comm]
    exact hA
  calc P {ω | ENNReal.ofReal t < realHitTime (drive κ B ω) (-δ)} ≤ P (⋃ n, G n) :=
        measure_mono_ae hsub
    _ = ⨆ n, P (G n) := hGmono.measure_iUnion
    _ ≤ _ := iSup_le hGle

/-- Passing from `IsBrownianReal` to a good version. -/
theorem exists_good_drive (hB : IsBrownianReal B P) :
    ∃ B' : ℝ≥0 → Ω → ℝ, IsPreBrownianReal B' P ∧ (∀ r, Measurable (B' r)) ∧
      (∀ ω, Continuous fun t => B' t ω) ∧ ∀ κ, ∀ᵐ ω ∂P, drive κ B' ω = drive κ B ω := by
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  refine ⟨B', hB.toIsPreBrownianReal.congr fun r => ?_, hB'm, hB'c, fun κ => ?_⟩
  · filter_upwards [hB'eq] with ω h using (h r).symm
  · filter_upwards [hB'eq] with ω h
    funext t; simp [drive, h]

/-- **E3 (i).** For `κ ∈ (0,4)`, `δ, t > 0`: `P(τ_{−δ} > t) ≤ δ²/((4−κ)t)`, where
`τ_{−δ} = realHitTime (√κ B) (−δ)`. -/
theorem prob_realHitTime_gt_le (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) :
    P {ω | ENNReal.ofReal t < realHitTime (drive κ B ω) (-δ)}
      ≤ ENNReal.ofReal (δ ^ 2 / ((4 - κ) * t)) := by
  obtain ⟨B', hB', hB'm, hB'c, hdr⟩ := exists_good_drive hB
  have heq : {ω | ENNReal.ofReal t < realHitTime (drive κ B ω) (-δ)} =ᵐ[P]
      {ω | ENNReal.ofReal t < realHitTime (drive κ B' ω) (-δ)} := by
    filter_upwards [hdr κ] with ω h
    simp only [h]
  rw [measure_congr heq]
  exact prob_realHitTime_gt_le_of_good hB' hB'm hB'c hκ hκ4 hδ ht

/-! ### 5. E3 (ii) -/

/-! ### 6. Measurability of the hitting time -/

/-- The tamed flow staying in `{Re ≤ −ε}` is a genuine real reverse solution. -/
theorem isRealRevSol_of_revZ (hW : Continuous W) {ε : ℝ} (hε : 0 < ε) {x q : ℝ} (hq : 0 ≤ q)
    (hreg : ∀ t ∈ Icc (0 : ℝ) q, ε ≤ -(revZ W ε x t).re) :
    IsRealRevSol W x q (fun t => (revZ W ε x t).re) := by
  refine ⟨Complex.continuous_re.comp_continuousOn (continuousOn_revZ hW hε hq x),
    fun t ht => ⟨?_, ?_⟩⟩
  · have := hreg t ht
    intro h0; simp only at h0; linarith
  · simp only
    rw [revZ_re_eq hW hε x ht.1]
    have hint : (∫ s in (0 : ℝ)..t, (revField ε (revZ W ε x s)).re)
        = -∫ s in (0 : ℝ)..t, 2 / (revZ W ε x s).re := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      simp only
      rw [revField_of_le (hreg s ⟨hs.1, hs.2.trans ht.2⟩)]
      simp [neg_div]
    rw [hint]; ring

theorem forall_Icc_of_forall_rat {g : ℝ → ℝ} {a q : ℝ} (hq : 0 ≤ q)
    (hg : ContinuousOn g (Icc 0 q)) (h : ∀ t : ℚ, (t : ℝ) ∈ Icc 0 q → a ≤ g t) :
    ∀ t ∈ Icc (0 : ℝ) q, a ≤ g t := by
  intro t ht
  by_contra hlt
  push Not at hlt
  rcases hq.eq_or_lt with rfl | hq0
  · have : t = 0 := le_antisymm ht.2 ht.1
    subst this
    exact absurd (h 0 (by simp)) (by simpa using hlt)
  have hev : ∀ᶠ s in 𝓝[Icc 0 q] t, g s < a :=
    (hg t ht).eventually (gt_mem_nhds hlt)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn
    (show max (t - δ / 2) 0 < min (t + δ / 2) q from
      max_lt (lt_min (by linarith) (by linarith [ht.2])) (lt_min (by linarith [ht.1]) hq0))
  have hrI : (r : ℝ) ∈ Icc 0 q :=
    ⟨(le_max_right _ _).trans hr1.le, hr2.le.trans (min_le_right _ _)⟩
  have hrd : dist (r : ℝ) t < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [le_max_left (t - δ / 2) 0, min_le_left (t + δ / 2) q]
  exact absurd (h r hrI) (not_le.2 (hball ⟨hrd, hrI⟩))

/-- For `x < W 0`, a real solution exists on `[0,q]` iff some tamed flow stays in
`{Re ≤ −1/(n+1)}` at all rational times of `[0,q]`. -/
theorem exists_isRealRevSol_iff (hW : Continuous W) {x q : ℝ} (hx : x < W 0) (hq : 0 ≤ q) :
    (∃ u, IsRealRevSol W x q u) ↔ ∃ n : ℕ, ∀ t : ℚ, (t : ℝ) ∈ Icc 0 q →
      (1 / ((n : ℝ) + 1)) ≤ -(revZ W (1 / ((n : ℝ) + 1)) x t).re := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨c, hc, K, hcK⟩ := exists_bounds_isRealRevSol hu hq hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hc
    refine ⟨n, fun t ht => ?_⟩
    have heq := revZ_eq_of_isRealRevSol hW (by positivity) hu
      (fun r hr => hn.le.trans (hcK r hr).1) t ht
    rw [heq, Complex.ofReal_re]
    exact hn.le.trans (hcK t ht).1
  · rintro ⟨n, hn⟩
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact ⟨_, isRealRevSol_of_revZ hW hε hq (forall_Icc_of_forall_rat hq
      (Complex.continuous_re.comp_continuousOn (continuousOn_revZ hW hε hq x)).neg hn)⟩

open Classical in
theorem realHitTime_eq_iSup_rat (W : ℝ → ℝ) (x : ℝ) :
    realHitTime W x = ⨆ q : ℚ,
      if 0 ≤ (q : ℝ) ∧ ∃ u, IsRealRevSol W x q u then ENNReal.ofReal q else 0 := by
  apply le_antisymm
  · show (⨆ (T : ℝ) (_ : 0 ≤ T) (_ : ∃ u, IsRealRevSol W x T u), ENNReal.ofReal T) ≤ _
    refine iSup_le fun T => iSup_le fun hT => iSup_le fun ⟨u, hu⟩ => ?_
    refine le_of_forall_lt fun r hr => ?_
    have hT0 : 0 < T := by
      by_contra h; push Not at h
      rw [ENNReal.ofReal_of_nonpos h] at hr; exact absurd hr (not_lt_bot)
    have hrt : r ≠ ⊤ := ne_top_of_lt hr
    have ha : r.toReal < T := by
      rw [← ENNReal.ofReal_toReal hrt] at hr
      exact (ENNReal.ofReal_lt_ofReal_iff hT0).1 hr
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt ha hT0 : max r.toReal 0 < T)
    have hq0 : (0 : ℝ) < q := (le_max_right _ _).trans_lt hq1
    refine lt_of_lt_of_le ?_ (le_iSup_of_le q (by
      rw [if_pos ⟨hq0.le, u, isRealRevSol_restrict hu hq2.le⟩]))
    rw [← ENNReal.ofReal_toReal hrt]
    exact (ENNReal.ofReal_lt_ofReal_iff hq0).2 ((le_max_left _ _).trans_lt hq1)
  · refine iSup_le fun q => ?_
    split_ifs with h
    · exact ofReal_le_realHitTime h.1 h.2.choose_spec
    · exact bot_le

theorem measurable_revZ_re_drive (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {ε : ℝ} (hε : 0 < ε) (x : ℝ) {t : ℝ}
    (ht : 0 ≤ t) : Measurable fun ω => (revZ (drive κ B ω) ε x t).re := by
  set U : ℝ≥0 → Ω → ℂ := fun t ω => revZ (drive κ B ω) ε (x : ℂ) t with hUdef
  have hU := fun ω (t : ℝ≥0) => revZ_integralEq hBc hε κ (x : ℂ) ω t
  have hUc : ∀ ω, Continuous (U · ω) := Dynkin.continuous_of_integralEq hBc
    (revField_lipschitz hε).continuous (norm_revField_le hε) hU
  have hm := Dynkin.measurable_of_integralEq (bmFilt hBm) (bmFilt_adapted hBm) hBc
    (revField_lipschitz hε) (norm_revField_le hε) hU hUc t.toNNReal
  have hm' : Measurable (U t.toNNReal) := hm.mono ((bmFilt hBm).le _) le_rfl
  have e : (fun ω => (revZ (drive κ B ω) ε x t).re) = fun ω => (U t.toNNReal ω).re := by
    funext ω; simp [hUdef, Real.coe_toNNReal t ht]
  rw [e]
  exact Complex.measurable_re.comp hm'

/-- **Measurability of `τ_x`** (`x < 0`), as an a.e.-measurable function. -/
theorem aemeasurable_realHitTime (hB : IsBrownianReal B P) (κ : ℝ) {x : ℝ} (hx : x < 0) :
    AEMeasurable (fun ω => realHitTime (drive κ B ω) x) P := by
  classical
  obtain ⟨B', hB', hB'm, hB'c, hdr⟩ := exists_good_drive hB
  set S : ℚ → Set Ω := fun q => {ω | 0 ≤ (q : ℝ) ∧ ∃ n : ℕ, ∀ t : ℚ, (t : ℝ) ∈ Icc 0 (q : ℝ) →
      (1 / ((n : ℝ) + 1)) ≤ -(revZ (drive κ B' ω) (1 / ((n : ℝ) + 1)) x t).re} with hS
  have hSm : ∀ q, MeasurableSet (S q) := by
    intro q
    by_cases hq : (0 : ℝ) ≤ q
    · have : S q = ⋃ n : ℕ, ⋂ t : ℚ, {ω | (t : ℝ) ∈ Icc 0 (q : ℝ) →
          (1 / ((n : ℝ) + 1)) ≤ -(revZ (drive κ B' ω) (1 / ((n : ℝ) + 1)) x t).re} := by
        have hq' : (0 : ℚ) ≤ q := by exact_mod_cast hq
        ext ω; simp [hS, hq']
      rw [this]
      refine MeasurableSet.iUnion fun n => MeasurableSet.iInter fun t => ?_
      by_cases ht : (t : ℝ) ∈ Icc 0 (q : ℝ)
      · simp only [ht, true_implies]
        exact measurableSet_le measurable_const
          (measurable_revZ_re_drive hB'm hB'c κ (by positivity) x ht.1).neg
      · simp [ht]
    · have hq' : ¬ (0 : ℚ) ≤ q := fun h => hq (by exact_mod_cast h)
      have : S q = ∅ := by ext ω; simp [hS, hq']
      rw [this]; exact MeasurableSet.empty
  set g : Ω → ℝ≥0∞ := fun ω => ⨆ q : ℚ, (S q).indicator (fun _ => ENNReal.ofReal q) ω with hg
  have hgm : Measurable g := Measurable.iSup fun q => measurable_const.indicator (hSm q)
  refine ⟨g, hgm, ?_⟩
  filter_upwards [hdr κ, hB'.eval_zero_ae_eq_zero] with ω h h0
  have hW : Continuous (drive κ B' ω) := continuous_drive_ns hB'c κ ω
  have hx0 : x < drive κ B' ω 0 := by rw [drive_zero_of h0]; exact hx
  rw [← h, realHitTime_eq_iSup_rat, hg]
  refine iSup_congr fun q => ?_
  by_cases hq : (0 : ℝ) ≤ q
  · have hiff := exists_isRealRevSol_iff hW hx0 hq
    by_cases hm : ω ∈ S q
    · rw [Set.indicator_of_mem hm, if_pos ⟨hq, hiff.2 hm.2⟩]
    · rw [Set.indicator_of_notMem hm, if_neg]
      rintro ⟨-, hex⟩; exact hm ⟨hq, hiff.1 hex⟩
  · rw [Set.indicator_of_notMem (fun hm => hq hm.1), if_neg (fun h => hq h.1)]

end Collision
end QuantumZipper
