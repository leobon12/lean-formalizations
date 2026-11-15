/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftAliveFun

/-!
# The lower strip gap as an adapted process; the stopped Lyapunov bound

Packet PROVE-ZHAN-A8. For a Brownian motion `B` with every path continuous and `B 0 = 0`, the tamed lower gap

  `X_t = q − √κ B_t + Λ_t`,  `Λ_t = ∫₀ᵗ (C(max(X_u, c)) − σ) du`,  `C = coth(·/2)`,

is realized for every `ω` by the adapted tamed flow `Sec2.markFlow` (`lgDrift`, `lgProc`); the state is `Λ` itself,
and the region is `U = {X > 0}` (`lgRegion`). With PROVE-ZHAN-B's localization (`AvoidMart.lean`: `locStop`, the
hitting time of the exit set `{dist(·, Uᶜ) ≤ 1/(n+1)} ∪ {‖·‖ ≥ n} ∪ {X ≥ R}` capped at `n`), the localized Itô
formula gives, for the Lyapunov function `lyap a` of `ConstDriftAliveFun.lean` (generator `≤ 0` on `{X ≥ c}`),

  `E lyap(X_σ) ≤ lyap(q)`  (`integral_lyap_locStop_le`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

namespace LowerGap

open Sec4 (cothHalf)

/-! ### The observable of the state `(Λ, b)` -/

section Obs

variable {κ q : ℝ}

/-- The lower gap read from the state `(Λ, b)`: `X = q − √κ b + Λ`. -/
def lgCoord (κ q : ℝ) (p : ℝ × ℝ) : ℝ := q - Real.sqrt κ * p.2 + p.1

/-- The region `X > 0`. -/
def lgRegion (κ q : ℝ) : Set (ℝ × ℝ) := {p | 0 < lgCoord κ q p}

theorem continuous_lgCoord : Continuous (lgCoord κ q) := by
  unfold lgCoord; fun_prop

theorem contDiff_lgCoord {n : WithTop ℕ∞} : ContDiff ℝ n (lgCoord κ q) := by
  unfold lgCoord
  exact (contDiff_const.sub (contDiff_const.mul contDiff_snd)).add contDiff_fst

theorem isOpen_lgRegion : IsOpen (lgRegion κ q) := isOpen_lt continuous_const continuous_lgCoord

@[simp] theorem lgCoord_zero : lgCoord κ q (0, 0) = q := by simp [lgCoord]

theorem partialSnd_lgCoord (p : ℝ × ℝ) : Ito.partialSnd (lgCoord κ q) p = -Real.sqrt κ := by
  refine Ito.partialSnd_eq_of_hasDerivAt ((contDiff_lgCoord (n := 1)).differentiable one_ne_zero p) ?_
  have h := (((hasDerivAt_id p.2).const_mul (Real.sqrt κ)).const_sub q).add_const p.1
  simpa [lgCoord] using h

theorem itoGen_lgCoord (p : ℝ × ℝ) (v : ℝ) : Ito.itoGen (lgCoord κ q) p v = v := by
  have hfst : Ito.partialFst (lgCoord κ q) p v = v := by
    refine Ito.partialFst_eq_of_hasDerivAt ((contDiff_lgCoord (n := 1)).differentiable one_ne_zero p) ?_
    have h0 := ((hasDerivAt_id (0 : ℝ)).mul_const v).const_add (q - Real.sqrt κ * p.2 + p.1)
    simp only [id, one_mul] at h0
    refine h0.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [lgCoord, smul_eq_mul]
    ring
  have hss : Ito.partialSndSnd (lgCoord κ q) p = 0 :=
    Ito.partialSndSnd_eq_of_hasDerivAt (contDiff_lgCoord.contDiffAt) (g := fun _ => -Real.sqrt κ)
      (Eventually.of_forall fun y => partialSnd_lgCoord (p.1, y)) (hasDerivAt_const _ _)
  rw [Ito.itoGen, hfst, hss]
  ring

/-- **The generator of `lyap a ∘ X`** at a point of the region: `lyapD(X) v + (κ/2) lyapDD(X)`. -/
theorem itoGen_lyap (hκ : 0 ≤ κ) (a : ℝ) {p : ℝ × ℝ} (hp : p ∈ lgRegion κ q) (v : ℝ) :
    Ito.itoGen (fun r => lyap a (lgCoord κ q r)) p v =
      lyapD a (lgCoord κ q p) * v + κ / 2 * lyapDD (lgCoord κ q p) := by
  have hp0 : 0 < lgCoord κ q p := hp
  have h1 : ∀ᶠ x in 𝓝 (lgCoord κ q p), HasDerivAt (lyap a) (lyapD a x) x := by
    filter_upwards [isOpen_Ioi.mem_nhds hp0] with x hx using hasDerivAt_lyap a hx
  rw [itoGen_comp_of_hasDerivAt (contDiffAt_lyap a hp0) contDiff_lgCoord.contDiffAt h1
    (hasDerivAt_lyapD a hp0.ne'), itoGen_lgCoord, partialSnd_lgCoord, neg_sq, Real.sq_sqrt hκ]
  ring

theorem contDiffOn_lyap_lgCoord (a : ℝ) :
    ContDiffOn ℝ 3 (fun r => lyap a (lgCoord κ q r)) (lgRegion κ q) :=
  ((contDiffOn_lyap a).of_le (WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) ≤ ⊤))).comp
    contDiff_lgCoord.contDiffOn fun _ hp => hp

/-! #### Distance to the complement of the region -/

theorem infDist_le_lgCoord {p : ℝ × ℝ} (hp : p ∈ lgRegion κ q) :
    Metric.infDist p (lgRegion κ q)ᶜ ≤ lgCoord κ q p := by
  have hp0 : 0 < lgCoord κ q p := hp
  have hmem : (p.1 - lgCoord κ q p, p.2) ∈ (lgRegion κ q)ᶜ := by
    simp only [lgRegion, mem_compl_iff, mem_ofPred_eq, not_lt]
    simp only [lgCoord]; linarith
  refine (Metric.infDist_le_dist_of_mem hmem).trans (le_of_eq ?_)
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
    show p.1 - (p.1 - lgCoord κ q p) = lgCoord κ q p by ring, abs_of_pos hp0]
  exact max_eq_left hp0.le

theorem compl_lgRegion_nonempty : (lgRegion κ q)ᶜ.Nonempty :=
  ⟨(-q, 0), by simp [lgRegion, lgCoord]⟩

theorem lgCoord_le_infDist (p : ℝ × ℝ) :
    lgCoord κ q p ≤ (1 + Real.sqrt κ) * Metric.infDist p (lgRegion κ q)ᶜ := by
  have hs : 0 < 1 + Real.sqrt κ := by positivity
  rw [← div_le_iff₀' hs]
  refine (Metric.le_infDist compl_lgRegion_nonempty).2 fun p' hp' => ?_
  simp only [lgRegion, mem_compl_iff, mem_ofPred_eq, not_lt] at hp'
  rw [div_le_iff₀' hs, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  have h1 := le_max_left |p.1 - p'.1| |p.2 - p'.2|
  have h2 := le_max_right |p.1 - p'.1| |p.2 - p'.2|
  have h3 := le_abs_self (p.1 - p'.1)
  have h4 := neg_abs_le (p.2 - p'.2)
  have hk := Real.sqrt_nonneg κ
  have e : lgCoord κ q p = lgCoord κ q p' + (p.1 - p'.1) - Real.sqrt κ * (p.2 - p'.2) := by
    simp only [lgCoord]; ring
  rw [e]
  nlinarith

end Obs

/-! ### The tamed field and the adapted lower gap -/

section Process

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {κ σ q c : ℝ} {B : ℝ≥0 → Ω → ℝ}

/-- The tamed field `Ψ(Λ, b) = C(max(X, c)) − σ`. -/
def lgField (κ σ q c : ℝ) (p : ℝ × ℝ) : ℝ := tame c (lgCoord κ q p) - σ

theorem continuous_lgField (hc : 0 < c) : Continuous (lgField κ σ q c) :=
  ((lipschitzWith_tame hc).continuous.comp continuous_lgCoord).sub continuous_const

theorem lgField_of_le {p : ℝ × ℝ} (h : c ≤ lgCoord κ q p) :
    lgField κ σ q c p = cothHalf (lgCoord κ q p) - σ := by
  rw [lgField, tame_of_le h]

/-- The drift integral `Λ_t = ∫₀ᵗ (C(max(X, c)) − σ)` of the tamed lower gap `X = q − √κ B + Λ` (the adapted flow
`Sec2.markFlow`). -/
def lgDrift (κ σ q c : ℝ) (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  Sec2.markFlow (fun x => tame c x - σ) 0 (fun _ => ⊤) (fun t ω => Real.sqrt κ * B t ω - q)

/-- The tamed lower gap `X_t = q − √κ B_t + Λ_t`. -/
def lgProc (κ σ q c : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  q - Real.sqrt κ * B t ω + lgDrift κ σ q c B t ω

theorem abs_tame_sub_le (hc : 0 < c) (σ x : ℝ) : |tame c x - σ| ≤ cothHalf c + |σ| :=
  (abs_sub _ _).trans (add_le_add (abs_tame_le hc x) le_rfl)

theorem lgDrift_facts (hc : 0 < c) {ω : Ω} (hBc : Continuous (B · ω)) :
    Continuous (fun t => lgDrift κ σ q c B t ω) ∧
      ∀ t : ℝ≥0, lgDrift κ σ q c B t ω =
        ∫ s in (0 : ℝ)..t, (tame c (lgProc κ σ q c B s.toNNReal ω) - σ) := by
  have hW : ContinuousOn (fun s => Real.sqrt κ * B s ω - q) {s : ℝ≥0 | (s : ℝ≥0∞) < ⊤} :=
    ((continuous_const.mul hBc).sub continuous_const).continuousOn
  obtain ⟨hcont, heq⟩ := Sec2.markFlow_eq_of_continuousOn (y := 0) (ζ := fun _ : Ω => (⊤ : ℝ≥0∞))
    (W := fun t ω => Real.sqrt κ * B t ω - q) ((lipschitzWith_tame hc).sub (LipschitzWith.const σ))
    (abs_tame_sub_le hc σ) hW
  refine ⟨?_, fun t => ?_⟩
  · rw [← continuousOn_univ]
    exact hcont.mono fun s _ => ENNReal.coe_lt_top
  · have h := heq t ENNReal.coe_lt_top
    rw [zero_add] at h
    change Sec2.markFlow _ _ _ _ t ω = _
    rw [h]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [lgProc, lgDrift]
    congr 2
    ring

theorem lgDrift_zero (ω : Ω) : lgDrift κ σ q c B 0 ω = 0 := Sec2.markFlow_zero _ _ _ _ ω

theorem continuous_lgProc (hc : 0 < c) {ω : Ω} (hBc : Continuous (B · ω)) :
    Continuous fun t => lgProc κ σ q c B t ω :=
  (continuous_const.sub (continuous_const.mul hBc)).add (lgDrift_facts hc hBc).1

/-- Each `lgDrift … t` is `𝓖_t`-measurable. -/
theorem measurable_lgDrift (hc : 0 < c) {𝓖 : Filtration ℝ≥0 mΩ} (hB : ∀ t, Measurable[𝓖 t] (B t))
    (t : ℝ≥0) : Measurable[𝓖 t] (lgDrift κ σ q c B t) := by
  refine Sec2.measurable_markFlow
    (((lipschitzWith_tame hc).continuous.sub continuous_const).measurable) (fun s A hA => ?_) t
  have h : {ω | ((s : ℝ≥0∞) < (⊤ : ℝ≥0∞)) ∧ Real.sqrt κ * B s ω - q ∈ A} =
      (fun ω => Real.sqrt κ * B s ω - q) ⁻¹' A := by
    ext ω; simp
  rw [h]
  exact (((hB s).const_mul _).sub_const q) hA

theorem lgCoord_pathX (t : ℝ≥0) (ω : Ω) :
    lgCoord κ q (Zhan.pathX (lgDrift κ σ q c B) B t ω) = lgProc κ σ q c B t ω := by
  simp only [lgCoord, Zhan.pathX, lgProc]

/-- **The state equation** `Λ_t = 0 + ∫₀ᵗ Ψ(Λ_s, B_s) ds`. -/
theorem lgDrift_eq_integral (hc : 0 < c) {ω : Ω} (hBc : Continuous (B · ω)) (t : ℝ≥0) :
    lgDrift κ σ q c B t ω =
      0 + ∫ s in (0 : ℝ)..t, lgField κ σ q c (Zhan.pathX (lgDrift κ σ q c B) B s.toNNReal ω) := by
  rw [zero_add, (lgDrift_facts hc hBc).2 t]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [lgField, lgCoord_pathX]

end Process


/-! ### The stopped Lyapunov bound -/

section Stopped

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {κ σ q c R a : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {n : ℕ}

/-- The localizing time of the tamed lower gap at level `(n, R)` (PROVE-ZHAN-B's `locStop`: the hitting time of
`{dist(·, Uᶜ) ≤ 1/(n+1)} ∪ {‖·‖ ≥ n} ∪ {X ≥ R}`, capped at `n`). -/
def lgStop (κ σ q c R : ℝ) (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  locStop univ (lgDrift κ σ q c B) B (lgRegion κ q) (lgCoord κ q) R n ω

/-- The lower gap at the localizing time. -/
def lgStopped (κ σ q c R : ℝ) (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  lgCoord κ q (pathX (lgDrift κ σ q c B) B (lgStop κ σ q c R B n ω) ω)

theorem lgCoord_ge_of_mem_keepSet {p : ℝ × ℝ} (hp : p ∈ keepSet (lgRegion κ q) (lgCoord κ q) R n) :
    1 / ((n : ℝ) + 1) ≤ lgCoord κ q p ∧ lgCoord κ q p ≤ R :=
  ⟨hp.1.trans (infDist_le_lgCoord (keepSet_subset hp)), hp.2.2⟩

variable [IsProbabilityMeasure P]

/-- **The stopped Lyapunov bound** `E lyap(X_σ) ≤ lyap(q)` (localized Itô formula for `lyap a ∘ X`, whose generator
is `≤ 0` on the keep set, where `X ≥ 1/(n+1) ≥ c` and the tamed field is the true one). -/
theorem integral_lyap_lgStopped_le (hB : IsFilteredBrownianReal 𝓖 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 4) (hσ : σ ≤ 1) (ha : 0 ≤ a)
    (ha' : κ / 2 - 1 + σ ≤ 2 * a) (hc : 0 < c) (hcn : c ≤ 1 / ((n : ℝ) + 1))
    (hX0 : ((0 : ℝ), (0 : ℝ)) ∉ exitSet (lgRegion κ q) (lgCoord κ q) R n) :
    Integrable (fun ω => lyap a (lgStopped κ σ q c R B n ω)) P ∧
      ∫ ω, lyap a (lgStopped κ σ q c R B n ω) ∂P ≤ lyap a q := by
  set Λ := lgDrift κ σ q c B with hΛdef
  set U := lgRegion κ q with hUdef
  set Φ := lgCoord κ q with hΦdef
  set F : ℝ × ℝ → ℝ := fun r => lyap a (lgCoord κ q r) with hFdef
  have hU : IsOpen U := isOpen_lgRegion
  have hΦc : ContinuousOn Φ U := continuous_lgCoord.continuousOn
  have hΨ : ContinuousOn (lgField κ σ q c) U := (continuous_lgField hc).continuousOn
  have hΛm : ∀ t, Measurable[𝓖 t] (Λ t) := measurable_lgDrift hc hB.2.1
  have hΛc : ∀ ω, Continuous (Λ · ω) := fun ω => (lgDrift_facts hc (hBc ω)).1
  have hG : MeasurableSet[𝓖 0] (univ : Set Ω) := MeasurableSet.univ
  have hΛ0 : ∀ ω, Λ 0 ω = 0 := lgDrift_zero
  have hpath : ∀ ω ∈ (univ : Set Ω), ∀ t : ℝ≥0,
      Λ t ω = 0 + ∫ s in (0 : ℝ)..t, lgField κ σ q c (pathX Λ B s.toNNReal ω) :=
    fun ω _ t => lgDrift_eq_integral hc (hBc ω) t
  have hF : ContDiffOn ℝ 3 F U := contDiffOn_lyap_lgCoord a
  have hM := martingale_loc hB hBc hU hΦc hΨ hΛm hΛc hG hΛ0 hB0 hpath hX0 hF
  have hsi := hM.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ (n : ℝ≥0)) MeasurableSet.univ
  simp only [setIntegral_univ] at hsi
  set σ' := locStop univ Λ B U Φ R n with hσdef
  have h0 : ∀ ω, F (pathX Λ B (min 0 (σ' ω)) ω) -
      ∫ s in (0 : ℝ)..((min 0 (σ' ω) : ℝ≥0) : ℝ), Ito.itoGen F (pathX Λ B s.toNNReal ω)
        (locDens univ Λ B (lgField κ σ q c) s ω) = F (0, 0) := fun ω => by
    simp [pathX, hΛ0, hB0]
  simp only [h0] at hsi
  rw [integral_const] at hsi
  simp only [probReal_univ, one_smul] at hsi
  have hmin : ∀ ω, min (n : ℝ≥0) (σ' ω) = σ' ω := fun ω => min_eq_right (locStop_le ω)
  simp only [hmin] at hsi
  have hkeep : ∀ ω, ∀ t ≤ σ' ω, pathX Λ B t ω ∈ keepSet U Φ R n := fun ω t ht =>
    pathX_mem_keepSet hBc hΦc hΛc hΛ0 hB0 hX0 ht
  have hin : ∀ ω, pathX Λ B (σ' ω) ω ∈ U := fun ω => keepSet_subset (hkeep ω _ le_rfl)
  have hFc : ContinuousOn F U := hF.continuousOn
  have hmeas := measurable_comp_pathX_locStop hB hBc hU hΦc hΛm hΛc hG hFc hin
  obtain ⟨C, hC⟩ := (isCompact_keepSet (U := U) (L := R) (n := n) hΦc).exists_bound_of_continuousOn
    (hFc.mono keepSet_subset)
  have hint1 : Integrable (fun ω => F (pathX Λ B (σ' ω) ω)) P :=
    Integrable.of_bound hmeas.aestronglyMeasurable C (Eventually.of_forall fun ω => hC _ (hkeep ω _ le_rfl))
  have hintM := hM.integrable (n : ℝ≥0)
  simp only [hmin] at hintM
  have hI : ∀ ω, ∫ s in (0 : ℝ)..((σ' ω : ℝ≥0) : ℝ),
      Ito.itoGen F (pathX Λ B s.toNNReal ω) (locDens univ Λ B (lgField κ σ q c) s ω) ≤ 0 := by
    intro ω
    have hnn := intervalIntegral.integral_nonneg (μ := volume) (σ' ω).coe_nonneg
      (f := fun s => -Ito.itoGen F (pathX Λ B s.toNNReal ω) (locDens univ Λ B (lgField κ σ q c) s ω))
      fun s hs => by
        have hk := hkeep ω s.toNNReal (Real.toNNReal_le_iff_le_coe.2 hs.2)
        obtain ⟨hX1, -⟩ := lgCoord_ge_of_mem_keepSet hk
        have hXc : c ≤ lgCoord κ q (pathX Λ B s.toNNReal ω) := hcn.trans hX1
        have hX0' : 0 < lgCoord κ q (pathX Λ B s.toNNReal ω) := hc.trans_le hXc
        simp only [locDens, mem_univ, ↓reduceIte]
        rw [itoGen_lyap hκ0 a (keepSet_subset hk), lgField_of_le hXc]
        linarith [lyap_gen_nonpos hκ hσ ha ha' hX0']
    rw [intervalIntegral.integral_neg] at hnn
    linarith
  have hIeq : (fun ω => ∫ s in (0 : ℝ)..((σ' ω : ℝ≥0) : ℝ),
      Ito.itoGen F (pathX Λ B s.toNNReal ω) (locDens univ Λ B (lgField κ σ q c) s ω)) = fun ω =>
        F (pathX Λ B (σ' ω) ω) - (F (pathX Λ B (σ' ω) ω) - ∫ s in (0 : ℝ)..((σ' ω : ℝ≥0) : ℝ),
          Ito.itoGen F (pathX Λ B s.toNNReal ω) (locDens univ Λ B (lgField κ σ q c) s ω)) := by
    funext ω; ring
  have hInt := integral_nonpos_of_ae (μ := P) (Eventually.of_forall hI)
  rw [hIeq, integral_sub hint1 hintM, ← hsi] at hInt
  have hF0 : F (0, 0) = lyap a q := by simp [hFdef]
  refine ⟨hint1, ?_⟩
  change ∫ ω, F (pathX Λ B (σ' ω) ω) ∂P ≤ lyap a q
  linarith

end Stopped

end LowerGap

end Zhan

end InteractingSLE
