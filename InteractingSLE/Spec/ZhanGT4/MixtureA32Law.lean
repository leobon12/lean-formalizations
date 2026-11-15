/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MixtureA32Mart

/-!
# A.3.2, (G3) in the strip, part 1: the finite-horizon mixture and the forced driver functional

Packet PROVE-ZHAN-A32. Source: Astra, *Follow-up proofs and dependency audit*, §A.3.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L686–L697, ruling R38): "Consequently the original strip law is
the mixture, with density `f(u) du`, of these forced laws, first on each finite-time sigma-algebra and then on the
full path sigma-algebra by a monotone class."

## Main results

* **`measure_eq_lintegral_mixMeasure`** (the mixture on a finite horizon): for every measurable event `A` and horizon
  `T`, `P(A) = ∫ f(u) Q_u^T(A) du` (Tonelli with `∫ M_T(u) du = 1`);
* `forcedDrv κ σ U β`: **the forced strip driver** built from a path `β` and a starting point `U`,
  `ξ̂_t = √κ β_t − σ t + 2 ∫₀ᵗ tanh(Y_s/2) ds` with `Y = U − √κ β + σ t − ∫₀^· tanh(Y/2)` (its upper point; `forcedY`,
  `forcedY_eq`, `forcedDrv_eq`) — measurable in `(U, β)` by construction (the tamed Euler flow `Sec2.markFlow`);
* **`forcedDrv_mixBM_eq`**: under the tilted measure the strip driver is the forced driver of `B̂`:
  `ξ_t = ξ̂_t(u, B̂)` for `t ≤ T`, path by path;
* `map_pathOf_eq_of_isPreBrownianReal`: two Brownian motions have the same law on the path space `ℝ≥0 → ℝ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.Mix

variable {κ σ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ### Joint measurability of `M_t(u)` -/

theorem continuous_mixMart_initial {ω : Ω} (hc : Continuous (B · ω)) (t : ℝ≥0) :
    Continuous fun u => mixMart κ σ B u t ω :=
  (continuous_mixDensity.comp (continuous_upFlow_initial (continuous_stripDrv hc) t.coe_nonneg)).mul
    (continuous_upDeriv_initial (continuous_stripDrv hc) t.coe_nonneg)

theorem measurable_mixMart {𝓕 : Filtration ℝ≥0 mΩ} (hBm : ∀ t, Measurable[𝓕 t] (B t))
    (hBc : ∀ ω, Continuous (B · ω)) (u : ℝ) (t : ℝ≥0) : Measurable[𝓕 t] (mixMart κ σ B u t) := by
  have e : mixMart κ σ B u t =
      fun ω => mixDensity κ σ (upFlow (stripDrv κ σ B ω) u t) * Real.exp (gamX κ σ B u ω t) := by
    funext ω; rw [mixMart, exp_gamX u t.coe_nonneg]
  rw [e]
  exact (continuous_mixDensity.measurable.comp (measurable_upFlow_stripDrv hBm hBc u t)).mul
    (Real.continuous_exp.measurable.comp (measurable_gamX hBm hBc u t))

theorem measurable_mixMart_uncurry {𝓕 : Filtration ℝ≥0 mΩ} (hBm : ∀ t, Measurable[𝓕 t] (B t))
    (hBc : ∀ ω, Continuous (B · ω)) (t : ℝ≥0) :
    Measurable fun p : ℝ × Ω => mixMart κ σ B p.1 t p.2 :=
  measurable_uncurry_of_continuous_of_measurable (u := fun u ω => mixMart κ σ B u t ω)
    (fun ω => continuous_mixMart_initial (hBc ω) t)
    (fun u => (measurable_mixMart hBm hBc u t).mono (𝓕.le t) le_rfl)

/-! ### The finite-horizon mixture -/

/-- **(G3), finite horizon**: `P(A) = ∫ f(u) Q_u^T(A) du` for every measurable `A`. -/
theorem measure_eq_lintegral_mixMeasure {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} [SFinite P] (hκ : 0 < κ)
    (hσ : |σ| < 1) (hBm : ∀ t, Measurable[𝓕 t] (B t)) (hBc : ∀ ω, Continuous (B · ω)) (T : ℝ≥0) {A : Set Ω}
    (hA : MeasurableSet A) :
    P A = ∫⁻ u, ENNReal.ofReal (mixDensity κ σ u) * mixMeasure P κ σ B u T A := by
  have hj := measurable_mixMart_uncurry (κ := κ) (σ := σ) hBm hBc T
  calc P A = ∫⁻ _ in A, 1 ∂P := (setLIntegral_one A).symm
    _ = ∫⁻ ω in A, (∫⁻ u, ENNReal.ofReal (mixMart κ σ B u T ω)) ∂P :=
        setLIntegral_congr_fun hA fun ω _ => (lintegral_mixMart hκ hσ (hBc ω) T).symm
    _ = ∫⁻ u, (∫⁻ ω in A, ENNReal.ofReal (mixMart κ σ B u T ω) ∂P) :=
        lintegral_lintegral_swap (f := fun ω u => ENNReal.ofReal (mixMart κ σ B u T ω))
          (ENNReal.measurable_ofReal.comp (hj.comp measurable_swap)).aemeasurable
    _ = ∫⁻ u, ENNReal.ofReal (mixDensity κ σ u) * mixMeasure P κ σ B u T A := by
        refine lintegral_congr fun u => ?_
        rw [mixMeasure, withDensity_apply _ hA, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun hA fun ω _ => ?_
        rw [← ENNReal.ofReal_mul (mixDensity_pos hκ hσ u).le, mul_div_cancel₀ _ (mixDensity_pos hκ hσ u).ne']

/-! ### The forced driver functional -/

/-- The forced flow `Λ̂ = ∫₀^· −tanh(Y/2)` (the tamed Euler flow `Sec2.markFlow` driven by `√κ β − σ t − U`). -/
def forcedLam (κ σ : ℝ) (U : Ω → ℝ) (β : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  Sec2.markFlow (fun z => -Real.tanh (z / 2)) 0 (fun _ => ⊤) (fun s ω => Real.sqrt κ * β s ω - σ * s - U ω)

/-- **The forced upper point** `Y_t = U − √κ β_t + σ t + Λ̂_t`. -/
def forcedY (κ σ : ℝ) (U : Ω → ℝ) (β : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  U ω - Real.sqrt κ * β t ω + σ * t + forcedLam κ σ U β t ω

/-- **The forced strip driver** `ξ̂_t = √κ β_t − σ t − 2 Λ̂_t = √κ β_t − σ t + 2 ∫₀ᵗ tanh(Y_s/2) ds`: strip SLE with
charge `−4` at the upper point started at `U + iπ`, charge `2` at the right end and `κ − 4` at the left end. -/
def forcedDrv (κ σ : ℝ) (U : Ω → ℝ) (β : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.sqrt κ * β t ω - σ * t - 2 * forcedLam κ σ U β t ω

theorem lipschitzWith_neg_tanh_half : LipschitzWith (1 / 2 : ℝ≥0) fun z : ℝ => -Real.tanh (z / 2) :=
  Zhan.lipschitzWith_tanh_half.neg

theorem forcedLam_facts {U : Ω → ℝ} {β : ℝ≥0 → Ω → ℝ} {ω : Ω} (hβ : Continuous (β · ω)) :
    Continuous (fun t => forcedLam κ σ U β t ω) ∧ ∀ t : ℝ≥0, forcedLam κ σ U β t ω =
      ∫ s in (0 : ℝ)..t, -Real.tanh (forcedY κ σ U β s.toNNReal ω / 2) := by
  have hW : ContinuousOn (fun s => Real.sqrt κ * β s ω - σ * s - U ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ⊤} :=
    (((continuous_const.mul hβ).sub (continuous_const.mul NNReal.continuous_coe)).sub
      continuous_const).continuousOn
  obtain ⟨hc, heq⟩ := Sec2.markFlow_eq_of_continuousOn (y := 0) (ζ := fun _ : Ω => (⊤ : ℝ≥0∞))
    (W := fun s ω => Real.sqrt κ * β s ω - σ * s - U ω) lipschitzWith_neg_tanh_half
    (fun x => by rw [abs_neg]; exact (Real.abs_tanh_lt_one _).le) hW
  refine ⟨?_, fun t => ?_⟩
  · rw [← continuousOn_univ]; exact hc.mono fun s _ => ENNReal.coe_lt_top
  · have h := heq t ENNReal.coe_lt_top
    rw [zero_add] at h
    change Sec2.markFlow _ _ _ _ t ω = _
    rw [h]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [forcedY, forcedLam]
    congr 2
    ring

theorem forcedY_eq {U : Ω → ℝ} {β : ℝ≥0 → Ω → ℝ} {ω : Ω} (hβ : Continuous (β · ω)) (t : ℝ≥0) :
    forcedY κ σ U β t ω = U ω - Real.sqrt κ * β t ω + σ * t +
      ∫ s in (0 : ℝ)..t, -Real.tanh (forcedY κ σ U β s.toNNReal ω / 2) := by
  rw [forcedY, (forcedLam_facts hβ).2 t]

theorem forcedDrv_eq {U : Ω → ℝ} {β : ℝ≥0 → Ω → ℝ} {ω : Ω} (hβ : Continuous (β · ω)) (t : ℝ≥0) :
    forcedDrv κ σ U β t ω = Real.sqrt κ * β t ω - σ * t +
      2 * ∫ s in (0 : ℝ)..t, Real.tanh (forcedY κ σ U β s.toNNReal ω / 2) := by
  rw [forcedDrv, (forcedLam_facts hβ).2 t, intervalIntegral.integral_neg]
  ring

theorem continuous_forcedY {U : Ω → ℝ} {β : ℝ≥0 → Ω → ℝ} {ω : Ω} (hβ : Continuous (β · ω)) :
    Continuous fun t => forcedY κ σ U β t ω :=
  (((continuous_const.sub (continuous_const.mul hβ)).add (continuous_const.mul NNReal.continuous_coe)).add
    (forcedLam_facts hβ).1)

/-- `forcedDrv` is measurable in `(U, β)` (for each time): the tamed flow is measurable for the constant filtration. -/
theorem measurable_forcedDrv {U : Ω → ℝ} {β : ℝ≥0 → Ω → ℝ} (hU : Measurable U) (hβ : ∀ t, Measurable (β t))
    (t : ℝ≥0) : Measurable (forcedDrv κ σ U β t) := by
  have hL : Measurable (forcedLam κ σ U β t) := by
    have h := Sec2.measurable_markFlow (𝓕 := (⊤ : Filtration ℝ≥0 mΩ)) (F := fun z => -Real.tanh (z / 2)) (y := 0)
      (ζ := fun _ => ⊤) (W := fun s ω => Real.sqrt κ * β s ω - σ * s - U ω)
      lipschitzWith_neg_tanh_half.continuous.measurable (fun s A hA => ?_) t
    · exact h
    · have e : {ω | ((s : ℝ≥0∞) < (⊤ : ℝ≥0∞)) ∧ Real.sqrt κ * β s ω - σ * s - U ω ∈ A} =
          (fun ω => Real.sqrt κ * β s ω - σ * s - U ω) ⁻¹' A := by
        ext ω; simp
      rw [e]
      exact ((((hβ s).const_mul _).sub_const _).sub hU) hA
  exact (((hβ t).const_mul _).sub_const _).sub (hL.const_mul _)

/-! ### Under the tilted measure the strip driver is the forced driver of `B̂` -/

theorem continuous_mixBM {ω : Ω} (hc : Continuous (B · ω)) (u : ℝ) (T : ℝ≥0) :
    Continuous fun t => mixBM κ σ B u T t ω := by
  have hξ := continuous_stripDrv (κ := κ) (σ := σ) hc
  set g : ℝ → ℝ := fun s => 2 / Real.sqrt κ * (σ - Real.tanh (upFlow (stripDrv κ σ B ω) u (max s 0) / 2))
  have hg : Continuous g := continuous_const.mul (continuous_const.sub
    (continuous_tanh_half.comp (continuous_upFlow_max hξ u)))
  have hprim : Continuous fun c : ℝ => ∫ s in (0 : ℝ)..c, g s :=
    continuous_iff_continuousAt.2 fun c => (hg.integral_hasStrictDerivAt 0 c).hasDerivAt.continuousAt
  have e : (fun t => mixBM κ σ B u T t ω) =
      fun t => B t ω + ∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), g s := by
    funext t
    rw [mixBM]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (min t T).coe_nonneg] at hs
    simp only [g, mixTheta, max_eq_left hs.1]
  rw [e]
  exact hc.add (hprim.comp (NNReal.continuous_coe.comp (continuous_id.min continuous_const)))

/-- **Path by path, the strip driver up to `T` is the forced driver of `B̂`** (the solution of the forced equation is
unique, so the forced upper point is `X_t(u)`). -/
theorem forcedDrv_mixBM_eq (hκ : 0 < κ) {ω : Ω} (hc : Continuous (B · ω)) (u : ℝ) {T t : ℝ≥0} (ht : t ≤ T) :
    forcedDrv κ σ (fun _ => u) (mixBM κ σ B u T) t ω = stripDrv κ σ B ω t := by
  have hξ := continuous_stripDrv (κ := κ) (σ := σ) hc
  have hβ := continuous_mixBM (κ := κ) (σ := σ) hc u T
  set w : ℝ → ℝ := fun s => -(Real.sqrt κ * mixBM κ σ B u T s.toNNReal ω) + σ * s with hw
  have hwc : Continuous w :=
    ((continuous_const.mul (hβ.comp continuous_real_toNNReal)).neg).add (continuous_const.mul continuous_id)
  have hLD : OneForce.LipData (fun z => -Real.tanh (z / 2)) w :=
    ⟨⟨_, lipschitzWith_neg_tanh_half⟩, ⟨1, fun x => by rw [abs_neg]; exact (Real.abs_tanh_lt_one _).le⟩, hwc⟩
  have hT : (0 : ℝ) ≤ T := T.coe_nonneg
  -- the upper point `X` solves the forced equation on `[0, T]`
  have hX : ∀ s ∈ Icc (0 : ℝ) T, upFlow (stripDrv κ σ B ω) u s =
      u + w s + ∫ r in (0 : ℝ)..s, -Real.tanh (upFlow (stripDrv κ σ B ω) u r / 2) := fun s hs => by
    have h1 := upFlow_eq hξ u hs.1
    have h2 := stripDrv_eq_forced (σ := σ) hκ hc u (T := T) (t := s.toNNReal)
      (by rw [Real.toNNReal_le_iff_le_coe]; exact hs.2)
    rw [Real.coe_toNNReal _ hs.1] at h2
    rw [intervalIntegral.integral_neg]
    simp only [hw]
    rw [h1, h2]
    ring
  -- the forced upper point solves it too
  set Y : ℝ → ℝ := fun s => forcedY κ σ (fun _ => u) (mixBM κ σ B u T) s.toNNReal ω with hY
  have hYc : Continuous Y :=
    (continuous_forcedY (κ := κ) (σ := σ) (U := fun _ => u) hβ).comp continuous_real_toNNReal
  have hYeq : ∀ s ∈ Icc (0 : ℝ) T, Y s = u + w s + ∫ r in (0 : ℝ)..s, -Real.tanh (Y r / 2) := fun s hs => by
    simp only [hY, hw]
    rw [forcedY_eq hβ s.toNNReal, Real.coe_toNNReal _ hs.1]
    ring
  have e1 := OneForce.eqOn_lipSol hLD hT ((continuousOn_upFlow hξ u).mono Icc_subset_Ici_self) hX
  have e2 := OneForce.eqOn_lipSol hLD hT hYc.continuousOn hYeq
  have hYX : ∀ s ∈ Icc (0 : ℝ) T, Y s = upFlow (stripDrv κ σ B ω) u s := fun s hs => by
    rw [← e1 hs, e2 hs]
  -- conclude
  have htT : (t : ℝ) ≤ T := NNReal.coe_le_coe.2 ht
  rw [forcedDrv_eq hβ t, stripDrv_eq_forced (σ := σ) hκ hc u ht]
  congr 2
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le t.coe_nonneg] at hs
  have := hYX s ⟨hs.1, hs.2.trans htT⟩
  simp only [hY] at this
  rw [this]

/-! ### The law of a Brownian path -/

/-- The path of a process, as a point of `ℝ≥0 → ℝ`. -/
def pathOf (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 → ℝ := fun t => X t ω

theorem measurable_pathOf {X : ℝ≥0 → Ω → ℝ} (hX : ∀ t, Measurable (X t)) : Measurable (pathOf X) :=
  measurable_pi_iff.2 hX

theorem isProjectiveLimit_map_pathOf {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} (hX : IsPreBrownianReal X P)
    (hXm : ∀ t, Measurable (X t)) : IsProjectiveLimit (P.map (pathOf X)) BrownianReal.projectiveFamily := fun I => by
  rw [Measure.map_map (Finset.measurable_restrict I) (measurable_pathOf hXm)]
  exact (hX.hasLaw I).map_eq

/-- **Two Brownian motions have the same law on the path space** (both are projective limits of the Brownian
finite-dimensional laws). -/
theorem map_pathOf_eq_of_isPreBrownianReal {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
    {Q : Measure Ω'} {X : ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω' → ℝ} (hX : IsPreBrownianReal X P)
    (hY : IsPreBrownianReal Y Q) (hXm : ∀ t, Measurable (X t)) (hYm : ∀ t, Measurable (Y t)) :
    P.map (pathOf X) = Q.map (pathOf Y) :=
  (isProjectiveLimit_map_pathOf hX hXm).unique (isProjectiveLimit_map_pathOf hY hYm)

end InteractingSLE.ZhanGT4.Mix
