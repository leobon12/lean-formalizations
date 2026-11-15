/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A5ClearanceGen
import InteractingSLE.Spec.Zhan.AvoidMart
import InteractingSLE.Stochastic.Martingale.OptionalSampling

/-!
# Protected-ray clearance, III: a hitting bound after a deterministic time

Packet PROVE-ZHAN-CLEAR. Generic form, in the setting of `Zhan.AvoidMart` (a Brownian motion `B`, an adapted
continuous state `Λ` with `Λ' = Ψ(Λ, B)` on a full-measure `𝓖₀`-event `G`, a nonnegative `C³` observable `Φ` on an open
`U` whose Itô drift `itoGen Φ (Λ, B) (Ψ(Λ, B))` is `≤ 0` on `G`, the path staying in `U`):

**`measure_hit_after_le`.** For a deterministic time `q`, an event `A ∈ 𝓖_q` on which `Φ(X_q) ≤ ℓ`, and a level
`L > 0`: `L · P(A ∩ {∃ t ≥ q, Φ(X_t) ≥ L}) ≤ ℓ · P(A)`.

Proof: localize with `Zhan.locStop` at level `n` (`Zhan.martingale_loc`), stop the localized martingale at the first
time `τ ∈ [q, N]` at which the stopped observable reaches `L` (a hitting time of the closed set `[L, ∞) × [q, ∞)` by
`(Φ(X_{t∧σ}), t)`), use the martingale identity between the deterministic times `q ≤ N` on `A ∩ {q ≤ σ_n}`, drop the
nonpositive drift, and let `n → ∞`, then `N → ∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A5Clear

open Zhan

/-! ### Hitting times -/

section Hitting

variable {Ω : Type*} {β : Type*} [TopologicalSpace β] {X : ℝ≥0 → Ω → β} {F : Set β} {ω : Ω}

/-- If a continuous path avoids a closed set on `[0, T]`, its hitting time (capped at `n ≥ T`) is `≥ T`. -/
theorem le_hittingBtwn_of_forall_notMem (hc : Continuous (X · ω)) (hF : IsClosed F) {T n : ℝ≥0} (hTn : T ≤ n)
    (h : ∀ t ∈ Icc 0 T, X t ω ∉ F) : T ≤ hittingBtwn X F 0 n ω := by
  by_contra hcon
  push Not at hcon
  have hex : ∃ j ∈ Icc (0 : ℝ≥0) n, X j ω ∈ F := by
    by_contra hno
    have : hittingBtwn X F 0 n ω = n := by simp only [hittingBtwn, hno, ↓reduceIte]
    rw [this] at hcon
    exact absurd hTn (not_le.2 hcon)
  exact h _ ⟨zero_le, hcon.le⟩ (mem_of_hittingBtwn hc hF hex)

end Hitting

/-! ### Exhaustion by the localizing times -/

section Exhaust

open scoped Classical

variable {Ω : Type*} {E : Type*} [NormedAddCommGroup E] {B : ℝ≥0 → Ω → ℝ} {U : Set (E × ℝ)}
  {Φ : E × ℝ → ℝ} {Λ : ℝ≥0 → Ω → E} {G : Set Ω}

/-- **The localizing times at level `n` exhaust `[0, ∞)`** on `G`, for a continuous path in `U`. -/
theorem exists_le_locStop (hUc : Uᶜ.Nonempty) (hU : IsOpen U) (hΦc : ContinuousOn Φ U) {ω : Ω} (hω : ω ∈ G)
    (hc : Continuous fun t => pathX Λ B t ω) (hin : ∀ t, pathX Λ B t ω ∈ U) (T : ℝ≥0) :
    ∃ n₁ : ℕ, ∀ n ≥ n₁, T ≤ locStop G Λ B U Φ n n ω := by
  obtain ⟨n₁, hn₁⟩ := exists_level_of_continuousOn hUc hU (x := fun t => pathX Λ B t ω) (T := T)
    hc.continuousOn fun t _ => hin t
  have hΦpc : ContinuousOn (fun t => Φ (pathX Λ B t ω)) (Icc 0 T) :=
    hΦc.comp hc.continuousOn fun t _ => hin t
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hΦpc
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt C
  refine ⟨max n₁ n₂, fun n hn => ?_⟩
  have h1 := hn₁ n (le_of_max_le_left hn)
  have h2 : (n₂ : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  simp only [locStop, hω, ↓reduceIte]
  refine le_hittingBtwn_of_forall_notMem hc (isClosed_exitSet hΦc) ?_ fun t ht hex => ?_
  · have := h1.1; exact_mod_cast this
  · obtain ⟨hd, hn⟩ := h1.2 t ht
    rcases hex with h | h | h
    · linarith
    · linarith
    · have := hC t ht
      rw [Real.norm_eq_abs] at this
      linarith [le_abs_self (Φ (pathX Λ B t ω)), h.2]

end Exhaust

/-! ### The localized estimate -/

section Generic

open scoped Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 mΩ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {B : ℝ≥0 → Ω → ℝ} {U : Set (E × ℝ)} {Φ : E × ℝ → ℝ}
  {Ψ : E × ℝ → E} {Λ : ℝ≥0 → Ω → E} {G : Set Ω} {p₀ : E}

/-- The localized integral `t ↦ ∫₀^{t ∧ σ} g` of a function continuous on `[0, σ]` is continuous. -/
theorem continuous_integral_min {g : ℝ → ℝ} {σ : ℝ≥0} (hg : ContinuousOn g (Icc 0 σ)) :
    Continuous fun t : ℝ≥0 => ∫ s in (0 : ℝ)..((min t σ : ℝ≥0) : ℝ), g s := by
  have hprim : ContinuousOn (fun x => ∫ s in (0 : ℝ)..x, g s) (uIcc 0 σ) :=
    intervalIntegral.continuousOn_primitive_interval
      ((hg.mono (by rw [uIcc_of_le σ.coe_nonneg])).integrableOn_compact isCompact_uIcc
        |>.mono_set (by rw [uIcc_of_le σ.coe_nonneg]))
  refine hprim.comp_continuous (NNReal.continuous_coe.comp (continuous_id.min continuous_const))
    fun t => ?_
  rw [uIcc_of_le σ.coe_nonneg]
  exact ⟨(min t σ).coe_nonneg, by exact_mod_cast min_le_right t σ⟩

variable (hB : IsFilteredBrownianReal 𝓖 B P) (hBc : ∀ ω, Continuous (B · ω)) (hU : IsOpen U)
  (hΦ : ContDiffOn ℝ 3 Φ U) (hΦ0 : ∀ p ∈ U, 0 ≤ Φ p) (hΨ : ContinuousOn Ψ U)
  (hgen : ∀ ω ∈ G, ∀ t, Ito.itoGen Φ (pathX Λ B t ω) (Ψ (pathX Λ B t ω)) ≤ 0)
  (hΛm : ∀ t, Measurable[𝓖 t] (Λ t)) (hΛc : ∀ ω, Continuous (Λ · ω)) (hG : MeasurableSet[𝓖 0] G)
  (hGc : P Gᶜ = 0) (hΛ0 : ∀ ω, Λ 0 ω = p₀) (hB0 : ∀ ω, B 0 ω = 0)
  (hpath : ∀ ω ∈ G, ∀ t : ℝ≥0, Λ t ω = p₀ + ∫ s in (0 : ℝ)..t, Ψ (pathX Λ B s.toNNReal ω))
  (hin : ∀ ω t, pathX Λ B t ω ∈ U)

include hB hBc hU hΦ hΦ0 hΨ hgen hΛm hΛc hG hGc hΛ0 hB0 hpath hin in
/-- **The localized hitting bound**: at level `n` (with the start off the exit set), for a deterministic `q ≤ N`, an
event `A ∈ 𝓖_q` on which `Φ(X_q) ≤ ℓ`, and `L > 0`, the probability that `A` holds, `q ≤ σ_n`, and `Φ(X_t) ≥ L` at
some `t ∈ [q, N]` with `t ≤ σ_n` is at most `ℓ P(A)/L`. -/
theorem measure_hit_loc_le {n : ℕ} (hX0 : ((p₀, 0) : E × ℝ) ∉ exitSet U Φ n n) {q N : ℝ≥0} (hqN : q ≤ N)
    {A : Set Ω} (hA : MeasurableSet[𝓖 q] A) {ℓ Lv : ℝ} (hℓ0 : 0 ≤ ℓ) (hLv : 0 < Lv)
    (hℓ : ∀ ω ∈ A, Φ (pathX Λ B q ω) ≤ ℓ) :
    Lv * P.real (A ∩ {ω | q ≤ locStop G Λ B U Φ n n ω} ∩
        {ω | ∃ t, q ≤ t ∧ t ≤ N ∧ t ≤ locStop G Λ B U Φ n n ω ∧ Lv ≤ Φ (pathX Λ B t ω)}) ≤
      ℓ * P.real A := by
  have hΦc : ContinuousOn Φ U := hΦ.continuousOn
  set σ := locStop G Λ B U Φ n n with hσdef
  have hσ : IsStoppingTime 𝓖 fun ω => (σ ω : WithTop ℝ≥0) :=
    isStoppingTime_locStop hB hBc hΦc hΛm hΛc hG
  have hM := martingale_loc hB hBc hU hΦc hΨ hΛm hΛc hG hΛ0 hB0 hpath hX0 hΦ
  set M : ℝ≥0 → Ω → ℝ := fun t ω => Φ (pathX Λ B (min t (σ ω)) ω) -
    ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), Ito.itoGen Φ (pathX Λ B s.toNNReal ω) (locDens G Λ B Ψ s ω)
    with hMdef
  -- the stopped observable
  set Y : ℝ≥0 → Ω → ℝ := fun t ω => Φ (pathX Λ B (min t (σ ω)) ω) with hYdef
  have hpc : ∀ ω, Continuous fun t => pathX Λ B t ω := continuous_pathX hΛc hBc
  have hYc : ∀ ω, Continuous (Y · ω) := fun ω =>
    hΦc.comp_continuous ((hpc ω).comp (continuous_id.min continuous_const)) fun t => hin ω _
  have hkeep : ∀ ω {t : ℝ≥0}, t ≤ σ ω → pathX Λ B t ω ∈ keepSet U Φ n n := fun ω t ht =>
    pathX_mem_keepSet hBc hΦc hΛc hΛ0 hB0 hX0 ht
  have hY0 : ∀ t ω, 0 ≤ Y t ω := fun t ω => hΦ0 _ (hin ω _)
  have hYn : ∀ t ω, Y t ω ≤ n := fun t ω => (hkeep ω (min_le_right t (σ ω))).2.2
  have hΛσm : ∀ t, Measurable[𝓖 t] fun ω => Λ (min t (σ ω)) ω := fun t => by
    have h := Ito.measurable_stopped_of_agree (X := Λ) hσ hΛm (G := univ)
      (@MeasurableSet.univ _ (𝓖 0)) (0 : E) (fun _ _ _ _ => rfl) (fun ω _ => (hΛc ω).continuousOn) t
    simpa using h
  have hBσm : ∀ t, Measurable[𝓖 t] fun ω => B (min t (σ ω)) ω := fun t => by
    have h := Ito.measurable_stopped_of_agree (X := B) hσ hB.2.1 (G := univ)
      (@MeasurableSet.univ _ (𝓖 0)) (0 : ℝ) (fun _ _ _ _ => rfl) (fun ω _ => (hBc ω).continuousOn) t
    simpa using h
  have hYm : ∀ t, Measurable[𝓖 t] (Y t) := fun t => by
    have hpw := (hΦc.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) hU.measurableSet).comp
      ((hΛσm t).prodMk (hBσm t))
    have heq : Y t = (U.piecewise Φ fun _ => (0 : ℝ)) ∘ fun ω => (Λ (min t (σ ω)) ω, B (min t (σ ω)) ω) := by
      funext ω
      simp only [hYdef, Function.comp_apply, pathX]
      rw [Set.piecewise_eq_of_mem _ _ _ (by simpa only [pathX] using hin ω (min t (σ ω)))]
    rw [heq]; exact hpw
  -- the hitting time after `q`
  set Yh : ℝ≥0 → Ω → ℝ × ℝ≥0 := fun t ω => (Y t ω, t) with hYh
  set K : Set (ℝ × ℝ≥0) := Ici Lv ×ˢ Ici q with hKdef
  have hK : IsClosed K := isClosed_Ici.prod isClosed_Ici
  have hYhc : ∀ ω, Continuous (Yh · ω) := fun ω => (hYc ω).prodMk continuous_id
  set τ : Ω → ℝ≥0 := fun ω => hittingBtwn Yh K 0 N ω with hτdef
  have hτ : IsStoppingTime 𝓖 fun ω => (τ ω : WithTop ℝ≥0) :=
    QuantumZipper.ItoLite.isStoppingTime_hittingBtwn_of_isClosed
      (fun t => (hYm t).prodMk measurable_const) hYhc hK N
  have hτN : ∀ ω, τ ω ≤ N := fun ω => hittingBtwn_le ω
  have hqτ : ∀ ω, q ≤ τ ω := by
    intro ω
    by_cases hex : ∃ j ∈ Icc (0 : ℝ≥0) N, Yh j ω ∈ K
    · exact (mem_of_hittingBtwn (hYhc ω) hK hex).2
    · have : τ ω = N := by simp only [hτdef, hittingBtwn, hex, ↓reduceIte]
      rw [this]; exact hqN
  have hhit : ∀ ω, (∃ t, q ≤ t ∧ t ≤ N ∧ t ≤ σ ω ∧ Lv ≤ Φ (pathX Λ B t ω)) → Lv ≤ Y (τ ω) ω := by
    rintro ω ⟨t, hqt, htN, htσ, hLt⟩
    have hex : ∃ j ∈ Icc (0 : ℝ≥0) N, Yh j ω ∈ K := by
      refine ⟨t, ⟨zero_le, htN⟩, ?_, hqt⟩
      show Lv ≤ Y t ω
      simp only [hYdef, min_eq_left htσ]; exact hLt
    exact (mem_of_hittingBtwn (hYhc ω) hK hex).1
  -- the localized martingale is continuous
  have hσG : ∀ ω, ω ∉ G → σ ω = 0 := fun ω hω => by simp [hσdef, locStop, hω]
  have hgc : ∀ ω, ContinuousOn (fun s : ℝ => Ito.itoGen Φ (pathX Λ B s.toNNReal ω) (locDens G Λ B Ψ s ω))
      (Icc 0 (σ ω)) := by
    intro ω
    by_cases hω : ω ∈ G
    · have h1 := (continuousOn_itoGen hU hΦ hΨ).comp_continuous
        ((hpc ω).comp continuous_real_toNNReal) fun s => hin ω _
      refine h1.continuousOn.congr fun s _ => ?_
      simp only [Function.comp_apply, locDens, hω, ↓reduceIte]
    · rw [hσG ω hω, NNReal.coe_zero, Icc_self]; exact continuousOn_singleton _ _
  have hMc : ∀ ω, Continuous (M · ω) := fun ω => (hYc ω).sub (continuous_integral_min (hgc ω))
  have hMτ := Martingale.stoppedProcess_of_rightContinuous hM (fun ω t => (hMc ω).continuousWithinAt) hτ
  -- the event `A' = A ∩ {q ≤ σ}`
  set A' := A ∩ {ω | q ≤ σ ω} with hA'def
  have hA' : MeasurableSet[𝓖 q] A' := by
    refine hA.inter ?_
    have h := hσ.measurableSet_ge q
    simpa only [WithTop.coe_le_coe] using h
  have hA'm : MeasurableSet A' := 𝓖.le q _ hA'
  have heq := hMτ.setIntegral_eq hqN hA'
  have hsq : ∀ ω, stoppedProcess M (fun ω => (τ ω : WithTop ℝ≥0)) q ω = M q ω := fun ω =>
    stoppedProcess_eq_of_le (by exact_mod_cast hqτ ω)
  have hsN : ∀ ω, stoppedProcess M (fun ω => (τ ω : WithTop ℝ≥0)) N ω = M (τ ω) ω := fun ω => by
    rw [stoppedProcess_eq_of_ge (by exact_mod_cast hτN ω)]; rfl
  simp only [hsq, hsN] at heq
  -- integrability
  have hYτm : Measurable fun ω => Y (τ ω) ω := by
    have hprog := isStronglyProgressive_of_rightContinuous (𝓕 := 𝓖) (X := Y)
      (fun t => (hYm t).stronglyMeasurable) fun ω t => (hYc ω).continuousWithinAt
    exact (measurable_stoppedValue hprog hτ).mono hτ.measurableSpace_le le_rfl
  have hYτi : Integrable (fun ω => Y (τ ω) ω) P := Integrable.of_bound hYτm.aestronglyMeasurable n
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hY0 _ _)]; exact hYn _ _)
  have hYqi : Integrable (Y q) P := Integrable.of_bound ((hYm q).mono (𝓖.le q) le_rfl).aestronglyMeasurable n
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hY0 _ _)]; exact hYn _ _)
  have hMqi : Integrable (M q) P := hM.integrable q
  have hMτi : Integrable (fun ω => M (τ ω) ω) P := by
    have := hMτ.integrable N
    have e : stoppedProcess M (fun ω => (τ ω : WithTop ℝ≥0)) N = fun ω => M (τ ω) ω := funext hsN
    rwa [e] at this
  -- the drift between `q ∧ σ` and `τ ∧ σ` is nonpositive on `G`
  have hdrift : ∀ ω ∈ G, Y (τ ω) ω - Y q ω ≤ M (τ ω) ω - M q ω := by
    intro ω hω
    have hab : ((min q (σ ω) : ℝ≥0) : ℝ) ≤ ((min (τ ω) (σ ω) : ℝ≥0) : ℝ) := by
      exact_mod_cast min_le_min_right _ (hqτ ω)
    have hbσ : ((min (τ ω) (σ ω) : ℝ≥0) : ℝ) ≤ σ ω := by exact_mod_cast min_le_right _ _
    have hint : ∀ b : ℝ, 0 ≤ b → b ≤ σ ω → IntervalIntegrable (fun s : ℝ => Ito.itoGen Φ
        (pathX Λ B s.toNNReal ω) (locDens G Λ B Ψ s ω)) volume 0 b := fun b hb0 hbσ =>
      ((hgc ω).mono (Icc_subset_Icc le_rfl hbσ)).intervalIntegrable_of_Icc hb0
    have hsplit := intervalIntegral.integral_interval_sub_left
      (hint _ (min (τ ω) (σ ω)).coe_nonneg hbσ) (hint _ (min q (σ ω)).coe_nonneg (hab.trans hbσ))
    have hneg : ∫ s in ((min q (σ ω) : ℝ≥0) : ℝ)..((min (τ ω) (σ ω) : ℝ≥0) : ℝ),
        Ito.itoGen Φ (pathX Λ B s.toNNReal ω) (locDens G Λ B Ψ s ω) ≤ 0 := by
      have hm := intervalIntegral.integral_mono_on hab
        (hint _ (min (τ ω) (σ ω)).coe_nonneg hbσ |>.mono_set (by
          rw [uIcc_of_le hab, uIcc_of_le (min (τ ω) (σ ω)).coe_nonneg]
          exact Icc_subset_Icc (min q (σ ω)).coe_nonneg le_rfl))
        (intervalIntegrable_const (c := (0 : ℝ))) fun s _ => by
          simp only [locDens, hω, ↓reduceIte]
          exact hgen ω hω s.toNNReal
      simpa using hm
    simp only [hMdef, hYdef]
    linarith
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hGc
  have hI1 : ∫ ω in A', (Y (τ ω) ω - Y q ω) ∂P ≤ ∫ ω in A', (M (τ ω) ω - M q ω) ∂P :=
    setIntegral_mono_ae (hYτi.sub hYqi).integrableOn (hMτi.sub hMqi).integrableOn
      (hGae.mono fun ω hω => hdrift ω hω)
  rw [integral_sub hYτi.integrableOn hYqi.integrableOn, integral_sub hMτi.integrableOn hMqi.integrableOn,
    heq, sub_self] at hI1
  -- the two ends
  set H' := {ω | Lv ≤ Y (τ ω) ω} with hH'def
  have hH'm : MeasurableSet H' := measurableSet_le measurable_const hYτm
  have hlow : Lv * P.real (A' ∩ H') ≤ ∫ ω in A', Y (τ ω) ω ∂P := by
    have h1 : ∫ ω in A', H'.indicator (fun _ => Lv) ω ∂P = Lv * P.real (A' ∩ H') := by
      rw [integral_indicator hH'm, setIntegral_const, measureReal_restrict_apply hH'm, smul_eq_mul,
        Set.inter_comm, mul_comm]
    rw [← h1]
    refine setIntegral_mono_on ((integrable_const Lv).indicator hH'm).integrableOn hYτi.integrableOn hA'm
      fun ω _ => ?_
    by_cases hω : ω ∈ H'
    · rw [Set.indicator_of_mem hω]; exact hω
    · rw [Set.indicator_of_notMem hω]; exact hY0 _ _
  have hup : ∫ ω in A', Y q ω ∂P ≤ ℓ * P.real A' := by
    have h1 : ∫ ω in A', ℓ ∂P = ℓ * P.real A' := by rw [setIntegral_const, smul_eq_mul, mul_comm]
    rw [← h1]
    refine setIntegral_mono_on hYqi.integrableOn (integrable_const ℓ).integrableOn hA'm fun ω hω => ?_
    have hq : q ≤ σ ω := hω.2
    simp only [hYdef, min_eq_left hq]
    exact hℓ ω hω.1
  have hsub : A ∩ {ω | q ≤ σ ω} ∩ {ω | ∃ t, q ≤ t ∧ t ≤ N ∧ t ≤ σ ω ∧ Lv ≤ Φ (pathX Λ B t ω)} ⊆ A' ∩ H' :=
    fun ω hω => ⟨hω.1, hhit ω hω.2⟩
  have hmono := measureReal_mono (μ := P) hsub
  have hA'A : P.real A' ≤ P.real A := measureReal_mono Set.inter_subset_left
  calc Lv * P.real (A ∩ {ω | q ≤ σ ω} ∩ {ω | ∃ t, q ≤ t ∧ t ≤ N ∧ t ≤ σ ω ∧ Lv ≤ Φ (pathX Λ B t ω)})
      ≤ Lv * P.real (A' ∩ H') := mul_le_mul_of_nonneg_left hmono hLv.le
    _ ≤ ∫ ω in A', Y (τ ω) ω ∂P := hlow
    _ ≤ ∫ ω in A', Y q ω ∂P := by linarith
    _ ≤ ℓ * P.real A' := hup
    _ ≤ ℓ * P.real A := mul_le_mul_of_nonneg_left hA'A hℓ0

include hB hBc hU hΦ hΦ0 hΨ hgen hΛm hΛc hG hGc hΛ0 hB0 hpath hin in
/-- **The hitting bound after a deterministic time**: for `q`, an event `A ∈ 𝓖_q` on which `Φ(X_q) ≤ ℓ`, and `L > 0`,
`L · P(A ∩ {∃ t ≥ q, Φ(X_t) ≥ L}) ≤ ℓ · P(A)`. -/
theorem measure_hit_after_le (hUc : Uᶜ.Nonempty) (hp₀ : ((p₀, 0) : E × ℝ) ∈ U) {q : ℝ≥0} {A : Set Ω}
    (hA : MeasurableSet[𝓖 q] A) {ℓ Lv : ℝ} (hℓ0 : 0 ≤ ℓ) (hLv : 0 < Lv)
    (hℓ : ∀ ω ∈ A, Φ (pathX Λ B q ω) ≤ ℓ) :
    Lv * P.real (A ∩ {ω | ∃ t, q ≤ t ∧ Lv ≤ Φ (pathX Λ B t ω)}) ≤ ℓ * P.real A := by
  have hΦc : ContinuousOn Φ U := hΦ.continuousOn
  set c : ℝ := ℓ * P.real A / Lv with hc
  have hc0 : 0 ≤ c := by positivity
  -- the start is eventually off the exit sets
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ n ≥ n₀, ((p₀, 0) : E × ℝ) ∉ exitSet U Φ n n := by
    set x₀ : E × ℝ := (p₀, 0)
    have hd : 0 < infDist x₀ Uᶜ :=
      (hU.isClosed_compl.notMem_iff_infDist_pos hUc).1 fun h => h hp₀
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max (1 / infDist x₀ Uᶜ) (max ‖x₀‖ (Φ x₀)))
    refine ⟨n₀, fun n hn => ?_⟩
    have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
    have h1 := le_max_left (1 / infDist x₀ Uᶜ) (max ‖x₀‖ (Φ x₀))
    have h2 := le_max_right (1 / infDist x₀ Uᶜ) (max ‖x₀‖ (Φ x₀))
    have h3 := le_max_left ‖x₀‖ (Φ x₀)
    have h4 := le_max_right ‖x₀‖ (Φ x₀)
    rintro (h | h | h)
    · have h5 : 1 / infDist x₀ Uᶜ < (n : ℝ) + 1 := by linarith
      have h6 : 1 / ((n : ℝ) + 1) < infDist x₀ Uᶜ := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hd] at h5
        linarith
      linarith
    · linarith
    · linarith [h.2]
  -- the bound at every localization level and horizon
  have hloc : ∀ n ≥ n₀, ∀ N : ℝ≥0, q ≤ N →
      P (A ∩ {ω | q ≤ locStop G Λ B U Φ n n ω} ∩
        {ω | ∃ t, q ≤ t ∧ t ≤ N ∧ t ≤ locStop G Λ B U Φ n n ω ∧ Lv ≤ Φ (pathX Λ B t ω)}) ≤
        ENNReal.ofReal c := by
    intro n hn N hqN
    have h := measure_hit_loc_le hB hBc hU hΦ hΦ0 hΨ hgen hΛm hΛc hG hGc hΛ0 hB0 hpath hin (hn₀ n hn)
      hqN hA hℓ0 hLv hℓ
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (by rw [hc, le_div_iff₀ hLv]; linarith)
  have hGc' : ∀ s : Set Ω, P (s \ G) = 0 := fun s => measure_mono_null (fun ω hω => hω.2) hGc
  -- a fixed horizon `q + N`
  have hN : ∀ N : ℕ, P (A ∩ {ω | ∃ t, q ≤ t ∧ t ≤ q + N ∧ Lv ≤ Φ (pathX Λ B t ω)}) ≤ ENNReal.ofReal c := by
    intro N
    set S : ℕ → Set Ω := fun n => A ∩ {ω | q ≤ locStop G Λ B U Φ n n ω} ∩
      {ω | ∃ t, q ≤ t ∧ t ≤ q + N ∧ t ≤ locStop G Λ B U Φ n n ω ∧ Lv ≤ Φ (pathX Λ B t ω)} with hS
    set D : ℕ → Set Ω := fun m => ⋂ n, ⋂ (_ : m + n₀ ≤ n), S n with hD
    have hDmono : Monotone D := fun m m' hmm' ω hω => by
      simp only [hD, mem_iInter] at hω ⊢
      exact fun n hn => hω n (le_trans (by omega) hn)
    have hDle : ∀ m, P (D m) ≤ ENNReal.ofReal c := fun m =>
      (measure_mono (iInter₂_subset (m + n₀) le_rfl)).trans (hloc (m + n₀) (by omega) _ le_self_add)
    have hsub : (A ∩ {ω | ∃ t, q ≤ t ∧ t ≤ q + N ∧ Lv ≤ Φ (pathX Λ B t ω)}) ∩ G ⊆ ⋃ m, D m := by
      rintro ω ⟨⟨hωA, t, hqt, htN, hLt⟩, hωG⟩
      obtain ⟨n₁, hn₁⟩ := exists_le_locStop hUc hU hΦc hωG (continuous_pathX hΛc hBc ω) (hin ω) (q + N)
      refine mem_iUnion.2 ⟨n₁, mem_iInter₂.2 fun n hn => ?_⟩
      have h1 := hn₁ n (by omega)
      exact ⟨⟨hωA, le_self_add.trans h1⟩, t, hqt, htN, htN.trans h1, hLt⟩
    calc P (A ∩ {ω | ∃ t, q ≤ t ∧ t ≤ q + N ∧ Lv ≤ Φ (pathX Λ B t ω)})
        ≤ P ((A ∩ {ω | ∃ t, q ≤ t ∧ t ≤ q + N ∧ Lv ≤ Φ (pathX Λ B t ω)}) ∩ G) +
            P ((A ∩ {ω | ∃ t, q ≤ t ∧ t ≤ q + N ∧ Lv ≤ Φ (pathX Λ B t ω)}) \ G) :=
          measure_le_inter_add_sdiff _ _ _
      _ = P ((A ∩ {ω | ∃ t, q ≤ t ∧ t ≤ q + N ∧ Lv ≤ Φ (pathX Λ B t ω)}) ∩ G) := by rw [hGc', add_zero]
      _ ≤ P (⋃ m, D m) := measure_mono hsub
      _ = ⨆ m, P (D m) := hDmono.measure_iUnion
      _ ≤ ENNReal.ofReal c := iSup_le hDle
  -- all horizons
  have hmono : Monotone fun N : ℕ => A ∩ {ω | ∃ t, q ≤ t ∧ t ≤ q + N ∧ Lv ≤ Φ (pathX Λ B t ω)} := by
    intro N N' hNN' ω ⟨hωA, t, hqt, htN, hLt⟩
    refine ⟨hωA, t, hqt, htN.trans ?_, hLt⟩
    have : (N : ℝ≥0) ≤ N' := by exact_mod_cast hNN'
    exact add_le_add_right this q
  have heq : A ∩ {ω | ∃ t, q ≤ t ∧ Lv ≤ Φ (pathX Λ B t ω)} =
      ⋃ N : ℕ, A ∩ {ω | ∃ t, q ≤ t ∧ t ≤ q + N ∧ Lv ≤ Φ (pathX Λ B t ω)} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hωA, t, hqt, hLt⟩
      obtain ⟨N, hN⟩ := exists_nat_ge t
      exact ⟨N, hωA, t, hqt, hN.trans le_add_self, hLt⟩
    · rintro ⟨N, hωA, t, hqt, -, hLt⟩
      exact ⟨hωA, t, hqt, hLt⟩
  have hall : P (A ∩ {ω | ∃ t, q ≤ t ∧ Lv ≤ Φ (pathX Λ B t ω)}) ≤ ENNReal.ofReal c := by
    rw [heq, hmono.measure_iUnion]; exact iSup_le hN
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hall
  rw [ENNReal.toReal_ofReal hc0, ← measureReal_def, hc, le_div_iff₀ hLv] at h
  linarith

end Generic

end InteractingSLE.ZhanGT4.A5Clear
