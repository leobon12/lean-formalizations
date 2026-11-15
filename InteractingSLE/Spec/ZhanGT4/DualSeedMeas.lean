/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFieldMart
import InteractingSLE.Spec.ZhanGT4.FrozenMeas
import InteractingSLE.Spec.Ito.Measurability

/-!
# Zhan's A.1.6, the seeded field VIII: the measurability inputs

Packet PROVE-ZHAN-GT4-A21. Source: Astra, *Follow-up proofs*, §A.1.6 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L426–L500, R38), with §A.1.2–A.1.3 (the factors of `M̃` are adapted processes).

`isDriftLogField_seed` (`DualSeedFieldMart`) takes as hypotheses the adaptedness of the seeded log-density `ℓ` and
of `ℓ_x`, `ℓ_xx` along the drifted driver `W = √κ B + D` (`hm0`–`hm2`). Here they are proved from the adaptedness of
the inputs. With the other curve frozen (deterministic hull `A`, chart `φ`, tip `ζ₀`), every conformal factor of
`ℓ(t, W_t)` is a canonical function of the random image hull `E_t = g_t(A)`:

* `A_{j,k}(t) = F_t^{(k)}(W_t)`, `A_{k,0}`, `A_{k,1}`, `log F`: A8's `FrozenMeas`, whose inputs (`FrzMeas`) hold for
  **every adapted continuous driver** (`frzMeas_of_adaptedX`, the version of A8's `frzMeas_of_adapted` for a general
  process `X` in place of `√κ B`);
* `B_{m,0}(t) = F_t(V^m_t)`, `B_{m,1}(t) = F_t'(V^m_t)` at the adapted random real point `V^m_t`: a forward limit of
  the mapping-out function of `E_t` along `ℍ \ E_t` at `V^m_t`, which has a clear disc
  (`FrzMeas.measurable_iterDeriv_ownExt_at`, `FrzMeas.measurable_F_at`);
* the own-chart coordinates `V⁰_t`, `G⁰_t`, `V^m_t` and the driver `W_t` (adapted inputs).

## Main results

* `frzMeas_of_adaptedX`: A8's measurability inputs for an adapted continuous driver;
* `FrzMeas.measurable_iterDeriv_ownExt_at`, `FrzMeas.measurable_F_at`: `F_t^{(k)}` at a random clear real point;
* `measurable_seed_parts`, **`measurable_seed_ell`, `measurable_seed_ellX`, `measurable_seed_ellXX`**: the factors
  and `ℓ`, `ℓ_x`, `ℓ_xx` along the driver are `𝓕_q`-measurable on any `𝓕_q`-event `G` on which the data are regular
  up to a horizon `T ≥ q`;
* **`seed_meas_inputs_on`**: the inputs `hm0`–`hm2` of `isDriftLogField_seed` (on an `𝓕_ε`-event `E`; `E = univ`
  is the form `isDriftLogField_seed` takes);
* **`integral_mul_seed_stopped_sub_eq_zero_of_adapted`**: A20's martingale identity with `hm0`–`hm2` discharged.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### A8's measurability inputs for an adapted continuous driver -/

/-- **`FrzMeas` from an adapted continuous driver.** For a driver `W ω = X(·, ω)` (as a path on `ℝ`) with `X`
adapted and continuous, on an `𝓕_r`-event `G` on which `OwnData` holds up to `T ω ≥ u` (`0 ≤ u ≤ r`), the
measurability inputs of `FrozenMeas` hold at time `u` for the σ-algebra `𝓕_r` (`Ito.measurableSet_aliveSet`,
`Ito.measurable_fwdMap_alive`). A8's `frzMeas_of_adapted` is the case `X = √κ B`. -/
theorem frzMeas_of_adaptedX {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} (hXm : ∀ u, Measurable[𝓕 u] (X u))
    (hXc : ∀ ω, Continuous (X · ω)) {W W' a : Ω → ℝ → ℝ} (hW : ∀ ω, W ω = Ito.rpath (X · ω)) {A : Set ℂ}
    {φ : ℂ → ℂ} {T : Ω → ℝ} {G : Set Ω} {r : ℝ≥0} (hG : MeasurableSet[𝓕 r] G)
    (hown : ∀ ω ∈ G, OwnData (W ω) A φ (T ω) (a ω) (W' ω)) {u : ℝ} (hu : u ∈ Icc 0 (r : ℝ))
    (hmem : ∀ ω ∈ G, u ∈ Icc 0 (T ω)) :
    @FrzMeas Ω (𝓕 r) W W' a A φ T G u := by
  classical
  have hAd : AdaptedBefore 𝓕 (fun _ => (⊤ : ℝ≥0∞)) X := fun t A hA => by
    have : {ω | ((t : ℝ≥0∞) < ⊤) ∧ X t ω ∈ A} = X t ⁻¹' A := by
      ext ω; simp [ENNReal.coe_lt_top]
    rw [this]; exact hXm t hA
  have hGc : ∀ ω ∈ (univ : Set Ω), ContinuousOn (fun t => X t ω) {t | (t : ℝ≥0∞) < ⊤} := fun ω _ =>
    (hXc ω).continuousOn
  set s := u.toNNReal with hs
  have hsr : s ≤ r := Real.toNNReal_le_iff_le_coe.2 hu.2
  have hus : ((s : ℝ≥0) : ℝ) = u := Real.coe_toNNReal _ hu.1
  have hal : ∀ z, {ω | ω ∈ G ∧ ∃ v, IsForwardSol (W ω) z u v} =
      G ∩ Ito.aliveSet X (fun _ => ⊤) univ z s := fun z => by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, Ito.aliveSet, mem_univ, true_and, ENNReal.coe_lt_top, hW ω, hus]
  have hdrv : Measurable[𝓕 r] fun ω => W ω u := by
    have : (fun ω => W ω u) = X s := by funext ω; rw [hW ω]; rfl
    rw [this]; exact (hXm s).mono (𝓕.mono hsr) le_rfl
  have hals : ∀ z ∈ H, MeasurableSet[𝓕 r] {ω | ω ∈ G ∧ ∃ v, IsForwardSol (W ω) z u v} := fun z hz => by
    rw [hal]
    exact hG.inter (𝓕.mono hsr _ (Ito.measurableSet_aliveSet hAd hGc MeasurableSet.univ hz s))
  have hfwd : ∀ z ∈ H, Measurable[𝓕 r] ({ω | ω ∈ G ∧ ∃ v, IsForwardSol (W ω) z u v}.indicator
      fun ω => fwdMap (W ω) u z) := fun z hz => by
    have heq : ({ω | ω ∈ G ∧ ∃ v, IsForwardSol (W ω) z u v}.indicator fun ω => fwdMap (W ω) u z) =
        G.indicator fun ω => if ω ∈ Ito.aliveSet X (fun _ => ⊤) univ z s then
          fwdMap (Ito.rpath fun x => X x ω) (s : ℝ) z else 0 := by
      funext ω
      rw [hal]
      by_cases hω : ω ∈ G
      · by_cases ha : ω ∈ Ito.aliveSet X (fun _ => ⊤) univ z s
        · rw [indicator_of_mem (show ω ∈ G ∩ Ito.aliveSet X (fun _ => ⊤) univ z s from ⟨hω, ha⟩),
            indicator_of_mem hω, hW ω, hus]
          simp only [ha, ↓reduceIte]
        · rw [indicator_of_notMem (show ω ∉ G ∩ Ito.aliveSet X (fun _ => ⊤) univ z s from fun h => ha h.2),
            indicator_of_mem hω]
          simp only [ha, ↓reduceIte]
      · rw [indicator_of_notMem (fun h => hω h.1), indicator_of_notMem hω]
    rw [heq]
    exact ((Ito.measurable_fwdMap_alive hAd hGc MeasurableSet.univ hz s).mono (𝓕.mono hsr) le_rfl).indicator hG
  exact @FrzMeas.mk Ω (𝓕 r) _ _ _ _ _ _ _ _ hG hown hmem hdrv hals hfwd

/-! ### `F_t^{(k)}` at a random clear real point -/

/-- The indicator of a real-valued function, coerced to `ℂ`. -/
theorem indicator_ofReal (G : Set Ω) (q : Ω → ℝ) :
    (G.indicator fun ω => ((q ω : ℝ) : ℂ)) = fun ω => ((G.indicator q ω : ℝ) : ℂ) := by
  funext ω
  by_cases hω : ω ∈ G
  · simp only [indicator_of_mem hω]
  · simp only [indicator_of_notMem hω, ofReal_zero]

section At

variable [MeasurableSpace Ω]

namespace FrzMeas

variable {W W' a : Ω → ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : Ω → ℝ} {G : Set Ω} {t : ℝ}
  (hM : FrzMeas W W' a A φ T G t)
include hM

/-- **`F_t^{(k)}(q)` is measurable at a random real point `q` with a clear disc**, `F_t = ownExt … t`: a forward
limit of `R_t^{(k)}` at `q` along `ℍ \ E_t` (`R_t` the mapping-out function of `E_t`). The case `q = W_t` is A8's
`measurable_iterDeriv_ownExt`. -/
theorem measurable_iterDeriv_ownExt_at (k : ℕ) {q : Ω → ℝ} (hq : Measurable (G.indicator q))
    (hcl : ∀ ω ∈ G, ∃ ρ > 0, Disjoint (ball (q ω : ℂ) ρ) (imgHull (W ω) A t)) :
    Measurable (G.indicator fun ω => deriv^[k] (ownExt (W ω) (W' ω) (a ω) φ t) (q ω)) := by
  have hqC : Measurable (G.indicator fun ω => ((q ω : ℝ) : ℂ)) := by
    rw [indicator_ofReal]; exact Complex.measurable_ofReal.comp hq
  refine measurable_indicator_of_tendsto' hM.meas (D := fun ω => H \ imgHull (W ω) A t)
    (f := fun ω => deriv^[k] (ConformalImage.mapOut (imgHull (W ω) A t))) (q := fun ω => (q ω : ℂ))
    (fun ω hω => (hM.isHPHull hω).2.2.1) hM.measurableSet_mem_diff (hM.measurable_iterDeriv_mapOut k) hqC
    (fun ω hω => ?_) (fun ω hω => ?_)
  · obtain ⟨ρ, hρ, hdisj⟩ := hcl ω hω
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hs : 0 < min ε ρ / 2 := by positivity
    have hlt : min ε ρ / 2 < ρ := by have := min_le_right ε ρ; linarith
    have hlt' : min ε ρ / 2 < ε := by have := min_le_left ε ρ; linarith
    have hd : dist (q ω : ℂ) ((q ω : ℂ) + ((min ε ρ / 2 : ℝ) : ℂ) * I) = min ε ρ / 2 := by
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    refine ⟨(q ω : ℂ) + ((min ε ρ / 2 : ℝ) : ℂ) * I, ⟨?_, fun hE => ?_⟩, by rw [hd]; exact hlt'⟩
    · show 0 < ((q ω : ℂ) + ((min ε ρ / 2 : ℝ) : ℂ) * I).im
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
      exact hs
    · refine Set.disjoint_left.1 hdisj ?_ hE
      rw [mem_ball, dist_comm, hd]
      exact hlt
  · obtain ⟨ρ, hρ, hdisj⟩ := hcl ω hω
    obtain ⟨hd, -, -, -, -, hR⟩ := (hM.own ω hω).ownExt_props (hM.mem ω hω) hdisj
    have hR' := hR _ (ConformalImage.isMapOut_mapOut (hM.isHPHull hω))
    have hc : ContinuousAt (deriv^[k] (ownExt (W ω) (W' ω) (a ω) φ t)) (q ω) :=
      (differentiableOn_iterate_deriv hd isOpen_ball k).continuousOn.continuousAt
        (ball_mem_nhds _ (half_pos hρ))
    refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (q ω : ℂ) (half_pos hρ)),
      self_mem_nhdsWithin] with z hz1 hz2
    have hU : IsOpen (ball (q ω : ℂ) (ρ / 2) ∩ H) := isOpen_ball.inter QuantumZipper.isOpen_H
    exact (eventuallyEq_iterate_deriv (Filter.eventuallyEq_of_mem (hU.mem_nhds ⟨hz1, hz2.1⟩) hR') k).eq_of_nhds

/-- **`Re F_t^{(k)}(q)` is measurable** at a random clear real point `q` (on `G`). -/
theorem measurable_F_at (k : ℕ) {q : Ω → ℝ} (hq : Measurable (G.indicator q))
    (hcl : ∀ ω ∈ G, ∃ ρ > 0, Disjoint (ball (q ω : ℂ) ρ) (imgHull (W ω) A t)) :
    Measurable (G.indicator fun ω => (deriv^[k] (ownExt (W ω) (W' ω) (a ω) φ t) (q ω)).re) := by
  have heq : (G.indicator fun ω => (deriv^[k] (ownExt (W ω) (W' ω) (a ω) φ t) (q ω)).re) = fun ω =>
      (G.indicator (fun ω => deriv^[k] (ownExt (W ω) (W' ω) (a ω) φ t) (q ω)) ω).re := by
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω]
    · simp only [indicator_of_notMem hω, zero_re]
  rw [heq]
  exact Complex.measurable_re.comp (hM.measurable_iterDeriv_ownExt_at k hq hcl)

end FrzMeas

end At

/-! ### Measurability of the log-density's building blocks -/

section Blocks

variable {n : ℕ}

theorem measurable_dualLogTime (κ : ℝ) (r : Fin n → ℝ) {a21 l a20 : Ω → ℝ} {b0 b1 : Fin n → Ω → ℝ}
    (h21 : Measurable a21) (hl : Measurable l) (h20 : Measurable a20) (hb0 : ∀ m, Measurable (b0 m))
    (hb1 : ∀ m, Measurable (b1 m)) :
    Measurable fun ω => dualLogTime κ r (a21 ω) (l ω) (a20 ω) (fun m => b0 m ω) (fun m => b1 m ω) := by
  unfold dualLogTime pairSum; fun_prop

theorem measurable_dualLogSpace (κ : ℝ) (r : Fin n → ℝ) {f f1 a0 : Ω → ℝ} {b0 : Fin n → Ω → ℝ}
    (hf : Measurable f) (hf1 : Measurable f1) (ha0 : Measurable a0) (hb0 : ∀ m, Measurable (b0 m)) :
    Measurable fun ω => dualLogSpace κ r (f ω) (f1 ω) (a0 ω) (fun m => b0 m ω) := by
  unfold dualLogSpace; fun_prop

theorem measurable_dualLogSpaceX (κ : ℝ) (r : Fin n → ℝ) {f f1 f2 a0 : Ω → ℝ} {b0 : Fin n → Ω → ℝ}
    (hf : Measurable f) (hf1 : Measurable f1) (hf2 : Measurable f2) (ha0 : Measurable a0)
    (hb0 : ∀ m, Measurable (b0 m)) :
    Measurable fun ω => dualLogSpaceX κ r (f ω) (f1 ω) (f2 ω) (a0 ω) (fun m => b0 m ω) := by
  unfold dualLogSpaceX; fun_prop

theorem measurable_dualLogSpaceXX (κ : ℝ) (r : Fin n → ℝ) {f f1 f2 f3 a0 : Ω → ℝ} {b0 : Fin n → Ω → ℝ}
    (hf : Measurable f) (hf1 : Measurable f1) (hf2 : Measurable f2) (hf3 : Measurable f3) (ha0 : Measurable a0)
    (hb0 : ∀ m, Measurable (b0 m)) :
    Measurable fun ω => dualLogSpaceXX κ r (f ω) (f1 ω) (f2 ω) (f3 ω) (a0 ω) (fun m => b0 m ω) := by
  unfold dualLogSpaceXX; fun_prop

end Blocks

/-! ### The seeded factors are adapted -/

section Seed

variable {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ} {X : ℝ≥0 → Ω → ℝ} {d : Ω → SeedData n} {A : Set ℂ} {φ : ℂ → ℂ}
  {ζ₀ : ℝ} {G : Set Ω} {T : Ω → ℝ}

/-- **The conformal factors of the seeded density at a time `q` are `𝓕_q`-measurable on an `𝓕_q`-event `G`**:
`A_{j,k}`, `A_{k,0}`, the unnormalized `A_{k,1}`, `log F`, `B_{m,0}`, `B_{m,1}` and the driver. The data along the
path `ω` have the driver `X(·, ω)` (adapted, continuous), the deterministic frozen chart `φ` and tip `ζ₀`; on `G`,
`OwnData` holds up to a horizon `T ω ≥ q`, the tip is alive for the image chain up to `a(T)`, and the marks `V^m_q`
are adapted with clear discs. -/
theorem measurable_seed_parts (hXm : ∀ u, Measurable[𝓕 u] (X u)) (hXc : ∀ ω, Continuous (X · ω))
    (hdW : ∀ ω, (d ω).W = Ito.rpath (X · ω)) (hdφ : ∀ ω, (d ω).φ = φ) (hdζ : ∀ ω, (d ω).ζ₀ = ζ₀) (q : ℝ≥0)
    (hG : MeasurableSet[𝓕 q] G) (hqT : ∀ ω ∈ G, (q : ℝ) ≤ T ω)
    (h : ∀ ω ∈ G, OwnData (d ω).W A (d ω).φ (T ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω ∈ G, ∃ v₀ : ℝ → ℂ, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (T ω)) v₀)
    (hcl : ∀ ω ∈ G, ∀ m, ∃ ρ > 0, Disjoint (ball ((d ω).V m q : ℂ) ρ) (imgHull (d ω).W A q))
    (hVm : ∀ m, Measurable[𝓕 q] (G.indicator fun ω => (d ω).V m q)) :
    (∀ k, Measurable[𝓕 q] (G.indicator fun ω => (d ω).A k q)) ∧
    Measurable[𝓕 q] (G.indicator fun ω => (d ω).A20 q) ∧
    Measurable[𝓕 q] (G.indicator fun ω => frzImgD (d ω).W' (d ω).a (d ω).ζ₀ q) ∧
    Measurable[𝓕 q] (G.indicator fun ω => (d ω).L q) ∧
    (∀ m, Measurable[𝓕 q] (G.indicator fun ω => (d ω).B0 q m)) ∧
    (∀ m, Measurable[𝓕 q] (G.indicator fun ω => (d ω).B1 q m)) ∧
    Measurable[𝓕 q] (G.indicator fun ω => (d ω).W q) := by
  have hown : ∀ ω ∈ G, OwnData (d ω).W A φ (T ω) (d ω).a (d ω).W' := fun ω hω => by rw [← hdφ ω]; exact h ω hω
  have hFM : ∀ u ∈ Icc (0 : ℝ) q, @FrzMeas Ω (𝓕 q) (fun ω => (d ω).W) (fun ω => (d ω).W')
      (fun ω => (d ω).a) A φ T G u := fun u hu =>
    frzMeas_of_adaptedX hXm hXc hdW hG hown hu fun ω hω => ⟨hu.1, hu.2.trans (hqT ω hω)⟩
  have hM := hFM q ⟨q.coe_nonneg, le_rfl⟩
  have hv : ∀ ω ∈ G, ∃ v, IsForwardSol (d ω).W' (ζ₀ : ℂ) ((d ω).a (T ω)) v := fun ω hω => by
    rw [← hdζ ω]; exact hv₀ ω hω
  have eF : ∀ k (x : Ω → ℝ), (fun ω => (d ω).F k q (x ω)) =
      fun ω => (deriv^[k] (ownExt (d ω).W (d ω).W' (d ω).a φ q) (x ω)).re := fun k x =>
    funext fun ω => by simp only [SeedData.F, hdφ ω]
  refine ⟨fun k => ?_, ?_, ?_, ?_, fun m => ?_, fun m => ?_, ?_⟩
  · have e : (fun ω => (d ω).A k q) = fun ω => frzA (d ω).W (d ω).W' (d ω).a φ k q :=
      funext fun ω => by simp only [SeedData.A, hdφ ω]
    rw [e]
    exact @FrzMeas.measurable_frzA Ω (𝓕 q) _ _ _ _ _ _ _ _ hM k
  · have e : (fun ω => (d ω).A20 q) = fun ω => frzImg (d ω).W' (d ω).a ζ₀ q :=
      funext fun ω => by simp only [SeedData.A20, hdζ ω]
    rw [e]
    exact @FrzMeas.measurable_frzImg Ω (𝓕 q) _ _ _ _ _ _ _ _ hM ζ₀ hv
  · have e : (fun ω => frzImgD (d ω).W' (d ω).a (d ω).ζ₀ q) = fun ω => frzImgD (d ω).W' (d ω).a ζ₀ q :=
      funext fun ω => by simp only [hdζ ω]
    rw [e]
    exact @FrzMeas.measurable_frzImgD Ω (𝓕 q) _ _ _ _ _ _ _ _ hM ζ₀ hv
  · have e : (fun ω => (d ω).L q) = fun ω => frzLogF (d ω).W (d ω).W' (d ω).a φ q :=
      funext fun ω => by simp only [SeedData.L, hdφ ω]
    rw [e]
    exact @measurable_frzLogF Ω (𝓕 q) _ _ _ _ _ _ _ _ q.coe_nonneg hFM
  · have e : (fun ω => (d ω).B0 q m) = fun ω => (d ω).F 0 q ((d ω).V m q) := rfl
    rw [e, eF]
    exact @FrzMeas.measurable_F_at Ω (𝓕 q) _ _ _ _ _ _ _ _ hM 0 _ (hVm m) fun ω hω => hcl ω hω m
  · have e : (fun ω => (d ω).B1 q m) = fun ω => (d ω).F 1 q ((d ω).V m q) := rfl
    rw [e, eF]
    exact @FrzMeas.measurable_F_at Ω (𝓕 q) _ _ _ _ _ _ _ _ hM 1 _ (hVm m) fun ω hω => hcl ω hω m
  · exact Measurable.indicator (m := 𝓕 q) (@FrzMeas.drv Ω (𝓕 q) _ _ _ _ _ _ _ _ hM) hG

section Ell

variable (hXm : ∀ u, Measurable[𝓕 u] (X u)) (hXc : ∀ ω, Continuous (X · ω))
  (hdW : ∀ ω, (d ω).W = Ito.rpath (X · ω)) (hdφ : ∀ ω, (d ω).φ = φ) (hdζ : ∀ ω, (d ω).ζ₀ = ζ₀) (q : ℝ≥0)
  (hG : MeasurableSet[𝓕 q] G) (hqT : ∀ ω ∈ G, (q : ℝ) ≤ T ω)
  (h : ∀ ω ∈ G, OwnData (d ω).W A (d ω).φ (T ω) (d ω).a (d ω).W')
  (hv₀ : ∀ ω ∈ G, ∃ v₀ : ℝ → ℂ, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (T ω)) v₀)
  (hcl : ∀ ω ∈ G, ∀ m, ∃ ρ > 0, Disjoint (ball ((d ω).V m q : ℂ) ρ) (imgHull (d ω).W A q))
  (hVm : ∀ m, Measurable[𝓕 q] (G.indicator fun ω => (d ω).V m q))
  {κ : ℝ} {rr : Fin n → ℝ} (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
  (hV₀m : Measurable[𝓕 q] (G.indicator fun ω => (d ω).V₀ q))
include hXm hXc hdW hdφ hdζ hG hqT h hv₀ hcl hVm hdκ hdr hV₀m

/-- **`ℓ(q, W_q)` is `𝓕_q`-measurable on `G`** (the input `hm0` of `isDriftLogField_seed`). -/
theorem measurable_seed_ell (hG₀m : Measurable[𝓕 q] (G.indicator fun ω => (d ω).G₀ q)) :
    Measurable[𝓕 q] (G.indicator fun ω => (d ω).ell q ((d ω).W q)) := by
  obtain ⟨hA, hI0, hD0, hL, hB0, hB1, hW⟩ := measurable_seed_parts hXm hXc hdW hdφ hdζ q hG hqT h hv₀ hcl hVm
  have hmeas := ((measurable_dualLogTime κ rr (hD0.div hG₀m) hL hI0 hB0 hB1).add
    (measurable_dualLogSpace κ rr (hA 0) (hA 1) hI0 hB0)).sub
    ((measurable_dualLogTime κ rr (a21 := fun _ => 1) (l := fun _ => 0) (b1 := fun _ _ => 1) measurable_const
      measurable_const hV₀m hVm fun _ => measurable_const).add
      (measurable_dualLogSpace κ rr (f1 := fun _ => 1) hW measurable_const hV₀m hVm))
  convert Measurable.indicator (m := 𝓕 q) hmeas hG using 1
  funext ω
  by_cases hω : ω ∈ G
  · simp only [indicator_of_mem hω, Pi.add_apply, Pi.sub_apply, Pi.div_apply]
    simp only [SeedData.ell, SeedData.LT, SeedData.LS, SeedData.LT0, SeedData.LS0, SeedData.A21,
      hdκ ω, hdr ω]
    rfl
  · simp only [indicator_of_notMem hω]

/-- **`∂_xℓ(q, W_q)` is `𝓕_q`-measurable on `G`** (the input `hm1` of `isDriftLogField_seed`). -/
theorem measurable_seed_ellX :
    Measurable[𝓕 q] (G.indicator fun ω => (d ω).ellX q ((d ω).W q)) := by
  obtain ⟨hA, hI0, -, -, hB0, -, hW⟩ := measurable_seed_parts hXm hXc hdW hdφ hdζ q hG hqT h hv₀ hcl hVm
  have hmeas := (measurable_dualLogSpaceX κ rr (hA 0) (hA 1) (hA 2) hI0 hB0).sub
    (measurable_dualLogSpaceX κ rr (f1 := fun _ => 1) (f2 := fun _ => 0) hW measurable_const measurable_const hV₀m
      hVm)
  convert Measurable.indicator (m := 𝓕 q) hmeas hG using 1
  funext ω
  by_cases hω : ω ∈ G
  · simp only [indicator_of_mem hω, Pi.sub_apply]
    simp only [SeedData.ellX, hdκ ω, hdr ω]
    rfl
  · simp only [indicator_of_notMem hω]

/-- **`∂²_xℓ(q, W_q)` is `𝓕_q`-measurable on `G`** (the input `hm2` of `isDriftLogField_seed`). -/
theorem measurable_seed_ellXX :
    Measurable[𝓕 q] (G.indicator fun ω => (d ω).ellXX q ((d ω).W q)) := by
  obtain ⟨hA, hI0, -, -, hB0, -, hW⟩ := measurable_seed_parts hXm hXc hdW hdφ hdζ q hG hqT h hv₀ hcl hVm
  have hmeas := (measurable_dualLogSpaceXX κ rr (hA 0) (hA 1) (hA 2) (hA 3) hI0 hB0).sub
    (measurable_dualLogSpaceXX κ rr (f1 := fun _ => 1) (f2 := fun _ => 0) (f3 := fun _ => 0) hW measurable_const
      measurable_const measurable_const hV₀m hVm)
  convert Measurable.indicator (m := 𝓕 q) hmeas hG using 1
  funext ω
  by_cases hω : ω ∈ G
  · simp only [indicator_of_mem hω, Pi.sub_apply]
    simp only [SeedData.ellXX, hdκ ω, hdr ω]
    rfl
  · simp only [indicator_of_notMem hω]

end Ell

/-- `driftDriver σ B D ω` is the real path of the process `σ B + D`. -/
theorem driftDriver_eq_rpath (σ : ℝ) (B D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    driftDriver σ B D ω = Ito.rpath (fun u => σ * B u ω + D u ω) := rfl

/-- **The measurability inputs of the seeded density on an `𝓕_ε`-event `E`**, along the drifted driver
`W = √κ B + D`, from the adaptedness of `B`, of `D` and of the own-chart coordinates `V^m`, `V⁰`, `G⁰` (on
`E ∩ {q ≤ S}`), with the clear discs of the marks from `SeedConst` on `E`. With `E = univ` these are the inputs
`hm0`–`hm2` of `isDriftLogField_seed`. -/
theorem seed_meas_inputs_on {S : Ω → ℝ≥0} {E : Set Ω} {ε : ℝ≥0} {B D : ℝ≥0 → Ω → ℝ}
    (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω)) (hDm : ∀ u, Measurable[𝓕 u] (D u))
    (hDc : ∀ ω, Continuous (D · ω)) {κ : ℝ} {rr : Fin n → ℝ} (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω)
    (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr) (hdφ : ∀ ω, (d ω).φ = φ) (hdζ : ∀ ω, (d ω).ζ₀ = ζ₀)
    (hE : MeasurableSet[𝓕 ε] E) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (h : ∀ ω ∈ E, OwnData (d ω).W A (d ω).φ (S ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω ∈ E, ∃ v₀ : ℝ → ℂ, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (S ω)) v₀)
    {r a₀ γ Γ lam ρm : ℝ} (hc : ∀ ω ∈ E, (d ω).SeedConst A ε (S ω) r a₀ γ Γ lam ρm)
    (hVm : ∀ (q : ℝ≥0) m, ε ≤ q → Measurable[𝓕 q] ((E ∩ {ω | q ≤ S ω}).indicator fun ω => (d ω).V m q))
    (hV₀m : ∀ q : ℝ≥0, ε ≤ q → Measurable[𝓕 q] ((E ∩ {ω | q ≤ S ω}).indicator fun ω => (d ω).V₀ q))
    (hG₀m : ∀ q : ℝ≥0, ε ≤ q → Measurable[𝓕 q] ((E ∩ {ω | q ≤ S ω}).indicator fun ω => (d ω).G₀ q)) :
    (∀ q : ℝ≥0, ε ≤ q → Measurable[𝓕 q]
      ((E ∩ {ω | q ≤ S ω}).indicator fun ω => (d ω).ell q (driftDriver (Real.sqrt κ) B D ω q))) ∧
    (∀ q : ℝ≥0, ε ≤ q → Measurable[𝓕 q]
      ((E ∩ {ω | q ≤ S ω}).indicator fun ω => (d ω).ellX q (driftDriver (Real.sqrt κ) B D ω q))) ∧
    (∀ q : ℝ≥0, ε ≤ q → Measurable[𝓕 q]
      ((E ∩ {ω | q ≤ S ω}).indicator fun ω => (d ω).ellXX q (driftDriver (Real.sqrt κ) B D ω q))) := by
  set X : ℝ≥0 → Ω → ℝ := fun u ω => Real.sqrt κ * B u ω + D u ω with hX
  have hXm : ∀ u, Measurable[𝓕 u] (X u) := fun u => (measurable_const.mul (hBm u)).add (hDm u)
  have hXc : ∀ ω, Continuous (X · ω) := fun ω => (continuous_const.mul (hBc ω)).add (hDc ω)
  have hdW' : ∀ ω, (d ω).W = Ito.rpath (X · ω) := fun ω => (hdW ω).trans (driftDriver_eq_rpath _ B D ω)
  have hG : ∀ q : ℝ≥0, ε ≤ q → MeasurableSet[𝓕 q] (E ∩ {ω | q ≤ S ω}) := fun q hq =>
    (𝓕.mono hq _ hE).inter (measurableSet_ge_of_isStoppingTime hS q)
  have hqT : ∀ q : ℝ≥0, ∀ ω ∈ E ∩ {ω | q ≤ S ω}, (q : ℝ) ≤ S ω := fun q ω hω => NNReal.coe_le_coe.2 hω.2
  have hcl : ∀ q : ℝ≥0, ∀ ω ∈ E ∩ {ω | q ≤ S ω}, ∀ m, ∃ ρ > 0,
      Disjoint (ball ((d ω).V m q : ℂ) ρ) (imgHull (d ω).W A q) := fun q ω hω m =>
    ⟨ρm, (hc ω hω.1).m0, (hc ω hω.1).mclr m q ⟨q.coe_nonneg, NNReal.coe_le_coe.2 hω.2⟩⟩
  have hh : ∀ q : ℝ≥0, ∀ ω ∈ E ∩ {ω | q ≤ S ω}, OwnData (d ω).W A (d ω).φ (S ω) (d ω).a (d ω).W' :=
    fun q ω hω => h ω hω.1
  have hv : ∀ q : ℝ≥0, ∀ ω ∈ E ∩ {ω | q ≤ S ω}, ∃ v₀ : ℝ → ℂ,
      IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (S ω)) v₀ := fun q ω hω => hv₀ ω hω.1
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · have := measurable_seed_ell hXm hXc hdW' hdφ hdζ q (hG q hq) (hqT q) (hh q) (hv q) (hcl q) (hVm q · hq) hdκ
      hdr (hV₀m q hq) (hG₀m q hq)
    simp only [← hdW] at this ⊢
    exact this
  · have := measurable_seed_ellX hXm hXc hdW' hdφ hdζ q (hG q hq) (hqT q) (hh q) (hv q) (hcl q) (hVm q · hq) hdκ
      hdr (hV₀m q hq)
    simp only [← hdW] at this ⊢
    exact this
  · have := measurable_seed_ellXX hXm hXc hdW' hdφ hdζ q (hG q hq) (hqT q) (hh q) (hv q) (hcl q) (hVm q · hq) hdκ
      hdr (hV₀m q hq)
    simp only [← hdW] at this ⊢
    exact this

end Seed

/-- **The seeded density is a martingale after `ε`, with its measurability inputs discharged**: A20's
`integral_mul_seed_stopped_sub_eq_zero` for a deterministic frozen hull `A` (chart `φ`, tip `ζ₀`), whose hypotheses
`hm0`–`hm2` are replaced by the adaptedness of the drift `D` and of the own-chart coordinates `V^m`, `V⁰`, `G⁰`
(`seed_meas_inputs_on` with `E = univ`). -/
theorem integral_mul_seed_stopped_sub_eq_zero_of_adapted (𝓕 : Filtration ℝ≥0 mΩ) {P : Measure Ω} {κ : ℝ}
    (hκ : 0 < κ) {n : ℕ} (rr : Fin n → ℝ) (B D : ℝ≥0 → Ω → ℝ) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hDm : ∀ u, Measurable[𝓕 u] (D u)) (hDc : ∀ ω, Continuous (D · ω))
    (ε : ℝ≥0) (S : Ω → ℝ≥0) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (d : Ω → SeedData n)
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω) (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    {A : Set ℂ} {φ : ℂ → ℂ} {ζ₀ : ℝ} (hdφ : ∀ ω, (d ω).φ = φ) (hdζ : ∀ ω, (d ω).ζ₀ = ζ₀)
    {r a₀ γ Γ lam ρm L Tm : ℝ} (hεS : ∀ ω, ε ≤ S ω) (hSTm : ∀ ω, (S ω : ℝ) ≤ Tm)
    (h : ∀ ω, OwnData (d ω).W A (d ω).φ (S ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω, ∃ v₀ : ℝ → ℂ, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (S ω)) v₀)
    (hc : ∀ ω, (d ω).SeedConst A ε (S ω) r a₀ γ Γ lam ρm) (hL : SeedScaleOK r a₀ γ Γ lam Tm L)
    (hV₀ : ∀ ω, ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt (d ω).V₀ (2 / ((d ω).V₀ t - (d ω).W t)) (Icc (ε : ℝ) (S ω)) t)
    (hG₀ : ∀ ω, ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt (d ω).G₀ (-2 * (d ω).G₀ t / ((d ω).V₀ t - (d ω).W t) ^ 2) (Icc (ε : ℝ) (S ω)) t)
    (hV : ∀ ω m, ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt ((d ω).V m) (2 / ((d ω).V m t - (d ω).W t)) (Icc (ε : ℝ) (S ω)) t)
    (hVc : ∀ ω m, ContinuousOn ((d ω).V m) (Icc 0 (S ω)))
    (hD : ∀ ω, ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt (fun s : ℝ => D s.toNNReal ω) ((d ω).drift t) (Icc (ε : ℝ) (S ω)) t)
    (hVm : ∀ (q : ℝ≥0) m, Measurable[𝓕 q] ({ω | q ≤ S ω}.indicator fun ω => (d ω).V m q))
    (hV₀m : ∀ q : ℝ≥0, Measurable[𝓕 q] ({ω | q ≤ S ω}.indicator fun ω => (d ω).V₀ q))
    (hG₀m : ∀ q : ℝ≥0, Measurable[𝓕 q] ({ω | q ≤ S ω}.indicator fun ω => (d ω).G₀ q))
    {s t : ℝ≥0} (hεs : ε ≤ s) (hst : s ≤ t) {ξ : Ω → ℝ} (hξ : Measurable[𝓕 s] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, ξ ω * (Real.exp ((d ω).ell (min t (S ω)) (driftDriver (Real.sqrt κ) B D ω (min t (S ω))))
      - Real.exp ((d ω).ell (min s (S ω)) (driftDriver (Real.sqrt κ) B D ω (min s (S ω))))) ∂P = 0 := by
  have eE : ∀ q : ℝ≥0, univ ∩ {ω | q ≤ S ω} = {ω | q ≤ S ω} := fun q => univ_inter _
  obtain ⟨hm0, hm1, hm2⟩ := seed_meas_inputs_on (E := univ) (ε := ε) (fun u => hB.2.1 u) hBc hDm hDc hdW hdκ hdr
    hdφ hdζ MeasurableSet.univ hS (fun ω _ => h ω) (fun ω _ => hv₀ ω) (fun ω _ => hc ω)
    (fun q m _ => by rw [eE]; exact hVm q m) (fun q _ => by rw [eE]; exact hV₀m q)
    (fun q _ => by rw [eE]; exact hG₀m q)
  simp only [eE] at hm0 hm1 hm2
  exact integral_mul_seed_stopped_sub_eq_zero 𝓕 hκ rr B D hB hBc ε S hS d hdW hdκ hdr (A := fun _ => A) hεS hSTm h
    hv₀ hc hL hV₀ hG₀ hV hVc hD hm0 hm1 hm2 hεs hst hξ hξb

end InteractingSLE.ZhanGT4
