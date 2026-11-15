/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FzData
import InteractingSLE.Spec.Supplement.SB2KqDrv

/-!
# SB2(1)'s late (S) line mean, part 17: FIN's literal driver and hull

Packet PROVE-T14-SB2DRV (round 12). FIN's hull is the literal Loewner hull `fwdHull (w ω) (t ω)` of a driver that is
continuous at EVERY sample (`hunbK`, the configuration). It is built from

* **`exists_eqOn_cfgDriver`**: the configuration's exploration driver (a global continuous driver whose trace is the
  coupling's generating trace up to some `t₂ > t`) is the coupling driver on some `[0, t₂']`, `t₂' > t`
  (`eqOn_driver_of_trace`);
* **`exists_finDriver`**: a driver that is the configuration's driver on the configuration event, a clamped coupling
  driver (continuous, same hull at `τ`) on the rest of a set `G` where `τ < ζ` and the coupling driver is continuous
  below `ζ`, and `0` off both.

Deterministic; no source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.SB.Lv

/-- **The configuration's exploration driver is the coupling driver past the line time.** -/
theorem exists_eqOn_cfgDriver {w : ℝ → ℝ} {ηw : ℝ → ℂ} (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w ηw) {W : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hWc : ContinuousOn W {t | (t : ℝ≥0∞) < ζ'}) (hW0 : W 0 = 0) (htr : IsGeneratingTrace W ζ' γ) {t : ℝ≥0}
    (htζ : (t : ℝ≥0∞) < ζ') (hagree : ∃ t₂ : ℝ, (t : ℝ) < t₂ ∧ ∀ r : ℝ, 0 ≤ r → r < t₂ → ηw r = γ r.toNNReal) :
    ∃ t₂ : ℝ, (t : ℝ) < t₂ ∧ EqOn w (fun r : ℝ => W r.toNNReal) (Icc 0 t₂) := by
  obtain ⟨c, htc, hc⟩ := hagree
  have hc0 : 0 < c := lt_of_le_of_lt t.coe_nonneg htc
  have htc' : (t : ℝ≥0∞) < ENNReal.ofReal c := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff hc0).2 htc
  obtain ⟨b', htb, hb⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min htζ htc')
  have htb' : t < b' := by exact_mod_cast htb
  obtain ⟨a, hta, hab⟩ := exists_between htb'
  have hbζ : (b' : ℝ≥0∞) < ζ' := lt_of_lt_of_le hb (min_le_left _ _)
  have hbc : (b' : ℝ) < c := by
    have h1 := lt_of_lt_of_le hb (min_le_right _ _)
    rw [← ENNReal.ofReal_coe_nnreal] at h1
    exact (ENNReal.ofReal_lt_ofReal_iff hc0).1 h1
  have hab' : (a : ℝ) < b' := by exact_mod_cast hab
  refine ⟨a, by exact_mod_cast hta, ?_⟩
  exact eqOn_driver_of_trace hw hw0 hη hWc hW0 htr hab hbζ fun r hr0 hra =>
    hc r hr0 (lt_of_le_of_lt hra (hab'.trans hbc))

/-- **FIN's literal driver**: the configuration's driver on the configuration event, a continuous driver with the
coupling hull at `τ` on the rest of `G`, `0` elsewhere. -/
theorem exists_finDriver {Ω : Type*} {G : Set Ω} (C : Ω → Prop) (wC : Ω → ℝ → ℝ) {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {τ' : Ω → ℝ≥0}
    (hG : ∀ ω ∈ G, (τ' ω : ℝ≥0∞) < ζ ω ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω}) :
    ∃ w : Ω → ℝ → ℝ, (∀ ω, C ω → w ω = wC ω) ∧
      (∀ ω ∈ G, ¬ C ω → Continuous (w ω) ∧ w ω 0 = W 0 ω ∧
        fwdHull (w ω) (τ' ω) = fwdHull (fun r : ℝ => W r.toNNReal ω) (τ' ω)) ∧
      (∀ ω, ω ∉ G → ¬ C ω → w ω = 0) := by
  classical
  have hT : ∀ ω ∈ G, ∃ T : ℝ≥0, τ' ω < T ∧ (T : ℝ≥0∞) < ζ ω := fun ω hω => by
    obtain ⟨T, h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (hG ω hω).1
    exact ⟨T, by exact_mod_cast h1, h2⟩
  refine ⟨fun ω => if C ω then wC ω else
      if hω : ω ∈ G then Ito.clampDrv (fun r : ℝ => W r.toNNReal ω) ((hT ω hω).choose : ℝ) else 0,
    fun ω hC => ite_eq_left hC, fun ω hω hC => ?_, fun ω hω hC => ?_⟩
  · obtain ⟨h1, h2⟩ := (hT ω hω).choose_spec
    beta_reduce
    rw [ite_eq_right hC, dite_eq_left hω]
    set T := (hT ω hω).choose
    have hcont : ContinuousOn (fun r : ℝ => W r.toNNReal ω) (Icc 0 (T : ℝ)) := by
      refine (hG ω hω).2.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
      show ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω
      refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) h2
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
      exact hr.2
    refine ⟨Ito.continuous_clampDrv T.coe_nonneg hcont, ?_, ?_⟩
    · simp only [Ito.clampDrv, max_self, min_eq_left T.coe_nonneg, Real.toNNReal_zero]
    · exact LocalExt.fwdHull_congr_of_eqOn_of_lt (τ' ω).coe_nonneg (by exact_mod_cast h1) Ito.clampDrv_eqOn
  · show (if C ω then wC ω else _) = 0
    rw [ite_eq_right hC, dite_eq_right hω]

end InteractingSLE.Theorem14.SB.Lv
