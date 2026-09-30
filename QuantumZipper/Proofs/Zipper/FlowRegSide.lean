import QuantumZipper.Proofs.Zipper.F1Side3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.3, F1/F2 flow regularity: existence of the side limits for every continuous driver

The side-limit clauses of the flow regularity bundles (`F1.CfgFlowRegStmt`, `F1.FlowScaleReg`,
`F1.CanonReg`) ask only that the one-sided limits of `x ↦ (fwdMap W t x).re` at `0` *exist*.
This holds **deterministically** for every continuous driver with `W 0 = 0` and every `t ≥ 0`:

* if every `x < 0` is alive at time `t`, the map is strictly increasing on `(−∞,0)`
  (`F1.isForwardSol_lt_of_lt`) and bounded above by `0` (a real solution started left of the
  driver stays left of it, `re_pos_isForwardSol_real` after the reflection `RS.isForwardSol_neg`),
  so it converges (`F1.tendsto_nhdsLT_of_monotoneOn`);
* otherwise some `x₀ < 0` is swallowed by time `t`; then every `x ∈ (x₀,0)` is swallowed too
  (monotonicity of aliveness, `RS.exists_isForwardSol_of_lt`, Kemppainen, *Schramm–Loewner
  Evolution* (2017), p. 80), so `fwdMap W t x = 0` (junk value) on `(x₀,0)` and the limit is `0`.

The right side is symmetric. For `κ < 4` the second case never occurs (Rohde–Schramm,
*Basic properties of SLE*, Ann. Math. 161 (2005), Lemma 6.2; `RS.ae_real_alive` for the unshifted
driver), so the limits are the genuine side images; *existence* needs no probability.
Own elementary argument (case split around the cited monotonicity).

Main results: `exists_tendsto_fwdMap_left`, `exists_tendsto_fwdMap_right`,
`zipCapDown_side_limits` (all `u, s ≥ 0` at once for `zipCapDown γ u c`, `c.2` continuous).
-/

noncomputable section

open Complex Filter MeasureTheory Set ProbabilityTheory
open scoped Topology NNReal

namespace QuantumZipper
namespace F1

private lemma neg_cast_real (x : ℝ) : -((x : ℂ)) = ((-x : ℝ) : ℂ) := by push_cast; ring

/-- Reflection of a forward solution, with the driver written as `-W`. -/
private lemma isForwardSol_neg_real {W : ℝ → ℝ} {x T : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W (x : ℂ) T u) :
    IsForwardSol (-W) ((-x : ℝ) : ℂ) T (fun t => -u t) := by
  have h := RS.isForwardSol_neg hu
  rwa [neg_cast_real] at h

/-- **Left side limit, deterministic.** -/
theorem exists_tendsto_fwdMap_left {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) :
    ∃ l, Tendsto (fun x : ℝ => (fwdMap W t x).re) (𝓝[<] (0 : ℝ)) (𝓝 l) := by
  set g : ℝ → ℝ := fun x => (fwdMap W t x).re with hg
  by_cases hall : ∀ x : ℝ, x < 0 → ∃ u, IsForwardSol W (x : ℂ) t u
  · have hval : ∀ x : ℝ, x < 0 → ∃ u, IsForwardSol W (x : ℂ) t u ∧ g x = (u t).re := by
      intro x hx
      obtain ⟨u, hu⟩ := hall x hx
      exact ⟨u, hu, by simp only [hg]; rw [fwdMap_eq_of_isForwardSol hu ⟨ht, le_rfl⟩]⟩
    refine ⟨_, tendsto_nhdsLT_of_monotoneOn (B := 0) (fun x hx y hy hxy => ?_) (fun x hx => ?_)⟩
    · rcases lt_or_eq_of_le hxy with hlt | heq
      · obtain ⟨u₁, hu₁, hg₁⟩ := hval x hx
        obtain ⟨u₂, hu₂, hg₂⟩ := hval y hy
        rw [hg₁, hg₂]
        exact (isForwardSol_lt_of_lt ht hlt hu₁ hu₂ t ⟨ht, le_rfl⟩).le
      · rw [heq]
    · obtain ⟨u, hu, hgx⟩ := hval x hx
      have h := re_pos_isForwardSol_real hW.neg ht (isForwardSol_neg_real hu)
        (by rw [Pi.neg_apply, hW0, neg_zero]; linarith [mem_Iio.1 hx]) t ⟨ht, le_rfl⟩
      rw [hgx]
      simp only [neg_re] at h
      linarith
  · push Not at hall
    obtain ⟨x₀, hx₀, hdead⟩ := hall
    refine ⟨0, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT hx₀] with x hx
    have hnot : ¬ ∃ u, IsForwardSol W (x : ℂ) t u := by
      rintro ⟨u, hu⟩
      obtain ⟨v, hv⟩ := RS.exists_isForwardSol_of_lt hW.neg ht
        (by rw [Pi.neg_apply, hW0, neg_zero]; linarith [hx.2]) (neg_lt_neg hx.1) (isForwardSol_neg_real hu)
      have h := isForwardSol_neg_real hv
      rw [neg_neg, neg_neg] at h
      exact hdead _ h
    simp only [hg, fwdMap, dif_neg hnot, zero_re]

/-- **Right side limit, deterministic.** -/
theorem exists_tendsto_fwdMap_right {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) :
    ∃ l, Tendsto (fun x : ℝ => (fwdMap W t x).re) (𝓝[>] (0 : ℝ)) (𝓝 l) := by
  set g : ℝ → ℝ := fun x => (fwdMap W t x).re with hg
  by_cases hall : ∀ x : ℝ, 0 < x → ∃ u, IsForwardSol W (x : ℂ) t u
  · have hval : ∀ x : ℝ, 0 < x → ∃ u, IsForwardSol W (x : ℂ) t u ∧ g x = (u t).re := by
      intro x hx
      obtain ⟨u, hu⟩ := hall x hx
      exact ⟨u, hu, by simp only [hg]; rw [fwdMap_eq_of_isForwardSol hu ⟨ht, le_rfl⟩]⟩
    refine ⟨_, tendsto_nhdsGT_of_monotoneOn (B := 0) (fun x hx y hy hxy => ?_) (fun x hx => ?_)⟩
    · rcases lt_or_eq_of_le hxy with hlt | heq
      · obtain ⟨u₁, hu₁, hg₁⟩ := hval x hx
        obtain ⟨u₂, hu₂, hg₂⟩ := hval y hy
        rw [hg₁, hg₂]
        exact (isForwardSol_lt_of_lt ht hlt hu₁ hu₂ t ⟨ht, le_rfl⟩).le
      · rw [heq]
    · obtain ⟨u, hu, hgx⟩ := hval x hx
      have h := re_pos_isForwardSol_real hW ht hu (by rw [hW0]; exact hx) t ⟨ht, le_rfl⟩
      rw [hgx]; exact h.le
  · push Not at hall
    obtain ⟨x₀, hx₀, hdead⟩ := hall
    refine ⟨0, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hx₀] with x hx
    have hnot : ¬ ∃ u, IsForwardSol W (x : ℂ) t u := by
      rintro ⟨u, hu⟩
      obtain ⟨v, hv⟩ := RS.exists_isForwardSol_of_lt hW ht (by rw [hW0]; exact hx.1) hx.2 hu
      exact hdead _ hv
    simp only [hg, fwdMap, dif_neg hnot, zero_re]

/-- **Both side limits along the whole capacity flow**, deterministically: for a configuration
with continuous driver, for all `u` and all `s ≥ 0` both one-sided limits of the driver of
`zipCapDown γ u c` exist at time `s`. -/
theorem zipCapDown_side_limits {γ : ℝ} {c : FieldSample × (ℝ → ℝ)} (hW : Continuous c.2)
    (u : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    (∃ l, Tendsto (fun r : ℝ => (fwdMap (zipCapDown γ u c).2 s r).re) (𝓝[<] (0 : ℝ)) (𝓝 l)) ∧
    (∃ l, Tendsto (fun r : ℝ => (fwdMap (zipCapDown γ u c).2 s r).re) (𝓝[>] (0 : ℝ)) (𝓝 l)) := by
  have hc : Continuous (zipCapDown γ u c).2 :=
    (hW.comp (continuous_const.add (continuous_id.max continuous_const))).sub continuous_const
  have h0 : (zipCapDown γ u c).2 0 = 0 := by simp [zipCapDown]
  exact ⟨exists_tendsto_fwdMap_left hc h0 hs, exists_tendsto_fwdMap_right hc h0 hs⟩

end F1
end QuantumZipper
