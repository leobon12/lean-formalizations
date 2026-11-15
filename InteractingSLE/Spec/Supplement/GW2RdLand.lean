/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdVer
import InteractingSLE.Foundations.Loewner.RealPoints
import InteractingSLE.Foundations.Loewner.FiniteEndpoint

/-!
# GW2's lifetime as a hitting time, part 1: a real landing swallows the real points inside it

Packet PROVE-GW2-RELDET (`FlowLifetimeHitStatement`, step (a)). Deterministic Loewner facts for a continuous driver
`U` with `U 0 = 0`:

* **`tip_ne_of_isForwardSol_real`**: a real point that is alive at time `s` (its centred forward flow exists on
  `[0, s]`) is not the tip at `s` — the forward map tends to the nonzero flow value at the point
  (`tendsto_fwdMap_of_isForwardSol_real`) and to `0` along the inverse map at the tip;
* `exists_isForwardSol_of_lt_neg`: on the left side, a real point alive at `s` keeps every point further left alive
  (the reflection of QuantumZipper's `RS.exists_isForwardSol_of_lt`);
* **`not_alive_of_tip_eq_pos`**, **`not_alive_of_tip_eq_neg`**: if the tip lands on the real line at
  `y` at time `t`, every real point between `0` and `y` (included) is swallowed by time `t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv IsForwardSol)

namespace InteractingSLE.Theorem14.GW2Rd

/-- **A real point alive at time `s` is not the tip at `s`.** -/
theorem tip_ne_of_isForwardSol_real {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    {p : ℂ} (htip : Tendsto (fwdMapInv U s) (𝓝[H] 0) (𝓝 p)) {x : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol U x s u) :
    p ≠ x := by
  intro hpx
  subst hpx
  have h1 : Tendsto (fwdMap U s) (𝓝[H] ((x : ℂ))) (𝓝 (u s)) :=
    tendsto_fwdMap_of_isForwardSol_real hU hU0 hs hu
  have h2 : Tendsto (fwdMapInv U s) (𝓝[H] 0) (𝓝[H] ((x : ℂ))) :=
    tendsto_nhdsWithin_iff.2 ⟨htip, eventually_nhdsWithin_of_forall fun w hw =>
      QuantumZipper.RS.fwdMapInv_mem_H hU hU0 hs hw⟩
  have h3 : Tendsto (fun w => fwdMap U s (fwdMapInv U s w)) (𝓝[H] 0) (𝓝 (u s)) := h1.comp h2
  have h4 : Tendsto (fun w => fwdMap U s (fwdMapInv U s w)) (𝓝[H] 0) (𝓝 0) := by
    refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (QuantumZipper.RS.fwdMap_fwdMapInv hU hU0 hs hw).symm
  have : (𝓝[H] (0 : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  exact (hu.2 s ⟨hs, le_rfl⟩).1 (tendsto_nhds_unique h3 h4)

/-- **Left monotonicity of real survival**: if `q < 0` is alive on `[0, T]`, so is every `y < q`. -/
theorem exists_isForwardSol_of_lt_neg {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {q y : ℝ} (hq : q < 0) (hyq : y < q) {u : ℝ → ℂ} (hu : IsForwardSol U q T u) :
    ∃ v, IsForwardSol U y T v := by
  have hneg := QuantumZipper.RS.isForwardSol_neg hu
  have hneg' : IsForwardSol (fun t => -U t) ((-q : ℝ) : ℂ) T (fun t => -u t) := by
    simpa only [Complex.ofReal_neg] using hneg
  obtain ⟨v, hv⟩ := QuantumZipper.RS.exists_isForwardSol_of_lt (W := fun t => -U t) hU.neg hT
    (q := -q) (y := -y) (by simp only [hU0, neg_zero]; linarith) (by linarith) hneg'
  have hback := QuantumZipper.RS.isForwardSol_neg hv
  refine ⟨fun t => -v t, ?_⟩
  simpa only [neg_neg, Complex.ofReal_neg] using hback

/-- **A right real landing swallows the real points inside it**: if the tip at `s` is the real point `y > 0`, no
real point of `(0, y]` is alive at `s`. -/
theorem not_alive_of_tip_eq_pos {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s) {y : ℝ}
    (htip : Tendsto (fwdMapInv U s) (𝓝[H] 0) (𝓝 (y : ℂ))) {x : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ¬ ∃ u, IsForwardSol U x s u := by
  rintro ⟨u, hu⟩
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact tip_ne_of_isForwardSol_real hU hU0 hs htip hu rfl
  · obtain ⟨v, hv⟩ := QuantumZipper.RS.exists_isForwardSol_of_lt hU hs (by rw [hU0]; exact hx) hlt hu
    exact tip_ne_of_isForwardSol_real hU hU0 hs htip hv rfl

/-- **A left real landing swallows the real points inside it**: if the tip at `s` is the real point `y < 0`, no
real point of `[y, 0)` is alive at `s`. -/
theorem not_alive_of_tip_eq_neg {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s) {y : ℝ}
    (htip : Tendsto (fwdMapInv U s) (𝓝[H] 0) (𝓝 (y : ℂ))) {x : ℝ} (hx : x < 0) (hyx : y ≤ x) :
    ¬ ∃ u, IsForwardSol U x s u := by
  rintro ⟨u, hu⟩
  rcases eq_or_lt_of_le hyx with rfl | hlt
  · exact tip_ne_of_isForwardSol_real hU hU0 hs htip hu rfl
  · obtain ⟨v, hv⟩ := exists_isForwardSol_of_lt_neg hU hU0 hs hx hlt hu
    exact tip_ne_of_isForwardSol_real hU hU0 hs htip hv rfl

end InteractingSLE.Theorem14.GW2Rd
