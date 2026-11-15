/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb2Join
import InteractingSLE.Spec.Sec7.CounterflowProb2Hull
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Spec.Sec5.TimeDensity
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane
import InteractingSLE.Spec.Zhan.ConstDriftTraceRs

/-!
# The image endpoint, part 1: a trace up to a positive time from the traces after every earlier positive time

Packet PROVE-A2-IMGEND. Source: Astra, *Follow-up 5* §1.2 L180–L184 (`source/external/AstraIG1/ig1_followup5.txt`,
R73): "For source-coincident lower marks, restart at a positive rational own time before the lifetime … Positive
rational times cover every positive-lifetime entrance realization." A local evolution of a word with marks at the
source is only known through its restarts at positive times, where the word is separated. This file is the
deterministic step that recovers the trace from time `0` (no probability):

* `mem_fwdHull_add_iff`: `F_q(w) ∈ K_{q+u}` iff `w ∈ K'_u` (`w ∈ ℍ`, `K'` the hulls of the shifted driver);
* **`isGeneratingTraceIcc_of_restarts`**: let `w` be continuous before `T`, `w 0 = 0`, `0 < q₀ < T`, and suppose that
  for a dense set of positive times `q < q₀` the shifted driver `w(q + ·) − w(q)` has a simple generating trace
  `η_q` on the closed interval `[0, q₀ − q]` lying in `ℍ` at positive times. Then the measurable trace evaluation
  `t ↦ LP.traceAt t w` is a generating trace of `w` on the closed interval `[0, q₀]` (with its tip at `q₀`), simple
  and in `ℍ` at positive times.

The proof: at a time `t > q`, `γ(t) = F_q(η_q(t − q))` (`trace_add_of_tendsto_shift`), which gives continuity,
injectivity and `γ(t) ∈ K_t` away from `0`; continuity at `0` is the shrinking of the hulls
(`Sec5.exists_fwdHull_subset_ball`). For the hulls, `ℍ \ K_t` is preconnected, unbounded and misses `γ[0, t]`, so it
lies in the unbounded domain of `γ[0, t]`; conversely a point of the unbounded domain is joined to `∞` by a path
avoiding `γ[0, t]`, hence at positive distance from `0`, hence outside `K_q` for a small `q`; its image under `f_q`
is joined to `∞` avoiding `η_q[0, t − q]`, so it is outside `K'_{t−q}`, and the point is outside `K_t`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A2ImgEnd

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv trace)
open QuantumZipper.RS (shiftDrive)
open Sec7 (IsGeneratingTraceIcc shiftNN)

/-! ### Composition of hulls and traces (continuous drivers on `ℝ`) -/

section Real

variable {W : ℝ → ℝ}

/-- **Hull composition, pointwise.** For `w ∈ ℍ`, `F_q(w) ∈ K_{q+u}` iff `w ∈ K'_u`, where `K'` are the hulls of the
shifted driver `W(q + ·) − W(q)`. -/
theorem mem_fwdHull_add_iff (hW : Continuous W) (hW0 : W 0 = 0) {q u : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ u)
    {w : ℂ} (hw : w ∈ H) :
    fwdMapInv W q w ∈ fwdHull W (q + u) ↔ w ∈ fwdHull (shiftDrive W q) u := by
  have hV : Continuous (shiftDrive W q) := QuantumZipper.RS.continuous_shiftDrive hW q
  have hV0 : shiftDrive W q 0 = 0 := by simp [shiftDrive]
  have hinj : InjOn (fwdMapInv W q) H := (isConformalBijection_fwdMapInv hW hW0 hq).2.injOn
  have hFw : fwdMapInv W q w ∈ H := QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hq hw
  have key : fwdMapInv W q w ∈ H \ fwdHull W (q + u) ↔ w ∈ H \ fwdHull (shiftDrive W q) u := by
    rw [← QuantumZipper.RS.image_fwdMapInv_H hW hW0 (add_nonneg hq hu),
      ← QuantumZipper.RS.image_fwdMapInv_H hV hV0 hu]
    constructor
    · rintro ⟨v, hv, hve⟩
      rw [QuantumZipper.RS.fwdMapInv_add_shift hW hW0 hq hu hv] at hve
      exact ⟨v, hv, hinj (QuantumZipper.RS.fwdMapInv_mem_H hV hV0 hu hv) hw hve⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, QuantumZipper.RS.fwdMapInv_add_shift hW hW0 hq hu hv⟩
  constructor
  · intro h
    by_contra hn
    exact (key.2 ⟨hw, hn⟩).2 h
  · intro h
    by_contra hn
    exact (key.1 ⟨hFw, hn⟩).2 h

/-- **The trace after a restart.** If the centred inverse maps of the shifted driver converge at `0` (within `ℍ`) to
`p ∈ ℍ` at time `u`, then the trace of `W` at `q + u` is `F_q(p)`. -/
theorem trace_add_eq (hW : Continuous W) (hW0 : W 0 = 0) {q u : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ u) {p : ℂ}
    (hp : p ∈ H) (hlim : Tendsto (fwdMapInv (shiftDrive W q) u) (𝓝[H] 0) (𝓝 p)) :
    trace W (q + u) = fwdMapInv W q p := by
  have hrad : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝[H] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝 0) (𝓝 ((0 : ℝ) * Complex.I)) :=
        ((Complex.continuous_ofReal.mul continuous_const).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact QuantumZipper.RS.mul_I_mem_H hy
  exact (QuantumZipper.RS.trace_add_of_tendsto_shift hW hW0 hq hu hp (hlim.comp hrad)).2.2


/-- A large point `M i` lies outside the hull `K_t` of a continuous driver. -/
theorem exists_big_notMem_fwdHull (hW : Continuous W) {t : ℝ} (ht : 0 < t) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → z ∉ fwdHull W t := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 t))
  have hK := QuantumZipper.CaraR.fwdHull_subset_closedBall hW ht (M := M) fun r hr => by
    simpa [Real.norm_eq_abs] using hM r hr
  refine ⟨|M + 3 * Real.sqrt t| + 1, by positivity, fun z hz hzK => ?_⟩
  have h1 := mem_closedBall_zero_iff.1 (hK hzK)
  linarith [le_abs_self (M + 3 * Real.sqrt t)]

/-- The complement of a hull in `ℍ` is unbounded. -/
theorem not_isBounded_H_diff_fwdHull (hW : Continuous W) {t : ℝ} (ht : 0 < t) :
    ¬ Bornology.IsBounded (H \ fwdHull W t) := by
  intro hb
  obtain ⟨R, hR, hRK⟩ := exists_big_notMem_fwdHull hW ht
  obtain ⟨r, hr⟩ := hb.subset_closedBall 0
  set M : ℝ := max R r + 1 with hMdef
  have hM0 : 0 < M := by positivity
  have hmem : ((M : ℂ) * I) ∈ H \ fwdHull W t := by
    refine ⟨show 0 < ((M : ℂ) * I).im by simpa using hM0, hRK _ ?_⟩
    rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos hM0]
    linarith [le_max_left R r]
  have h1 := mem_closedBall_zero_iff.1 (hr hmem)
  rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos hM0] at h1
  linarith [le_max_right R r]

/-- **The hull at a positive time from the restarts.** Let `γ` be continuous on `[0, t]` with `γ 0 = 0` and
`γ(s) ∈ K_s` for `0 < s ≤ t`, and suppose that for every `δ > 0` there is a time `q ∈ (0, t)` with `K_q ⊆ B(0, δ)`
and a curve `η₁` (`η₁ 0 = 0`) whose filling is the hull `K'_{t−q}` of the shifted driver, with `γ(q + u) = F_q(η₁ u)`
for `0 < u ≤ t − q`. Then `K_t = fill(γ[0, t])`. -/
theorem fwdHull_eq_fillH_of_restarts (hW : Continuous W) (hW0 : W 0 = 0) {γ : ℝ≥0 → ℂ} {t : ℝ≥0}
    (ht : 0 < t) (hγc : ContinuousOn γ (Icc 0 t)) (hγ0 : γ 0 = 0)
    (hγK : ∀ s : ℝ≥0, 0 < s → s ≤ t → γ s ∈ fwdHull W s)
    (hrest : ∀ δ : ℝ, 0 < δ → ∃ q : ℝ≥0, 0 < q ∧ q < t ∧ fwdHull W q ⊆ ball 0 δ ∧ ∃ η₁ : ℝ≥0 → ℂ,
      η₁ 0 = 0 ∧ IsCompact (η₁ '' Icc 0 (t - q)) ∧
      fwdHull (shiftDrive W q) ((t - q : ℝ≥0) : ℝ) = fillH (η₁ '' Icc 0 (t - q)) ∧
      ∀ u : ℝ≥0, 0 < u → u ≤ t - q → γ (q + u) = fwdMapInv W q (η₁ u)) :
    fwdHull W t = fillH (γ '' Icc 0 t) := by
  set C : Set ℂ := γ '' Icc 0 t with hCdef
  have hCc : IsCompact C := isCompact_Icc.image_of_continuousOn hγc
  have hCcl := hCc.isClosed
  have hCb := hCc.isBounded
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hCH : ∀ z ∈ C, z ∈ H → z ∈ fwdHull W t := by
    rintro _ ⟨s, hs, rfl⟩ hzH
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, hγ0] at hzH; exact absurd hzH (by simp [QuantumZipper.H])
    · exact (QuantumZipper.fwdHull_mono).1 (by exact_mod_cast hs.2) (hγK s h0 hs.2)
  -- (a) the hull complement lies in the unbounded domain of `C`
  have ha : H \ fwdHull W t ⊆ H \ fillH C :=
    HalfPlaneSep.subset_H_diff_fillH_of_not_isBounded hCcl
      (QuantumZipper.RS.isPreconnected_compl_fwdHull hW hW0 ht0.le) (not_isBounded_H_diff_fwdHull hW ht0)
      fun z hz => ⟨hz.1, fun hzC => hz.2 (hCH z hzC hz.1)⟩
  -- (b) the unbounded domain of `C` lies in the hull complement
  have hb : H \ fillH C ⊆ H \ fwdHull W t := by
    intro z hz
    obtain ⟨R, hR, hCR, hEq⟩ := HalfPlaneSep.exists_H_diff_fillH_eq hCcl hCb
    obtain ⟨RK, hRK, hRKK⟩ := exists_big_notMem_fwdHull hW ht0
    set M : ℝ := max R RK + 1 with hMdef
    have hM0 : 0 < M := by positivity
    set Z : ℂ := (M : ℂ) * I with hZdef
    have hZn : ‖Z‖ = M := by
      rw [hZdef, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos hM0]
    have hZH : Z ∈ H := show 0 < Z.im by simpa [hZdef] using hM0
    have hZU : Z ∈ H \ fillH C :=
      HalfPlaneSep.mem_H_diff_fillH_of_le_norm hCcl hR hCR hZH (by rw [hZn]; linarith [le_max_left R RK])
    have hZK : Z ∉ fwdHull W t := hRKK Z (by rw [hZn]; linarith [le_max_right R RK])
    have hUo : IsOpen (H \ fillH C) := by
      rw [hEq]; exact (QuantumZipper.isOpen_H.sdiff hCcl).connectedComponentIn
    have hUc : IsConnected (H \ fillH C) := ⟨⟨z, hz⟩, HalfPlaneSep.isPreconnected_H_diff_fillH hCcl hCb⟩
    have hj := ((hUo.isConnected_iff_isPathConnected).1 hUc).joinedIn z hz Z hZU
    set p := hj.somePath with hp
    have hpU : ∀ s, p s ∈ H \ fillH C := hj.somePath_mem
    set P : Set ℂ := range p with hPdef
    have hPc : IsCompact P := isCompact_range p.continuous
    have hPU : P ⊆ H \ fillH C := by rintro _ ⟨s, rfl⟩; exact hpU s
    have hzP : z ∈ P := ⟨0, p.source⟩
    have hZP : Z ∈ P := ⟨1, p.target⟩
    obtain ⟨x₀, hx₀P, hx₀min⟩ := hPc.exists_isMinOn ⟨z, hzP⟩ continuous_norm.continuousOn
    have hδ : 0 < ‖x₀‖ := by
      refine norm_pos_iff.2 fun h0 => ?_
      have : (0 : ℝ) < x₀.im := (hPU hx₀P).1
      rw [h0] at this; simp at this
    obtain ⟨q, hq0, hqt, hKq, η₁, hη0, hBc, hKB, hγη⟩ := hrest ‖x₀‖ hδ
    have hq0' : (0 : ℝ) ≤ q := NNReal.coe_nonneg q
    have htq : ((q : ℝ) + ((t - q : ℝ≥0) : ℝ)) = t := by
      rw [NNReal.coe_sub hqt.le]; ring
    have hPD : P ⊆ H \ fwdHull W q := fun x hx => ⟨(hPU hx).1, fun hxK => by
      have h1 : ‖x‖ < ‖x₀‖ := mem_ball_zero_iff.1 (hKq hxK)
      exact absurd (hx₀min hx) (not_le.2 h1)⟩
    set f := fwdMap W q with hf
    have hfc : ContinuousOn f (H \ fwdHull W q) :=
      (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hq0').continuousOn
    set B : Set ℂ := η₁ '' Icc 0 (t - q) with hBdef
    have hBcl : IsClosed B := hBc.isClosed
    have hfPB : f '' P ⊆ H \ B := by
      rintro _ ⟨x, hx, rfl⟩
      have hxD := hPD hx
      have hfx : f x ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hq0' hxD
      refine ⟨hfx, ?_⟩
      rintro ⟨u, hu, hue⟩
      rcases eq_or_lt_of_le hu.1 with h0 | h0
      · rw [← h0, hη0] at hue
        rw [← hue] at hfx; exact absurd hfx (by simp [QuantumZipper.H])
      · have hx' : x = γ (q + u) := by
          rw [hγη u h0 hu.2, hue, QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hq0' hxD]
        have hqu : q + u ≤ t := by
          calc q + u ≤ q + (t - q) := add_le_add_right hu.2 q
            _ = t := add_tsub_cancel_of_le hqt.le
        exact (HalfPlaneSep.H_diff_fillH_subset_H_diff hCcl (hPU hx)).2
          (hx' ▸ ⟨q + u, ⟨zero_le, hqu⟩, rfl⟩)
    have hZD : Z ∈ H \ fwdHull W q := hPD hZP
    have hfZ : f Z ∈ H \ fillH B := by
      refine ⟨QuantumZipper.FwdHolo.mapsTo_fwdMap hW hq0' hZD, fun hmem => ?_⟩
      have hmK : f Z ∈ fwdHull (shiftDrive W q) ((t - q : ℝ≥0) : ℝ) := by rw [hKB]; exact hmem
      have h2 := (mem_fwdHull_add_iff hW hW0 hq0' (NNReal.coe_nonneg _)
        (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hq0' hZD)).2 hmK
      rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hq0' hZD, htq] at h2
      exact hZK h2
    have hpre : IsPreconnected (f '' P) :=
      (isPreconnected_range p.continuous).image f (hfc.mono hPD)
    have hsub := hpre.subset_connectedComponentIn ⟨Z, hZP, rfl⟩ hfPB
    have hfz : f z ∈ H \ fillH B :=
      HalfPlaneSep.connectedComponentIn_subset_H_diff_fillH hBcl hfZ (hsub ⟨z, hzP, rfl⟩)
    have hzD : z ∈ H \ fwdHull W q := hPD hzP
    refine ⟨hz.1, fun hzK => hfz.2 ?_⟩
    rw [← hKB]
    refine (mem_fwdHull_add_iff hW hW0 hq0' (NNReal.coe_nonneg _)
      (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hq0' hzD)).1 ?_
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hq0' hzD, htq]
    exact hzK
  -- (c) conclusion
  ext z
  by_cases hzH : z ∈ H
  · constructor
    · intro hzK
      by_contra hn
      exact (hb ⟨hzH, hn⟩).2 hzK
    · intro hzF
      by_contra hn
      exact (ha ⟨hzH, hn⟩).2 hzF
  · exact ⟨fun h => absurd ((QuantumZipper.fwdHull_mono).2 _ h) hzH, fun h => absurd (fillH_subset_H _ h) hzH⟩

end Real

/-! ### The restart data and the frozen driver -/

section Restarts

variable {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {q₀ : ℝ≥0} {D : Set ℝ≥0} {η : ℝ≥0 → ℝ≥0 → ℂ}

/-- **The restart data on `[0, q₀]`**: at every time `q ∈ D ∩ (0, q₀)` the shifted driver `w(q + ·) − w(q)` has the
simple generating trace `η q` on the closed interval `[0, q₀ − q]`, in `ℍ` at positive times. -/
def RestartData (w : ℝ≥0 → ℝ) (q₀ : ℝ≥0) (D : Set ℝ≥0) (η : ℝ≥0 → ℝ≥0 → ℂ) : Prop :=
  ∀ q ∈ D, 0 < q → q < q₀ → IsGeneratingTraceIcc (shiftNN w q) (q₀ - q) (η q) ∧
    InjOn (η q) (Icc 0 (q₀ - q)) ∧ ∀ u : ℝ≥0, 0 < u → u ≤ q₀ - q → η q u ∈ H

/-- The shifted driver is continuous before `q₀ − q`. -/
theorem continuousOn_shiftNN_of_lt (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hq₀T : (q₀ : ℝ≥0∞) < T)
    {q : ℝ≥0} (hq : q ≤ q₀) :
    ContinuousOn (shiftNN w q) {s | (s : ℝ≥0∞) < ((q₀ - q : ℝ≥0) : ℝ≥0∞)} := by
  refine Sec7.continuousOn_shiftNN (hw.mono fun s hs => ?_)
  have hs' : (s : ℝ≥0∞) < (q : ℝ≥0∞) + ((q₀ - q : ℝ≥0) : ℝ≥0∞) := hs
  rw [← ENNReal.coe_add, add_tsub_cancel_of_le hq] at hs'
  exact hs'.trans hq₀T

section Frozen

variable {t₂ : ℝ}

/-- The frozen driver and the shifted driver agree on `[0, t₂ − q]`. -/
theorem shiftDrive_frozen (q : ℝ≥0) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (t₂ - q)) :
    shiftDrive (frozenDrive w t₂) q r = shiftNN w q r.toNNReal :=
  Zhan.shiftDrive_frozenDrive_eq hr

/-- **The tips of the restarted traces through the frozen driver.** -/
theorem tendsto_shift_tip (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hq₀T : (q₀ : ℝ≥0∞) < T)
    (ht₂ : (q₀ : ℝ) < t₂) {q : ℝ≥0} (hq : q < q₀) {η₁ : ℝ≥0 → ℂ}
    (h : IsGeneratingTraceIcc (shiftNN w q) (q₀ - q) η₁) {u : ℝ≥0} (hu : u ≤ q₀ - q) :
    Tendsto (fwdMapInv (shiftDrive (frozenDrive w t₂) q) u) (𝓝[H] 0) (𝓝 (η₁ u)) := by
  have hut : (u : ℝ) < t₂ - q := by
    have : (u : ℝ) ≤ (q₀ : ℝ) - q := by rw [← NNReal.coe_sub hq.le]; exact_mod_cast hu
    linarith
  rw [fwdMapInv_eq_of_eqOn (W' := fun s : ℝ => shiftNN w q s.toNNReal) (NNReal.coe_nonneg u) hut
    fun r hr => shiftDrive_frozen q hr]
  rcases hu.lt_or_eq with hlt | heq
  · exact h.1.tendsto_fwdMapInv_tip (continuousOn_shiftNN_of_lt hw hq₀T hq.le) (Sec7.shiftNN_zero w q)
      (by exact_mod_cast hlt)
  · rw [heq]; exact h.2.2

/-- **The hulls of the restart through the frozen driver**: `K'_u = fill(η_q[0, u])` for `u ≤ q₀ − q`. -/
theorem fwdHull_shift_eq (ht₂ : (q₀ : ℝ) < t₂) {q : ℝ≥0} (hq : q < q₀)
    {η₁ : ℝ≥0 → ℂ} (h : IsGeneratingTraceIcc (shiftNN w q) (q₀ - q) η₁) {u : ℝ≥0} (hu : u ≤ q₀ - q) :
    fwdHull (shiftDrive (frozenDrive w t₂) q) u = fillH (η₁ '' Icc 0 u) := by
  have hut : (u : ℝ) < t₂ - q := by
    have : (u : ℝ) ≤ (q₀ : ℝ) - q := by rw [← NNReal.coe_sub hq.le]; exact_mod_cast hu
    linarith
  rw [fwdHull_eq_of_eqOn (W' := fun s : ℝ => shiftNN w q s.toNNReal) (NNReal.coe_nonneg u) hut
    fun r hr => shiftDrive_frozen q hr]
  have hB : IsCompact (η₁ '' Icc 0 u) := isCompact_Icc.image_of_continuousOn
    (h.1.2.1.mono fun v hv => (ENNReal.coe_le_coe.2 (hv.2.trans hu)))
  refine (fillH_eq_iff_isFilling_of_isClosed hB.isBounded hB.isClosed ((QuantumZipper.fwdHull_mono).2 _)).1 ?_
  rcases hu.lt_or_eq with hlt | heq
  · exact h.1.2.2 u (by exact_mod_cast hlt)
  · rw [heq]; exact h.2.1


/-- **The trace through a restart**: `LP.traceAt (q + u) w = F_q(η₁ u)` for `0 < u ≤ q₀ − q` (`η₁ u ∈ ℍ`). -/
theorem traceAt_add_eq (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) (hq₀T : (q₀ : ℝ≥0∞) < T)
    (ht₂ : (q₀ : ℝ) < t₂) (ht₂T : ENNReal.ofReal t₂ < T) {q : ℝ≥0} (hq : q < q₀) {η₁ : ℝ≥0 → ℂ}
    (h : IsGeneratingTraceIcc (shiftNN w q) (q₀ - q) η₁) {u : ℝ≥0} (hu : u ≤ q₀ - q) (hH : η₁ u ∈ H) :
    LP.traceAt (q + u) w = fwdMapInv (frozenDrive w t₂) q (η₁ u) := by
  have ht₂0 : 0 ≤ t₂ := (NNReal.coe_nonneg q₀).trans ht₂.le
  have hc : ContinuousOn w (Iic t₂.toNNReal) := hw.mono fun s hs => by
    show (s : ℝ≥0∞) < T
    refine lt_of_le_of_lt ?_ ht₂T
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal ((Real.le_toNNReal_iff_coe_le ht₂0).1 hs)
  have hqu : q + u ≤ q₀ := by
    calc q + u ≤ q + (q₀ - q) := add_le_add_right hu q
      _ = q₀ := add_tsub_cancel_of_le hq.le
  have hqu' : ((q + u : ℝ≥0) : ℝ) < t₂ := lt_of_le_of_lt (by exact_mod_cast hqu) ht₂
  rw [LP.traceAt_eq_trace hqu' hc hw0, trace_eq_of_eqOn (NNReal.coe_nonneg _) hqu'
    (fun r hr => (frozenDrive_eq hr).symm), NNReal.coe_add]
  exact trace_add_eq (continuous_frozenDrive_of_lt hw ht₂T) (by rw [frozenDrive_zero ht₂0, hw0])
    (NNReal.coe_nonneg q) (NNReal.coe_nonneg u) hH (tendsto_shift_tip hw hq₀T ht₂ hq h hu)

/-- **The trace point lies in the hull**: `LP.traceAt (q + u) w ∈ K_{q+u}` for `0 < u ≤ q₀ − q`. -/
theorem traceAt_add_mem (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) (hq₀T : (q₀ : ℝ≥0∞) < T)
    (ht₂ : (q₀ : ℝ) < t₂) (ht₂T : ENNReal.ofReal t₂ < T) {q : ℝ≥0} (hq : q < q₀) {η₁ : ℝ≥0 → ℂ}
    (h : IsGeneratingTraceIcc (shiftNN w q) (q₀ - q) η₁) {u : ℝ≥0} (hu : u ≤ q₀ - q) (hH : η₁ u ∈ H) :
    LP.traceAt (q + u) w ∈ fwdHull (frozenDrive w t₂) ((q + u : ℝ≥0) : ℝ) := by
  have ht₂0 : 0 ≤ t₂ := (NNReal.coe_nonneg q₀).trans ht₂.le
  rw [traceAt_add_eq hw hw0 hq₀T ht₂ ht₂T hq h hu hH, NNReal.coe_add,
    mem_fwdHull_add_iff (continuous_frozenDrive_of_lt hw ht₂T) (by rw [frozenDrive_zero ht₂0, hw0])
      (NNReal.coe_nonneg q) (NNReal.coe_nonneg u) hH, fwdHull_shift_eq ht₂ hq h hu]
  exact ⟨hH, Or.inl (subset_closure ⟨u, ⟨zero_le, le_rfl⟩, rfl⟩)⟩

end Frozen


/-- **The trace up to `q₀` from the restarts** (follow-up 5 §1.2 L180–L184). Let `w` be continuous before `T` with
`w 0 = 0`, `0 < q₀ < T`, `D` dense in `ℝ≥0`, and let the shifted drivers at the times of `D ∩ (0, q₀)` have simple
generating traces on the closed intervals up to `q₀`, in `ℍ` at positive times (`RestartData`). Then
`t ↦ LP.traceAt t w` generates the chain of `w` on the closed interval `[0, q₀]` with its tip at `q₀`, is injective on
`[0, q₀]` and lies in `ℍ` at positive times. -/
theorem isGeneratingTraceIcc_of_restarts (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0)
    (hq₀ : 0 < q₀) (hq₀T : (q₀ : ℝ≥0∞) < T) (hD : ∀ a b : ℝ≥0, a < b → ∃ q ∈ D, a < q ∧ q < b)
    (hR : RestartData w q₀ D η) :
    IsGeneratingTraceIcc w q₀ (fun t => LP.traceAt t w) ∧ InjOn (fun t => LP.traceAt t w) (Icc 0 q₀) ∧
      ∀ t : ℝ≥0, 0 < t → t ≤ q₀ → LP.traceAt t w ∈ H := by
  obtain ⟨t₂, ht₂, ht₂T⟩ := exists_real_btwn_of_lt hq₀T
  have ht₂0 : 0 ≤ t₂ := (NNReal.coe_nonneg q₀).trans ht₂.le
  set W := frozenDrive w t₂ with hWdef
  have hWc : Continuous W := continuous_frozenDrive_of_lt hw ht₂T
  have hW0 : W 0 = 0 := by rw [hWdef, frozenDrive_zero ht₂0, hw0]
  have hEq : ∀ r ∈ Icc (0 : ℝ) t₂, w r.toNNReal = W r := fun r hr => (frozenDrive_eq hr).symm
  set γ : ℝ≥0 → ℂ := fun t => LP.traceAt t w with hγdef
  -- the restart identity at every positive time
  have hid : ∀ t : ℝ≥0, 0 < t → t ≤ q₀ → ∀ q ∈ D, 0 < q → q < t →
      γ t = fwdMapInv W q (η q (t - q)) ∧ η q (t - q) ∈ H ∧ γ t ∈ fwdHull W t := by
    intro t ht0 htq₀ q hqD hq0 hqt
    have hqq₀ : q < q₀ := lt_of_lt_of_le hqt htq₀
    obtain ⟨h1, -, h3⟩ := hR q hqD hq0 hqq₀
    have hu : t - q ≤ q₀ - q := tsub_le_tsub_right htq₀ q
    have hH := h3 (t - q) (tsub_pos_of_lt hqt) hu
    have e : q + (t - q) = t := add_tsub_cancel_of_le hqt.le
    refine ⟨?_, hH, ?_⟩
    · have := traceAt_add_eq hw hw0 hq₀T ht₂ ht₂T hqq₀ h1 hu hH
      rwa [e] at this
    · have := traceAt_add_mem hw hw0 hq₀T ht₂ ht₂T hqq₀ h1 hu hH
      rwa [e] at this
  have hγ0 : γ 0 = 0 := by
    have hc : Continuous fun r : ℝ≥0 => W r := hWc.comp NNReal.continuous_coe
    show LP.traceAt 0 w = 0
    rw [LP.traceAt_congr (w' := fun r : ℝ≥0 => W r) fun r hr => by
      rw [le_antisymm hr zero_le]; simp [hW0, hw0]]
    exact Sec7.Coding.traceAt_zero hc (by simpa using hW0)
  have hpos : ∀ t : ℝ≥0, 0 < t → ∃ q ∈ D, 0 < q ∧ q < t := fun t ht => by
    obtain ⟨q, hqD, hq0, hqt⟩ := hD 0 t ht
    exact ⟨q, hqD, hq0, hqt⟩
  have hγH : ∀ t : ℝ≥0, 0 < t → t ≤ q₀ → γ t ∈ H := fun t ht htq => by
    obtain ⟨q, hqD, hq0, hqt⟩ := hpos t ht
    obtain ⟨e, hH, -⟩ := hid t ht htq q hqD hq0 hqt
    rw [e]; exact QuantumZipper.RS.fwdMapInv_mem_H hWc hW0 (NNReal.coe_nonneg q) hH
  have hγK : ∀ t : ℝ≥0, 0 < t → t ≤ q₀ → γ t ∈ fwdHull W t := fun t ht htq => by
    obtain ⟨q, hqD, hq0, hqt⟩ := hpos t ht
    exact (hid t ht htq q hqD hq0 hqt).2.2
  -- injectivity
  have hinj : InjOn γ (Icc 0 q₀) := by
    have h0 : (0 : ℂ) ∉ H := by simp [QuantumZipper.H]
    intro t₁ ht₁ t₃ ht₃ heq
    rcases eq_or_lt_of_le ht₁.1 with h1 | h1 <;> rcases eq_or_lt_of_le ht₃.1 with h3 | h3
    · rw [← h1, ← h3]
    · rw [← h1, hγ0] at heq; exact absurd (heq ▸ hγH t₃ h3 ht₃.2) h0
    · rw [← h3, hγ0] at heq; exact absurd (heq.symm ▸ hγH t₁ h1 ht₁.2) h0
    · obtain ⟨q, hqD, hq0, hqt⟩ := hpos (min t₁ t₃) (lt_min h1 h3)
      have hq1 : q < t₁ := lt_of_lt_of_le hqt (min_le_left _ _)
      have hq3 : q < t₃ := lt_of_lt_of_le hqt (min_le_right _ _)
      obtain ⟨e1, hH1, -⟩ := hid t₁ h1 ht₁.2 q hqD hq0 hq1
      obtain ⟨e3, hH3, -⟩ := hid t₃ h3 ht₃.2 q hqD hq0 hq3
      have hqq₀ : q < q₀ := lt_of_lt_of_le hq1 ht₁.2
      have hF := (isConformalBijection_fwdMapInv hWc hW0 (NNReal.coe_nonneg q)).2.injOn hH1 hH3
        (by rw [← e1, ← e3]; exact heq)
      have := (hR q hqD hq0 hqq₀).2.1 ⟨zero_le, tsub_le_tsub_right ht₁.2 q⟩
        ⟨zero_le, tsub_le_tsub_right ht₃.2 q⟩ hF
      calc t₁ = q + (t₁ - q) := (add_tsub_cancel_of_le hq1.le).symm
        _ = q + (t₃ - q) := by rw [this]
        _ = t₃ := add_tsub_cancel_of_le hq3.le
  -- continuity on `[0, q₀]`
  have hcont : ContinuousOn γ (Iic q₀) := by
    intro t ht
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | h0
    · rw [← h0]
      refine Metric.continuousWithinAt_iff.2 fun ε hε => ?_
      obtain ⟨s₀, hs₀, hs₀K⟩ := Sec5.exists_fwdHull_subset_ball hWc hW0 hε
      refine ⟨s₀, hs₀, fun s hs hds => ?_⟩
      rw [hγ0, dist_zero_right]
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs0 | hs0
      · rw [← hs0, hγ0, norm_zero]; exact hε
      · have hss₀ : (s : ℝ) ≤ s₀ := by
          have := hds
          rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg s)] at this
          exact this.le
        exact hs₀K _ ((QuantumZipper.fwdHull_mono).1 hss₀ (hγK s hs0 hs))
    · obtain ⟨q, hqD, hq0, hqt⟩ := hpos t h0
      have hqq₀ : q < q₀ := lt_of_lt_of_le hqt ht
      obtain ⟨h1, -, -⟩ := hR q hqD hq0 hqq₀
      obtain ⟨-, hHt, -⟩ := hid t h0 ht q hqD hq0 hqt
      set g : ℝ≥0 → ℂ := fun s => fwdMapInv W q (η q (s - q)) with hg
      have hηc : ContinuousWithinAt (fun s : ℝ≥0 => η q (s - q)) (Iic q₀) t := by
        have hc1 : ContinuousWithinAt (η q) {u : ℝ≥0 | (u : ℝ≥0∞) ≤ ((q₀ - q : ℝ≥0) : ℝ≥0∞)} (t - q) :=
          h1.1.2.1 (t - q) (ENNReal.coe_le_coe.2 (tsub_le_tsub_right ht q))
        have hsub : Continuous fun s : ℝ≥0 => s - q := continuous_id.sub continuous_const
        exact ContinuousWithinAt.comp (f := fun s : ℝ≥0 => s - q) (x := t) hc1 hsub.continuousWithinAt
          fun s (hs : s ≤ q₀) => (ENNReal.coe_le_coe.2 (tsub_le_tsub_right hs q) : ((s - q : ℝ≥0) : ℝ≥0∞) ≤ _)
      have hgc : ContinuousWithinAt g (Iic q₀) t :=
        ContinuousAt.comp_continuousWithinAt (f := fun s : ℝ≥0 => η q (s - q)) (x := t)
          (QuantumZipper.RS.continuousAt_fwdMapInv hWc hW0 (NNReal.coe_nonneg q) hHt) hηc
      refine hgc.congr_of_eventuallyEq ?_ (hid t h0 ht q hqD hq0 hqt).1
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hqt), self_mem_nhdsWithin] with s hs hsq
      exact (hid s (lt_trans hq0 hs) hsq q hqD hq0 hs).1
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (q₀ : ℝ≥0∞)} = Iic q₀ := by
    ext t; simp only [mem_ofPred_eq, mem_Iic, ENNReal.coe_le_coe]
  -- the hulls
  have hfill : ∀ t : ℝ≥0, t ≤ q₀ → IsFilling (fwdHull (fun s : ℝ => w s.toNNReal) t) (γ '' Icc 0 t) := by
    intro t ht
    have htt₂ : (t : ℝ) < t₂ := lt_of_le_of_lt (by exact_mod_cast ht) ht₂
    rw [fwdHull_eq_of_eqOn (NNReal.coe_nonneg t) htt₂ hEq]
    have hcpt : IsCompact (γ '' Icc 0 t) := isCompact_Icc.image_of_continuousOn
      (hcont.mono fun s hs => hs.2.trans ht)
    refine (fillH_eq_iff_isFilling_of_isClosed hcpt.isBounded hcpt.isClosed
      ((QuantumZipper.fwdHull_mono).2 _)).2 ?_
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | h0
    · rw [← h0, NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty hWc]
      have e : γ '' Icc 0 0 = {0} := by
        rw [Icc_self, image_singleton, hγ0]
      rw [e, YuanCharacterisation.fillH_eq_empty_of_subset]
      intro z hz; rw [mem_singleton_iff.1 hz]; simp
    · refine fwdHull_eq_fillH_of_restarts hWc hW0 h0 (hcont.mono fun s hs => hs.2.trans ht) hγ0
        (fun s hs hst => hγK s hs (hst.trans ht)) fun δ hδ => ?_
      obtain ⟨s₀, hs₀, hs₀K⟩ := Sec5.exists_fwdHull_subset_ball hWc hW0 hδ
      obtain ⟨q, hqD, hq0, hqt⟩ := hpos (min s₀.toNNReal t) (lt_min (Real.toNNReal_pos.2 hs₀) h0)
      have hqt' : q < t := lt_of_lt_of_le hqt (min_le_right _ _)
      have hqs : (q : ℝ) ≤ s₀ := by
        have := (lt_of_lt_of_le hqt (min_le_left _ _)).le
        exact (Real.le_toNNReal_iff_coe_le hs₀.le).1 this
      have hqq₀ : q < q₀ := lt_of_lt_of_le hqt' ht
      obtain ⟨h1, -, -⟩ := hR q hqD hq0 hqq₀
      have hu : t - q ≤ q₀ - q := tsub_le_tsub_right ht q
      refine ⟨q, hq0, hqt', fun z hz => mem_ball_zero_iff.2 (hs₀K z ((QuantumZipper.fwdHull_mono).1 hqs hz)),
        η q, h1.1.1, isCompact_Icc.image_of_continuousOn
          (h1.1.2.1.mono fun v hv => ENNReal.coe_le_coe.2 (hv.2.trans hu)),
        fwdHull_shift_eq ht₂ hqq₀ h1 hu, fun u hu0 hut => ?_⟩
      have hqu : q + u ≤ q₀ := by
        calc q + u ≤ q + (t - q) := add_le_add_right hut q
          _ = t := add_tsub_cancel_of_le hqt'.le
          _ ≤ q₀ := ht
      have := (hid (q + u) (lt_of_lt_of_le hq0 le_self_add) hqu q hqD hq0
        (lt_add_of_pos_right q hu0)).1
      rwa [add_tsub_cancel_left] at this
  -- the tip at `q₀`
  have htend : Tendsto (fwdMapInv (fun s : ℝ => w s.toNNReal) q₀) (𝓝[H] 0) (𝓝 (γ q₀)) := by
    rw [fwdMapInv_eq_of_eqOn (NNReal.coe_nonneg q₀) ht₂ hEq]
    obtain ⟨q, hqD, hq0, hqq₀⟩ := hpos q₀ hq₀
    obtain ⟨h1, -, -⟩ := hR q hqD hq0 hqq₀
    obtain ⟨e, hH, -⟩ := hid q₀ hq₀ le_rfl q hqD hq0 hqq₀
    rw [e]
    have hlim := tendsto_shift_tip hw hq₀T ht₂ hqq₀ h1 le_rfl
    have hcomp := (QuantumZipper.RS.continuousAt_fwdMapInv hWc hW0 (NNReal.coe_nonneg q) hH).tendsto.comp hlim
    refine hcomp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have e2 : ((q₀ : ℝ≥0) : ℝ) = (q : ℝ) + ((q₀ - q : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_sub hqq₀.le]; ring
    show fwdMapInv W q (fwdMapInv (shiftDrive W q) ((q₀ - q : ℝ≥0) : ℝ) z) = fwdMapInv W q₀ z
    rw [e2, QuantumZipper.RS.fwdMapInv_add_shift hWc hW0 (NNReal.coe_nonneg q) (NNReal.coe_nonneg _) hz]
  refine ⟨⟨⟨hγ0, by rw [hset]; exact hcont, fun t ht => hfill t (ENNReal.coe_lt_coe.1 ht).le⟩,
    hfill q₀ le_rfl, htend⟩, hinj, hγH⟩

end Restarts

end InteractingSLE.ZhanGT4.A2ImgEnd
