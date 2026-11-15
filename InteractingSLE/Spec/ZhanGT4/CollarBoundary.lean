/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.Collar
import InteractingSLE.Foundations.Loewner.FiniteEndpoint
import InteractingSLE.Foundations.Loewner.Capacity

/-!
# The real collar from the interior inverse boundary (Part A.4.3, first step)

Packet PROVE-ZHAN-GT4-A. Source: Astra, *Follow-up proofs and dependency audit*, §A.4.3
(`source/external/AstraIG1/ig1_followup_proofs.txt` L780–L787, ruling R38):

> If `η(T) ∈ ℍ`, §A.4.2 immediately gives `f((c, d)) ⊂ ℍ` (G5). This implies that every `x ∈ (a, b)` has a relative
> upper-half-plane collar in `K_T`: otherwise `x` belongs to the closed boundary of the active domain, so
> surjectivity of the continuous prime-end boundary map gives a real preimage; the exterior rays map outside
> `(a, b)`, and the remaining interval is interior-valued, a contradiction.

This file proves that deduction for every continuous driver whose inverse map `F_T = g_T⁻¹(W_T + ·)` has a continuous
extension to `ℍ̄` (Carathéodory–Torhorst; for a continuous Loewner trace, `IsLoewnerTraceLT.exists_extension`), and
its probabilistic consequence: **the stopping-time collar statement (G7) follows from its inverse-boundary half (G5)**
(`stoppingCollarStatement_of_inverseBoundary`).

## Proof

Suppose `y` lies strictly between two swallowed real points `x < y < z` and points `w_n ∈ ℍ \ K_T` tend to `y`. Their
images `ζ_n = f_T(w_n) ∈ ℍ` are bounded (uniform displacement `‖f_T(w) − w‖ ≤ 24 M + 8√T`,
`norm_fwdMap_sub_self_le`), so a subsequence converges to `ζ ∈ ℍ̄`, and the extension `F̄` has `F̄(ζ) = y`.

* `ζ ∈ ℍ` is impossible: `F̄(ζ) = F_T(ζ) ∈ ℍ`.
* `ζ = u` real with `u` an exterior coordinate: `F̄` maps the centered image `f_T(x')` of every real point `x'` alive
  at `T` to `x'` (`extension_fwdMap_eq_of_isForwardSol`), and such `x'` lie outside `(x, z)` (alive real points form
  the two outer rays, `le_or_le_of_alive`); by continuity `F̄(u) ∉ (x, z)`.
* `ζ = u` real off the exterior coordinates: (G5) gives a limit `p ∈ ℍ` of `F_T` at `u`, so `y = p ∈ ℍ`.

## Main results

* `le_or_le_of_alive`: a real point alive at `T` is not strictly between two swallowed real points.
* `extension_fwdMap_eq_of_isForwardSol`: `F̄(f_T(x')) = x'` for alive real `x'`.
* `hasRealCollar_of_hasInteriorInverseBoundary`: (G5) ⟹ collar, given a continuous extension of `F_T` to `ℍ̄`.
* `hasRealCollar_of_isLoewnerTrace`: the same for a driver with a continuous trace.
* `StoppingInverseBoundaryStatement κ` (the (G5) half of `StoppingCollarStatement κ`) and
  `stoppingCollarStatement_of_inverseBoundary`: for `κ > 0`, (G5) at every positive finite stopping time implies the
  full (G7).
* `HasRealCollar.exists_uniform`: one collar width over a compact set strictly between swallowed points (L839).
* The two source parts of (G5): `HasInteriorOpenSides` (A.4.2, the open driver sides `(c, W)`, `(W, d)` map into
  `ℍ`) and `HasInteriorTip` (A.4.3, a real tip has `W ∈ {c, d}`), with `hasInteriorInverseBoundary_of_openSides_of_tip`,
  their stopping-time forms `StoppingOpenSidesStatement κ`, `StoppingRealTipStatement κ`, and
  `stoppingCollarStatement_of_openSides_of_tip`: (G7) from A.4.2 and A.4.3.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open QuantumZipper QuantumZipper.RS

variable {W : ℝ → ℝ}

/-- No real point alive at `T` is centered at the driver. -/
theorem not_isForwardSol_zero (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) {v : ℝ → ℂ} :
    ¬ IsForwardSol W ((0 : ℝ) : ℂ) T v := by
  intro hv
  have h := hv.2 0 ⟨le_rfl, hT⟩
  apply h.1
  rw [h.2, hW0]
  simp

/-- **Alive real points lie on the outer rays.** If `x` and `z` are swallowed by time `T` and `x'` is alive at `T`,
then `x' ≤ x` or `z ≤ x'`: on the positive side every point beyond an alive point is alive
(`exists_isForwardSol_of_lt`), and reflection treats the negative side; `0` is never alive. -/
theorem le_or_le_of_alive (hW : Continuous W) (hW0 : W 0 = 0) {x z x' T : ℝ} (hT : 0 ≤ T)
    (hx : IsSwallowedBy W x T) (hz : IsSwallowedBy W z T) (h' : ∃ v, IsForwardSol W (x' : ℂ) T v) :
    x' ≤ x ∨ z ≤ x' := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hxx, hxz⟩ := hcon
  obtain ⟨v, hv⟩ := h'
  rcases lt_trichotomy x' 0 with hneg | h0 | hpos
  · -- reflect: `−x' > 0` alive for `−W`, so `−x > −x'` is alive for `−W`
    have hv' := isForwardSol_neg hv
    rw [← Complex.ofReal_neg] at hv'
    obtain ⟨u, hu⟩ := exists_isForwardSol_of_lt (W := fun s => -W s) hW.neg hT
      (by simp [hW0]; linarith) (by linarith : -x' < -x) hv'
    exact hx (exists_isForwardSol_neg_iff.1 ⟨u, hu⟩)
  · subst h0
    exact not_isForwardSol_zero hW0 hT hv
  · exact hz (exists_isForwardSol_of_lt hW hT (by rw [hW0]; exact hpos) hxz hv)

/-- Points of `ℍ` near a starting point of a solution on `[0, T]` are not swallowed by time `T`. -/
theorem eventually_not_mem_fwdHull (hW : Continuous W) {p : ℂ} {T : ℝ} (hT : 0 ≤ T)
    {v : ℝ → ℂ} (hv : IsForwardSol W p T v) :
    ∀ᶠ z in 𝓝[H] p, z ∈ H \ fwdHull W T := by
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hT hv
  set E := Real.exp (2 / δ ^ 2 * T) with hEdef
  have hE : 0 < E := Real.exp_pos _
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds p (div_pos hδ hE))] with z hz hball
  refine ⟨hz, not_mem_fwdHull_of_isForwardSol hW hv hδ hlow hz ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hball
  rwa [lt_div_iff₀ hE] at hball

/-- **The extension maps the image of an alive real point back to it**: if `F̄` is a continuous extension of
`F_T = fwdMapInv W T` to `ℍ̄` and `x'` is alive at `T`, then `F̄(f_T(x')) = x'`. -/
theorem extension_fwdMap_eq_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 ≤ T) {F : ℂ → ℂ} (hFeq : EqOn F (fwdMapInv W T) H) (hFc : ContinuousOn F Hbar)
    {x' : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol W (x' : ℂ) T v) :
    F (fwdMap W T x') = x' := by
  have := FiniteEndpoint.neBot_nhdsWithin_H (z := (x' : ℂ)) (by simp)
  have hval : v T = fwdMap W T x' := (fwdMap_eq_of_isForwardSol hW hv ⟨hT, le_rfl⟩).symm
  have hlim1 := tendsto_fwdMap_of_isForwardSol hW hT hv
  rw [hval] at hlim1
  have hev := eventually_not_mem_fwdHull hW hT hv
  have hmem : fwdMap W T x' ∈ Hbar := by
    rw [fwdMap_eq_ofReal_re hW hv ⟨hT, le_rfl⟩]
    show (0 : ℝ) ≤ ((fwdMap W T x').re : ℂ).im
    simp
  have hlim2 : Tendsto (fun z => F (fwdMap W T z)) (𝓝[H] (x' : ℂ)) (𝓝 (F (fwdMap W T x'))) :=
    (hFc _ hmem).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim1, hev.mono fun z hz =>
      H_subset_Hbar (FwdHolo.mapsTo_fwdMap hW hT hz)⟩)
  have hid : (fun z => F (fwdMap W T z)) =ᶠ[𝓝[H] (x' : ℂ)] id := by
    filter_upwards [hev] with z hz
    rw [hFeq (FwdHolo.mapsTo_fwdMap hW hT hz), RS.fwdMapInv_fwdMap hW hW0 hT hz]
    rfl
  have hlim3 : Tendsto (fun z => F (fwdMap W T z)) (𝓝[H] (x' : ℂ)) (𝓝 (x' : ℂ)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).congr' hid.symm
  exact tendsto_nhds_unique hlim2 hlim3

/-- **(G5) gives the real collar** (§A.4.3, first step). Let `W` be continuous with `W 0 = 0`, `T ≥ 0`, and let
`F̄` be a continuous extension of `F_T = fwdMapInv W T` from `ℍ` to `ℍ̄`. If the boundary values of `F_T` on the open
inverse interval lie in `ℍ` (`HasInteriorInverseBoundary`), then every real point strictly between two swallowed real
points has a relative upper-half-plane neighbourhood in `K_T`. -/
theorem hasRealCollar_of_hasInteriorInverseBoundary (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 ≤ T) {F : ℂ → ℂ} (hFeq : EqOn F (fwdMapInv W T) H) (hFc : ContinuousOn F Hbar)
    (hG5 : HasInteriorInverseBoundary W T) : HasRealCollar W T := by
  intro x y z hx hz hxy hyz
  by_contra hcon
  push Not at hcon
  -- points of the active domain tending to `y`
  have hseq : ∀ n : ℕ, ∃ w ∈ H, ‖w - y‖ < 1 / ((n : ℝ) + 1) ∧ w ∉ fwdHull W T :=
    fun n => hcon _ (by positivity)
  choose w hwH hwy hwK using hseq
  have hwlim : Tendsto w atTop (𝓝 (y : ℂ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hwy n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- their images are bounded
  set ζ : ℕ → ℂ := fun n => fwdMap W T (w n) with hζdef
  have hwmem : ∀ n, w n ∈ H \ fwdHull W T := fun n => ⟨hwH n, hwK n⟩
  have hζH : ∀ n, ζ n ∈ H := fun n => FwdHolo.mapsTo_fwdMap hW hT (hwmem n)
  have hFζ : ∀ n, F (ζ n) = w n := fun n => by
    rw [hFeq (hζH n)]; exact RS.fwdMapInv_fwdMap hW hW0 hT (hwmem n)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 T))
  have hM' : ∀ r ∈ Icc (0 : ℝ) T, |W r| ≤ M := fun r hr => by
    simpa [Real.norm_eq_abs] using hM r hr
  set D := 24 * M + 8 * Real.sqrt T with hDdef
  have hζbd : ∀ n, ζ n ∈ Metric.closedBall (0 : ℂ) (‖(y : ℂ)‖ + 1 + D) := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := norm_fwdMap_sub_self_le hW hW0 hT hM' (hwmem n) ⟨hT, le_rfl⟩
    have h2 : ‖w n‖ ≤ ‖(y : ℂ)‖ + 1 := by
      have h3 := hwy n
      have h4 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      calc ‖w n‖ ≤ ‖(y : ℂ)‖ + ‖w n - y‖ := norm_le_norm_add_norm_sub' _ _
        _ ≤ ‖(y : ℂ)‖ + 1 := by linarith
    calc ‖ζ n‖ ≤ ‖w n‖ + ‖ζ n - w n‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖(y : ℂ)‖ + 1 + D := by linarith
  obtain ⟨ζs, -, φ, hφ, hζlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hζbd
  have hζsH : ζs ∈ Hbar :=
    isClosed_Hbar.mem_of_tendsto hζlim (Eventually.of_forall fun n => H_subset_Hbar (hζH (φ n)))
  -- the extension at the limit point is `y`
  have hlimF : Tendsto (fun n => F (ζ (φ n))) atTop (𝓝 (F ζs)) :=
    (hFc ζs hζsH).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hζlim, Eventually.of_forall fun n => H_subset_Hbar (hζH (φ n))⟩)
  have hlimw : Tendsto (fun n => F (ζ (φ n))) atTop (𝓝 (y : ℂ)) := by
    simp only [hFζ]
    exact hwlim.comp hφ.tendsto_atTop
  have hFy : F ζs = y := tendsto_nhds_unique hlimF hlimw
  rcases (show (0 : ℝ) ≤ ζs.im from hζsH).lt_or_eq with hpos | hzero
  · -- an interior limit point: `F̄(ζ) ∈ ℍ`
    have h1 : F ζs ∈ H := by
      rw [hFeq hpos]; exact RS.fwdMapInv_mem_H hW hW0 hT hpos
    rw [hFy] at h1
    have h2 : (0 : ℝ) < (y : ℂ).im := h1
    simp at h2
  -- a real limit point `u`
  set u := ζs.re with hudef
  have hζu : ζs = (u : ℂ) := Complex.ext (by simp [hudef]) (by simp [← hzero])
  by_cases hu : u ∈ exteriorCoords W T
  · -- exterior coordinates are mapped to the outer rays
    have hcont : Continuous fun r : ℝ => F (r : ℂ) :=
      hFc.comp_continuous continuous_ofReal fun r => by
        show (0 : ℝ) ≤ (r : ℂ).im
        simp
    set C : Set ℝ := {r | (F (r : ℂ)).im = 0 ∧ ((F (r : ℂ)).re ≤ x ∨ z ≤ (F (r : ℂ)).re)}
      with hCdef
    have hC : IsClosed C :=
      (isClosed_eq (continuous_im.comp hcont) continuous_const).inter
        ((isClosed_le (continuous_re.comp hcont) continuous_const).union
          (isClosed_le continuous_const (continuous_re.comp hcont)))
    have hS : {r : ℝ | ∃ x' : ℝ, (∃ v, IsForwardSol W (x' : ℂ) T v) ∧ (fwdMap W T x').re = r} ⊆ C := by
      rintro r ⟨x', ⟨v, hv⟩, rfl⟩
      have hreal := fwdMap_eq_ofReal_re hW hv ⟨hT, le_rfl⟩
      have hF := extension_fwdMap_eq_of_isForwardSol hW hW0 hT hFeq hFc hv
      rw [hreal] at hF
      rw [mem_ofPred_eq, hF]
      refine ⟨by simp, ?_⟩
      simpa using le_or_le_of_alive hW hW0 hT hx hz ⟨v, hv⟩
    have huC : u ∈ C := closure_minimal hS hC hu
    obtain ⟨-, h2⟩ := huC
    rw [← hζu, hFy] at h2
    simp only [ofReal_re] at h2
    rcases h2 with h | h <;> linarith
  · -- off the exterior coordinates, (G5) puts the boundary value in `ℍ`
    obtain ⟨p, hpH, hplim⟩ := hG5 u hu
    have hζlim' : Tendsto (fun n => ζ (φ n)) atTop (𝓝[H] (u : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hζu ▸ hζlim, Eventually.of_forall fun n => hζH (φ n)⟩
    have h1 : Tendsto (fun n => F (ζ (φ n))) atTop (𝓝 p) := by
      have := hplim.comp hζlim'
      refine this.congr fun n => ?_
      simp only [Function.comp]
      rw [hFeq (hζH (φ n))]
    have hpy : p = y := tendsto_nhds_unique h1 hlimw
    rw [hpy] at hpH
    have h2 : (0 : ℝ) < (y : ℂ).im := hpH
    simp at h2

/-- **(G5) gives the real collar for a driver with a continuous trace** (`IsLoewnerTrace`, Carathéodory–Torhorst
boundary extension `IsLoewnerTraceLT.exists_extension`). -/
theorem hasRealCollar_of_isLoewnerTrace {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hG5 : HasInteriorInverseBoundary W T) : HasRealCollar W T := by
  have hLT : IsLoewnerTraceLT W (T + 1) η :=
    ⟨hη.1, hη.2.1.mono Ico_subset_Ici_self, fun t ht _ => hη.2.2 t ht⟩
  obtain ⟨F, hFeq, hFc, -⟩ := hLT.exists_extension hW hW0 hT (by linarith)
  exact InteractingSLE.ZhanGT4.hasRealCollar_of_hasInteriorInverseBoundary hW hW0 hT hFeq hFc hG5

/-- **(G5) at a stopping time** (Part A.4, L833: `f_T((c(T), d(T))) ⊂ ℍ`): the inverse-boundary half of
`StoppingCollarStatement κ`. -/
def StoppingInverseBoundaryStatement (κ : ℝ) : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓕 B P →
    ∀ T : Ω → ℝ≥0, IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0)) → (∀ ω, 0 < T ω) →
      ∀ᵐ ω ∂P, HasInteriorInverseBoundary (drive κ B ω) (T ω)

/-- **The stopping-time collar (G7) from its inverse-boundary half (G5)** (§A.4.3: "This implies that every
`x ∈ (a, b)` has a relative upper-half-plane collar in `K_T`"), for every `κ > 0`: ordinary `SLE_κ` has a continuous
trace almost surely (`ae_isLoewnerTrace_sleTrace`), so `hasRealCollar_of_isLoewnerTrace`
applies pathwise. -/
theorem stoppingCollarStatement_of_inverseBoundary {κ : ℝ} (hκ : 0 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{u} κ) : StoppingCollarStatement.{u} κ := by
  intro Ω mΩ P _ 𝓕 B hB T hT hT0
  filter_upwards [hG5 P 𝓕 B hB T hT hT0, ae_isLoewnerTrace_sleTrace hB.1 hκ, hB.1.cont,
    hB.1.eval_zero_ae_eq_zero] with ω h5 hη hc h0
  have hW : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  exact ⟨h5, hasRealCollar_of_isLoewnerTrace hη hW hW0 (T ω).coe_nonneg h5⟩

/-- **A uniform collar over a compact set** (§A.4.3, L839: "For any compact `I ⊂ (a(T), b(T))`, a finite subcover
gives one uniform collar width for `I`"): if the real collar holds at `T` and the compact set `I ⊆ ℝ` lies strictly
between two swallowed real points, one `ε > 0` works for every point of `I`. This is the form LP4 applies to the
compact fibre `F = f_T⁻¹({0})` (specification p. 483). -/
theorem HasRealCollar.exists_uniform {T : ℝ} (hC : HasRealCollar W T) {x z : ℝ}
    (hx : IsSwallowedBy W x T) (hz : IsSwallowedBy W z T) {I : Set ℝ} (hI : IsCompact I)
    (hIxz : I ⊆ Ioo x z) :
    ∃ ε > (0 : ℝ), ∀ y ∈ I, ∀ w ∈ H, ‖w - y‖ < ε → w ∈ fwdHull W T := by
  have hloc : ∀ y ∈ I, ∃ ε > (0 : ℝ), ∀ w ∈ H, ‖w - y‖ < ε → w ∈ fwdHull W T :=
    fun y hy => hC x y z hx hz (hIxz hy).1 (hIxz hy).2
  choose! ε hε hεK using hloc
  -- cover `I` by the half-radius intervals and take a finite subcover
  obtain ⟨t, htI, hcover⟩ := hI.elim_nhds_subcover (fun y => Metric.ball y (ε y / 2))
    fun y hy => Metric.ball_mem_nhds y (half_pos (hε y hy))
  rcases t.eq_empty_or_nonempty with ht | ht
  · refine ⟨1, one_pos, fun y hy => ?_⟩
    have := hcover hy
    simp [ht] at this
  set δ := t.inf' ht (fun y => ε y / 2) with hδdef
  have hδ : 0 < δ := (Finset.lt_inf'_iff ht).2 fun y hy => half_pos (hε y (htI y hy))
  refine ⟨δ, hδ, fun y hy w hw hwy => ?_⟩
  obtain ⟨y₀, hy₀t, hyy₀⟩ := Set.mem_iUnion₂.1 (hcover hy)
  have hy₀I := htI y₀ hy₀t
  rw [Metric.mem_ball, Real.dist_eq] at hyy₀
  have hδle : δ ≤ ε y₀ / 2 := Finset.inf'_le _ hy₀t
  refine hεK y₀ hy₀I w hw ?_
  calc ‖w - y₀‖ = ‖(w - y) + ((y : ℂ) - y₀)‖ := by ring_nf
    _ ≤ ‖w - y‖ + ‖((y : ℂ) - y₀)‖ := norm_add_le _ _
    _ < ε y₀ / 2 + ε y₀ / 2 := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact add_lt_add_of_lt_of_le (hwy.trans_le hδle) hyy₀.le
    _ = ε y₀ := by ring

/-! ### (G5) from its two source parts: the open driver sides (A.4.2) and the tip (A.4.3) -/

/-- **The open driver sides are interior** (§A.4.2, L743–L744: "`f` is injective on each of `(c, W)` and `(W, d)`,
and maps both intervals into `ℍ`", the mapping part): at every real `u ≠ 0` off the exterior coordinates (centered
coordinates, the driver at `0`) the inverse map has a boundary value in `ℍ`. -/
def HasInteriorOpenSides (W : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ u : ℝ, u ∉ exteriorCoords W T → u ≠ 0 →
    ∃ p ∈ H, Tendsto (fwdMapInv W T) (𝓝[H] (u : ℂ)) (𝓝 p)

/-- **A real tip sits at an end of the inverse interval** (§A.4.3, L798–L831: "Consequently a real tip must have
`W = c` or `W = d`"): if the driver coordinate `0` is off the exterior coordinates (`c < W_T < d`), the tip
(the boundary value of the inverse map at `0`) exists and lies in `ℍ`. -/
def HasInteriorTip (W : ℝ → ℝ) (T : ℝ) : Prop :=
  (0 : ℝ) ∉ exteriorCoords W T → ∃ p ∈ H, Tendsto (fwdMapInv W T) (𝓝[H] (0 : ℂ)) (𝓝 p)

/-- (G5) is the conjunction of its two source parts (§A.4.3: "§A.4.2 then gives (G5)"). -/
theorem hasInteriorInverseBoundary_of_openSides_of_tip {T : ℝ} (h1 : HasInteriorOpenSides W T)
    (h2 : HasInteriorTip W T) : HasInteriorInverseBoundary W T := by
  intro u hu
  rcases eq_or_ne u 0 with rfl | h0
  · simpa using h2 hu
  · exact h1 u hu h0

/-- **A.4.2 at a stopping time**: for ordinary `SLE_κ` and every positive finite stopping time, almost surely the
open driver sides of the inverse interval are interior. -/
def StoppingOpenSidesStatement (κ : ℝ) : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓕 B P →
    ∀ T : Ω → ℝ≥0, IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0)) → (∀ ω, 0 < T ω) →
      ∀ᵐ ω ∂P, HasInteriorOpenSides (drive κ B ω) (T ω)

/-- **A.4.3 (real tip) at a stopping time**: for ordinary `SLE_κ` and every positive finite stopping time, almost
surely a real tip sits at an end of the inverse interval. -/
def StoppingRealTipStatement (κ : ℝ) : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓕 B P →
    ∀ T : Ω → ℝ≥0, IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0)) → (∀ ω, 0 < T ω) →
      ∀ᵐ ω ∂P, HasInteriorTip (drive κ B ω) (T ω)

/-- (G5) at stopping times from A.4.2 and A.4.3's tip statement. -/
theorem stoppingInverseBoundaryStatement_of_openSides_of_tip {κ : ℝ}
    (h1 : StoppingOpenSidesStatement.{u} κ) (h2 : StoppingRealTipStatement.{u} κ) :
    StoppingInverseBoundaryStatement.{u} κ := by
  intro Ω mΩ P _ 𝓕 B hB T hT hT0
  filter_upwards [h1 P 𝓕 B hB T hT hT0, h2 P 𝓕 B hB T hT hT0] with ω ha hb
  exact hasInteriorInverseBoundary_of_openSides_of_tip ha hb

/-- **(G7) from A.4.2 and A.4.3** (for `κ > 0`): the full stopping-time collar statement. -/
theorem stoppingCollarStatement_of_openSides_of_tip {κ : ℝ} (hκ : 0 < κ)
    (h1 : StoppingOpenSidesStatement.{u} κ) (h2 : StoppingRealTipStatement.{u} κ) :
    StoppingCollarStatement.{u} κ :=
  stoppingCollarStatement_of_inverseBoundary hκ (stoppingInverseBoundaryStatement_of_openSides_of_tip h1 h2)

end InteractingSLE.ZhanGT4
