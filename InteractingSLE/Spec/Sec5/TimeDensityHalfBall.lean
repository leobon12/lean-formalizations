/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TimeDensity
import InteractingSLE.Spec.ZhanGT4.NoClusterGirsanov
import InteractingSLE.Spec.Supplement.LP4HalfBallFuture
import InteractingSLE.Foundations.SLE.All
import InteractingSLE.WangWu.SideValues
import InteractingSLE.Spec.ZhanGT4.RealTip
import InteractingSLE.Foundations.Loewner.YuanShift

/-!
# (5.8): the future half-ball property of an integrated `SLE_κ(ρ)` evolution, `κ > 4`

Packet PROVE-PROP513. Specification §5.2, proof of Proposition 5.13 (`source/spec/p145-192.md` L101–L109,
pp. 149–150):

  "For ordinary chordal `SLE_κ'`, `κ' > 4`, every positive-time hull contains an upper half-neighborhood of its
  starting point [RS05, Lemma 7.3] … Fix deterministic `r > 0` and `δ > 0`. At time `r` the original force points of
  the present non-boundary-intersecting counterflow are almost surely separated from its driver. Conditional on the
  history through `r`, stop the future driving evolution before any of these gaps becomes smaller than a fixed
  positive cutoff, and impose a finite horizon. … The additional drift is bounded up to this stop. Stopped Girsanov
  therefore makes this evolution mutually absolutely continuous with ordinary chordal `SLE_κ'` up to the same stop.
  … Apply the preceding ordinary-SLE assertion at a positive rational time smaller than both this localization
  duration and `δ` … Hull monotonicity then gives a random `a = a(r, δ) > 0` such that
  `B(W_r, a) ∩ ℍ ⊆ g_r(K_{r+δ} \ K_r)` (5.8)."

**`IsIntegratedSLEEvolution.ae_hasFutureHalfBall`**: for an integrated `SLE_κ(ρ)` evolution with `κ > 4`, a
deterministic time `r` and `δ > 0`, almost surely on `{r < ζ}` with every force point strictly separated from the
driver at time `r`, the future half-ball property `HasFutureHalfBall w r δ` holds for every continuous driver `w`
agreeing with `W` before the lifetime. The separation at the fixed time `r` is a hypothesis of the event, exactly as
the source states it ("At time `r` the original force points … are almost surely separated from its driver"); it is
not proved here.

Proof (the source's): the cut-drift Girsanov change (`Girsanov.girsanov_cutDrift`, cut level `1/(n+1)`, horizon `n`;
template `ZhanGT4.IsIntegratedSLEEvolution.ae_hasInteriorInverseBoundary_level`) makes `B̂` a Brownian motion under an
equivalent probability `Q`; its increments after `r` form a Brownian motion (`IsBrownianReal.shift`); [RS05,
Lemma 7.3] (`ae_forall_sleHull_halfBall_of_four_lt`) holds for them `Q`-almost surely, hence `P`-almost surely; while
the gaps stay above the cut level, the driver increments after `r` are `√κ` times those of `B̂`
(`Dimension.sub_eq_sqrt_mul_sub_of_cut`), so the restarted hulls coincide with the ordinary `SLE_κ` hulls of `B̂`'s
increments for a short positive time; hull monotonicity finishes. A union over the levels removes the cut level.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec5

open QuantumZipper QuantumZipper.RS InteractingSLE.Girsanov

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- Gaps that start above `2δ` at an interior time `r` of `{s < ζ}` stay above `δ` on a short interval after `r`,
which also stays before `ζ` and before a horizon `N > r`. -/
theorem exists_gap_interval {m : ℕ} {w : ℝ≥0 → ℝ} {v : Fin m → ℝ≥0 → ℝ} {ζ₀ : ℝ≥0∞} {r N : ℝ≥0} {δ : ℝ}
    (hδ : 0 < δ) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ₀}) (hv : ∀ k, ContinuousOn (v k) {s | (s : ℝ≥0∞) < ζ₀})
    (hrζ : (r : ℝ≥0∞) < ζ₀) (hrN : r < N) (hg : ∀ k, 2 * δ ≤ |w r - v k r|) :
    ∃ s₁ : ℝ≥0, 0 < s₁ ∧ ((r + s₁ : ℝ≥0) : ℝ≥0∞) < ζ₀ ∧ r + s₁ ≤ N ∧
      ∀ s : ℝ≥0, r ≤ s → s ≤ r + s₁ → ∀ k, δ ≤ |w s - v k s| := by
  have hO : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ₀} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hOr : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ₀} ∈ 𝓝 r := hO.mem_nhds hrζ
  have hev : ∀ᶠ s : ℝ≥0 in 𝓝 r, (s : ℝ≥0∞) < ζ₀ ∧ s < N ∧ ∀ k, δ < |w s - v k s| := by
    have h1 : ∀ᶠ s : ℝ≥0 in 𝓝 r, (s : ℝ≥0∞) < ζ₀ := hO.mem_nhds hrζ
    have h2 : ∀ᶠ s : ℝ≥0 in 𝓝 r, s < N := (isOpen_gt' N).mem_nhds hrN
    refine h1.and (h2.and ?_)
    refine eventually_all.2 fun k => ?_
    have hc : ContinuousAt (fun s => |w s - v k s|) r :=
      (((hw.continuousAt hOr).sub ((hv k).continuousAt hOr)).abs)
    exact hc.eventually (lt_mem_nhds (by linarith [hg k]))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hs₁ : (0 : ℝ≥0) < (ε / 2).toNNReal := Real.toNNReal_pos.2 (by positivity)
  have hdist : ∀ s : ℝ≥0, r ≤ s → s ≤ r + (ε / 2).toNNReal → dist s r < ε := by
    intro s hrs hs
    rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hrs))]
    have h1 : (s : ℝ) ≤ r + ε / 2 := by
      have := NNReal.coe_le_coe.2 hs
      rwa [NNReal.coe_add, Real.coe_toNNReal _ (by positivity)] at this
    linarith
  have hend := hball (hdist _ le_self_add le_rfl)
  refine ⟨(ε / 2).toNNReal, hs₁, hend.1, hend.2.1.le, fun s hrs hs k => ?_⟩
  exact (hball (hdist s hrs hs)).2.2 k |>.le

/-- **(5.8) at one localization level.** Almost surely: if `r < n`, `r` comes before the lifetime and every gap at
time `r` is at least `2/(n+1)`, then the future half-ball property at `(r, δ)` holds for every continuous driver
agreeing with `W` before the lifetime. -/
theorem IsIntegratedSLEEvolution.ae_hasFutureHalfBall_level [IsProbabilityMeasure P] (hκ : 4 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (r δ : ℝ≥0) (hδ : 0 < δ) (n : ℕ) :
    ∀ᵐ ω ∂P, r < (n : ℝ≥0) → (r : ℝ≥0∞) < ζ ω →
      (∀ k, 2 * (1 / ((n : ℝ) + 1)) ≤ |W r ω - allMarks VL VR k r ω|) →
      ∀ w' : ℝ≥0 → ℝ, Continuous w' → (∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω → w' s = W s ω) →
        HasFutureHalfBall w' r δ := by
  have hκ0 : 0 < κ := by linarith
  obtain ⟨hBF, hW, hVL, hVR, hpath⟩ := hE
  set δn : ℝ := 1 / ((n : ℝ) + 1) with hδdef
  have hδn : 0 < δn := by positivity
  set U : Fin (nL + nR) → ℝ≥0 → Ω → ℝ := allMarks VL VR with hUdef
  set σ : Fin (nL + nR) → ℝ := Fin.addCases (motive := fun _ => ℝ) ρL ρR with hσ
  set F : ℝ → (Fin (nL + nR) → ℝ) → ℝ := fun w u => (Real.sqrt κ)⁻¹ * addedDriftCut σ δn w u
    with hFdef
  have hFc : Continuous fun p : ℝ × (Fin (nL + nR) → ℝ) => F p.1 p.2 :=
    continuous_const.mul (continuous_addedDriftCut σ hδn)
  have hFb : ∀ w u, |F w u| ≤ (Real.sqrt κ)⁻¹ * ((∑ j, |σ j|) * δn⁻¹) := fun w u => by
    rw [hFdef, abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg κ))]
    exact mul_le_mul_of_nonneg_left (abs_addedDriftCut_le σ hδn w u)
      (inv_nonneg.2 (Real.sqrt_nonneg κ))
  set N : ℝ≥0 := (n : ℝ≥0) with hN
  set τ : Ω → ℝ≥0∞ := fun ω => min (ζ ω) (N : ℝ≥0∞) with hτdef
  have hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s} := by
    intro s
    have h1 : MeasurableSet[𝓕 s] {ω | (s : ℝ≥0∞) < ζ ω ∧ W s ω ∈ (univ : Set ℝ)} :=
      hW s univ MeasurableSet.univ
    have h2 : {ω | τ ω ≤ s} = {ω | (s : ℝ≥0∞) < ζ ω ∧ W s ω ∈ (univ : Set ℝ)}ᶜ ∪
        {_ω : Ω | (N : ℝ≥0∞) ≤ s} := by
      ext ω
      simp [hτdef, min_le_iff, not_lt]
    rw [h2]
    exact h1.compl.union (MeasurableSet.const _)
  have hτζ : ∀ ω, τ ω ≤ ζ ω := fun ω => min_le_left _ _
  have hτT : ∀ ω, τ ω ≤ (N : ℝ≥0∞) := fun ω => min_le_right _ _
  have hU : ∀ k, AdaptedBefore 𝓕 ζ (U k) := fun k => by
    cases k using Fin.addCases with
    | left i => simpa [hUdef, allMarks] using hVL i
    | right i => simpa [hUdef, allMarks] using hVR i
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ k, ContinuousOn (fun s => U k s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hpath] with ω hp
    refine ⟨hp.2.2.2.1, fun k => ?_⟩
    cases k using Fin.addCases with
    | left i => simpa [hUdef, allMarks] using hp.2.2.2.2.1 i
    | right i => simpa [hUdef, allMarks] using hp.2.2.2.2.2.1 i
  obtain ⟨hequiv, hBM, hident⟩ := girsanov_cutDrift hBF hFc hFb hW hU hτ hτζ hτT hcont
  set θ := cutDrift τ ζ F W U with hθ
  set Q := girsanovMeasure P 𝓕 B θ (N + 1) with hQ
  set Bh := girsanovProcess B θ with hBh
  have : IsProbabilityMeasure Q := hequiv.isProb
  -- the increments of `B̂` after `r` are a Brownian motion under `Q`; [RS05, Lemma 7.3] for them
  set B' : ℝ≥0 → Ω → ℝ := fun s ω => Bh (r + s) ω - Bh r ω with hB'def
  have hB' : IsBrownianReal B' Q := hBM.1.shift r
  have hPhb := hequiv.ac'.ae_le (ae_forall_sleHull_halfBall_of_four_lt hB' hκ)
  have hPc := hequiv.ac'.ae_le hB'.cont
  filter_upwards [hident, hpath, hPhb, hPc, hcont] with ω hid hp hhb hBc hc hrN hrζ hg w' hw' hw'eq
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgapL, hgapR, hweq, -⟩ := hp
  obtain ⟨s₁, hs₁, hs₁ζ, hs₁N, hgap⟩ := exists_gap_interval hδn hc.1 hc.2 hrζ hrN hg
  -- the driver increments after `r` are `√κ` times those of `B̂` on `[r, r + s₁]`
  have hsplit : ∀ t : ℝ≥0, (∑ k, ∫ s in (0 : ℝ)..(t : ℝ), σ k / (W s.toNNReal ω - U k s.toNNReal ω))
      = (∑ i, ∫ s in (0 : ℝ)..(t : ℝ), ρL i / (W s.toNNReal ω - VL i s.toNNReal ω))
        + (∑ i, ∫ s in (0 : ℝ)..(t : ℝ), ρR i / (W s.toNNReal ω - VR i s.toNNReal ω)) := by
    intro t
    rw [Fin.sum_univ_add]
    simp only [hσ, hUdef, allMarks, Fin.addCases_left, Fin.addCases_right]
  have hagree : ∀ u : ℝ≥0, u ≤ s₁ → W (r + u) ω - W r ω = Real.sqrt κ * B' u ω := by
    intro u hu
    have hruζ : ((r + u : ℝ≥0) : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (add_le_add le_rfl hu)) hs₁ζ
    have ht' : ((r + u : ℝ≥0) : ℝ≥0∞) ≤ τ ω :=
      le_min hruζ.le (ENNReal.coe_le_coe.2 ((add_le_add le_rfl hu).trans hs₁N))
    have hr' : (r : ℝ≥0∞) ≤ τ ω := le_min hrζ.le (ENNReal.coe_le_coe.2 hrN.le)
    have hint : ∀ k, IntervalIntegrable (fun s : ℝ => σ k / (W s.toNNReal ω - U k s.toNNReal ω))
        volume 0 ((r + u : ℝ≥0) : ℝ) := fun k => by
      cases k using Fin.addCases with
      | left i =>
        simp only [hσ, hUdef, allMarks, Fin.addCases_left, div_eq_mul_inv]
        exact (hgapL _ hruζ i).const_mul (ρL i)
      | right i =>
        simp only [hσ, hUdef, allMarks, Fin.addCases_right, div_eq_mul_inv]
        exact (hgapR _ hruζ i).const_mul (ρR i)
    have hfint := intervalIntegrable_comp_of_le hFc hFb hW hU hτ (hτζ ω) hc.1 hc.2 ht'
    have key := Dimension.sub_eq_sqrt_mul_sub_of_cut (u := fun k s => U k s ω) (w := fun s => W s ω)
      (b := fun s => B s ω) (bh := fun s => Bh s ω) hκ0 hδn σ hint hfint ?_ ?_ (hid _ ht') (hid _ hr') ?_
    · exact key
    · have h1 := hweq (r + u) hruζ
      beta_reduce at h1
      rw [hsplit]; linarith
    · have h1 := hweq r hrζ
      beta_reduce at h1
      rw [hsplit]; linarith
    · intro s hrs hs k
      exact hgap s hrs (hs.trans (add_le_add le_rfl hu)) k
  -- [RS05, Lemma 7.3] at the time `t = min s₁ δ`
  set t : ℝ≥0 := min s₁ δ with htdef
  have ht0 : (0 : ℝ) < t := by exact_mod_cast lt_min hs₁ hδ
  obtain ⟨ε, hε, hball⟩ := hhb (t : ℝ) ht0
  refine ⟨ε, hε, fun z hz hzε => ?_⟩
  set V : ℝ → ℝ := fun s => w' s.toNNReal with hVdef
  have hV : Continuous V := hw'.comp continuous_real_toNNReal
  have hdc : Continuous (drive κ B' ω) := drive_continuous hBc
  have heq : fwdHull (drive κ B' ω) t = fwdHull (shiftDrive V r) t := by
    refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc hdc (continuous_shiftDrive hV r) t.coe_nonneg
      fun x hx => ?_
    have hxu : x.toNNReal ≤ s₁ := by
      have : x.toNNReal ≤ t := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hx.1]; exact hx.2
      exact this.trans (min_le_left _ _)
    have hrx : ((r : ℝ) + x).toNNReal = r + x.toNNReal := by
      rw [← NNReal.coe_inj, Real.coe_toNNReal _ (add_nonneg r.coe_nonneg hx.1), NNReal.coe_add,
        Real.coe_toNNReal _ hx.1]
    have hζ1 : ((r + x.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (add_le_add le_rfl hxu)) hs₁ζ
    simp only [drive, shiftDrive, hVdef, hrx, Real.toNNReal_coe, hw'eq _ hζ1, hw'eq _ hrζ]
    rw [hagree _ hxu]
  have hzt : z ∈ fwdHull (shiftDrive V r) t := by
    rw [← heq]; exact hball z hz hzε
  exact fwdHull_mono.1 (by exact_mod_cast (min_le_right s₁ δ : t ≤ δ)) hzt

/-- **(5.8) for an integrated `SLE_κ(ρ)` evolution, `κ > 4`** (proof of Proposition 5.13, pp. 149–150). For a
deterministic time `r` and `δ > 0`, almost surely: if `r` comes before the lifetime and every force point is
strictly separated from the driver at time `r`, then the hull at time `δ` of the restarted driver contains a
half-ball, for every continuous driver `w'` agreeing with `W` before the lifetime. -/
theorem IsIntegratedSLEEvolution.ae_hasFutureHalfBall [IsProbabilityMeasure P] (hκ : 4 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (r δ : ℝ≥0) (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, (r : ℝ≥0∞) < ζ ω → (∀ i, VL i r ω < W r ω) → (∀ j, W r ω < VR j r ω) →
      ∀ w' : ℝ≥0 → ℝ, Continuous w' → (∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω → w' s = W s ω) →
        HasFutureHalfBall w' r δ := by
  have hall := ae_all_iff.2 fun n : ℕ =>
    IsIntegratedSLEEvolution.ae_hasFutureHalfBall_level hκ hE r δ hδ n
  filter_upwards [hall] with ω hlev hrζ hL hR w' hw' hw'eq
  -- a uniform positive lower bound for the gaps at `r`
  have hpos : ∀ k, 0 < |W r ω - allMarks VL VR k r ω| := by
    intro k
    cases k using Fin.addCases with
    | left i =>
      simp only [allMarks, Fin.addCases_left]
      exact abs_pos.2 (sub_pos.2 (hL i)).ne'
    | right j =>
      simp only [allMarks, Fin.addCases_right]
      exact abs_pos.2 (sub_neg.2 (hR j)).ne
  obtain ⟨c, hc, hcle⟩ := ZhanGT4.exists_pos_forall_of_fintype
    (p := fun k a => a ≤ |W r ω - allMarks VL VR k r ω|) (fun _ _ _ hab h => hab.trans h)
    (fun k => ⟨_, hpos k, le_rfl⟩)
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt (r : ℝ)
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt (2 / c)
  set n := max n₁ n₂ with hn
  refine hlev n ?_ hrζ (fun k => ?_) w' hw' hw'eq
  · have : (r : ℝ) < (n : ℝ) := hn₁.trans_le (by exact_mod_cast le_max_left n₁ n₂)
    exact_mod_cast this
  · have hn2 : 2 / c < (n : ℝ) + 1 :=
      hn₂.trans_le (by have : (n₂ : ℝ) ≤ n := by exact_mod_cast le_max_right n₁ n₂
                       linarith)
    have : 2 * (1 / ((n : ℝ) + 1)) ≤ c := by
      rw [div_lt_iff₀ hc] at hn2
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      linarith
    exact this.trans (hcle k)

/-- **A tip in the open half-plane separates the force points from the driver**: for an integrated `SLE_κ(ρ)` path
with a generating trace `η` on `[0, ∞)`, if `η(t) ∈ ℍ` at a time `t` before the lifetime, every left force point is
strictly left of the driver and every right force point strictly right of it at `t` (the boundary value of the inverse
map at the centred driver `0` is the tip; WangWu's `vL_sub_lt_of_extendFrom_mem_H`, `lt_vR_sub_of_extendFrom_mem_H`).
This is how "the original force points of the present non-boundary-intersecting counterflow are almost surely
separated from its driver" follows from the counterflow avoiding the boundary at positive times. -/
theorem sep_of_trace_mem_H {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    {ζ₀ : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ₀) (hw : Continuous w)
    (hη : IsGeneratingTrace w ⊤ η) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ₀) (hηt : η t ∈ H) :
    (∀ i, vL i t < w t) ∧ ∀ j, w t < vR j t := by
  have hη' := isLoewnerTrace_of_isGeneratingTrace hη
  have hW : Continuous fun s : ℝ => w s.toNNReal := hw.comp continuous_real_toNNReal
  have hW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simpa using hp.1
  have hF : extendFrom H (fwdMapInv (Ito.rpath w) t) ((0 : ℝ) : ℂ) ∈ H := by
    rw [Complex.ofReal_zero]
    have := ZhanGT4.extendFrom_zero_eq hη' hW hW0 t.coe_nonneg
    simp only [Real.toNNReal_coe] at this
    change extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) t) 0 ∈ H
    rw [this]; exact hηt
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have := WangWu.vL_sub_lt_of_extendFrom_mem_H hp hw hη' ht hF i
    linarith
  · have := WangWu.lt_vR_sub_of_extendFrom_mem_H hp hw hη' ht hF j
    linarith

end Sec5

end InteractingSLE
