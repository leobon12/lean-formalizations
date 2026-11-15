/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.OneForceSwallow

/-!
# Lifting a terminal cluster point through a restart, one force (Part B.2, (E8))

Packet PROVE-ZHAN-GT4-B3. Source: Astra, *Follow-up proofs*, §B.2 L1127–L1150 (ruling R38): "The stopping-time collar
gives
a relative neighborhood of every point of `(a, b)` inside `L_T`. No later trace can enter those neighborhoods. A cluster
point on `(−∞, a]` would have a mapped future cluster point at or to the left of `c − ξ_T` … Here the inverse-boundary
assertion of the stopping-time theorem is also used." (Additional note, Lemma 3.2, L1434–L1450, ruling R39.)

`exists_cluster_lift` is GT4-B2's lifting lemma (`exists_band_cluster`) without the two-sided bands: with the inverse
boundary interior at `T` ((G5)), a terminal cluster point `x ∈ ℝ` of the trace is the limit of real points `x'_n`
alive at
`T` whose centred images converge to a real terminal cluster point `y` of the restarted trace. For one left force at
`p < 0`, if every point of `(0, x₀]` is swallowed by `T` and `x < x₀`, the `x'_n` are eventually negative, and the
same-side contraction of real flows (`band_of_isForwardSol_neg`) gives `|y − (V_T − W_T)| ≤ |x − p|`
(`exists_cluster_near_mark`). No extremal length is needed.

## Main results

* `exists_cluster_lift`: the lifting lemma.
* `abs_re_sub_le_of_isForwardSol_neg`: `|f_T(x') − f_T(p)| ≤ |x' − p|` for alive `x', p < 0`.
* `exists_cluster_near_mark`: the one-force band.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper

section Lift

variable {w : ℝ≥0 → ℝ}

/-- **Lifting a terminal cluster point through a restart** (B.2 L1127–L1150). Let `η` generate the chain of a continuous
driver `w` on `[0, ∞)`, `η₂` that of the driver restarted at `T`, and let the inverse boundary at `T` be interior
((G5)).
Every real terminal cluster point `x` of `η` is the limit of real points `x'_n` alive at `T` whose centred images
`f_T(x'_n)` converge to a real terminal cluster point `y` of `η₂`. -/
theorem exists_cluster_lift (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) {T : ℝ≥0} {η₂ : ℝ≥0 → ℂ}
    (hη₂ : IsGeneratingTrace (Sec7.shiftNN w T) ⊤ η₂)
    (hG5 : HasInteriorInverseBoundary (fun s : ℝ => w s.toNNReal) T) {x : ℝ} (hcl : IsTermCluster η x) :
    ∃ y : ℝ, IsTermCluster η₂ y ∧ ∃ x' : ℕ → ℝ,
      (∀ n, ∃ v, IsForwardSol (fun s : ℝ => w s.toNNReal) (x' n : ℂ) T v) ∧ Tendsto x' atTop (𝓝 x) ∧
        Tendsto (fun n => (fwdMap (fun s : ℝ => w s.toNNReal) T (x' n)).re) atTop (𝓝 y) := by
  set Wr : ℝ → ℝ := fun s : ℝ => w s.toNNReal with hWr
  have hWrc : Continuous Wr := hw.comp continuous_real_toNNReal
  have hWr0 : Wr 0 = 0 := by simp [hWr, hw0]
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  -- the extension `F̄_T` and the join
  have hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ⊤} := hw.continuousOn
  have h₁ := Sec7.IsGeneratingTrace.isGeneratingTraceIcc hη hwc hw0 (σ := T) ENNReal.coe_lt_top
  have hσt₂ : (T : ℝ) < (T : ℝ) + 1 := lt_add_one _
  have hfc : Continuous (frozenDrive w ((T : ℝ) + 1)) := continuous_frozenDrive hw.continuousOn
  obtain ⟨hF, -, hEq, hcont, -, ⟨C, hC⟩, -⟩ := h₁.extend_props hσt₂ hfc hw0
  set Fb := extendFrom H (fwdMapInv (frozenDrive w ((T : ℝ) + 1)) T) with hFb
  have hEq' : EqOn Fb (fwdMapInv Wr T) H := fun z hz => by rw [hEq hz, hF]
  have hwc' : ContinuousOn w {s | (s : ℝ≥0∞) < (T : ℝ≥0∞) + ⊤} := by rw [add_top]; exact hwc
  obtain ⟨hjoin, -⟩ := h₁.join hwc' hw0 hη₂
  rw [add_top] at hjoin
  have hjoinF : ∀ t : ℝ≥0, T < t → η t = Fb (η₂ (t - T)) := by
    intro t ht
    rw [hη.eq_of_le hjoin hwc hw0 le_top, Sec7.joinTrace_of_lt ht, hF]
  have hw₂ : Continuous fun s : ℝ => Sec7.shiftNN w T s.toNNReal := by
    unfold Sec7.shiftNN
    exact ((hw.comp (continuous_const.add continuous_id)).sub continuous_const).comp continuous_real_toNNReal
  have hη₂H : ∀ s, η₂ s ∈ Hbar := fun s =>
    Sec4.im_nonneg_of_isGeneratingTrace hw₂ (Sec7.shiftNN_zero w T) hη₂ s
  have hf0 : frozenDrive w ((T : ℝ) + 1) 0 = 0 := by
    simp [frozenDrive, min_eq_left (show (0 : ℝ) ≤ (T : ℝ) + 1 by positivity), hw0]
  have hFbH : ∀ z ∈ H, Fb z ∈ H := fun z hz => by
    rw [hEq hz]
    exact QuantumZipper.RS.fwdMapInv_mem_H hfc hf0 T.coe_nonneg hz
  -- Step 1: `x` is a terminal cluster point of `F̄ ∘ η₂`
  have hcl₂ : MapClusterPt (x : ℂ) atTop fun s => Fb (η₂ s) := by
    rw [IsTermCluster, mapClusterPt_iff_frequently] at hcl
    rw [mapClusterPt_iff_frequently]
    intro S hS
    have h1 : ∃ᶠ t in atTop, Fb (η₂ (t - T)) ∈ S := by
      refine (hcl S hS).mp ((eventually_gt_atTop T).mono fun t ht h => ?_)
      rwa [← hjoinF t ht]
    have htend : Tendsto (fun t : ℝ≥0 => t - T) atTop atTop :=
      tendsto_atTop.2 fun b => (eventually_ge_atTop (b + T)).mono fun t ht =>
        le_tsub_of_add_le_right ht
    exact htend.frequently h1
  -- Step 2: compactness gives a cluster point `y` of `η₂` with `F̄ y = x`
  have hseq : ∀ n : ℕ, ∃ s : ℝ≥0, (n : ℝ≥0) ≤ s ∧ ‖Fb (η₂ s) - x‖ < 1 / ((n : ℝ) + 1) := fun n => by
    have hb := mapClusterPt_iff_frequently.1 hcl₂ _
      (ball_mem_nhds (x : ℂ) (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
    obtain ⟨s, hs1, hs2⟩ := (hb.and_eventually (eventually_ge_atTop (n : ℝ≥0))).exists
    exact ⟨s, hs2, by rwa [mem_ball, dist_eq_norm] at hs1⟩
  choose s hs using hseq
  set K : Set ℂ := closedBall (0 : ℂ) (‖(x : ℂ)‖ + 1 + C) ∩ Hbar with hK
  have hHbc : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_right hHbc
  have hyK : ∀ n, η₂ (s n) ∈ K := fun n => by
    refine ⟨?_, hη₂H _⟩
    rw [mem_closedBall, dist_zero_right]
    have h1 := hC _ (hη₂H (s n))
    have h2 := (hs n).2
    have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    calc ‖η₂ (s n)‖ ≤ ‖(x : ℂ)‖ + ‖Fb (η₂ (s n)) - x‖ + ‖Fb (η₂ (s n)) - η₂ (s n)‖ := by
          have e : η₂ (s n) = x + (Fb (η₂ (s n)) - x) - (Fb (η₂ (s n)) - η₂ (s n)) := by ring
          calc ‖η₂ (s n)‖ = ‖(x : ℂ) + (Fb (η₂ (s n)) - x) - (Fb (η₂ (s n)) - η₂ (s n))‖ := by
                rw [← e]
            _ ≤ ‖(x : ℂ) + (Fb (η₂ (s n)) - x)‖ + ‖Fb (η₂ (s n)) - η₂ (s n)‖ := norm_sub_le _ _
            _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖(x : ℂ)‖ + 1 + C := by linarith
  obtain ⟨y, hyKm, φ, hφ, hlim⟩ := hKc.tendsto_subseq hyK
  have hsφ : Tendsto (fun n => s (φ n)) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    obtain ⟨m, hm⟩ := exists_nat_ge (b : ℝ)
    refine (eventually_ge_atTop m).mono fun n hn => ?_
    have h1 : (m : ℝ≥0) ≤ (φ n : ℝ≥0) := by exact_mod_cast hn.trans (hφ.id_le n)
    rw [← NNReal.coe_le_coe] at h1 ⊢
    exact hm.trans (h1.trans (by exact_mod_cast (hs (φ n)).1))
  have hcly : IsTermCluster η₂ y := MapClusterPt.of_comp hsφ hlim.mapClusterPt
  have hFy : Fb y = x := by
    have hA : Tendsto (fun n => Fb (η₂ (s (φ n)))) atTop (𝓝 (Fb y)) :=
      (hcont y hyKm.2).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hη₂H _⟩)
    have hB : Tendsto (fun n => Fb (η₂ (s (φ n)))) atTop (𝓝 (x : ℂ)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ((hs (φ n)).2).le.trans ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      have : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    exact tendsto_nhds_unique hA hB
  -- Step 3: `y` is real
  have hyim : y.im = 0 := by
    rcases (show 0 ≤ y.im from hyKm.2).lt_or_eq with hpos | hzero
    · have := hFbH y hpos
      rw [hFy] at this
      exact absurd this (by simp [H])
    · exact hzero.symm
  have hyr : y = (y.re : ℂ) := Complex.ext (by simp) (by simp [hyim])
  -- Step 4: `y` lies in the exterior coordinates
  have hyext : y.re ∈ exteriorCoords Wr T := by
    by_contra hne
    obtain ⟨p, hpH, hp⟩ := hG5 y.re hne
    have := FiniteEndpoint.neBot_nhdsWithin_H (z := ((y.re : ℝ) : ℂ)) (by simp)
    have h1 : Tendsto Fb (𝓝[H] ((y.re : ℝ) : ℂ)) (𝓝 (x : ℂ)) := by
      rw [← hyr, ← hFy]
      exact ((hcont y hyKm.2).mono fun z (hz : 0 < z.im) => le_of_lt hz).tendsto
    have h2 : Tendsto Fb (𝓝[H] ((y.re : ℝ) : ℂ)) (𝓝 p) :=
      hp.congr' (eventually_nhdsWithin_of_forall fun z hz => (hEq' hz).symm)
    have := tendsto_nhds_unique h1 h2
    rw [← this] at hpH
    exact absurd hpH (by simp [H])
  -- Step 5: the band
  obtain ⟨r, hrS, hr⟩ := mem_closure_iff_seq_limit.1 hyext
  choose x' hx'alive hx'r using hrS
  choose v hv using hx'alive
  have hFx' : ∀ n, Fb (r n) = x' n := fun n => by
    have h := extension_fwdMap_eq_of_isForwardSol hWrc hWr0 hT0 hEq' hcont (hv n)
    rwa [fwdMap_eq_ofReal_re hWrc (hv n) ⟨hT0, le_rfl⟩, hx'r n] at h
  have hx'lim : Tendsto x' atTop (𝓝 x) := by
    have hc : Tendsto (fun n => ((r n : ℝ) : ℂ)) atTop (𝓝 y) := by
      rw [hyr]; exact (Complex.continuous_ofReal.tendsto _).comp hr
    have h := (hcont y hyKm.2).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hc, Eventually.of_forall fun n => show (0 : ℝ) ≤ ((r n : ℝ) : ℂ).im by simp⟩)
    rw [hFy] at h
    have h' : Tendsto (fun n => ((x' n : ℝ) : ℂ)) atTop (𝓝 (x : ℂ)) :=
      h.congr fun n => by simp only [Function.comp_apply, hFx' n]
    exact (Complex.continuous_re.tendsto _).comp h' |>.congr (fun n => by simp) |>.trans (by simp)
  refine ⟨y.re, by rw [← hyr]; exact hcly, x', fun n => ⟨v n, hv n⟩, hx'lim, ?_⟩
  exact hr.congr fun n => (hx'r n).symm

end Lift

/-! ### The one-force band -/

section Band

variable {W : ℝ → ℝ}

/-- **Same-side contraction**, both orders: for `p, x' < 0` alive at `T`, `|f_T(x') − f_T(p)| ≤ |x' − p|`. -/
theorem abs_re_sub_le_of_isForwardSol_neg (hW : Continuous W) (hW0 : W 0 = 0) {p x' T : ℝ} (hT : 0 ≤ T)
    (hp : p < 0) (hx' : x' < 0) {u v : ℝ → ℂ} (hu : IsForwardSol W (p : ℂ) T u)
    (hv : IsForwardSol W (x' : ℂ) T v) : |(fwdMap W T x').re - (fwdMap W T p).re| ≤ |x' - p| := by
  rcases lt_trichotomy p x' with h | rfl | h
  · obtain ⟨h1, h2⟩ := band_of_isForwardSol_neg hW hW0 hT hx' h hu hv
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith
  · simp
  · obtain ⟨h1, h2⟩ := band_of_isForwardSol_neg hW hW0 hT hp h hv hu
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
    linarith

end Band

section NearMark

variable {w : ℝ≥0 → ℝ}

/-- **The one-force band** (B.2 L1127–L1150; additional note L1442–L1450). Let a continuous driver `w` (`w 0 = 0`) carry
one force point `v < w` started at `p < 0` (the integrated equation (1.11)), let (G5) hold at `T`, and let every point
of
`(0, x₀]` be swallowed by `T`. Then every terminal cluster point `x < x₀` of the trace lifts to a real terminal cluster
point `y` of the trace restarted at `T` with `|y − (v_T − w_T)| ≤ |x − p|`; moreover `x ≤ 0`. -/
theorem exists_cluster_near_mark (hw : Continuous w) (hw0 : w 0 = 0) {v : ℝ≥0 → ℝ} (hv : Continuous v)
    (hsep : ∀ t, v t < w t) {p : ℝ} (hp : p < 0)
    (hveq : ∀ t : ℝ≥0, v t = p + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η) {T : ℝ≥0} {η₂ : ℝ≥0 → ℂ}
    (hη₂ : IsGeneratingTrace (Sec7.shiftNN w T) ⊤ η₂)
    (hG5 : HasInteriorInverseBoundary (fun s : ℝ => w s.toNNReal) T) {x₀ : ℝ}
    (hdead : ∀ x' ∈ Ioc (0 : ℝ) x₀, ¬ ∃ u, IsForwardSol (fun s : ℝ => w s.toNNReal) (x' : ℂ) T u)
    {x : ℝ} (hx : x < x₀) (hcl : IsTermCluster η x) :
    x ≤ 0 ∧ ∃ y : ℝ, IsTermCluster η₂ y ∧ |y - (v T - w T)| ≤ |x - p| := by
  set Wr : ℝ → ℝ := fun s : ℝ => w s.toNNReal with hWr
  have hWrc : Continuous Wr := hw.comp continuous_real_toNNReal
  have hWr0 : Wr 0 = 0 := by simp [hWr, hw0]
  obtain ⟨y, hy, x', halive, hlim, himg⟩ := exists_cluster_lift hw hw0 hη hη₂ hG5 hcl
  have huL := isForwardSol_of_force hw hv (fun t => (hsep t).ne) hveq T
  have hfL : (fwdMap Wr T p).re = v T - w T := by
    rw [fwdMap_eq_of_isForwardSol hWrc huL ⟨T.coe_nonneg, le_rfl⟩]
    simp
  have hnegev : ∀ᶠ n in atTop, x' n < 0 := by
    filter_upwards [hlim (Iio_mem_nhds hx)] with n hn
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hpos | hzero
    · exact hdead (x' n) ⟨hpos, (show x' n < x₀ from hn).le⟩ (halive n)
    · obtain ⟨u, hu⟩ := halive n
      rw [← hzero] at hu
      exact not_isForwardSol_zero hWr0 T.coe_nonneg hu
  refine ⟨le_of_tendsto hlim (hnegev.mono fun n hn => hn.le), y, hy, ?_⟩
  have hev : ∀ᶠ n in atTop, |(fwdMap Wr T (x' n)).re - (v T - w T)| ≤ |x' n - p| := by
    filter_upwards [hnegev] with n hneg
    obtain ⟨u, hu⟩ := halive n
    rw [← hfL]
    exact abs_re_sub_le_of_isForwardSol_neg hWrc hWr0 T.coe_nonneg hp hneg huL hu
  exact le_of_tendsto_of_tendsto ((himg.sub_const _).abs) ((hlim.sub_const p).abs) hev

end NearMark

end InteractingSLE.ZhanGT4
