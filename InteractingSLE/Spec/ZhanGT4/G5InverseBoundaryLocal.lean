/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.NoCluster
import InteractingSLE.Spec.ZhanGT4.A5Det

/-!
# (G5) localized: the real points at which the interior inverse boundary is used

Packet PROVE-ZHAN-G5. Part A's (G5) (`HasInteriorInverseBoundary W T`, `f_T((c, d)) ⊂ ℍ`) enters every consumer of
`StoppingInverseBoundaryStatement` through one deterministic step: the lifting lemma `exists_band_cluster` (and its
one-force twin), applied at a restart time `T` to a real terminal cluster point `x` of the trace. There it is used for
the single point `x` only: a real `u` off the exterior coordinates must not have `x` as a boundary value of `F_T`.

This file isolates that pointwise property (`NoInteriorPreimage W T x`) and shows exactly when it needs (G5):

* (G5) gives it at every real point (`HasInteriorInverseBoundary.noInteriorPreimage`), and conversely, for a driver
  whose inverse map extends continuously to `ℍ̄` (every driver with a continuous trace), (G5) at `T` **is** the
  conjunction over all real `x` (`hasInteriorInverseBoundary_iff_forall_noInteriorPreimage`).
* It holds **without (G5)** at every real point alive at `T` (`noInteriorPreimage_of_isForwardSol`: an alive point has
  the single boundary coordinate `f_T(x)`) and at every point with a relative `ℍ`-collar in `K_T`
  (`noInteriorPreimage_of_collar`).
* So it can fail only at a real point that is swallowed by `T` and lies on the frontier of `ℍ \ K_T`
  (`isSwallowedBy_of_not_noInteriorPreimage`, `frequently_notMem_fwdHull_of_not_noInteriorPreimage`) — a real frontier
  point inside the swallowed interval, the "pocket" points of the handoff (`planning/handoffs/PROVE-ZHAN-G5.md`).
* A point collared at some time is never a terminal cluster point (`not_isTermCluster_of_collar`).
* The lifting lemma and the pathwise restart step hold with the pointwise hypothesis at the cluster point
  (`exists_band_cluster_of_noInteriorPreimage`, `bandEvent_of_cluster_of_noInteriorPreimage`); in particular a
  terminal cluster point that is alive at the restart time needs no (G5) at all (`exists_band_cluster_of_isForwardSol`,
  `bandEvent_of_cluster_of_isForwardSol`).

The handoff explains why the remaining case (swallowed real frontier points, at a deterministic or a stopping time) is
not reachable by a pathwise argument: a deterministic continuous Loewner chain can have its tip in `ℍ` and a real
frontier point strictly inside the swallowed interval, and for `SLE_κ`, `κ > 4`, excluding such points at a fixed
time is a critical intersection statement.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper

/-! ### The pointwise property -/

section Pointwise

variable {W : ℝ → ℝ}

/-- **`x` has no interior inverse preimage at time `T`**: no real point `u` off the exterior coordinates (the open
inverse interval `(c − W_T, d − W_T)`) has `x` as a boundary value of the centred inverse map `F_T`. (G5) at `T` is
this property at every real `x` (`hasInteriorInverseBoundary_iff_forall_noInteriorPreimage`). -/
def NoInteriorPreimage (W : ℝ → ℝ) (T : ℝ) (x : ℂ) : Prop :=
  ∀ u : ℝ, u ∉ exteriorCoords W T → ¬ Tendsto (fwdMapInv W T) (𝓝[H] (u : ℂ)) (𝓝 x)

/-- **(G5) gives the pointwise property at every real point.** -/
theorem HasInteriorInverseBoundary.noInteriorPreimage {T : ℝ} (h : HasInteriorInverseBoundary W T) (x : ℝ) :
    NoInteriorPreimage W T x := by
  intro u hu hlim
  obtain ⟨p, hpH, hp⟩ := h u hu
  have := FiniteEndpoint.neBot_nhdsWithin_H (z := ((u : ℝ) : ℂ)) (by simp)
  have hpx : p = x := tendsto_nhds_unique hp hlim
  rw [hpx] at hpH
  have h2 : (0 : ℝ) < ((x : ℝ) : ℂ).im := hpH
  simp at h2

/-- `F_T` tends to `x` within `ℍ` whenever it tends to `x`: it maps `ℍ` into `ℍ`. -/
theorem tendsto_fwdMapInv_nhdsWithin_H (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {u x : ℂ} (hlim : Tendsto (fwdMapInv W T) (𝓝[H] u) (𝓝 x)) :
    Tendsto (fwdMapInv W T) (𝓝[H] u) (𝓝[H] x) :=
  tendsto_nhdsWithin_iff.2 ⟨hlim, eventually_nhdsWithin_of_forall fun _ hz =>
    (RS.fwdMapInv_mem_compl_fwdHull hW hW0 hT hz).1⟩

/-- **An alive real point has no interior inverse preimage** (no (G5) needed): if `F_T(z) → x` as `z → u` within `ℍ`
and `x` is alive at `T`, then `f_T(F_T(z)) = z` tends both to `u` and to `f_T(x)` (the boundary value of `f_T` at an
alive point, `tendsto_fwdMap_of_isForwardSol`), so `u = f_T(x)` is an exterior coordinate. -/
theorem noInteriorPreimage_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) {x : ℝ}
    {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) T v) : NoInteriorPreimage W T x := by
  intro u hu hlim
  apply hu
  have := FiniteEndpoint.neBot_nhdsWithin_H (z := ((u : ℝ) : ℂ)) (by simp)
  have h1 : Tendsto (fun z => fwdMap W T (fwdMapInv W T z)) (𝓝[H] (u : ℂ)) (𝓝 (v T)) :=
    (tendsto_fwdMap_of_isForwardSol hW hT hv).comp (tendsto_fwdMapInv_nhdsWithin_H hW hW0 hT hlim)
  have h2 : Tendsto (fun z => fwdMap W T (fwdMapInv W T z)) (𝓝[H] (u : ℂ)) (𝓝 (u : ℂ)) := by
    refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (RS.fwdMap_fwdMapInv hW hW0 hT hz).symm
  have hvu : v T = u := tendsto_nhds_unique h1 h2
  have hval : fwdMap W T x = v T := fwdMap_eq_of_isForwardSol hW hv ⟨hT, le_rfl⟩
  refine subset_closure ⟨x, ⟨v, hv⟩, ?_⟩
  rw [hval, hvu]
  simp

/-- **A collared point has no interior inverse preimage**: `F_T` takes values in `ℍ \ K_T`, which does not come near a
point with a relative `ℍ`-neighbourhood in `K_T`. -/
theorem noInteriorPreimage_of_collar (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) {x : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hcol : ∀ w ∈ H, ‖w - x‖ < ε → w ∈ fwdHull W T) : NoInteriorPreimage W T x := by
  intro u hu hlim
  have := FiniteEndpoint.neBot_nhdsWithin_H (z := ((u : ℝ) : ℂ)) (by simp)
  have hev : ∀ᶠ z in 𝓝[H] ((u : ℝ) : ℂ), fwdMapInv W T z ∈ ball x ε := hlim (ball_mem_nhds x hε)
  obtain ⟨z, hz, hzH⟩ := (hev.and self_mem_nhdsWithin).exists
  have hm := RS.fwdMapInv_mem_compl_fwdHull hW hW0 hT hzH
  rw [mem_ball, dist_eq_norm] at hz
  exact hm.2 (hcol _ hm.1 hz)

/-- **Where the pointwise property can fail, the point is swallowed**: a real point without the property at `T` is not
alive at `T`. -/
theorem isSwallowedBy_of_not_noInteriorPreimage (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) {x : ℝ}
    (h : ¬ NoInteriorPreimage W T x) : IsSwallowedBy W x T :=
  fun ⟨_, hv⟩ => h (noInteriorPreimage_of_isForwardSol hW hW0 hT hv)

/-- **… and it lies on the frontier of `ℍ \ K_T`**: every relative `ℍ`-neighbourhood of a point without the property
meets `ℍ \ K_T`. -/
theorem frequently_notMem_fwdHull_of_not_noInteriorPreimage (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 ≤ T) {x : ℂ} (h : ¬ NoInteriorPreimage W T x) :
    ∀ ε > (0 : ℝ), ∃ w ∈ H, ‖w - x‖ < ε ∧ w ∉ fwdHull W T := by
  intro ε hε
  by_contra hcon
  push Not at hcon
  exact h (noInteriorPreimage_of_collar hW hW0 hT hε hcon)

/-- **(G5) is the pointwise property at every real point**, for a driver whose centred inverse map `F_T` has a
continuous extension `F̄` to `ℍ̄` (Carathéodory–Torhorst; every driver with a continuous trace). At a real `u` the
boundary value `F̄(u)` exists and lies in `ℍ̄`; (G5) asks it to lie in `ℍ`, the pointwise property forbids it to be
real. -/
theorem hasInteriorInverseBoundary_iff_forall_noInteriorPreimage {T : ℝ} {F : ℂ → ℂ}
    (hFeq : EqOn F (fwdMapInv W T) H) (hFc : ContinuousOn F Hbar)
    (hFH : ∀ z ∈ H, fwdMapInv W T z ∈ H) :
    HasInteriorInverseBoundary W T ↔ ∀ x : ℝ, NoInteriorPreimage W T x := by
  refine ⟨fun h x => h.noInteriorPreimage x, fun h u hu => ?_⟩
  have huH : ((u : ℝ) : ℂ) ∈ Hbar := by
    show (0 : ℝ) ≤ ((u : ℝ) : ℂ).im
    simp
  have := FiniteEndpoint.neBot_nhdsWithin_H (z := ((u : ℝ) : ℂ)) (by simp)
  have hlim : Tendsto (fwdMapInv W T) (𝓝[H] (u : ℂ)) (𝓝 (F u)) :=
    ((hFc _ huH).tendsto.mono_left (nhdsWithin_mono _ H_subset_Hbar)).congr'
      (eventually_nhdsWithin_of_forall fun z hz => hFeq hz)
  have hFu : F u ∈ Hbar :=
    isClosed_Hbar.mem_of_tendsto hlim (eventually_nhdsWithin_of_forall fun z hz => H_subset_Hbar (hFH z hz))
  rcases (show (0 : ℝ) ≤ (F u).im from hFu).lt_or_eq with hpos | hzero
  · exact ⟨F u, hpos, hlim⟩
  · exfalso
    have hr : F u = (((F u).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← hzero])
    exact h (F u).re u hu (hr ▸ hlim)

/-- **(G5) is the pointwise property at every real point, for a driver with a continuous trace** (the extension of
`IsLoewnerTraceLT.exists_extension`). -/
theorem hasInteriorInverseBoundary_iff_of_isLoewnerTrace {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) :
    HasInteriorInverseBoundary W T ↔ ∀ x : ℝ, NoInteriorPreimage W T x := by
  have hLT : IsLoewnerTraceLT W (T + 1) η :=
    ⟨hη.1, hη.2.1.mono Ico_subset_Ici_self, fun t ht _ => hη.2.2 t ht⟩
  obtain ⟨F, hFeq, hFc, -⟩ := hLT.exists_extension hW hW0 hT (by linarith)
  exact hasInteriorInverseBoundary_iff_forall_noInteriorPreimage hFeq hFc
    fun z hz => RS.fwdMapInv_mem_H hW hW0 hT hz

end Pointwise


/-! ### Collared points are not terminal cluster points -/

section Cluster

variable {w : ℝ≥0 → ℝ}

/-- **A point with a relative `ℍ`-collar in some `K_t` is not a terminal cluster point** of a generating trace on
`[0, ∞)`: after `t` the trace stays in `closure (ℍ \ K_s) ⊆ closure (ℍ \ K_t)`, which avoids the collar. -/
theorem not_isTermCluster_of_collar (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) {t : ℝ≥0} {x : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hcol : ∀ z ∈ H, ‖z - x‖ < ε → z ∈ fwdHull (fun r : ℝ => w r.toNNReal) t) : ¬ IsTermCluster η x := by
  have hWrc : Continuous fun r : ℝ => w r.toNNReal := hw.comp continuous_real_toNNReal
  have hWr0 : (fun r : ℝ => w r.toNNReal) 0 = 0 := by simp [hw0]
  rw [isTermCluster_iff_not, not_not]
  refine ⟨ε / 2, half_pos hε, (eventually_ge_atTop t).mono fun s hts => ?_⟩
  have htip := hη.tendsto_fwdMapInv_tip hw.continuousOn hw0 (t := s) ENNReal.coe_lt_top
  have := FiniteEndpoint.neBot_nhdsWithin_H (z := (0 : ℂ)) (by simp)
  have hcl : η s ∈ closure (H \ fwdHull (fun r : ℝ => w r.toNNReal) s) :=
    mem_closure_of_tendsto htip (eventually_nhdsWithin_of_forall fun z hz =>
      RS.fwdMapInv_mem_compl_fwdHull hWrc hWr0 s.coe_nonneg hz)
  by_contra hlt
  push Not at hlt
  obtain ⟨z, hzK, hzd⟩ := Metric.mem_closure_iff.1 hcl (ε / 2) (half_pos hε)
  have hzx : ‖z - x‖ < ε := by
    rw [dist_eq_norm] at hzd
    calc ‖z - x‖ = ‖(η s - x) - (η s - z)‖ := by ring_nf
      _ ≤ ‖η s - x‖ + ‖η s - z‖ := norm_sub_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hlt hzd
      _ = ε := add_halves ε
  exact hzK.2 ((QuantumZipper.fwdHull_mono).1 (show (t : ℝ) ≤ s by exact_mod_cast hts) (hcol z hzK.1 hzx))

end Cluster

/-! ### The lifting lemma and the restart step with the pointwise hypothesis -/

section Lift

variable {w : ℝ≥0 → ℝ}

/-- **The lifting lemma with (G5) only at the cluster point** (`exists_band_cluster` with
`HasInteriorInverseBoundary … T` replaced by `NoInteriorPreimage … T x`; the proof is the same, Step 4 uses only the
point `x`). -/
theorem exists_band_cluster_of_noInteriorPreimage (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) {T : ℝ≥0} {η₂ : ℝ≥0 → ℂ}
    (hη₂ : IsGeneratingTrace (Sec7.shiftNN w T) ⊤ η₂)
    {pL pR : ℝ} {uL uR : ℝ → ℂ}
    (huL : IsForwardSol (fun s : ℝ => w s.toNNReal) (pL : ℂ) T uL)
    (huR : IsForwardSol (fun s : ℝ => w s.toNNReal) (pR : ℂ) T uR) {x : ℝ} (hxL : pL < x)
    (hxR : x < pR) (hcl : IsTermCluster η x)
    (hNI : NoInteriorPreimage (fun s : ℝ => w s.toNNReal) T x) :
    ∃ y : ℝ, IsTermCluster η₂ y ∧
      (y ∈ Icc (fwdMap (fun s : ℝ => w s.toNNReal) T pL).re
          ((fwdMap (fun s : ℝ => w s.toNNReal) T pL).re - pL) ∨
        y ∈ Icc ((fwdMap (fun s : ℝ => w s.toNNReal) T pR).re - pR)
          (fwdMap (fun s : ℝ => w s.toNNReal) T pR).re) := by
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
    refine hNI y.re hne ?_
    have h1 : Tendsto Fb (𝓝[H] ((y.re : ℝ) : ℂ)) (𝓝 (x : ℂ)) := by
      rw [← hyr, ← hFy]
      exact ((hcont y hyKm.2).mono fun z (hz : 0 < z.im) => le_of_lt hz).tendsto
    exact h1.congr' (eventually_nhdsWithin_of_forall fun z hz => hEq' hz)
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
  have hB : IsClosed (Icc (fwdMap Wr T pL).re ((fwdMap Wr T pL).re - pL) ∪
      Icc ((fwdMap Wr T pR).re - pR) (fwdMap Wr T pR).re) := isClosed_Icc.union isClosed_Icc
  have hev : ∀ᶠ n in atTop, r n ∈ Icc (fwdMap Wr T pL).re ((fwdMap Wr T pL).re - pL) ∪
      Icc ((fwdMap Wr T pR).re - pR) (fwdMap Wr T pR).re := by
    filter_upwards [hx'lim (Ioo_mem_nhds hxL hxR)] with n hn
    rw [← hx'r n]
    rcases lt_trichotomy (x' n) 0 with hneg | hzero | hpos
    · obtain ⟨h1, h2⟩ := band_of_isForwardSol_neg hWrc hWr0 hT0 hneg hn.1 huL (hv n)
      exact Or.inl ⟨h1.le, by linarith⟩
    · exact absurd (hzero ▸ hv n) (not_isForwardSol_zero hWr0 hT0)
    · obtain ⟨h1, h2⟩ := band_of_isForwardSol_pos hWrc hWr0 hT0 hpos hn.2 huR (hv n)
      exact Or.inr ⟨by linarith, h2.le⟩
  refine ⟨y.re, by rw [← hyr]; exact hcly, hB.mem_of_tendsto hr hev⟩

/-- **An alive terminal cluster point lifts into the bands without (G5)**: if the cluster point `x` is alive at the
restart time `T`, the lifting lemma holds with no hypothesis on the inverse boundary. -/
theorem exists_band_cluster_of_isForwardSol (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) {T : ℝ≥0} {η₂ : ℝ≥0 → ℂ}
    (hη₂ : IsGeneratingTrace (Sec7.shiftNN w T) ⊤ η₂) {pL pR : ℝ} {uL uR : ℝ → ℂ}
    (huL : IsForwardSol (fun s : ℝ => w s.toNNReal) (pL : ℂ) T uL)
    (huR : IsForwardSol (fun s : ℝ => w s.toNNReal) (pR : ℂ) T uR) {x : ℝ} (hxL : pL < x)
    (hxR : x < pR) (hcl : IsTermCluster η x) {v : ℝ → ℂ}
    (hv : IsForwardSol (fun s : ℝ => w s.toNNReal) (x : ℂ) T v) :
    ∃ y : ℝ, IsTermCluster η₂ y ∧
      (y ∈ Icc (fwdMap (fun s : ℝ => w s.toNNReal) T pL).re
          ((fwdMap (fun s : ℝ => w s.toNNReal) T pL).re - pL) ∨
        y ∈ Icc ((fwdMap (fun s : ℝ => w s.toNNReal) T pR).re - pR)
          (fwdMap (fun s : ℝ => w s.toNNReal) T pR).re) :=
  exists_band_cluster_of_noInteriorPreimage hw hw0 hη hη₂ huL huR hxL hxR hcl
    (noInteriorPreimage_of_isForwardSol (hw.comp continuous_real_toNNReal) (by simp [hw0]) T.coe_nonneg hv)

end Lift

/-- **The pathwise restart step with (G5) only at the cluster point** (`bandEvent_of_cluster` with
`HasInteriorInverseBoundary … m` replaced by `NoInteriorPreimage … m x`). -/
theorem bandEvent_of_cluster_of_noInteriorPreimage {w vL vR : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) (hl : Continuous vL)
    (hr : Continuous vR) (hsL : ∀ t, vL t < w t) (hsR : ∀ t, w t < vR t) {pL pR : ℝ} (hpL : pL < 0)
    (hpR : 0 < pR) (hLeq : ∀ t : ℝ≥0, vL t = pL + ∫ s in (0 : ℝ)..t, 2 / (vL s.toNNReal - w s.toNNReal))
    (hReq : ∀ t : ℝ≥0, vR t = pR + ∫ s in (0 : ℝ)..t, 2 / (vR s.toNNReal - w s.toNNReal))
    {θ : ℝ} (hθ : 0 < θ) {m : ℝ≥0} (hsep : ((pR - pL) / θ) ^ 2 ≤ (vR m - vL m) ^ 2)
    (hratio : vR m - w m = pR / (-pL) * (w m - vL m)) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η)
    {η₂ : ℝ≥0 → ℂ} (hη₂ : IsGeneratingTrace (Sec7.shiftNN w m) ⊤ η₂)
    {x : ℝ} (hxL : pL < x) (hxR : x < pR) (hcl : IsTermCluster η x)
    (hNI : NoInteriorPreimage (fun s : ℝ => w s.toNNReal) m x) :
    BandEvent θ ((fun _ => vL m - w m), fun _ => vR m - w m) (Sec7.shiftNN w m) ⊤ := by
  have hWrc : Continuous fun s : ℝ => w s.toNNReal := hw.comp continuous_real_toNNReal
  have huL := isForwardSol_of_force hw hl (fun t => (hsL t).ne) hLeq m
  have huR := isForwardSol_of_force hw hr (fun t => (hsR t).ne') hReq m
  have hfL : (fwdMap (fun s : ℝ => w s.toNNReal) m pL).re = vL m - w m := by
    rw [fwdMap_eq_of_isForwardSol hWrc huL ⟨m.coe_nonneg, le_rfl⟩]
    simp
  have hfR : (fwdMap (fun s : ℝ => w s.toNNReal) m pR).re = vR m - w m := by
    rw [fwdMap_eq_of_isForwardSol hWrc huR ⟨m.coe_nonneg, le_rfl⟩]
    simp
  obtain ⟨y, hy, hband⟩ := exists_band_cluster_of_noInteriorPreimage hw hw0 hη hη₂ huL huR hxL hxR hcl hNI
  rw [hfL, hfR] at hband
  have hw₂ : Continuous (Sec7.shiftNN w m) := (hw.comp (continuous_const.add continuous_id)).sub continuous_const
  rw [bandEvent_top_iff hw₂ (Sec7.shiftNN_zero w m) hη₂]
  refine realBand_of_isTermCluster ?_ hy
  -- the bands of widths `−p_L`, `p_R` lie in the `θ`-bands
  set L := w m - vL m with hL
  set R := vR m - w m with hR
  have hL0 : 0 < L := sub_pos.2 (hsL m)
  have hR0 : 0 < R := sub_pos.2 (hsR m)
  have ha : 0 < -pL := neg_pos.2 hpL
  have hsep' : (pR - pL) / θ ≤ R + L := by
    have h1 : vR m - vL m = R + L := by rw [hR, hL]; ring
    rw [h1] at hsep
    exact (pow_le_pow_iff_left₀ (by have := sub_pos.2 (hpL.trans hpR); positivity) (by positivity)
      two_ne_zero).1 hsep
  have hRL : R = pR / (-pL) * L := hratio
  have hkey : -pL ≤ θ * L := by
    have hpL0 : pL ≠ 0 := hpL.ne
    have hD : 0 < pR - pL := by linarith
    have e : (-pL) * (R + L) = L * (pR - pL) := by rw [hRL]; field_simp; ring
    have h := (div_le_iff₀ hθ).1 hsep'
    have h5 : (-pL) * (pR - pL) ≤ (-pL) * ((R + L) * θ) := mul_le_mul_of_nonneg_left h ha.le
    have h6 : (-pL) * ((R + L) * θ) = θ * L * (pR - pL) := by rw [← mul_assoc, e]; ring
    rw [h6] at h5
    exact le_of_mul_le_mul_right (by linarith : (-pL) * (pR - pL) ≤ (θ * L) * (pR - pL)) hD
  rcases hband with h | h
  · left
    simp only
    refine ⟨h.1, h.2.trans ?_⟩
    show vL m - w m - pL ≤ (1 - θ) * (vL m - w m)
    have : vL m - w m = -L := by rw [hL]; ring
    rw [this]; linarith
  · right
    simp only
    refine ⟨le_trans ?_ h.1, h.2⟩
    show (1 - θ) * (vR m - w m) ≤ vR m - w m - pR
    rw [← hR]
    have h4 : pR ≤ θ * R := by
      rw [hRL]
      have := mul_le_mul_of_nonneg_left hkey (div_nonneg hpR.le ha.le)
      rw [div_mul_cancel₀ _ ha.ne'] at this
      have e : θ * (pR / -pL * L) = pR / -pL * (θ * L) := by ring
      linarith
    linarith

/-- **The pathwise restart step for a cluster point alive at the restart time**: no (G5). -/
theorem bandEvent_of_cluster_of_isForwardSol {w vL vR : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (hl : Continuous vL) (hr : Continuous vR) (hsL : ∀ t, vL t < w t) (hsR : ∀ t, w t < vR t) {pL pR : ℝ}
    (hpL : pL < 0) (hpR : 0 < pR)
    (hLeq : ∀ t : ℝ≥0, vL t = pL + ∫ s in (0 : ℝ)..t, 2 / (vL s.toNNReal - w s.toNNReal))
    (hReq : ∀ t : ℝ≥0, vR t = pR + ∫ s in (0 : ℝ)..t, 2 / (vR s.toNNReal - w s.toNNReal))
    {θ : ℝ} (hθ : 0 < θ) {m : ℝ≥0} (hsep : ((pR - pL) / θ) ^ 2 ≤ (vR m - vL m) ^ 2)
    (hratio : vR m - w m = pR / (-pL) * (w m - vL m)) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η)
    {η₂ : ℝ≥0 → ℂ} (hη₂ : IsGeneratingTrace (Sec7.shiftNN w m) ⊤ η₂) {x : ℝ} (hxL : pL < x) (hxR : x < pR)
    (hcl : IsTermCluster η x) {v : ℝ → ℂ} (hv : IsForwardSol (fun s : ℝ => w s.toNNReal) (x : ℂ) m v) :
    BandEvent θ ((fun _ => vL m - w m), fun _ => vR m - w m) (Sec7.shiftNN w m) ⊤ :=
  bandEvent_of_cluster_of_noInteriorPreimage hw hw0 hl hr hsL hsR hpL hpR hLeq hReq hθ hsep hratio hη hη₂ hxL hxR
    hcl (noInteriorPreimage_of_isForwardSol (hw.comp continuous_real_toNNReal) (by simp [hw0]) m.coe_nonneg hv)

/-- **The only cluster points needing (G5) at the restart time**: if the pointwise property fails at a terminal cluster
point `x` of the trace at time `T`, then `x` is swallowed by `T` and lies on the frontier of `ℍ \ K_T` (every relative
`ℍ`-neighbourhood of `x` meets `ℍ \ K_T`; a collar at `T` is excluded twice over, by `noInteriorPreimage_of_collar`
and by `not_isTermCluster_of_collar`). -/
theorem isSwallowedBy_frontier_of_not_noInteriorPreimage {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    {T : ℝ≥0} {x : ℝ} (h : ¬ NoInteriorPreimage (fun s : ℝ => w s.toNNReal) T x) :
    IsSwallowedBy (fun s : ℝ => w s.toNNReal) x T ∧
      ∀ ε > (0 : ℝ), ∃ z ∈ H, ‖z - x‖ < ε ∧ z ∉ fwdHull (fun s : ℝ => w s.toNNReal) T :=
  ⟨isSwallowedBy_of_not_noInteriorPreimage (hw.comp continuous_real_toNNReal) (by simp [hw0]) T.coe_nonneg h,
    frequently_notMem_fwdHull_of_not_noInteriorPreimage (hw.comp continuous_real_toNNReal) (by simp [hw0])
      T.coe_nonneg h⟩


/-! ### The remaining input in pointwise form -/

universe u

/-- **(G5) at deterministic rational times, pointwise form**: for ordinary `SLE_κ` and every rational `q > 0`, almost
surely no real point is a boundary value of `F_q` at a real point off the exterior coordinates (no real frontier point
of `ℍ \ K_q` is reached through the open inverse interval). -/
def DetNoInteriorPreimageStatement (κ : ℝ) : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓕 B P →
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, ∀ x : ℝ, NoInteriorPreimage (drive κ B ω) q x

/-- **The pointwise form is (G5) at deterministic rational times** (`κ > 0`: ordinary `SLE_κ` has a continuous trace,
so `hasInteriorInverseBoundary_iff_of_isLoewnerTrace` applies pathwise). -/
theorem detNoInteriorPreimageStatement_iff {κ : ℝ} (hκ : 0 < κ) :
    DetNoInteriorPreimageStatement.{u} κ ↔ DetInverseBoundaryStatement.{u} κ := by
  constructor
  · intro h Ω mΩ P _ 𝓕 B hB q hq
    have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq.le
    filter_upwards [h P 𝓕 B hB q hq, ae_isLoewnerTrace_sleTrace hB.1 hκ, hB.1.cont,
      hB.1.eval_zero_ae_eq_zero] with ω h5 hη hc h0
    exact (hasInteriorInverseBoundary_iff_of_isLoewnerTrace hη (drive_continuous hc) (drive_zero h0) hq').2 h5
  · intro h Ω mΩ P _ 𝓕 B hB q hq
    filter_upwards [h P 𝓕 B hB q hq] with ω h5 x
    exact h5.noInteriorPreimage x

end InteractingSLE.ZhanGT4
