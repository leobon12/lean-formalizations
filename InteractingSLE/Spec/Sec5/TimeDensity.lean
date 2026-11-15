/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Lemma57Visit
import InteractingSLE.Spec.Sec5.Recovery
import InteractingSLE.Foundations.Loewner.Capacity
import QuantumZipper.Proofs.RS.TraceShift
import QuantumZipper.Proofs.Loewner.CaraRZ

/-!
# The time density (5.7) of the first visits (proof of Proposition 5.13)

Packet PROVE-PROP513. Specification §5.2, proof of Proposition 5.13 (`source/spec/p145-192.md` L94–L132,
pp. 149–151):

  "We need a time-density assertion, in addition to spatial density. For `z ∈ Γ`, let `T_z` be the first counterflow
  time at which `z` is visited. We will prove that `{T_z : z ∈ Γ}` is dense in `(0, ∞)` (5.7). … Hull monotonicity
  then gives a random `a = a(r, δ) > 0` such that `B(W_r, a) ∩ ℍ ⊆ g_r(K_{r+δ} \ K_r)` (5.8). … Its inverse image
  under `g_r` is consequently an open subset of the interior of `K_{r+δ}` which is disjoint from `K_r`. … some
  allowed prefix therefore enters the open set `Φ⁻¹(int_ℍ K_{r+δ} \ K_r)`. … hence a point `z ∈ Γ` in the same open
  set. … Thus `r < T_z ≤ r + δ`. Impose this assertion for all positive rational `r, δ`. Every nonempty open interval
  of positive times contains one of the resulting intervals `(r, r+δ]`, proving (5.7)."

We work in the capacity chart (`hcap(K_t) = 2t`), with the counterflow trace `η` a generating trace of the
continuous driver `w` on `[0, ∞)`. Equation (5.8) is the **future half-ball property** `HasFutureHalfBall w r δ`:
the hull at time `δ` of the restarted driver `W(r + ·) − W(r)` contains a half-ball `ℍ ∩ B(0, ε)`. The restarted
hulls are the images of the hull increments under the inverse map at `r` (`fwdHull_add_sdiff_eq_image`), which is
the formal content of "`g_r(K_{r+δ} \ K_r)`".

**Spatial density instead of the image-range construction.** The specification enters the open set
`int K_{r+δ} \ K_r` with an allowed prefix produced by the construction of Proposition 5.9 in the coordinate `ψ`. Here
the open set is entered by the counterflow trace itself — on every interval `(r, r + s₀]` the trace visits
`K_{r+s₀} \ K_r` (strict growth of hulls), and for small `s₀` this increment lies in `int K_{r+δ}`
(`exists_fwdHull_sdiff_subset_interior`) — and then by a point of `Γ`, because `Γ` is dense in the counterflow range
(Corollary 5.12, extreme-angle version: the root-`0` case of Proposition 5.9). The proof otherwise follows the
source.

## Main results

* `fwdHull_add_sdiff_eq_image`: `K_{r+u} \ K_r = F_r(K^{(r)}_u)` with `F_r = fwdMapInv W r` and `K^{(r)}` the hulls
  of the restarted driver.
* `isOpen_image_fwdMapInv`: `F_r` maps open subsets of `ℍ` to open sets (open mapping theorem).
* `HasFutureHalfBall` ((5.8)) and **`exists_fwdHull_sdiff_subset_interior`**: under (5.8), for some `s₀ > 0`,
  `K_{r+s₀} \ K_r ⊆ int K_{r+δ}`.
* **`exists_lt_traceFirstVisit_le`** (one window): a family `z i` of visited points dense in the trace range, and
  (5.8) at `(r, δ)`, give some `i` with `r < T_{z i} ≤ r + δ`.
* **`dense_traceFirstVisit`** ((5.7), pathwise) and **`ae_dense_traceFirstVisit`** (almost surely, with (5.8) at
  the positive rational windows almost surely).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5

open QuantumZipper

/-! ### Restarted hulls -/

/-- **The hull increments are the images of the restarted hulls**: `K_{r+u} \ K_r = F_r(K^{(r)}_u)`, where
`F_r = fwdMapInv W r` and `K^{(r)}` are the hulls of `W(r + ·) − W(r)`. -/
theorem fwdHull_add_sdiff_eq_image {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {r u : ℝ} (hr : 0 ≤ r)
    (hu : 0 ≤ u) :
    fwdHull W (r + u) \ fwdHull W r = fwdMapInv W r '' fwdHull (RS.shiftDrive W r) u := by
  have hA := RS.continuous_shiftDrive hW r
  have hA0 := RS.shiftDrive_zero W r
  obtain ⟨-, hFm, hFi, hFs⟩ := isConformalBijection_fwdMapInv hW hW0 hr
  obtain ⟨-, hGm, -, hGs⟩ := isConformalBijection_fwdMapInv hA hA0 hu
  obtain ⟨-, hSm, -, hSs⟩ := isConformalBijection_fwdMapInv hW hW0 (add_nonneg hr hu)
  ext z
  constructor
  · rintro ⟨hz, hzr⟩
    have hzH : z ∈ H := fwdHull_mono.2 _ hz
    obtain ⟨x, hxH, rfl⟩ := hFs ⟨hzH, hzr⟩
    refine ⟨x, ?_, rfl⟩
    by_contra hxK
    obtain ⟨v, hvH, rfl⟩ := hGs ⟨hxH, hxK⟩
    have := (hSm hvH).2
    rw [RS.fwdMapInv_add_shift hW hW0 hr hu hvH] at this
    exact this hz
  · rintro ⟨x, hxK, rfl⟩
    have hxH : x ∈ H := fwdHull_mono.2 _ hxK
    refine ⟨?_, (hFm hxH).2⟩
    by_contra hz
    obtain ⟨v, hvH, hv⟩ := hSs ⟨(hFm hxH).1, hz⟩
    rw [RS.fwdMapInv_add_shift hW hW0 hr hu hvH] at hv
    have hGv := hGm hvH
    have := hFi hGv.1 hxH hv
    exact hGv.2 (this ▸ hxK)

/-- **`F_r` is an open map on `ℍ`** (open mapping theorem: `F_r` is holomorphic and injective on the connected
open set `ℍ`). -/
theorem isOpen_image_fwdMapInv {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {r : ℝ} (hr : 0 ≤ r)
    {U : Set ℂ} (hUH : U ⊆ H) (hU : IsOpen U) : IsOpen (fwdMapInv W r '' U) := by
  obtain ⟨hd, -, hFi, -⟩ := isConformalBijection_fwdMapInv hW hW0 hr
  have hpc : IsPreconnected H := (convex_halfSpace_gt Complex.imLm.isLinear 0 : Convex ℝ H).isPreconnected
  rcases (hd.analyticOnNhd isOpen_H).is_constant_or_isOpen hpc with ⟨c, hc⟩ | h
  · exfalso
    have h1 : Complex.I ∈ H := by show (0 : ℝ) < Complex.I.im; simp
    have h2 : 2 * Complex.I ∈ H := by show (0 : ℝ) < (2 * Complex.I).im; simp
    have := hFi h1 h2 ((hc _ h1).trans (hc _ h2).symm)
    have h3 := congrArg Complex.im this
    simp at h3
  · exact h U hUH hU

/-! ### The future half-ball property (5.8) -/

/-- **(5.8), the future half-ball property at `(r, δ)`**: the hull at time `δ` of the restarted driver
`W(r + ·) − W(r)` (`W = w ∘ toNNReal`) contains a half-ball `ℍ ∩ B(0, ε)`, `ε > 0` ("`B(W_r, a) ∩ ℍ ⊆
g_r(K_{r+δ} \ K_r)`"). -/
def HasFutureHalfBall (w : ℝ≥0 → ℝ) (r δ : ℝ≥0) : Prop :=
  ∃ ε > (0 : ℝ), ∀ z ∈ H, ‖z‖ < ε → z ∈ fwdHull (RS.shiftDrive (fun s : ℝ => w s.toNNReal) r) δ

/-- Small hulls of a continuous driver starting at `0` lie in a given ball around `0`. -/
theorem exists_fwdHull_subset_ball {A : ℝ → ℝ} (hA : Continuous A) (hA0 : A 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ z ∈ fwdHull A s₀, ‖z‖ < ε := by
  obtain ⟨s₁, hs₁, hs₁A⟩ := Metric.continuousAt_iff.1 hA.continuousAt (ε / 3) (by positivity)
  set s₀ : ℝ := min (s₁ / 2) ((ε / 9) ^ 2) with hs₀
  have hs₀p : 0 < s₀ := lt_min (by positivity) (by positivity)
  refine ⟨s₀, hs₀p, fun z hz => ?_⟩
  have hM : ∀ x ∈ Icc (0 : ℝ) s₀, |A x| ≤ ε / 3 := by
    intro x hx
    have hx1 : dist x 0 < s₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
      exact hx.2.trans_lt ((min_le_left _ _).trans_lt (by linarith))
    have := hs₁A hx1
    rw [Real.dist_eq, hA0, sub_zero] at this
    exact this.le
  have hsq : Real.sqrt s₀ ≤ ε / 9 := by
    rw [Real.sqrt_le_left (by positivity)]
    exact min_le_right _ _
  have hball := CaraR.fwdHull_subset_closedBall hA hs₀p hM hz
  rw [Metric.mem_closedBall, dist_zero_right] at hball
  linarith

/-- **Under (5.8), the hull increment just after `r` lies in the interior of `K_{r+δ}`**: for some `s₀ > 0`,
`K_{r+s₀} \ K_r ⊆ int K_{r+δ}` ("Its inverse image under `g_r` is consequently an open subset of the interior of
`K_{r+δ}` which is disjoint from `K_r`"). -/
theorem exists_fwdHull_sdiff_subset_interior {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {r δ : ℝ≥0}
    (hb : HasFutureHalfBall w r δ) :
    ∃ s₀ : ℝ≥0, 0 < s₀ ∧ fwdHull (fun s : ℝ => w s.toNNReal) ((r + s₀ : ℝ≥0) : ℝ) \
      fwdHull (fun s : ℝ => w s.toNNReal) r ⊆ interior (fwdHull (fun s : ℝ => w s.toNNReal) ((r + δ : ℝ≥0) : ℝ)) := by
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  have hW : Continuous W := hw.comp continuous_real_toNNReal
  have hW0 : W 0 = 0 := by simp [hWdef, hw0]
  obtain ⟨ε, hε, hball⟩ := hb
  set A := RS.shiftDrive W r with hAdef
  have hA := RS.continuous_shiftDrive hW r
  have hA0 := RS.shiftDrive_zero W r
  obtain ⟨s₀, hs₀, hsmall⟩ := exists_fwdHull_subset_ball hA hA0 hε
  refine ⟨s₀.toNNReal, Real.toNNReal_pos.2 hs₀, ?_⟩
  set U : Set ℂ := H ∩ Metric.ball 0 ε with hUdef
  have hUo : IsOpen U := isOpen_H.inter Metric.isOpen_ball
  have hUH : U ⊆ H := inter_subset_left
  have hUK : U ⊆ fwdHull A δ := fun z hz => hball z hz.1 (by simpa using hz.2)
  have hV := isOpen_image_fwdMapInv hW hW0 r.coe_nonneg hUH hUo
  have hVK : fwdMapInv W r '' U ⊆ fwdHull W ((r + δ : ℝ≥0) : ℝ) := by
    have h := fwdHull_add_sdiff_eq_image hW hW0 r.coe_nonneg δ.coe_nonneg
    push_cast
    intro z hz
    have : z ∈ fwdMapInv W r '' fwdHull A δ := image_mono hUK hz
    rw [← h] at this
    exact this.1
  have hinc : fwdHull W ((r + s₀.toNNReal : ℝ≥0) : ℝ) \ fwdHull W r ⊆ fwdMapInv W r '' U := by
    have h := fwdHull_add_sdiff_eq_image hW hW0 r.coe_nonneg hs₀.le
    rw [NNReal.coe_add, Real.coe_toNNReal _ hs₀.le, h]
    refine image_mono fun z hz => ⟨fwdHull_mono.2 _ hz, ?_⟩
    simpa using hsmall z hz
  exact hinc.trans (interior_maximal hVK hV)

/-! ### One window and the time density -/

variable {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ}

/-- **One window of (5.7).** Let `z i` be points visited by the trace whose closure contains the trace range
(Lemma 5.7 and Corollary 5.12). Under (5.8) at `(r, δ)`, some `z i` has its first visit in `(r, r + δ]`. -/
theorem exists_lt_traceFirstVisit_le (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsGeneratingTrace w ⊤ η)
    {ι : Type*} {z : ι → ℂ} (hzη : ∀ i, ∃ t, η t = z i) (hdense : range η ⊆ closure (range z)) {r δ : ℝ≥0}
    (hb : HasFutureHalfBall w r δ) :
    ∃ i, r < traceFirstVisit η (z i) ∧ traceFirstVisit η (z i) ≤ r + δ := by
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  have hW : Continuous W := hw.comp continuous_real_toNNReal
  obtain ⟨s₀, hs₀, hsub⟩ := exists_fwdHull_sdiff_subset_interior hw hw0 hb
  obtain ⟨u, hru, -, hu⟩ := exists_mem_fwdHull_sdiff hw hw0 hη (lt_add_of_pos_right r hs₀)
  set O : Set ℂ := interior (fwdHull W ((r + δ : ℝ≥0) : ℝ)) ∩ (H \ fwdHull W r) with hOdef
  have hO : IsOpen O := isOpen_interior.inter (FwdHolo.isOpen_compl_fwdHull hW r.coe_nonneg)
  have huO : η u ∈ O := ⟨hsub hu, fwdHull_mono.2 _ hu.1, hu.2⟩
  obtain ⟨_, hzO, i, rfl⟩ :=
    mem_closure_iff.1 (hdense (mem_range_self u)) O hO huO
  exact ⟨i, lt_traceFirstVisit_and_le hw hw0 hη (hzη i) hzO.2.1 hzO.2.2 hzO.1⟩

/-- **(5.7), pathwise**: if the visited points `z i` are dense in the trace range and (5.8) holds at every positive
rational window, the first visits `T_{z i}` are dense in `(0, ∞)`. -/
theorem dense_traceFirstVisit (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsGeneratingTrace w ⊤ η)
    {ι : Type*} {z : ι → ℂ} (hzη : ∀ i, ∃ t, η t = z i) (hdense : range η ⊆ closure (range z))
    (hb : ∀ r δ : ℚ, 0 < r → 0 < δ → HasFutureHalfBall w (r : ℝ).toNNReal (δ : ℝ).toNNReal)
    {t : ℝ} (ht : 0 < t) : ∀ ε > 0, ∃ i, |(traceFirstVisit η (z i) : ℝ) - t| < ε := by
  refine dense_of_rat_windows (fun r δ hr hδ => ?_) ht
  have hr' : (0 : ℝ) ≤ r := by exact_mod_cast hr.le
  have hδ' : (0 : ℝ) ≤ δ := by exact_mod_cast hδ.le
  obtain ⟨i, h1, h2⟩ := exists_lt_traceFirstVisit_le hw hw0 hη hzη hdense (hb r δ hr hδ)
  refine ⟨i, ?_, ?_⟩
  · have := NNReal.coe_lt_coe.2 h1
    rwa [Real.coe_toNNReal _ hr'] at this
  · have := NNReal.coe_le_coe.2 h2
    rwa [NNReal.coe_add, Real.coe_toNNReal _ hr', Real.coe_toNNReal _ hδ'] at this

/-- **(5.7), almost surely.** For random drivers `w ω` with generating traces `η ω` on `[0, ∞)`, a countable family
of points `z i ω` visited by the trace (Lemma 5.7) and dense in its range (Corollary 5.12), and (5.8) almost surely at
every positive rational window: almost surely the first visits are dense in `(0, ∞)`. -/
theorem ae_dense_traceFirstVisit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {w : Ω → ℝ≥0 → ℝ}
    {η : Ω → ℝ≥0 → ℂ} {ι : Type*} {z : ι → Ω → ℂ}
    (hη : ∀ᵐ ω ∂P, Continuous (w ω) ∧ w ω 0 = 0 ∧ IsGeneratingTrace (w ω) ⊤ (η ω))
    (hzη : ∀ᵐ ω ∂P, ∀ i, ∃ t, η ω t = z i ω)
    (hdense : ∀ᵐ ω ∂P, range (η ω) ⊆ closure (range fun i => z i ω))
    (hb : ∀ r δ : ℚ, 0 < r → 0 < δ → ∀ᵐ ω ∂P, HasFutureHalfBall (w ω) (r : ℝ).toNNReal (δ : ℝ).toNNReal) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ ε > 0, ∃ i, |(traceFirstVisit (η ω) (z i ω) : ℝ) - t| < ε := by
  have hb' : ∀ᵐ ω ∂P, ∀ r δ : ℚ, 0 < r → 0 < δ →
      HasFutureHalfBall (w ω) (r : ℝ).toNNReal (δ : ℝ).toNNReal := by
    refine ae_all_iff.2 fun r => ae_all_iff.2 fun δ => ?_
    by_cases hr : 0 < r
    · by_cases hδ : 0 < δ
      · filter_upwards [hb r δ hr hδ] with ω hω _ _ using hω
      · exact Eventually.of_forall fun ω _ h => absurd h hδ
    · exact Eventually.of_forall fun ω h => absurd h hr
  filter_upwards [hη, hzη, hdense, hb'] with ω ⟨hw, hw0, hηω⟩ hzω hdω hbω t ht
  exact dense_traceFirstVisit hw hw0 hηω hzω hdω hbω ht

end Sec5

end InteractingSLE
