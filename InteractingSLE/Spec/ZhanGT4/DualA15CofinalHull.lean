/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import QuantumZipper.Proofs.Complex.BasicsMontel
import QuantumZipper.Proofs.GFF.K3.C5Kernel
import InteractingSLE.Foundations.Loewner.Capacity
import InteractingSLE.Foundations.Loewner.CapacityEstimates
import InteractingSLE.Foundations.Loewner.ConformalImageFull

/-!
# Zhan's A.1.5: the hull at an exit time stays in the enclosure

Packet PROVE-ZHAN-GT4-A15F. Source: Astra, *Follow-up proofs*, §A.1.3 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L300–L305, R38): "Let `S_j` be the first exit of `K_j` from `H_j`", used in §A.1.5 (L409–L425).

For a continuous driver the hull `K_s` at a time `s` is controlled by the earlier hulls `K_t`, `t < s`, without any
trace: if a preconnected open set `V ⊆ ℍ` meets no `K_t`, `t < s`, then it is either swallowed entirely at time `s` or
not met by `K_s` at all (`subset_or_disjoint_fwdHull`). The proof is local (`ball_subset_fwdHull_of_mem`): if the centre
of a ball avoiding all earlier hulls is swallowed at time `s`, the centred maps `f_t = g_t − W_t` along times `t ↑ s`
with
`Im f_t(z) → 0` form a normal family on the ball (Montel, with the uniform bound `‖f_t(w) − w‖ ≤ 24M + 8√s`); a limit
`φ` has `Im φ ≥ 0` and `Im φ(z) = 0`, so `exp(iφ)` attains its maximum modulus at `z` and `Im φ ≡ 0` on the ball; an
alive point `w` would have `Im f_t(w) ≥ Im f_s(w) > 0`.

Consequently **the hull at the first exit time stays in the enclosure** (`fwdHull_subset_of_forall_lt`): if `ℍ \ E` is
open, preconnected and unbounded (for instance `E` a compact `ℍ`-hull) and `K_t ⊆ E` for every `t < s`, then
`K_s ⊆ E`. This is the step "`K_{S} ⊆ H`" of the exit time; it is not "`K_s ⊆ closure ⋃_{t<s} K_t`" (false at
swallowing times).

## Main results

* `swallowTime_eq_ofReal`, `ball_subset_fwdHull_of_mem`, `subset_or_disjoint_fwdHull`;
* **`fwdHull_subset_of_forall_lt`**, `fwdHull_subset_of_forall_lt_add` (a driver started at `x`);
* `IsHPHull.isOpen_H_diff`, `IsHPHull.isPreconnected_H_diff`, `IsHPHull.not_isBounded_H_diff`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull swallowTime)

variable {W : ℝ → ℝ}

/-- A point swallowed at time `s` but at no earlier time has swallowing time exactly `s`. -/
theorem swallowTime_eq_ofReal {s : ℝ} {z : ℂ} (hz : z ∈ fwdHull W s)
    (hlt : ∀ t, 0 ≤ t → t < s → z ∉ fwdHull W t) : swallowTime W z = ENNReal.ofReal s := by
  refine le_antisymm hz.2 (not_lt.1 fun h => ?_)
  have hne : swallowTime W z ≠ ⊤ := ne_top_of_lt h
  refine hlt (swallowTime W z).toReal ENNReal.toReal_nonneg (ENNReal.toReal_lt_of_lt_ofReal h) ⟨hz.1, ?_⟩
  rw [ENNReal.ofReal_toReal hne]

/-- **A ball avoiding all earlier hulls is swallowed entirely when its centre is.** -/
theorem ball_subset_fwdHull_of_mem (hW : Continuous W) (hW0 : W 0 = 0) {s r : ℝ} {z : ℂ} (hs : 0 < s)
    (hr : 0 < r) (hbH : ball z r ⊆ H) (havoid : ∀ t, 0 ≤ t → t < s → Disjoint (ball z r) (fwdHull W t))
    (hz : z ∈ fwdHull W s) : ball z r ⊆ fwdHull W s := by
  have hzb : z ∈ ball z r := mem_ball_self hr
  have hzH : z ∈ H := hbH hzb
  have halive : ∀ w ∈ ball z r, ∀ t, 0 ≤ t → t < s → w ∈ H \ fwdHull W t := fun w hw t ht0 hts =>
    ⟨hbH hw, fun hwK => Set.disjoint_left.1 (havoid t ht0 hts) hw hwK⟩
  have hσ : swallowTime W z = ENNReal.ofReal s :=
    swallowTime_eq_ofReal hz fun t ht0 hts => (halive z hzb t ht0 hts).2
  -- times `τ n ↑ s` with `Im f_{τ n}(z) < 1/(n+1)`
  have hseq : ∀ n : ℕ, ∃ t, s - s / ((n : ℝ) + 2) ≤ t ∧ t < s ∧ (fwdMap W t z).im < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨t', ht'0, ht's, ht'im⟩ :=
      QuantumZipper.FwdClock.exists_im_fwdMap_lt_of_swallowTime hW (show 0 < z.im from hzH) hσ
        (c := 1 / ((n : ℝ) + 1)) (by positivity)
    have hlt : s - s / ((n : ℝ) + 2) < s := by
      have : 0 < s / ((n : ℝ) + 2) := by positivity
      linarith
    have ht0 : 0 ≤ max t' (s - s / ((n : ℝ) + 2)) := ht'0.trans (le_max_left _ _)
    have hts : max t' (s - s / ((n : ℝ) + 2)) < s := max_lt ht's hlt
    refine ⟨max t' (s - s / ((n : ℝ) + 2)), le_max_right _ _, hts, lt_of_le_of_lt ?_ ht'im⟩
    obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull ht0 hzH (halive z hzb _ ht0 hts).2
    exact (QuantumZipper.K3.im_fwdMap_antitoneOn hW hzH ⟨u, hu⟩).1 ⟨ht'0, le_max_left _ _⟩ ⟨ht0, le_rfl⟩
      (le_max_left _ _)
  choose τ hτlo hτs hτim using hseq
  have hτpos : ∀ n, 0 < τ n := fun n => by
    have h2 : s / ((n : ℝ) + 2) < s := div_lt_self hs (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    linarith [hτlo n]
  -- the uniform bound
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := s)).exists_bound_of_continuousOn hW.continuousOn
  have hbound : ∀ n, ∀ w ∈ ball z r, ‖fwdMap W (τ n) w‖ ≤ ‖z‖ + r + (24 * M + 8 * Real.sqrt s) := by
    intro n w hw
    have h1 := QuantumZipper.CoreArc.norm_fwdMap_sub_le_uniform hW hW0 (hτpos n)
      (fun t ht => by
        have := hM t ⟨ht.1, ht.2.trans (hτs n).le⟩
        rwa [Real.norm_eq_abs] at this) (halive w hw (τ n) (hτpos n).le (hτs n))
    have h2 : Real.sqrt (τ n) ≤ Real.sqrt s := Real.sqrt_le_sqrt (hτs n).le
    have h3 : ‖w‖ ≤ ‖z‖ + r := by
      have := norm_le_norm_add_norm_sub' w z
      rw [mem_ball, dist_eq_norm] at hw
      linarith
    calc ‖fwdMap W (τ n) w‖ = ‖w + (fwdMap W (τ n) w - w)‖ := by rw [add_sub_cancel]
      _ ≤ ‖w‖ + ‖fwdMap W (τ n) w - w‖ := norm_add_le _ _
      _ ≤ ‖z‖ + r + (24 * M + 8 * Real.sqrt s) := by linarith
  obtain ⟨φ, f, hφ, hf, hconv⟩ := QuantumZipper.CA.montel (U := ball z r) isOpen_ball
    (F := fun n => fwdMap W (τ n))
    (fun n => (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW (hτpos n).le).mono
      fun w hw => halive w hw (τ n) (hτpos n).le (hτs n))
    (fun K hK _ => ⟨_, fun n w hw => hbound n w (hK hw)⟩)
  have hlim : ∀ w ∈ ball z r, Tendsto (fun k => (fwdMap W (τ (φ k)) w).im) atTop (𝓝 (f w).im) :=
    fun w hw => (Complex.continuous_im.tendsto _).comp (hconv.tendsto_at hw)
  have himpos : ∀ n, ∀ w ∈ ball z r, 0 < (fwdMap W (τ n) w).im := fun n w hw =>
    QuantumZipper.FwdHolo.mapsTo_fwdMap hW (hτpos n).le (halive w hw (τ n) (hτpos n).le (hτs n))
  have hnn : ∀ w ∈ ball z r, 0 ≤ (f w).im := fun w hw =>
    ge_of_tendsto' (hlim w hw) fun k => (himpos (φ k) w hw).le
  have hz0 : (f z).im = 0 := by
    have hup : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hsq : Tendsto (fun k => (fwdMap W (τ (φ k)) z).im) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun k => (himpos (φ k) z hzb).le) fun k => (hτim (φ k)).le
    exact tendsto_nhds_unique (hlim z hzb) hsq
  -- maximum modulus for `exp (i f)`
  have hnorm : ∀ w, ‖Complex.exp (Complex.I * f w)‖ = Real.exp (-(f w).im) := fun w => by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have hmax : IsMaxOn (norm ∘ fun w => Complex.exp (Complex.I * f w)) (ball z r) z := by
    intro w hw
    simp only [mem_ofPred_eq, Function.comp_apply, hnorm, hz0, neg_zero]
    exact Real.exp_le_exp.2 (neg_nonpos.2 (hnn w hw))
  have hzero : ∀ w ∈ ball z r, (f w).im = 0 := by
    intro w hw
    have h := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn (convex_ball z r).isPreconnected isOpen_ball
      ((hf.const_mul Complex.I).cexp) hzb hmax hw
    simp only [Function.comp_apply, Function.const_apply, hnorm, hz0, neg_zero, Real.exp_zero] at h
    have := Real.exp_eq_one_iff _ |>.1 h
    linarith
  intro w hw
  by_contra hwK
  obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hs.le (hbH hw) hwK
  have hanti := QuantumZipper.K3.im_fwdMap_antitoneOn hW (hbH hw) ⟨u, hu⟩
  have hpos : 0 < (fwdMap W s w).im := hanti.2 s ⟨hs.le, le_rfl⟩
  have hge : (fwdMap W s w).im ≤ (f w).im := ge_of_tendsto' (hlim w hw) fun k =>
    hanti.1 ⟨(hτpos (φ k)).le, (hτs (φ k)).le⟩ ⟨hs.le, le_rfl⟩ (hτs (φ k)).le
  linarith [hzero w hw]

/-- **A preconnected open set avoiding all earlier hulls is swallowed entirely at time `s` or not met by `K_s`.** -/
theorem subset_or_disjoint_fwdHull (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) {V : Set ℂ}
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVH : V ⊆ H)
    (havoid : ∀ t, 0 ≤ t → t < s → Disjoint V (fwdHull W t)) :
    V ⊆ fwdHull W s ∨ Disjoint V (fwdHull W s) := by
  rcases hs.eq_or_lt with rfl | hs
  · right
    rw [QuantumZipper.RS.fwdHull_zero_eq_empty hW]
    exact disjoint_empty V
  have hcov : V ⊆ (H \ fwdHull W s) ∪ interior (fwdHull W s) := by
    intro w hw
    by_cases hwK : w ∈ fwdHull W s
    · right
      obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hVo w hw
      exact mem_interior.2 ⟨ball w r, ball_subset_fwdHull_of_mem hW hW0 hs hr (hrV.trans hVH)
        (fun t ht0 hts => (havoid t ht0 hts).mono_left hrV) hwK, isOpen_ball, mem_ball_self hr⟩
    · exact Or.inl ⟨hVH hw, hwK⟩
  have hdisj : Disjoint (H \ fwdHull W s) (interior (fwdHull W s)) :=
    Set.disjoint_left.2 fun w hw hw' => hw.2 (interior_subset hw')
  rcases hVc.subset_or_subset (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hs.le) isOpen_interior hdisj hcov
    with h | h
  · exact Or.inr (Set.disjoint_left.2 fun w hw hwK => (h hw).2 hwK)
  · exact Or.inl (h.trans interior_subset)

/-- **The hull at the first exit time stays in the enclosure.** If `ℍ \ E` is open, preconnected and unbounded and
`K_t ⊆ E` for every `t < s`, then `K_s ⊆ E`. -/
theorem fwdHull_subset_of_forall_lt (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) {E : Set ℂ}
    (hEo : IsOpen (H \ E)) (hEc : IsPreconnected (H \ E)) (hEb : ¬ Bornology.IsBounded (H \ E))
    (hlt : ∀ t, 0 ≤ t → t < s → fwdHull W t ⊆ E) : fwdHull W s ⊆ E := by
  rcases subset_or_disjoint_fwdHull hW hW0 hs hEo hEc sdiff_subset fun t ht0 hts =>
      Set.disjoint_left.2 fun w hw hwK => hw.2 (hlt t ht0 hts hwK) with h | h
  · exact absurd ((isBounded_fwdHull hW s).subset h) hEb
  · intro z hz
    by_contra hzE
    exact Set.disjoint_left.1 h ⟨(QuantumZipper.fwdHull_mono.2 s) hz, hzE⟩ hz

/-- The exit-time step for a driver started at `x`: `K_t(W + x) ⊆ E` for `t < s` gives `K_s(W + x) ⊆ E`. -/
theorem fwdHull_subset_of_forall_lt_add (hW : Continuous W) (hW0 : W 0 = 0) (x : ℝ) {s : ℝ} (hs : 0 ≤ s)
    {E : Set ℂ} (hEo : IsOpen (H \ E)) (hEc : IsPreconnected (H \ E)) (hEb : ¬ Bornology.IsBounded (H \ E))
    (hlt : ∀ t, 0 ≤ t → t < s → fwdHull (fun u => W u + x) t ⊆ E) : fwdHull (fun u => W u + x) s ⊆ E := by
  set e : ℂ → ℂ := fun z => z + (x : ℂ) with he
  have hec : Continuous e := continuous_id.add continuous_const
  have hpre : H \ (e ⁻¹' E) = e ⁻¹' (H \ E) := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_preimage, QuantumZipper.H, Set.mem_ofPred_eq, he, Complex.add_im,
      Complex.ofReal_im, add_zero]
  have hEo' : IsOpen (H \ (e ⁻¹' E)) := hpre ▸ hEo.preimage hec
  have himg : e '' (e ⁻¹' (H \ E)) = H \ E := image_preimage_eq _ fun w => ⟨w - x, by simp [he]⟩
  have hEc' : IsPreconnected (H \ (e ⁻¹' E)) := by
    have hhomeo : e ⁻¹' (H \ E) = (fun z : ℂ => z - (x : ℂ)) '' (H \ E) := by
      ext z; simp only [Set.mem_preimage, Set.mem_image, he]
      exact ⟨fun h => ⟨z + x, h, by ring⟩, fun ⟨w, hw, hwz⟩ => by rw [← hwz]; simpa using hw⟩
    rw [hpre, hhomeo]
    exact hEc.image _ (continuous_id.sub continuous_const).continuousOn
  have hEb' : ¬ Bornology.IsBounded (H \ (e ⁻¹' E)) := fun hb => hEb (by
    rw [← himg, ← hpre]
    exact (IsometryEquiv.addRight (x : ℂ)).isometry.lipschitzWith.isBounded_image hb)
  have key := fwdHull_subset_of_forall_lt hW hW0 hs hEo' hEc' hEb' fun t ht0 hts => by
    intro z hz
    show z + (x : ℂ) ∈ E
    exact hlt t ht0 hts (by rw [ConformalImageFull.fwdHull_add_const]; exact ⟨z, hz, rfl⟩)
  rw [ConformalImageFull.fwdHull_add_const]
  rintro _ ⟨z, hz, rfl⟩
  exact key hz

/-! ### The complement of a compact `ℍ`-hull -/

theorem IsHPHull.isOpen_H_diff {E : Set ℂ} (hE : IsHPHull E) : IsOpen (H \ E) := hE.2.2.1

theorem IsHPHull.isPreconnected_H_diff {E : Set ℂ} (hE : IsHPHull E) : IsPreconnected (H \ E) :=
  hE.isConnected.isPreconnected

theorem IsHPHull.not_isBounded_H_diff {E : Set ℂ} (hE : IsHPHull E) : ¬ Bornology.IsBounded (H \ E) := by
  intro hb
  have hb' : Bornology.IsBounded H := by
    have : H ⊆ (H \ E) ∪ E := fun z hz => by
      by_cases h : z ∈ E
      · exact Or.inr h
      · exact Or.inl ⟨hz, h⟩
    exact (hb.union hE.2.1).subset this
  obtain ⟨R, hR⟩ := hb'.subset_closedBall 0
  have hmem : ((|R| + 1 : ℝ) : ℂ) * Complex.I ∈ H := by
    show 0 < (((|R| + 1 : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
      mul_zero, add_zero]
    positivity
  have h1 := mem_closedBall_zero_iff.1 (hR hmem)
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
  linarith [le_abs_self R]

end InteractingSLE.ZhanGT4
