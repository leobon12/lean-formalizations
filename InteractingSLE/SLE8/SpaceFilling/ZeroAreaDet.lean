import InteractingSLE.Foundations.Loewner.YuanTrace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import QuantumZipper.Proofs.Thm11.AddendumArea

/-!
# κ = 8 space filling, Proposition 5: the deterministic steps

Source: the user's note *Space filling of a continuous SLE₈ trace*
(`source/external/SLE8SF/sle8_space_filling_formalization.pdf`, §3, proof of Proposition 5, p. 5).

For a continuous driver `W` with `W 0 = 0`, `t ≥ 0`, `D_t = ℍ \ K_t` (`H \ fwdHull W t`) and the
boundary extension `F̄_t = extendFrom H (fwdMapInv W t)` of `F_t` (continuous on `ℍ̄` when the chain
has a continuous trace, (L1)):

* `exists_real_extendFrom_eq_of_mem_frontier`: **every finite point `w ∈ ∂D_t ∩ ℍ` lies in
  `F̄_t(ℝ)`.** Choose `w_j ∈ D_t`, `w_j → w`, and `v_j = F_t⁻¹(w_j)`. By (L3) (`F_t - id` is bounded,
  `exists_norm_fwdMapInv_sub_le`) the `v_j` are bounded; a subsequence converges to `v ∈ ℍ̄`. If
  `v ∈ ℍ` then `w = F_t(v) ∈ D_t`, impossible since `D_t` is open; so `v ∈ ℝ` and `F̄_t(v) = w`.
* `frontier_inter_H_subset_iUnion`: hence `∂D_t ∩ ℍ` is covered by the countably many sets
  `F̄_t([-L, L]) ∩ {Im w ≥ 2h}`, `L ∈ ℕ_{≥1}`, `h = 1/k`;
* `volume_frontier_eq_zero_of_hausdorffMeasure`: `H^{14/9}(∂D ∩ ℍ) = 0` gives `area(∂D) = 0` for
  `D ⊆ ℍ̄` (`14/9 < 2`; the rest of `∂D` lies on `ℝ`, a null line);
* `frontier_fwdHull_inter_H`, `frontier_inter_H_eq_of_inter_H_eq`: `∂K_t ∩ ℍ = ∂D_t ∩ ℍ`, for every
  `K ⊆ ℍ̄` with `K ∩ ℍ = K_t ∩ ℍ`;
* `isLoewnerTrace_of_connectedComponentIn`: the conclusion of the frozen SLE₈ trace theorem
  (`ae_exists_continuous_trace`: `D_t` is the unbounded component of `ℍ \ γ([0, t])`) makes `γ` a
  continuous Loewner trace in the sense of `IsLoewnerTrace` (`K_t = fill(γ[0, t])`), the form to which
  the boundary-extension theorem (L1) (`IsLoewnerTrace.fiber_hyps`) applies.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.SLE8.SpaceFilling

open QuantumZipper (H Hbar fwdHull fwdMapInv)

variable {W : ℝ → ℝ} {t : ℝ}

/-! ## Boundary points are images of real points -/

/-- **Every finite boundary point of `D_t` in `ℍ` is `F̄_t(v)` for a real `v`** (proof of
Proposition 5, using (L3)). -/
theorem exists_real_extendFrom_eq_of_mem_frontier (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    (hc : ContinuousOn (extendFrom H (fwdMapInv W t)) Hbar) {w : ℂ}
    (hw : w ∈ frontier (H \ fwdHull W t)) :
    ∃ v : ℝ, extendFrom H (fwdMapInv W t) v = w := by
  set F := fwdMapInv W t
  set D := H \ fwdHull W t
  have hcb := isConformalBijection_fwdMapInv hW hW0 ht
  have himg : F '' H = D := hcb.2.image_eq
  have hFc : ContinuousOn F H := hcb.1.continuousOn
  have hDo : IsOpen D := (isHPHull_fwdHull hW ht).2.2.1
  obtain ⟨x, hxD, hxw⟩ := mem_closure_iff_seq_limit.1 (frontier_subset_closure hw)
  have hpre : ∀ n, ∃ v ∈ H, F v = x n := fun n => by
    rw [← himg] at hxD; exact hxD n
  choose v hvH hvx using hpre
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 ht
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto x hxw)
  have hvK : ∀ n, v n ∈ closedBall (0 : ℂ) (R + C) ∩ Hbar := fun n => by
    refine ⟨?_, QuantumZipper.H_subset_Hbar (hvH n)⟩
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖F (v n) - v n‖ ≤ C := hC (v n) (hvH n)
    have h2 := hR (x n) (mem_range_self n)
    rw [hvx n] at h1
    have h3 : ‖v n‖ ≤ ‖x n‖ + ‖x n - v n‖ := by
      calc ‖v n‖ = ‖x n - (x n - v n)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x n‖ + ‖x n - v n‖ := norm_sub_le _ _
    linarith
  obtain ⟨v₀, ⟨-, hv₀⟩, φ, hφ, hvφ⟩ :=
    ((isCompact_closedBall _ _).inter_right QuantumZipper.isClosed_Hbar).tendsto_subseq hvK
  have hxφ : Tendsto (x ∘ φ) atTop (𝓝 w) := hxw.comp hφ.tendsto_atTop
  by_cases hv₀H : v₀ ∈ H
  · exfalso
    have h1 : Tendsto (F ∘ v ∘ φ) atTop (𝓝 (F v₀)) :=
      ((hFc.continuousAt (QuantumZipper.isOpen_H.mem_nhds hv₀H)).tendsto).comp hvφ
    have h2 : F ∘ v ∘ φ = x ∘ φ := funext fun n => hvx (φ n)
    rw [h2] at h1
    have hweq : w = F v₀ := tendsto_nhds_unique hxφ h1
    have hwD : w ∈ D := by rw [hweq, ← himg]; exact mem_image_of_mem F hv₀H
    rw [hDo.frontier_eq] at hw
    exact hw.2 hwD
  · have hv₀im : v₀.im = 0 := le_antisymm (not_lt.1 hv₀H) hv₀
    refine ⟨v₀.re, ?_⟩
    have hv₀eq : ((v₀.re : ℝ) : ℂ) = v₀ := Complex.ext (by simp) (by simp [hv₀im])
    rw [hv₀eq]
    have hvφ' : Tendsto (v ∘ φ) atTop (𝓝[Hbar] v₀) :=
      tendsto_nhdsWithin_iff.2 ⟨hvφ, Eventually.of_forall fun n =>
        QuantumZipper.H_subset_Hbar (hvH (φ n))⟩
    have h1 := (hc v₀ hv₀).tendsto.comp hvφ'
    have h2 : extendFrom H F ∘ v ∘ φ = x ∘ φ := funext fun n => by
      simp only [Function.comp_apply]
      rw [extendFrom_H_eq hFc (hvH (φ n)), hvx]
    rw [h2] at h1
    exact tendsto_nhds_unique h1 hxφ

/-- **The countable cover of `∂D_t ∩ ℍ`.** `∂D_t ∩ ℍ ⊆ ⋃_{L, k} F̄_t([-(L+1), L+1]) ∩
{Im w ≥ 2/(k+1)}`. -/
theorem frontier_inter_H_subset_iUnion (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    (hc : ContinuousOn (extendFrom H (fwdMapInv W t)) Hbar) :
    frontier (H \ fwdHull W t) ∩ H ⊆ ⋃ L : ℕ, ⋃ k : ℕ,
      (fun x : ℝ => extendFrom H (fwdMapInv W t) x) '' Icc (-((L + 1 : ℕ) : ℝ)) ((L + 1 : ℕ) : ℝ) ∩
        {w | 2 * (1 / ((k : ℝ) + 1)) ≤ w.im} := by
  rintro w ⟨hwf, hwH⟩
  obtain ⟨v, hv⟩ := exists_real_extendFrom_eq_of_mem_frontier hW hW0 ht hc hwf
  have hwim : 0 < w.im := hwH
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hwim)
  refine mem_iUnion.2 ⟨⌈|v|⌉₊, mem_iUnion.2 ⟨k, ⟨v, ?_, hv⟩, ?_⟩⟩
  · have h1 := Nat.le_ceil |v|
    have h2 : (⌈|v|⌉₊ : ℝ) ≤ ((⌈|v|⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact abs_le.1 (h1.trans h2)
  · show 2 * (1 / ((k : ℝ) + 1)) ≤ w.im
    linarith

/-! ## Frontiers and area -/

/-- `∂K_t ∩ ℍ = ∂D_t ∩ ℍ` (for any set `K`, with `D = ℍ \ K`). -/
theorem frontier_fwdHull_inter_H (W : ℝ → ℝ) (t : ℝ) :
    frontier (fwdHull W t) ∩ H = frontier (H \ fwdHull W t) ∩ H := by
  rw [sdiff_eq, inter_comm H, frontier_inter_open_inter QuantumZipper.isOpen_H, frontier_compl]

/-- `H^d(s) = 0` with `d ≤ 2` implies zero area (`ℂ → ℝ²` is `1`-Lipschitz for the sup
metric, and Lebesgue measure on `ℝ²` is `H²`). -/
theorem volume_eq_zero_of_hausdorffMeasure_eq_zero {d : ℝ} (hd : d ≤ 2) {s : Set ℂ}
    (hs : μH[d] s = 0) : volume s = 0 := by
  have h2 : μH[2] s = 0 := le_antisymm ((Measure.hausdorffMeasure_mono hd s).trans hs.le) bot_le
  set e := Complex.measurableEquivPi
  have hlip : LipschitzWith 1 e := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
    intro i
    simp only [e, Complex.measurableEquivPi_apply]
    rw [Complex.dist_eq]
    fin_cases i
    · simpa [Real.dist_eq] using Complex.abs_re_le_norm (u - v)
    · simpa [Real.dist_eq] using Complex.abs_im_le_norm (u - v)
  have himg : μH[2] (e '' s) = 0 := by
    have := hlip.hausdorffMeasure_image_le (d := 2) (by norm_num) s
    rw [h2, mul_zero] at this
    exact le_antisymm this bot_le
  have hvol : volume (e '' s) = 0 := by
    have hcard : ((Fintype.card (Fin 2) : ℕ) : ℝ) = 2 := by simp
    rw [← hausdorffMeasure_pi_real, hcard]
    exact himg
  rw [← Complex.volume_preserving_equiv_pi.measure_preimage_equiv (e '' s),
    e.injective.preimage_image] at hvol
  exact hvol

/-- **Zero area from zero `H^{14/9}`-measure.** If `H^{14/9}(∂D ∩ ℍ) = 0` for some `D ⊆ ℍ̄`, then
`area(∂D) = 0` (the rest of `∂D` lies on the null line `ℝ`, QuantumZipper's
`Thm11Area.volume_setOf_im_eq_zero`). -/
theorem volume_frontier_eq_zero_of_hausdorffMeasure {D : Set ℂ} (hD : D ⊆ Hbar)
    (hs : μH[14 / 9] (frontier D ∩ H) = 0) : volume (frontier D) = 0 := by
  have hsub : frontier D ⊆ (frontier D ∩ H) ∪ {z : ℂ | z.im = 0} := by
    intro z hz
    have hzc : z ∈ Hbar :=
      closure_minimal hD QuantumZipper.isClosed_Hbar (frontier_subset_closure hz)
    by_cases hzH : z ∈ H
    · exact Or.inl ⟨hz, hzH⟩
    · exact Or.inr (le_antisymm (not_lt.1 hzH) hzc)
  refine measure_mono_null hsub
    (measure_union_null ?_ QuantumZipper.Thm11Area.volume_setOf_im_eq_zero)
  exact volume_eq_zero_of_hausdorffMeasure_eq_zero (by norm_num) hs

/-- For any `K ⊆ ℍ̄` (for instance any closed hull) with `K ∩ ℍ = fwdHull W t`,
`∂K ∩ ℍ = ∂(K_t ∩ ℍ) ∩ ℍ`. -/
theorem frontier_inter_H_eq_of_inter_H_eq {K : Set ℂ} (hK : K ∩ H = fwdHull W t) :
    frontier K ∩ H = frontier (fwdHull W t) ∩ H := by
  rw [← hK, frontier_inter_open_inter QuantumZipper.isOpen_H]

/-! ## The frozen trace is a continuous Loewner trace -/

/-- The conclusion of the frozen SLE₈ trace theorem (`ae_exists_continuous_trace`) for one driver:
if `γ : [0, ∞) → ℂ` is continuous, `γ 0 = 0`, and each `D_t` is an unbounded connected component of
`ℍ \ γ([0, t])`, then `s ↦ γ(s₊)` is a continuous Loewner trace of `W` (`K_t = fill(γ[0, t])`). -/
theorem isLoewnerTrace_of_connectedComponentIn {γ : ℝ≥0 → ℂ} (hγc : Continuous γ) (hγ0 : γ 0 = 0)
    (hgen : ∀ t : ℝ≥0, (∃ z ∈ H \ fwdHull W t,
        connectedComponentIn (H \ γ '' Icc 0 t) z = H \ fwdHull W t) ∧
      ¬ Bornology.IsBounded (H \ fwdHull W t)) :
    IsLoewnerTrace W (fun s => γ s.toNNReal) := by
  refine ⟨by simp [hγ0], (hγc.comp continuous_real_toNNReal).continuousOn, fun t ht => ?_⟩
  set t' := t.toNNReal
  have htt : (t' : ℝ) = t := Real.coe_toNNReal t ht
  have himg : (fun s => γ s.toNNReal) '' Icc 0 t = γ '' Icc 0 t' := by
    ext w
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.toNNReal, ⟨bot_le, Real.toNNReal_le_toNNReal hs.2⟩, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨(u : ℝ), ⟨u.2, ?_⟩, by simp⟩
      have := hu.2
      rw [← htt]; exact_mod_cast this
  rw [himg]
  set A := γ '' Icc 0 t'
  have hAc : IsCompact A := isCompact_Icc.image hγc
  obtain ⟨R, hR, hAR⟩ := exists_closure_subset_ball hAc.isBounded
  obtain ⟨⟨z, -, hcc⟩, hunb⟩ := hgen t'
  rw [htt] at hcc hunb
  have hcl : closure A = A := hAc.isClosed.closure_eq
  have hb : ¬ Bornology.IsBounded (connectedComponentIn (H \ closure A) z) := by
    rw [hcl, hcc]; exact hunb
  have hdiff : H \ fillH A = H \ fwdHull W t := by
    rw [H_diff_fillH hR hAR, ← connectedComponentIn_eq_of_not_isBounded hR hAR hb, hcl, hcc]
  have h1 : fwdHull W t ⊆ H := fun _ hz => hz.1
  rw [← sdiff_sdiff_cancel_left h1, ← hdiff, sdiff_sdiff_cancel_left (fillH_subset_H A)]

end InteractingSLE.SLE8.SpaceFilling
