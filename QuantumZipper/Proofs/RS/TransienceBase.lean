import QuantumZipper.Proofs.RS.TipB
import QuantumZipper.Proofs.Thm14.WeldingData
import QuantumZipper.Proofs.Loewner.CoreArc1
import Mathlib.Topology.MetricSpace.Sequences

/-!
# EXT-RS node BASE: the two limit points of `g₁` at the base of the curve

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §4, node **BASE** (deterministic).

Let `W` be a driver whose trace `η` is good (`RadialGood`), whose shifted driver
`W¹ = W(1+·) − W 1` has a good trace `η¹` lying in `ℍ` at positive times, and let `F` be the
Carathéodory extension of the reverse map `f̂₁ = revMap V 1` (`V = W(1−·) − W 1` on `[0,1]`).
Then:

* `car_zero_eq_trace`: `F 0 = η 1` (the tip);
* `zeroMinus_ne_zero_of_car`, `zeroPlus_ne_zero_of_car`: `0₋ ≠ 0 ≠ 0₊` when `η 1 ≠ 0`;
* `base_cluster`: if `0 ∈ closure (η '' [1,∞))` then `0₋` or `0₊` lies in
  `closure (η¹ '' [0,∞))`. Indeed `η (1+s) = F (η¹ s)` (P3(b)); `η¹ s` stays bounded (UB,
  `CoreArc.norm_revMap_sub_le`), so a subsequence converges to some `w ∈ ℍ̄` with `F w = 0`,
  and `F⁻¹{0} ∩ ℍ̄ = {0₋, 0₊}` by the two-sided boundary correspondence.
* `isSimpleCurveHull_revHull_of_good`: the hypothesis of `RevMapCaratheodory` at time 1.

Source: Rohde–Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), proof of Thm 7.1,
p. 34 ("a.s. there are two limit points `x₀, x₁` for `g₁(z)` as `z → 0` in `H₁`. Note that
`g₁(γ[1,∞))` has the same distribution as `γ[0,∞)` translated by `ξ(1)`"); Kemppainen, *SLE*,
Prop. 5.5 proof (p. 82). The boundary correspondence is `CaraR.revMapCaratheodory`.
-/

noncomputable section

open MeasureTheory Filter Set Complex
open scoped Topology

namespace QuantumZipper
namespace RS

variable {W : ℝ → ℝ}

/-- The time reversal of `W` at time `1`. -/
def trev1 (W : ℝ → ℝ) : ℝ → ℝ := fun r => W (1 - r) - W 1

theorem mem_H_mul_I {y : ℝ} (hy : 0 < y) : (y : ℂ) * I ∈ H := by
  show 0 < ((y : ℂ) * I).im
  simpa using hy

/-- The reverse map of `V` at time `1` is `f̂₁` on `ℍ`. -/
theorem revMap_eq_fwdMapInv_of_eqOn (hW : RadialGood W) {V : ℝ → ℝ}
    (hV : EqOn (trev1 W) V (Icc 0 1)) {w : ℂ} (hw : w ∈ H) :
    revMap V 1 w = fwdMapInv W 1 w := by
  rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW.1 hW.2.1 zero_le_one hw]
  exact (ReverseFlow.revMap_congr_drive w hV).symm

/-- `F 0 = η 1`: the Carathéodory extension sends `0` to the tip. -/
theorem car_zero_eq_trace (hW : RadialGood W) {V : ℝ → ℝ} (hV : EqOn (trev1 W) V (Icc 0 1))
    {F : ℂ → ℂ} (hF : Blueprint.IsCaratheodoryRevExt V 1 F) : F 0 = trace W 1 := by
  have hpath : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝[>] 0) (𝓝[Hbar] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun y hy =>
      le_of_lt (α := ℝ) (mem_H_mul_I hy)⟩
    have : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝 0) (𝓝 ((0 : ℝ) * I)) :=
      ((Complex.continuous_ofReal.mul continuous_const).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  have h1 := ((hF.2.1 0 (by simp [Hbar])).tendsto).comp hpath
  have h2 : Tendsto (fun y : ℝ => F ((y : ℂ) * I)) (𝓝[>] 0) (𝓝 (trace W 1)) := by
    refine (hW.tendsto zero_le_one).congr' (eventually_mem_nhdsWithin.mono fun y hy => ?_)
    show _ = F _
    rw [hF.1 (mem_H_mul_I hy), revMap_eq_fwdMapInv_of_eqOn hW hV (mem_H_mul_I hy)]
  exact tendsto_nhds_unique h1 h2

theorem car_zeroPlus_eq_zero {V : ℝ → ℝ} {F : ℂ → ℂ} (hF : Blueprint.IsCaratheodoryRevExt V 1 F) :
    F (zeroPlus V 1) = 0 := by
  have hm := WeldingUniqueness.zeroMinus_nonpos V 1
  have h := (hF.2.2.2.2.2.2 (zeroPlus V 1) (Thm14WeldingData.hbar_ofReal _) (zeroMinus V 1)
    (Thm14WeldingData.hbar_ofReal _)).2 (Or.inr ⟨zeroMinus V 1, ⟨le_rfl, hm⟩,
      Or.inr ⟨by rw [hF.2.2.2.2.1], rfl⟩⟩)
  rw [h, hF.2.2.2.1]

theorem zeroMinus_ne_zero_of_car (hW : RadialGood W) (htip : trace W 1 ≠ 0) {V : ℝ → ℝ}
    (hV : EqOn (trev1 W) V (Icc 0 1)) {F : ℂ → ℂ} (hF : Blueprint.IsCaratheodoryRevExt V 1 F) :
    zeroMinus V 1 ≠ 0 := by
  intro h
  have := hF.2.2.2.1
  rw [h, Complex.ofReal_zero, car_zero_eq_trace hW hV hF] at this
  exact htip this

theorem zeroPlus_ne_zero_of_car (hW : RadialGood W) (htip : trace W 1 ≠ 0) {V : ℝ → ℝ}
    (hV : EqOn (trev1 W) V (Icc 0 1)) {F : ℂ → ℂ} (hF : Blueprint.IsCaratheodoryRevExt V 1 F) :
    zeroPlus V 1 ≠ 0 := by
  intro h
  have := car_zeroPlus_eq_zero hF
  rw [h, Complex.ofReal_zero, car_zero_eq_trace hW hV hF] at this
  exact htip this

/-- The zero set of `F` in `ℍ̄` is `{0₋, 0₊}`. -/
theorem eq_zeroMinus_or_zeroPlus_of_car {V : ℝ → ℝ} {F : ℂ → ℂ}
    (hF : Blueprint.IsCaratheodoryRevExt V 1 F) {w : ℂ} (hw : w ∈ Hbar) (h0 : F w = 0) :
    w = zeroMinus V 1 ∨ w = zeroPlus V 1 := by
  have hm := WeldingUniqueness.zeroMinus_nonpos V 1
  have h := (hF.2.2.2.2.2.2 w hw (zeroMinus V 1) (Thm14WeldingData.hbar_ofReal _)).1
    (by rw [h0, hF.2.2.2.1])
  rcases h with h | ⟨s, hs, ⟨hws, hφ⟩ | ⟨hws, hs'⟩⟩
  · exact Or.inl h
  · have hφ0 : 0 ≤ weldingHom V 1 s := Real.sInf_nonneg fun _ hy => hy.1
    have : zeroMinus V 1 = 0 := le_antisymm hm (by rw [Complex.ofReal_inj] at hφ; linarith)
    have hs0 : s = 0 := le_antisymm hs.2 (by linarith [hs.1])
    left; rw [hws, this, hs0]
  · right
    rw [hws]
    have hs'' : s = zeroMinus V 1 := by exact_mod_cast hs'.symm
    rw [hs'', hF.2.2.2.2.1]

/-- `η (1 + s) = F (η¹ s)` for `s ≥ 0`. -/
theorem trace_one_add_eq_car (hW : RadialGood W) (hW1 : RadialGood (shiftDrive W 1))
    (hH1 : ∀ s > (0 : ℝ), trace (shiftDrive W 1) s ∈ H) {V : ℝ → ℝ}
    (hV : EqOn (trev1 W) V (Icc 0 1)) {F : ℂ → ℂ} (hF : Blueprint.IsCaratheodoryRevExt V 1 F)
    {s : ℝ} (hs : 0 ≤ s) : trace W (1 + s) = F (trace (shiftDrive W 1) s) := by
  rcases hs.lt_or_eq with hs | rfl
  · have h := trace_add_of_tendsto_shift hW.1 hW.2.1 zero_le_one hs.le (hH1 s hs)
      (hW1.tendsto hs.le)
    rw [h.2.2, hF.1 (hH1 s hs), revMap_eq_fwdMapInv_of_eqOn hW hV (hH1 s hs)]
  · rw [hW1.2.2.1, car_zero_eq_trace hW hV hF, add_zero]

/-- **BASE.** If the trace after time `1` accumulates at `0`, then the shifted trace accumulates
at `0₋` or at `0₊`. -/
theorem base_cluster (hW : RadialGood W) (hW1 : RadialGood (shiftDrive W 1))
    (hH1 : ∀ s > (0 : ℝ), trace (shiftDrive W 1) s ∈ H) {V : ℝ → ℝ} (hVc : Continuous V)
    (hV : EqOn (trev1 W) V (Icc 0 1)) {F : ℂ → ℂ} (hF : Blueprint.IsCaratheodoryRevExt V 1 F)
    (hz : (0 : ℂ) ∈ closure (trace W '' Ici 1)) :
    ((zeroMinus V 1 : ℝ) : ℂ) ∈ closure (trace (shiftDrive W 1) '' Ici 0) ∨
      ((zeroPlus V 1 : ℝ) : ℂ) ∈ closure (trace (shiftDrive W 1) '' Ici 0) := by
  set η1 := trace (shiftDrive W 1)
  obtain ⟨p, hp, hplim⟩ := mem_closure_iff_seq_limit.1 hz
  choose t ht htp using hp
  set w : ℕ → ℂ := fun n => η1 (t n - 1) with hw
  have hFw : ∀ n, F (w n) = p n := fun n => by
    rw [hw, ← trace_one_add_eq_car hW hW1 hH1 hV hF (by linarith [(mem_Ici.1 (ht n))]),
      add_sub_cancel, htp]
  have hwH : ∀ n, w n ∈ Hbar := fun n => by
    rcases (sub_nonneg.2 (mem_Ici.1 (ht n))).lt_or_eq with h | h
    · exact le_of_lt (α := ℝ) (hH1 _ h)
    · show trace (shiftDrive W 1) (t n - 1) ∈ Hbar
      rw [← h, hW1.2.2.1]; simp [Hbar]
  -- UB: `‖F w - w‖ ≤ C` on the sequence
  have hV0 : V 0 = 0 := by rw [← hV ⟨le_rfl, zero_le_one⟩]; simp [trev1]
  obtain ⟨M, hM⟩ : ∃ M, ∀ r ∈ Icc (0 : ℝ) 1, |V r| ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hVc.continuousOn).isBounded.exists_norm_le
    exact ⟨M, fun r hr => hM _ (mem_image_of_mem _ hr)⟩
  have hbd : ∀ n, ‖w n‖ ≤ ‖p n‖ + (12 * M + 8 * Real.sqrt 1) := fun n => by
    rcases (sub_nonneg.2 (mem_Ici.1 (ht n))).lt_or_eq with h | h
    · have hH := hH1 _ h
      have := CoreArc.norm_revMap_sub_le hVc hV0 zero_lt_one hM hH
      rw [← hF.1 hH, hFw n] at this
      have h2 := norm_sub_norm_le (w n) (p n)
      rw [← norm_neg, neg_sub] at this
      linarith
    · have : w n = 0 := by show trace (shiftDrive W 1) (t n - 1) = 0; rw [← h, hW1.2.2.1]
      rw [this, norm_zero]
      have := CoreArc.norm_revMap_sub_le hVc hV0 zero_lt_one hM (mem_H_mul_I one_pos)
      have h0 : (0 : ℝ) ≤ 12 * M + 8 * Real.sqrt 1 := (norm_nonneg _).trans this
      linarith [norm_nonneg (p n)]
  obtain ⟨R, hR⟩ : ∃ R, ∀ n, ‖p n‖ ≤ R := by
    obtain ⟨R, hR⟩ := hplim.norm.bddAbove_range
    exact ⟨R, fun n => hR ⟨n, rfl⟩⟩
  have hwb : ∀ n, w n ∈ Metric.closedBall (0 : ℂ) (R + (12 * M + 8 * Real.sqrt 1)) :=
    fun n => by
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith [hbd n, hR n]
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hwb
  have ha : a ∈ Hbar := isClosed_Hbar.mem_of_tendsto hlim (Eventually.of_forall fun n => hwH _)
  have hacl : a ∈ closure (η1 '' Ici 0) := mem_closure_of_tendsto hlim
    (Eventually.of_forall fun n => ⟨t (φ n) - 1, sub_nonneg.2 (mem_Ici.1 (ht (φ n))), rfl⟩)
  have hF1 : Tendsto (fun n => F (w (φ n))) atTop (𝓝 (F a)) :=
    (hF.2.1 a ha).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hlim, Eventually.of_forall fun n => hwH _⟩)
  have hF2 : Tendsto (fun n => F (w (φ n))) atTop (𝓝 0) := by
    simp only [hFw]
    exact hplim.comp hφ.tendsto_atTop
  have hFa : F a = 0 := tendsto_nhds_unique hF1 hF2
  rcases eq_zeroMinus_or_zeroPlus_of_car hF ha hFa with h | h
  · exact Or.inl (h ▸ hacl)
  · exact Or.inr (h ▸ hacl)

/-- The reverse hull of `V` at time `1` is a simple curve hull (the hypothesis of
`RevMapCaratheodory`). -/
theorem isSimpleCurveHull_revHull_of_good (hW : RadialGood W) (hinj : InjOn (trace W) (Ici 0))
    (hH : ∀ t > (0 : ℝ), trace W t ∈ H) (hhull : fwdHull W 1 = trace W '' Ioc 0 1)
    {V : ℝ → ℝ} (hV : EqOn (trev1 W) V (Icc 0 1)) :
    IsSimpleCurveHull (revHull V 1) := by
  have hrev : revHull V 1 = revHull (trev1 W) 1 := by
    unfold revHull
    congr 1
    exact image_congr fun w _ => (ReverseFlow.revMap_congr_drive w hV).symm
  have hTc : Continuous (trev1 W) := by unfold trev1; have := hW.1; fun_prop
  have hT0 : trev1 W 0 = 0 := by simp [trev1]
  rw [hrev, LoewnerAlgebra.revHull_eq_fwdHull_timeRev _ hTc hT0 one_pos]
  have hWW : (fun s => trev1 W (1 - s) - trev1 W 1) = W := by
    funext s; simp only [trev1, sub_sub_cancel, sub_self, hW.2.1]; ring
  rw [hWW, hhull]
  refine ⟨trace W, hW.2.2.2.1.mono Icc_subset_Ici_self, hinj.mono Icc_subset_Ici_self,
    by rw [hW.2.2.1]; simp, fun t ht => hH t ht.1, rfl⟩

end RS
end QuantumZipper
