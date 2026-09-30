import QuantumZipper.Proofs.Zipper.FieldLawlerCoverDefs
import QuantumZipper.Proofs.Thm18.LWExcUpper

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM-COVER: `FLCoverStmt` from the image crosscut sum and the excursion lower bound

**Source.** L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*, EJP 20 (2015)
no. 10, arXiv:1407.3314: the proof of Prop. 3.4 (p. 9) gives `Σⱼ ℰ(ηⱼ, ·) ≤ c ε/R`
(`FLImageCrosscutSumStmt`), the proof of Prop. 3.1 (p. 7) gives
`ℰ_ℍ(η', ℝ₋) ≥ c (diam η'/dist(0, η') ∧ 1)` (`FLExcLowerStmt`). The remaining step, done here,
is the covering stated in the FL-THM docstring (FieldLawlerDefs.lean): every point under an
image crosscut `η'` with real endpoint `a` lies in `B̄(a, diam η')`, because
`ℍ \ B̄(a, diam η')` is connected, unbounded and disjoint from `η'`
(own elementary argument, the step FL leave implicit), so the disks `B(aⱼ, 2 diam η'ⱼ)` cover,
and `2 diam η'ⱼ / |aⱼ| ≤ (2/c₁) ℰⱼ`; unused indices get tiny dummy disks.
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- The real endpoint `a = η(0+)` of a crosscut lies in the closure of its arc. -/
lemma flCover_endpoint_mem_closure {η : ℝ → ℂ} {a : ℂ} (h0 : Tendsto η (𝓝[>] 0) (𝓝 a)) :
    a ∈ closure (arcH η) :=
  mem_closure_of_tendsto h0
    (Filter.mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) fun s hs => ⟨s, hs, rfl⟩)

/-- The arc lies in `B̄(a, diam η)`. -/
lemma flCover_arc_subset_closedBall {η : ℝ → ℂ} (hη : IsCrosscutH η) {a : ℂ}
    (h0 : Tendsto η (𝓝[>] 0) (𝓝 a)) : arcH η ⊆ closedBall a (Metric.diam (arcH η)) := by
  intro w hw
  have hb := lwExc_arc_isBounded hη
  rw [mem_closedBall, ← Metric.diam_closure]
  exact Metric.dist_le_diam_of_mem hb.closure (subset_closure hw)
    (flCover_endpoint_mem_closure h0)

/-- The diameter of a crosscut is positive. -/
lemma flCover_diam_pos {η : ℝ → ℂ} (hη : IsCrosscutH η) : 0 < Metric.diam (arcH η) := by
  have hb := lwExc_arc_isBounded hη
  have h1 : (1 / 4 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h2 : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hne : η (1 / 4) ≠ η (1 / 2) := fun he => by
    have := hη.2.1 h1 h2 he
    norm_num at this
  exact lt_of_lt_of_le (dist_pos.2 hne)
    (Metric.dist_le_diam_of_mem hb ⟨_, h1, rfl⟩ ⟨_, h2, rfl⟩)

/-- The upper half-plane outside `B̄(a, d)`, parametrized in polar coordinates about `a`. -/
def flCoverOuter (a : ℂ) (d : ℝ) : Set ℂ :=
  (fun q : ℝ × ℝ => a + (q.1 : ℂ) * exp ((q.2 : ℂ) * I)) '' (Ioi d ×ˢ Ioo 0 Real.pi)

lemma flCoverOuter_isPreconnected (a : ℂ) (d : ℝ) : IsPreconnected (flCoverOuter a d) :=
  (isPreconnected_Ioi.prod isPreconnected_Ioo).image _ (by fun_prop)

lemma flCoverOuter_norm {a : ℂ} {d : ℝ} (hd : 0 ≤ d) {z : ℂ} (hz : z ∈ flCoverOuter a d) :
    d < ‖z - a‖ ∧ 0 < z.im - a.im := by
  obtain ⟨⟨r, θ⟩, ⟨hr, hθ⟩, rfl⟩ := hz
  simp only [mem_Ioi] at hr
  have hr0 : d < r := hr
  refine ⟨?_, ?_⟩
  · simp only [add_sub_cancel_left, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    exact lt_of_lt_of_le hr0 (le_abs_self r)
  · have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    have : (a + (r : ℂ) * exp ((θ : ℂ) * I)).im - a.im = r * Real.sin θ := by
      rw [exp_mul_I]
      simp [← ofReal_cos, ← ofReal_sin]
    rw [this]
    exact mul_pos (by linarith) hs

lemma flCoverOuter_mem {a : ℝ} {d : ℝ} {p : ℂ} (hp : p ∈ H) (hd : d < ‖p - a‖) :
    p ∈ flCoverOuter a d := by
  have hp' : 0 < p.im := hp
  have hpim : 0 < (p - a).im := by simpa using hp'
  refine ⟨(‖p - a‖, arg (p - a)), ⟨hd, ?_, ?_⟩, ?_⟩
  · exact lt_of_le_of_ne (arg_nonneg_iff.2 hpim.le) (fun h => by
      have := (arg_eq_zero_iff.1 h.symm).2
      linarith)
  · exact arg_lt_pi_iff.2 (Or.inr hpim.ne')
  · simp only
    rw [norm_mul_exp_arg_mul_I]
    ring

lemma flCoverOuter_unbounded (a : ℂ) (d : ℝ) : ¬ Bornology.IsBounded (flCoverOuter a d) := by
  intro hb
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  set r : ℝ := |d| + ‖a‖ + |M| + 1
  have hrd : d < r := by
    simp only [r]
    linarith [le_abs_self d, norm_nonneg a, abs_nonneg M]
  have hpi1 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hpi2 : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
  have hmem : a + (r : ℂ) * exp (((Real.pi / 2 : ℝ) : ℂ) * I) ∈ flCoverOuter a d :=
    ⟨(r, Real.pi / 2), ⟨hrd, hpi1, hpi2⟩, rfl⟩
  have h1 := hM _ hmem
  have h2 : ‖(r : ℂ) * exp (((Real.pi / 2 : ℝ) : ℂ) * I)‖ = r := by
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have h3 := norm_sub_norm_le ((r : ℂ) * exp (((Real.pi / 2 : ℝ) : ℂ) * I)) (-a)
  rw [sub_neg_eq_add, norm_neg, h2, add_comm] at h3
  simp only [r] at h3
  linarith [le_abs_self M, abs_nonneg d]

/-- **Points under a crosscut are within its diameter of its endpoint** (own elementary
argument: `ℍ \ B̄(a, diam η)` is connected, unbounded and disjoint from `η`). -/
theorem flCover_le_diam_of_not_mem_hullComp {η : ℝ → ℂ} (hη : IsCrosscutH η) {a : ℝ}
    (h0 : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) {p : ℂ} (hp : p ∈ H) (hpn : p ∉ hullComp η) :
    ‖p - a‖ ≤ Metric.diam (arcH η) := by
  by_contra hlt
  push Not at hlt
  set d := Metric.diam (arcH η)
  have hd : 0 ≤ d := Metric.diam_nonneg
  have hsub : flCoverOuter a d ⊆ H \ arcH η := by
    intro z hz
    have hz' := flCoverOuter_norm hd hz
    refine ⟨by simpa [H] using hz'.2, fun hza => ?_⟩
    have := flCover_arc_subset_closedBall hη h0 hza
    rw [mem_closedBall, dist_eq_norm] at this
    linarith [hz'.1]
  have hpV := flCoverOuter_mem hp hlt
  have hpS : p ∈ H \ arcH η := hsub hpV
  have hcc := (flCoverOuter_isPreconnected (a : ℂ) d).subset_connectedComponentIn hpV hsub
  exact hpn ⟨hpS, fun hbd => flCoverOuter_unbounded (a : ℂ) d (hbd.subset hcc)⟩

/-- **FL-THM-COVER reduction.** `FLCoverStmt` from the image crosscut sum (FL proof of
Prop. 3.4) and the excursion lower bound (FL proof of Prop. 3.1 / Corollary 5.2). -/
theorem flCover_of_imageSum_excLower (hS : FLImageCrosscutSumStmt) (hL : FLExcLowerStmt) :
    FLCoverStmt := by
  obtain ⟨C, δ₁, hC, hδ₁, hN⟩ := hS
  obtain ⟨c₁, hc₁, hlow⟩ := hL
  refine ⟨2 * C / c₁ + 1, min (min δ₁ 1) (c₁ / (4 * (C + 1))), by positivity, by positivity, ?_⟩
  intro W hW hW0 t R ε ht hR hε hεR h1 h2 h3 h4 h5 h6 h7 h8
  have hδle1 : min (min δ₁ 1) (c₁ / (4 * (C + 1))) ≤ δ₁ :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hεR' : ε ≤ δ₁ * R := le_trans hεR (mul_le_mul_of_nonneg_right hδle1 hR.le)
  obtain ⟨S, η, a, b, h, hj, hsum, hcov⟩ := hN W hW hW0 t R ε ht hR hε hεR' h1 h2 h3 h4 h5 h6 h7 h8
  set q := ε / R with hqdef
  have hq0 : 0 < q := div_pos hε hR
  have hqδ : q ≤ min (min δ₁ 1) (c₁ / (4 * (C + 1))) := by
    rw [hqdef, div_le_iff₀ hR]; exact hεR
  have hq1 : q ≤ 1 := le_trans hqδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hCq : C * q ≤ c₁ / 4 := by
    have h4' : q ≤ c₁ / (4 * (C + 1)) := le_trans hqδ (min_le_right _ _)
    have : C * (c₁ / (4 * (C + 1))) ≤ c₁ / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    exact le_trans (mul_le_mul_of_nonneg_left h4' hC) this
  set F : ℕ → ℝ≥0∞ := fun j => S.indicator (fun j => excR (h j) {x : ℝ | x * a j ≤ 0}) j
    with hFdef
  have hFtop : ∑' j, F j ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
  have hFj : ∀ j, F j ≠ ⊤ := fun j => ne_top_of_le_ne_top hFtop (ENNReal.le_tsum j)
  -- per-crosscut consequences of the lower bound
  have key : ∀ j ∈ S, 4 * Metric.diam (arcH (η j)) ≤ |a j| ∧
      c₁ * (Metric.diam (arcH (η j)) / |a j|) ≤ (F j).toReal := by
    intro j hjS
    obtain ⟨hηj, h0j, h1j, habj, hHj⟩ := hj j hjS
    have hlo := hlow (η j) (a j) (b j) (h j) hηj h0j h1j habj hHj
    have hFeq : F j = excR (h j) {x : ℝ | x * a j ≤ 0} := by
      simp [hFdef, Set.indicator_of_mem hjS]
    rw [← hFeq] at hlo
    have ha : 0 < |a j| := abs_pos.2 (fun h0 => by simp [h0] at habj)
    have hd := flCover_diam_pos hηj
    have hx0 : 0 ≤ Metric.diam (arcH (η j)) / |a j| := by positivity
    have hup : c₁ * min (Metric.diam (arcH (η j)) / |a j|) 1 ≤ C * q := by
      have := le_trans hlo (le_trans (ENNReal.le_tsum j) hsum)
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
    have hmin : min (Metric.diam (arcH (η j)) / |a j|) 1 ≤ 1 / 4 := by
      have := le_trans hup hCq
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)] at this
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
      nlinarith [min_le_right (Metric.diam (arcH (η j)) / |a j|) 1]
    have hx : Metric.diam (arcH (η j)) / |a j| ≤ 1 / 4 := by
      by_contra hc
      push Not at hc
      have : 1 / 4 < min (Metric.diam (arcH (η j)) / |a j|) 1 := lt_min hc (by norm_num)
      linarith
    have hmin' : min (Metric.diam (arcH (η j)) / |a j|) 1 = Metric.diam (arcH (η j)) / |a j| :=
      min_eq_left (by linarith)
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ ha] at hx; linarith
    · rw [hmin'] at hlo
      exact (ENNReal.ofReal_le_iff_le_toReal (hFj j)).1 hlo
  classical
  refine ⟨fun j => if j ∈ S then a j else 1,
    fun j => if j ∈ S then 2 * Metric.diam (arcH (η j)) else (1 / 2) ^ j * (q / 4), ?_, ?_⟩
  · intro j
    by_cases hjS : j ∈ S
    · simp only [hjS, ite_true]
      exact ⟨by linarith [flCover_diam_pos (hj j hjS).1], by linarith [(key j hjS).1]⟩
    · simp only [hjS, ite_false, abs_one]
      have hp : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hp0 : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
      exact ⟨by positivity, by nlinarith⟩
  · set g : ℕ → ℝ := fun j => 2 / c₁ * (F j).toReal + (1 / 2 : ℝ) ^ j * (q / 4) with hgdef
    have hle : ∀ j, (if j ∈ S then 2 * Metric.diam (arcH (η j)) else (1 / 2 : ℝ) ^ j * (q / 4)) /
        |if j ∈ S then a j else 1| ≤ g j := by
      intro j
      have hT : 0 ≤ 2 / c₁ * (F j).toReal := by positivity
      have hG : 0 ≤ (1 / 2 : ℝ) ^ j * (q / 4) := by positivity
      by_cases hjS : j ∈ S
      · simp only [hjS, ite_true, hgdef]
        have h2 := (key j hjS).2
        have e : Metric.diam (arcH (η j)) / |a j| ≤ (F j).toReal / c₁ := by
          rw [le_div_iff₀ hc₁]; linarith
        have e2 : 2 * Metric.diam (arcH (η j)) / |a j| = 2 * (Metric.diam (arcH (η j)) / |a j|) :=
          by ring
        have e3 : 2 / c₁ * (F j).toReal = 2 * ((F j).toReal / c₁) := by ring
        rw [e2]
        linarith
      · simp only [hjS, ite_false, abs_one, div_one, hgdef]
        linarith
    have hnn : ∀ j, 0 ≤ (if j ∈ S then 2 * Metric.diam (arcH (η j)) else (1 / 2 : ℝ) ^ j * (q / 4)) /
        |if j ∈ S then a j else 1| := by
      intro j
      by_cases hjS : j ∈ S
      · simp only [hjS, ite_true]; positivity
      · simp only [hjS, ite_false]; positivity
    have hg : Summable g :=
      ((ENNReal.summable_toReal hFtop).mul_left _).add (summable_geometric_two.mul_right _)
    have hsumm := Summable.of_nonneg_of_le hnn hle hg
    refine ⟨hsumm, ?_, ?_⟩
    · have hX := ENNReal.toReal_le_of_le_ofReal (by positivity) hsum
      have hgs : ∑' j, g j = 2 / c₁ * (∑' j, F j).toReal + 2 * (q / 4) := by
        rw [hgdef, Summable.tsum_add ((ENNReal.summable_toReal hFtop).mul_left _)
          (summable_geometric_two.mul_right _), tsum_mul_left, tsum_mul_right, tsum_geometric_two,
          ENNReal.tsum_toReal_eq hFj]
      have hmono : 2 / c₁ * (∑' j, F j).toReal ≤ 2 / c₁ * (C * q) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
      have e : 2 / c₁ * (C * q) = 2 * C / c₁ * q := by ring
      calc _ ≤ ∑' j, g j := hsumm.tsum_le_tsum hle hg
        _ ≤ (2 * C / c₁ + 1) * q := by rw [hgs]; nlinarith
    · intro p hp hpε
      obtain ⟨j, hjS, hpj⟩ := hcov p hp hpε
      refine ⟨j, ?_⟩
      simp only [hjS, ite_true]
      have := flCover_le_diam_of_not_mem_hullComp (hj j hjS).1 (hj j hjS).2.1 hp hpj
      linarith [flCover_diam_pos (hj j hjS).1]

end FieldLawler
end QuantumZipper
