import QuantumZipper.Proofs.Thm18.RTBeurNear
import QuantumZipper.Proofs.Thm18.RTBeurCircle

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-BEURLING, part 3: from a pointwise strip bound to the pulled-back mass bound

* `fwdMapInv_of_im_nonpos`, `measurable_fwdMapInv_rt`: `f_s⁻¹` is `0` off `ℍ` and measurable.
* `margin_of_circleOff`: a circle off `K` (after folding) has a closed-half-plane neighbourhood
  of its folded image that avoids `K`.
* `mass_of_pointwise`: if every point `v` of the folded circle is sent by `f` into a bounded set,
  and `Φ(f v) ≤ ρ ≤ ρ₀` forces `Im v ≤ A √ρ`, then the pushforward of the folded circle measure
  is carried by a bounded set and gives mass `≤ Cm q^k` to `{Φ ≤ 2^{-k}}`, `q = 2^{-1/4}`
  (`circleUnif_strip_le`). Own elementary argument (bookkeeping).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal ComplexConjugate

namespace QuantumZipper
namespace RTBeur

theorem measurable_foldH_rt : Measurable foldH := by
  unfold foldH
  exact Measurable.ite (measurableSet_le measurable_const Complex.measurable_im) measurable_id
    Complex.continuous_conj.measurable

theorem fwdMapInv_of_im_nonpos {W : ℝ → ℝ} (hWc : Continuous W) {s : ℝ} (hs : 0 ≤ s) {v : ℂ}
    (hv : v.im ≤ 0) : fwdMapInv W s v = 0 := by
  unfold fwdMapInv
  rw [dif_neg]
  rintro ⟨z', ⟨hz', hfz⟩, -⟩
  have := (RS.im_fwdMap_le_of_le hWc hs le_rfl hz').2
  rw [hfz] at this
  linarith

theorem measurable_fwdMapInv_rt {W : ℝ → ℝ} (hWc : Continuous W) (hW0 : W 0 = 0) {s : ℝ}
    (hs : 0 ≤ s) : Measurable (fwdMapInv W s) := by
  classical
  have hH : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  have e : fwdMapInv W s = H.piecewise (fwdMapInv W s) (fun _ => 0) := by
    funext v
    by_cases hv : v ∈ H
    · simp [Set.piecewise, hv]
    · simp only [Set.piecewise, hv, if_false]
      exact fwdMapInv_of_im_nonpos hWc hs (not_lt.1 hv)
  rw [e]
  exact ContinuousOn.measurable_piecewise (E6.continuousOn_fwdMapInv_H hWc hW0 hs)
    continuousOn_const hH.measurableSet

/-- The folded neighbourhood of a circle that is off `K`. -/
theorem margin_of_circleOff {K : Set ℂ} {d : ℂ} {r : ℝ} (h : CircleOff K d r) :
    ∃ δ₀ > 0, ∀ v : ℂ, (dist v d = r ∨ dist v (conj d) = r) → ∀ w : ℂ, 0 ≤ w.im →
      dist w v < δ₀ → w ∉ K := by
  obtain ⟨δ, hδ, hK⟩ := h
  refine ⟨δ, hδ, fun v hv w hw hwv => ?_⟩
  rcases hv with hv | hv
  · have h1 := dist_triangle w v d
    have h2 := dist_triangle v w d
    rw [dist_comm v w] at h2
    have := hK w (by rw [abs_lt]; constructor <;> linarith)
    rwa [show foldH w = w from if_pos hw] at this
  · have e1 : dist (conj w) d = dist w (conj d) := by
      rw [← Complex.dist_conj_conj, Complex.conj_conj]
    have h1 := dist_triangle w v (conj d)
    have h2 := dist_triangle v w (conj d)
    rw [dist_comm v w] at h2
    have := hK (conj w) (by rw [e1, abs_lt]; constructor <;> linarith)
    have e2 : foldH (conj w) = w := by
      unfold foldH
      split_ifs with hc
      · have : w.im = 0 := by simp at hc; linarith
        apply Complex.ext <;> simp [this]
      · simp
    rwa [e2] at this

/-- Points of the closed upper half-plane are closer to each other than to reflections. -/
theorem dist_le_dist_conj {z p : ℂ} (hz : 0 ≤ z.im) (hp : 0 ≤ p.im) :
    dist z p ≤ dist z (conj p) := by
  rw [Complex.dist_eq, Complex.dist_eq]
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  nlinarith [mul_nonneg hz hp]

theorem sqrt_sqrt_radius (k : ℕ) :
    Real.sqrt (Real.sqrt (radius k)) = Real.sqrt (Real.sqrt 2⁻¹) ^ k := by
  induction k with
  | zero => simp [radius]
  | succ k ih =>
    rw [pow_succ, ← ih, radius, pow_succ, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (Real.sqrt_nonneg _)]
    rfl

/-- **From the pointwise strip bound to the mass bound.** -/
theorem mass_of_pointwise {f : ℂ → ℂ} (hf : Measurable f) {Φ : ℂ → ℝ} (hΦ : Continuous Φ)
    {d : ℂ} {r : ℝ} (hr : 0 < r) {Rr A ρ₀ : ℝ} (hA : 0 ≤ A) (hρ₀ : 0 < ρ₀)
    (hsupp : ∀ v : ℂ, 0 ≤ v.im → (dist v d = r ∨ dist v (conj d) = r) → ‖f v‖ ≤ Rr)
    (hkey : ∀ v : ℂ, 0 ≤ v.im → (dist v d = r ∨ dist v (conj d) = r) → ∀ ρ : ℝ, 0 < ρ →
      ρ ≤ ρ₀ → Φ (f v) ≤ ρ → v.im ≤ A * Real.sqrt ρ) :
    ∃ Cm q : ℝ, 0 ≤ Cm ∧ 0 ≤ q ∧ q < 1 ∧
      (foldedCircle d r).map f {w | ¬ ‖w‖ ≤ Rr} = 0 ∧
      ∀ k : ℕ, (foldedCircle d r).map f {w | Φ w ≤ radius k} ≤ ENNReal.ofReal (Cm * q ^ k) := by
  set ν := foldedCircle d r with hν
  set Z : Set ℂ := {v | 0 ≤ v.im ∧ (dist v d = r ∨ dist v (conj d) = r)} with hZ
  have hZc : IsClosed Z :=
    (isClosed_le continuous_const Complex.continuous_im).inter
      ((isClosed_eq (continuous_id.dist continuous_const) continuous_const).union
        (isClosed_eq (continuous_id.dist continuous_const) continuous_const))
  have hfoldZ : ∀ u : ℂ, dist u d = r → foldH u ∈ Z := by
    intro u hu
    unfold foldH
    split_ifs with h
    · exact ⟨h, Or.inl hu⟩
    · refine ⟨by simp; linarith, Or.inr ?_⟩
      rw [Complex.dist_conj_conj]; exact hu
  have hνZ : ν Zᶜ = 0 := by
    rw [hν, foldedCircle, Measure.map_apply measurable_foldH_rt hZc.measurableSet.compl]
    unfold circleUnif
    rw [Measure.smul_apply, Measure.map_apply (measurable_circleMap d r)
      (measurable_foldH_rt hZc.measurableSet.compl)]
    have : circleMap d r ⁻¹' (foldH ⁻¹' Zᶜ) = ∅ := by
      ext θ
      simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
      exact hfoldZ _ (mem_sphere.1 (circleMap_mem_sphere d hr.le θ))
    rw [this, measure_empty, smul_zero]
  set q : ℝ := Real.sqrt (Real.sqrt 2⁻¹) with hq
  have hq1 : q < 1 := by
    rw [hq, Real.sqrt_lt' one_pos, one_pow, Real.sqrt_lt' one_pos, one_pow]
    norm_num
  set Cm : ℝ := 3 / 2 * Real.sqrt (A / r) + 1 / Real.sqrt (Real.sqrt ρ₀) with hCm
  have hssρ₀ : 0 < Real.sqrt (Real.sqrt ρ₀) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hρ₀)
  have hCm0 : 0 ≤ Cm := by positivity
  refine ⟨Cm, q, hCm0, Real.sqrt_nonneg _, hq1, ?_, fun k => ?_⟩
  · rw [Measure.map_apply hf (s := {w | ¬ ‖w‖ ≤ Rr})
      (measurableSet_le continuous_norm.measurable measurable_const).compl]
    refine measure_mono_null (t := Zᶜ) (fun v hv => ?_) hνZ
    intro hvZ
    exact hv (hsupp v hvZ.1 hvZ.2)
  have hSm : MeasurableSet {w | Φ w ≤ radius k} :=
    (isClosed_le hΦ continuous_const).measurableSet
  rw [Measure.map_apply hf hSm]
  have hrk : 0 < radius k := by unfold radius; positivity
  have hqk : q ^ k = Real.sqrt (Real.sqrt (radius k)) := (sqrt_sqrt_radius k).symm
  by_cases hk : radius k ≤ ρ₀
  · set ε : ℝ := A * Real.sqrt (radius k) with hε
    have hε0 : 0 ≤ ε := by positivity
    set G : Set ℂ := {u | |u.im| ≤ ε} with hG
    have hGm : MeasurableSet G :=
      measurableSet_le (Complex.continuous_im.abs.measurable) measurable_const
    have hsub : f ⁻¹' {w | Φ w ≤ radius k} ⊆ G ∪ Zᶜ := by
      intro v hv
      by_cases hvZ : v ∈ Z
      · left
        have := hkey v hvZ.1 hvZ.2 (radius k) hrk hk hv
        show |v.im| ≤ ε
        rw [abs_of_nonneg hvZ.1]; exact this
      · exact Or.inr hvZ
    have hνG : ν G ≤ ENNReal.ofReal (3 / 2 * Real.sqrt (ε / r)) := by
      rw [hν, foldedCircle, Measure.map_apply measurable_foldH_rt hGm]
      have : foldH ⁻¹' G = {u : ℂ | |u.im| ≤ ε} := by
        ext u
        simp only [mem_preimage, hG, mem_setOf_eq]
        unfold foldH
        split_ifs <;> simp
      rw [this]
      exact circleUnif_strip_le d hr hε0
    calc ν (f ⁻¹' {w | Φ w ≤ radius k}) ≤ ν (G ∪ Zᶜ) := measure_mono hsub
      _ ≤ ν G + ν Zᶜ := measure_union_le _ _
      _ = ν G := by rw [hνZ, add_zero]
      _ ≤ ENNReal.ofReal (3 / 2 * Real.sqrt (ε / r)) := hνG
      _ ≤ ENNReal.ofReal (Cm * q ^ k) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e : ε / r = A / r * Real.sqrt (radius k) := by rw [hε]; ring
        rw [e, Real.sqrt_mul (div_nonneg hA hr.le), ← hqk, hCm]
        have : 0 ≤ 1 / Real.sqrt (Real.sqrt ρ₀) * q ^ k := by positivity
        nlinarith
  · push Not at hk
    have hle : Real.sqrt (Real.sqrt ρ₀) ≤ q ^ k := by
      rw [hqk]; exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hk.le)
    calc ν (f ⁻¹' {w | Φ w ≤ radius k}) ≤ ν univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (Cm * q ^ k) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : 1 ≤ 1 / Real.sqrt (Real.sqrt ρ₀) * q ^ k := by
          rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hssρ₀, one_mul]; exact hle
        have : 0 ≤ 3 / 2 * Real.sqrt (A / r) * q ^ k := by positivity
        rw [hCm]; nlinarith

end RTBeur
end QuantumZipper
