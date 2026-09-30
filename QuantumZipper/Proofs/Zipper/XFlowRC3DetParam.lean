import QuantumZipper.Proofs.Zipper.JointModDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-FLOW-RC3, deterministic part: folded-circle means with a metric parameter

`continuousOn_integral_foldedCircle_param'` is `RegUnif.continuousOn_integral_foldedCircle_param`
(`JointModDet.lean`) with the time parameter `t ∈ [0,T]` replaced by a parameter `q` in a subset
`K` of a pseudo-metric space admitting a continuous retraction `ρ` onto `K` (used here for
`(u, s) ∈ [0,T]²`). The proof is the same, word for word, with `projIcc` replaced by `ρ`
(own elementary argument, as the original).
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real

namespace QuantumZipper
namespace F1

open RegCont TwoPoint RegUnif

/-- **Folded-circle means of an integrand with a metric parameter** are jointly continuous. -/
theorem continuousOn_integral_foldedCircle_param' {α : Type} [PseudoMetricSpace α]
    [LocallyCompactSpace α] {K : Set α}
    {ρ : α → α} (hρc : Continuous ρ) (hρK : ∀ q, ρ q ∈ K) (hρid : ∀ q ∈ K, ρ q = q)
    {G : α → ℂ → ℝ}
    (hGm : ∀ t ∈ K, Measurable (G t))
    (hGc : ContinuousOn (fun p : α × ℂ => G p.1 p.2) (K ×ˢ H))
    (hGb : ∀ R, ∃ A, 0 ≤ A ∧ ∀ t ∈ K, ∀ u ∈ H, ‖u‖ ≤ R →
      |G t u| ≤ A + |Real.log u.im|) :
    ContinuousOn (fun p : α × (ℂ × ℝ) => ∫ u, G p.1 u ∂foldedCircle p.2.1 p.2.2)
      (K ×ˢ {p : ℂ × ℝ | 0 < p.2}) := by
  rintro ⟨t₀, c₀, r₀⟩ ⟨ht₀, hr₀⟩
  have hr₀' : 0 < r₀ := hr₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set R := ‖c₀‖ + r₀ + 2 with hR
  have hR0 : 0 ≤ R := by positivity
  obtain ⟨A, hA0, hA⟩ := hGb (2 * R + 1)
  obtain ⟨τ, hτ0, hτ1, hτε⟩ := exists_tail_small (K := 18 * Real.sqrt (2 / r₀))
    (c := 2 * A + 4) (by positivity) (by positivity : 0 < ε / 3)
  set Gτ : α → ℂ → ℝ := fun t u => G (ρ t) (clampIm τ u) with hGτ
  have hGτc : Continuous fun p : α × ℂ => Gτ p.1 p.2 := by
    have hmap : Continuous (fun p : α × ℂ => (ρ p.1, clampIm τ p.2)) :=
      (hρc.comp continuous_fst).prodMk ((continuous_clampIm τ).comp continuous_snd)
    exact hGc.comp_continuous hmap fun p => ⟨hρK p.1,
      show 0 < (clampIm τ p.2).im by rw [clampIm_im]; exact lt_max_of_lt_right hτ0⟩
  have hGτm : ∀ t, Measurable (Gτ t) := fun t =>
    (hGτc.comp (continuous_const.prodMk continuous_id)).measurable
  have hIc : Continuous fun p : α × (ℂ × ℝ) => ∫ u, Gτ p.1 u ∂foldedCircle p.2.1 p.2.2 := by
    have e : (fun p : α × (ℂ × ℝ) => ∫ u, Gτ p.1 u ∂foldedCircle p.2.1 p.2.2) = fun p =>
        (2 * π)⁻¹ * ∫ θ in Icc 0 (2 * π), Gτ p.1 (foldH (circleMap p.2.1 p.2.2 θ)) := by
      funext p; rw [integral_foldedCircle_eq (hGτm p.1), integral_Icc_eq_integral_Ico]
    rw [e]
    have hc : Continuous (fun q : (α × (ℂ × ℝ)) × ℝ => circleMap q.1.2.1 q.1.2.2 q.2) := by
      simp only [circleMap]; fun_prop
    exact continuous_const.mul (continuous_parametric_integral_of_continuous
      (f := fun (p : α × (ℂ × ℝ)) (θ : ℝ) => Gτ p.1 (foldH (circleMap p.2.1 p.2.2 θ)))
      (hGτc.comp ((continuous_fst.comp continuous_fst).prodMk (continuous_foldH.comp hc)))
      isCompact_Icc)
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.1 (hIc.continuousAt (x := (t₀, c₀, r₀)))
    (ε / 3) (by positivity)
  have tail : ∀ q : α × (ℂ × ℝ), q.1 ∈ K → r₀ / 2 ≤ q.2.2 → ‖q.2.1‖ + q.2.2 ≤ R →
      |(∫ u, G q.1 u ∂foldedCircle q.2.1 q.2.2) - ∫ u, Gτ q.1 u ∂foldedCircle q.2.1 q.2.2| <
        ε / 3 := by
    intro q hq0 hq1 hq2
    have hq0' : 0 < q.2.2 := by linarith
    have hGτq : ∀ u, Gτ q.1 u = G q.1 (clampIm τ u) := fun u => by
      simp only [hGτ, hρid q.1 hq0]
    have hAq := hA q.1 hq0
    have hint1 := integrable_of_log_bound (hGm q.1 hq0) hAq q.2.1 hq0' (by linarith)
    have hint2 : Integrable (Gτ q.1) (foldedCircle q.2.1 q.2.2) := by
      refine (integrable_const (A + |Real.log τ| + |Real.log (2 * R + 1)|)).mono'
        (hGτm q.1).aestronglyMeasurable ?_
      filter_upwards [foldedCircle_ae_norm_le q.2.1 hq0'.le] with u hu
      have hcl : clampIm τ u ∈ H :=
        show 0 < (clampIm τ u).im by rw [clampIm_im]; exact lt_max_of_lt_right hτ0
      have hG2 := hAq _ hcl ((norm_clampIm_le hτ0.le u).trans (by linarith))
      rw [clampIm_im] at hG2
      have hmax : max u.im τ ≤ 2 * R + 1 :=
        max_le (by linarith [Complex.im_le_norm u]) (by linarith)
      have hl := abs_log_le_of_mem hτ0 (le_max_right u.im τ) hmax
      rw [Real.norm_eq_abs, hGτq]
      linarith
    rw [← integral_sub hint1 hint2]
    refine abs_integral_le_integral_abs.trans_lt ?_
    simp_rw [hGτq]
    refine (integral_abs_sub_clamp_le (hGm q.1 hq0) hA0 (R := R) hAq q.2.1 hq0' hτ0 hτ1
      hq2).trans_lt ?_
    refine lt_of_le_of_lt ?_ hτε
    have hs : Real.sqrt (τ / q.2.2) ≤ Real.sqrt (2 / r₀) * Real.sqrt τ := by
      rw [← Real.sqrt_mul (by positivity)]
      refine Real.sqrt_le_sqrt ?_
      calc τ / q.2.2 ≤ τ / (r₀ / 2) := div_le_div_of_nonneg_left hτ0.le (by positivity) hq1
        _ = 2 / r₀ * τ := by field_simp
    have hf : 0 ≤ 2 * A + 2 * |Real.log τ| + 4 := by positivity
    calc 18 * Real.sqrt (τ / q.2.2) * (2 * A + 2 * |Real.log τ| + 4)
        ≤ 18 * (Real.sqrt (2 / r₀) * Real.sqrt τ) * (2 * A + 2 * |Real.log τ| + 4) := by
          gcongr
      _ = 18 * Real.sqrt (2 / r₀) * Real.sqrt τ * (2 * A + 4 + 2 * |Real.log τ|) := by ring
  refine ⟨min δ₁ (min 1 (r₀ / 2)), by positivity, ?_⟩
  rintro ⟨t, c, r⟩ ⟨ht, -⟩ hp
  have hp1 : dist (t, c, r) (t₀, c₀, r₀) < δ₁ := hp.trans_le (min_le_left _ _)
  have hp2 : dist (t, c, r) (t₀, c₀, r₀) < 1 :=
    hp.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hp3 : dist (t, c, r) (t₀, c₀, r₀) < r₀ / 2 :=
    hp.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have e : dist (t, c, r) (t₀, c₀, r₀) = max (dist t t₀) (max (dist c c₀) (dist r r₀)) := by
    simp only [Prod.dist_eq]
  rw [e] at hp2 hp3
  have hc1 : ‖c - c₀‖ < 1 := by
    rw [← dist_eq_norm]; exact (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hp2)
  have hr1 : |r - r₀| < 1 := by
    rw [← Real.dist_eq]; exact (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hp2)
  have hr2 : |r - r₀| < r₀ / 2 := by
    rw [← Real.dist_eq]; exact (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hp3)
  have hn : ‖c‖ ≤ ‖c₀‖ + ‖c - c₀‖ := by
    have := norm_sub_norm_le c c₀; linarith
  have t1 := abs_lt.1 (tail (t, c, r) ht (by simp only; linarith [(abs_lt.1 hr2).1])
    (by simp only; linarith [(abs_lt.1 hr1).2]))
  have t3 := abs_lt.1 (tail (t₀, c₀, r₀) ht₀ (by simp only; linarith) (by simp only; linarith))
  have t2 : |(∫ u, Gτ t u ∂foldedCircle c r) - ∫ u, Gτ t₀ u ∂foldedCircle c₀ r₀| < ε / 3 := by
    have := hδ₁' hp1; rwa [Real.dist_eq] at this
  have t2' := abs_lt.1 t2
  rw [Real.dist_eq, abs_lt]
  simp only at t1 t3 ⊢
  constructor <;> linarith [t1.1, t1.2, t2'.1, t2'.2, t3.1, t3.2]

end F1
end QuantumZipper
