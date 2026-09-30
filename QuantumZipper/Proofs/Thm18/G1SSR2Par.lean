import QuantumZipper.Proofs.Loewner.TwoPoint
import QuantumZipper.Proofs.LQG.RegularClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1SSR2 (4): moving folded circles against a parameter-dependent log-bounded integrand

Theorem 1.8, G1 zoom, toward `G1SidePushUCRepStmt`. Parametric version of
`TwoPoint.continuousOn_integral_foldedCircle`: if `G σ u` is jointly continuous on
`[0, σ₀] × ℍ` and `|G σ u| ≤ A_R + |log Im u|` on `ℍ ∩ B̄(0, R)` uniformly in `σ`, then
`(w, r, σ) ↦ ∫ G σ dfc(w, r)` is continuous on `{r > 0, σ ∈ [0, σ₀]}`. Same proof (truncation
`clampIm τ` of the imaginary part and the uniform tail bound `TwoPoint.integral_abs_sub_clamp_le`),
own elementary adaptation.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1SSR2

open TwoPoint

/-- **Continuity of folded-circle means of a parameter-dependent log-bounded integrand.** -/
theorem continuousOn_integral_fc_param {σ₀ : ℝ} {G : ℝ → ℂ → ℝ}
    (hGm : ∀ σ ∈ Icc 0 σ₀, Measurable (G σ))
    (hGc : ContinuousOn (fun q : ℝ × ℂ => G q.1 q.2) (Icc 0 σ₀ ×ˢ H))
    (hGb : ∀ R, ∃ A, 0 ≤ A ∧ ∀ σ ∈ Icc 0 σ₀, ∀ u ∈ H, ‖u‖ ≤ R →
      |G σ u| ≤ A + |Real.log u.im|) :
    ContinuousOn (fun p : ℂ × ℝ × ℝ => ∫ u, G p.2.2 u ∂foldedCircle p.1 p.2.1)
      {p | 0 < p.2.1 ∧ p.2.2 ∈ Icc 0 σ₀} := by
  intro p₀ hp₀
  have hr₀ : 0 < p₀.2.1 := hp₀.1
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set R := ‖p₀.1‖ + p₀.2.1 + 2 with hR
  have hR0 : 0 ≤ R := by positivity
  obtain ⟨A, hA0, hA⟩ := hGb (2 * R + 1)
  obtain ⟨τ, hτ0, hτ1, hτε⟩ := exists_tail_small (K := 18 * Real.sqrt (2 / p₀.2.1))
    (c := 2 * A + 4) (by positivity) (by positivity : 0 < ε / 3)
  set S' : Set (ℂ × ℝ × ℝ) := univ ×ˢ univ ×ˢ Icc 0 σ₀ with hS'
  have hclH : ∀ u : ℂ, clampIm τ u ∈ H := fun u =>
    show 0 < (clampIm τ u).im by rw [clampIm_im]; exact lt_max_of_lt_right hτ0
  have hQc : ContinuousOn (fun p : ℂ × ℝ × ℝ =>
      ∫ u, G p.2.2 (clampIm τ u) ∂foldedCircle p.1 p.2.1) S' := by
    refine RegClosure.continuousOn_integral_fc (P := ℂ × ℝ × ℝ) (S := S')
      (H := fun p u => G p.2.2 (clampIm τ u)) ?_ continuousOn_fst
      continuous_snd.fst.continuousOn
    refine hGc.comp ((continuous_fst.snd.snd).continuousOn.prodMk
      ((continuous_clampIm τ).comp continuous_snd).continuousOn) fun q hq => ⟨hq.1.2.2, hclH _⟩
  have hp₀S : p₀ ∈ S' := ⟨mem_univ _, mem_univ _, hp₀.2⟩
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousWithinAt_iff.1 (hQc p₀ hp₀S) (ε / 3)
    (by positivity)
  have tail : ∀ q : ℂ × ℝ × ℝ, q.2.2 ∈ Icc 0 σ₀ → p₀.2.1 / 2 ≤ q.2.1 → ‖q.1‖ + q.2.1 ≤ R →
      |(∫ u, G q.2.2 u ∂foldedCircle q.1 q.2.1) -
        ∫ u, G q.2.2 (clampIm τ u) ∂foldedCircle q.1 q.2.1| < ε / 3 := by
    intro q hqσ hq1 hq2
    have hq0 : 0 < q.2.1 := by linarith
    have hAq : ∀ u ∈ H, ‖u‖ ≤ 2 * R + 1 → |G q.2.2 u| ≤ A + |Real.log u.im| :=
      fun u hu huR => hA q.2.2 hqσ u hu huR
    have hint1 := integrable_of_log_bound (hGm _ hqσ) hAq q.1 hq0 (by linarith)
    have hint2 : Integrable (fun u => G q.2.2 (clampIm τ u)) (foldedCircle q.1 q.2.1) := by
      refine (integrable_const (A + |Real.log τ| + |Real.log (2 * R + 1)|)).mono'
        ((hGm _ hqσ).comp (continuous_clampIm τ).measurable).aestronglyMeasurable ?_
      filter_upwards [foldedCircle_ae_norm_le q.1 hq0.le] with u hu
      have hG2 := hAq _ (hclH u) ((norm_clampIm_le hτ0.le u).trans (by linarith))
      rw [clampIm_im] at hG2
      have hmax : max u.im τ ≤ 2 * R + 1 :=
        max_le (by linarith [Complex.im_le_norm u]) (by linarith)
      have hl := abs_log_le_of_mem hτ0 (le_max_right u.im τ) hmax
      rw [Real.norm_eq_abs]
      linarith
    rw [← integral_sub hint1 hint2]
    refine abs_integral_le_integral_abs.trans_lt ?_
    refine (integral_abs_sub_clamp_le (hGm _ hqσ) hA0 (R := R) hAq q.1 hq0 hτ0 hτ1
      hq2).trans_lt ?_
    refine lt_of_le_of_lt ?_ hτε
    have hs : Real.sqrt (τ / q.2.1) ≤ Real.sqrt (2 / p₀.2.1) * Real.sqrt τ := by
      rw [← Real.sqrt_mul (by positivity)]
      refine Real.sqrt_le_sqrt ?_
      calc τ / q.2.1 ≤ τ / (p₀.2.1 / 2) := div_le_div_of_nonneg_left hτ0.le (by positivity) hq1
        _ = 2 / p₀.2.1 * τ := by field_simp
    have hf : 0 ≤ 2 * A + 2 * |Real.log τ| + 4 := by positivity
    calc 18 * Real.sqrt (τ / q.2.1) * (2 * A + 2 * |Real.log τ| + 4)
        ≤ 18 * (Real.sqrt (2 / p₀.2.1) * Real.sqrt τ) * (2 * A + 2 * |Real.log τ| + 4) := by
          gcongr
      _ = 18 * Real.sqrt (2 / p₀.2.1) * Real.sqrt τ * (2 * A + 4 + 2 * |Real.log τ|) := by ring
  refine ⟨min δ₁ (min 1 (p₀.2.1 / 2)), by positivity, fun p hp hpd => ?_⟩
  have hp1 : dist p p₀ < δ₁ := hpd.trans_le (min_le_left _ _)
  have hp2 : dist p p₀ < 1 := hpd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hp3 : dist p p₀ < p₀.2.1 / 2 := hpd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hpS : p ∈ S' := ⟨mem_univ _, mem_univ _, hp.2⟩
  have t2 := hδ₁' hpS hp1
  rw [Prod.dist_eq, max_lt_iff, Prod.dist_eq, max_lt_iff] at hp2 hp3
  rw [dist_eq_norm] at hp2
  rw [Real.dist_eq, abs_lt] at hp2 hp3
  have hn : ‖p.1‖ ≤ ‖p₀.1‖ + ‖p.1 - p₀.1‖ := by
    have := norm_sub_norm_le p.1 p₀.1; linarith
  have t1 := abs_lt.1 (tail p hp.2 (by linarith [hp3.2.1.1]) (by linarith [hp2.1, hp2.2.1.2]))
  have t3 := abs_lt.1 (tail p₀ hp₀.2 (by linarith) (by linarith))
  rw [Real.dist_eq] at t2
  have t2' := abs_lt.1 t2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [t1.1, t1.2, t2'.1, t2'.2, t3.1, t3.2]

end G1SSR2
end Thm18Asm
end QuantumZipper
