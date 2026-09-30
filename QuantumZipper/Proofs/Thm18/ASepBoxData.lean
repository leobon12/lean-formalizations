import QuantumZipper.Proofs.Thm18.ASepPFacts
import QuantumZipper.Proofs.Thm18.ASepPar

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP: box data for a rational box of good parameters

For a nonempty rational box of good parameters (`ASep.ParGood`, flow from the `δ`-neighbourhood
of the scaled folded circle survives beyond `τ`), the uniform data used by `ASep.genFam_muA0`,
`ASep.det_unif_A0`, `ASep.ae_exact_free_box` and `ASep.pfacts_A0`: a horizon `T`, scale bounds
`a₀ > 0`, `a₁`, a margin `δ`, survival up to `T` for all scales of the box, and survival beyond `τ`
at every parameter (`boxData_A0`). Own bookkeeping (uniform margin `exists_unif_of_isCompact`).
-/

noncomputable section

open MeasureTheory Set Filter Metric

namespace QuantumZipper
namespace ASep

open GenUC

/-- **Box data.** -/
theorem boxData_A0 {W : ℝ → ℝ} {d : ℂ} {r : ℝ} (hr : 0 < r) {lo hi : Fin 2 → ℚ}
    (hsub : ratBox lo hi ⊆ {p | ParGood W (foldSph d r) p}) (hne : (ratBox lo hi).Nonempty) :
    ∃ T a₀ a₁ δ : ℝ, 0 < T ∧ 0 < a₀ ∧ 0 < δ ∧ (∀ i, (lo i : ℝ) ≤ hi i) ∧
      (∀ p ∈ ratBox lo hi, p 0 ∈ Icc (0 : ℝ) T ∧ p 1 ∈ Icc a₀ a₁ ∧ 0 < p 0) ∧
      (∀ a ∈ Icc a₀ a₁,
        ∀ w ∈ Metric.cthickening δ (foldH '' Metric.sphere d r) ∩ {w : ℂ | 0 ≤ w.im},
        ∃ u, IsForwardSol W ((a : ℂ) * w) T u) ∧
      ∀ p ∈ ratBox lo hi, ∀ w ∈ cthickening δ (foldSph d r) ∩ {w : ℂ | 0 ≤ w.im},
        ∃ T' > p 0, ∃ u, IsForwardSol W ((p 1 : ℂ) * w) T' u := by
  have hR : (0 : ℝ) ≤ ‖d‖ + r := by positivity
  have hK : foldSph d r ⊆ closedBall 0 (‖d‖ + r) := fun x hx => by
    rw [mem_closedBall, dist_zero_right]; exact norm_le_of_mem_foldSph hx
  obtain ⟨δ, hδ, hu⟩ := exists_unif_of_isCompact hR hK (isCompact_ratBox lo hi) hsub
  obtain ⟨p₀, hp₀⟩ := hne
  have hlohi : ∀ i, (lo i : ℝ) ≤ hi i := fun i =>
    ((hp₀ i (mem_univ i)).1).trans (hp₀ i (mem_univ i)).2
  set q : ℝ → Fin 2 → ℝ := fun a i => if i = 0 then (hi 0 : ℝ) else a with hq
  have hq0 : ∀ a, q a 0 = hi 0 := fun a => by simp [hq]
  have hq1 : ∀ a, q a 1 = a := fun a => by simp [hq]
  have hqS : ∀ a ∈ Icc (lo 1 : ℝ) (hi 1), q a ∈ ratBox lo hi := by
    intro a ha i _
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, hq0]; exact ⟨hlohi 0, le_rfl⟩
    · simp only [Fin.mk_one, Fin.isValue, hq1]; exact ha
  have hlo1 : (lo 1 : ℝ) ∈ Icc (lo 1 : ℝ) (hi 1) := ⟨le_rfl, hlohi 1⟩
  obtain ⟨hpos0, hpos1, -⟩ := hsub (hqS _ hlo1)
  rw [hq0] at hpos0
  rw [hq1] at hpos1
  refine ⟨hi 0 + δ / 2, lo 1, hi 1, δ, by linarith, hpos1, hδ, hlohi, fun p hp => ?_,
    fun a ha w hw => ?_, fun p hp w hw => ?_⟩
  · have h0 := hp 0 (mem_univ 0)
    have h1 := hp 1 (mem_univ 1)
    have hpos := (hsub hp).1
    exact ⟨⟨hpos.le, by linarith [h0.2]⟩, h1, hpos⟩
  · obtain ⟨u, hu'⟩ := hu (q a) (hqS a ha) w hw
    rw [hq0, hq1] at hu'
    exact ⟨u, isForwardSol_restrict hu' (by linarith) (by linarith)⟩
  · obtain ⟨u, hu'⟩ := hu p hp w hw
    exact ⟨p 0 + δ, by linarith, u, hu'⟩

end ASep
end QuantumZipper
