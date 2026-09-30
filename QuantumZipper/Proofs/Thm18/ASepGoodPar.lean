import QuantumZipper.Proofs.Thm18.ASepPar
import QuantumZipper.Proofs.Thm18.ASepSep
import QuantumZipper.Proofs.Thm18.ASepModA
import QuantumZipper.Proofs.Loewner.CaraRZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP: separated parameters are good (`BackSepI` at `τ' = 0` ⇒ `ParGood`)

If the folded circle `σ = fc(d, r)` gives no mass to the `δ`-thickening of the reverse hull of
`revDrv W τ a` (`BackSepI` at `τ' = 0`), `τ, a > 0`, and every real point `x ≠ 0` stays alive
under the flow (true a.s. for SLE_κ, κ ≤ 4: `RS.ae_real_alive`), then on a neighbourhood of
the folded circle in `ℍ̄` the scaled points avoid `0` and are not swallowed by time `τ`
(`sep_pointwise`). Ingredients: every point of the folded circle carries
mass on its neighbourhoods (`foldedCircle_pos_of_mem`, as `G3Fid.fc_dist_pos`), the reverse hull
at `τ' = 0` is the dilated forward hull (`ASep.revHull_revDrv_eq`), `0 ∈ closure` of the reverse
hull (`zero_mem_closure_revHull`), and the characterization of `ℍ ∖ K_τ`
(`FwdHolo.mem_compl_fwdHull_iff`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric Real
open scoped ENNReal Topology

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core

/-- Every point of the folded sphere carries mass on its open neighbourhoods. -/
theorem foldedCircle_pos_of_mem (c : ℂ) {ρ : ℝ} {U : Set ℂ} (hU : IsOpen U) (θ₀ : ℝ)
    (h : foldH (circleMap c ρ θ₀) ∈ U) : 0 < foldedCircle c ρ U := by
  have hUm := hU.measurableSet
  rw [foldedCircle, Measure.map_apply measurable_foldH hUm, circleUnif, Measure.smul_apply,
    Measure.map_apply (measurable_circleMap c ρ) (measurable_foldH hUm), smul_eq_mul,
    Measure.restrict_apply ((measurable_circleMap c ρ) (measurable_foldH hUm))]
  refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top) (ne_of_gt ?_)
  set V := circleMap c ρ ⁻¹' (foldH ⁻¹' U) with hVdef
  have hV : IsOpen V := hU.preimage (TwoPoint.continuous_foldH.comp (continuous_circleMap c ρ))
  set θ₁ := toIcoMod Real.two_pi_pos 0 θ₀ with hθ₁
  have hθI : θ₁ ∈ Ico 0 (0 + 2 * π) := toIcoMod_mem_Ico _ _ _
  rw [zero_add] at hθI
  have hθV : θ₁ ∈ V := by
    have : circleMap c ρ θ₁ = circleMap c ρ θ₀ := by
      rw [hθ₁, toIcoMod]
      exact (periodic_circleMap c ρ).sub_zsmul_eq _
    show foldH (circleMap c ρ θ₁) ∈ U
    rw [this]; exact h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV θ₁ hθV
  have hsub : Ioo θ₁ (min (θ₁ + ε) (2 * π)) ⊆ V ∩ Ico 0 (2 * π) := by
    intro θ hθ
    refine ⟨hball ?_, hθI.1.trans hθ.1.le, hθ.2.trans_le (min_le_right _ _)⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [hθ.1]
    · linarith [hθ.2.trans_le (min_le_left _ _)]
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo, ENNReal.ofReal_pos]
  have := hθI.2
  exact sub_pos.2 (lt_min (by linarith) this)

/-- Points of the folded sphere are at distance `≥ δ` from a set whose `δ`-thickening is null. -/
theorem le_infDist_of_thickening_null {d : ℂ} {r δ : ℝ} {K : Set ℂ}
    (hK : foldedCircle d r (thickening δ K) = 0) {y : ℂ} (hy : y ∈ foldSph d r) :
    ∀ h ∈ K, δ ≤ dist y h := by
  intro h hh
  by_contra hlt
  push_neg at hlt
  obtain ⟨x, hx, rfl⟩ := hy
  have hxc : ∃ θ, circleMap d r θ = x := by
    have hr : 0 ≤ r := by
      have := mem_sphere.1 hx; linarith [dist_nonneg (x := x) (y := d)]
    have : x ∈ range (circleMap d r) := by
      rw [range_circleMap, abs_of_nonneg hr]; exact hx
    exact this
  obtain ⟨θ, rfl⟩ := hxc
  have hopen : IsOpen (thickening δ K) := isOpen_thickening
  have hmem : foldH (circleMap d r θ) ∈ thickening δ K :=
    mem_thickening_iff.2 ⟨h, hh, hlt⟩
  exact (foldedCircle_pos_of_mem d hopen θ hmem).ne' hK

/-- **Separated parameters, pointwise.** Under `BackSepI` at `τ' = 0` with margin `δ`, every
point `w` of the closed `δ/2`-neighbourhood of the folded circle in `ℍ̄` satisfies `w ≠ 0`, and if
`w ∈ ℍ` then `a w` is not swallowed by time `τ`. (Uniform survival beyond `τ` on this
neighbourhood — the remaining half of `ParGood` — needs continuation near the real points.) -/
theorem sep_pointwise {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {d : ℂ} {r : ℝ} {p : Fin 2 → ℝ} (hτ : 0 < p 0) (ha : 0 < p 1) {δ : ℝ} (hδ : 0 < δ)
    (hnull : foldedCircle d r
      (thickening δ (revHull (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1)) = 0) :
    ∀ w ∈ cthickening (δ / 2) (foldSph d r) ∩ {w : ℂ | 0 ≤ w.im},
      w ≠ 0 ∧ (0 < w.im → (p 1 : ℂ) * w ∈ H \ fwdHull W (p 0)) := by
  set τ := p 0
  set a := p 1
  set Kr := revHull (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 with hKr
  have hfar := fun y hy => le_infDist_of_thickening_null hnull (y := y) hy
  have hrev : Kr = {w : ℂ | w ∈ H ∧ (a : ℂ) * w ∈ fwdHull W τ} := by
    rw [hKr, backDrv_zero]; exact revHull_revDrv_eq hW hW0 hτ ha
  have h0 : (0 : ℂ) ∈ closure Kr := by
    rw [hKr]
    refine CaraR.zero_mem_closure_revHull (continuous_backDrv hW τ 0 a) (by simp [backDrv]) ?_
    simp only [backDrv]; positivity
  intro w hw
  obtain ⟨hwK, hwH⟩ := hw
  have hwfar : ∀ h ∈ Kr, δ / 2 ≤ dist w h := by
    intro h hh
    have hδ2 : (0 : ℝ) ≤ δ / 2 := by positivity
    rw [(isCompact_foldSph d r).cthickening_eq_biUnion_closedBall hδ2] at hwK
    obtain ⟨y, hy, hyw⟩ := mem_iUnion₂.1 hwK
    have h1 : δ ≤ dist y h := hfar y hy h hh
    have h2 : dist w y ≤ δ / 2 := mem_closedBall.1 hyw
    have h3 := dist_triangle y w h
    rw [dist_comm y w] at h3
    linarith
  have hw0 : w ≠ 0 := by
    intro hw0
    obtain ⟨h, hh, hdist⟩ := Metric.mem_closure_iff.1 h0 (δ / 2) (by positivity)
    have h1 := hwfar h hh
    rw [hw0] at h1
    linarith
  refine ⟨hw0, fun hpos => ⟨?_, fun hK => ?_⟩⟩
  · show 0 < ((a : ℂ) * w).im
    simpa using mul_pos ha hpos
  · have hmem : w ∈ Kr := by rw [hrev]; exact ⟨hpos, hK⟩
    have h1 := hwfar w hmem
    rw [dist_self] at h1
    linarith

end ASep
end QuantumZipper
