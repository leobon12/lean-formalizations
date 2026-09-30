import QuantumZipper.Proofs.Thm18.ASepModI

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (mod J): `GenFam` for the A-sep family at `τ' = 0`

`genFam_muA0`: on any parameter set `S ⊆ [0,T] × [a₀,a₁]`, the family `muA0 W d r` satisfies the
hypotheses `GenFam` of the GENERIC-UC Kolmogorov step (GenUCKolm.lean): admissible probability
measures (`adm_muA0`) with the joint Hölder energy modulus (`energy_muA0_joint`). The uniform
lower bound `m` of the forward trajectories is the centre modulus (C1) `exists_fwdMap_lower`.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace QuantumZipper
namespace ASep

open GenUC

/-- **`GenFam` for the A-sep family at `τ' = 0`.** -/
theorem genFam_muA0 {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T α CH : ℝ} (hT : 0 < T)
    (hα : 0 < α) (hα1 : α ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ α)
    {d : ℂ} {r : ℝ} (hd : 0 ≤ d.im) (hr : 0 < r) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀)
    {S : Set (Fin 2 → ℝ)} (hS : IsCompact S)
    (hSb : ∀ p ∈ S, p 0 ∈ Icc (0 : ℝ) T ∧ p 1 ∈ Icc a₀ a₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgood : ∀ a ∈ Icc a₀ a₁,
      ∀ w ∈ Metric.cthickening δ (foldH '' Metric.sphere d r) ∩ {w : ℂ | 0 ≤ w.im},
      ∃ u, IsForwardSol W ((a : ℂ) * w) T u) :
    ∃ (M : ℝ≥0∞) (K c : ℝ), GenFam S (muA0 W d r) M K c := by
  clear hS hδ
  by_cases ha₀₁ : a₀ ≤ a₁
  swap
  · refine ⟨1, 0, 1, ⟨fun p hp => ?_, fun p hp => ?_, le_rfl, one_pos, fun p hp => ?_⟩⟩ <;>
    · have := (hSb p hp).2; exact absurd (this.1.trans this.2) ha₀₁
  have hgood0 : ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u := by
    intro a ha w hw
    refine hgood a ha w ⟨self_subset_cthickening _ hw, ?_⟩
    obtain ⟨y, -, rfl⟩ := hw
    show 0 ≤ (foldH y).im
    rw [TwoPoint.im_foldH]; exact abs_nonneg _
  have hsol : ∀ z ∈ scaledSph d r a₀ a₁, ∃ u, IsForwardSol W z T u := by
    rintro _ ⟨q, hq, rfl⟩; exact hgood0 q.1 hq.1 q.2 hq.2
  obtain ⟨m, hm, hlow⟩ := exists_fwdMap_lower hW hW0 hT.le (isCompact_scaledSph d r a₀ a₁) hsol
  obtain ⟨M, hM⟩ := RegCont.exists_abs_le_on_Icc hW T
  obtain ⟨K, c, hK, hc, hE⟩ := energy_muA0_joint hW hW0 hT.le hα hα1 hCH hH hd hr ha₀ ha₀₁
    hgood0 hm hlow hM
  refine ⟨1, K, c, ⟨fun p hp ρ hρ => ?_, fun p hp ρ hρ => ?_, hK, hc,
    fun p hp p' hp' ρ hρ ρ' hρ' => hE p p' (hSb p hp).1 (hSb p hp).2 (hSb p' hp').1
      (hSb p' hp').2 ρ hρ ρ' hρ'⟩⟩
  · exact (adm_muA0 hW hW0 hr ha₀ hm hgood0 hlow hM (hSb p hp).1 (hSb p hp).2 hρ).1
  · exact (adm_muA0 hW hW0 hr ha₀ hm hgood0 hlow hM (hSb p hp).1 (hSb p hp).2 hρ).2

end ASep
end QuantumZipper
