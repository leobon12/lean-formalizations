import HigherDimLQGMetric.Thm13.Decomp
import HigherDimLQGMetric.Determ.StableLU

/-! Almost-sure compact-open convergence implies the probability form of
local-uniform convergence used in Theorem 1.3. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l8_tendstoInProbLU_of_ae
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ))
    (Y : Ω → C(Rd d × Rd d, ℝ))
    (hX : ∀ n, AEMeasurable (X n) P) (_hY : Measurable Y)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    TendstoInProbLU P (fun n ω => X n ω) atTop (fun ω => Y ω) := by
  intro R _ δ hδ
  let K : Set (Rd d × Rd d) :=
    closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R
  letI : CompactSpace K :=
    isCompact_iff_compactSpace.mp
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  let ρ : C(Rd d × Rd d, ℝ) → C(K, ℝ) :=
    fun u => u.restrict K
  have hρ : Continuous ρ := ContinuousMap.continuous_restrict _
  let X' : ℕ → Ω → C(Rd d × Rd d, ℝ) := fun n => (hX n).mk _
  have hXm (n : ℕ) : Measurable (X' n) := (hX n).measurable_mk
  have hXe (n : ℕ) : X n =ᵐ[P] X' n := (hX n).ae_eq_mk
  have hTIM : TendstoInMeasure P (fun n ω => ρ (X' n ω)) atTop
      (fun ω => ρ (Y ω)) := by
    refine tendstoInMeasure_of_tendsto_ae
      (fun n => (hρ.measurable.comp (hXm n)).aestronglyMeasurable) ?_
    filter_upwards [hae, ae_all_iff.2 hXe] with ω ht he
    have ht' : Tendsto (fun n => X' n ω) atTop (𝓝 (Y ω)) := by
      simpa only [← he] using ht
    exact (hρ.tendsto _).comp ht'
  have hk := hTIM (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hk
    (fun _ => zero_le) fun n => measure_mono_ae ?_
  filter_upwards [hXe n] with ω hω hmem
  change ENNReal.ofReal δ ≤ _ at hmem ⊢
  refine hmem.trans (iSup₂_le fun p hp => ?_)
  have h1 : X n ω p = ρ (X' n ω) ⟨p, hp⟩ := by
    rw [hω]
    rfl
  have h2 : Y ω p = ρ (Y ω) ⟨p, hp⟩ := rfl
  rw [h1, h2, edist_dist, edist_dist]
  exact ENNReal.ofReal_le_ofReal (ContinuousMap.dist_apply_le_dist _)

end HigherDimLQGMetric
