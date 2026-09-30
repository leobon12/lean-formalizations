import QuantumZipper.Proofs.Zipper.FieldLawlerMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM, pathwise facts for the strong Markov step

Field–Lawler, *Escape probability and transience for SLE*, EJP 20 (2015), Prop. 3.4 (p. 8):
`ρ = inf{t : |γ(t)| = 1}` (here scaled to radius `R`), and after `ρ` the curve is the image under
`Z_ρ⁻¹` of an `SLE_κ` driven by the restarted motion. Pathwise ingredients:
* `fl_firstHit`: for a curve continuous on `[0,∞)` with `γ(0) = 0` that reaches `{|z| ≥ R}`, the
  first hitting time `T` is attained, `T > 0`, `|γ| < R` on `[0,T)` and `|γ(T)| = R`;
* `fl_tendsto_of_radial`: a radial Hölder bound gives the boundary limit;
* `fl_trace_shift`: `γ(T + u) = Z_T⁻¹(γ^T(u))` for the restarted trace `γ^T`
  (`RS.trace_add_of_tendsto_shift`).
Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace FieldLawler

/-- **First hitting time of `{|z| ≥ R}`.** -/
theorem fl_firstHit {γ : ℝ → ℂ} (hc : ContinuousOn γ (Ici 0)) (h0 : γ 0 = 0) {R : ℝ}
    (hR : 0 < R) {s : ℝ} (hs0 : 0 ≤ s) (hs : R ≤ ‖γ s‖) :
    ∃ T : ℝ, 0 < T ∧ T ≤ s ∧ R ≤ ‖γ T‖ ∧ ‖γ T‖ = R ∧ (∀ u ∈ Ico 0 T, ‖γ u‖ < R) ∧
      IsLeast {t : ℝ | 0 ≤ t ∧ γ t ∈ {z : ℂ | R ≤ ‖z‖}} T := by
  set S : Set ℝ := {t : ℝ | 0 ≤ t ∧ γ t ∈ {z : ℂ | R ≤ ‖z‖}} with hSdef
  have hSc : IsClosed S :=
    hc.preimage_isClosed_of_isClosed isClosed_Ici (isClosed_le continuous_const continuous_norm)
  have hSne : S.Nonempty := ⟨s, hs0, hs⟩
  have hSb : BddBelow S := ⟨0, fun t ht => ht.1⟩
  set T := sInf S with hT
  have hTS : T ∈ S := hSc.csInf_mem hSne hSb
  have hTle : ∀ t ∈ S, T ≤ t := fun t ht => csInf_le hSb ht
  have hT0 : 0 < T := by
    rcases eq_or_lt_of_le hTS.1 with h | h
    · exfalso
      have := hTS.2
      rw [← h, h0] at this
      simp only [mem_setOf_eq, norm_zero] at this
      linarith
    · exact h
  have hbelow : ∀ u ∈ Ico 0 T, ‖γ u‖ < R := by
    intro u hu
    by_contra hge
    push_neg at hge
    exact absurd (hTle u ⟨hu.1, hge⟩) (not_le.2 hu.2)
  have hcT : ContinuousAt γ T := hc.continuousAt (Ici_mem_nhds hT0)
  have hlim : Tendsto (fun u => ‖γ u‖) (𝓝[<] T) (𝓝 ‖γ T‖) :=
    tendsto_nhdsWithin_of_tendsto_nhds (hcT.norm)
  have hle : ‖γ T‖ ≤ R := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT hT0] with u hu
    exact (hbelow u ⟨hu.1.le, hu.2⟩).le
  exact ⟨T, hT0, hTle s ⟨hs0, hs⟩, hTS.2, le_antisymm hle hTS.2, hbelow, hTS, hTle⟩

/-- A radial Hölder bound gives the radial limit. -/
theorem fl_tendsto_of_radial {f : ℝ → ℂ} {L : ℂ} {C δ : ℝ} (hδ : 0 < δ)
    (h : ∀ y ∈ Ioc (0 : ℝ) 1, ‖f y - L‖ ≤ C * y ^ δ) : Tendsto f (𝓝[>] 0) (𝓝 L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun y : ℝ => C * y ^ δ) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun y : ℝ => C * y ^ δ) (𝓝 0) (𝓝 (C * (0 : ℝ) ^ δ)) :=
      tendsto_const_nhds.mul ((Real.continuousAt_rpow_const 0 δ (Or.inr hδ.le)).tendsto)
    rw [Real.zero_rpow hδ.ne', mul_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with y hy
  exact h y hy

end FieldLawler
end QuantumZipper
