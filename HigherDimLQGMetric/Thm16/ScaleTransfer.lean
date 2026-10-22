import HigherDimLQGMetric.Frozen.IsWeakExpMetric
import HigherDimLQGMetric.Frozen.IsSharpWeakExpMetric
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prokhorov
import HigherDimLQGMetric.Select.MetricBorel
import HigherDimLQGMetric.Metric.ContMetric

/-! Bounded deterministic changes of normalization preserve the frozen `TightOver` property. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Topology TopologicalSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

private def l9c_smulLaw {d : ℕ}
    (p : ℝ × ProbabilityMeasure C(Rd d × Rd d, ℝ)) :
    ProbabilityMeasure C(Rd d × Rd d, ℝ) :=
  ((diracProba p.1).prod p.2).map (fun q : ℝ × C(Rd d × Rd d, ℝ) => q.1 • q.2)

private theorem l9c_continuous_smulLaw {d : ℕ} :
    Continuous (l9c_smulLaw (d := d)) :=
  (ProbabilityMeasure.continuous_map continuous_smul).comp
    (ProbabilityMeasure.continuous_prod.comp (continuous_diracProba.prodMap continuous_id))

private theorem l9c_toMeasure_smulLaw {d : ℕ} (a : ℝ)
    (ν : ProbabilityMeasure C(Rd d × Rd d, ℝ)) :
    ((l9c_smulLaw (a, ν) : ProbabilityMeasure C(Rd d × Rd d, ℝ)) :
      Measure C(Rd d × Rd d, ℝ)) =
      (ν : Measure C(Rd d × Rd d, ℝ)).map (fun D => a • D) := by
  show ((Measure.dirac a).prod (ν : Measure C(Rd d × Rd d, ℝ))).map _ = _
  rw [Measure.dirac_prod, Measure.map_map continuous_smul.measurable measurable_prodMk_left]
  rfl

theorem l9c_tightOver_smul {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {S : Set ℝ} {X Y : ℝ → Ω → C(Rd d × Rd d, ℝ)}
    {a : ℝ → ℝ} {m M : ℝ} (hm : 0 < m)
    (ha : ∀ r ∈ S, a r ∈ Icc m M)
    (hY : ∀ r ∈ S, Y r = fun ω => a r • X r ω)
    (hX : TightOver P X S) : TightOver P Y S := by
  have hmap (r : ℝ) (hr : r ∈ S) :
      P.map (Y r) = (P.map (X r)).map (fun D => a r • D) := by
    rw [hY r hr]
    exact (AEMeasurable.map_map_of_aemeasurable
      (continuous_const_smul _).measurable.aemeasurable (hX.1 r hr)).symm
  refine ⟨(fun r hr => by rw [hY r hr]; exact
    (continuous_const_smul _).measurable.aemeasurable.comp_aemeasurable (hX.1 r hr)), ?_, ?_⟩
  · have hT := hX.2.1
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hT ⊢
    intro ε hε
    obtain ⟨K, hK, hKε⟩ := hT ε hε
    have hK' := ((isCompact_Icc (a := m) (b := M)).prod hK).image
      (continuous_smul (M := ℝ) (X := C(Rd d × Rd d, ℝ)))
    refine ⟨_, hK', ?_⟩
    rintro μ ⟨r, hr, rfl⟩
    rw [hmap r hr, Measure.map_apply (continuous_const_smul _).measurable
      hK'.isClosed.measurableSet.compl]
    refine (measure_mono ?_).trans (hKε _ ⟨r, hr, rfl⟩)
    intro D hD hDK
    exact hD ⟨(a r, D), ⟨ha r hr, hDK⟩, rfl⟩
  · let T := {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ r ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (X r)}
    have hTt : IsTightMeasureSet
        {((ν : ProbabilityMeasure C(Rd d × Rd d, ℝ)) : Measure C(Rd d × Rd d, ℝ)) |
          ν ∈ T} :=
      hX.2.1.subset (by rintro _ ⟨ν, ⟨r, hr, hν⟩, rfl⟩; exact ⟨r, hr, hν⟩)
    have hK : IsCompact (l9c_smulLaw '' (Icc m M ×ˢ closure T)) :=
      ((isCompact_Icc (a := m) (b := M)).prod
        (isCompact_closure_of_isTightMeasureSet hTt)).image l9c_continuous_smulLaw
    have hsub : {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
        ∃ r ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (Y r)} ⊆
        l9c_smulLaw '' (Icc m M ×ˢ closure T) := by
      rintro ν ⟨r, hr, hν⟩
      refine ⟨(a r, (⟨P.map (X r), inferInstance⟩ :
        ProbabilityMeasure C(Rd d × Rd d, ℝ))),
        ⟨ha r hr, subset_closure ⟨r, hr, rfl⟩⟩, ?_⟩
      apply ProbabilityMeasure.toMeasure_injective
      refine (l9c_toMeasure_smulLaw _ _).trans ?_
      rw [hν, hmap r hr]
      rfl
    intro μ hμ
    obtain ⟨⟨a₀, ν⟩, ⟨ha₀, hν⟩, rfl⟩ := closure_minimal hsub hK.isClosed hμ
    rw [l9c_toMeasure_smulLaw, ae_map_iff (continuous_const_smul a₀).measurable.aemeasurable
      (measurableSet_isContinuousMetric_select d)]
    filter_upwards [hX.2.2 ν hν] with D hD
    exact (ContMetric.smul a₀ (hm.trans_le ha₀.1) ⟨D, hD⟩).2

private theorem l9c_normalizedAtScale_change {d : ℕ} (ξ : ℝ)
    (D : DistRd d → ContMetric d) (c : ℝ → ℝ) (α r : ℝ)
    (hcr : c r ≠ 0) (hpr : r ^ α ≠ 0) (H : DistRd d) :
    normalizedAtScale ξ D (fun s => s ^ α) H r =
      (c r / r ^ α) • normalizedAtScale ξ D c H r := by
  unfold normalizedAtScale
  rw [smul_smul]
  congr 1
  field_simp

/-- Uniform comparability of normalizers transfers every axiom of the weak class
to the sharp normalization. -/
theorem l9c_sharpWeak_of_powerBounds {d : ℕ} {ξ α : ℝ}
    {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) {C : ℝ} (hC : 1 ≤ C)
    (hc : ∀ r : ℝ, 0 < r →
      C⁻¹ * r ^ α ≤ c r ∧ c r ≤ C * r ^ α) :
    IsWeakExpMetric d ξ D (fun r => r ^ α) := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let b : ℝ → ℝ := fun r => c r / r ^ α
  have hb (r : ℝ) (hr : 0 < r) : b r ∈ Icc C⁻¹ C := by
    have hp : 0 < r ^ α := Real.rpow_pos_of_pos hr _
    obtain ⟨hl, hu⟩ := hc r hr
    constructor
    · exact (le_div_iff₀ hp).2 (by simpa [mul_comm] using hl)
    · exact (div_le_iff₀ hp).2 (by simpa [mul_comm] using hu)
  have hchange (r : ℝ) (hr : 0 < r) (H : DistRd d) :
      normalizedAtScale ξ D (fun s => s ^ α) H r =
        b r • normalizedAtScale ξ D c H r :=
    l9c_normalizedAtScale_change ξ D c α r (hD.c_pos r hr).ne'
      (Real.rpow_pos_of_pos hr α).ne' H
  have htransfer {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d) (S : Set ℝ)
      (hS : S ⊆ Ioi (0 : ℝ))
      (hT : TightOver P (fun r ω => normalizedAtScale ξ D c (h ω) r) S) :
      TightOver P (fun r ω => normalizedAtScale ξ D (fun s => s ^ α) (h ω) r) S := by
    apply l9c_tightOver_smul (a := b) (m := C⁻¹) (M := C)
      (inv_pos.mpr hCpos) (fun r hr => hb r (hS hr))
      (fun r hr => by funext ω; exact hchange r (hS hr) (h ω)) hT
  exact {
    measurable := hD.measurable
    length := hD.length
    locality := hD.locality
    weyl := hD.weyl
    translation := hD.translation
    c_pos := fun r hr => Real.rpow_pos_of_pos hr α
    tight := fun P _ h hh R hR =>
      htransfer P h (Ioo 0 R) (fun r hr => hr.1) (hD.tight P h hh R hR)
    tight_bdd := fun P _ h hh =>
      htransfer P h (Ioi 0) (fun r hr => hr) (hD.tight_bdd P h hh) }

end HigherDimLQGMetric
