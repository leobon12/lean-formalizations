import SupercriticalLQGUniqueness.Frozen.IsHeatSmoothing
import SupercriticalLQGUniqueness.Frozen.IsNormalizedWholePlaneGFF
import LQGMetric.Papers.DFGPS.L2_1PolarJoint

/-!
# A jointly continuous heat-kernel version

The heat field `h*_ε(z)` is the limit of the positive-time truncated pairings in
`LQGMetric.heatMollify`.  DFGPS proves that these limits exist simultaneously and form a jointly
continuous field in `(ε,z)`.  This file packages that result in the continuous-map carrier used by
the frozen statement surface.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open LQGMetric (DistC heatMollify heatTrunc)
open SupercriticalLQGUniqueness (IsHeatSmoothing IsNormalizedWholePlaneGFF)

namespace SupercriticalLFPPAS.Field

/-- For every normalized whole-plane GFF, the heat-kernel mollifications have a family of
continuous spatial versions, each satisfying the frozen heat-smoothing property, and the family
is almost surely jointly continuous in positive scale and space.

This is the core existence statement from which the frozen anchor `exists_jointHeatVersion` is
obtained by direct specialization.  The proof reuses DFGPS's proved `lem2_1HeatJoint` result. -/
theorem exists_jointHeatVersion_core {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∃ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
      (∀ ε, IsHeatSmoothing P h ε (X ε)) ∧
        ∀ᵐ ω ∂P, Continuous fun p : Set.Ioi (0 : ℝ) × ℂ => X p.1 ω p.2 := by
  classical
  let good : Ω → Prop := fun ω =>
    (∀ ε : ℝ, 0 < ε → ∀ z : ℂ,
      ∃ L : ℝ, Tendsto (fun n : ℕ => h ω (heatTrunc (ε ^ 2 / 2) z n)) atTop (𝓝 L)) ∧
    ContinuousOn (fun p : ℝ × ℂ => heatMollify p.1 (h ω) p.2) (Ioi 0 ×ˢ univ)
  let X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ) := fun ε ω =>
    if hω : good ω then
      ⟨fun z => heatMollify (ε : ℝ) (h ω) z, by
        rw [continuous_iff_continuousAt]
        intro z
        have hF : ContinuousAt (fun p : ℝ × ℂ => heatMollify p.1 (h ω) p.2)
            ((ε : ℝ), z) :=
          hω.2.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds
            (by simp [ε.2] : ((ε : ℝ), z) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)))
        exact hF.comp (continuousAt_const.prodMk continuous_id.continuousAt)⟩
    else 0
  have hJ := LQGMetric.DFGPS.lem2_1HeatJoint P h hh.1
  refine ⟨X, ?_, ?_⟩
  · intro ε z
    filter_upwards [hJ] with ω hω
    have hgood : good ω := hω
    obtain ⟨L, hL⟩ := hω.1 (ε : ℝ) ε.2 z
    have hX : (X ε ω) z = L := by
      rw [show (X ε ω) z = heatMollify (ε : ℝ) (h ω) z by simp [X, hgood]]
      change Filter.limUnder atTop
          (fun n : ℕ => h ω (heatTrunc ((ε : ℝ) ^ 2 / 2) z n)) = L
      exact hL.limUnder_eq
    rw [hX]
    exact hL
  · filter_upwards [hJ] with ω hω
    have hgood : good ω := hω
    change Continuous fun p : Set.Ioi (0 : ℝ) × ℂ => X p.1 ω p.2
    rw [continuous_iff_continuousAt]
    intro p
    have hF : ContinuousAt (fun q : ℝ × ℂ => heatMollify q.1 (h ω) q.2)
        ((p.1 : ℝ), p.2) :=
      hω.2.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (by simp [p.1.2] : ((p.1 : ℝ), p.2) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)))
    have hcomp : ContinuousAt
        (fun q : Set.Ioi (0 : ℝ) × ℂ => heatMollify (q.1 : ℝ) (h ω) q.2) p :=
      hF.comp₂ (continuous_subtype_val.comp continuous_fst).continuousAt
        continuous_snd.continuousAt
    have hXeq : (fun q : Set.Ioi (0 : ℝ) × ℂ => X q.1 ω q.2) =
        fun q => heatMollify (q.1 : ℝ) (h ω) q.2 := by
      funext q
      simp [X, hgood]
    rw [hXeq]
    exact hcomp

end SupercriticalLFPPAS.Field
