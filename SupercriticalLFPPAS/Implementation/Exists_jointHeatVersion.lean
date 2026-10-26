import SupercriticalLQGUniqueness.Frozen.IsNormalizedWholePlaneGFF
import SupercriticalLQGUniqueness.Frozen.IsHeatSmoothing
import LQGMetric.Papers.DFGPS.L2_1PolarJoint

/-!
# Provider of the frozen anchor `exists_jointHeatVersion`

`exists_jointHeatVersion_impl` restates the exact type of `SupercriticalLFPPAS.exists_jointHeatVersion`
(`SupercriticalLFPPAS/Frozen/Exists_jointHeatVersion.lean`; ruling P7, S1 §5.1) and proves it from the proved
`LQGMetric.DFGPS.lem2_1HeatJoint`: for a whole-plane GFF, almost surely the truncated heat pairings converge at every
`(ε, z)` and `(ε, z) ↦ heatMollify ε (h ω) z` is continuous on `(0, ∞) × ℂ`. The family is
`X ε ω = heatMollify ε (h ω)` when this function is continuous, and `0` otherwise (only on a null set).

`exists_jointHeatVersion_pathwise` is the stronger pathwise form (S1 §5.3): on one probability-one event the
realization-wise convolution `h ∗ p_{ε²/2}` exists at every `(ε, z)` and equals `X ε ω z`, and the family is jointly
continuous. The proofs are those of the S1 evidence (`planning/audits/S1-statement-audit.md`, Details for later use).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open LQGMetric (DistC)

namespace SupercriticalLFPPAS.Implementation

open SupercriticalLQGUniqueness (IsNormalizedWholePlaneGFF IsHeatSmoothing)

/-- **Jointly continuous heat versions, pathwise.** For a whole-plane GFF `h` there is a family `X ε` of continuous
functions such that, on one probability-one event, the truncated pairings `⟨h ω, p_{ε²/2}(z - ·) χ_n⟩` converge to
`X ε ω z` at every `ε > 0` and `z`, and `(ε, z) ↦ X ε ω z` is jointly continuous on `(0, ∞) × ℂ`. -/
theorem exists_jointHeatVersion_pathwise {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (hh : LQGMetric.IsWholePlaneGFF h P) :
    ∃ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
      (∀ᵐ ω ∂P, ∀ ε : Set.Ioi (0 : ℝ), ∀ z : ℂ,
        Tendsto (fun n : ℕ => h ω (SupercriticalLQGUniqueness.positiveHeatTrunc
          ⟨(ε : ℝ) ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos ε.2 2) two_pos)⟩ z n)) atTop
          (𝓝 (X ε ω z))) ∧
      ∀ᵐ ω ∂P, Continuous fun p : Set.Ioi (0 : ℝ) × ℂ => X p.1 ω p.2 := by
  classical
  have hJ := LQGMetric.DFGPS.lem2_1HeatJoint P h hh
  have hsec : ∀ ω, ContinuousOn (fun q : ℝ × ℂ => LQGMetric.heatMollify q.1 (h ω) q.2)
      (Ioi 0 ×ˢ univ) → ∀ ε : Set.Ioi (0 : ℝ), Continuous (LQGMetric.heatMollify (ε : ℝ) (h ω)) :=
    fun ω hω ε => by
      have := hω.comp_continuous (continuous_const.prodMk continuous_id)
        fun z => (⟨ε.2, mem_univ z⟩ : ((ε : ℝ), z) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ))
      simpa only [Function.comp_def, id_eq] using this
  let X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ) := fun ε ω =>
    if hc : Continuous (LQGMetric.heatMollify (ε : ℝ) (h ω)) then ⟨_, hc⟩ else 0
  have hXv : ∀ ω (ε : Set.Ioi (0 : ℝ)), Continuous (LQGMetric.heatMollify (ε : ℝ) (h ω)) →
      ∀ z, X ε ω z = LQGMetric.heatMollify (ε : ℝ) (h ω) z := by
    intro ω ε hc z
    simp only [X, hc, dite_true, ContinuousMap.coe_mk]
  refine ⟨X, ?_, ?_⟩
  · filter_upwards [hJ] with ω hω ε z
    obtain ⟨L, hL⟩ := hω.1 ε ε.2 z
    rw [hXv ω ε (hsec ω hω.2 ε) z]
    have e : LQGMetric.heatMollify (ε : ℝ) (h ω) z = L := hL.limUnder_eq
    rw [e]
    unfold SupercriticalLQGUniqueness.positiveHeatTrunc
    exact hL
  · filter_upwards [hJ] with ω hω
    have heq : (fun p : Set.Ioi (0 : ℝ) × ℂ => X p.1 ω p.2) =
        (fun q : ℝ × ℂ => LQGMetric.heatMollify q.1 (h ω) q.2) ∘
          (fun p : Set.Ioi (0 : ℝ) × ℂ => ((p.1 : ℝ), p.2)) := by
      funext p
      exact hXv ω p.1 (hsec ω hω.2 p.1) p.2
    rw [heq]
    exact hω.2.comp_continuous (by fun_prop) fun p => ⟨p.1.2, mem_univ _⟩

/-- Provider of `SupercriticalLFPPAS.exists_jointHeatVersion` (exact frozen type, S1 §5.1). -/
theorem exists_jointHeatVersion_impl :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P →
        ∃ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) ∧
          ∀ᵐ ω ∂P, Continuous fun p : Set.Ioi (0 : ℝ) × ℂ => X p.1 ω p.2 := by
  intro Ω _ P _ h hh
  obtain ⟨X, hX, hXc⟩ := exists_jointHeatVersion_pathwise P h hh.1
  exact ⟨X, fun ε z => by filter_upwards [hX] with ω hω using hω ε z, hXc⟩

end SupercriticalLFPPAS.Implementation
