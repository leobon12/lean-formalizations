/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OwnHistoryPath
import InteractingSLE.Spec.Supplement.GW2RootC11Prefixes

/-!
# Continuous carriers of the actual switched canonical prefixes

Packet PROVE-T14-GW2ROOT2. The canonical staged law and Theorem 1.3 supply
piece regularity. The landed own-history path construction then joins all
the switches; no path representation or attachment premise is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootR18

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
  (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (h : Ω → DistOn upperHalfPlaneOpens)

/-- Every finite canonical schedule from zero has its actual continuous
physical carrier, almost surely, including switches and killed endings. -/
theorem ae_exists_path_prefixSet (h13 : Theorem13Statement.{u})
    (hβA : IsStopLaw.{u} κ βA) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (l : List (ℝ × ℝ≥0)) :
    ∀ᵐ ω ∂P, ∃ p : ℝ → ℂ, ContinuousOn p (Icc 0 1) ∧ p 0 = 0 ∧
      MapsTo p (Icc 0 1) Hbar ∧
      prefixSet hκ h12p βA b jumps c₀ h 0 l ω = p '' Icc 0 1 := by
  have hS := isStagedHistory_canonFam hκ h12p βA c₀
    (specAngle (schedSpec 0 l)) (specDelta (schedSpec 0 l))
    h13 hβA hb hc₀J hc₀ hh (spec := schedSpec 0 l) rfl
    (isFlowProg_spec 0 true l) (specDelta_ne_top _)
  have hR := stagedPiecesRegular_of_regular h13 hκ hb hS
    (fun k ω => isRegularDriver_canonDrive hκ h12p βA c₀ 0
      (specAngle (schedSpec 0 l)) (specDelta (schedSpec 0 l)) (h ω) k)
  filter_upwards [hR.ae_pieceRegular] with ω hω
  obtain ⟨p, hp, hp0, hpH, hset⟩ := OwnHistoryPath.exists_path_prefixPhysSet_schedule
    (κ := κ) (b := b) (jumps := jumps) l
    (fun j => canonSpecFam hκ h12p βA c₀ h (schedSpec 0 l) j ω) hω
    (schedSpec 0 l).2.2.length
  exact ⟨p, hp, hp0, hpH, hset⟩

/-- The same actual carrier on nonnegative time, for the relative-chart
and capacity APIs. The finite parameter interval is always `[0,1]`. -/
theorem ae_exists_nnpath_prefixSet (h13 : Theorem13Statement.{u})
    (hβA : IsStopLaw.{u} κ βA) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (l : List (ℝ × ℝ≥0)) :
    ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, ContinuousOn γ (Icc 0 1) ∧ γ 0 = 0 ∧
      MapsTo γ (Icc 0 1) Hbar ∧
      prefixSet hκ h12p βA b jumps c₀ h 0 l ω = γ '' Icc 0 1 := by
  filter_upwards [ae_exists_path_prefixSet hκ h12p βA b jumps c₀ P h
    h13 hβA hb hc₀J hc₀ hh l] with ω hω
  obtain ⟨p, hp, hp0, hpH, hset⟩ := hω
  have hcoe : MapsTo ((↑) : ℝ≥0 → ℝ) (Icc 0 1) (Icc 0 1) :=
    fun t ht => ⟨t.coe_nonneg, by exact_mod_cast ht.2⟩
  refine ⟨fun t => p t, hp.comp continuous_subtype_val.continuousOn hcoe,
    hp0, fun t ht => hpH (hcoe ht), hset.trans ?_⟩
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t.toNNReal, ⟨zero_le, Real.toNNReal_le_one.2 ht.2⟩, ?_⟩
    change p (t.toNNReal : ℝ) = p t
    rw [Real.coe_toNNReal _ ht.1]
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, hcoe ht, rfl⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootR18
