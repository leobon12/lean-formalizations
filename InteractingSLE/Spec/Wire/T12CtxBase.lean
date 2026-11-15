/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12AsmInputs
import InteractingSLE.Spec.Sec5.ChartRawMembers
import InteractingSLE.Spec.Sec7.RefFrameExists
import InteractingSLE.Spec.Sec5.TwoAngWire

/-! # The physical boundary word and counterflow for Theorems 1.2–1.3

The boundary word is exactly Aux. 130's prescribed reference word. Its field
and counterflow exist on a standard Borel probability space by Theorem 1.1.
The two-angle experiments use only the acyclic Cond44 determination theorem.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Ctx

open Current Sec7 Sec7.StripMarks Sec7.StripSysField

/-- Cond44 determination from the proved directional C laws (R74). -/
theorem cond44 : AdmCode.Theorem12ParamCond44Statement.{0} :=
  T12Asm.cond44 (fun κ _ _ => ZhanGT4.A1G3L2.g3RectLawSndC_holds κ)
    (fun κ _ _ => ZhanGT4.A1G3Lg.g3RectLawFstC_holds κ)
    (fun κ _ => ZhanGT4.A1ESRec.eightRectLawSndC κ)

/-- The exact boundary word of the fixed Figure 5.1 reference frame. -/
def boundary (i : BothLow) : ℝ → ℝ := (aux130RefFrame i).word (16 / i.kappa)

/-- Aux. 130's three exceptional boundary points. -/
def jumps : Finset ℝ := {-1, 0, 1}

/-- The boundary-data binder. -/
theorem boundary_piecewise (i : BothLow) : IsPiecewiseConstantBoundaryData (boundary i) jumps :=
  aux130Frame_isPiecewiseConstantBoundaryData (Sec5.TwoAngle.sixteen_div_kappa_pos i)

/-- Both boundary-bound binders, at every permitted angle. -/
theorem boundary_heights (i : BothLow) :
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      boundary i y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa)) ∧
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps →
      sleLambda (16 / i.kappa) ≤ boundary i y + a * chiC (16 / i.kappa)) := by
  have hp := Sec5.TwoAngle.sixteen_div_kappa_pos i
  have h4 := Sec5.TwoAngle.sixteen_div_kappa_lt_four i
  exact ⟨aux130Frame_word_left hp h4 (by simp only [jumps, Finset.mem_insert_self]),
    aux130Frame_word_right hp h4 (by simp only [jumps, Finset.mem_insert, Finset.mem_singleton,
      or_true])⟩

/-- The harmonic extension required to center the original field. -/
theorem exists_originalMean (i : BothLow) :
    ∃ u : ℂ → ℝ, IsBoundedHarmonicExtension (boundary i) jumps u := by
  obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension (boundary_piecewise i)
  exact ⟨u, hu⟩

/-- The actual two final angles are strictly inside the permitted interval. -/
theorem angles (i : BothLow) :
    rs136Theta1 (16 / i.kappa) i.leftWeight ∈ Ioo (-(π / 2)) (π / 2) ∧
    rs136Theta2 (16 / i.kappa) i.rightWeight ∈ Ioc (-(π / 2)) (π / 2) := by
  have he : counterflowA (16 / i.kappa) - 2 = i.kappa / 2 - 4 := by
    unfold counterflowA
    have hd : 16 / (16 / i.kappa) = i.kappa := by field_simp
    rw [hd]
    ring
  obtain ⟨hL, hR⟩ := rs136_mem_Ioo (Sec5.TwoAngle.sixteen_div_kappa_pos i)
    (Sec5.TwoAngle.sixteen_div_kappa_lt_four i)
    (show i.leftWeight ∈ Ioo (-2) (counterflowA (16 / i.kappa) - 2) from
      ⟨i.left_gt, he ▸ i.left_lt⟩)
    (show i.rightWeight ∈ Ioo (-2) (counterflowA (16 / i.kappa) - 2) from
      ⟨i.right_gt, he ▸ i.right_lt⟩)
  exact ⟨hL, Ioo_subset_Ioc_self hR⟩

/-- The exact Figure 5.1 counterflow-word equality of the top-level assembly. -/
theorem reference_word (i : BothLow) :
    ∀ y ∉ counterflowJumps jumps ∪ Sec5.Prop513Field.jumps
      (Real.exp (π * (aux130RefFrame i).x₀)) (Sec4.stripHJumps {0} {(aux130RefFrame i).x₀}),
      counterflowData (16 / i.kappa) (boundary i) y =
        Sec4.stripCounterflowData (16 / i.kappa) 0 (Real.exp (π * (aux130RefFrame i).x₀))
          (Sec5.fig51Lower (aux130RefFrame i).a (aux130RefFrame i).b)
          (Sec5.fig51Upper (aux130RefFrame i).x₀ (aux130RefFrame i).a' (aux130RefFrame i).b') y :=
  (aux130RefFrame i).refWord_of_boundary_eq _ _ rfl

/-- The space, GFF, counterflow and infinite-lifetime binder group, with no input. -/
theorem exists_counterflow (i : BothLow) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω)
      (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsGFFWithBoundaryData P h (boundary i) jumps ∧
      IsCenteredCounterflowDriver (16 / i.kappa) P h W ζ ∧
      ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  have hp := Sec5.TwoAngle.sixteen_div_kappa_pos i
  obtain ⟨Ω, mΩ, hSB, P, hP, h, W, ζ, hh, hcf, hζ⟩ :=
    StripSysBorel.exists_isCenteredCounterflowDriver_standardBorel.{0} hp (boundary_piecewise i)
  exact ⟨Ω, mΩ, hSB, P, hP, h, W, ζ, hh, hcf,
    hζ (isNonhitCounterflowWord_aux130Frame hp (Sec5.TwoAngle.sixteen_div_kappa_lt_four i))⟩

end InteractingSLE.Wire.T12Ctx
