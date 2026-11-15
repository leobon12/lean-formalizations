/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootR18Image

/-!
# The actual switched root capacity before trace contact

Packet PROVE-T14-GW2ROOT2. The previous attachment-history assumption is
discharged for every finite canonical schedule from zero. All earlier
prefixes also avoid trace contact by canonical prefix consistency; their
capacity geometry follows from the source data. Thus the running maximum
is the capacity of the actual last image, including killed endings.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootR18

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
  (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (h : Ω → DistOn upperHalfPlaneOpens)
  (h13 : Theorem13Statement.{u}) (hβA : IsStopLaw.{u} κ βA)
  (hb : IsPiecewiseConstantBoundaryData b jumps)
  (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
  (hh : IsGFFWithBoundaryData P h b jumps)
  (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
  (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
  (α : Ω → ℝ≥0 → ℂ) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (α ω))
  (s : ℝ≥0) (Θ : Set ℝ) (Q : Set ℝ≥0)

include h13 hβA hb hc₀J hc₀ hh hcf hζ hα

/-- For the actual switched canonical history from zero, its last image
determines the running capacity before original trace contact. -/
theorem ae_schedCap_eq_capOf_before_contact (e₀ : ℝ × ℝ≥0) (xs : List (ℝ × ℝ≥0)) :
    ∀ᵐ ω ∂P, SchedAdm b jumps Θ Q (κ := κ) 0 e₀ xs →
      Disjoint (α ω '' Icc 0 s)
        ((fun z : ℂ => -z⁻¹) ''
          (prefixSet hκ h12p βA b jumps c₀ h 0 (schedOf e₀ xs) ω \ {0})) →
      schedCap hκ h12p βA b jumps c₀ h (regW s W' ζ') s Θ Q 0 e₀ xs ω =
        capOf (prefixImage hκ h12p βA b jumps c₀ h (regW s W' ζ') s 0 (schedOf e₀ xs) ω) := by
  induction xs with
  | nil =>
    exact Eventually.of_forall fun ω hadm _ => by
      simp only [schedCap, capV, ite_eq_left hadm]
  | cons y xs ih =>
    filter_upwards [ih,
      ae_prefixImage_geometry hκ h12p βA b jumps c₀ P h
        h13 hβA hb hc₀J hc₀ hh W' ζ' hcf hζ α hα s (schedOf e₀ xs),
      ae_prefixImage_geometry hκ h12p βA b jumps c₀ P h
        h13 hβA hb hc₀J hc₀ hh W' ζ' hcf hζ α hα s (schedOf e₀ (y :: xs))]
      with ω hprev hbefore hafter hadm hsep
    have hsub : prefixSet hκ h12p βA b jumps c₀ h 0 (schedOf e₀ xs) ω ⊆
        prefixSet hκ h12p βA b jumps c₀ h 0 (schedOf e₀ (y :: xs)) ω := by
      rw [schedOf_cons]
      exact RootC11.prefixSet_subset_append hκ h12p βA b jumps c₀ h 0 (schedOf e₀ xs) y ω
    have hsep' := hsep.mono_right (image_mono (sdiff_subset_sdiff_left hsub))
    obtain ⟨hb₀, ha₀, _⟩ := hbefore hsep'
    obtain ⟨hb₁, ha₁, _⟩ := hafter hsep
    rw [schedCap, hprev (SchedAdm.of_cons b jumps Θ Q hadm) hsep',
      capV, ite_eq_left hadm]
    apply max_eq_right
    apply RootC11.capOf_mono _ hb₀ ha₀ hb₁ ha₁
    rw [schedOf_cons]
    exact RootC11.prefixImage_subset_append hκ h12p βA b jumps c₀ h
      (regW s W' ζ') s 0 (schedOf e₀ xs) y ω

/-- The repaired scaled capacity of every switched zero-root history is
the scaled capacity of its actual image. No attachment or carrier inputs. -/
theorem ae_capR_eq_scaled_capOf_before_contact (r : ScaledRootIdx Θ Q)
    (hroot : rootPt r.1 = 0) (l : List (EntryIdx Θ Q)) :
    ∀ᵐ ω ∂P,
      SchedAdm b jumps Θ Q (κ := κ) (rootPt r.1) (rootEntry r.1) (entryList l) →
      Disjoint (α ω '' Icc 0 s)
        ((fun z : ℂ => -z⁻¹) ''
          (prefixSet hκ h12p βA b jumps c₀ h (rootPt r.1)
            (schedOf (rootEntry r.1) (entryList l)) ω \ {0})) →
      capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω =
        4 ^ r.2 * capOf (RootC11.rootImage hκ h12p βA b jumps c₀ h W' s Θ Q ζ' r l ω) := by
  filter_upwards [ae_schedCap_eq_capOf_before_contact hκ h12p βA b jumps c₀ P h
    h13 hβA hb hc₀J hc₀ hh W' ζ' hcf hζ α hα s Θ Q (rootEntry r.1) (entryList l)]
    with ω hω hadm hsep
  change 4 ^ r.2 * schedCap hκ h12p βA b jumps c₀ h (regW s W' ζ') s Θ Q
      (rootPt r.1) (rootEntry r.1) (entryList l) ω = _
  change _ = 4 ^ r.2 * capOf (prefixImage hκ h12p βA b jumps c₀ h
    (regW s W' ζ') s (rootPt r.1) (schedOf (rootEntry r.1) (entryList l)) ω)
  rw [hroot] at hadm hsep ⊢
  exact congrArg (fun c : ℝ => 4 ^ r.2 * c) (hω hadm hsep)

end InteractingSLE.Theorem14.GW2TipSystem.RootR18
