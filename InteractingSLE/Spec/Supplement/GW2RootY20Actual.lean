/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootY20Records
import InteractingSLE.Spec.Supplement.SBTail2SidePhys

/-!
# A Borel capacity reader for the actual switched pre-contact prefixes

Packet PROVE-T14-GW2ROOT2. The original staged GFF law supplies a Borel
dense physical code. R18 supplies the relative carrier, and the retained
record supplies its actual chart. Thus the capacity reader is constructed
from the source hypotheses, without assuming any capacity measurability,
relative geometry, or measurable choice of a joined physical path.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootY20

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric Supp8.GB6

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
  (s : ℝ≥0)

include h13 hβA hb hc₀J hc₀ hh hcf hζ hα

/-- The actual switched zero-root image capacity has a globally Borel
reader agreeing almost surely before original trace contact. The reader
is constructed, and no measurability of the contact event is assumed. -/
theorem exists_measurable_prefix_capacity_before_contact (l : List (ℝ × ℝ≥0)) :
    ∃ C : Ω → ℝ, Measurable C ∧ (∀ ω, 0 ≤ C ω) ∧
      ∀ᵐ ω ∂P, Disjoint (α ω '' Icc 0 s)
        ((fun z : ℂ => -z⁻¹) '' (prefixSet hκ h12p βA b jumps c₀ h 0 l ω \ {0})) →
        C ω = capOf (prefixImage hκ h12p βA b jumps c₀ h (regW s W' ζ') s 0 l ω) := by
  let spec := schedSpec 0 l
  have hS := isStagedHistory_canonFam hκ h12p βA c₀
    (specAngle spec) (specDelta spec) h13 hβA hb hc₀J hc₀ hh
    (spec := spec) rfl (isFlowProg_spec 0 true l) (specDelta_ne_top _)
  have hR := stagedPiecesRegular_of_regular h13 hκ hb hS
    (fun k ω => isRegularDriver_canonDrive hκ h12p βA c₀ 0
      (specAngle spec) (specDelta spec) (h ω) k)
  have hCm : ∀ j, Measurable (canonSpecFam hκ h12p βA c₀ h spec j) := fun j =>
    measurable_canonFam hκ h12p βA c₀ (specAngle spec) (specDelta spec) 0 hβA.1 hh.1 j
  obtain ⟨F, hFm, hF⟩ := SB.Side.exists_measurable_physSet_dense_code hb spec hCm hR
  let C : Ω → ℝ := fun ω => codeCapacity s (cfRec s W' ζ' ω) (F ω)
  refine ⟨C, measurable_codeCapacity s (measurable_cfRec hcf s) hFm,
    (fun ω => div_nonneg ENNReal.toReal_nonneg (by norm_num)), ?_⟩
  filter_upwards [hF, RootR18.ae_exists_relative_prefix hκ h12p βA b jumps c₀ P h
    h13 hβA hb hc₀J hc₀ hh W' ζ' hcf hζ α hα s l,
    GW2Later.ae_counterflow_regular h13 hκ hcf hζ, hζ]
    with ω hFω hgeom hreg hζω hsep
  obtain ⟨Γ, hΓc, hΓ0, himage⟩ := hgeom hsep
  obtain ⟨_, _, hW, hW0, _⟩ := hreg
  obtain ⟨hmap, hdom⟩ := record_chart_eq_regW W' ζ' s ω hW hW0 hζω
  have hcode : closure (range (F ω)) = prefixSet hκ h12p βA b jumps c₀ h 0 l ω := hFω.symm
  have himage' : relMap (rdrv (cfRec s W' ζ' ω)) s ''
      (prefixSet hκ h12p βA b jumps c₀ h 0 l ω ∩
        CoordB.relDomain (rdrv (cfRec s W' ζ' ω)) s) = Γ '' Icc 0 1 ∩ H := by
    rw [hmap, hdom]
    exact himage
  have he := codeCapacity_eq_capOf s (cfRec s W' ζ' ω) (F ω) hcode hΓc
    (show (Γ 0).im ≤ 0 by rw [hΓ0]; exact le_rfl) himage'
  change codeCapacity s (cfRec s W' ζ' ω) (F ω) = _
  rw [he, hmap, hdom]
  rfl

/-- The repaired scaled root capacity also has a Borel reader on every
admissible zero-root history before contact. -/
theorem exists_measurable_capR_before_contact {Θ : Set ℝ} {Q : Set ℝ≥0}
    (r : ScaledRootIdx Θ Q) (hroot : rootPt r.1 = 0) (l : List (EntryIdx Θ Q)) :
    ∃ C : Ω → ℝ, Measurable C ∧ (∀ ω, 0 ≤ C ω) ∧
      ∀ᵐ ω ∂P,
        SchedAdm b jumps Θ Q (κ := κ) (rootPt r.1) (rootEntry r.1) (entryList l) →
        Disjoint (α ω '' Icc 0 s)
          ((fun z : ℂ => -z⁻¹) '' (prefixSet hκ h12p βA b jumps c₀ h (rootPt r.1)
            (schedOf (rootEntry r.1) (entryList l)) ω \ {0})) →
        C ω = capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω := by
  obtain ⟨C, hCm, hC0, hC⟩ := exists_measurable_prefix_capacity_before_contact
    hκ h12p βA b jumps c₀ P h h13 hβA hb hc₀J hc₀ hh W' ζ' hcf hζ α hα s
    (schedOf (rootEntry r.1) (entryList l))
  refine ⟨fun ω => 4 ^ r.2 * C ω, measurable_const.mul hCm,
    (fun ω => mul_nonneg (by positivity) (hC0 ω)), ?_⟩
  filter_upwards [hC, RootR18.ae_capR_eq_scaled_capOf_before_contact
    hκ h12p βA b jumps c₀ P h h13 hβA hb hc₀J hc₀ hh W' ζ' hcf hζ α hα s Θ Q r hroot l]
    with ω hCω hcap hadm hsep
  rw [hcap hadm hsep]
  change _ = 4 ^ r.2 * capOf (prefixImage hκ h12p βA b jumps c₀ h
    (regW s W' ζ') s (rootPt r.1) (schedOf (rootEntry r.1) (entryList l)) ω)
  rw [hroot] at hsep ⊢
  rw [hCω hsep]

/-- All histories of a fixed zero root have Borel capacity readers on one
common conull source event. Countability is precisely the source's
countability of the angle and candidate-time sets. -/
theorem exists_measurable_capR_family_before_contact {Θ : Set ℝ} {Q : Set ℝ≥0}
    (hΘc : Θ.Countable) (hQc : Q.Countable)
    (r : ScaledRootIdx Θ Q) (hroot : rootPt r.1 = 0) :
    ∃ C : List (EntryIdx Θ Q) → Ω → ℝ,
      (∀ l, Measurable (C l)) ∧ (∀ l ω, 0 ≤ C l ω) ∧
      ∀ᵐ ω ∂P, ∀ l,
        SchedAdm b jumps Θ Q (κ := κ) (rootPt r.1) (rootEntry r.1) (entryList l) →
        Disjoint (α ω '' Icc 0 s)
          ((fun z : ℂ => -z⁻¹) '' (prefixSet hκ h12p βA b jumps c₀ h (rootPt r.1)
            (schedOf (rootEntry r.1) (entryList l)) ω \ {0})) →
        C l ω = capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω := by
  have : Countable Θ := hΘc.to_subtype
  have : Countable Q := hQc.to_subtype
  choose C hCm hC0 hC using fun l => exists_measurable_capR_before_contact
    hκ h12p βA b jumps c₀ P h h13 hβA hb hc₀J hc₀ hh W' ζ' hcf hζ α hα s r hroot l
  exact ⟨C, hCm, hC0, ae_all_iff.mpr hC⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootY20
