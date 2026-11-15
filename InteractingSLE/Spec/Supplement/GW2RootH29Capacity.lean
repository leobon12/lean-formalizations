/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootH29Switch
import InteractingSLE.Spec.Supplement.GW2RootY20Actual

/-!
# Actual switched capacities and Borel readers at low-arc roots

Packet PROVE-T14-GW2ROOT2. The new boundary-root carrier discharges
the geometry needed by the landed capacity monotonicity and dense-code
readers. No measurable choice of a joined physical path is made.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootH29

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24 Supp8.GB6

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The running capacity is the actual final image capacity at every
nonnegative root, before contact with an untouched root connector. -/
theorem ae_schedCap_eq_capOf_before_contact (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (x : ℝ) (hx : 0 ≤ x)
    (e₀ : ℝ × ℝ≥0) (xs : List (ℝ × ℝ≥0)) :
    ∀ᵐ ω ∂c.P, (∀ u ∈ Icc 0 c.s, x * ‖c.α ω u‖ < 1) →
      SchedAdm c.b c.jumps c.Θ c.Q (κ := c.κ) x e₀ xs →
      Disjoint (c.α ω '' Icc 0 c.s) ((fun z : ℂ => -z⁻¹) ''
        (prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x (schedOf e₀ xs) ω \ {0})) →
      schedCap c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h (regW c.s c.W c.ζ)
        c.s c.Θ c.Q x e₀ xs ω = capOf (prefixImage c.hκ c.h12p c.βA c.b
          c.jumps c.c₀ c.h (regW c.s c.W c.ζ) c.s x (schedOf e₀ xs) ω) := by
  induction xs with
  | nil =>
    exact Eventually.of_forall fun ω _ hadm _ => by
      simp only [schedCap, capV, ite_eq_left hadm]
  | cons y xs ih =>
    filter_upwards [ih, ae_prefixImage_geometry h13 c x hx (schedOf e₀ xs),
      ae_prefixImage_geometry h13 c x hx (schedOf e₀ (y :: xs))]
      with ω hprev hbefore hafter harc hadm hsep
    have hsub : prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x (schedOf e₀ xs) ω ⊆
        prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x (schedOf e₀ (y :: xs)) ω := by
      rw [schedOf_cons]
      exact RootC11.prefixSet_subset_append c.hκ c.h12p c.βA c.b c.jumps c.c₀
        c.h x (schedOf e₀ xs) y ω
    have hsep' := hsep.mono_right (image_mono (sdiff_subset_sdiff_left hsub))
    obtain ⟨hb₀, ha₀, _⟩ := hbefore harc hsep'
    obtain ⟨hb₁, ha₁, _⟩ := hafter harc hsep
    rw [schedCap, hprev harc (SchedAdm.of_cons c.b c.jumps c.Θ c.Q hadm) hsep',
      capV, ite_eq_left hadm]
    apply max_eq_right
    apply RootC11.capOf_mono _ hb₀ ha₀ hb₁ ha₁
    rw [schedOf_cons]
    exact RootC11.prefixImage_subset_append c.hκ c.h12p c.βA c.b c.jumps c.c₀
      c.h (regW c.s c.W c.ζ) c.s x (schedOf e₀ xs) y ω

/-- A globally Borel reader of the literal switched image capacity,
valid on all protected nonnegative-root histories. -/
theorem exists_measurable_prefix_capacity_before_contact (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (x : ℝ) (hx : 0 ≤ x) (l : List (ℝ × ℝ≥0)) :
    ∃ C : Ω → ℝ, Measurable C ∧ (∀ ω, 0 ≤ C ω) ∧
      ∀ᵐ ω ∂c.P, (∀ u ∈ Icc 0 c.s, x * ‖c.α ω u‖ < 1) →
        Disjoint (c.α ω '' Icc 0 c.s) ((fun z : ℂ => -z⁻¹) ''
          (prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x l ω \ {0})) →
        C ω = capOf (prefixImage c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h
          (regW c.s c.W c.ζ) c.s x l ω) := by
  let spec := schedSpec x l
  have hS := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh
    (spec := spec) rfl (isFlowProg_spec x true l) (specDelta_ne_top _)
  have hR := stagedPiecesRegular_of_regular h13 c.hκ c.hb hS
    (fun k ω => isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x
      (specAngle spec) (specDelta spec) (c.h ω) k)
  have hCm : ∀ j, Measurable (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec j) := fun j =>
    measurable_canonFam c.hκ c.h12p c.βA c.c₀ (specAngle spec) (specDelta spec)
      x c.hβA.1 c.hh.1 j
  obtain ⟨F, hFm, hF⟩ := SB.Side.exists_measurable_physSet_dense_code c.hb spec hCm hR
  refine ⟨fun ω => RootY20.codeCapacity c.s (cfRec c.s c.W c.ζ ω) (F ω),
    RootY20.measurable_codeCapacity c.s (measurable_cfRec c.hcf c.s) hFm,
    (fun ω => div_nonneg ENNReal.toReal_nonneg (by norm_num)), ?_⟩
  filter_upwards [hF, ae_exists_relative_prefix h13 c x hx l,
    GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ]
    with ω hFω hgeom hreg hζ harc hsep
  obtain ⟨Γ, hc, h0, himage⟩ := hgeom harc hsep
  obtain ⟨_, _, hW, hW0, _⟩ := hreg
  obtain ⟨hmap, hdom⟩ := RootY20.record_chart_eq_regW c.W c.ζ c.s ω hW hW0 hζ
  have himage' : relMap (rdrv (cfRec c.s c.W c.ζ ω)) c.s ''
      (prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x l ω ∩
        CoordB.relDomain (rdrv (cfRec c.s c.W c.ζ ω)) c.s) = Γ '' Icc 0 1 ∩ H := by
    rw [hmap, hdom]
    exact himage
  have he := RootY20.codeCapacity_eq_capOf c.s (cfRec c.s c.W c.ζ ω) (F ω)
    hFω.symm hc h0.le himage'
  rw [he, hmap, hdom]
  rfl

/-- Every switched low-arc root capacity has a nonnegative Borel
reader; its almost-sure identity uses only the source trace geometry. -/
theorem exists_measurable_capR_before_contact (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (hx : 0 ≤ rootPt r.1)
    (l : List (EntryIdx c.Θ c.Q)) :
    ∃ C : Ω → ℝ, Measurable C ∧ (∀ ω, 0 ≤ C ω) ∧
      ∀ᵐ ω ∂c.P, (∀ u ∈ Icc 0 c.s, rootPt r.1 * ‖c.α ω u‖ < 1) →
        SchedAdm c.b c.jumps c.Θ c.Q (κ := c.κ)
          (rootPt r.1) (rootEntry r.1) (entryList l) →
        Disjoint (c.α ω '' Icc 0 c.s) ((fun z : ℂ => -z⁻¹) ''
          (prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h (rootPt r.1)
            (schedOf (rootEntry r.1) (entryList l)) ω \ {0})) →
        C ω = capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ω := by
  obtain ⟨C, hCm, hC0, hC⟩ := exists_measurable_prefix_capacity_before_contact h13 c
    (rootPt r.1) hx (schedOf (rootEntry r.1) (entryList l))
  refine ⟨fun ω => 4 ^ r.2 * C ω, measurable_const.mul hCm,
    (fun ω => mul_nonneg (by positivity) (hC0 ω)), ?_⟩
  filter_upwards [hC, ae_schedCap_eq_capOf_before_contact h13 c (rootPt r.1)
    hx (rootEntry r.1) (entryList l)] with ω hCω hcap harc hadm hsep
  change _ = 4 ^ r.2 * schedCap c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h
    (regW c.s c.W c.ζ) c.s c.Θ c.Q (rootPt r.1) (rootEntry r.1) (entryList l) ω
  rw [hCω harc hsep, hcap harc hadm hsep]

end InteractingSLE.Theorem14.GW2TipSystem.RootH29
