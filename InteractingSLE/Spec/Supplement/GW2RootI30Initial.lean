/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootI30Capacity
import InteractingSLE.Spec.Supplement.GW2RootI30Single
import InteractingSLE.Spec.Supplement.GW2RootH29Initial

/-!
# The initial literal root capacity at every low-arc root

Packet PROVE-T14-GW2ROOT2. The actual first canonical trace identifies
the physical carrier. Root admissibility follows from COVER's seed
condition. Its literal normalized capacity is the translated Borel
clock reader, with no zero-root restriction.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Complex MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootI30

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24
open Supp8.GB6 Supp8.GB6.CoordB

variable {Ω : Type u} [MeasurableSpace Ω]

/-- COVER's seed condition implies the literal initial schedule is admissible. -/
theorem schedAdm_nil_of_seedOK (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (hseed : RootCv.RootSeedOK c r.1) :
    SchedAdm c.b c.jumps c.Θ c.Q (κ := c.κ) (rootPt r.1) (rootEntry r.1) [] := by
  refine ⟨?_, ?_⟩
  · rcases hseed.2 with hzero | ⟨hx, hno, hlow⟩
    · exact Or.inl (by simp only [rootPt, hzero])
    · right
      have hlow' : PiecewiseConstantBoundaryData.rightLim c.b 0 -
          Real.pi / 2 * QuantumZipper.chiC c.κ ≤
          -sleLambda c.κ := by simpa only [neg_mul, sub_eq_add_neg] using hlow
      rw [lowerArcRoots, ite_eq_left hlow']
      refine ⟨?_, hx, ?_⟩
      · cases hq : r.1.1 with
        | none => exact (ne_of_gt hx (by simp only [rootPt, hq])).elim
        | some q => exact ⟨q, by simp only [rootPt, hq]⟩
      · intro y hy hy0 hyx
        exact False.elim (hno y (Finset.mem_filter.mp hy).1 ⟨hy0, hyx⟩)
  · rw [schedOf_nil]
    refine ⟨?_, by simp⟩
    intro p hp
    obtain rfl := List.mem_singleton.mp hp
    exact ⟨r.1.2.1.property, r.1.2.2.property⟩

/-- Literal initial capacity equals the scaled actual Borel clock at
any protected low-arc root, from the original canonical trace. -/
theorem capR_nil_eq_reader (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (ω : Ω)
    (hseed : RootCv.RootSeedOK c r.1)
    (hα : IsGeneratingTrace (c.W · ω) ⊤ (c.α ω))
    (hW : Continuous (c.W · ω)) (hW0 : c.W 0 ω = 0) (hζ : c.ζ ω = ⊤)
    (hs : 0 < c.s) :
    let E := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 []) 0 ω
    ∀ {γ : ℝ≥0 → ℂ}, IsGeneratingTrace E.1 E.2 γ →
      (∀ u ∈ Icc 0 c.s, rootPt r.1 * ‖c.α ω u‖ < 1) →
      ((rootEntry r.1).2 : ℝ≥0∞) < min
        (firstContactTime (fun t => sphereInv (((rootPt r.1 : ℂ) + γ t : ℂ) : OnePoint ℂ))
          ((fun u => (c.α ω u : OnePoint ℂ)) '' Icc 0 c.s)) E.2 →
      capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ω =
        4 ^ r.2 * RootH29.forwardCapacity (rootPt r.1) c.s (rootEntry r.1).2
          (RootCv.rootRecs c r.1 ω) := by
  intro E γ hγ harc hv
  let x := rootPt r.1
  let θ := (rootEntry r.1).1
  let v := (rootEntry r.1).2
  let p := (cfRec c.s c.W c.ζ ω, recOf (v : ℝ≥0∞) E)
  let U := rdrv p.1
  let U₀ := Ito.rpath (c.W · ω)
  have he : IsRegularDriver E := isRegularDriver_canonDrive
    c.hκ c.h12p c.βA c.c₀ x _ _ (c.h ω) 0
  have hrec := GaugeE.record_prefix_eq c.s hW0 hW.continuousOn
    (show (c.s : ℝ≥0∞) < c.ζ ω by rw [hζ]; exact ENNReal.coe_lt_top)
  have hUK : fwdHull U c.s = fwdHull U₀ c.s :=
    GaugeE.record_hull_eq c.s hW0 hW.continuousOn
      (by rw [hζ]; exact ENNReal.coe_lt_top)
  have hmap : relMap U c.s = relMap U₀ c.s := relMap_eq_of_eqOn c.s.coe_nonneg hrec
  have hdom : relDomain U c.s = relDomain U₀ c.s := by
    unfold relDomain Supp8.Q3Rel.invHull
    rw [hUK]
  have hset := prefixSet_single_of_live c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h
    x θ v ω hγ (lt_min_iff.mp hv).2
  have hreg : (fun q : ℝ => regW c.s c.W c.ζ q.toNNReal ω) = U₀ := by
    funext q
    exact regW_eq c.s hζ hW0 hW q.toNNReal
  have hsafe : MapsTo (fun q => (x : ℂ) + γ q) (Icc 0 v) (relSafe U c.s) :=
    fun q hq => RootH29.trace_mem_record_relSafe c.W c.ζ ω hα hW hW0 hζ
      (RootH29.rootPt_nonneg_of_seedOK c hseed) harc he hγ hv hq.2
  have hinter : (fun q => γ q + (x : ℂ)) '' Icc 0 v ∩ relDomain U c.s =
      (fun q => (x : ℂ) + γ q) '' Icc 0 v ∩ H := by
    have hcomm : (fun q => γ q + (x : ℂ)) = (fun q => (x : ℂ) + γ q) :=
      funext fun q => add_comm _ _
    rw [hcomm]
    apply Subset.antisymm
    · exact inter_subset_inter_right _ fun _ hz => hz.1
    · rintro z ⟨⟨q, hq, rfl⟩, hzH⟩
      exact ⟨mem_image_of_mem _ hq, hzH, fun hzInv => (hsafe hq).2 (subset_closure hzInv)⟩
  have himage : prefixImage c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h
      (regW c.s c.W c.ζ) c.s x [(θ, v)] ω =
      relMap U c.s '' ((fun q => (x : ℂ) + γ q) '' Icc 0 v ∩ H) := by
    rw [prefixImage, hreg, hset, ← RootY20.relDomain_eq_jointDomain, ← hdom]
    change relMap U₀ c.s '' _ = _
    rw [← hmap, hinter]
  have hcap := capOf_mapped_prefix_eq_reader c.W c.ζ ω hα hW hW0 hζ hs
    (RootH29.rootPt_nonneg_of_seedOK c hseed) harc he hγ hv v ⟨zero_le, le_rfl⟩
  have hp : RootCv.rootRecs c r.1 ω = p :=
    Prod.ext rfl (RootCv.stopRec_root_eq c r.1 ω)
  rw [hp]
  simp only [capR, entryList, List.map_nil, schedCap]
  rw [capV, ite_eq_left (schedAdm_nil_of_seedOK c r hseed), schedOf_nil]
  change 4 ^ r.2 * capOf (prefixImage c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h
    (regW c.s c.W c.ζ) c.s x [(θ, v)] ω) = _
  rw [himage, hcap]

end InteractingSLE.Theorem14.GW2TipSystem.RootI30
