/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxPair
import InteractingSLE.Spec.Supplement.GW2PsmRead0
import InteractingSLE.Spec.Supplement.GW2PsmHarm
import InteractingSLE.Spec.Supplement.GW2TjLoc

/-!
# Instance readings at a root `x ≥ 0`

Packet PROVE-GW2-GEOM2, round 14 (D49). The root-`x` versions of the root-`0` instance readings STAGEMEAN's
`GW2Psm.pair_instS` uses:

* `mul_add_one_ne_zero_of_lt_contactXx`, **`ae_noContact_rootX`**: before the version's cap, no explored point,
  translated by `x`, is the counterflow's point: `α v · (x + γ u) + 1 ≠ 0` (from `GW2Psm.ae_lt_contactX_all`);
* **`ae_shape_rootX`**: the root-`x` union's shape at every stage time below the cap, through the re-centred chart
  `relChartX` (ROOTX's `GW2Psm.ae_compl_union_eq_relChartX_all`, no `baseRead` normalization);
* **`isHistoryAvoidanceLocal_stgFX`**: the root-`x` union is local for the stage filtration, for any bounded
  harmonic extension `u₀` (RELDET's `GW2Rd.exists_schedLinesLocal_setsX`);
* **`harmonicOnNhd_stgMeanRX`**: the root-`x` stage mean is harmonic off the stage hull.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Kx

open Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Schedule GW2Tip Supp8.GB6 Supp8.GB6.ReadD GW2Rz GW2Rd GW2Psm Supp8

/-- **Before the contact, no explored point translated by `x` is the counterflow's point.** -/
theorem mul_add_one_ne_zero_of_lt_contactXx {x : ℝ} {s : ℝ≥0} {γ α : ℝ≥0 → ℂ} {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < firstContactTime (fun u => sphereInv (((x : ℂ) + γ u : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) :
    ∀ v ∈ Icc 0 s, ∀ u ≤ t, α v * ((x : ℂ) + γ u) + 1 ≠ 0 := by
  intro v hv u hu h
  have hlt : (u : ℝ≥0∞) < firstContactTime (fun u => sphereInv (((x : ℂ) + γ u : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) := (ENNReal.coe_le_coe.2 hu).trans_lt ht
  refine notMem_of_lt_firstContactTime hlt ⟨v, hv, ?_⟩
  have hγ0 : (x : ℂ) + γ u ≠ 0 := fun h0 => by rw [h0, mul_zero, zero_add] at h; exact one_ne_zero h
  have he : α v = -((x : ℂ) + γ u)⁻¹ := by
    field_simp
    linear_combination h
  rw [sphereInv_coe_of_ne hγ0]
  show ((α v : ℂ) : OnePoint ℂ) = _
  rw [he]

section Live

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {x₀ : ℝ} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  (hGT : ∀ ω ∈ GT, PhysGoodX x₀ s Wα ζα W γ α ω) (hs₀ : 0 < s) (hx₀ : 0 ≤ x₀)

include hGT hs₀ hx₀ in
/-- **No contact before the version's cap** (root `x ≥ 0`, product form). -/
theorem ae_noContact_rootX (hver : IsRelVersionX x₀ s P Wα ζα W γ α R V) :
    ∀ᵐ ω ∂P, ω ∈ GT → ∀ T : ℝ≥0, min (physClockX x₀ s Wα ζα W GT T ω) (V ω) < V ω →
      ∀ v ∈ Icc 0 s, ∀ u ≤ T, α ω v * ((x₀ : ℂ) + γ ω u) + 1 ≠ 0 := by
  filter_upwards [ae_lt_contactX_all hGT hs₀ hx₀ hver] with ω hω hωG T hlt
  exact mul_add_one_ne_zero_of_lt_contactXx (hω hωG T hlt)

end Live

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **The root-`x` union's shape at every stage time below the cap** (on the history's success). -/
theorem ae_shape_rootX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hx : 0 ≤ rootPt r.1) (hs0 : 0 < c.s) {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hv : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V) :
    ∀ᵐ ω ∂c.P, ω ∈ GT → oldSuccess c r l ω → ∀ u : ℝ≥0,
      min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + u) ω) (V ω) < V ω →
      H \ schedUnionX c r l a (historyTime c r l) u ω = (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)).2.1 ''
        (H \ fwdHull (Ito.rpath fun q => R q ω)
          (capA (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) u ω)) := by
  filter_upwards [ae_compl_union_eq_relChartX_all hGT hs0 hx hv] with ω hω hωG hsucc u hlt
  have h := hω hωG (historyTime c r l + u) hlt
  have e : schedUnionX c r l a (historyTime c r l) u ω = Supp8.Q3Rel.invHull (rdrv (cfRec c.s c.W c.ζ ω)) c.s ∪
      (fun z : ℂ => z + ((rootPt r.1 : ℝ) : ℂ)) ''
        fwdHull (fun q : ℝ => schedW c r l a q.toNNReal ω) ((historyTime c r l + u : ℝ≥0) : ℝ) := by
    simp only [schedUnionX, schedHullX, hsucc, ↓reduceIte, schedHull]
    congr 1
    exact congrArg (fun f : ℂ → ℂ => f '' _) (funext fun z => add_comm _ _)
  rw [e]
  exact h

/-- **The root-`x` union is local for the stage filtration** (any root, any bounded harmonic extension `u₀`). -/
theorem isHistoryAvoidanceLocal_stgFX [StandardBorelSpace Ω] (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hord : Sec5.Prop513Schedule.TimeOrdered 0 (historyProgram c r l))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀) (t : ℝ≥0) :
    IsHistoryAvoidanceLocal (stgF c r l a t) (schedUnionX c r l a (historyTime c r l) t)
      (centredField c.h u₀) c.P := by
  obtain ⟨u₁, ℋ', -, hzb, hstg, -, -, -, hloc'⟩ :=
    exists_schedLinesLocal_setsX c r l a h12 h13 hord (le_refl (historyTime c r l))
  have hS := smoothDist_eq_of_isZeroBoundaryGFF hzb
    (Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀)
  have hu : centredField c.h u₁ = centredField c.h u₀ := by
    funext ω
    simp only [centredField, hS]
  rw [← hu]
  exact fun U G hUH hG hd F hF => hloc' t U G hUH hG hd F (hstg t F hF)

/-- **The root-`x` stage mean is harmonic off the stage hull.** -/
theorem harmonicOnNhd_stgMeanRX (κ x : ℝ) (s : ℝ≥0) (rec : RecData) {R : ℝ≥0 → ℝ} (hR : Continuous R)
    (hR0 : R 0 = 0) (a₀ : ℝ≥0) {Q : ℝ} (hQ : 0 ≤ Q) {U u₀ : ℂ → ℝ} (hU : InnerProductSpace.HarmonicOnNhd U H)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (σa : ℝ) :
    InnerProductSpace.HarmonicOnNhd (stgMeanRX κ x s rec R a₀ Q U u₀ σa)
      ((stgChart (relChartX x s rec) R a₀).2.1 '' (H \ fwdHull (Ito.rpath (stgDrv R a₀)) Q)) := by
  set cs := stgChart (relChartX x s rec) R a₀ with hcsdef
  have hcsD := isDomainChart_stgChart_relChartX x s rec hR hR0 a₀
  have hcs : cs.IsConformal := hcsD.isConformal
  have hlh : InnerProductSpace.HarmonicOnNhd cs.2.2 cs.dom := by
    have h := GW2Rd.harmonicOnNhd_lift_of_isDomainChart hcsD
    exact h
  rintro y ⟨z, hz, rfl⟩
  have hdom : cs.2.1 z ∈ cs.dom := hcs.inv_mem_dom hz.1
  have hSc : Continuous (Ito.rpath (stgDrv R a₀)) := (continuous_stgDrv hR a₀).comp continuous_real_toNNReal
  have hf := hcs.differentiableOn_fwd.analyticAt (cs.dom.isOpen.mem_nhds hdom)
  have hcm := Sec7.SideHeight.harmonicOnNhd_couplingMean (κ := κ) hSc hQ hU z hz
  rw [← hcs.2.2 z hz.1] at hcm
  have hm := QuantumZipper.FieldLawler.fl_harmonicAt_comp hf hcm
  have harg : InnerProductSpace.HarmonicAt (fun x => QuantumZipper.chiC κ * cs.2.2 x) (cs.2.1 z) := by
    have he : (QuantumZipper.chiC κ • cs.2.2) = (fun x => QuantumZipper.chiC κ * cs.2.2 x) := by
      funext x
      rfl
    simpa only [he] using (hlh _ hdom).const_smul (c := QuantumZipper.chiC κ)
  have hu := hu₀ _ (hcs.2.1 hz.1)
  exact ((hm.sub hu).sub (InnerProductSpace.harmonicAt_const σa)).sub harg

end InteractingSLE.Theorem14.GW2Kx
