/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzSched
import InteractingSLE.Spec.Supplement.GW2SdiInst


/-!
# GW2 at a root `x`: the corrected schedule instance (`ℍ` off the history's success)

Packet PROVE-GW2-ROOTX, round 4. SDE's `GW2SdiInst` correction (RELDET round 17: off `oldSuccess` the explored
driver is the zero driver, whose deterministic slit is not marked local) at the root point `rootPt r.1`:

* `schedUnionSX`: the root-`x` physical union `GW2Rz.schedPhysUnionX` on the history's success, `ℍ` off it;
* **`schedInstSX`**: `GW2Rz.schedInstX` on successful records (`SchedChoice.succ`) with the corrected union;
* **`schedInstSX_good`**: `StageInst.GoodX` from a root-`x` good set, an announced root-`x` version with finite stops,
  the word map's properties, a measurable record event, `u₀` and the owners' open inputs `GW2Rz.OpenLinesX`; the
  shape is the physical union's on the live event (`GW2Rz.shape_of_unionX`), whose records are successful.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Rv

open GW2KM2 Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId Supp8.RelSafe
  GW2Rd GW2Sde GW2Sdf GW2Sdh GW2Sdi GW2Stl GW2Rz Restart.DomainMarkov Restart.FCDet Sec7.PocketTraversal
  Supp8.RelSafeS GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 LocalSets WholeField

/-! ### The corrected root-`x` instance (`ℍ` off the history's success) -/

section Inst

variable {Ω : Type u} [MeasurableSpace Ω]

open Classical in
/-- **The corrected root-`x` stage union** (SDE's `GW2Sdi.schedUnionS` at a root): the root-`x` physical union on
the history's success, `ℍ` off it. -/
def schedUnionSX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (t : ℝ≥0)
    (ω : Ω) : Set ℂ :=
  if oldSuccess c r l ω then schedPhysUnionX c r l a t ω else H

/-- **The corrected schedule instance at the root point** (SDE's `GW2Sdi.schedInstS` at a root): the root-`x`
instance on successful records with the corrected union. -/
def schedInstSX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (GT : Set Ω)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (ch : SchedChoice Ω) : StageInst Ω :=
  { schedInstX c r l a GT hA (ch.succ c r l) with B := schedUnionSX c r l a }

end Inst

section Good

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **`StageInst.GoodX` for the corrected schedule instance at the root point** (SDE's `GW2Sdi.schedInstS_good` at
the root `rootPt r.1 ≥ 0`): the shape of the corrected union is the physical union's on the live event, whose records
are successful. -/
theorem schedInstSX_good (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1) {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : SchedChoice Ω)
    (hβ : Measurable ch.β ∧ (range fun y => wordType c.κ (ch.β y)).Countable ∧ ∀ y, (ch.β y).IsSorted)
    (hE₀ : MeasurableSet ch.E₀) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (hopen : OpenLinesX (schedInstSX c r l a GT hA ch) c r l (rootPt r.1) (measurable_schedW c r l a)) :
    (schedInstSX c r l a GT hA ch).GoodX c r l (rootPt r.1) := by
  set I := schedInstSX c r l a GT hA ch with hI
  have hWm : ∀ t, Measurable (I.W t) := measurable_schedW c r l a
  have hver : IsRelVersionXR (rootPt r.1) c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V := hA.1
  have hv : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V := hA.1.1
  have hρ := hA.1.2.choose_spec
  have hρs := hA.2.choose_spec
  have hpre : Measurable (stgPreRecX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T I.R) :=
    (measurable_stgPreRecX hGT.1 hs hx (measurable_gb6Rec_src c) hWm
      (measurableSet_goodSetX_physFilt (measurable_gb6Rec_src c) hWm hGT.2.1 hGT.2.2) hver I.T).mono
      ((physFilt (measurable_gb6Rec_src c) hWm c.P).le I.T) le_rfl
  have hE : MeasurableSet I.E :=
    (hE₀.inter (measurableSet_succRec c r l)).inter (measurableSet_aliveRecX _ _ c.s hρ.1)
  have hfin : ∀ᵐ ω ∂c.P, I.srecX c r l (rootPt r.1) ω ∈ I.E →
      stgStartMX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ => ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
  have hEgood := StageInst.E_good_of_recordX I hv hρ.2.1 hρ.2.2 inter_subset_right hfin
  have hHr : Measurable I.Hr :=
    measurable_stgField c.hh.1 (isMeasChart_stgChartX (measurable_gb6Rec_src c) hv.2.1 hv.2.2.1 hpre)
  have hzb := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  obtain ⟨𝒢, M, hrec, hM0, hM, hgff⟩ := hopen.condGFF
  have hshape : ∀ (w : WordType) (t : ℝ≥0), ∀ᵐ ω ∂c.P,
      ω ∈ liveEvRec c.κ w I.β I.E (I.srecX c r l (rootPt r.1)) →
      min (physClockX (rootPt r.1) c.s c.W c.ζ I.W I.GT (I.T + t) ω) (I.V ω) < I.V ω →
      H \ I.B t ω = (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)).2.1 ''
        (H \ fwdHull (Ito.rpath fun u => I.R u ω)
          (min (physClockX (rootPt r.1) c.s c.W c.ζ I.W I.GT (I.T + t) ω) (I.V ω)).toNNReal) := by
    intro w t
    filter_upwards [shape_of_unionX hGT.1 hs hx hv hGT.2.2
      (F := liveEvRec c.κ w I.β I.E (I.srecX c r l (rootPt r.1))) (hEgood.mono fun _ h hm => (h hm.1).1) I.T
      (B := schedPhysUnionX c r l a) (fun _ _ => rfl) t] with ω h hlive hlt
    have hsucc : oldSuccess c r l ω := (augRec_mem_succRec_iff c r l _ ω).1 hlive.1.1.2
    have hB : I.B t ω = schedPhysUnionX c r l a t ω := by
      change schedUnionSX c r l a t ω = schedPhysUnionX c r l a t ω
      unfold schedUnionSX
      exact ite_eq_left hsucc
    rw [hB]
    exact h hlive hlt
  exact
    { s_pos := hs
      x_nonneg := hx
      physGood := hGT.1
      measurable_W := hWm
      measurableSet_GT := hGT.2.1
      GT_ae := hGT.2.2
      version := hv
      measurable_ρ := hρ.1
      isPathRule_ρ := hρ.2.1
      V_eq := hρ.2.2
      measurable_ρs := hρs.1
      isPathRule_ρs := hρs.2.1
      ρs_ne_top := hρs.2.2.1
      ρs_mono := hρs.2.2.2.1
      announce := hρs.2.2.2.2
      prefix_retained := comap_stgPreRecX_le_aeSigma hGT.1 hs hx (measurable_gb6Rec_src c) hWm hGT.2.1 hGT.2.2
        hver I.T ((GW2Rd.measurable_cfRec_sigma c r l).comap_le.trans (LocalSets.le_aeSigma _ _))
        fun t ht => (comap_schedW_le_sigma c r l a ht).trans (LocalSets.le_aeSigma _ _)
      measurable_β := hβ.1
      measurableSet_E := hE
      countable_wordType := hβ.2.1
      isSorted := fun y _ => hβ.2.2 y
      E_good := hEgood
      measurable_Hr := hHr
      lines := fun w => StageInst.linesLocalX_of I hv hpre hβ.1 hE hHr hWm w
        (Eventually.of_forall fun _ _ hc => chartTransport_eq_stgField hc) hu₀.1 hzb hopen.sets_le
        hopen.sets_amb hopen.sets_meas hopen.sets_open hopen.loc (hshape w)
        (hopen.mean w) hopen.noThreshold 𝒢.2 hrec hM0 hM hgff }

end Good

end InteractingSLE.Theorem14.GW2Rv
