/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TjKer
import InteractingSLE.Spec.Supplement.WalkLeafLaunch
import InteractingSLE.Spec.Supplement.SBLwChart

/-!
# (T1), geometric half: the explored set of the earlier pieces lies in the union; the launch image of the union

Packet PROVE-GW2-RELDET, ruling R117(b), item (T1).

* **`ae_stageSet_subset_schedUnionS`**: at root `0`, for a time-ordered history, almost surely the explored set of the
  earlier pieces (the first `curIdx` instructions of the future program) lies in the instance's union `B t`. On
  `oldSuccess` it is the physical history, which is the explored trace on `[0, T]` (`Gm.prefixSet_history_eq`), and
  the trace lies in the filled explored hull at `T + t`; off `oldSuccess` the union is `ℍ`.
* `launchUnion_eq`: the launch image of a set is the complement in `ℍ` of the chart pre-image of its complement.
* `measurable_launchUnion`: the launch image is hitting-measurable for any marks recording the set.
* `harmonicOnNhd_lift_of_isDomainChart`: the lift of a domain chart is harmonic on its domain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open LocalSets WholeField Exist Staged StagedLaw GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Sdi Restart.MarkovChart

/-- The lift of a domain chart is harmonic on its domain. -/
theorem harmonicOnNhd_lift_of_isDomainChart {D : Set ℂ} {c : Chart} (hc : IsDomainChart D c) :
    InnerProductSpace.HarmonicOnNhd c.2.2 D := by
  have hD : IsOpen D := IsDomainChart.isOpen hc
  obtain ⟨-, -, L, hL, hlift⟩ := hc
  intro z hz
  have han : AnalyticAt ℂ L z := hL.1.analyticAt (hD.mem_nhds hz)
  rw [InnerProductSpace.harmonicAt_congr_nhds (f₂ := fun w => (L w).im)]
  · exact han.harmonicAt_im
  · filter_upwards [hD.mem_nhds hz] with w hw
    exact hlift hw

/-- The launch image of a set: the complement in `ℍ` of the chart pre-image of its complement. -/
theorem launchUnion_eq {c : Chart} (hc : c.IsConformal) (B : Set ℂ) :
    c.1 '' (B ∩ (c.dom : Set ℂ)) = H \ chartPre c (H \ B) := by
  ext w
  constructor
  · rintro ⟨z, ⟨hzB, hzD⟩, rfl⟩
    refine ⟨hc.fwd_mem hzD, fun hw => hw.2.2 ?_⟩
    rw [hc.inv_fwd hzD]
    exact hzB
  · rintro ⟨hwH, hw⟩
    have hinv : c.2.1 w ∈ (c.dom : Set ℂ) := hc.inv_mem_dom hwH
    have hB : c.2.1 w ∈ B := by
      by_contra hn
      exact hw ⟨hwH, hc.dom_subset hinv, hn⟩
    exact ⟨c.2.1 w, ⟨hB, hinv⟩, hc.2.2 w hwH⟩

theorem disjoint_launch_iff {c : Chart} (hc : c.IsConformal) {B U : Set ℂ} (hUH : U ⊆ H) :
    Disjoint (H \ chartPre c (H \ B)) U ↔ Disjoint B (c.2.1 '' U) := by
  constructor
  · intro h
    refine disjoint_left.2 fun z hzB ⟨w, hwU, hwz⟩ => disjoint_left.1 h ⟨hUH hwU, fun hw => ?_⟩ hwU
    rw [← hwz] at hzB
    exact hw.2.2 hzB
  · intro h
    refine disjoint_left.2 fun w ⟨hwH, hw⟩ hwU => ?_
    have hB : c.2.1 w ∈ B := by
      by_contra hn
      exact hw ⟨hwH, hc.dom_subset (hc.inv_mem_dom hwH), hn⟩
    exact disjoint_left.1 h hB ⟨w, hwU, rfl⟩

/-- The launch image is hitting-measurable for any marks recording the set. -/
theorem measurable_launch {Ω : Type*} {𝓜 : MeasurableSpace Ω} {c : Chart} (hc : c.IsConformal)
    {B : Ω → Set ℂ} (hBm : Measurable[𝓜, hittingSigma] B) :
    Measurable[𝓜, hittingSigma] fun ω => H \ chartPre c (H \ B ω) := by
  refine Sec5.Aux61ULoc.measurable_hitting_of_avoid fun U hU hUH => ?_
  have ho : IsOpen (c.2.1 '' U) := hc.isOpen_image_of_subset hU hUH
  have hsub : c.2.1 '' U ⊆ H := by
    rintro _ ⟨w, hw, rfl⟩
    exact hc.dom_subset (hc.inv_mem_dom (hUH hw))
  have he : {ω | Disjoint (H \ chartPre c (H \ B ω)) U} = B ⁻¹' {S | Disjoint S (c.2.1 '' U)} := by
    ext ω
    exact disjoint_launch_iff hc hUH
  rw [he]
  exact hBm (measurableSet_avoid ho hsub)

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The explored set of the earlier pieces lies in the union, almost surely** (root `0`, time-ordered history). -/
theorem ae_stageSet_subset_schedUnionS (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hr0 : rootPt r.1 = 0)
    (hord : Sec5.Prop513Schedule.TimeOrdered 0 (historyProgram c r l)) (t : ℝ≥0) :
    ∀ᵐ ω ∂c.P, WalkLaw.stageSet c.κ c.b c.jumps (GW2Olm.futSpec c r l a) (GW2Olm.futFam c r l a)
      (GW2Olm.curIdx c r l) ω ⊆ schedUnionS c r l a t ω := by
  filter_upwards [Gm.ae_futureJoined_trace h13 c r, ae_schedW_trace c r l a h13] with ω hfut htr
  intro z hz
  by_cases hωE : oldSuccess c r l ω
  swap
  · have e : schedUnionS c r l a t ω = H := by simp only [schedUnionS, hωE, ↓reduceIte]
    rw [e]
    exact hz.2
  set x := rootPt r.1 with hx
  set Lh := historyProgram c r l with hLh
  set y : ℝ × ℝ≥0 := ((candidateAngle c r a : ℝ), historyTime c r l + candidateCap c r a) with hy
  -- the run of the future program through the history is the history's run
  have hrun := RootC11.run_schedSpec_append c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x y ω
    (l := Lh) (n := Lh.length) le_rfl
  have hz' : z ∈ (⋃ p ∈ (ExplState.run c.κ c.b c.jumps (schedSpec x Lh)
      (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lh) j ω) Lh.length).1,
      p.1.tipSet p.2.1 p.2.2) := by
    rw [← hrun]
    exact hz.1
  have hlen : (schedSpec x Lh).2.2.length = Lh.length := length_scheduleProgram 0 Lh
  have hzP : z ∈ prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x Lh ω := by
    change z ∈ ExplState.physSet c.κ c.b c.jumps (schedSpec x Lh)
      (fun k => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lh) k ω)
    unfold ExplState.physSet
    simp only []
    rw [hlen]
    exact Or.inl (Or.inr hz')
  have hγ : IsGeneratingTrace (Gm.futureJoined c r l a ω) ⊤ (schedTr c r l a ω) := by
    rw [← schedW_of_oldSuccess c r l a hωE]
    exact htr.1
  rw [Gm.prefixSet_history_eq c r l a ω hord hωE (hfut l a hωE).1 hγ] at hzP
  obtain ⟨w, ⟨s, hs, rfl⟩, rfl⟩ := hzP
  have h0 : rootPt r.1 = 0 := hr0
  simp only [h0, Complex.ofReal_zero, zero_add] at hz ⊢
  -- the trace lies in the filled explored hull at `T + t`
  have hfill : IsFilling (schedHull c r l a (historyTime c r l + t) ω)
      (schedTr c r l a ω '' Icc 0 (historyTime c r l + t)) :=
    htr.1.2.2 (historyTime c r l + t) ENNReal.coe_lt_top
  have hmem : schedTr c r l a ω s ∈ schedHull c r l a (historyTime c r l + t) ω := by
    by_contra hn
    obtain ⟨⟨z₀, -, hcc⟩, -⟩ := hfill
    have hin : schedTr c r l a ω s ∈ H \ schedHull c r l a (historyTime c r l + t) ω := ⟨hz.2, hn⟩
    rw [← hcc] at hin
    exact (connectedComponentIn_subset _ _ hin).2 ⟨s, ⟨hs.1, hs.2.trans le_self_add⟩, rfl⟩
  have e : schedUnionS c r l a t ω = schedUnion c r l a (historyTime c r l) t ω := by
    rw [GW2Sdj.schedUnionS_eq_schedUnionL]
    exact schedUnionL_eq_of_oldSuccess c r l a _ t hωE
  rw [e]
  exact Or.inr hmem

end InteractingSLE.Theorem14.GW2Rd
