/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NuSafe
import InteractingSLE.Spec.Supplement.GW2NuMean

/-!
# D38's export without SAFE's version: the stage driver's own hull identity on the pre-cap window

Packet PROVE-GW2-NOTHR (round 3). D38's export `GW2Nt.StageKernelExportX` asked, besides GEOM2's launch datum and
STAGEMEAN's Claim(j), for SAFE's per-sample facts at the counterflow's own time `t₀`: a good sample
(`RelSafe.PhysGood`), a global relative version `(R, V)` (`RelSafe.VersionAt`) and its cofinality. Those are now
discharged (`GW2Nu.ae_no_threshold_gw2_at`). The good sample comes from the datum's traces at every `t₀`. The version is
replaced, at each stage time `u` of the pre-cap window, by the dilated stage driver `scD λ (stage driver)` itself:

* **`StageKernelExportL`**: GEOM2's launch configuration (now with the counterflow complete with its trace, as
  `GW2Xk.ae_launch_form_pairX` gives it) and, `ν`-almost surely on the record event, Claim(j)'s data identity and, at
  each stage time `u` of the pre-cap window, (a) `λ² u` is below the relative clock of a time before the physical end
  and (b) the dilated stage driver generates the relative hulls at every relative time `≤ λ² u`. No `PhysGood`, no
  `(R, V)`, and no continuity at the relative contact is asked;
* **`noThresholdX_of_exportL`**: `GW2Rz.NoThresholdX` of ROOTX's instance from it;
* **`ExportFamilyL`**, **`hno_of_exportL`**, **`hmean_noThreshold_of_exportL`**, **`hmean_of_exportL`**: the binder
  `hno` of the current top and the `noThreshold` clause of the `hmean` binder of
  `Wire.theorem14Statement_assembled7` (D36) from it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Nu

open Restart Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Supp8 Supp8.GB6 GW2Rd GW2TipSystem
  GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rv GW2Sde GW2Sdh GW2Sdi GW2Schedule GW2Tip MartChar.RealFlow
  Sec5.CrossCond.StagedRepLater Sec5.Prop513Schedule Supp8.GB6.RelDrv Supp8.RelSafe GW2Nt

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **D38's export, SAFE's version facts discharged** (PROVE-GW2-STAGEMEAN; launch datum PROVE-GW2-GEOM2): for
`P`-almost every `ω₀`, at a launch `(cL, θ)` of the candidate, under the launch kernel `ν`: a flow line `(Wα, ζα, α)`
of the launch field `h` at angle `θ` and the complete counterflow `(W, ζ = ⊤, γ)` of the infinity-chart field `h'`,
a word `cw` of the counterflow data; and, `ν`-almost surely on the instance's record event, at the counterflow's own
time `t₀`: an interior tip, the dilation `λ > 0`, the stage-start data identity off a finite set, and at every stage
time `u` of the pre-cap window, `λ² u` is below the relative clock of a time before the physical end and the dilated
stage driver generates the relative hulls at the relative times `≤ λ² u`. -/
def StageKernelExportL (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (I : StageInst Ω) (x₀ : ℝ) : Prop :=
  ∀ᵐ ω₀ ∂c.P, ∀ (cL : Chart) (θ : ℝ), GW2Olm.curLaunch c r l a ω₀ = some (cL, θ) →
    ∃ (b : ℝ → ℝ) (J : Finset ℝ) (h : Ω → DistOn upperHalfPlaneOpens) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞)
      (α : Ω → ℝ≥0 → ℂ) (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens) (cw : BoundaryWord)
      (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ) (t₀ : Ω → ℝ≥0) (lam : Ω → ℝ) (F : Ω → Set ℝ),
      IsPiecewiseConstantBoundaryData b J ∧ IsPiecewiseConstantBoundaryData b' J' ∧
      (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC c.κ)) (chiC (16 / c.κ)) (h ω) (h' ω)) ∧
      IsFlowLineDriver c.κ b J θ (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀) h Wα ζα ∧
      (∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀), IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) ∧
      IsFlowLineDriver (16 / c.κ) b' J' 0 (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀) h' W ζ ∧
      (∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀), ζ ω = ⊤ ∧
        IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω)) ∧
      cw.jumps = J' ∧ (∀ y ∉ J', cw.fn y = b' y) ∧
      ∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀), I.srecX c r l x₀ ω ∈ I.E →
        γ ω (t₀ ω) ∈ H ∧ 0 < lam ω ∧ (F ω).Finite ∧
        (∀ y, y ∉ F ω → (I.β (I.srecX c r l x₀ ω)).fn y = (gw2Word c.κ θ cw (gb6Rec (t₀ ω) W ζ ω)).fn (lam ω * y)) ∧
        ∀ u : ℝ≥0, (u : ℝ≥0∞) < I.capX c x₀ ω →
          (((I.T + candidateCap c r a : ℝ≥0) : ℝ≥0∞) < contactX x₀ c.s I.γ c.α ω →
            ((stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω : ℝ≥0) : ℝ) + u ≤
              clockX x₀ c.s c.W c.ζ I.W (I.T + candidateCap c r a) ω) →
          (∃ t : ℝ≥0, (t : ℝ≥0∞) < gw2End (t₀ ω) ζα γ α ω ∧ (lam ω) ^ 2 * u < gw2Clock (t₀ ω) W Wα ω t) ∧
          ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc (t₀ ω) (extTr (t₀ ω) Wα ζα α) γ ω →
            gb6Clock (t₀ ω) (regW (t₀ ω) Wα ζα) W ω t ≤ (lam ω) ^ 2 * u →
            fwdHull (scD (lam ω) (fun q : ℝ => I.drvX c x₀ q.toNNReal ω))
                (gb6Clock (t₀ ω) (regW (t₀ ω) Wα ζα) W ω t) =
              relMap (fun r : ℝ => W r.toNNReal ω) (t₀ ω) ''
                fwdHull (fun r : ℝ => regW (t₀ ω) Wα ζα r.toNNReal ω) t

omit mΩ [StandardBorelSpace Ω] in
/-- The relative clock is nonnegative. -/
theorem gb6Clock_nonneg (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) : 0 ≤ gb6Clock s W Wα ω t := by
  unfold gb6Clock relClock
  have h : 0 ≤ ConformalImage.hcapSet (relMap (fun r : ℝ => Wα r.toNNReal ω) s ''
      fwdHull (fun r : ℝ => W r.toNNReal ω) t) := by
    unfold ConformalImage.hcapSet
    split_ifs
    · exact HPHull.hcap_nonneg _
    · exact le_rfl
  positivity

/-- The dilated driver `scD λ D` is continuous for a continuous `D`. -/
theorem continuous_scD {lam : ℝ} {D : ℝ → ℝ} (hD : Continuous D) : Continuous (scD lam D) :=
  continuous_const.mul (hD.comp (continuous_id.div_const _))

/-- **`noThreshold` of the corrected root-`x` instance from the export without SAFE's version** (route (M)): the
collision exclusion at each relative time (`ae_no_threshold_gw2_at`) along the dilated stage driver, the data-level
transfer on the pre-cap window, the after-cap part beyond it, and the kernel-to-`P` transfer. -/
theorem noThresholdX_of_exportL (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    (hord : TimeOrdered 0 (historyProgram c r l)) {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : SchedChoice Ω)
    (hβ : Measurable ch.β ∧ (range fun y => Supp8.Q3Stop.wordType c.κ (ch.β y)).Countable ∧ ∀ y, (ch.β y).IsSorted)
    (hE₀ : MeasurableSet ch.E₀)
    (hexp : StageKernelExportL c r l a (schedInstSX c r l a GT hA ch) (rootPt r.1)) :
    NoThresholdX (schedInstSX c r l a GT hA ch) c r l (rootPt r.1) := by
  set I := schedInstSX c r l a GT hA ch with hI
  set x := rootPt r.1 with hxdef
  have hWm : ∀ t, Measurable (I.W t) := measurable_schedW c r l a
  have hver : IsRelVersionXR x c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V := hA.1
  have hv : IsRelVersionX x c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V := hA.1.1
  have hρ := hA.1.2.choose_spec
  have hpre : Measurable (stgPreRecX x c.s c.W c.ζ I.W I.GT I.V I.T I.R) :=
    (measurable_stgPreRecX hGT.1 hs hx (measurable_gb6Rec_src c) hWm
      (measurableSet_goodSetX_physFilt (measurable_gb6Rec_src c) hWm hGT.2.1 hGT.2.2) hver I.T).mono
      ((physFilt (measurable_gb6Rec_src c) hWm c.P).le I.T) le_rfl
  have hE : MeasurableSet I.E :=
    (hE₀.inter (measurableSet_succRec c r l)).inter (measurableSet_aliveRecX _ _ c.s hρ.1)
  have hrec : Measurable (I.srecX c r l x) := measurable_augRec (measurable_stageEncRec c r l) hpre
  have hDm : ∀ t, Measurable (I.drvX c x t) := measurable_stgRX hv.1 hv.2.1 hpre
  have hDc : ∀ ω, Continuous fun t => I.drvX c x t ω := fun ω => continuous_stgDrv (hv.2.1 ω) _
  have hcap : Measurable (I.capX c x) := measurable_stgVX hv.2.2.2.2.1 hpre
  set L := futureProgram c r l a with hL
  set spec := GW2Olm.futSpec c r l a with hspec
  set E := GW2Olm.futFam c r l a with hEdef
  set k := GW2Olm.curIdx c r l with hkdef
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _)
  have h𝒢 : GW2Olm.pastG c r l a ≤ mΩ := hS.2.1 k
  have hlenL : L.length = k + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
  have hlen : spec.2.2.length = k + 1 := (GW2Schedule.length_scheduleProgram 0 L).trans hlenL
  have hLS : MeasurableSet[GW2Olm.pastG c r l a] {ω | AllSucc (specDelta spec) (fun j => E j ω) k} :=
    measurableSet_allSucc (κ := c.κ) (b := c.b) (jumps := c.jumps) rfl (isFlowProg_spec x true L)
      (specDelta_ne_top _) E (by rw [hlen]; omega)
  have hcov : ∀ᵐ ω ∂c.P, I.srecX c r l x ω ∈ I.E → ω ∈ {ω | AllSucc (specDelta spec) (fun j => E j ω) k} :=
    Eventually.of_forall fun ω hEω =>
      Gm.allSucc_future_of_oldSuccess c r l a ω ((augRec_mem_succRec_iff c r l _ ω).1 hEω.1.2)
  have hACk := KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (ae_not_threshold_afterCapX c r l a hx hs hord hGT hA hV ch)
  refine ae_noThr_of_kernel h𝒢 hrec hE hβ.1 hβ.2.1 hDm hDc hcap hLS hcov ?_
  filter_upwards [hexp, hACk] with ω₀ hX hAC₀ hL₀
  have hlaunch := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _) (fun j => E j ω₀) (show k < spec.2.2.length by omega)).1 hL₀
  obtain ⟨b, J, h, Wα, ζα, α, b', J', h', cw, W, ζ, γ, t₀, lam, F, hb, hb', hT, hfl, hα, hcf, hγ, hcwJ, hcwb,
    hid⟩ := hX _ _ hlaunch
  have hG := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver c.hκ hb hfl
  have hsafe := ae_no_threshold_gw2_at c.hκ c.hκ4 hb hG hb' hT hfl hα hcf hγ cw hcwJ hcwb
  filter_upwards [hsafe, hid, hAC₀] with ω hs1 hid1 hac hEω u hu
  by_cases hwin : ((I.T + candidateCap c r a : ℝ≥0) : ℝ≥0∞) < contactX x c.s I.γ c.α ω ∧
      clockX x c.s c.W c.ζ I.W (I.T + candidateCap c r a) ω <
        ((stgStartX x c.s c.W c.ζ I.W I.GT I.V I.T ω : ℝ≥0) : ℝ) + u
  · exact hac hEω u hu hwin.1 hwin.2 (Restart.FlowStopIdentCMI.flowLineXL_nonpos' _ _ 0)
      (Restart.FlowStopIdentCMI.flowLineXR_nonneg' _ _ 0)
  · obtain ⟨hγH, hlam, hFfin, hdata, hw⟩ := hid1 hEω
    obtain ⟨hcof, hhull⟩ := hw u hu fun hc => le_of_not_gt fun hlt => hwin ⟨hc, hlt⟩
    set D : ℝ → ℝ := fun q : ℝ => I.drvX c x q.toNNReal ω with hDdef
    have hDc' : Continuous D := (hDc ω).comp continuous_real_toNNReal
    have hD0 : D 0 = 0 := by
      simp only [hDdef, Real.toNNReal_zero]
      exact GW2Rd.stgDrv_zero _ _
    set Rr : ℝ≥0 → ℝ := fun v => scD (lam ω) D v with hRrdef
    have hRrc : Continuous Rr := (continuous_scD hDc').comp NNReal.continuous_coe
    have hRr0 : Rr 0 = 0 := by simp [hRrdef, scD, hD0]
    have hpos : (0 : ℝ) ≤ lam ω ^ 2 * u := mul_nonneg (sq_nonneg _) u.coe_nonneg
    have hcoe : (((lam ω ^ 2 * u).toNNReal : ℝ≥0) : ℝ) = lam ω ^ 2 * u := Real.coe_toNNReal _ hpos
    have hRrW : ∀ v ∈ Icc (0 : ℝ) (lam ω ^ 2 * u), Rr v.toNNReal = scD (lam ω) D v := fun v hv => by
      simp only [hRrdef, Real.coe_toNNReal _ hv.1]
    have hn := hs1 (t₀ ω) hγH Rr hRrc hRr0 (lam ω ^ 2 * u).toNNReal (by
      obtain ⟨t, ht, hlt⟩ := hcof
      exact ⟨t, ht, by rw [hcoe]; exact hlt⟩) (fun t ht hle => by
      have hle' : gb6Clock (t₀ ω) (regW (t₀ ω) Wα ζα) W ω t ≤ lam ω ^ 2 * u := by
        change ENNReal.ofReal _ ≤ ENNReal.ofReal _ at hle
        exact (ENNReal.ofReal_le_ofReal_iff hpos).1 hle
      rw [← hhull t ht hle']
      refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc (hRrc.comp continuous_real_toNNReal) (continuous_scD hDc')
        (gb6Clock_nonneg _ _ _ _ _) fun v hv => ?_
      show scD (lam ω) D ((v.toNNReal : ℝ≥0) : ℝ) = scD (lam ω) D v
      rw [Real.coe_toNNReal _ hv.1])
    have h1 := not_threshold_stage_of_joint c.hκ hlam hFfin hdata (D := D) hDc' (Rr := Rr) hRrW hn
    simp only [hDdef, Real.toNNReal_coe] at h1
    exact h1

/-- **The export without SAFE's version at every root-`x` instance of a version family and a base family.** -/
def ExportFamilyL (ver : SchedVerXFamily.{u}) (base : SchedChoiceFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GoodRoot c r) → ∀ a n : ℕ,
      StageKernelExportL c r l a (Wire.T14Cur.instC ver base Ω c r l a n h) (rootPt r.1)

/-- **The binder `hno` of Theorem 1.4's current top from the export without SAFE's version.** -/
theorem hno_of_exportL {ver : SchedVerXFamily.{u}} {base : SchedChoiceFamily.{u}}
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, Measurable (base Ω c r l a).β ∧
        (Set.range fun y => Supp8.Q3Stop.wordType c.κ ((base Ω c r l a).β y)).Countable ∧
        ∀ y, ((base Ω c r l a).β y).IsSorted)
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, MeasurableSet (base Ω c r l a).E₀)
    (hexp : ExportFamilyL ver base) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GoodRoot c r) →
      ∀ a n : ℕ, NoThresholdX (Wire.T14Cur.instC ver base Ω c r l a n h) c r l (rootPt r.1) := by
  intro Ω _ _ c r l hTO h a n
  have hβ := hword Ω c r l hTO h a
  have hE := hE₀ Ω c r l hTO h a
  rw [← GW2Rd.schedChoiceLinesX_β Wire.T14Asm7.h12 Wire.T14Asm7.h13 base c r l a] at hβ
  rw [← GW2Rd.schedChoiceLinesX_E₀ Wire.T14Asm7.h12 Wire.T14Asm7.h13 base c r l a] at hE
  exact noThresholdX_of_exportL Wire.T14Asm7.h13 c r l a h.1 h.2 hTO (schedGTX_spec Wire.T14Asm7.h13 c r l a)
    ((ver Ω c r l a).isA h.1 n) ((ver Ω c r l a).fin n) (Wire.T14Cur.chL base Ω c r l a) hβ hE
    (hexp Ω c r l hTO h a n)

/-- **The clause `noThreshold` of the `hmean` binder of `Wire.theorem14Statement_assembled7`** (D36) from the export
without SAFE's version. -/
theorem hmean_noThreshold_of_exportL {ver : SchedVerXFamily.{u}} {base : SchedChoiceFamily.{u}}
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, Measurable (base Ω c r l a).β ∧
        (Set.range fun y => Supp8.Q3Stop.wordType c.κ ((base Ω c r l a).β y)).Countable ∧
        ∀ y, ((base Ω c r l a).β y).IsSorted)
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, MeasurableSet (base Ω c r l a).E₀)
    (hexp : ExportFamilyL ver base) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GoodRoot c r) → ∀ a n : ℕ,
        NoThresholdX (instX Wire.T14Asm7.h13 ver (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base)
          Ω c r l a n h.1) c r l (rootPt r.1) :=
  hno_of_exportL hword hE₀ hexp

/-- **The `hmean` binder of `Wire.theorem14Statement_assembled7` from its fields `mean` and `condGFF` and the
export without SAFE's version** (the field `noThreshold`). -/
theorem hmean_of_exportL {ver : SchedVerXFamily.{u}} {base : SchedChoiceFamily.{u}}
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, Measurable (base Ω c r l a).β ∧
        (Set.range fun y => Supp8.Q3Stop.wordType c.κ ((base Ω c r l a).β y)).Countable ∧
        ∀ y, ((base Ω c r l a).β y).IsSorted)
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, MeasurableSet (base Ω c r l a).E₀)
    (hexp : ExportFamilyL ver base)
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l →
      (h : GoodRoot c r) → ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0)
        (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean ((instX Wire.T14Asm7.h13 ver
          (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).B t)
          (WholeField.centredField c.h (instX Wire.T14Asm7.h13 ver
            (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          stageMeanAtX (instX Wire.T14Asm7.h13 ver
            (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1) c r l (rootPt r.1)
            w t ψ ω (g ω))
    (hcond : ∀ (Ω : Type u) [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l →
      (h : GoodRoot c r) → ∀ a n : ℕ,
        ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : ℝ),
          Measurable[𝒢.1] ((instX Wire.T14Asm7.h13 ver
            (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).srecX c r l
              (rootPt r.1)) ∧ 0 ≤ M ∧
          (∀ y ∈ (instX Wire.T14Asm7.h13 ver
            (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).E,
            ∀ x ∉ ((instX Wire.T14Asm7.h13 ver
              (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).β y).jumps,
              |((instX Wire.T14Asm7.h13 ver
                (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).β y).fn x| ≤ M) ∧
          ∀ᵐ ω₀ ∂c.P, (instX Wire.T14Asm7.h13 ver
            (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).srecX c r l
              (rootPt r.1) ω₀ ∈ (instX Wire.T14Asm7.h13 ver
                (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).E →
            IsGFFWithBoundaryData (condExpKernel c.P 𝒢.1 ω₀) (instX Wire.T14Asm7.h13 ver
              (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).Hr
              ((instX Wire.T14Asm7.h13 ver (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base)
                Ω c r l a n h.1).β ((instX Wire.T14Asm7.h13 ver
                  (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).srecX c r l
                    (rootPt r.1) ω₀)).fn
              ((instX Wire.T14Asm7.h13 ver (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base)
                Ω c r l a n h.1).β ((instX Wire.T14Asm7.h13 ver
                  (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).srecX c r l
                    (rootPt r.1) ω₀)).jumps) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GoodRoot c r) → ∀ a n : ℕ,
        GW2Rd.OpenLinesMeanX (instX Wire.T14Asm7.h13 ver
          (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1) c r l (rootPt r.1) :=
  fun Ω _ _ c r l hTO h a n =>
    ⟨hmeanF Ω c r l hTO h a n, hmean_noThreshold_of_exportL hword hE₀ hexp Ω c r l hTO h a n,
      hcond Ω c r l hTO h a n⟩

end InteractingSLE.Theorem14.GW2Nu
