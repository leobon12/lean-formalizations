/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TwCons
import InteractingSLE.Spec.Supplement.GW2KxInst
import InteractingSLE.Spec.Supplement.GW2PsmMeanI
import InteractingSLE.Spec.Supplement.GW2NwMean

/-!
# Claim(k) at a root `x`: the `mean` statement

Packet PROVE-GW2-RELDET (round 34, decision D58 item 2, the root-`x` wrapper as NOTHR's round 5). STAGEMEAN's
`GW2Psm.meanX_inst` (root `0`) ported to a root `x ∈ {0} ∪ lowerArcRoots`, in the root-`x` stage chart:

* **`meanX_instX`**: `stageMeanAtX` at ROOTX's corrected root-`x` instance, for every local-set mean of `B t` and
  every stage time, from Claim(k) in the root-`x` chart (`GW2Kx.ClaimAtX`), the life and cap readings and the far
  height (GEOM2's `pair_instX`, `ae_shape_rootX`, `harmonicOnNhd_stgMeanRX`, `isDomainChart_stgChart_relChartX`;
  STAGEMEAN's `StageInst.meanX_of_pair`);
* **`meanX_histX`**: the same at every strictly time-ordered history, for versions stopped at the candidate's stop
  (D49 (A)), from Claim(k) at the history (`ClaimAllX`) — NOTHR's `GW2Nw.meanX_hist` at a root `x`;
* **`hmeanF_rootX_of_nil`**: the top's `hmeanF` at roots `x ∈ {0} ∪ lowerArcRoots` (NOTHR's `hmeanF_root0`), with
  Claim(k)'s base at the roots of `lowerArcRoots` (GEOM2's, D58) as its one input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Rz GW2Sde Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop
  Restart.DomainMarkov MartChar.RealFlow GW2JointKernel Sec7.PocketTraversal Supp8.RelSafe GW2Psm

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The per-stage mean at ROOTX's corrected instance at a root `x ∈ {0} ∪ lowerArcRoots`** (one word type, every
stage time), from Claim(k) in the root-`x` chart (`GW2Kx.ClaimAtX`). -/
theorem meanX_instX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) (hs0 : 0 < c.s)
    {GT : Set Ω} (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : GW2Sdh.SchedChoice Ω) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (hkc : ch.kc = chiC c.κ) (hβm : Measurable ch.β) (hE₀ : MeasurableSet ch.E₀) (w : WordType) (t : ℝ≥0)
    (hcapb : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω <
        (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω → t < candidateCap c r a)
    (hlife : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω <
        (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω →
      (t : ℝ≥0∞) < candLife c r l a ω)
    (hfar : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      GW2Wm.FarR (ch.β ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω))
        (sleLambda (16 / c.κ) - Real.pi * chiC c.κ + candAngle c r l a * chiC c.κ))
    (hclaim : GW2Kx.ClaimAtX c r l a GT hA ch w)
    (g : Ω → DistOn upperHalfPlaneOpens)
    (hg : IsLocalSetMean ((GW2Rv.schedInstSX c r l a GT hA ch).B t) (centredField c.h ch.u₀) c.P g)
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂c.P, stageMeanAtX (GW2Rv.schedInstSX c r l a GT hA ch) c r l (rootPt r.1) w t ψ ω (g ω) := by
  classical
  have hx : (0 : ℝ) ≤ rootPt r.1 :=
    hroot.elim (fun h => h.ge) fun h => (GW2Sched.pos_of_mem_lowerArcRoots h).le
  have hv := hA.1.1
  have hB : ∀ q : ℝ≥0, (GW2Rv.schedInstSX c r l a GT hA ch).B q = schedUnionX c r l a (historyTime c r l) q :=
    fun q => schedUnionSX_eq_schedUnionX c r l a q
  -- beyond the cap the statement is vacuous
  by_cases htc : t < candidateCap c r a
  swap
  · filter_upwards [hcapb] with ω h hlive hlt
    exact absurd (h hlive hlt) htc
  set I := GW2Rv.schedInstSX c r l a GT hA ch with hIdef
  set a₀ : Ω → ℝ≥0 := fun ω => stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω
    with ha₀
  set cs : Ω → Chart := fun ω => stgChart (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) (fun q => R q ω) (a₀ ω)
    with hcsdef
  set Q : Ω → ℝ≥0 := fun ω => (I.clockX c (rootPt r.1) t ω).toNNReal with hQdef
  set VLp : Fin w.1 → ℝ≥0 → Ω → ℝ := fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (ch.β y.1)) i t
    (I.srecX c r l (rootPt r.1) ω, relVar I.Hr (I.drvX c (rootPt r.1)) (I.capX c (rootPt r.1)) ω) with hVLp
  set VRp : Fin w.2.1 → ℝ≥0 → Ω → ℝ := fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (ch.β y.1)) j t
    (I.srecX c r l (rootPt r.1) ω, relVar I.Hr (I.drvX c (rootPt r.1)) (I.capX c (rootPt r.1)) ω) with hVRp
  set U : Ω → ℂ → ℝ := fun ω => bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drvX c (rootPt r.1)) VLp VRp ω (Q ω)
    with hU
  have hUh : ∀ ω, InnerProductSpace.HarmonicOnNhd (U ω) H := fun ω =>
    (bhe_bheProc_typedX (r := r) (l := l) I (rootPt r.1) w ω (continuous_stgDrv (hv.2.1 ω) _) (stgDrv_zero _ _)
      (Q ω)).1
  set Mf : Ω → ℂ → ℝ := fun ω =>
    GW2Kx.stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) (Q ω) (U ω) ch.u₀
      ch.σa with hMf
  set M : Ω → ℂ → ℝ := fun ω => if H \ I.B t ω =
      (cs ω).2.1 '' (H \ fwdHull (Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω))) (Q ω)) then Mf ω else 0 with hM
  have hMh : ∀ ω, InnerProductSpace.HarmonicOnNhd (M ω) (H \ I.B t ω) := by
    intro ω
    by_cases hc : H \ I.B t ω = (cs ω).2.1 '' (H \ fwdHull (Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω))) (Q ω))
    · simp only [hM, hc, ↓reduceIte]
      exact GW2Kx.harmonicOnNhd_stgMeanRX c.κ (rootPt r.1) c.s _ (hv.2.1 ω) (hv.2.2.1 ω) (a₀ ω) (Q ω).coe_nonneg
        (hUh ω) hu₀.1 ch.σa
    · simp only [hM, hc, ↓reduceIte]
      exact fun z _ => InnerProductSpace.harmonicAt_const 0
  have hρ := hA.1.2.choose_spec
  have hfin : ∀ᵐ ω ∂c.P, I.srecX c r l (rootPt r.1) ω ∈ I.E →
      stgStartMX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ => ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
  have hEgood := StageInst.E_good_of_recordX I hv hρ.2.1 hρ.2.2 inter_subset_right hfin
  have hGs : ∀ ω, ω ∈ liveEvRec c.κ w ch.β I.E (I.srecX c r l (rootPt r.1)) → oldSuccess c r l ω :=
    fun ω h => (GW2Sdi.augRec_mem_succRec_iff c r l _ ω).1 h.1.1.2
  have hltVG : ∀ ω, I.clockX c (rootPt r.1) t ω < I.capX c (rootPt r.1) ω →
      min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + t) ω) (V ω) < V ω := by
    intro ω hlt
    have hstartne : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω ≠ ⊤ :=
      ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
    by_contra hcon
    push Not at hcon
    have h1 : V ω - stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω ≤
        min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + t) ω) (V ω) -
          stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω :=
      tsub_le_tsub_right hcon _
    have h2 : I.capX c (rootPt r.1) ω =
        V ω - stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω := by
      show V ω - ((stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω).toNNReal :
        ℝ≥0∞) = _
      rw [ENNReal.coe_toNNReal hstartne]
    have h3 : I.clockX c (rootPt r.1) t ω =
        min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + t) ω) (V ω) -
          stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω := rfl
    have hlt' := hlt
    rw [h2, h3] at hlt'
    exact absurd (lt_of_lt_of_le hlt' h1) (lt_irrefl _)
  have hsh : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β I.E (I.srecX c r l (rootPt r.1)) →
      I.clockX c (rootPt r.1) t ω < I.capX c (rootPt r.1) ω →
      H \ I.B t ω = (cs ω).2.1 '' (H \ fwdHull (Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω))) (Q ω)) ∧
        I.chartX c (rootPt r.1) ω = cs ω := by
    filter_upwards [GW2Kx.ae_shape_rootX c r l a hx hs0 hGT.1 hv, hGT.2.2, hEgood, c.hζ] with ω hshω hGTω hEω hζ
      hlive hlt
    have hωGT : ω ∈ GT := hGTω.2 (hEω hlive.1).1
    have hsh := hshω hωGT (hGs ω hlive) t (hltVG ω hlt)
    have e : ((Q ω : ℝ)) =
        (capA (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) t ω : ℝ) - a₀ ω :=
      coe_toNNReal_stgClockX hGT.1 hs0 hx (historyTime c r l) t (hV ω)
    have hsum : a₀ ω + Q ω = capA (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) t ω := by
      apply NNReal.eq
      rw [NNReal.coe_add, e]
      ring
    have hiv := stgChart_inv_image (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) (hv.2.1 ω) (hv.2.2.1 ω) (a₀ ω)
      (Q ω)
    rw [hsum] at hiv
    refine ⟨by rw [hB t, hsh, ← hiv], ?_⟩
    rfl
  have hpair : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
      ω ∈ liveEvRec c.κ w ch.β I.E (I.srecX c r l (rootPt r.1)) ∩
        {ω | I.clockX c (rootPt r.1) t ω < I.capX c (rootPt r.1) ω} →
      tsupport φ ⊆ H \ I.B t ω → g ω φ = ∫ z, M ω z * φ z := by
    intro φ
    by_cases ht0 : t = 0
    · subst ht0
      filter_upwards [hclaim g hg φ, hsh] with ω h1 h2 hωG hsupp
      have hlt : I.clockX c (rootPt r.1) 0 ω < I.capX c (rootPt r.1) ω := hωG.2
      have hcap0 : (0 : ℝ≥0∞) < I.capX c (rootPt r.1) ω := lt_of_le_of_lt zero_le hlt
      rw [h1 hωG.1 hcap0 hsupp]
      have hc := (h2 hωG.1 hlt).1
      have hQ0 : Q ω = 0 := by
        show (stgClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) 0 ω).toNNReal = 0
        rw [stgClock_zeroX, ENNReal.toNNReal_zero]
      congr 1
      funext z
      simp only [hM, hc, ↓reduceIte, hMf, hU, hQ0, NNReal.coe_zero]
      rfl
    · have htpos : 0 < t := pos_iff_ne_zero.2 ht0
      filter_upwards [GW2Kx.pair_instX h12 h13 h12₀ h13₀ c r l a hroot hord hs0 hGT hA hV ch hu₀ hkc hβm hE₀ w t htpos
        htc hlife hfar hclaim g hg φ, hsh] with ω h1 h2 hωG hsupp
      have hlt : I.clockX c (rootPt r.1) t ω < I.capX c (rootPt r.1) ω := hωG.2
      rw [h1 hωG.1 hlt hsupp]
      have hc := (h2 hωG.1 hlt).1
      congr 1
      funext z
      simp only [hM, hc, ↓reduceIte, hMf, hU]
      rfl
  have hread : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β I.E (I.srecX c r l (rootPt r.1)) ∩
        {ω | I.clockX c (rootPt r.1) t ω < I.capX c (rootPt r.1) ω} →
      ∀ z ∈ H \ fwdHull (fun s : ℝ => I.drvX c (rootPt r.1) s.toNNReal ω)
        ((I.clockX c (rootPt r.1) t ω).toNNReal : ℝ),
      M ω ((I.chartX c (rootPt r.1) ω).2.1 z) + I.u₀ ((I.chartX c (rootPt r.1) ω).2.1 z) + I.σa +
          I.kc * (I.chartX c (rootPt r.1) ω).2.2 ((I.chartX c (rootPt r.1) ω).2.1 z) =
        couplingMean c.κ (fun s : ℝ => I.drvX c (rootPt r.1) s.toNNReal ω) (I.clockX c (rootPt r.1) t ω).toNNReal
          (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drvX c (rootPt r.1))
            (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
              (I.srecX c r l (rootPt r.1) ω, relVar I.Hr (I.drvX c (rootPt r.1)) (I.capX c (rootPt r.1)) ω))
            (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
              (I.srecX c r l (rootPt r.1) ω, relVar I.Hr (I.drvX c (rootPt r.1)) (I.capX c (rootPt r.1)) ω)) ω
            (I.clockX c (rootPt r.1) t ω).toNNReal) z := by
    filter_upwards [hsh] with ω h hωG z hz
    have hlt : I.clockX c (rootPt r.1) t ω < I.capX c (rootPt r.1) ω := hωG.2
    obtain ⟨hc, hch⟩ := h hωG.1 hlt
    rw [hch]
    simp only [hM, hc, ↓reduceIte, hMf]
    have hconf : (cs ω).IsConformal :=
      (GW2Kx.isDomainChart_stgChart_relChartX (rootPt r.1) c.s _ (hv.2.1 ω) (hv.2.2.1 ω) (a₀ ω)).isConformal
    have hfi : (cs ω).1 ((cs ω).2.1 z) = z := hconf.2.2 z hz.1
    unfold GW2Kx.stgMeanRX
    rw [hfi]
    show _ + ch.u₀ _ + ch.σa + ch.kc * _ = _
    rw [hkc]
    have e1 : (cs ω).2.2 ((cs ω).2.1 z) =
        (stgChart (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) (fun q => R q ω) (a₀ ω)).2.2 ((cs ω).2.1 z) := rfl
    rw [e1]
    have e2 : ∀ x y v w' : ℝ, x - y - v - w' + y + v + w' = x := fun x y v w' => by ring
    rw [e2]
    rfl
  have hcsm : WalkInf.IsMeasChart mΩ fun ω => I.chartX c (rootPt r.1) ω := by
    have hWm : ∀ q, Measurable (schedW c r l a q) := measurable_schedW c r l a
    have hGTm : ∀ q, MeasurableSet[physFilt (measurable_gb6Rec_src c) hWm c.P q] GT :=
      measurableSet_goodSetX_physFilt (measurable_gb6Rec_src c) hWm hGT.2.1 hGT.2.2
    have hpre : Measurable (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) R) :=
      (measurable_stgPreRecX hGT.1 hs0 hx (measurable_gb6Rec_src c) hWm hGTm hA.1 (historyTime c r l)).mono
        ((physFilt (measurable_gb6Rec_src c) hWm c.P).le _) le_rfl
    exact isMeasChart_stgChartX (measurable_gb6Rec_src c) hv.2.1 hv.2.2.1 hpre
  exact StageInst.meanX_of_pair (G := liveEvRec c.κ w ch.β I.E (I.srecX c r l (rootPt r.1)) ∩
      {ω | I.clockX c (rootPt r.1) t ω < I.capX c (rootPt r.1) ω}) I (rootPt r.1) w t hcsm.2.1 hu₀.1
    (fun ω => by rw [hB t]; exact schedUnionX_subset_isOpen c r l a (historyTime c r l) t ω)
    (Eventually.of_forall fun ω h1 h2 => ⟨h1, h2⟩)
    (by filter_upwards [hsh] with ω h h1 h2; rw [(h h1 h2).2]; exact (h h1 h2).1) hMh g hg.2.1 hpair hread ψ

/-- **The `mean` statement at a root-`x` instance of a strictly time-ordered history**, for versions stopped at the
candidate's stop (D49 (A)), from Claim(k) at the history in the root-`x` chart (NOTHR's `GW2Nw.meanX_hist` at a root
`x ∈ {0} ∪ lowerArcRoots`). -/
theorem meanX_histX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
    (hs0 : 0 < c.s) {cw : BoundaryWord} (l : List (EntryIdx c.Θ c.Q))
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) (hall : ClaimAllX c r cw l) (a : ℕ)
    {GT : Set Ω} (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : GW2Sdh.SchedChoice Ω) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (hkc : ch.kc = chiC c.κ) (hβm : Measurable ch.β) (hE₀ : MeasurableSet ch.E₀)
    (hβ : ch.β = GW2Wm.schedWordMapX c.κ cw (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
      (length_historyProgram c r l) (candAngle c r l a))
    (hσa : ch.σa = specOffset c.κ + candAngle c r l a * chiC c.κ) (w : WordType)
    (hVd : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      V ω ≤ physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + candStop c r l a ω) ω)
    (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens)
    (hg : IsLocalSetMean ((GW2Rv.schedInstSX c r l a GT hA ch).B t) (centredField c.h ch.u₀) c.P g)
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂c.P, stageMeanAtX (GW2Rv.schedInstSX c r l a GT hA ch) c r l (rootPt r.1) w t ψ ω (g ω) := by
  have hx : (0 : ℝ) ≤ rootPt r.1 :=
    hroot.elim (fun h => h.ge) fun h => (GW2Sched.pos_of_mem_lowerArcRoots h).le
  have hstop : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω <
        (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω → t < candStop c r l a ω := by
    filter_upwards [hVd] with ω hω hlive hlt
    exact lt_stop_of_clockX c r l a hs0 hx hGT.1 hA hV ch (hω hlive) hlt
  have hcapb : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω <
        (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω → t < candidateCap c r a := by
    filter_upwards [hstop] with ω hω hlive hlt
    exact capb_of_stop (hω hlive hlt)
  have hlife : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω <
        (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω → (t : ℝ≥0∞) < candLife c r l a ω := by
    filter_upwards [hstop] with ω hω hlive hlt
    exact life_of_stop (hω hlive hlt)
  have hfar := ae_farR_srecX c r l a hGT hA hV ch cw (length_historyProgram c r l) (candAngle c r l a) hβ w
  exact meanX_instX h12 h13 h12₀ h13₀ c r l a hroot hord hs0 hGT hA hV ch hu₀ hkc hβm hE₀ w t hcapb hlife hfar
    (hall a hGT hA hV ch hu₀ hβm hE₀ hβ hσa w) g hg ψ

/-- **The `hmeanF` binder of Theorem 1.4's current top at roots `x ∈ {0} ∪ lowerArcRoots`** and strictly
time-ordered histories, at the top's instances `T14Cur.instC ver (T14Cur.baseWm cw)`, for version families stopped at
the candidate's stop (D49 (A)) and counterflow words `cw` (NOTHR's `GW2Nw.hmeanF_root0` at a root `x`). Conditional
helper: its one input `hnil` is Claim(k)'s base at the roots of `lowerArcRoots` (GEOM2's root-`x` base, D58); at the
root `0` the base is GEOM2's landed `GW2Kc.claimAt_nil`. -/
theorem hmeanF_rootX_of_nil (ver : GW2Rv.SchedVerXFamily.{u}) (cw : Wire.T14Cur.CfWord.{u})
    (hcw : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ (cw Ω c r))
    (hnil : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), GW2Rv.GoodRoot c r → rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps →
      ClaimAllX c r (cw Ω c r) [])
    (hVd : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) → (h : GW2Rv.GoodRoot c r) → ∀ (a n : ℕ)
      (w : WordType), ∀ᵐ ω ∂c.P,
        ω ∈ liveEvRec c.κ w (Wire.T14Cur.instC ver (Wire.T14Cur.baseWm cw) Ω c r l a n h).β
          (Wire.T14Cur.instC ver (Wire.T14Cur.baseWm cw) Ω c r l a n h).E
          ((Wire.T14Cur.instC ver (Wire.T14Cur.baseWm cw) Ω c r l a n h).srecX c r l (rootPt r.1)) →
        (ver Ω c r l a).V n ω ≤ physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
          (schedGTX Wire.T14Asm7.h13 c r l a) (historyTime c r l + candStop c r l a ω) ω) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
      (h : GW2Rv.GoodRoot c r) → (rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) →
      ∀ (a n : ℕ) (w : WordType) (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean ((Wire.T14Cur.instC ver (Wire.T14Cur.baseWm cw) Ω c r l a n h).B t)
        (centredField c.h (Wire.T14Cur.instC ver (Wire.T14Cur.baseWm cw) Ω c r l a n h).u₀) c.P g →
      ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
        stageMeanAtX (Wire.T14Cur.instC ver (Wire.T14Cur.baseWm cw) Ω c r l a n h) c r l (rootPt r.1) w t ψ ω
          (g ω) := by
  intro Ω _ _ c r l hord h hroot a n w t g hg ψ
  have hTO : Sec5.Prop513Schedule.TimeOrdered 0 (historyProgram c r l) := Gm.timeOrdered_of_pairwise_lt hord
  have hβ : (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).β = GW2Wm.schedWordMapX c.κ (cw Ω c r)
      (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1) (length_historyProgram c r l)
      (candAngle c r l a) := by
    rw [schedChoiceLinesX_β Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a]
    rfl
  have hσa : (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).σa =
      specOffset c.κ + candAngle c r l a * chiC c.κ := by
    show (schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) Ω c r l a).σa = _
    unfold schedChoiceLinesX
    split_ifs
    rfl
  have hkc : (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).kc = chiC c.κ := by
    show (schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) Ω c r l a).kc = _
    unfold schedChoiceLinesX
    split_ifs
    rfl
  have hu₀ := schedChoiceLinesX_u₀ Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a hTO
  have hβm : Measurable (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).β := by
    rw [schedChoiceLinesX_β Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a]
    exact (Wire.T14Cur.hword_baseWm cw Ω c r l hTO h a).1
  have hE₀ : MeasurableSet (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).E₀ := by
    rw [schedChoiceLinesX_E₀ Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a]
    exact Wire.T14Cur.hE₀_baseWm cw Ω c r l hTO h a
  have hbase : ClaimAllX c r (cw Ω c r) [] := hroot.elim
    (fun hr0 => claimAllX_nil_root0 Wire.T14Asm7.h12 Wire.T14Asm7.h13 c r hr0 h.2 (hcw Ω c r))
    (fun hx => hnil Ω c r h hx)
  have hall := claimAtX_all_of_nil Wire.T14Asm7.h12 Wire.T14Asm7.h13 Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀ c r hroot
    h.2 (cw Ω c r) hbase l hord
  exact meanX_histX Wire.T14Asm7.h12 Wire.T14Asm7.h13 Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀ c r hroot h.2 l hord hall a
    (schedGTX_spec Wire.T14Asm7.h13 c r l a) ((ver Ω c r l a).isA h.1 n) ((ver Ω c r l a).fin n)
    (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a) hu₀ hkc hβm hE₀ hβ hσa w (hVd Ω c r l hord h a n w) t g hg ψ

end InteractingSLE.Theorem14.GW2Rd
