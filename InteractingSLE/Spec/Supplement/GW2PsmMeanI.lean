/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmPairI
import InteractingSLE.Spec.Supplement.GW2PsmMean

/-!
# GW2's open lines: the per-stage mean at ROOTX's corrected instance (root `0`), from Claim(k)

Packet PROVE-GW2-STAGEMEAN, R121 round. **`meanX_inst`**: `stageMeanAtX` for every local-set mean of the corrected
instance's union `B t`, at every stage time `t`, from

* `hclaim`: the stage-start pairing (Claim(k));
* `hlife`, `hcapb`: below the version's cap the candidate is alive and runs before its cap (the death-capped and
  cap-bounded readings of the version);
* `hfar`: the far-right height of the word map.

At `t = 0` the pairing is `hclaim`; for `0 < t` below the cap it is `pair_inst`; beyond the cap the statement is
vacuous (`hcapb`). Then `StageInst.meanX_of_pair` with the explicit stage mean.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Psm

open Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Rd GW2Rz GW2Sde Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop
  Restart.DomainMarkov MartChar.RealFlow GW2JointKernel Sec7.PocketTraversal Supp8.RelSafe

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The per-stage mean at ROOTX's corrected instance** (root `0`, one word type, every stage time), from Claim(k). -/
theorem meanX_inst (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hr0 : rootPt r.1 = 0) (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) (hs0 : 0 < c.s)
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
    (hclaim : ∀ g₀ : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean ((GW2Rv.schedInstSX c r l a GT hA ch).B 0) (centredField c.h ch.u₀) c.P g₀ →
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
        ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
          ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
        (0 : ℝ≥0∞) < (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω →
        tsupport φ ⊆ H \ (GW2Rv.schedInstSX c r l a GT hA ch).B 0 ω →
        g₀ ω φ = ∫ z, stgMeanR c.κ (gb6Rec c.s c.W c.ζ ω) (fun q => R q ω)
          (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω) 0
          (bheProc c.κ (typedRhoL w) (typedRhoR w) ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
            (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (ch.β y.1)) i t
              ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω,
                relVar (GW2Rv.schedInstSX c r l a GT hA ch).Hr
                  ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
                  ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) ω))
            (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (ch.β y.1)) j t
              ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω,
                relVar (GW2Rv.schedInstSX c r l a GT hA ch).Hr
                  ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
                  ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) ω)) ω 0)
          ch.u₀ ch.σa z * φ z)
    (g : Ω → DistOn upperHalfPlaneOpens)
    (hg : IsLocalSetMean ((GW2Rv.schedInstSX c r l a GT hA ch).B t) (centredField c.h ch.u₀) c.P g)
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂c.P, stageMeanAtX (GW2Rv.schedInstSX c r l a GT hA ch) c r l (rootPt r.1) w t ψ ω (g ω) := by
  classical
  have hx : (0 : ℝ) ≤ rootPt r.1 := by rw [hr0]
  have hv := hA.1.1
  have hB : ∀ q : ℝ≥0, (GW2Rv.schedInstSX c r l a GT hA ch).B q = GW2Sdi.schedUnionS c r l a q := fun q =>
    funext fun ω => schedUnionSX_eq_schedUnionS c r l a hr0 q ω
  -- beyond the cap the statement is vacuous
  by_cases htc : t < candidateCap c r a
  swap
  · filter_upwards [hcapb] with ω h hlive hlt
    exact absurd (h hlive hlt) htc
  set I := GW2Rv.schedInstSX c r l a GT hA ch with hIdef
  set a₀ : Ω → ℝ≥0 := fun ω => stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω
    with ha₀
  set cs : Ω → Chart := fun ω => stgChart (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) (fun q => R q ω) (a₀ ω)
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
  set Mf : Ω → ℂ → ℝ := fun ω => stgMeanR c.κ (gb6Rec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) (Q ω) (U ω) ch.u₀
    ch.σa with hMf
  set M : Ω → ℂ → ℝ := fun ω => if H \ I.B t ω =
      (cs ω).2.1 '' (H \ fwdHull (Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω))) (Q ω)) then Mf ω else 0 with hM
  have hMh : ∀ ω, InnerProductSpace.HarmonicOnNhd (M ω) (H \ I.B t ω) := by
    intro ω
    by_cases hc : H \ I.B t ω = (cs ω).2.1 '' (H \ fwdHull (Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω))) (Q ω))
    · simp only [hM, hc, ↓reduceIte]
      exact harmonicOnNhd_stgMeanR c.κ _ (hv.2.1 ω) (hv.2.2.1 ω) (a₀ ω) (Q ω).coe_nonneg (hUh ω) hu₀.1 ch.σa
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
    filter_upwards [ae_shape_root0 c r l a hr0 hs0 hGT.1 hv, hGT.2.2, hEgood, c.hζ] with ω hshω hGTω hEω hζ
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
    have hiv := stgChart_inv_image (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) (hv.2.1 ω) (hv.2.2.1 ω) (a₀ ω)
      (Q ω)
    rw [hsum] at hiv
    refine ⟨by rw [hB t, hsh, ← hiv], ?_⟩
    have hb : baseRead (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) = 0 := by
      rw [hr0]
      exact baseRead_zero_cfRec c.s c.W c.ζ ω hζ
    show stgChart (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) (fun q => R q ω) (a₀ ω) = _
    rw [relChartX_of_baseRead_zero hb]
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
      filter_upwards [pair_inst h12 h13 h12₀ h13₀ c r l a hr0 hord hs0 hGT hA hV ch hu₀ hkc hβm hE₀ w t htpos htc
        hlife hfar hclaim g hg φ, hsh] with ω h1 h2 hωG hsupp
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
      isConformal_stgChart (RelSafeS.isConformal_relChart _) (hv.2.1 ω) (hv.2.2.1 ω) (a₀ ω)
    have hfi : (cs ω).1 ((cs ω).2.1 z) = z := hconf.2.2 z hz.1
    unfold stgMeanR
    rw [hfi]
    show _ + ch.u₀ _ + ch.σa + ch.kc * _ = _
    rw [hkc]
    have e1 : (cs ω).2.2 ((cs ω).2.1 z) =
        (stgChart (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) (fun q => R q ω) (a₀ ω)).2.2 ((cs ω).2.1 z) := rfl
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
    (fun ω => by rw [hB t]; exact GW2Sdi.schedUnionS_subset_isOpen c r l a t ω)
    (Eventually.of_forall fun ω h1 h2 => ⟨h1, h2⟩)
    (by filter_upwards [hsh] with ω h h1 h2; rw [(h h1 h2).2]; exact (h h1 h2).1) hMh g hg.2.1 hpair hread ψ

end InteractingSLE.Theorem14.GW2Psm
