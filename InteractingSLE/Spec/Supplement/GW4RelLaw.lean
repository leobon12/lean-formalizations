/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4RelMatch
import InteractingSLE.Spec.Supplement.GW4RelClock
import InteractingSLE.Spec.Supplement.GW4R51
import InteractingSLE.Spec.Supplement.GW4KernelLife
import InteractingSLE.Spec.Supplement.GW4Chain
import InteractingSLE.Spec.Supplement.GB10Proof
import InteractingSLE.Spec.Restart.FlowCodeMain
import InteractingSLE.Spec.Sec7.Lemma78MeanWordMeas

/-!
# Theorem GW4's component (Det) from the relative stopped coupling

Packet PROVE-GW4-RELLAW. **`gw4RelativeLawRegStatement_of_stopCoupling`** proves Theorem 1.4's leaf
`GW4Reg.GW4RelativeLawRegStatement` ("the counterflow of the component field coincides with the counterflow's
traversal of the component"; Theorem GW4, pp. 638–639) from

* `GW4RelStopCouplingStatement` (the relative stopped coupling: Astra's follow-up 3, Q3, for the GW4 component);
* Aux. lemma 54 (`StoppedExtend.StoppedHullExtendStatement.{0}` at `16/κ > 4`, already a Theorem 1.4 leaf);
* `GW4Reg.GW4BarrierPocketRegStatement` (the walks' barrier and pocket shape) and `GW4R51.GW3WordBoundRegStatement`
  (GW3's word bounds), both derived in the Theorem 1.4 wiring;
* Theorems 1.2–1.3 at universes `u` and `0` (R48: GW4 serves Theorem 1.4 only).

Proof, for `P`-almost every `ω₀`, a component `C`, a chart `c` and the conditional law `ν`:
1. the component field `h_C` read in the inverted chart is a GFF with the data of a sorted word `c₀` of its
   counterflow data (`isGFFWithBoundaryData_invField_word`), so the field-determined driver `W_C = cfDrv(h_C)` of
   Theorem 1.2 is a centred counterflow of `h_C` (`BRLeaf.isCenteredCounterflowDriver_cfDrv`) with infinite lifetime
   (GW3's word bounds and integrated nonexplosion, `GW4.ae_lifetime_eq_top_of_counterflowWord`);
2. for every exhausting version `(R m, V m)` of the relative stopped coupling, `W_C = R m` before `V m`
   (`ae_cfDrv_eq_of_stopCoupling`: Aux. 54, the canonical driver code, Theorem 1.2);
3. pathwise: the relative endpoint is infinity (`exists_far_relHullFam`, from the barrier and the pocket coordinate),
   so the stops exhaust `[0, ∞)` and every hull of `W_C` is a relative hull (`exists_clock_of_versions`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4Rel

open GW4Traverse Supp8.GB6.RelDrv Restart Restart.StoppedExtend Sec7.StripSysField

/-- **The ambient counterflow's trace, transience and GB10** (`P`-almost surely): continuous driver from `0` with a
generating trace on `[0, ∞]` that tends to `∞` and has no time interval in a compact simple arc. -/
theorem ae_trace_transient_noSimpleArc (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) :
    ∀ᵐ ω ∂P, Continuous (fun t => W' t ω) ∧ W' 0 ω = 0 ∧ ∃ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W' t ω) ⊤ γ ∧ Tendsto (fun t => ‖γ t‖) atTop atTop ∧
        GB10.NoSimpleArcInterval γ ⊤ := by
  obtain ⟨b', J', h', -, -, hfl⟩ := id hcf
  obtain ⟨h'', 𝓕, VL, VR, B, -, hcoup⟩ := hfl
  have hG := GB10.gb10Statement (16 / κ) (GW4Ident.four_lt_sixteen_div hκ hκ4) _ _ _ _
    (Theorem15.isOrderedForceWord_flowLine b' J' 0) P 𝓕 W' VL VR B ζ' hcoup.1
  filter_upwards [hG, ae_trace_of_isCenteredCounterflowDriver h13 hκ hcf hζ', hζ'] with ω hGω htrω hζω
  obtain ⟨hc, h0, γ, hγ, hγt⟩ := htrω
  rw [hζω] at hGω
  exact ⟨hc, h0, γ, hγ, hγt, hGω γ hγ⟩

/-- **The relative stopped match** (the common consequence of the two forms of the remaining input,
`GW4RelStopCouplingStatement` and `GW4RelSafe.GW4RelSafeLawStatement`). Binders of `GW4RelStopCouplingStatement`; for
every sorted word `c₀` of the counterflow data and every canonical driver code `F` at `16/κ`, there are exhausting
measurable versions `(R m, V m)` of the relative traversal such that `ν`-almost surely each `R m` is the code of
`(c₀, h_C)` (inverted) at the dyadic times before `V m`. -/
def GW4RelStopMatchStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ (c : Chart) (hC : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (bC : ℝ → ℝ) (jumpsC : Finset ℝ),
          IsComponentChart R L C c →
          (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (hC ω)) →
          IsPiecewiseConstantBoundaryData bC jumpsC →
          IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
            (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC →
          IsGFFWithBoundaryData ν hC bC jumpsC →
          ∀ c₀ : BoundaryWord, c₀.IsSorted → c₀.jumps = counterflowJumps jumpsC →
            (∀ y ∉ c₀.jumps, c₀.fn y = counterflowData κ bC y) →
          ∀ F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞,
            IsCanonicalDriverCode (16 / κ) 0 F →
          ∃ (Rv : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
            (∀ m, IsGW4RelVersion ν W' c C (Rv m) (V m)) ∧
            (∀ᵐ ω ∂ν, ∀ t : ℝ≥0, Bornology.IsBounded (relHullFam c C (fun u => W' u ω) t) →
              ∃ m, ∃ s : ℝ≥0, (s : ℝ≥0∞) < V m ω ∧
                fwdHull (fun r : ℝ => Rv m r.toNNReal ω) s = relHullFam c C (fun u => W' u ω) t) ∧
            ∀ m, ∀ᵐ ω ∂ν, IsStopDrvMatch (F (c₀, invField κ (hC ω))) (fun t => Rv m t ω) (V m ω)

/-- **The relative stopped coupling gives the relative stopped match** (Aux. lemma 54 and the canonical driver code,
`ae_isStopDrvMatch_of_relCoupling`). -/
theorem gw4RelStopMatchStatement_of_stopCoupling
    (hext : ∀ k : ℝ, 4 < k → StoppedHullExtendStatement.{0} k) (hK : GW4RelStopCouplingStatement.{u}) :
    GW4RelStopMatchStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  have hext' : StoppedHullExtendStatement.{0} (16 / κ) :=
    hext (16 / κ) (GW4Ident.four_lt_sixteen_div hκ hκ4)
  filter_upwards [hK κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hKω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀ F hF
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  obtain ⟨Rv, V, hver, hexh, hcpl⟩ := hKω C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
  refine ⟨Rv, V, hver, hexh, fun m => ?_⟩
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕, VL, VR, B, hSC⟩ := hcpl m
  exact ae_isStopDrvMatch_of_relCoupling hext' hF c₀ ((measurable_invField κ).comp hgff.1) (hver m).1
    (hver m).2.1 (hver m).2.2.1 (hver m).2.2.2.1 hSC

/-- **Theorem GW4's component (Det) from the relative stopped match** (conditional helper with a distinct name):
`GW4Reg.GW4RelativeLawRegStatement` from `GW4RelStopMatchStatement`, the walks' barrier with its pocket shape, GW3's
word bounds and Theorems 1.2–1.3. -/
theorem gw4RelativeLawRegStatement_of_stopMatch (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hB : GW4Reg.GW4BarrierPocketRegStatement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u}) (hM : GW4RelStopMatchStatement.{u}) :
    GW4Reg.GW4RelativeLawRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  have hk : 0 < 16 / κ := sixteen_div_pos hκ
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  obtain ⟨F, hF⟩ := canonicalDriverCodeStatement_of_param h12p₀ h13₀ (16 / κ) 0 hk
  have hamb := ae_ae_condExpKernel
    (m := pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length)
    (ae_trace_transient_noSimpleArc h13 hκ hκ4 hcf hζ')
  filter_upwards [hamb, hB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hM κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hWB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hambω hBω hMω hWBω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  -- the word of the counterflow data and the inverted component field
  obtain ⟨c₀, hc₀m, hc₀J, hc₀⟩ :=
    BoundaryWord.exists_fn_eq_strictMonoOn (isPiecewiseConstant_counterflowData κ hpc)
  have hc₀s : c₀.IsSorted := fun i j hij hj =>
    hc₀m.monotoneOn (show i < c₀.1 from lt_of_le_of_lt hij hj) (show j < c₀.1 from hj) hij
  have hc₀' : ∀ y ∉ c₀.jumps, c₀.fn y = counterflowData κ bC y := by
    rw [hc₀J]
    exact hc₀
  have hX := isGFFWithBoundaryData_invField_word hκ hpc hgff hc₀J hc₀'
  -- the field-determined centred counterflow, with infinite lifetime
  have hcd := BRLeaf.isCenteredCounterflowDriver_cfDrv h12p h13 hκ hk hgff.1 hX
  obtain ⟨b', J', h', hb', htr', hfl'⟩ := id hcd
  obtain ⟨hwL, hwR⟩ := hWBω C hCm c hC bC jumpsC hch htr hpc hbd hgff b' J' h' _ _ hb' htr' hfl'
  have hlife := GW4.ae_lifetime_eq_top_of_counterflowWord hfl' hwL hwR
  -- the exhausting versions and the stopped matches
  obtain ⟨Rv, V, hver, hexh, hcm⟩ := hMω C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀' F hF
  have hmatch : ∀ m, ∀ᵐ ω ∂ν, V m ω ≤ (BRLeaf.cfDrv h12p hk c₀ (invField κ (hC ω))).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < V m ω → (BRLeaf.cfDrv h12p hk c₀ (invField κ (hC ω))).1 t = Rv m t ω :=
    fun m => ae_cfDrv_eq_of_match h12p h13 hk hF hc₀s hX (hver m).2.1 (hcm m)
  have hmatch' := ae_all_iff.2 hmatch
  have hverae := ae_all_iff.2 fun m => (hver m).2.2.2.2
  obtain ⟨αR, αL, hαR, hαL, hP, hbar⟩ := hBω
  have hCm' : C ∈ betweenComponents (range αR) (range αL) := by rw [hαR, hαL]; exact hCm
  have hch' : IsComponentChart (range αR) (range αL) C c := by rw [hαR, hαL]; exact hch
  refine ⟨_, _, hcd, hlife, ?_⟩
  filter_upwards [hambω, hbar, hlife, hmatch', hverae, hexh] with ω hambω' hbarω hlifeω hmω hvω hexω
  obtain ⟨hW'c, hW'0, γ, hγ, hγt, hno⟩ := hambω'
  -- the field-determined driver is continuous on `[0, ∞)`
  have hcfc : Continuous fun t => (BRLeaf.cfDrv h12p hk c₀ (invField κ (hC ω))).1 t := by
    have hl : (BRLeaf.cfDrv h12p hk c₀ (invField κ (hC ω))).2 = ⊤ := hlifeω
    have h1 : ContinuousOn (BRLeaf.cfDrv h12p hk c₀ (invField κ (hC ω))).1
        {t | (t : ℝ≥0∞) < (BRLeaf.cfDrv h12p hk c₀ (invField κ (hC ω))).2} :=
      (Exist.Staged.drvOf_regular _).1
    rw [hl] at h1
    simp only [ENNReal.coe_lt_top, ofPred_true] at h1
    exact continuousOn_univ.1 h1
  exact exists_clock_of_versions hcfc (fun m t ht => (hmω m).2 t ht) hvω hexω
    (exists_far_relHullFam hW'c hW'0 hγ hγt hno (hbarω γ hγ) hP hCm' hch')


/-- **Theorem GW4's component (Det) from the relative stopped coupling** (conditional helper with a distinct name):
`GW4Reg.GW4RelativeLawRegStatement` from `GW4RelStopCouplingStatement`, Aux. lemma 54, the walks' barrier with its
pocket shape, GW3's word bounds and Theorems 1.2–1.3. -/
theorem gw4RelativeLawRegStatement_of_stopCoupling (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hext : ∀ k : ℝ, 4 < k → StoppedHullExtendStatement.{0} k)
    (hB : GW4Reg.GW4BarrierPocketRegStatement.{u}) (hWB : GW4R51.GW3WordBoundRegStatement.{u})
    (hK : GW4RelStopCouplingStatement.{u}) : GW4Reg.GW4RelativeLawRegStatement.{u} :=
  gw4RelativeLawRegStatement_of_stopMatch h12 h13 h12₀ h13₀ hB hWB
    (gw4RelStopMatchStatement_of_stopCoupling hext hK)

end GW4Rel

end Theorem14

end InteractingSLE
