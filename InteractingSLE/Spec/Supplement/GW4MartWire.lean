/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4MartAssemble
import InteractingSLE.Spec.Supplement.GW4SafeRConnMean
import InteractingSLE.Spec.Supplement.GW4CLocWire

/-!
# GW4's protected martingales, part 8: the global statements

Packet PROVE-GW4-MART. The protected-martingale half of `GW4Fix.GW4ComponentPhaseInputsStatement` is proved in
`exists_componentPhaseBefore` for every **announced** version (`IsGW4RelVersionA`) of the relative traversal; its
remaining input is the boundary representation with a lattice phase constant in time, which belongs to
PROVE-GW4-SAFER's half:

* **`GW4ComponentRepStatement`** (named input, SAFER's half): for every component, path-rule version and locality
  witnesses, the boundary representation `ComponentPhaseRepresentation` holds for some phase that is constant in
  time and lattice-valued (Astra's follow-up 3 (Q3.6): "one common discrepancy `δ_u ∈ 2πχℤ`", "`δ_u` is constant on
  the connected positive lifetime");
* `GW4ComponentRepAStatement` (the same for announced versions only; implied, `gw4ComponentRepAStatement_of_rep`) and
  `GW4ComponentRepDStatement` (the form of SAFER's interface: a phase process, almost surely lattice-valued and
  constant at positive relative times before `V`; it implies the constant form, `gw4ComponentRepStatement_of_repD`);
* **`gw4ComponentBeforeInputsAStatement_of_rep`**: SAFER's `GW4ComponentBeforeInputsStatement` for announced versions;
* `gw4ComponentMeanAStatement_of_before`, `gw4ComponentLinesAStatement_of_mean`, `gw4RelSafeAStatement_of_lines`,
  `gw4RelStopMatchStatement_of_relSafeA`: the zero-phase mean (Aux. 122), the component lines, the relative safe law
  and the relative stopped match for announced versions — the only versions the stopped match uses;
* **`gw4RelativeLawRegStatement_of_repA`** (and `gw4RelativeLawRegStatement_of_rep`): Theorem GW4's component law
  `GW4Reg.GW4RelativeLawRegStatement` from Theorems 1.2–1.3, the walks' barrier, GW3's word bounds and
  `GW4ComponentRepAStatement` alone (component locality is PROVE-GW4-CLOC's theorem).

**Why announced versions.** `ComponentPhaseBefore` asks for local martingales before `s(z) ∧ V` in the sense of
`MartChar.IsLocalMartingaleBefore`, whose localizing times may reach `V`. The line kernels and the representation
are available only strictly before `V` (on `{lineClock t < V}`), so the martingale property at `V` itself needs `V`
to be announced by stopping times strictly before it. A path-rule version (`IsGW4RelVersionR`) carries no
announcing sequence; the announced versions (`IsGW4RelVersionA`) do, and they exhaust the traversal
(`GW4RelVersionAStatement`), which is all the downstream relative stopped match consumes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW4Fix.Mart

open Restart Sec7.StripSysField GW4Rel GW4Traverse Supp8.Q3Stop Supp8.GB6.RelDrv Supp8.RelSafe Exist.StagedLaw
  Sec7.PhaseClause Sec7.PhaseSel

/-! ### The named input of the representation half -/

/-- **Named input (PROVE-GW4-SAFER's half): the boundary representation with a lattice phase constant in time.**
For every actual GW4 component, path-rule version and locality witnesses, the actual local-set means have the
finite-word boundary representation `ComponentPhaseRepresentation` for a phase `c` that does not depend on time and
takes values in `2πχℤ` (`phaseStep`). Its value at relative time `0` is irrelevant (the seeds coincide). -/
def GW4ComponentRepStatement : Prop :=
  GW4ComponentProperty.{u} fun {Ω} _ k c₀ F ν X Wd GT R V hWm =>
    ∀ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
      ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B →
      ∃ c : Ω → ℝ, (∀ ω, ∃ j : ℤ, c ω = j * phaseStep k) ∧
        ComponentPhaseRepresentation k c₀ F ν X Wd GT R V u₀ B (fun _ ω => c ω)

/-- The representation input for announced versions only (implied by `GW4ComponentRepStatement`). -/
def GW4ComponentRepAStatement : Prop :=
  GW4ComponentProperty.{u} fun {Ω} _ k c₀ F ν X Wd GT R V hWm =>
    IsGW4RelVersionA ν Wd F.c F.C R V →
    ∀ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
      ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B →
      ∃ c : Ω → ℝ, (∀ ω, ∃ j : ℤ, c ω = j * phaseStep k) ∧
        ComponentPhaseRepresentation k c₀ F ν X Wd GT R V u₀ B (fun _ ω => c ω)

theorem gw4ComponentRepAStatement_of_rep (h : GW4ComponentRepStatement.{u}) : GW4ComponentRepAStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ hh0 hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [h κ hκ hκ4 b jumps hb P hh0 hh W' ζ' hcf hζ' E hE hreg] with ω₀ hω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver _
  exact hω C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver

/-- The representation input in the form of SAFER's interface: a phase **process** `d`, almost surely constant
and lattice-valued at the positive relative times before the lifetime. -/
def GW4ComponentRepDStatement : Prop :=
  GW4ComponentProperty.{u} fun {Ω} _ k c₀ F ν X Wd GT R V hWm =>
    ∀ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
      ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B →
      ∃ d : ℝ≥0 → Ω → ℝ, (∀ᵐ ω ∂ν, ∃ c : ℝ, (∃ j : ℤ, c = j * phaseStep k) ∧
          ∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < V ω → d q ω = c) ∧
        ComponentPhaseRepresentation k c₀ F ν X Wd GT R V u₀ B d

/-- **The phase-process form of the representation input gives the constant form.** -/
theorem gw4ComponentRepStatement_of_repD (h : GW4ComponentRepDStatement.{u}) : GW4ComponentRepStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ hh0 hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [h κ hκ hκ4 b jumps hb P hh0 hh W' ζ' hcf hζ' E hE hreg] with ω₀ hω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver u₀ ℋ B hloc
  obtain ⟨d, hdc, hrep⟩ := hω C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver u₀ ℋ B hloc
  classical
  set c' : Ω → ℝ := fun ω => if hc : ∃ c : ℝ, (∃ j : ℤ, c = j * phaseStep (16 / κ)) ∧
      ∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < V ω → d q ω = c then hc.choose else 0 with hc'
  refine ⟨c', fun ω => ?_, ?_⟩
  · by_cases hc : ∃ c : ℝ, (∃ j : ℤ, c = j * phaseStep (16 / κ)) ∧
        ∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < V ω → d q ω = c
    · simp only [hc', hc, ↓reduceDIte]
      exact hc.choose_spec.1
    · simp only [hc', hc, ↓reduceDIte]
      exact ⟨0, by simp⟩
  · intro t g hg
    filter_upwards [hrep t g hg, hdc] with ω h1 h2 hlt
    obtain ⟨w, G, hw, hpair, hG, hm⟩ := h1 hlt
    refine ⟨w, G, hw, hpair, ?_, hm⟩
    have hlt' : ((lineClock F Wd GT V t ω).toNNReal : ℝ≥0∞) < V ω := by
      rw [ENNReal.coe_toNNReal (ne_top_of_lt hlt)]
      exact hlt
    by_cases hpos : 0 < (lineClock F Wd GT V t ω).toNNReal
    · have he : d (lineClock F Wd GT V t ω).toNNReal ω = c' ω := by
        simp only [hc', h2, ↓reduceDIte]
        exact h2.choose_spec.2 _ hpos hlt'
      rw [← he]
      exact hG
    · have hq : (lineClock F Wd GT V t ω).toNNReal = 0 := le_antisymm (not_lt.1 hpos) bot_le
      rw [hq] at hG ⊢
      have hs := component_seeds_zero (16 / κ) c₀ (fun ω => invField κ (hC ω)) Rv V ω
      have heq := phaseData_eq_of_seeds_eq (k := 16 / κ) (typedRhoL (wordType (16 / κ) c₀))
        (typedRhoR (wordType (16 / κ) c₀))
        (vL := fun i => componentVL (16 / κ) c₀ (fun ω => invField κ (hC ω)) Rv V i 0 ω - Rv 0 ω)
        (vR := fun j => componentVR (16 / κ) c₀ (fun ω => invField κ (hC ω)) Rv V j 0 ω - Rv 0 ω)
        (congrArg (· - Rv 0 ω) (hs.1.trans hs.2.symm)) ((fun _ ω => c' ω) 0 ω) (d 0 ω)
      convert hG using 1

/-! ### The protected-martingale half -/

/-- **SAFER's `GW4ComponentBeforeInputsStatement` for announced versions.** -/
def GW4ComponentBeforeInputsAStatement : Prop :=
  GW4ComponentProperty.{u} fun {Ω} _ k c₀ F ν X Wd GT R V hWm =>
    IsGW4RelVersionA ν Wd F.c F.C R V →
    ∀ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
      ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B →
      ∃ h : ComponentPhaseBefore k c₀ ν X R V,
        ComponentPhaseRepresentation k c₀ F ν X Wd GT R V u₀ B h.phase

/-- **The protected-martingale half of `GW4ComponentPhaseInputsStatement`**, for announced versions, from the
representation half. -/
theorem gw4ComponentBeforeInputsAStatement_of_rep (hR : GW4ComponentRepAStatement.{u}) :
    GW4ComponentBeforeInputsAStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver hverA u₀ ℋ B hloc
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  have hX : IsGFFWithBoundaryData ν (fun ω => invField κ (hC ω)) c₀.fn c₀.jumps :=
    isGFFWithBoundaryData_invField_word hκ hpc hgff hc₀J hc₀
  obtain ⟨c', hlat, hrep⟩ := hω C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver hverA u₀ ℋ B hloc
  exact exists_componentPhaseBefore (by positivity) hX hF hGT hGTm hGTae hverA hloc hlat hrep

/-! ### The zero-phase mean, the component lines and the relative law for announced versions -/

/-- The shared zero-phase mean target for announced versions. -/
def GW4ComponentMeanAStatement : Prop :=
  GW4ComponentProperty.{u} fun {Ω} _ k c₀ F ν X Wd GT R V hWm =>
    IsGW4RelVersionA ν Wd F.c F.C R V →
    ∀ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
      ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B →
      ComponentLineMean k c₀ F ν X Wd GT R V u₀ B

/-- **The zero-phase finite-word mean for announced versions** (Aux. lemma 122 through SAFER's
`componentLineMean_of_phaseInputs`, with the caps of `ComponentPhaseBefore.toCaps`, the upper seed bounds of
`gw4ComponentSeedUpper_of_theorem13` and the lower ones of GW3's word bound; the proof of
`gw4ComponentMeanStatement_of_phaseInputs` and `gw4ComponentPhaseInputsStatement_of_before`). -/
theorem gw4ComponentMeanAStatement_of_before
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hWB : GW4R51.GW3WordBoundRegStatement.{u})
    (hI : GW4ComponentBeforeInputsAStatement.{u}) : GW4ComponentMeanAStatement.{u} := by
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hI κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hWB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    gw4ComponentSeedUpper_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg]
    with ω₀ hi hBound hu
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver hverA u₀ ℋ B hloc
  obtain ⟨hbefore, hrep⟩ := hi C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver hverA u₀ ℋ B hloc
  obtain ⟨huL, huR⟩ := hu C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver
  have hk : 4 < 16 / κ := (lt_div_iff₀ hκ).2 (by linarith only [hκ4])
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  let X := fun ω => invField κ (hC ω)
  have hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps :=
    isGFFWithBoundaryData_invField_word hκ hpc hgff hc₀J hc₀
  have hk0 : 0 < 16 / κ := by positivity
  have hcan := isFlowLineDriver_cfDrv_word h12p h13 hk0 c₀ hX
  obtain ⟨hsL, hsR⟩ := hBound C hCm c hC bC jumpsC hch htr hpc hbd hgff
    c₀.fn c₀.jumps X (fun t ω => (BRLeaf.cfDrv h12p hk0 c₀ (X ω)).1 t)
    (fun ω => (BRLeaf.cfDrv h12p hk0 c₀ (X ω)).2) c₀.isPiecewiseConstantBoundaryData
    (fun ω => isChartTransport_invField hκ (hC ω)) hcan
  have htL : ∀ i, typedRhoL (wordType (16 / κ) c₀) i =
      flowLineRhoL (16 / κ) c₀.fn c₀.jumps 0 0 i := fun i => padFL_snd_fst_fin _ _ _ _ i
  have htR : ∀ i, typedRhoR (wordType (16 / κ) c₀) i =
      flowLineRhoR (16 / κ) c₀.fn c₀.jumps 0 0 i := fun i => padFL_snd_snd_fin _ _ _ _ i
  have hR0 : ∀ ω, Rv 0 ω = 0 := hver.1.1.2.2.1
  have hRc : ∀ ω, Continuous (Rv · ω) := hver.1.1.2.1
  refine componentLineMean_of_phaseInputs hk hloc ?_ ?_ hR0 hRc (hbefore.toCaps hR0 hRc huL huR) hrep
  · rw [htL]
    exact seed_lower_of_partialSums hsL
  · rw [htR]
    exact seed_lower_of_partialSums hsR

/-- The component lines for announced versions. -/
def GW4ComponentLinesAStatement : Prop :=
  GW4ComponentProperty.{u} fun {_Ω} _ k c₀ F ν X Wd GT R V hWm =>
    IsGW4RelVersionA ν Wd F.c F.C R V → HasComponentLines k c₀ F ν X Wd GT R V hWm

/-- **The component lines for announced versions** from component locality and the zero-phase mean. -/
theorem gw4ComponentLinesAStatement_of_mean (hL : GW4ComponentLocalityStatement.{u})
    (hM : GW4ComponentMeanAStatement.{u}) : GW4ComponentLinesAStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hM κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hl hm
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver hverA
  obtain ⟨u₀, ℋ, B, hloc⟩ := hl C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver
  exact hasComponentLines_of_locality_mean hloc
    (hm C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
      F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver hverA u₀ ℋ B hloc)

/-- **GW4's relative safe law for announced versions** (`GW4RelSafeRStatement` with `IsGW4RelVersionA`). -/
def GW4RelSafeAStatement : Prop :=
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
          ∀ (Rv : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞), IsGW4RelVersionA ν W' c C Rv V →
            HasRelSafe (16 / κ) (wordType (16 / κ) c₀) (fun _ => c₀) univ
              (ν.map fun ω => (gw4Rec, relVar (fun ω => invField κ (hC ω)) Rv V ω))

/-- An announced version for the counterflow is one for an almost surely equal physical driver. -/
theorem isGW4RelVersionA_of_ae_eq {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {Wd W' : ℝ≥0 → Ω → ℝ}
    {c : Chart} {C : Set ℂ} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} (h : IsGW4RelVersionA ν W' c C R V)
    (hVW : ∀ᵐ ω ∂ν, ∀ t, Wd t ω = W' t ω) : IsGW4RelVersionA ν Wd c C R V :=
  ⟨(h.isGW4RelVersionR.of_ae_eq hVW).1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- **The relative safe law for announced versions from the component lines** (the proof of
`gw4RelSafeRStatement_of_componentLines`). -/
theorem gw4RelSafeAStatement_of_lines
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hB : GW4Reg.GW4BarrierPocketRegStatement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u})
    (hLines : GW4ComponentLinesAStatement.{u}) : GW4RelSafeAStatement.{u} := by
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [exists_frame h13 hB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hWB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hLines κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hFr hBound hLine
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀ Rv V hverA
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  let X := fun ω => invField κ (hC ω)
  have hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps :=
    isGFFWithBoundaryData_invField_word hκ hpc hgff hc₀J hc₀
  have hk : 0 < 16 / κ := by positivity
  have hcan := isFlowLineDriver_cfDrv_word h12p h13 hk c₀ hX
  obtain ⟨hsL, hsR⟩ := hBound C hCm c hC bC jumpsC hch htr hpc hbd hgff
    c₀.fn c₀.jumps X (fun t ω => (BRLeaf.cfDrv h12p hk c₀ (X ω)).1 t)
    (fun ω => (BRLeaf.cfDrv h12p hk c₀ (X ω)).2) c₀.isPiecewiseConstantBoundaryData
    (fun ω => isChartTransport_invField hκ (hC ω)) hcan
  obtain ⟨F, Wd, GT, hF, hFC, hFc, hGT, hWm, hGTm, hGTae, hVW⟩ := hFr C hCm c hch
  have hvdA : IsGW4RelVersionA ν Wd F.c F.C Rv V := by
    rw [hFC, hFc]
    exact isGW4RelVersionA_of_ae_eq hverA hVW
  have hvd : IsGW4RelVersionR ν Wd F.c F.C Rv V := hvdA.isGW4RelVersionR
  have hlocal := hLine C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hvd hvdA
  exact hasRelSafe_of_componentLines hX hF hGT hWm hGTm hGTae hvd hsL hsR hlocal

/-- **The relative stopped match from announced versions and their safe law** (the proof of
`gw4RelStopMatchStatement_of_relSafeR`, which uses the safe law only at announced versions). -/
theorem gw4RelStopMatchStatement_of_relSafeA (hV : GW4RelVersionAStatement.{u})
    (hS : GW4RelSafeAStatement.{u}) : GW4RelStopMatchStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hV κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hVω hSω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀ F hF
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  obtain ⟨Rv, V, hver, hexh⟩ := hVω C hCm c hch
  refine ⟨Rv, V, fun m => (hver m).1.1, hexh, fun m => ?_⟩
  have hSm := hSω C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀ (Rv m) (V m) (hver m)
  obtain ⟨hsv, hV0, ⟨ρ, hρm, hρ, hVρ⟩, ρs, hρsm, hρs, hρsfin, hρsmono, hann⟩ := hver m
  have hk : 0 < 16 / κ := sixteen_div_pos hκ
  have hm := ae_isStopDrvMatch_of_hasRelSafe (P := ν) hk hF (β := fun _ => c₀) measurable_const
    MeasurableSet.univ (wordType (16 / κ) c₀) (rec := fun _ => gw4Rec) measurable_const
    ((measurable_invField κ).comp hgff.1) hsv.1.1 hsv.1.2.1 hsv.1.2.2.1 hsv.1.2.2.2.1 hSm
    (hV0.mono fun ω h _ => h) (ρ := fun x => ρ x.2) (hρm.comp measurable_snd) (isPathRule_comp_snd hρ) hVρ
    (ρs := fun n x => ρs n x.2) (fun n => (hρsm n).comp measurable_snd) (fun n => isPathRule_comp_snd (hρs n))
    (fun n x => hρsfin n x.2) (fun x => hρsmono x.2) (hann.mono fun ω h _ => h.1) (hann.mono fun ω h _ => h.2)
  filter_upwards [hm] with ω hω using hω (mem_univ _) rfl

/-- **Theorem GW4's component law from the representation half alone**: `GW4Reg.GW4RelativeLawRegStatement` from
Theorems 1.2–1.3, the walks' barrier with its pocket shape, GW3's word bounds and the representation input for
announced versions `GW4ComponentRepAStatement` (component locality: `CLoc.gw4ComponentLocalityStatement`; the
protected martingales: `gw4ComponentBeforeInputsAStatement_of_rep`). -/
theorem gw4RelativeLawRegStatement_of_repA (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hB : GW4Reg.GW4BarrierPocketRegStatement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u}) (hRep : GW4ComponentRepAStatement.{u}) :
    GW4Reg.GW4RelativeLawRegStatement.{u} :=
  gw4RelativeLawRegStatement_of_stopMatch h12 h13 h12₀ h13₀ hB hWB
    (gw4RelStopMatchStatement_of_relSafeA (gw4RelVersionAStatement_of_coord h13 hB (gw4RelCoordStatement h13 hB))
      (gw4RelSafeAStatement_of_lines h12 h13 hB hWB
        (gw4ComponentLinesAStatement_of_mean (CLoc.gw4ComponentLocalityStatement h12 h13)
          (gw4ComponentMeanAStatement_of_before h12 h13 h13₀ hWB
            (gw4ComponentBeforeInputsAStatement_of_rep hRep)))))

/-- The same from the representation input for all path-rule versions. -/
theorem gw4RelativeLawRegStatement_of_rep (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hB : GW4Reg.GW4BarrierPocketRegStatement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u}) (hRep : GW4ComponentRepStatement.{u}) :
    GW4Reg.GW4RelativeLawRegStatement.{u} :=
  gw4RelativeLawRegStatement_of_repA h12 h13 h12₀ h13₀ hB hWB (gw4ComponentRepAStatement_of_rep hRep)

end InteractingSLE.Theorem14.GW4Fix.Mart
