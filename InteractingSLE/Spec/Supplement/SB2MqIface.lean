/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XbAE
import InteractingSLE.Spec.Supplement.SB2JtT
import InteractingSLE.Spec.Supplement.SB2XcIface
import InteractingSLE.Spec.Supplement.SB2XgIface
import InteractingSLE.Spec.Supplement.SB2MoPhys

/-!
# SB2(2)'s conditional half over LIFTSET's `RelDriverAtT` bundle (ruling R120, decisions D5, D7, D11)

Packet PROVE-SB2-LCMEAN, round 12. Ruling R120: the conditional half ranges over relative families carrying LIFTSET's
bundle of `Lk.RelDriverAt''` (D7), in LIFTSET's corrected form `Lk.RelDriverAtT` (round 16); the per-stage
correspondence is SB2LIFT's corrected `Mn.SB2LowerStageChainStatementR` (D11) over that bundle — in SB2LIFT's R2
variant (`Mn.StageChainAtR2`, `SB2XgIface`) — with the physical domain identity of `Mo.physRelChart` added (D5); a
relative stage of zero lifetime is a separate case (D11).

* `RelDataClause3`: the almost-sure bundle of LIFTSET's corrected `Lk.RelDriverAtT` (D7's `RelDriverAt''` off the
  infinite-start-piece event, `SB2JtT`) for one family `EL`;
* the re-typed conditional half `RelStageCond3` / **`SB2LowerRelStageCond3Statement`** and its kernel form
  `RelStageKernel3` / **`SB2LowerRelKernel3Statement`**
  (all launching stages; the relative stage of zero lifetime — the arc-start root, D11 — is a case of its proof);
* **`sb2LowerRelStageCond3Statement_of_kernel3`** (Theorems 1.2–1.3): the kernel form gives the conditional half;
* **`sb2LowerLaunchLiftStatement_of_relDriverT_cond3`**: SB2(2)'s combined target (R104a) from LIFTSET's corrected
  `SB2LowerRelDriverStatementT` and the re-typed conditional half (and Theorems 1.2–1.3);
* the per-stage correspondence over the bundle, with the physical domain identity and the zero clause:
  `StageChainAtP`, `StageChainAtZ` and **`SB2LowerStageChainStatementRP`** (PROVE-T14-SB2LIFT's, R120/D11).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mq

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk Mn
open LuM (trOf)

/-! ### The bundle -/

/-- **The almost-sure bundle of LIFTSET's corrected `Lk.RelDriverAtT`** for one relative family `EL` (ruling R120, D7;
LIFTSET's round-16 correction of `RelDriverAt''` at an infinite start piece, `SB2JtT`). -/
def RelDataClause3 (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ)
    (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
    ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
      ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀ tL γ →
        ∃ (ι : ℝ → ℝ) (o : ℕ),
          RayCorr b jumps (affData 1 m b') (affJumps 1 m J') (realMax (upperPrefix κ b jumps E u l k ω₀)) ι ∧
          RayChartLim c (realMax (upperPrefix κ b jumps E u l k ω₀)) m ι ∧
          (∀ s, ∀ x : ℝ, β₀ (tL + s) = x → realMax (upperPrefix κ b jumps E u l k ω₀) ≤ x) ∧
          (∀ s, ∀ x : ℝ, realMax (upperPrefix κ b jumps E u l k ω₀) < x → β₀ (tL + s) = x → γ s = ι x) ∧
          ((∃ N : ℕ, RunInputs'' κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
            (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
            (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o N ∧
          (ArcStart κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ tL o ∨
            PieceStartV κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
              (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
              (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o)) ∨
          (PieceStartV κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
              (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
              (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o ∧
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) o ω).2 = ⊤))

/-! ### The re-typed conditional half (R120) -/

section Cond

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → Drv) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ)
  (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens)

/-- **The conditional half at one launch, over families carrying the bundle of `Lk.RelDriverAtT`**
(`Lk.RelStageCond` with
`RelDataClause3` in place of the set-level tail lift; ruling R116). -/
def RelStageCond3 : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → Drv,
    (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
    RelDataClause3 κ b jumps P E u l k ω₀ c b' J' m EL →
    ∀ j, ∀ᵐ ω₁ ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ (c₁ : Chart) (θ : ℝ),
        (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω₁)
          (j + 1)).2.2.2.1 j = some (c₁, θ) →
        ∃ (b'' : ℝ → ℝ) (J'' : Finset ℝ) (h'' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b'' J'' ∧
          (∀ ω, IsChartTransport c₁ 1 0 (chiC κ) (affField m one_pos (h' ω)) (h'' ω)) ∧
          IsFlowLineDriver κ b'' J'' θ
            (condExpKernel (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
              (pastSigma κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j) ω₁)
            h'' (fun t ω => (EL j ω).1 t) (fun ω => (EL j ω).2)

/-- **The kernel form at one launch, over families carrying the bundle of `Lk.RelDriverAtT`**
(`Lcd.RelStageKernel` with
`RelDataClause3`): per stage, a conditional flow line given a σ-algebra containing the relative past. -/
def RelStageKernel3 : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → Drv,
    (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
    RelDataClause3 κ b jumps P E u l k ω₀ c b' J' m EL →
    ∀ j : ℕ, ∃ (𝒢' : {m' : MeasurableSpace Ω // m' ≤ mΩ}) (F' : Set Ω) (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ),
      pastSigma κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j ≤
        LocalSets.aeSigma 𝒢'.1 (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀) ∧
      (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
          (j + 1)).2.2.2.1 j ≠ none → ω ∈ F') ∧
      SB.IsCondFlowLineDriverOn κ (-(Real.pi / 2)) 𝒢'.1
        (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀) F'
        (fun ω => affField m one_pos (h' ω))
        (Cond.runChart κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j) bc jc
        (fun t ω => (EL j ω).1 t) (fun ω => (EL j ω).2)

end Cond

/-- **This packet's target (R120): SB2(2)'s conditional half over families carrying the bundle of
`Lk.RelDriverAtT`.** -/
def SB2LowerRelStageCond3Statement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → RelStageCond3 κ b jumps P E u l k ω₀ c b' J' h'

/-- **The kernel form of this packet's target (R120).** -/
def SB2LowerRelKernel3Statement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → RelStageKernel3 κ b jumps P E u l k ω₀ c b' J' h'

/-- **The kernel form gives the conditional half** (Theorems 1.2–1.3; LCOND's generic code match
`Lcd.ae_codeMatch_of_condFlowLine_data` and staged induction `Lcd.stageOK_all_of_codeMatch`). -/
theorem sb2LowerRelStageCond3Statement_of_kernel3 (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (hker : SB2LowerRelKernel3Statement.{u}) :
    SB2LowerRelStageCond3Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hker κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl j
  have hb'' := isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb'
  have hG'' := hG'.affine_finset (m := m) one_pos
  refine Lcd.stageOK_all_of_codeMatch h12p h13 hκ hb'' hG'' (-(Real.pi / 2))
    (fun _ _ _ _ hl => Lv.launch_angle_boundaryWalk hl) hELm hELr (fun j β Y hW => ?_) j
  obtain ⟨𝒢', F', bc, jc, hpast, hcov, hcfl⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl j
  exact Lcd.ae_codeMatch_of_condFlowLine_data h12p h13 hκ (-(Real.pi / 2)) hb'' hELm hELr 𝒢' hpast hcov hW hcfl

/-- **SB2(2)'s erasure identity for one relative walk from LIFTSET's corrected data with lifts and the re-typed
conditional half** (`Lk.sb2LowerRelWalkRangeStatement_of_relDriverT`, keeping the family). -/
theorem sb2LowerTailLiftExStatement_of_relDriverT_cond3 (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hD : SB2LowerRelDriverStatementT.{u}) (hcond : SB2LowerRelStageCond3Statement.{u}) :
    SB2LowerTailLiftExStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHead κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerAllowed h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRightHits h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerActualInputs h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft,
    sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hcond κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft]
    with ω₀ h₀ hH₀ hA₀ hX₀ hI₀ hC₀ hcond₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hELm, hELr, hae⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  have hst := hcond₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hae
  have hb'' := isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb'
  have hpast : ∀ j, Measurable (pastMap κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j) :=
    fun j => measurable_pastMap runMeasStatement hb'' (relLowerSpec b' J' m) (k := j) (fun i _ => hELm i)
      (fun i _ => hELr i) j le_rfl
  have hS : IsStagedHistory κ (affData 1 m b') (affJumps 1 m J')
      (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
      (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL := by
    refine ⟨hELm, fun j => ?_, fun j => Eventually.of_forall fun ω hne hpos c₀ hc₀ =>
      (hELr j ω).2.2.2 hne hpos c₀ hc₀, hst⟩
    rw [pastSigma_eq_comap]
    exact (hpast j).comap_le
  refine ⟨EL, hS, stagedPiecesRegular_of_regular h13 hκ hb'' hS hELr, ?_⟩
  filter_upwards [hae, hH₀ c θ hlaunch b' J' h' hb' hT' hG', hA₀ c θ hlaunch b' J' h' hb' hT' hG',
    hX₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG',
    hC₀ c θ hlaunch b' J' h' hb' hT' hG' m hm] with ω hω hHω hAω hXω hIω hCω
  intro β₀ hβ hβ0 hβr
  obtain ⟨tL, γ, hγ⟩ := hCω β₀ hβ hβ0 hβr
  obtain ⟨ι, o, hι, hlim, htail, hray, hS'⟩ := hω β₀ hβ hβ0 hβr tL γ hγ
  obtain ⟨hP₁, hW₁, hn⟩ := hIω
  have hhead := hHω β₀ hβ hβ0 hβr tL hγ.1
  have hC : CurveInputs κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) β₀ γ tL :=
    ⟨hβr, hβ.2.1, hγ.1, hγ.2.2.1, hhead, htail, hray⟩
  refine isTailLiftOf_iff.2 ⟨tL, γ, hγ, ?_⟩
  rcases hS' with ⟨N, hR, hS'⟩ | ⟨hP, htop⟩
  · have hDc : LiftCurveData β₀ γ tL (realMax (upperPrefix κ b jumps E u l k ω₀)) ι :=
      ⟨hβ.1, hβ.2.2.1, hγ.2.1.1, hγ.2.1.2.2.1, hγ.1, hγ.2.2.1,
        fun t ht him => hhead t ht _ (Complex.ext (by simp) (by simp [him])), hray, back_of_rayChartLim hγ hlim⟩
    exact range_eq_physSet_of_bundles'' hι hC hR (fun j => hELr j ω) hP₁ hW₁ (fun j => (hn j).1)
      (fun j => (hn j).2.1) (fun j hj => hAω j (by omega)) (fun j _ => hXω j) hβ hγ.2.1 hβ0 hDc hS'
  · exact range_eq_physSet_of_topV hι hC hP htop (hn o).2.1

/-- **SB2(2)'s combined target (R104a) from LIFTSET's corrected data with lifts and the re-typed conditional half**
(ruling R120; and Theorems 1.2–1.3). -/
theorem sb2LowerLaunchLiftStatement_of_relDriverT_cond3 (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hD : SB2LowerRelDriverStatementT.{u}) (hcond : SB2LowerRelStageCond3Statement.{u}) :
    Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_liftEx h12 h13 h12₀ h13₀
    (sb2LowerTailLiftExStatement_of_relDriverT_cond3 h12 h13 h12₀ h13₀ hD hcond)

/-! ### The per-stage correspondence over the bundle, with the physical domain identity (R120, D5/D11) -/

section Corr

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → Drv) (u : ℝ)
  (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ) (EL : ℕ → Ω → Drv)

/-- **The physical domain identity at one sample** (D5): at every relative stage of positive lifetime that launches
with chart `c₁`, the relative chart in physical coordinates `Mo.physRelChart c c₁ m` is a domain chart of the
complement of the fill of the retained union (the upper prefix with B's prefix before the matched stage). -/
def StageChainAtP (ω : Ω) : Prop :=
  ∀ (j : ℕ) (c₁ : Chart) (θ' : ℝ),
    (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
      (j + 1)).2.2.2.1 j = some (c₁, θ') →
    (EL j ω).2 ≠ 0 →
    IsDomainChart (H \ fillH (upperPrefix κ b jumps E u l k ω₀ ∪
        SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
          (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω))))
      (Mo.physRelChart c c₁ m)

/-- **Zero lifetime only at the root** (D11's consumer check, from SB2LIFT's (L1) "zero together"): every relative
stage after the root that launches has positive lifetime (its matched actual stage has, by the bundle's `nz₁`). -/
def StageChainAtZ (ω : Ω) : Prop :=
  ∀ (j : ℕ) (c₁ : Chart) (θ' : ℝ), 1 ≤ j →
    (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
      (j + 1)).2.2.2.1 j = some (c₁, θ') →
    (EL j ω).2 ≠ 0

end Corr

/-- **Named input (PROVE-T14-SB2LIFT, rulings R116/R120): SB2(2)'s per-stage correspondence over the bundle of
`Lk.RelDriverAtT`, with the physical domain identity** — SB2LIFT's `Mn.StageChainAtR2` (the R form of D11 with the
chain's driver and trace agreeing with `EL`'s up to the chain's horizon, `SB2XgIface`) together with `StageChainAtP`
and the zero clause `StageChainAtZ` ((L1)). -/
def SB2LowerStageChainStatementRP : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv,
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      RelDataClause3 κ b jumps P E u l k ω₀ c b' J' m EL →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        StageChainAtR2 κ b jumps E u l k ω₀ c b' J' m EL ω ∧ StageChainAtP κ b jumps E u l k ω₀ c b' J' m EL ω ∧
          StageChainAtZ κ b' J' m EL ω

end InteractingSLE.Theorem14.SB.Mq
