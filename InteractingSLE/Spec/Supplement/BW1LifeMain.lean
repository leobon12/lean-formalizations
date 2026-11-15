/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1LifeCanon
import InteractingSLE.Spec.Supplement.BW1LifeType
import InteractingSLE.Spec.Supplement.BW1PropTip
import InteractingSLE.Spec.Supplement.BW1
import InteractingSLE.Spec.Restart.FlowCodeMain
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Spec.Supplement.HullDetGen

/-!
# Proposition BW1 by the non-circular route: conditional law first, infinite relative lifetime last

Packet PROVE-BW1-LIFE. Proposition BW1 (`source/spec/p577-624.md` L830–L870, pp. 613–615). The route (the corrected
architecture of PROVE-BW1-LINES §4.1; the explosion hypothesis of the first chain is a conclusion of BW1, not an
input):

1. **The canonical conditional counterflow** (`BW1LifeCanon`, PROVED): conditionally on the retained past, the field
   read in the state chart `g_A − W` is the GFF of the stop word (staged law), whose counterflow word is admissible
   (`BW1LifeWord`, (BW1.2)); its canonical counterflow driver `Wr` (Theorem 1.2 jointly measurable in the word,
   Theorem 1.3) drives the conditional centred counterflow with infinite lifetime.
2. **The stopped conditional law of the actual relative exploration** (K2 with the relative lifetime `V` = the
   relative capacity at the contact, no explosion assumption): for a measurable version `(R, V)` of the relative
   driver (named input `BW1RelVersionStatement`, the measurability being proved generically by PROVE-GB6-RELSAFE) and
   K2's inputs (S) and (L) for its image law (named input `BW1RelSafeStatement`, the marked union law in the relative
   clock), the stopped K2 on the canonical relative space (`Supp8.Q3Stop.ae_isStopDrvMatch_of_hasRelSafe`, PROVED)
   identifies `R` with `Wr` before `V`: **`ae_bwDrv_eq_of_relSafe`** (PROVED).
3. **The endpoint** (named input `BW1EndpointStatement`, p. 614–615 "The endpoint and all relative stopping times"):
   a conditional counterflow with infinite lifetime that agrees with the relative exploration before `V` forces
   `V = ∞`, `T < ∞` and `η(T) = q`.
4. **The assembly**: **`bw1Statement_of_inputs`** (PROVED): `BW1.BW1Statement` from Theorems 1.2–1.3 (allowed, R48:
   BW1 serves Theorem 1.4) and the three named inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.BW1Life

open Exist Exist.StagedLaw Exist.Staged Restart Supp8.Q3Stop
open Sec2.Assembly (dyad)

/-! ### BW1's objects -/

section Defs

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*}

/-- BW1's program: a flow of angle `θ` from the root `0` with own time `t`, followed by `rest`. -/
abbrev bwSpec (gw2 : Bool) (θ : ℝ) (t : ℝ≥0∞) (rest : List Instr) : ExplSpec := ⟨0, gw2, Sum.inl (θ, t) :: rest⟩

/-- BW1's threshold event on the side `r`: the first piece stops at a continuation threshold on that side. -/
def bwEvent (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (r : Bool) : Set Ω :=
  {ω | BW1.EndsAtThresholdSide (ExplState.run κ b jumps spec (fun j => E j ω) 1) r}

/-- BW1's state chart after the first piece (`g_A − W` on the threshold event). -/
def bwChart (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : Chart :=
  BW1.stateChart (ExplState.run κ b jumps spec (fun j => E j ω) 1)

/-- BW1's contact time `T`: the first time the physical counterflow tip lies in the retained set (root and piece). -/
def bwContact (spec : ExplSpec) (W' : ℝ≥0 → Ω → ℝ) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  firstTipTime infinitySourceChart (fun s => W' s ω) (SB.prefixPhysSet κ b jumps spec (fun j => E j ω) 1)

/-- BW1's record: the record of the regularized first piece. -/
def bwRec (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : RecData :=
  pastMap κ b jumps spec (StagedReg.regHist spec E) 1 ω (Fin.last 0)

/-- BW1's relative field: the post-piece field read in the counterflow frame (`GW4Traverse.cfField`), regularized
history. -/
def bwRelField (spec : ExplSpec) (h : Ω → DistOn upperHalfPlaneOpens) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) :
    DistOn upperHalfPlaneOpens :=
  GW4Traverse.cfField κ (bwField κ b jumps spec h (StagedReg.regHist spec E) ω)

end Defs

/-- BW1's conditional relative word of a record: the counterflow word of the stop word. -/
def bwRelWord (κ θ : ℝ) (c₀ : BoundaryWord) (r : RecData) : BoundaryWord :=
  GW1Laws.cfWordOf κ (stopWord κ (BoundaryWord.shiftW 0 c₀, θ, r))

theorem measurable_bwRelWord (κ θ : ℝ) (c₀ : BoundaryWord) : Measurable (bwRelWord κ θ c₀) :=
  (GW1Laws.measurable_cfWordOf κ).comp ((measurable_stopWord κ).comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id)))

/-- **BW1's setting**: the hypotheses of `BW1.BW1Statement` (before the side `r`). -/
def IsBW1Setting (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) (gw2 : Bool)
    (rest : List Instr) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) [StandardBorelSpace Ω] [IsFiniteMeasure P] : Prop :=
  0 < κ ∧ κ < 4 ∧ IsPiecewiseConstantBoundaryData b jumps ∧ IsGFFWithBoundaryData P h b jumps ∧
    IsCenteredCounterflowDriver κ P h W' ζ' ∧ (∀ᵐ ω ∂P, ζ' ω = ⊤) ∧
    θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) ∧ IsStagedHistory κ b jumps P h (bwSpec gw2 θ t rest) E

/-! ### The relative exploration and the named inputs -/

/-- **A measurable exhausting version of BW1's relative exploration** (p. 614: "Fixed-hull restriction and positive
separation give continuous, strict relative Loewner growth"; p. 615: "Relative capacity is adapted, continuous and
strictly increasing"). Processes `R m` (measurable, continuous, from `0`, frozen after `V m`) with measurable stops
`V m`, each `V m` a path rule of (record, `R m`) announced by finite path rules on `F`; a clock `ℓ` measurable at
every time; almost surely on `F`: every `V m` is positive, `ℓ` is continuous and strictly increasing on the relative
interval `[0, sup_m V m)` and maps it onto the physical interval `[0, T)`, and before `V m` the tips of `R m` read
through the chart `c` and the inversion are the physical counterflow tips at the times `ℓ`. -/
def IsBW1RelVersion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (rec : Ω → RecData) (F : Set Ω)
    (c : Ω → Chart) (W' : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0∞) (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞)
    (ℓ : Ω → ℝ≥0 → ℝ≥0) : Prop :=
  (∀ m s, Measurable (R m s)) ∧ (∀ m ω, Continuous fun s => R m s ω) ∧ (∀ m ω, R m 0 ω = 0) ∧
    (∀ m ω (s : ℝ≥0), V m ω ≤ s → R m s ω = R m (V m ω).toNNReal ω) ∧ (∀ m, Measurable (V m)) ∧
    (∀ s, Measurable fun ω => ℓ ω s) ∧
    (∀ m, ∃ (ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞) (ρs : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞),
      Measurable ρ ∧ Supp8.GB6.HullId.IsPathRule ρ ∧ (∀ᵐ ω ∂P, V m ω = ρ (rec ω, fun u => R m u ω)) ∧
      (∀ n, Measurable (ρs n)) ∧ (∀ n, Supp8.GB6.HullId.IsPathRule (ρs n)) ∧ (∀ n x, ρs n x ≠ ⊤) ∧
      (∀ x, Monotone fun n => ρs n x) ∧
      ∀ᵐ ω ∂P, ω ∈ F → (∀ n, ρs n (rec ω, fun u => R m u ω) < V m ω) ∧
        ⨆ n, ρs n (rec ω, fun u => R m u ω) = V m ω) ∧
    ∀ᵐ ω ∂P, ω ∈ F → (∀ m, 0 < V m ω) ∧
      StrictMonoOn (ℓ ω) {s | (s : ℝ≥0∞) < ⨆ m, V m ω} ∧ ContinuousOn (ℓ ω) {s | (s : ℝ≥0∞) < ⨆ m, V m ω} ∧
      ℓ ω '' {s | (s : ℝ≥0∞) < ⨆ m, V m ω} = {u : ℝ≥0 | (u : ℝ≥0∞) < T ω} ∧
      ∀ m (s : ℝ≥0), (s : ℝ≥0∞) < V m ω → ∀ z : ℂ,
        ((c ω).trans infinitySourceChart).tipAt (fun u => R m u ω) s z ↔
          infinitySourceChart.tipAt (fun u => W' u ω) (ℓ ω s) z

/-- **Named input (measurability): BW1's relative exploration has a measurable exhausting version**
(`IsBW1RelVersion` for BW1's record, threshold event, state chart, physical counterflow and contact time). The
relative driver of one sample exists (PROVE-BW1-PROP, `ae_exists_isRelConfigOff_bw1`); this asks for a measurable
choice through announced stops (the GB6 analogue is `Q3Stop.GB6RelVersionAStatement`; PROVE-GB6-RELSAFE proves the
measurability generically). -/
def BW1RelVersionStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ)
    (ζ' : Ω → ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) (gw2 : Bool) (rest : List Instr) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
    IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E → ∀ r : Bool,
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
      IsBW1RelVersion P (bwRec κ b jumps (bwSpec gw2 θ t rest) E) (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r)
        (bwChart κ b jumps (bwSpec gw2 θ t rest) E) W' (bwContact κ b jumps (bwSpec gw2 θ t rest) W' E) R V ℓ

/-- **Named input: BW1's relative safe law** (p. 614, "Actual pre-contact geometry and the retained kernel": the
terminal `A` is a local marked history, marked optional-union locality retains it from the outset, nested marked
comparison identifies the full Poisson mean and Green covariance at every retained stop; Astra's follow-up 3, Q3, in
the filtration of the record and the relative path). For every measurable record event `TS` representing the
threshold event, every word `c₀` of the data, every version of the relative exploration, every `m` and every word type
`w`: the joint law of BW1's record and the relative variable (relative field, `R m`, `V m`), conditioned on the record
event of type `w`, has K2's inputs (S) and (L) at `16/κ` with lifetime `V m`, the stop is before the continuation
threshold, and the relative field is integrable (`Supp8.Q3Stop.HasRelSafe`), for the counterflow word `bwRelWord` of
the stop word. The GB6 analogue is `Q3Stop.GB6RelSafeStatement`. -/
def BW1RelSafeStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ)
    (ζ' : Ω → ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) (gw2 : Bool) (rest : List Instr) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
    IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E → ∀ (r : Bool) (TS : Set RecData), MeasurableSet TS →
    (∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ↔ bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS) →
    ∀ c₀ : BoundaryWord, c₀.jumps = jumps → (∀ y ∉ jumps, c₀.fn y = b y) →
    ∀ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
      IsBW1RelVersion P (bwRec κ b jumps (bwSpec gw2 θ t rest) E) (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r)
        (bwChart κ b jumps (bwSpec gw2 θ t rest) E) W' (bwContact κ b jumps (bwSpec gw2 θ t rest) W' E) R V ℓ →
      ∀ (m : ℕ) (w : WordType), HasRelSafe (16 / κ) w (bwRelWord κ θ c₀) TS
        (P.map fun ω => (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω,
          Supp8.GB6.RelDrv.relVar (bwRelField κ b jumps (bwSpec gw2 θ t rest) h E) (R m) (V m) ω))

/-- **Named input: BW1's endpoint** (p. 614–615, "The endpoint and all relative stopping times": if the limiting
relative capacity at `T` were finite, the canonical trace would have a finite endpoint, which the continuous inverse
of (BW1.1) identifies with the physical endpoint; for `T < ∞` it lies in `A` off the `q`-end, on the protected tail
excluded by GB5; for `T = ∞` original transience gives `x`, again excluded; so the relative lifetime is infinite,
relative transience gives the endpoint `q`, and `T < ∞`). For every version of the relative exploration and every
measurable driver `Wr` of the conditional centred counterflow in the state chart (`SB.IsCondCounterflowDriverOn`)
with infinite lifetime, continuous from `0`, and agreeing with every `R m` before `V m` on the threshold event:
almost surely on that event `sup_m V m = ∞`, `T < ∞` and the physical tip at `T` is the state's point `q`. -/
def BW1EndpointStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ)
    (ζ' : Ω → ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) (gw2 : Bool) (rest : List Instr) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
    IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E → ∀ r : Bool,
    ∀ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
      IsBW1RelVersion P (bwRec κ b jumps (bwSpec gw2 θ t rest) E) (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r)
        (bwChart κ b jumps (bwSpec gw2 θ t rest) E) W' (bwContact κ b jumps (bwSpec gw2 θ t rest) W' E) R V ℓ →
    ∀ (Wr : ℝ≥0 → Ω → ℝ) (ζr : Ω → ℝ≥0∞), (∀ s, Measurable (Wr s)) → Measurable ζr →
      SB.IsCondCounterflowDriverOn (mΩ := mΩ) κ (pastSigma κ b jumps (bwSpec gw2 θ t rest) E 1) P
        (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r) h (bwChart κ b jumps (bwSpec gw2 θ t rest) E) Wr ζr →
      (∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r →
        ζr ω = ⊤ ∧ Continuous (fun s => Wr s ω) ∧ Wr 0 ω = 0) →
      (∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r →
        ∀ m (s : ℝ≥0), (s : ℝ≥0∞) < V m ω → Wr s ω = R m s ω) →
      ∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r →
        (⨆ m, V m ω) = ⊤ ∧ bwContact κ b jumps (bwSpec gw2 θ t rest) W' E ω < ⊤ ∧
        infinitySourceChart.tipAt (fun s => W' s ω) (bwContact κ b jumps (bwSpec gw2 θ t rest) W' E ω).toNNReal
          (BW1.statePoint (ExplState.run κ b jumps (bwSpec gw2 θ t rest) (fun j => E j ω) 1))

/-! ### The canonical relative driver is the decoded canonical code -/

section Bridge

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ : ℝ} {t : ℝ≥0∞} {gw2 : Bool}
  {rest : List Instr} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- BW1's relative code: a canonical driver code read at BW1's relative word and field. -/
def bwCode (F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞) (κ : ℝ) (b : ℝ → ℝ)
    (jumps : Finset ℝ) (spec : ExplSpec) (θ : ℝ) (c₀ : BoundaryWord) {Ω : Type*} (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : Sec2.Assembly.PCode × ℝ≥0∞ :=
  F (bwRelWord κ θ c₀ (bwRec κ b jumps spec E ω), bwRelField κ b jumps spec h E ω)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem measurable_bwCode {F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hF : Measurable F) (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : Measurable h)
    (hEm : ∀ j, Measurable (E j)) (spec : ExplSpec) (c₀ : BoundaryWord) :
    Measurable (bwCode F κ b jumps spec θ c₀ h E) := by
  have hEm' : ∀ j, Measurable (StagedReg.regHist spec E j) := StagedReg.measurable_regHist hEm
  have hreg' : ∀ j ω, IsRegularDriver (StagedReg.regHist spec E j ω) := fun j ω =>
    StagedReg.isRegularDriver_regHist j ω
  have hrec : Measurable (bwRec κ b jumps spec E) := measurable_pastMap_one_last hb hEm' hreg'
  have hHc : Measurable (bwRelField κ b jumps spec h E) :=
    (GW4Traverse.measurable_cfField κ).comp (measurable_bwField hb hh hEm' hreg')
  exact hF.comp (((measurable_bwRelWord κ θ c₀).comp hrec).prodMk hHc)

open Supp8.GB6 in
/-- **The canonical relative driver is the decoded canonical driver code** of BW1's relative word and field, almost
surely on the event of a finite stop: under the regular conditional law given the retained past, the canonical driver
is a flow-line driver of the relative field (`GW1Laws.exists_coupling_of_ae_cfDrvOf`), so the universe bridge
`Supp8.HullDetGen.ae_flowLineDriver_eq_drvDec` identifies it with the decoded code; the good event is integrated
back. -/
theorem ae_bwDrv_eq_drvDec (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hS : IsStagedHistory κ b jumps P h (bwSpec gw2 θ t rest) E) {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps)
    (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) {F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode (16 / κ) 0 F) :
    ∀ᵐ ω ∂P, min t (E 0 ω).2 ≠ ⊤ →
      IsGoodDrvCode (bwCode F κ b jumps (bwSpec gw2 θ t rest) θ c₀ h E ω) ∧
      bwLife h12p hκ b jumps (bwSpec gw2 θ t rest) θ c₀ h (StagedReg.regHist (bwSpec gw2 θ t rest) E) ω =
        (bwCode F κ b jumps (bwSpec gw2 θ t rest) θ c₀ h E ω).2 ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) <
          bwLife h12p hκ b jumps (bwSpec gw2 θ t rest) θ c₀ h (StagedReg.regHist (bwSpec gw2 θ t rest) E) ω →
        bwDrv h12p hκ b jumps (bwSpec gw2 θ t rest) θ c₀ h (StagedReg.regHist (bwSpec gw2 θ t rest) E) s ω =
          drvDec (bwCode F κ b jumps (bwSpec gw2 θ t rest) θ c₀ h E ω) s := by
  set spec := bwSpec gw2 θ t rest with hspec
  set E' := StagedReg.regHist spec E with hE'
  have hEm' : ∀ j, Measurable (E' j) := StagedReg.measurable_regHist hS.1
  have hreg' : ∀ j ω, IsRegularDriver (E' j ω) := fun j ω => StagedReg.isRegularDriver_regHist j ω
  have hsnd : ∀ ω, (E' 0 ω).2 = (E 0 ω).2 := fun ω => StagedReg.regHist_snd 0 ω
  have hk : 0 < 16 / κ := GW4Traverse.sixteen_div_pos hκ
  obtain ⟨-, hgff⟩ := ae_bwField_gff (θ := θ) hκ hb hh (spec := spec) rfl hEm' hreg' (stageOK_regHist_zero hS)
    hc₀J hc₀
  have h𝒢 : pastSigma κ b jumps spec E' 1 ≤ mΩ := (measurable_pastMap_one hb hEm' hreg').comap_le
  have hM𝒢 : MeasurableSet[pastSigma κ b jumps spec E' 1] {ω | min t (E' 0 ω).2 ≠ ⊤} :=
    measurableSet_pastSigma_finStop (spec := spec) (θ := θ) (rest := rest) rfl
  set q : Ω → Sec2.Assembly.PCode × ℝ≥0∞ := bwCode F κ b jumps spec θ c₀ h E with hqdef
  have hqm : Measurable q := measurable_bwCode hF.1 hb hh.1 hS.1 spec c₀
  set D := bwDrv h12p hκ b jumps spec θ c₀ h E' with hDdef
  set L := bwLife h12p hκ b jumps spec θ c₀ h E' with hLdef
  have hDm : ∀ s, Measurable (D s) := measurable_bwDrv h12p hκ hb hh.1 hEm' hreg' c₀
  have hLm : Measurable L := measurable_bwLife h12p hκ hb hh.1 hEm' hreg' c₀
  set G : Set Ω := {ω | IsGoodDrvCode (q ω) ∧ L ω = (q ω).2 ∧
    ∀ n k : ℕ, (dyad n k : ℝ≥0∞) < L ω → D (dyad n k) ω = drvDec (q ω) (dyad n k)} with hGdef
  have hGm : MeasurableSet G := by
    have h1 : MeasurableSet {ω | IsGoodDrvCode (q ω)} := hqm measurableSet_isGoodDrvCode
    have h2 : MeasurableSet {ω | L ω = (q ω).2} := measurableSet_eq_fun hLm (measurable_snd.comp hqm)
    have h3 : ∀ n k : ℕ, MeasurableSet {ω | (dyad n k : ℝ≥0∞) < L ω →
        D (dyad n k) ω = drvDec (q ω) (dyad n k)} := fun n k => by
      have e : {ω | (dyad n k : ℝ≥0∞) < L ω → D (dyad n k) ω = drvDec (q ω) (dyad n k)} =
          {ω | (dyad n k : ℝ≥0∞) < L ω}ᶜ ∪ {ω | D (dyad n k) ω = drvDec (q ω) (dyad n k)} := by
        ext ω
        simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
      rw [e]
      exact (measurableSet_lt measurable_const hLm).compl.union
        (measurableSet_eq_fun (hDm _) ((measurable_drvDec _).comp hqm))
    have e : G = {ω | IsGoodDrvCode (q ω)} ∩ ({ω | L ω = (q ω).2} ∩ ⋂ n : ℕ, ⋂ k : ℕ,
        {ω | (dyad n k : ℝ≥0∞) < L ω → D (dyad n k) ω = drvDec (q ω) (dyad n k)}) := by
      ext ω
      simp only [hGdef, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    rw [e]
    exact h1.inter (h2.inter (MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => h3 n k))
  have hker : ∀ᵐ ω₀ ∂P, ω₀ ∈ {ω | min t (E' 0 ω).2 ≠ ⊤} →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E' 1) ω₀), ω ∈ G := by
    filter_upwards [hgff, Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒢 (measurable_bwWord (θ := θ) c₀)]
      with ω₀ hg hw hfin
    set ν := condExpKernel P (pastSigma κ b jumps spec E' 1) ω₀ with hν
    set c := bwWord κ b jumps spec θ c₀ E' ω₀ with hcdef
    have hc : c.IsSorted := isSorted_stopWord κ _
    have hG := hg hfin
    have hX := GW1Laws.isGFFWithBoundaryData_cfField_cfWordOf κ hc hG
    have hae : ∀ᵐ ω ∂ν, L ω = (GW1Laws.cfDrvOf h12p hκ (c, bwField κ b jumps spec h E' ω)).2 ∧
        ∀ s, D s ω = (GW1Laws.cfDrvOf h12p hκ (c, bwField κ b jumps spec h E' ω)).1 s := by
      filter_upwards [hw] with ω hwω
      simp only [hDdef, hLdef, bwDrv, bwLife]
      rw [hwω]
      exact ⟨rfl, fun _ => rfl⟩
    obtain ⟨𝓕, VL, VR, B, hcoup⟩ := GW1Laws.exists_coupling_of_ae_cfDrvOf h12p hκ h13 hc hG hDm hLm hae
    have hfl : IsFlowLineDriver (16 / κ) (GW1Laws.cfWordOf κ c).fn (GW1Laws.cfWordOf κ c).jumps 0 ν
        (fun ω => GW4Traverse.cfField κ (bwField κ b jumps spec h E' ω)) D L :=
      ⟨_, 𝓕, VL, VR, B, fun ω => Exist.isTranslateAddConst_flowField 0 _ _, hcoup⟩
    have hc' := GW1Laws.isSorted_cfWordOf κ hc
    have hdet := Supp8.HullDetGen.ae_flowLineDriver_eq_drvDec h12p h13 hk hF hc' hX hfl
    have hgood := ae_isGoodDrvCode_gffLaw hk hF hc'
    rw [← Supp8.HullDetGen.map_eq_gffLaw hc' hX] at hgood
    have hgood' := ae_of_ae_map hX.1.aemeasurable hgood
    filter_upwards [hdet, hgood', hw] with ω hdω h3 hwω
    obtain ⟨h1, h2⟩ := hdω
    have hq : q ω = F (GW1Laws.cfWordOf κ c, GW4Traverse.cfField κ (bwField κ b jumps spec h E' ω)) := by
      have e1 : bwRelWord κ θ c₀ (bwRec κ b jumps spec E ω) =
          GW1Laws.cfWordOf κ (bwWord κ b jumps spec θ c₀ E' ω) := rfl
      simp only [hqdef, bwCode, bwRelField]
      rw [e1, hwω]
    refine ⟨?_, ?_, fun n k hnk => ?_⟩
    · rw [hq]; exact h3
    · rw [hq]; exact h1
    · rw [hq]; exact h2 _ hnk
  have hP := GW2Schedule.ae_of_ae_condExpKernel_on h𝒢 hM𝒢 hGm hker
  filter_upwards [hP] with ω hω hfin
  have hfin' : min t (E' 0 ω).2 ≠ ⊤ := by rw [hsnd]; exact hfin
  obtain ⟨g1, g2, g3⟩ := hω hfin'
  refine ⟨g1, g2, fun s hs => ?_⟩
  have hDc : ContinuousOn (fun s => D s ω) {s | (s : ℝ≥0∞) < L ω} :=
    (GW1Laws.cfDrvOf_regular h12p hκ (bwWord κ b jumps spec θ c₀ E' ω, bwField κ b jumps spec h E' ω)).1
  have hqc : ContinuousOn (drvDec (q ω)) {s | (s : ℝ≥0∞) < L ω} := by
    rw [g2]; exact continuousOn_drvDec (q ω)
  exact RelDrv.eqOn_of_dyad_lt hDc hqc g3 s hs

end Bridge

/-! ### The stopped match of the relative exploration (the non-circular K2 route) -/

section Match

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ : ℝ} {t : ℝ≥0∞} {gw2 : Bool}
  {rest : List Instr} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- On the threshold event the first piece has a finite stop. -/
theorem finStop_of_mem_bwEvent {r : Bool} {ω : Ω} (hω : ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r) :
    min t (E 0 ω).2 ≠ ⊤ :=
  ne_top_of_le_ne_top (BW1Prop.ne_top_of_endsAtThresholdSide (s := ExplState.init 0) (k := 0) hω)
    (min_le_right _ _)

omit [StandardBorelSpace Ω] in
open Supp8.GB6 in
/-- **The stopped K2 identifies the relative exploration with the relative code** (word type by word type on the
canonical relative space, `Supp8.Q3Stop.ae_isStopDrvMatch_of_hasRelSafe`; BW1's conditional words take countably many
types, `countable_range_wordType_retStop`): almost surely on the threshold event, `R m` matches BW1's relative code
before `V m`. The relative lifetime is the stop `V m`, not an explosion time (no reach hypothesis). -/
theorem ae_isStopDrvMatch_bw (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : Measurable h)
    (hEm : ∀ j, Measurable (E j)) {F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode (16 / κ) 0 F) {r : Bool} {TS : Set RecData} (hTS : MeasurableSet TS)
    (hFTS : ∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ↔
      bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS)
    {c₀ : BoundaryWord} {W' : ℝ≥0 → Ω → ℝ} {R : ℕ → ℝ≥0 → Ω → ℝ} {V : ℕ → Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hver : IsBW1RelVersion P (bwRec κ b jumps (bwSpec gw2 θ t rest) E) (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r)
      (bwChart κ b jumps (bwSpec gw2 θ t rest) E) W' (bwContact κ b jumps (bwSpec gw2 θ t rest) W' E) R V ℓ)
    (hsafe : ∀ (m : ℕ) (w : WordType), HasRelSafe (16 / κ) w (bwRelWord κ θ c₀) TS
        (P.map fun ω => (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω,
          RelDrv.relVar (bwRelField κ b jumps (bwSpec gw2 θ t rest) h E) (R m) (V m) ω)))
    (m : ℕ) :
    ∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r →
      RelDrv.IsStopDrvMatch (bwCode F κ b jumps (bwSpec gw2 θ t rest) θ c₀ h E ω) (fun s => R m s ω) (V m ω) := by
  set spec := bwSpec gw2 θ t rest with hspec
  obtain ⟨hRm, hRc, hR0, -, hVm, -, hrule, hae⟩ := hver
  obtain ⟨ρ, ρs, hρm, hρ, hVρ, hρsm, hρs, hρsfin, hρsmono, hρslt⟩ := hrule m
  have hk : 0 < 16 / κ := GW4Traverse.sixteen_div_pos hκ
  have hEm' : ∀ j, Measurable (StagedReg.regHist spec E j) := StagedReg.measurable_regHist hEm
  have hreg' : ∀ j ω, IsRegularDriver (StagedReg.regHist spec E j ω) := fun j ω =>
    StagedReg.isRegularDriver_regHist j ω
  have hrec : Measurable (bwRec κ b jumps spec E) := measurable_pastMap_one_last hb hEm' hreg'
  have hHc : Measurable (bwRelField κ b jumps spec h E) :=
    (GW4Traverse.measurable_cfField κ).comp (measurable_bwField hb hh hEm' hreg')
  have hcount : (range fun r : RecData => wordType (16 / κ) (bwRelWord κ θ c₀ r)).Countable :=
    countable_range_wordType_retStop (16 / κ) κ θ (Sec7.StripSysField.cfOffset κ -
      2 * Real.pi * Sec7.StripSysField.cfCoeff κ) (-Sec7.StripSysField.cfCoeff κ) (BoundaryWord.shiftW 0 c₀)
  have hV0 : ∀ᵐ ω ∂P, bwRec κ b jumps spec E ω ∈ TS → 0 < V m ω := by
    filter_upwards [hae, hFTS] with ω h1 h2 hT
    exact (h1 (h2.2 hT)).1 m
  have hlt : ∀ᵐ ω ∂P, bwRec κ b jumps spec E ω ∈ TS →
      ∀ n, ρs n (bwRec κ b jumps spec E ω, fun u => R m u ω) < V m ω := by
    filter_upwards [hρslt, hFTS] with ω h1 h2 hT
    exact (h1 (h2.2 hT)).1
  have hsup : ∀ᵐ ω ∂P, bwRec κ b jumps spec E ω ∈ TS →
      ⨆ n, ρs n (bwRec κ b jumps spec E ω, fun u => R m u ω) = V m ω := by
    filter_upwards [hρslt, hFTS] with ω h1 h2 hT
    exact (h1 (h2.2 hT)).2
  have hw : ∀ w : WordType, ∀ᵐ ω ∂P, bwRec κ b jumps spec E ω ∈ TS →
      wordType (16 / κ) (bwRelWord κ θ c₀ (bwRec κ b jumps spec E ω)) = w →
      RelDrv.IsStopDrvMatch (F (bwRelWord κ θ c₀ (bwRec κ b jumps spec E ω), bwRelField κ b jumps spec h E ω))
        (fun s => R m s ω) (V m ω) := fun w =>
    ae_isStopDrvMatch_of_hasRelSafe hk hF (measurable_bwRelWord κ θ c₀) hTS w hrec hHc (hRm m) (hRc m) (hR0 m)
      (hVm m) (hsafe m w) hV0 hρm hρ hVρ hρsm hρs hρsfin hρsmono hlt hsup
  have hall := (ae_ball_iff hcount).2 fun w _ => hw w
  filter_upwards [hall, hFTS] with ω h1 h2 hFω
  exact h1 _ ⟨_, rfl⟩ (h2.1 hFω) rfl

open Supp8.GB6 in
/-- **The relative exploration is the canonical relative driver before its stops** (BW1, p. 614: "Theorem 2.4 and
integrated uniqueness identify the actual stopped relative law with the independently constructed canonical word"):
almost surely on the threshold event, for every `m`, BW1's canonical relative driver `bwDrv` agrees with `R m` before
`V m` (the stopped match and the universe bridge `ae_bwDrv_eq_drvDec`). -/
theorem ae_bwDrv_eq_of_relSafe (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h (bwSpec gw2 θ t rest) E)
    {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode (16 / κ) 0 F) {r : Bool} {TS : Set RecData} (hTS : MeasurableSet TS)
    (hFTS : ∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ↔
      bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS)
    {W' : ℝ≥0 → Ω → ℝ} {R : ℕ → ℝ≥0 → Ω → ℝ} {V : ℕ → Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hver : IsBW1RelVersion P (bwRec κ b jumps (bwSpec gw2 θ t rest) E) (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r)
      (bwChart κ b jumps (bwSpec gw2 θ t rest) E) W' (bwContact κ b jumps (bwSpec gw2 θ t rest) W' E) R V ℓ)
    (hsafe : ∀ (m : ℕ) (w : WordType), HasRelSafe (16 / κ) w (bwRelWord κ θ c₀) TS
        (P.map fun ω => (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω,
          RelDrv.relVar (bwRelField κ b jumps (bwSpec gw2 θ t rest) h E) (R m) (V m) ω))) :
    ∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r → ∀ (m : ℕ) (s : ℝ≥0), (s : ℝ≥0∞) < V m ω →
      bwDrv h12p hκ b jumps (bwSpec gw2 θ t rest) θ c₀ h (StagedReg.regHist (bwSpec gw2 θ t rest) E) s ω =
        R m s ω := by
  have hbr := ae_bwDrv_eq_drvDec h12p h13 hκ hb hh hS hc₀J hc₀ hF
  have hmat := fun m => ae_isStopDrvMatch_bw hκ hb hh.1 hS.1 hF hTS hFTS hver hsafe m
  have hRc := hver.2.1
  filter_upwards [hbr, ae_all_iff.2 hmat] with ω h1 h2 hFω m s hs
  obtain ⟨hgood, hL, hD⟩ := h1 (finStop_of_mem_bwEvent hFω)
  have hm := h2 m hFω
  have hRe := RelDrv.eqOn_drvDec_of_isStopDrvMatch hgood (hRc m ω).continuousOn hm s hs
  have hsL : (s : ℝ≥0∞) <
      bwLife h12p hκ b jumps (bwSpec gw2 θ t rest) θ c₀ h (StagedReg.regHist (bwSpec gw2 θ t rest) E) ω := by
    rw [hL]; exact lt_of_lt_of_le hs hm.1
  rw [hD s hsL, hRe]

end Match

/-! ### The record event and the tips -/

section Assembly

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ : ℝ} {t : ℝ≥0∞} {gw2 : Bool}
  {rest : List Instr} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **BW1's threshold event is a record event**: for a measurable set of records `TS`, almost surely the first piece
ends at a threshold on the side `r` iff its record is in `TS` (the status of the run is a measurable function of the
retained past, `isMeasState_run`; the regularized history runs through the same first state). -/
theorem exists_recordEvent (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hS : IsStagedHistory κ b jumps P h (bwSpec gw2 θ t rest) E) (r : Bool) :
    ∃ TS : Set RecData, MeasurableSet TS ∧
      ∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ↔ bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS := by
  set spec := bwSpec gw2 θ t rest with hspec
  set E' := StagedReg.regHist spec E with hE'
  have hEm' : ∀ j, Measurable (E' j) := StagedReg.measurable_regHist hS.1
  have hreg' : ∀ j ω, IsRegularDriver (E' j ω) := fun j ω => StagedReg.isRegularDriver_regHist j ω
  set F' : Set Ω := bwEvent κ b jumps spec E' r with hF'
  have hF'm : MeasurableSet F' :=
    (isMeasState_run (κ := κ) hb spec hEm' hreg' 1).1 (Sum.inr (Sum.inr (Sum.inl (some r))))
  have hF'𝒢 : MeasurableSet[pastSigma κ b jumps spec E' 1] F' :=
    measurableSet_pastSigma_of_run runMeasStatement hb spec (fun j _ => hEm' j) (fun j _ => hreg' j) hF'm
      fun ω ω' he hω => by
        change BW1.EndsAtThresholdSide (ExplState.run κ b jumps spec (fun j => E' j ω') 1) r
        rw [← he]
        exact hω
  rw [pastSigma_eq_comap] at hF'𝒢
  obtain ⟨B, hB, hpre⟩ := hF'𝒢
  have hcm : Measurable fun x : RecData => (fun _ : Fin 1 => x) := measurable_pi_iff.2 fun _ => measurable_id
  refine ⟨(fun x : RecData => (fun _ : Fin 1 => x)) ⁻¹' B, hcm hB, ?_⟩
  filter_upwards [ae_run_one_regHist h13 hκ hb hh hS rfl rfl] with ω hrun
  have hpm : pastMap κ b jumps spec E' 1 ω = fun _ : Fin 1 => bwRec κ b jumps spec E ω := by
    funext i
    rw [Subsingleton.elim i (Fin.last 0)]
    rfl
  have hmem : ω ∈ F' ↔ ω ∈ bwEvent κ b jumps spec E r := by
    change BW1.EndsAtThresholdSide (ExplState.run κ b jumps spec (fun j => E' j ω) 1) r ↔
      BW1.EndsAtThresholdSide (ExplState.run κ b jumps spec (fun j => E j ω) 1) r
    rw [hrun]
  rw [← hmem, ← hpre]
  change pastMap κ b jumps spec E' 1 ω ∈ B ↔ (fun _ : Fin 1 => bwRec κ b jumps spec E ω) ∈ B
  rw [hpm]

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **The tip at time `s` only depends on the driver before any later time** (`fwdMapInv_eq_of_eqOn`). -/
theorem tipAt_congr_of_lt (c : Chart) {U U' : ℝ≥0 → ℝ} {e : ℝ≥0∞} {s : ℝ≥0} (hs : (s : ℝ≥0∞) < e)
    (hU : ∀ u : ℝ≥0, (u : ℝ≥0∞) < e → U u = U' u) (z : ℂ) : c.tipAt U s z ↔ c.tipAt U' s z := by
  obtain ⟨t₂, hst₂, ht₂e⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  have hst₂' : s < t₂ := ENNReal.coe_lt_coe.1 hst₂
  have hinv : QuantumZipper.fwdMapInv (fun r : ℝ => U r.toNNReal) s =
      QuantumZipper.fwdMapInv (fun r : ℝ => U' r.toNNReal) s :=
    fwdMapInv_eq_of_eqOn (NNReal.coe_nonneg s) (by exact_mod_cast hst₂') fun r hr =>
      hU _ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) ht₂e)
  unfold Chart.tipAt
  rw [hinv]

/-! ### The assembly -/

/-- **Proposition BW1** (`BW1.BW1Statement`) from Theorems 1.2–1.3 (R48: BW1 serves Theorem 1.4), the canonical
driver codes, and the three named inputs: the measurable relative version (`BW1RelVersionStatement`), the relative
safe law (`BW1RelSafeStatement`, K2's (S) and (L) for the relative exploration with lifetime the stop) and the
endpoint (`BW1EndpointStatement`). The route is non-circular: the conditional law of the relative exploration is
identified with the canonical conditional counterflow **before** its stops (`ae_bwDrv_eq_of_relSafe`), and only then
the endpoint argument gives the infinite relative lifetime, `T < ∞` and `η(T) = q`. -/
theorem bw1Statement_of_inputs (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    (hcode : Restart.CanonicalDriverCodeStatement) (hV : BW1RelVersionStatement.{u})
    (hSafe : BW1RelSafeStatement.{u}) (hEnd : BW1EndpointStatement.{u}) : BW1.BW1Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hcf hζ' θ hθ t gw2 rest E hS r
  have hset : IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E := ⟨hκ, hκ4, hb, hh, hcf, hζ', hθ, hS⟩
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  obtain ⟨F, hF⟩ := hcode (16 / κ) 0 (GW4Traverse.sixteen_div_pos hκ)
  obtain ⟨hWm, hζm, hcond, hreg⟩ := condCounterflow_first (spec := bwSpec gw2 θ t rest) h12p h13 hT13₀ hκ hκ4 hb hh
    hcf hζ' hθ rfl rfl hS hc₀J hc₀
  obtain ⟨R, V, ℓ, hver⟩ := hV κ b jumps P h W' ζ' θ t gw2 rest E hset r
  obtain ⟨TS, hTS, hFTS⟩ := exists_recordEvent h13 hκ hb hh hS r
  have hsafe := hSafe κ b jumps P h W' ζ' θ t gw2 rest E hset r TS hTS hFTS c₀ hc₀J hc₀ R V ℓ hver
  have heq := ae_bwDrv_eq_of_relSafe h12p h13 hκ hb hh hS hc₀J hc₀ hF hTS hFTS hver hsafe
  have hFM : bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ⊆ {ω | min t (E 0 ω).2 ≠ ⊤} := fun ω hω =>
    finStop_of_mem_bwEvent hω
  have hcondF := hcond.mono hFM
  have hregF := hreg.mono fun ω hω hFω => hω (hFM hFω)
  have hend := hEnd κ b jumps P h W' ζ' θ t gw2 rest E hset r R V ℓ hver _ _ hWm hζm hcondF hregF heq
  refine ⟨_, _, ℓ, hcondF, hver.2.2.2.2.2.1, ?_⟩
  filter_upwards [hregF, hend, hver.2.2.2.2.2.2.2, heq] with ω hr he hv hq hFω
  obtain ⟨hζ, -, -⟩ := hr hFω
  obtain ⟨hsup, hT, htip⟩ := he hFω
  obtain ⟨-, hmono, hcont, himg, htipR⟩ := hv hFω
  have huniv : {s : ℝ≥0 | (s : ℝ≥0∞) < ⨆ m, V m ω} = univ :=
    eq_univ_of_forall fun s => by rw [mem_ofPred_eq, hsup]; exact ENNReal.coe_lt_top
  rw [huniv] at hmono hcont himg
  refine ⟨hζ, hT, htip, continuousOn_univ.1 hcont, strictMonoOn_univ.1 hmono, ?_, fun s z => ?_⟩
  · rw [← image_univ]; exact himg
  · obtain ⟨m, hm⟩ : ∃ m, (s : ℝ≥0∞) < V m ω := lt_iSup_iff.1 (by rw [hsup]; exact ENNReal.coe_lt_top)
    rw [← htipR m s hm z]
    exact tipAt_congr_of_lt _ hm (fun u hu => hq hFω m u hu) z

end Assembly

end InteractingSLE.Theorem14.BW1Life
