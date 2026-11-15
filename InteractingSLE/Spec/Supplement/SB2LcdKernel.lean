/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LcdNested

/-!
# SB2(2)'s conditional half from finer conditional flow lines with their own data

Packet PROVE-T14-SB2LCOND. With the nested conditional-variance identity (`SB2LcdNested`), the erasure clause of the
finer form (`SB2LcdFiner`) is no longer an input:

* `isCondFlowLineDriverOn_sup_of_le_aeSigma`: a conditional flow line given `𝒢'` is one given `𝒢' ⊔ m` when `m` is
  contained in `𝒢'` up to null sets (the regular conditional laws agree almost everywhere);
* **`ae_codeMatch_of_condFlowLine_data`** (generic): if a σ-algebra `𝒢'` contains the retained past of stage `k` up to
  null sets, `F'` covers the launch event, and given `𝒢'` the stage is the angle-`θ₀` flow line of the field read in
  the run chart with ANY piecewise-constant data `bc` off `jc`, then the stage driver matches the canonical code of
  every witness `(β, Y)` of the stage's conditional law. Proof: given `𝒢' ⊔ pastSigma k` the chart field is the GFF of
  `bc`; given `pastSigma k` it is the GFF of `β`; the nested conditional-variance identity
  (`ae_isGFF_condExpKernel_of_le`) makes it the GFF of `β` given the finer σ-algebra, so `bc` and `β` agree off a
  finite set (`eq_of_isGFFWithBoundaryData`) and the flow line has the data of `β`; then `SB2LcdFiner`;
* **`SB2LowerRelKernelStatement`** (named input) and **`sb2LowerRelStageCondStatement_of_kernel`**: SB2(2)'s
  conditional half from Theorems 1.2–1.3 and, per relative stage, a conditional flow line given some σ-algebra that
  contains the relative past up to null sets (supplement pp. 631–633: the union kernel in the filtration retaining
  the first history, its exterior projection and the erased portion; "Integrated uniqueness and the
  field-determining graphs identify the actual relative ordinary flows").

The named input loses nothing: `𝒢'` the relative past, `F'` the launch event and the data of the conditional half give
it back.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lcd

open Restart Exist Exist.Staged Exist.StagedLaw

section Generic

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

omit [IsProbabilityMeasure P] in
/-- A conditional flow line given `𝒢'` is one given `𝒢' ⊔ m` when `m ≤ 𝒢'` up to null sets. -/
theorem isCondFlowLineDriverOn_sup_of_le_aeSigma [IsFiniteMeasure P] {θ : ℝ} (𝒢' m : {m : MeasurableSpace Ω // m ≤ mΩ})
    (hle : m.1 ≤ LocalSets.aeSigma 𝒢'.1 P) {F : Set Ω} {c : Ω → Chart} {bc : Ω → ℝ → ℝ} {jc : Ω → Finset ℝ}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hcfl : SB.IsCondFlowLineDriverOn κ θ 𝒢'.1 P F h c bc jc W ζ) :
    SB.IsCondFlowLineDriverOn κ θ (𝒢'.1 ⊔ m.1) P F h c bc jc W ζ := by
  have hker : ∀ᵐ ω ∂P, condExpKernel P 𝒢'.1 ω = condExpKernel P (𝒢'.1 ⊔ m.1) ω :=
    KernelTower.ae_condExpKernel_eq_of_le_aeSigma 𝒢'.2 (sup_le 𝒢'.2 m.2)
      (le_sup_left.trans (LocalSets.le_aeSigma _ P)) (sup_le (LocalSets.le_aeSigma _ P) hle)
  filter_upwards [hcfl, hker] with ω₀ h1 h2 hF
  rw [← h2]
  exact h1 hF

/-- **The code match from a finer conditional flow line with its own data.** -/
theorem ae_codeMatch_of_condFlowLine_data (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (θ₀ : ℝ) {k : ℕ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (𝒢' : {m : MeasurableSpace Ω // m ≤ mΩ}) (hpast : pastSigma κ b jumps spec E k ≤ LocalSets.aeSigma 𝒢'.1 P)
    {F' : Set Ω}
    (hcov : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none → ω ∈ F')
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y) {bc : Ω → ℝ → ℝ} {jc : Ω → Finset ℝ}
    (hcfl : SB.IsCondFlowLineDriverOn κ θ₀ 𝒢'.1 P F' h (Cond.runChart κ b jumps spec E k) bc jc
      (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2)) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      IsDriverCodeMatch (driverCode h12p hκ θ₀ (β ω, Y ω)) (fun t => (E k ω).1 t) (E k ω).2 := by
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := by
    rw [pastSigma_eq_comap]
    exact (measurable_pastMap runMeasStatement hb spec (fun j _ => hEm j) (fun j _ => hreg j) k le_rfl).comap_le
  set 𝒢'' : {m : MeasurableSpace Ω // m ≤ mΩ} := ⟨𝒢'.1 ⊔ pastSigma κ b jumps spec E k, sup_le 𝒢'.2 h𝒢⟩
    with h𝒢''
  have hcfl'' : SB.IsCondFlowLineDriverOn κ θ₀ 𝒢''.1 P F' h (Cond.runChart κ b jumps spec E k) bc jc
      (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2) :=
    isCondFlowLineDriverOn_sup_of_le_aeSigma 𝒢' ⟨_, h𝒢⟩ hpast hcfl
  have hL : MeasurableSet[pastSigma κ b jumps spec E k]
      {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} :=
    Lv.measurableSet_launch_pastSigma hb hEm hreg k
  -- given the finer σ-algebra, the chart field is the GFF of `bc`
  have hfine : ∀ᵐ ω₀ ∂P, ω₀ ∈ {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} →
      IsGFFWithBoundaryData (condExpKernel P 𝒢''.1 ω₀) Y (bc ω₀) (jc ω₀) := by
    filter_upwards [hcfl'', hcov, hW.2.2.1,
      CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b) (jumps := jumps) spec (fun j _ => hreg j) 𝒢''.2
        le_sup_right,
      Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) 𝒢''.2 hW.2.2.1] with ω₀ hc₀ hcov₀ hp₀ hrun₀ hpk₀ hl₀
    obtain ⟨hb₀, h', hT, hfl⟩ := hc₀ (hcov₀ hl₀)
    obtain ⟨hconf, -, -⟩ := hp₀ hl₀
    have hg := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb₀ hfl
    refine isGFFWithBoundaryData_congr_ae hg hW.2.1 ?_
    filter_upwards [hrun₀, hpk₀] with ω hrunω hpω
    have hlω : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [launches_run_succ_of_run_eq spec hrunω]
      exact hl₀
    obtain ⟨-, -, hYω⟩ := hpω hlω
    have hYω' : IsChartTransport (Cond.runChart κ b jumps spec E k ω₀) 1 0 (chiC κ) (h ω) (Y ω) := by
      change IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω₀) k).2.2.2.2.1 1 0 (chiC κ) (h ω) (Y ω)
      rw [← hrunω]
      exact hYω
    exact (IsChartTransport.unique hconf hYω' (hT ω)).symm
  have hdata : ∀ᵐ ω₀ ∂P, ω₀ ∈ {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} →
      IsPiecewiseConstantBoundaryData (bc ω₀) (jc ω₀) := by
    filter_upwards [hcfl'', hcov] with ω₀ h1 h2 hl
    exact (h1 (h2 hl)).1
  -- the nested conditional-variance identity: given the finer σ-algebra, it is still the GFF of `β`
  have hnest := ae_isGFF_condExpKernel_of_le (P := P) (𝒢 := pastSigma κ b jumps spec E k) (𝒢' := 𝒢''.1)
    le_sup_right 𝒢''.2 hW.2.1 hL (g := fun ω => (β ω).fn) (S := fun ω => (β ω).jumps)
    (Eventually.of_forall fun ω _ => (β ω).isPiecewiseConstantBoundaryData) hdata hW.2.2.2 hfine
  have hcflβ : SB.IsCondFlowLineDriverOn κ θ₀ 𝒢''.1 P
      {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} h
      (Cond.runChart κ b jumps spec E k) (fun ω => (β ω).fn) (fun ω => (β ω).jumps)
      (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2) := by
    filter_upwards [hcfl'', hcov, hnest, hfine] with ω₀ h1 h2 h3 h4 hl₀
    obtain ⟨hb₀, h', hT, hfl⟩ := h1 (h2 hl₀)
    refine ⟨(β ω₀).isPiecewiseConstantBoundaryData, h', hT, ?_⟩
    have heq := eq_of_isGFFWithBoundaryData (β ω₀).isPiecewiseConstantBoundaryData hb₀ (h3 hl₀) (h4 hl₀)
    exact (isFlowLineDriver_congr_of_eqOn (β ω₀).isPiecewiseConstantBoundaryData hb₀ _
      fun y hy => (heq y hy).symm).1 hfl
  exact ae_codeMatch_of_condFlowLine_le h12p h13 hκ θ₀ hb hEm hreg 𝒢'' le_sup_right
    (Eventually.of_forall fun _ hl => hl) hW hcflβ

end Generic

/-! ### SB2(2): the conditional half from finer conditional flow lines -/

section SB2

open Supp9B Lx Lu Leaf FlowDilate Sec4

/-- **Finer conditional flow lines at one launch** (no erasure clause): for `m = −e_R`, every measurable family `EL`
of drivers, regular at every sample, whose relative walk carries the actual tail's lift almost surely under the
retained kernel `Q`, and every stage `j`: there are a σ-algebra `𝒢'` containing the relative past of stage `j` up to
`Q`-null sets, an event `F'` covering the launch event `Q`-almost surely, and piecewise-constant data `bc` off `jc`
(read at the conditioning sample) such that, given `𝒢'` (for `Q`-almost every sample of `F'`), the stage is the
angle-`(−π/2)` flow line of the conditional field `affField m h'` read in the run chart of stage `j`. -/
def RelStageKernel (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ)
    (h' : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
    (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
    (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
        Lf.IsTailLiftOf c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀
          (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω)) →
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

/-- **Named input: SB2(2)'s finer conditional flow lines at the later launches** (per stage; no erasure clause). -/
def SB2LowerRelKernelStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → RelStageKernel κ b jumps P E u l k ω₀ c b' J' h'

/-- The finer conditional flow lines give the pathwise identification (through the nested conditional-variance
identity). -/
theorem sb2LowerRelCodeStatement_of_kernel (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hker : SB2LowerRelKernelStatement.{u}) : SB2LowerRelCodeStatement.{u} h12p := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hker κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft]
    with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk hκ' m hm EL hELm hELr hlift j β Y hW
  obtain ⟨𝒢', F', bc, jc, hpast, hcov, hcfl⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hlift j
  exact ae_codeMatch_of_condFlowLine_data h12p h13 hκ' (-(Real.pi / 2))
    (isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb') hELm hELr 𝒢' hpast hcov hW hcfl

/-- **SB2(2)'s conditional half from the finer conditional flow lines** (and Theorems 1.2–1.3). -/
theorem sb2LowerRelStageCondStatement_of_kernel (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (hker : SB2LowerRelKernelStatement.{u}) :
    Lk.SB2LowerRelStageCondStatement.{u} :=
  sb2LowerRelStageCondStatement_of_code h12p h13 (sb2LowerRelCodeStatement_of_kernel h12p h13 hker)

/-- **SB2(2)'s combined target (R104a)** from the geometric half and the finer conditional flow lines. -/
theorem sb2LowerLaunchLiftStatement_of_kernel (h12 : Theorem12Statement.{u})
    (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0})
    (h13₀ : Theorem13Statement.{0}) (hgeo : Lk.SB2LowerRelWalkStatement.{u})
    (hker : SB2LowerRelKernelStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  Lk.sb2LowerLaunchLiftStatement_of_split h12 h13 h12₀ h13₀ hgeo
    (sb2LowerRelStageCondStatement_of_kernel h12p h13 hker)

/-- **The named input loses nothing**: SB2(2)'s conditional half gives the finer conditional flow lines (with `𝒢'`
the relative past, `F'` the launch event and the data of the conditional half, selected by choice). -/
theorem sb2LowerRelKernelStatement_of_cond (hcond : Lk.SB2LowerRelStageCondStatement.{u}) :
    SB2LowerRelKernelStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hcond κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft]
    with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hlift j
  have hst := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hlift j
  have hb'' := isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb'
  have h𝒢 : pastSigma κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j ≤ mΩ := by
    rw [pastSigma_eq_comap]
    exact (measurable_pastMap runMeasStatement hb'' _ (fun i _ => hELm i) (fun i _ => hELr i) j le_rfl).comap_le
  set Q := condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀ with hQ
  set 𝒢' : {m' : MeasurableSpace Ω // m' ≤ mΩ} := ⟨_, h𝒢⟩ with h𝒢'
  let p : Ω → (ℝ → ℝ) × Finset ℝ → Prop := fun ω₁ bJ =>
    IsPiecewiseConstantBoundaryData bJ.1 bJ.2 ∧ ∃ h'' : Ω → DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport (Cond.runChart κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j ω₁)
        1 0 (chiC κ) (affField m one_pos (h' ω)) (h'' ω)) ∧
      IsFlowLineDriver κ bJ.1 bJ.2 (-(Real.pi / 2)) (condExpKernel Q 𝒢'.1 ω₁) h''
        (fun t ω => (EL j ω).1 t) (fun ω => (EL j ω).2)
  refine ⟨𝒢', {ω | (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
    (j + 1)).2.2.2.1 j ≠ none}, fun ω => (Classical.epsilon (p ω)).1, fun ω => (Classical.epsilon (p ω)).2,
    LocalSets.le_aeSigma _ _, Eventually.of_forall fun _ hl => hl, ?_⟩
  filter_upwards [hst] with ω₁ h₁ hl₁
  obtain ⟨⟨c₁, θ₁⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl₁
  have hθ₁ : θ₁ = -(Real.pi / 2) := Lv.launch_angle_boundaryWalk hcθ
  have hc₁ : c₁ = Cond.runChart κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j ω₁ :=
    (eq_launch_of_launches _ _ hcθ).2.2
  obtain ⟨b'', J'', h'', hp, hT, hfl⟩ := h₁ c₁ θ₁ hcθ
  subst hθ₁ hc₁
  have hex : ∃ bJ, p ω₁ bJ := ⟨(b'', J''), hp, h'', hT, hfl⟩
  exact Classical.epsilon_spec hex

end SB2

end InteractingSLE.Theorem14.SB.Lcd
