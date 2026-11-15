/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LcdCode
import InteractingSLE.Spec.Supplement.KernelTower2

/-!
# SB2(2)'s conditional half: a conditional flow line in a finer σ-algebra suffices

Packet PROVE-T14-SB2LCOND. The source proves the identification of the relative stages with the retained first
history, its exterior projection and the erased initial portion all in the conditioning (supplement pp. 631–632:
"Retain the full marked first history and the orthogonal field projection outside `D_A`"; "even the full erased
history, its entry germ and stopping flags leave the same conditional field in `D_A`"). This file shows that such a
finer conditioning is enough:

* **`ae_codeMatch_of_condFlowLine_le`** (generic): if a σ-algebra `𝒢'` contains the retained past of stage `k`, an event
  `F'` covers the launch event almost surely, and given `𝒢'` (for almost every sample of `F'`) the stage is the
  angle-`θ₀` flow line of the field read in the run chart with the stage word `β` of a witness `(β, Y)` (this contains
  the erasure clause: given `𝒢'` the chart field is still the GFF of `β`), then almost surely on the launch event the
  stage driver matches the canonical code of `(β, Y)` (Theorem 1.2 under each `𝒢'`-conditional law, then integrated
  back);
* the SB2(2) input in this form, **`SB2LowerRelFinerStatement`**, and **`sb2LowerRelStageCondStatement_of_finer`**:
  with `SB2LcdCode`, the conditional half follows from Theorems 1.2–1.3 and the finer conditional flow lines.

* **`ae_codeMatch_of_condFlowLine_aeSigma`**: the same when `𝒢'` contains the retained past only up to null sets.

Taking `𝒢'` the relative past itself shows the finer form is also implied by the conditional half, so it loses
nothing. Its point: `𝒢'` may be a σ-algebra fixed BEFORE `ω₀` (the upper past, the actual lower walk's past and the
erased history), for which the nested-kernel tower identity (`SB2LkTower`) transfers `P`-level kernels to `Q`; the
relative past of `EL` (chosen after `ω₀`) only has to be contained in it up to `Q`-null sets.

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

/-- **The code match from a conditional flow line in a finer σ-algebra.** -/
theorem ae_codeMatch_of_condFlowLine_le (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (θ₀ : ℝ) {k : ℕ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (𝒢' : {m : MeasurableSpace Ω // m ≤ mΩ}) (hpast : pastSigma κ b jumps spec E k ≤ 𝒢'.1)
    {F' : Set Ω}
    (hcov : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none → ω ∈ F')
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y)
    (hcfl : SB.IsCondFlowLineDriverOn κ θ₀ 𝒢'.1 P F' h (Cond.runChart κ b jumps spec E k)
      (fun ω => (β ω).fn) (fun ω => (β ω).jumps) (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2)) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      IsDriverCodeMatch (driverCode h12p hκ θ₀ (β ω, Y ω)) (fun t => (E k ω).1 t) (E k ω).2 := by
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := hpast.trans 𝒢'.2
  have hβm : Measurable β := hW.1.mono h𝒢 le_rfl
  have hl : MeasurableSet {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} :=
    measurableSet_launch_self runMeasStatement hb (fun j _ => hEm j) (fun j _ => hreg j)
  have hmatch : MeasurableSet {ω | IsDriverCodeMatch (driverCode h12p hκ θ₀ (β ω, Y ω))
      (fun t => (E k ω).1 t) (E k ω).2} :=
    Cond.measurableSet_driverCodeMatch_self ((measurable_driverCode h12p hκ θ₀).comp (hβm.prodMk hW.2.1))
      (fun t => (measurable_pi_apply t).comp (measurable_fst.comp (hEm k))) (measurable_snd.comp (hEm k))
  have hS : MeasurableSet ({ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none}ᶜ ∪
      {ω | IsDriverCodeMatch (driverCode h12p hκ θ₀ (β ω, Y ω)) (fun t => (E k ω).1 t) (E k ω).2}) :=
    hl.compl.union hmatch
  have hae := Sec5.Lemma56Stages.ae_of_ae_condExpKernel (μ := P) 𝒢'.2 hS ?_
  · filter_upwards [hae] with ω hω hlω
    rcases hω with hω | hω
    · exact absurd hlω hω
    · exact hω
  filter_upwards [hcfl, hcov, Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) 𝒢'.2 hW.2.2.1,
    CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b) (jumps := jumps) spec (fun j _ => hreg j) 𝒢'.2
      hpast,
    Sec7.Lemma725RefK2.ae_ae_condExpKernel_eq_self (P := P) 𝒢'.2 (hW.1.mono hpast le_rfl), hW.2.2.1]
    with ω₀ hc₀ hcov₀ hpk₀ hrun₀ hβ₀ hp₀
  by_cases hl₀ : (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none
  · obtain ⟨-, h', hT, hfl⟩ := hc₀ (hcov₀ hl₀)
    obtain ⟨hconf, -, -⟩ := hp₀ hl₀
    filter_upwards [Cond.ae_driverCodeMatch_of_isFlowLineDriver_univ h12p hκ θ₀ h13 (β ω₀) hfl, hpk₀, hrun₀, hβ₀]
      with ω hmω hpω hrunω hβω
    by_cases hlω : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none
    · right
      obtain ⟨-, -, hYω⟩ := hpω hlω
      have hYω' : IsChartTransport (Cond.runChart κ b jumps spec E k ω₀) 1 0 (chiC κ) (h ω) (Y ω) := by
        change IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω₀) k).2.2.2.2.1 1 0 (chiC κ) (h ω)
          (Y ω)
        rw [← hrunω]
        exact hYω
      have hY : Y ω = h' ω := IsChartTransport.unique hconf hYω' (hT ω)
      change IsDriverCodeMatch (driverCode h12p hκ θ₀ (β ω, Y ω)) (fun t => (E k ω).1 t) (E k ω).2
      rw [hβω, hY]
      exact hmω
    · left
      exact hlω
  · filter_upwards [hrun₀] with ω hrunω
    left
    intro hlω
    exact hl₀ (by rw [← launches_run_succ_of_run_eq spec hrunω]; exact hlω)

/-- **The same with the retained past contained in the finer σ-algebra only up to null sets** (a σ-algebra fixed in
advance may be used without completing it): replace `𝒢'` by `𝒢' ⊔ pastSigma k`, whose regular conditional laws agree
with those of `𝒢'` almost everywhere (`KernelTower.ae_condExpKernel_eq_of_le_aeSigma`). -/
theorem ae_codeMatch_of_condFlowLine_aeSigma (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (θ₀ : ℝ) {k : ℕ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (𝒢' : {m : MeasurableSpace Ω // m ≤ mΩ}) (hpast : pastSigma κ b jumps spec E k ≤ LocalSets.aeSigma 𝒢'.1 P)
    {F' : Set Ω}
    (hcov : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none → ω ∈ F')
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y)
    (hcfl : SB.IsCondFlowLineDriverOn κ θ₀ 𝒢'.1 P F' h (Cond.runChart κ b jumps spec E k)
      (fun ω => (β ω).fn) (fun ω => (β ω).jumps) (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2)) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      IsDriverCodeMatch (driverCode h12p hκ θ₀ (β ω, Y ω)) (fun t => (E k ω).1 t) (E k ω).2 := by
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := by
    rw [pastSigma_eq_comap]
    exact (measurable_pastMap runMeasStatement hb spec (fun j _ => hEm j) (fun j _ => hreg j) k le_rfl).comap_le
  set 𝒢'' : {m : MeasurableSpace Ω // m ≤ mΩ} := ⟨𝒢'.1 ⊔ pastSigma κ b jumps spec E k, sup_le 𝒢'.2 h𝒢⟩
    with h𝒢''
  have hker : ∀ᵐ ω ∂P, condExpKernel P 𝒢'.1 ω = condExpKernel P 𝒢''.1 ω :=
    KernelTower.ae_condExpKernel_eq_of_le_aeSigma 𝒢'.2 𝒢''.2
      ((le_sup_left : 𝒢'.1 ≤ 𝒢''.1).trans (LocalSets.le_aeSigma _ P))
      (sup_le (LocalSets.le_aeSigma _ P) hpast)
  refine ae_codeMatch_of_condFlowLine_le h12p h13 hκ θ₀ hb hEm hreg 𝒢'' le_sup_right hcov hW ?_
  filter_upwards [hcfl, hker] with ω₀ h1 h2 hF
  rw [← h2]
  exact h1 hF

end Generic

/-! ### SB2(2): the conditional half from finer conditional flow lines -/

section SB2

open Supp9B Lx Lu Leaf FlowDilate Sec4

/-- **The finer conditional flow lines at one launch**: for `m = −e_R`, every measurable family `EL` of drivers, regular
at every sample, whose relative walk carries the actual tail's lift almost surely under the retained kernel `Q`, every
stage `j` and every witness `(β, Y)` of the stage's conditional law given the relative past: there are a σ-algebra `𝒢'`
containing the relative past of stage `j` up to `Q`-null sets and an event `F'` covering the launch event `Q`-almost
surely such that, given `𝒢'` (for `Q`-almost every sample of `F'`), the stage is the angle-`(−π/2)` flow line of the
conditional field `affField m h'` read in the run chart of stage `j`, with the stage word `β` (the erasure clause: the
finer conditioning leaves the same conditional field). -/
def RelStageFiner (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ)
    (h' : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
    (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
    (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
        Lf.IsTailLiftOf c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀
          (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω)) →
    ∀ (j : ℕ) (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ (affData 1 m b') (affJumps 1 m J')
        (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
        (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL j β Y →
      ∃ (𝒢' : {m' : MeasurableSpace Ω // m' ≤ mΩ}) (F' : Set Ω),
        pastSigma κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j ≤
          LocalSets.aeSigma 𝒢'.1 (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀) ∧
        (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
          (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
            (j + 1)).2.2.2.1 j ≠ none → ω ∈ F') ∧
        SB.IsCondFlowLineDriverOn κ (-(Real.pi / 2)) 𝒢'.1
          (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀) F'
          (fun ω => affField m one_pos (h' ω))
          (Cond.runChart κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j)
          (fun ω => (β ω).fn) (fun ω => (β ω).jumps) (fun t ω => (EL j ω).1 t) (fun ω => (EL j ω).2)

/-- **Named input: SB2(2)'s finer conditional flow lines at the later launches** (per stage). -/
def SB2LowerRelFinerStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → RelStageFiner κ b jumps P E u l k ω₀ c b' J' h'

/-- The finer conditional flow lines give the pathwise identification. -/
theorem sb2LowerRelCodeStatement_of_finer (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hfin : SB2LowerRelFinerStatement.{u}) : SB2LowerRelCodeStatement.{u} h12p := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hfin κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft]
    with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk hκ' m hm EL hELm hELr hlift j β Y hW
  obtain ⟨𝒢', F', hpast, hcov, hcfl⟩ :=
    h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hlift j β Y hW
  exact ae_codeMatch_of_condFlowLine_aeSigma h12p h13 hκ' (-(Real.pi / 2))
    (isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb') hELm hELr 𝒢' hpast hcov hW hcfl

/-- **SB2(2)'s conditional half from the finer conditional flow lines** (and Theorems 1.2–1.3). -/
theorem sb2LowerRelStageCondStatement_of_finer (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (hfin : SB2LowerRelFinerStatement.{u}) :
    Lk.SB2LowerRelStageCondStatement.{u} :=
  sb2LowerRelStageCondStatement_of_code h12p h13 (sb2LowerRelCodeStatement_of_finer h12p h13 hfin)

end SB2

end InteractingSLE.Theorem14.SB.Lcd
