/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1LifeWord
import InteractingSLE.Spec.Supplement.GW1LawsCanon
import InteractingSLE.Spec.Supplement.StagedRegularize
import InteractingSLE.Spec.Supplement.BW1PropConfig
import InteractingSLE.Spec.Supplement.GW2ScheduleIdent

/-!
# Proposition BW1: the canonical counterflow of the conditional field after the first piece

Packet PROVE-BW1-LIFE. Proof of Proposition BW1 (`source/spec/p577-624.md` L845, p. 614): "Consequently the whole
conditional word is admissible […] Using LP11, construct the canonical counterflow coupled to that conditional field.
This construction uses no frontier theorem."

For the first piece of a staged history from the root `0` (angle `θ ∈ [−π/2, π/2]`, own stop `t`), on the event
that its stop `min t ζ` is finite:

* `ae_bwField_gff`: conditionally on the retained past `pastSigma … 1`, the field read in the chart right after the
  piece (`bwField`) is the GFF of the stop word `bwWord` (the staged law `Exist.StagedLaw.post_stage` at the first
  instruction, for a family that is regular at every sample);
* `isCfGoodWord_bwWord`: that word is admissible for the counterflow (`isCfGoodWord_stopWord`, the ambient bounds of
  the original counterflow word, GW1Conn);
* **`exists_condCounterflow_first`**: the canonical counterflow driver of that conditional field (Theorem 1.2
  jointly measurable in the word, R44, and Theorem 1.3: `GW1Laws.cfDrvOf`) is measurable, drives the conditional
  centred counterflow in the state chart (`SB.IsCondCounterflowDriverOn`), and almost surely on the event has an
  infinite lifetime and is continuous from `0`. The staged history need not be regular at every sample: the first
  piece is regularized (`StagedReg.regHist`), which changes neither the runs nor the regular conditional laws given the
  retained past, almost surely.

R48: BW1 serves Theorem 1.4 (Theorems 1.2–1.3 may be used); nothing here serves Theorems 1.2–1.3.
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

open Exist Exist.StagedLaw Exist.Staged Restart

/-! ### The post-piece field and word -/

section Defs

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} (spec : ExplSpec)

/-- The field read in the chart right after the first piece (the record chart of the piece, in the launch chart). -/
def bwField (h : Ω → DistOn upperHalfPlaneOpens) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) :
    DistOn upperHalfPlaneOpens :=
  recField κ (pastMap κ b jumps spec E 1 ω (Fin.last 0)) (flowField spec.1 0 (h ω))

/-- The word of the conditional law right after the first piece: the stop word of its record. -/
def bwWord (θ : ℝ) (c₀ : BoundaryWord) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : BoundaryWord :=
  stopWord κ (BoundaryWord.shiftW spec.1 c₀, θ, pastMap κ b jumps spec E 1 ω (Fin.last 0))

end Defs

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec} {θ : ℝ}
  {t : ℝ≥0∞} {rest : List Instr} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

omit [StandardBorelSpace Ω] in
theorem instrTime_zero (hp : spec.2.2 = Sum.inl (θ, t) :: rest) : instrTime spec 0 = t := by
  unfold instrTime; rw [hp]; rfl

omit [StandardBorelSpace Ω] in
theorem instrAngle_zero (hp : spec.2.2 = Sum.inl (θ, t) :: rest) : instrAngle spec 0 = θ := by
  unfold instrAngle; rw [hp]; rfl

omit [StandardBorelSpace Ω] in
theorem measurable_pastMap_one (hb : IsPiecewiseConstantBoundaryData b jumps) (hEm : ∀ j, Measurable (E j))
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) : Measurable (pastMap κ b jumps spec E 1) :=
  measurable_pastMap runMeasStatement hb spec (fun j _ => hEm j) (fun j _ => hreg j) 1 le_rfl

omit [StandardBorelSpace Ω] in
theorem measurable_pastMap_one_last (hb : IsPiecewiseConstantBoundaryData b jumps) (hEm : ∀ j, Measurable (E j))
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    Measurable fun ω => pastMap κ b jumps spec E 1 ω (Fin.last 0) :=
  (measurable_pi_apply (X := fun _ : Fin 1 => RecData) (Fin.last 0)).comp (measurable_pastMap_one hb hEm hreg)

omit mΩ [StandardBorelSpace Ω] in
theorem measurable_pastSigma_pastMap_one_last :
    Measurable[pastSigma κ b jumps spec E 1] fun ω => pastMap κ b jumps spec E 1 ω (Fin.last 0) := by
  rw [pastSigma_eq_comap]
  exact (measurable_pi_apply (X := fun _ : Fin 1 => RecData) (Fin.last 0)).comp
    (comap_measurable (pastMap κ b jumps spec E 1))

omit mΩ [StandardBorelSpace Ω] in
/-- The post-piece word is a function of the retained past. -/
theorem measurable_bwWord (c₀ : BoundaryWord) :
    Measurable[pastSigma κ b jumps spec E 1] (bwWord κ b jumps spec θ c₀ E) :=
  (measurable_stopWord κ).comp (measurable_const.prodMk (measurable_const.prodMk
    measurable_pastSigma_pastMap_one_last))

omit [StandardBorelSpace Ω] in
theorem measurable_bwField (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : Measurable h)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    Measurable (bwField κ b jumps spec h E) :=
  measurable_recField_comp κ (measurable_pastMap_one_last hb hEm hreg) ((measurable_flowField _ _).comp hh)

/-! ### The conditional law after the first piece -/

/-- **The conditional law after the first piece** (the staged law at the first instruction, `post_stage`). For a
family regular at every sample whose first stage is a conditional flow line: almost surely on the event of a finite
stop, the chart after the piece is conformal and reads `h` as `bwField`; and conditionally on the retained past
`bwField` is the GFF of the stop word `bwWord`. -/
theorem ae_bwField_gff (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hp : spec.2.2 = Sum.inl (θ, t) :: rest)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hok : StageOK κ b jumps P h spec E 0) {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps)
    (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) :
    (∀ᵐ ω ∂P, min t (E 0 ω).2 ≠ ⊤ →
      (BW1.stateChart (ExplState.run κ b jumps spec (fun j => E j ω) 1)).IsConformal ∧
      ContinuousOn (fun w => (BW1.stateChart (ExplState.run κ b jumps spec (fun j => E j ω) 1)).2.2
        ((BW1.stateChart (ExplState.run κ b jumps spec (fun j => E j ω) 1)).2.1 w)) QuantumZipper.H ∧
      IsChartTransport (BW1.stateChart (ExplState.run κ b jumps spec (fun j => E j ω) 1)) 1 0 (chiC κ) (h ω)
        (bwField κ b jumps spec h E ω)) ∧
    ∀ᵐ ω₀ ∂P, min t (E 0 ω₀).2 ≠ ⊤ →
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E 1) ω₀) (bwField κ b jumps spec h E)
        (bwWord κ b jumps spec θ c₀ E ω₀).fn (bwWord κ b jumps spec θ c₀ E ω₀).jumps := by
  have hW := GW1W.isStageWitness_zero (κ := κ) (spec := spec) (E := E) hh hc₀J hc₀
  have hpost := post_stage (GW1W.isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh (ℓ := 0)
    (fun j _ => hEm j) (fun j _ => hreg j) hok hW.1 hW.2.1 hW.2.2.1 hW.2.2.2
  have hl : ∀ ω, (ExplState.run κ b jumps spec (fun j => E j ω) (0 + 1)).2.2.2.1 0 ≠ none := fun ω => by
    rw [GW1.launches_run_one_of_cons κ b jumps spec hp]; exact Option.some_ne_none _
  have ht := instrTime_zero hp
  have hθ := instrAngle_zero hp
  have h𝒢 : pastSigma κ b jumps spec E 1 ≤ mΩ := (measurable_pastMap_one hb hEm hreg).comap_le
  refine ⟨?_, ?_⟩
  · filter_upwards [hpost.1, hW.2.2.1] with ω hgood hpath hfin
    have hfin' : min (instrTime spec 0) (E 0 ω).2 ≠ ⊤ := by rw [ht]; exact hfin
    have hg := hgood (hl ω) hfin'
    obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 (hl ω)
    obtain ⟨-, hrun, -⟩ := eq_launch_of_launches spec _ hcθ
    obtain ⟨hconf, hlift, hT⟩ := hpath (hl ω)
    have hreg0 := hreg 0 ω
    have hWc : Continuous fun x : ℝ => (retOf (instrTime spec 0) (E 0 ω)).1 x.toNNReal :=
      (continuous_retOf hreg0 hg).comp continuous_real_toNNReal
    have hW0 : (fun x : ℝ => (retOf (instrTime spec 0) (E 0 ω)).1 x.toNNReal) 0 = 0 := by
      change (E 0 ω).1 (min (((0 : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) (min (instrTime spec 0) (E 0 ω).2)).toNNReal = 0
      rw [Real.toNNReal_zero, ENNReal.coe_zero, min_eq_left (zero_le (a := min (instrTime spec 0) (E 0 ω).2)),
        ENNReal.toNNReal_zero]
      exact hreg0.2.1
    have hchart1 : (ExplState.run κ b jumps spec (fun j => E j ω) (0 + 1)).2.2.2.2.1 =
        (ExplState.run κ b jumps spec (fun j => E j ω) 0).2.2.2.2.1.loewner
          (fun x : ℝ => (retOf (instrTime spec 0) (E 0 ω)).1 x.toNNReal)
          ((min (instrTime spec 0) (E 0 ω).2).toNNReal : ℝ) := by
      rw [hrun]
      exact chart_launch _ _ _ _ _ hfin'
    have hZ : bwField κ b jumps spec h E ω =
        recField κ (recOf (instrTime spec 0) (E 0 ω)) (flowField spec.1 0 (h ω)) := by
      unfold bwField
      rw [pastMap_last_of_launch (hl ω)]
    refine ⟨?_, ?_, ?_⟩
    · change (ExplState.run κ b jumps spec (fun j => E j ω) (0 + 1)).2.2.2.2.1.IsConformal
      rw [hchart1]; exact hconf.loewner hWc hW0 (NNReal.coe_nonneg _)
    · change ContinuousOn (fun w => (ExplState.run κ b jumps spec (fun j => E j ω) (0 + 1)).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps spec (fun j => E j ω) (0 + 1)).2.2.2.2.1.2.1 w)) QuantumZipper.H
      rw [hchart1]; exact hconf.continuousOn_loewner_lift hlift hWc hW0 (NNReal.coe_nonneg _)
    · change IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) (0 + 1)).2.2.2.2.1 1 0 (chiC κ) (h ω)
        (bwField κ b jumps spec h E ω)
      rw [hchart1, InteractingSLE.Chart.loewner_eq_trans, ← recChart_eq_loewner hreg0 hg, hZ]
      exact IsChartTransport.trans hconf (isConformal_recChart _) hlift (continuousOn_recChart_lift _) hT
        (isChartTransport_recField κ _ _)
  · have hsort : ∀ᵐ ω ∂P, ω ∈ {ω | min t (E 0 ω).2 ≠ ⊤} → (bwWord κ b jumps spec θ c₀ E ω).IsSorted :=
      Eventually.of_forall fun ω _ => isSorted_stopWord κ _
    have hG : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ {ω | min t (E 0 ω).2 ≠ ⊤} →
        P[fun ω' => Complex.exp (Complex.I * (bwField κ b jumps spec h E ω' φ : ℂ)) |
          pastSigma κ b jumps spec E 1] ω = gaussCF (bwWord κ b jumps spec θ c₀ E ω) φ := by
      intro φ
      filter_upwards [hpost.2 φ] with ω hω hfin
      have hfin' : min (instrTime spec 0) (E 0 ω).2 ≠ ⊤ := by rw [ht]; exact hfin
      have h1 := hω (hl ω) hfin'
      rw [hθ] at h1
      exact h1
    exact ae_isGFFWithBoundaryData_condExpKernel h𝒢 hsort (measurable_bwField hb hh.1 hEm hreg) hG

/-! ### The canonical counterflow of the conditional field -/

section Canonical

variable (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (hκ : 0 < κ)

/-- **BW1's canonical relative driver**: the canonical centred counterflow driver (`GW1Laws.cfDrvOf`) of the
post-piece word and field. -/
def bwDrv (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (θ : ℝ) (c₀ : BoundaryWord)
    (h : Ω → DistOn upperHalfPlaneOpens) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (s : ℝ≥0) (ω : Ω) : ℝ :=
  (GW1Laws.cfDrvOf h12p hκ (bwWord κ b jumps spec θ c₀ E ω, bwField κ b jumps spec h E ω)).1 s

/-- **BW1's canonical relative lifetime**. -/
def bwLife (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (θ : ℝ) (c₀ : BoundaryWord)
    (h : Ω → DistOn upperHalfPlaneOpens) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  (GW1Laws.cfDrvOf h12p hκ (bwWord κ b jumps spec θ c₀ E ω, bwField κ b jumps spec h E ω)).2

omit [StandardBorelSpace Ω] in
theorem measurable_bwDrvLife (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : Measurable h)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (c₀ : BoundaryWord) :
    Measurable fun ω => GW1Laws.cfDrvOf h12p hκ (bwWord κ b jumps spec θ c₀ E ω, bwField κ b jumps spec h E ω) :=
  (GW1Laws.measurable_cfDrvOf h12p hκ).comp
    ((measurable_bwWord c₀).mono (measurable_pastMap_one hb hEm hreg).comap_le le_rfl |>.prodMk
      (measurable_bwField hb hh hEm hreg))

omit [StandardBorelSpace Ω] in
theorem measurable_bwDrv (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : Measurable h)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (c₀ : BoundaryWord) (s : ℝ≥0) :
    Measurable (bwDrv h12p hκ b jumps spec θ c₀ h E s) :=
  (measurable_pi_apply s).comp (measurable_fst.comp (measurable_bwDrvLife h12p hκ hb hh hEm hreg c₀))

omit [StandardBorelSpace Ω] in
theorem measurable_bwLife (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : Measurable h)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (c₀ : BoundaryWord) :
    Measurable (bwLife h12p hκ b jumps spec θ c₀ h E) :=
  measurable_snd.comp (measurable_bwDrvLife h12p hκ hb hh hEm hreg c₀)

omit mΩ [StandardBorelSpace Ω] in
/-- The event of a finite stop of the first piece is an event of the retained past. -/
theorem measurableSet_pastSigma_finStop (hp : spec.2.2 = Sum.inl (θ, t) :: rest) :
    MeasurableSet[pastSigma κ b jumps spec E 1] {ω | min t (E 0 ω).2 ≠ ⊤} := by
  have hl : ∀ ω, (ExplState.run κ b jumps spec (fun j => E j ω) (0 + 1)).2.2.2.1 0 ≠ none := fun ω => by
    rw [GW1.launches_run_one_of_cons κ b jumps spec hp]; exact Option.some_ne_none _
  have e : {ω | min t (E 0 ω).2 ≠ ⊤} =
      (fun ω => pastMap κ b jumps spec E 1 ω (Fin.last 0)) ⁻¹' ((fun r : RecData => r.2.1) ⁻¹' {⊤}ᶜ) := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, mem_compl_iff, mem_singleton_iff]
    rw [pastMap_last_of_launch (hl ω), instrTime_zero hp]
    rfl
  rw [e]
  exact measurable_pastSigma_pastMap_one_last ((measurable_fst.comp measurable_snd)
    (measurableSet_singleton (⊤ : ℝ≥0∞)).compl)

/-- **The conditional centred counterflow after the first piece, for a regular family** (BW1, p. 614: "Using LP11,
construct the canonical counterflow coupled to that conditional field"). Almost surely on the event of a finite stop,
under the regular conditional law given the retained past, the canonical driver `bwDrv` drives the centred
counterflow of the field read in the state chart, and its lifetime is infinite. -/
theorem ae_isCenteredCounterflowDriver_bw (h13 : Exist.Theorem13Statement.{u}) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hroot : spec.1 = 0) (hp : spec.2.2 = Sum.inl (θ, t) :: rest)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hok : StageOK κ b jumps P h spec E 0)
    {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hL : ∀ y, y < 0 → y ∉ jumps → b y + -(Real.pi / 2) * chiC κ < sleLambda κ)
    (hR : ∀ y, 0 < y → y ∉ jumps → -sleLambda κ < b y + Real.pi / 2 * chiC κ) :
    ∀ᵐ ω₀ ∂P, min t (E 0 ω₀).2 ≠ ⊤ →
      ∃ h' : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω, IsChartTransport (BW1.stateChart (ExplState.run κ b jumps spec (fun j => E j ω₀) 1)) 1 0 (chiC κ)
          (h ω) (h' ω)) ∧
        IsCenteredCounterflowDriver κ (condExpKernel P (pastSigma κ b jumps spec E 1) ω₀) h'
          (bwDrv h12p hκ b jumps spec θ c₀ h E) (bwLife h12p hκ b jumps spec θ c₀ h E) ∧
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E 1) ω₀), bwLife h12p hκ b jumps spec θ c₀ h E ω = ⊤ := by
  obtain ⟨hchart, hgff⟩ := ae_bwField_gff (θ := θ) hκ hb hh hp hEm hreg hok hc₀J hc₀
  have h𝒢 : pastSigma κ b jumps spec E 1 ≤ mΩ := (measurable_pastMap_one hb hEm hreg).comap_le
  have hM𝒢 := measurableSet_pastSigma_finStop (κ := κ) (b := b) (jumps := jumps) (E := E) hp
  -- the post-piece word is admissible for every record
  have hc₀w : BoundaryWord.shiftW spec.1 c₀ = c₀ := by
    rw [hroot]
    obtain ⟨n, p, v⟩ := c₀
    simp [BoundaryWord.shiftW]
  have hgood : ∀ ω, GW1Laws.IsCfGoodWord κ (bwWord κ b jumps spec θ c₀ E ω) := fun ω => by
    unfold bwWord
    rw [hc₀w]
    refine isCfGoodWord_stopWord hκ hκ4 hθ (fun y hy hyJ => ?_) (fun y hy hyJ => ?_) _
    · rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hL y hy hyJ
    · rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hR y hy hyJ
  filter_upwards [hchart, hgff, ae_ae_run_eq runMeasStatement hb spec (k := 1) (fun j _ => hEm j)
      (fun j _ => hreg j) (P := P), Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hchart,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒢 (measurable_bwWord (θ := θ) c₀),
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hM𝒢] with ω₀ hc₀' hg₀ hrunK hchK hwK hmK hfin
  set ν := condExpKernel P (pastSigma κ b jumps spec E 1) ω₀ with hν
  obtain ⟨hconf, hlift, -⟩ := hc₀' hfin
  set c := BW1.stateChart (ExplState.run κ b jumps spec (fun j => E j ω₀) 1) with hcdef
  set h' : Ω → DistOn upperHalfPlaneOpens := fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (h ω) with hh'def
  have hh' : ∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω) := fun ω =>
    Chart.isChartTransport_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift) 1 0 _ (h ω)
  have hh'm : Measurable h' := (Chart.measurable_chartTransport hconf 1 0 _).comp hh.1
  have hYe : bwField κ b jumps spec h E =ᵐ[ν] h' := by
    filter_upwards [hrunK, hchK, hmK hfin] with ω hr hc hm
    obtain ⟨-, -, hT⟩ := hc hm
    rw [hr] at hT
    exact hT.unique hconf (hh' ω)
  have hgff' : IsGFFWithBoundaryData ν h' (bwWord κ b jumps spec θ c₀ E ω₀).fn
      (bwWord κ b jumps spec θ c₀ E ω₀).jumps :=
    isGFFWithBoundaryData_congr_ae (hg₀ hfin) hh'm hYe
  have hae : ∀ᵐ ω ∂ν, bwLife h12p hκ b jumps spec θ c₀ h E ω =
        (GW1Laws.cfDrvOf h12p hκ (bwWord κ b jumps spec θ c₀ E ω₀, h' ω)).2 ∧
      ∀ s, bwDrv h12p hκ b jumps spec θ c₀ h E s ω =
        (GW1Laws.cfDrvOf h12p hκ (bwWord κ b jumps spec θ c₀ E ω₀, h' ω)).1 s := by
    filter_upwards [hwK, hYe] with ω hw hy
    unfold bwDrv bwLife
    rw [hw, hy]
    exact ⟨rfl, fun _ => rfl⟩
  obtain ⟨hs, -, -⟩ := hgood ω₀
  obtain ⟨-, hgL, hgR⟩ := hgood ω₀
  refine ⟨h', hh', GW1Laws.isCenteredCounterflowDriver_of_ae_cfDrvOf h12p hκ h13 hs hgff'
    (measurable_bwDrv h12p hκ hb hh.1 hEm hreg c₀) (measurable_bwLife h12p hκ hb hh.1 hEm hreg c₀) hae, ?_⟩
  filter_upwards [hae, GW1Laws.ae_cfDrvOf_snd_eq_top h12p hκ h13 hs hgL hgR hgff'] with ω h1 h2
  rw [h1.1, h2]

end Canonical

/-! ### From a staged history: regularizing the first piece -/

section Reg

/-- **The first stage of the regularized history is again a conditional flow line** (the regularized driver agrees
with the piece before its lifetime almost surely; the past before the first instruction is trivial). -/
theorem stageOK_regHist_zero (hS : IsStagedHistory κ b jumps P h spec E) :
    StageOK κ b jumps P h spec (StagedReg.regHist spec E) 0 := by
  have hm' : ∀ k, Measurable (StagedReg.regHist spec E k) := StagedReg.measurable_regHist hS.1
  have hpast : pastSigma κ b jumps spec (StagedReg.regHist spec E) 0 = pastSigma κ b jumps spec E 0 := by
    rw [pastSigma_zero, pastSigma_zero]
  filter_upwards [hS.2.2.2 0] with ω₀ h4 c θ' hl
  have he : ExplState.run κ b jumps spec (fun j => E j ω₀) 0 =
      ExplState.run κ b jumps spec (fun j => StagedReg.regHist spec E j ω₀) 0 := rfl
  have hl' : (ExplState.run κ b jumps spec (fun j => E j ω₀) (0 + 1)).2.2.2.1 0 = some (c, θ') := by
    rw [launches_run_succ_of_run_eq spec he]; exact hl
  obtain ⟨b', jumps', h', hb', htr, hfl⟩ := h4 c θ' hl'
  refine ⟨b', jumps', h', hb', htr, ?_⟩
  rw [hpast]
  have hζ : (fun ω => (StagedReg.regHist spec E 0 ω).2) = fun ω => (E 0 ω).2 :=
    funext fun ω => StagedReg.regHist_snd 0 ω
  rw [hζ]
  refine StagedReg.isFlowLineDriver_congr_ae hfl
    (fun s => (measurable_pi_apply s).comp (measurable_fst.comp (hm' 0))) ?_
  obtain ⟨_, _, _, _, _, _, hC⟩ := hfl
  filter_upwards [hC.1.2.2.2.2] with ω hp
  exact ⟨StagedReg.regularize_zero _ hp.1, fun s hs => StagedReg.regularize_eq_of_lt _ hp.1 hp.2.2.2.1 hs⟩

/-- **The regularized history runs through the same first state**, almost surely (the first piece is almost surely
continuous from `0` through its stop, `GW1P.ae_pieceRegular_first`, and a launch only sees its retained datum). -/
theorem ae_run_one_regHist (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hS : IsStagedHistory κ b jumps P h spec E) (hroot : spec.1 = 0) (hp : spec.2.2 = Sum.inl (θ, t) :: rest) :
    ∀ᵐ ω ∂P, ExplState.run κ b jumps spec (fun j => StagedReg.regHist spec E j ω) 1 =
      ExplState.run κ b jumps spec (fun j => E j ω) 1 := by
  filter_upwards [GW1P.ae_pieceRegular_first h13 hκ hb hh hS hroot hp] with ω hω
  have hl := GW1.launches_run_one_of_cons κ b jumps spec hp
  obtain ⟨-, h1, -⟩ := eq_launch_of_launches spec (fun j => StagedReg.regHist spec E j ω) (hl _)
  obtain ⟨-, h2, -⟩ := eq_launch_of_launches spec (fun j => E j ω) (hl _)
  change ExplState.run κ b jumps spec (fun j => StagedReg.regHist spec E j ω) (0 + 1) =
    ExplState.run κ b jumps spec (fun j => E j ω) (0 + 1)
  rw [h1, h2]
  change ExplState.launch (ExplState.run κ b jumps spec (fun j => E j ω) 0) 0
      (StagedReg.regularize (instrTime spec 0) (E 0 ω)) θ (instrTime spec 0) =
    ExplState.launch (ExplState.run κ b jumps spec (fun j => E j ω) 0) 0 (E 0 ω) θ (instrTime spec 0)
  rw [← launch_canonDrv _ _ (StagedReg.regularize (instrTime spec 0) (E 0 ω)),
    StagedReg.canonDrv_regularize hω.1 hω.2.1, launch_canonDrv]

/-- **The regularized history has the same regular conditional laws given the retained past**, almost surely. -/
theorem ae_condExpKernel_regHist_eq (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hS : IsStagedHistory κ b jumps P h spec E) (hroot : spec.1 = 0) (hp : spec.2.2 = Sum.inl (θ, t) :: rest) :
    ∀ᵐ ω ∂P, condExpKernel P (pastSigma κ b jumps spec (StagedReg.regHist spec E) 1) ω =
      condExpKernel P (pastSigma κ b jumps spec E 1) ω := by
  have hm' := measurable_pastMap_one (κ := κ) (spec := spec) (E := StagedReg.regHist spec E) hb
    (StagedReg.measurable_regHist (spec := spec) hS.1) (fun j ω => StagedReg.isRegularDriver_regHist (spec := spec) j ω)
  have hm : Measurable (pastMap κ b jumps spec E 1) := Measurable.of_comap_le (hS.2.1 1)
  have hae : pastMap κ b jumps spec (StagedReg.regHist spec E) 1 =ᵐ[P] pastMap κ b jumps spec E 1 := by
    filter_upwards [ae_run_one_regHist h13 hκ hb hh hS hroot hp] with ω hω
    unfold pastMap
    rw [hω]
  rw [pastSigma_eq_comap, pastSigma_eq_comap]
  exact StagedReg.ae_condExpKernel_eq_of_ae_eq hm' hm hae

end Reg

/-! ### The conditional half of Proposition BW1 -/

/-- **The conditional half of Proposition BW1 for the first piece, with the canonical driver explicit** (p. 614):
for `0 < κ < 4`, a GFF `h` whose centred counterflow has an infinite lifetime, a staged history whose first
instruction is a flow of angle `θ ∈ [−π/2, π/2]` from the root `0`, and a word `c₀` of the data: the canonical driver
`bwDrv` of the regularized history is measurable and, almost surely on the event of a finite stop of the first piece,
conditionally on the retained past it drives the centred counterflow of the field read in the state chart
(`SB.IsCondCounterflowDriverOn`), with `bwLife = ∞`, `bwDrv` continuous and `bwDrv 0 = 0`. -/
theorem condCounterflow_first (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hroot : spec.1 = 0)
    (hp : spec.2.2 = Sum.inl (θ, t) :: rest) (hS : IsStagedHistory κ b jumps P h spec E) {c₀ : BoundaryWord}
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) :
    (∀ s, Measurable (bwDrv h12p hκ b jumps spec θ c₀ h (StagedReg.regHist spec E) s)) ∧
      Measurable (bwLife h12p hκ b jumps spec θ c₀ h (StagedReg.regHist spec E)) ∧
      SB.IsCondCounterflowDriverOn κ (pastSigma κ b jumps spec E 1) P {ω | min t (E 0 ω).2 ≠ ⊤} h
        (fun ω => BW1.stateChart (ExplState.run κ b jumps spec (fun j => E j ω) 1))
        (bwDrv h12p hκ b jumps spec θ c₀ h (StagedReg.regHist spec E))
        (bwLife h12p hκ b jumps spec θ c₀ h (StagedReg.regHist spec E)) ∧
      ∀ᵐ ω ∂P, min t (E 0 ω).2 ≠ ⊤ → bwLife h12p hκ b jumps spec θ c₀ h (StagedReg.regHist spec E) ω = ⊤ ∧
        Continuous (fun s => bwDrv h12p hκ b jumps spec θ c₀ h (StagedReg.regHist spec E) s ω) ∧
        bwDrv h12p hκ b jumps spec θ c₀ h (StagedReg.regHist spec E) 0 ω = 0 := by
  obtain ⟨hL, hR⟩ := GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀) hκ hκ4 hb hh hcf hζ'
  set E' := StagedReg.regHist spec E with hE'
  have hEm' : ∀ j, Measurable (E' j) := StagedReg.measurable_regHist hS.1
  have hreg' : ∀ j ω, IsRegularDriver (E' j ω) := fun j ω => StagedReg.isRegularDriver_regHist j ω
  have hsnd : ∀ ω, (E' 0 ω).2 = (E 0 ω).2 := fun ω => StagedReg.regHist_snd 0 ω
  have hmain := ae_isCenteredCounterflowDriver_bw h12p hκ h13 hκ4 hb hh hθ hroot hp hEm' hreg'
    (stageOK_regHist_zero hS) hc₀J hc₀ hL hR
  have hrun := ae_run_one_regHist h13 hκ hb hh hS hroot hp
  have hK := ae_condExpKernel_regHist_eq h13 hκ hb hh hS hroot hp
  have h𝒢 : pastSigma κ b jumps spec E' 1 ≤ mΩ := (measurable_pastMap_one hb hEm' hreg').comap_le
  have hM𝒢 : MeasurableSet[pastSigma κ b jumps spec E' 1] {ω | min t (E' 0 ω).2 ≠ ⊤} :=
    measurableSet_pastSigma_finStop hp
  have hlm := measurable_bwLife h12p hκ (θ := θ) hb hh.1 hEm' hreg' c₀ (spec := spec)
  refine ⟨measurable_bwDrv h12p hκ hb hh.1 hEm' hreg' c₀, hlm, ?_, ?_⟩
  · filter_upwards [hmain, hrun, hK] with ω₀ hm hr hk hfin
    have hfin' : min t (E' 0 ω₀).2 ≠ ⊤ := by rw [hsnd]; exact hfin
    obtain ⟨h', hh', hcd, -⟩ := hm hfin'
    refine ⟨h', ?_, ?_⟩
    · rw [← hr]; exact hh'
    · rw [← hk]; exact hcd
  · have htop : ∀ᵐ ω ∂P, ω ∈ {ω | min t (E' 0 ω).2 ≠ ⊤} →
        ω ∈ {ω | bwLife h12p hκ b jumps spec θ c₀ h E' ω = ⊤} :=
      GW2Schedule.ae_of_ae_condExpKernel_on h𝒢 hM𝒢 (hlm (measurableSet_singleton ⊤))
        (hmain.mono fun ω₀ hm hfin => by obtain ⟨_, _, _, h3⟩ := hm hfin; exact h3)
    filter_upwards [htop] with ω hω hfin
    have hfin' : min t (E' 0 ω).2 ≠ ⊤ := by rw [hsnd]; exact hfin
    have hζ := hω hfin'
    obtain ⟨hc, h0⟩ := GW1Laws.cfDrvOf_regular h12p hκ
      (bwWord κ b jumps spec θ c₀ E' ω, bwField κ b jumps spec h E' ω)
    refine ⟨hζ, ?_, h0⟩
    have hζ' : (GW1Laws.cfDrvOf h12p hκ (bwWord κ b jumps spec θ c₀ E' ω, bwField κ b jumps spec h E' ω)).2 = ⊤ :=
      hζ
    rw [hζ'] at hc
    have huniv : {s : ℝ≥0 | (s : ℝ≥0∞) < ⊤} = univ := eq_univ_of_forall fun s => ENNReal.coe_lt_top
    rw [huniv] at hc
    exact continuousOn_univ.1 hc

/-- **The conditional half of Proposition BW1 for the first piece** (existence form of `condCounterflow_first`). -/
theorem exists_condCounterflow_first (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hroot : spec.1 = 0)
    (hp : spec.2.2 = Sum.inl (θ, t) :: rest) (hS : IsStagedHistory κ b jumps P h spec E) :
    ∃ (Wr : ℝ≥0 → Ω → ℝ) (ζr : Ω → ℝ≥0∞), (∀ s, Measurable (Wr s)) ∧ Measurable ζr ∧
      SB.IsCondCounterflowDriverOn κ (pastSigma κ b jumps spec E 1) P {ω | min t (E 0 ω).2 ≠ ⊤} h
        (fun ω => BW1.stateChart (ExplState.run κ b jumps spec (fun j => E j ω) 1)) Wr ζr ∧
      ∀ᵐ ω ∂P, min t (E 0 ω).2 ≠ ⊤ → ζr ω = ⊤ ∧ Continuous (fun s => Wr s ω) ∧ Wr 0 ω = 0 := by
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  exact ⟨_, _, condCounterflow_first h12p h13 hT13₀ hκ hκ4 hb hh hcf hζ' hθ hroot hp hS hc₀J hc₀⟩

end InteractingSLE.Theorem14.BW1Life
