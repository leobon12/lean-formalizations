/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfPa
import InteractingSLE.Spec.Supplement.GW1ActiveLaw
import InteractingSLE.Spec.Supplement.GW2RdHitSet
import InteractingSLE.Spec.Supplement.SBLuDense
import InteractingSLE.Spec.Supplement.SB2WdInd
import InteractingSLE.Spec.Sec7.Lemma725RefK2

/-!
# A launched piece of the walk avoids the forbidden set of its word, almost surely

Packet PROVE-T14-SB2WORD (round 3, the junction fact of E7). At a launch `ℓ` of the right walk with a stage witness
`β`, almost surely the chosen trace `trOf (E ℓ ω)` does not visit `forb κ θ (β ω)` before its lifetime and the seed
right weight of `β ω` exceeds `−2` when the lifetime is positive (`ae_stage_avoid`):

* under the regular conditional law given the retained past the piece is the flow line of the field of word `β ω₀`
  (`ae_isFlowLineDriver_stage_gff`, `ae_isFlowLineDriver_stage` with the field law exported), so `ae_avoid_forb` and
  `Supp9.ae_seedWeights_of_isFlowLine` apply, with the word frozen (`ae_ae_condExpKernel_eq_self`);
* the event is measurable through the atoms of `forb` visited at rational times (`BadVisit`, `badVisit_iff`) and a
  rational reading of the seed weight (`seedOK_iff`), then transferred (`Lemma56Stages.ae_of_ae_condExpKernel`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.SB.Wf

open Exist Exist.StagedLaw Exist.Staged Restart GW1W LQGMetric
open PiecewiseConstantBoundaryData (rightLim leftLim)

/-! ### The seed weight, read at a rational point -/

/-- The seed right weight of a word exceeds `−2`. -/
def SeedOK (κ θ : ℝ) (c : BoundaryWord) : Prop := -2 < Sec4.cumWeightRight κ (rightLim c.fn 0 + θ * chiC κ)

theorem rightLim_zero_eq_of_noPos {c : BoundaryWord} {q : ℝ} (hq : 0 < q)
    (hno : ∀ j < c.1, ¬ (0 < c.2.1 j ∧ c.2.1 j < q)) : rightLim c.fn 0 = c.fn q := by
  refine Sec4.rightLim_eq_of_forall (a := q) hq fun t ht => ?_
  have hidx : c.index t = c.index q :=
    index_eq_of_noPos ht.2.le fun j hj hj' => hno j hj ⟨lt_of_lt_of_le ht.1 hj'.1, hj'.2⟩
  unfold BoundaryWord.fn
  rw [hidx]

theorem seedOK_iff {κ θ : ℝ} {c : BoundaryWord} : SeedOK κ θ c ↔ ∃ q : ℚ, 0 < (q : ℝ) ∧
    (∀ j < c.1, ¬ (0 < c.2.1 j ∧ c.2.1 j < q)) ∧ -2 < Sec4.cumWeightRight κ (c.fn q + θ * chiC κ) := by
  constructor
  · intro hs
    obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem c.jumps 0
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (0 : ℝ) < δ by linarith)
    have hno : ∀ j < c.1, ¬ (0 < c.2.1 j ∧ c.2.1 j < q) := fun j hj hj' =>
      (hδJ _ (BoundaryWord.mem_jumps.2 ⟨j, hj, rfl⟩)).1 ⟨hj'.1, by rw [zero_add]; linarith [hj'.2]⟩
    refine ⟨q, hq1, hno, ?_⟩
    rw [← rightLim_zero_eq_of_noPos hq1 hno]
    exact hs
  · rintro ⟨q, hq, hno, hw⟩
    unfold SeedOK
    rw [rightLim_zero_eq_of_noPos hq hno]
    exact hw

theorem measurableSet_seedOK (κ θ : ℝ) : MeasurableSet {c : BoundaryWord | SeedOK κ θ c} := by
  have hno : ∀ q : ℚ, MeasurableSet {c : BoundaryWord | ∀ j < c.1, ¬ (0 < c.2.1 j ∧ c.2.1 j < q)} := by
    intro q
    have : {c : BoundaryWord | ∀ j < c.1, ¬ (0 < c.2.1 j ∧ c.2.1 j < q)} =
        ⋂ j : ℕ, ({c : BoundaryWord | c.1 ≤ j} ∪ ({c | c.2.1 j ≤ 0} ∪ {c | (q : ℝ) ≤ c.2.1 j})) := by
      ext c
      simp only [mem_ofPred_eq, mem_iInter, mem_union, not_and, not_lt]
      refine ⟨fun h j => ?_, fun h j hj h1 => ?_⟩
      · by_cases hj : j < c.1
        · by_cases h1 : 0 < c.2.1 j
          · exact Or.inr (Or.inr (h j hj h1))
          · exact Or.inr (Or.inl (not_lt.1 h1))
        · exact Or.inl (not_lt.1 hj)
      · rcases h j with h' | h' | h'
        · exact absurd hj (not_lt.2 h')
        · exact absurd h1 (not_lt.2 h')
        · exact h'
    rw [this]
    exact MeasurableSet.iInter fun j => (measurable_fst (measurableSet_Iic (a := j))).union
      ((measurableSet_le (measurable_position j) measurable_const).union
        (measurableSet_le measurable_const (measurable_position j)))
  have hR : ∀ q : ℚ, Measurable fun c : BoundaryWord => Sec4.cumWeightRight κ (c.fn q + θ * chiC κ) := by
    intro q
    unfold Sec4.cumWeightRight
    exact (((Supp7.measurable_boundaryWord_fn _).add_const _).div_const _).sub_const _
  have : {c : BoundaryWord | SeedOK κ θ c} = ⋃ q : ℚ, ({_c : BoundaryWord | 0 < (q : ℝ)} ∩
      ({c | ∀ j < c.1, ¬ (0 < c.2.1 j ∧ c.2.1 j < q)} ∩
        {c | -2 < Sec4.cumWeightRight κ (c.fn q + θ * chiC κ)})) := by
    ext c
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    exact seedOK_iff
  rw [this]
  exact MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter ((hno q).inter
    (measurableSet_lt measurable_const (hR q)))

/-! ### Visiting an atom of the forbidden set -/

/-- **Some atom of the forbidden set is visited before `T`** (rational reading). -/
def BadVisit (κ θ : ℝ) (c : BoundaryWord) (Γ : ℝ≥0 → ℂ) (T : ℝ≥0∞) : Prop :=
  (∃ a₁ a₂ : ℚ, predR κ θ c a₁ a₂ ∧ visitBefore Γ T (atomI a₁ a₂)) ∨
    (∃ a₁ a₂ : ℚ, predL κ θ c a₁ a₂ ∧ visitBefore Γ T (atomI a₁ a₂)) ∨
    (∃ i, predJL c i ∧ visitBefore Γ T {((c.2.1 i : ℝ) : ℂ)}) ∨
    (∃ i, predJR κ θ c i ∧ visitBefore Γ T {((c.2.1 i : ℝ) : ℂ)})

theorem atomI_nonempty {a₁ a₂ : ℚ} (h : (a₁ : ℝ) < a₂) : (atomI a₁ a₂).Nonempty :=
  ⟨((a₁ : ℝ) : ℂ), (a₁ : ℝ), ⟨le_rfl, h.le⟩, rfl⟩

/-- **For a path continuous before `T`, a bad visit is a visit of the forbidden set.** -/
theorem badVisit_iff {κ θ : ℝ} {c : BoundaryWord} {Γ : ℝ≥0 → ℂ} {T : ℝ≥0∞}
    (hΓ : ContinuousOn Γ {t | (t : ℝ≥0∞) < T}) :
    BadVisit κ θ c Γ T ↔ ∃ t : ℝ≥0, (t : ℝ≥0∞) < T ∧ Γ t ∈ forb κ θ c := by
  constructor
  · rintro (⟨a₁, a₂, hp, hv⟩ | ⟨a₁, a₂, hp, hv⟩ | ⟨i, hp, hv⟩ | ⟨i, hp, hv⟩)
    · obtain ⟨t, ht, hm⟩ := (visitBefore_iff hΓ (isClosed_atomI a₁ a₂) (atomI_nonempty hp.2.1)).1 hv
      exact ⟨t, ht, atom_subset_forb_R hp hm⟩
    · obtain ⟨t, ht, hm⟩ := (visitBefore_iff hΓ (isClosed_atomI a₁ a₂) (atomI_nonempty hp.2.1)).1 hv
      exact ⟨t, ht, atom_subset_forb_L hp hm⟩
    · obtain ⟨t, ht, hm⟩ := (visitBefore_iff hΓ isClosed_singleton (singleton_nonempty _)).1 hv
      rw [mem_singleton_iff] at hm
      exact ⟨t, ht, hm ▸ mem_forb_JL hp⟩
    · obtain ⟨t, ht, hm⟩ := (visitBefore_iff hΓ isClosed_singleton (singleton_nonempty _)).1 hv
      rw [mem_singleton_iff] at hm
      exact ⟨t, ht, hm ▸ mem_forb_JR hp⟩
  · rintro ⟨t, ht, hm⟩
    rcases exists_atom_of_mem_forb hm with ⟨a₁, a₂, hp, hz⟩ | ⟨a₁, a₂, hp, hz⟩ | ⟨i, hp, hz⟩ | ⟨i, hp, hz⟩
    · exact Or.inl ⟨a₁, a₂, hp, (visitBefore_iff hΓ (isClosed_atomI a₁ a₂) (atomI_nonempty hp.2.1)).2
        ⟨t, ht, hz⟩⟩
    · exact Or.inr (Or.inl ⟨a₁, a₂, hp, (visitBefore_iff hΓ (isClosed_atomI a₁ a₂)
        (atomI_nonempty hp.2.1)).2 ⟨t, ht, hz⟩⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i, hp, (visitBefore_iff hΓ isClosed_singleton (singleton_nonempty _)).2
        ⟨t, ht, hz⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i, hp, (visitBefore_iff hΓ isClosed_singleton (singleton_nonempty _)).2
        ⟨t, ht, hz⟩⟩))

/-- **The bad-visit event is measurable.** -/
theorem measurableSet_badVisit (κ θ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {β : Ω → BoundaryWord}
    (hβ : Measurable β) {Γ : Ω → ℝ≥0 → ℂ} (hΓ : ∀ q : ℝ≥0, Measurable fun ω => Γ ω q) {T : Ω → ℝ≥0∞}
    (hT : Measurable T) : MeasurableSet {ω | BadVisit κ θ (β ω) (Γ ω) (T ω)} := by
  have hpt : ∀ i : ℕ, Measurable fun ω => (((β ω).2.1 i : ℝ) : ℂ) := fun i =>
    Complex.measurable_ofReal.comp ((measurable_position i).comp hβ)
  have : {ω | BadVisit κ θ (β ω) (Γ ω) (T ω)} =
      (⋃ a₁ : ℚ, ⋃ a₂ : ℚ, (β ⁻¹' {c | predR κ θ c a₁ a₂} ∩ {ω | visitBefore (Γ ω) (T ω) (atomI a₁ a₂)})) ∪
      ((⋃ a₁ : ℚ, ⋃ a₂ : ℚ, (β ⁻¹' {c | predL κ θ c a₁ a₂} ∩ {ω | visitBefore (Γ ω) (T ω) (atomI a₁ a₂)})) ∪
      ((⋃ i : ℕ, (β ⁻¹' {c | predJL c i} ∩ {ω | visitBefore (Γ ω) (T ω) {(((β ω).2.1 i : ℝ) : ℂ)}})) ∪
      (⋃ i : ℕ, (β ⁻¹' {c | predJR κ θ c i} ∩ {ω | visitBefore (Γ ω) (T ω) {(((β ω).2.1 i : ℝ) : ℂ)}})))) := by
    ext ω
    simp only [BadVisit, mem_ofPred_eq, mem_union, mem_iUnion, mem_inter_iff, mem_preimage]
  rw [this]
  refine (MeasurableSet.iUnion fun a₁ => MeasurableSet.iUnion fun a₂ =>
    (hβ (measurableSet_predR κ θ a₁ a₂)).inter (measurableSet_visitBefore hΓ hT _)).union
    ((MeasurableSet.iUnion fun a₁ => MeasurableSet.iUnion fun a₂ =>
      (hβ (measurableSet_predL κ θ a₁ a₂)).inter (measurableSet_visitBefore hΓ hT _)).union
    ((MeasurableSet.iUnion fun i => (hβ (measurableSet_predJL i)).inter
      (measurableSet_visitBefore_pt hΓ hT (hpt i))).union
    (MeasurableSet.iUnion fun i => (hβ (measurableSet_predJR κ θ i)).inter
      (measurableSet_visitBefore_pt hΓ hT (hpt i)))))

/-- **On a regular piece, no bad visit is avoidance of the forbidden set by the chosen trace.** -/
theorem not_badVisit_iff {κ θ : ℝ} {c : BoundaryWord} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (hP : GW1P.PieceRegular e.1 e.2) :
    ¬ BadVisit κ θ c (fun q => LP.traceAt q e.1) e.2 ↔ ∀ t : ℝ≥0, (t : ℝ≥0∞) < e.2 → LuM.trOf e t ∉ forb κ θ c := by
  have heq : EqOn (fun q => LP.traceAt q e.1) (LuM.trOf e) {t | (t : ℝ≥0∞) < e.2} := fun t ht =>
    LuM.traceAt_eq_trOf he hP ht
  have hc : ContinuousOn (fun q => LP.traceAt q e.1) {t | (t : ℝ≥0∞) < e.2} := by
    have hmono : {t : ℝ≥0 | (t : ℝ≥0∞) < e.2} ⊆ {t | (t : ℝ≥0∞) ≤ e.2} := fun t (ht : (t : ℝ≥0∞) < e.2) =>
      show (t : ℝ≥0∞) ≤ e.2 from le_of_lt ht
    exact ((LuM.isGeneratingTrace_trOf hP).2.1.mono hmono).congr heq
  rw [badVisit_iff hc]
  constructor
  · intro h t ht hm
    exact h ⟨t, ht, by rw [LuM.traceAt_eq_trOf he hP ht]; exact hm⟩
  · rintro h ⟨t, ht, hm⟩
    rw [LuM.traceAt_eq_trOf he hP ht] at hm
    exact h t ht hm

/-! ### The stage law with the field exported -/

section Stage

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- `GW1W.ae_isFlowLineDriver_stage`, with the conditional field law of the driving field exported. -/
theorem ae_isFlowLineDriver_stage_gff {spec : ExplSpec} (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {ℓ : ℕ} {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E ℓ β Y) :
    ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      ∃ h' : Ω → DistOn upperHalfPlaneOpens,
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀) h' (β ω₀).fn (β ω₀).jumps ∧
        IsFlowLineDriver κ (β ω₀).fn (β ω₀).jumps (instrAngle spec ℓ)
          (condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀) h' (fun t ω => (E ℓ ω).1 t) (fun ω => (E ℓ ω).2) := by
  have h𝒢 : pastSigma κ b jumps spec E ℓ ≤ mΩ := hE.2.1 ℓ
  filter_upwards [hE.2.2.2 ℓ, hW.2.2.1, hW.2.2.2, Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hW.2.2.1,
    ae_ae_run_eq runMeasStatement hb spec (k := ℓ) (fun j _ => hE.1 j) (fun j _ => hreg j) (P := P)]
    with ω₀ hstg hp₀ hk₀ hpK hrunK
  intro hl
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  obtain ⟨b', J', h', hb', hT', hfl⟩ := hstg c θ' hcθ
  obtain ⟨hspec, -, hc⟩ := eq_launch_of_launches spec _ hcθ
  have hθ' : instrAngle spec ℓ = θ' := by unfold instrAngle; rw [hspec]
  obtain ⟨hconf, hlift, -⟩ := hp₀ hl
  rw [← hc] at hconf hlift
  have hgT : ∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω)
      (Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω)) := fun ω =>
    Chart.isChartTransport_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift) 1 0 _ (h ω)
  have hh'e : h' = fun ω => Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω) :=
    funext fun ω => (hT' ω).unique hconf (hgT ω)
  have hh'm : Measurable h' := by
    rw [hh'e]; exact (Chart.measurable_chartTransport hconf 1 0 _).comp hh.1
  have hYe : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀), Y ω = h' ω := by
    filter_upwards [hpK, hrunK] with ω hpω hrω
    have hlω : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      rw [launches_run_succ_of_run_eq spec hrω]; exact hl
    obtain ⟨-, -, hT⟩ := hpω hlω
    rw [hrω, ← hc] at hT
    exact hT.unique hconf (hT' ω)
  have hG : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀) h' (β ω₀).fn (β ω₀).jumps :=
    isGFFWithBoundaryData_congr_ae (hk₀ hl) hh'm hYe
  rw [hθ']
  exact ⟨h', hG, isFlowLineDriver_word hκ hG hb' hfl⟩

/-- **A launched piece of the walk avoids the forbidden set of its word, almost surely**, and its word has a seed
right weight `> −2` when the lifetime is positive. -/
theorem ae_stage_avoid (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {θ : ℝ}
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ true) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hRS : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps θ true) E)
    {ℓ : ℕ} {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps θ true) E ℓ β Y) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠
        none →
      (0 < (E ℓ ω).2 → SeedOK κ θ (β ω)) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < (E ℓ ω).2 → LuM.trOf (E ℓ ω) t ∉ forb κ θ (β ω) := by
  classical
  set spec := boundaryWalkSpec b jumps θ true with hspec
  have h𝒢 : pastSigma κ b jumps spec E ℓ ≤ mΩ := hE.2.1 ℓ
  have hLp := measurableSet_pastSigma_launch (κ := κ) hb spec hE.1 hreg ℓ
  have hβm : Measurable β := hW.1.mono h𝒢 le_rfl
  have hζm : Measurable fun ω => (E ℓ ω).2 := measurable_snd.comp (hE.1 ℓ)
  have hΓm : ∀ q : ℝ≥0, Measurable fun ω => LP.traceAt q (E ℓ ω).1 := fun q =>
    (LP.measurable_traceAt q).comp (measurable_fst.comp (hE.1 ℓ))
  -- the regular pieces at launches
  have hPR : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      GW1P.PieceRegular (E ℓ ω).1 (E ℓ ω).2 := by
    filter_upwards [regLaunches_of_stagedPiecesRegular hRS] with ω hRLω hl
    obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
    have := hRLω ℓ c θ' hcθ
    rwa [instrTime_walk hl, min_eq_right le_top] at this
  -- the measurable good event
  set G : Set Ω := {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      (0 < (E ℓ ω).2 → SeedOK κ θ (β ω)) ∧ ¬ BadVisit κ θ (β ω) (fun q => LP.traceAt q (E ℓ ω).1) (E ℓ ω).2}
    with hGdef
  have hGm : MeasurableSet G := by
    have h1 : MeasurableSet {ω | 0 < (E ℓ ω).2 → SeedOK κ θ (β ω)} :=
      ((measurableSet_lt measurable_const hζm).compl.union (hβm (measurableSet_seedOK κ θ))).congr
        (by ext ω; simp only [mem_union, mem_compl_iff, mem_ofPred_eq, mem_preimage]; tauto)
    have h2 := (measurableSet_badVisit κ θ hβm hΓm hζm).compl
    exact ((h𝒢 _ hLp).compl.union (h1.inter h2)).congr
      (by ext ω; simp only [mem_union, mem_compl_iff, mem_inter_iff, mem_ofPred_eq, hGdef]; tauto)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    refine Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hGm ?_
    filter_upwards [ae_isFlowLineDriver_stage_gff hκ hb hh hE hreg hW,
      Sec7.Aux122Disint.ae_ae_condExpKernel_mem h𝒢 hLp, Sec7.Aux122Disint.ae_ae_condExpKernel_mem h𝒢 hLp.compl,
      Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hPR,
      Sec7.Lemma725RefK2.ae_ae_condExpKernel_eq_self (P := P) h𝒢 hW.1] with ω₀ hfl₀ hLK hLKc hPRK hβK
    by_cases hl₀ : (ExplState.run κ b jumps spec (fun j => E j ω₀) (ℓ + 1)).2.2.2.1 ℓ ≠ none
    swap
    · filter_upwards [hLKc hl₀] with ω hω hlω
      exact absurd hlω hω
    obtain ⟨h', hG', hfl⟩ := hfl₀ hl₀
    rw [instrAngle_walk hl₀] at hfl
    have htr : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀),
        IsGeneratingTrace (fun t => (E ℓ ω).1 t) (E ℓ ω).2 (LuM.trOf (E ℓ ω)) := by
      filter_upwards [hLK hl₀, hPRK] with ω hlω hPω using LuM.isGeneratingTrace_trOf (hPω hlω)
    have hη := GW2Rd.isFlowLine_of_driver hfl htr
    have hav := ae_avoid_forb (β := β ω₀) (F := ∅) hκ hκ4 (β ω₀).isPiecewiseConstantBoundaryData hG' hη
      fun _ _ => rfl
    have hsd := Supp9.ae_seedWeights_of_isFlowLine hη
    filter_upwards [hav, hsd, hLK hl₀, hPRK, hβK] with ω havω hsdω hlω hPω hβω _
    rw [hβω]
    exact ⟨fun hpos => (hsdω hpos).2, (not_badVisit_iff (hreg ℓ ω) (hPω hlω)).2 havω⟩
  filter_upwards [hGae, hPR] with ω hGω hPω hl
  obtain ⟨h1, h2⟩ := hGω hl
  exact ⟨h1, (not_badVisit_iff (hreg ℓ ω) (hPω hl)).1 h2⟩

end Stage

end InteractingSLE.Theorem14.SB.Wf
