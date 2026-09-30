import QuantumZipper.Proofs.GFF.K3.CondExistence
import QuantumZipper.Proofs.NonVacuityFinal
import QuantumZipper.Proofs.RS.TraceMeas
import QuantumZipper.Proofs.Thm12.CharFun
import QuantumZipper.Statements.Thm11
import QuantumZipper.Blueprint.External3

/-!
# Non-vacuity of the hypotheses of the Theorem 1.1 addendum (K3-E5; DECISIONS D15, task F2)

`blueprint/GFF_K3_BLUEPRINT.md` §3, node E5; DECISIONS D15 (F2, `exists_addendum_setup`);
TASKS §4 note (AUDIT6 P2).

For κ ∈ (4,8) and `T > 0` there is a probability space carrying a Brownian motion `B`, a
zero-boundary GFF `X`, and a conditional zero-boundary GFF `X'` on `U_T = sleComplement κ B · T`
given `pathOf B` (`exists_addendum_setup`). So the hypotheses of the addendum are satisfiable.

Construction: `Ω = (Ω_B × Ω_X) × (ℕ → ℝ)`, with the Brownian motion of `brownianMotionExists`
(replaced by a version with all paths continuous and measurable, `CharFun.exists_good_version`),
the zero-boundary GFF of `exists_zeroGFF`, and the i.i.d. Gaussian sequence of E4
(`K3.exists_condZeroGFF`). E4 is applied to `Ũ ω = H \ closure (η̃ ω [0,T])`, where `η̃` is the
jointly measurable continuous version of the trace (TR6, `RS.exists_measurable_sleTrace`); the
events `{tsupport f_j ⊆ Ũ ω}` are measurable because for compact `K ⊆ H` they are
`⋃_m ⋂_{q ∈ ℚ ∩ (0,T)} {dist(η̃ ω q, K) ≥ 1/(m+1)}` (`measurableSet_subset_compl_closure_image`).
Finally `Ũ = U_T` almost surely (`IsCondZeroBoundaryGFFH.congr_ae`). Own elementary argument
following the blueprint (no literature source needed).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace QuantumZipper
namespace NonVacuityAddendum

open LQGDimension.ExistAsm

/-- For compact `K`, the event `{K ⊆ H \ closure (η ω [0,T])}` is measurable for a jointly
measurable family of continuous paths. -/
theorem measurableSet_subset_compl_closure_image {Ω : Type*} [MeasurableSpace Ω]
    {η : Ω → ℝ → ℂ} (hη : Measurable η) (hc : ∀ ω, Continuous (η ω)) {T : ℝ} (hT : 0 < T)
    {K : Set ℂ} (hK : IsCompact K) :
    MeasurableSet {ω | K ⊆ H \ closure (η ω '' Icc 0 T)} := by
  by_cases hKH : K ⊆ H
  swap
  · have : {ω | K ⊆ H \ closure (η ω '' Icc 0 T)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => hKH (h.trans sdiff_subset)
    rw [this]; exact MeasurableSet.empty
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · have : {ω | K ⊆ H \ closure (η ω '' Icc 0 T)} = univ := by
      ext ω; simp [hKe]
    rw [this]; exact MeasurableSet.univ
  set D : Set ℝ := Ioo 0 T ∩ range ((↑) : ℚ → ℝ) with hDdef
  have hDc : D.Countable := (countable_range _).mono inter_subset_right
  have hDcl : Icc 0 T ⊆ closure D := by
    rw [← closure_Ioo hT.ne]
    exact closure_minimal (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo)
      isClosed_closure
  have hDsub : D ⊆ Icc 0 T := inter_subset_left.trans Ioo_subset_Icc_self
  have heq : {ω | K ⊆ H \ closure (η ω '' Icc 0 T)}
      = ⋃ m : ℕ, ⋂ q ∈ D, {ω | 1 / ((m : ℝ) + 1) ≤ infDist (η ω q) K} := by
    ext ω
    have hcl : closure (η ω '' Icc 0 T) = η ω '' Icc 0 T :=
      (isCompact_Icc.image (hc ω)).isClosed.closure_eq
    have hfc : Continuous fun s => infDist (η ω s) K := (continuous_infDist_pt K).comp (hc ω)
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, hcl]
    constructor
    · intro h
      -- the distance to `K` is positive and continuous on `[0,T]`
      obtain ⟨s₀, hs₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMinOn
        (nonempty_Icc.2 hT.le) hfc.continuousOn
      have hpos : 0 < infDist (η ω s₀) K := by
        refine (hK.isClosed.notMem_iff_infDist_pos hKne).1 fun hmem => ?_
        exact (h hmem).2 ⟨s₀, hs₀, rfl⟩
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
      exact ⟨m, fun q hq => hm.le.trans (hmin (hDsub hq))⟩
    · rintro ⟨m, hm⟩ z hz
      refine ⟨hKH hz, ?_⟩
      rintro ⟨t, ht, rfl⟩
      have hS : IsClosed {s | 1 / ((m : ℝ) + 1) ≤ infDist (η ω s) K} :=
        isClosed_le continuous_const hfc
      have ht' := closure_minimal (fun q hq => hm q hq) hS (hDcl ht)
      have ht'' : 1 / ((m : ℝ) + 1) ≤ infDist (η ω t) K := ht'
      rw [infDist_zero_of_mem hz] at ht''
      have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      linarith
  rw [heq]
  refine MeasurableSet.iUnion fun m => MeasurableSet.biInter hDc fun q _ => ?_
  exact measurableSet_le measurable_const
    ((continuous_infDist_pt K).measurable.comp ((measurable_pi_apply q).comp hη))

/-- **K3-E5 / D15 F2: the hypotheses of the Theorem 1.1 addendum are satisfiable.** -/
theorem exists_addendum_setup (κ T : ℝ) (hκ4 : 4 < κ) (hκ8 : κ < 8) (hT : 0 < T) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
      (X X' : Ω → FieldSample),
      IsProbabilityMeasure P ∧ IsBrownianReal B P ∧ IsZeroBoundaryGFFH X P ∧
      IsCondZeroBoundaryGFFH (fun ω => sleComplement κ B ω T) (pathOf B) X' P := by
  obtain ⟨Ω₁, _, P₁, B₁, hP₁, hB₁⟩ := brownianMotionExists
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB₁
  have hB' : IsBrownianReal B' P₁ :=
    ⟨hB₁.toIsPreBrownianReal.congr fun t => hB'eq.mono fun ω h => (h t).symm,
      ae_of_all _ hB'c⟩
  obtain ⟨η, -, hηm, hηc, hηeq⟩ := RS.exists_measurable_sleTrace hB' (by linarith) hκ8
  obtain ⟨Ω₂, _, P₂, X₂, hP₂, hX₂⟩ := exists_zeroGFF
  set P₀ : Measure (Ω₁ × Ω₂) := P₁.prod P₂ with hP₀
  set Y : Ω₁ × Ω₂ → (ℝ≥0 → ℝ) := fun ω => pathOf B' ω.1 with hYdef
  have hY : Measurable Y := measurable_pi_iff.2 fun t => (hB'm t).comp measurable_fst
  set U : Ω₁ × Ω₂ → Set ℂ := fun ω => H \ closure (η ω.1 '' Icc 0 T) with hUdef
  have hU : ∀ ω, IsOpen (U ω) ∧ U ω ⊆ H := fun ω =>
    ⟨(isOpen_lt continuous_const Complex.continuous_im).sdiff isClosed_closure, sdiff_subset⟩
  have hE : ∀ j, MeasurableSet {ω | tsupport (K3.testFamily j) ⊆ U ω} := fun j =>
    measurable_fst (measurableSet_subset_compl_closure_image hηm hηc hT
      (K3.testFamily_mem j).2.1)
  obtain ⟨X', hX'⟩ := K3.exists_condZeroGFF P₀ Y hY U hU hE
  have h1 : MeasurePreserving (fun p : (Ω₁ × Ω₂) × (ℕ → ℝ) => p.1.1) (P₀.prod stdP) P₁ :=
    measurePreserving_fst.comp measurePreserving_fst
  have h2 : MeasurePreserving (fun p : (Ω₁ × Ω₂) × (ℕ → ℝ) => p.1.2) (P₀.prod stdP) P₂ :=
    measurePreserving_snd.comp measurePreserving_fst
  refine ⟨(Ω₁ × Ω₂) × (ℕ → ℝ), inferInstance, P₀.prod stdP, fun t p => B' t p.1.1,
    fun p => X₂ p.1.2, X', inferInstance, NonVacuity.nv_isBrownianReal h1 hB',
    NonVacuity.nv_zeroGFF h2 hX₂, K3.IsCondZeroBoundaryGFFH.congr_ae hX' ?_⟩
  filter_upwards [h1.quasiMeasurePreserving.ae hηeq] with p hp
  show H \ closure (η p.1.1 '' Icc 0 T) = H \ closure (sleTrace κ B' p.1.1 '' Icc 0 T)
  rw [(hp.mono Icc_subset_Ici_self).image_eq]

/-- **K3-E5** in the blueprint's form (with the now-proved `RohdeSchrammTraceGen` hypothesis). -/
theorem addendum_hypotheses_nonvacuous {κ T : ℝ} (hκ : 4 < κ ∧ κ < 8) (hT : 0 < T)
    (_hRS : Blueprint.RohdeSchrammTraceGen κ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
      (X X' : Ω → FieldSample),
      IsProbabilityMeasure P ∧ IsBrownianReal B P ∧ IsZeroBoundaryGFFH X P ∧
      IsCondZeroBoundaryGFFH (fun ω => sleComplement κ B ω T) (pathOf B) X' P :=
  exists_addendum_setup κ T hκ.1 hκ.2 hT

end NonVacuityAddendum
end QuantumZipper
