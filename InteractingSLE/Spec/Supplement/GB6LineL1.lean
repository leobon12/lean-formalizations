/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkUnionLaw
import InteractingSLE.Spec.Supplement.Q3ChainDet
import InteractingSLE.Spec.Sec7.Lemma72DHull
import InteractingSLE.Spec.Supplement.Q3RelGB6Chart

/-!
# GB6's line locality, part 1: gluing determined marked local sets

Packet PROVE-GB6-LINELOCAL. For a field-determined random set `A` with field-determined marks `ℋ`, the history-marked
avoidance criterion says that every marked avoidance event `{A ∩ U = ∅} ∩ F` is almost surely an event of the
complementary Markov projection `h − G h` (`WalkLaw.isHistoryAvoidanceLocal_of_mem_aeSigma`). Those events form a
σ-algebra (`WalkLaw.complSigma`), so the criterion can be checked piece by piece on a countable cover:

* `ae_eq_zero_of_isMarkovDecomposition_empty`, **`aeSigma_le_complSigma_of_empty`**: for `U = ∅` the harmonic part of
  a Markov decomposition vanishes, so every field-determined event is an event of the complementary projection;
* **`mem_complSigma_inter_of_piece`**: on an event `E` where `A` agrees with a marked local set `A'` whose marks
  contain `F ∩ E` for every mark `F`, the marked avoidance events of `A` cut to `E` are events of the complementary
  projection;
* **`isHistoryAvoidanceLocal_glue_det`**: `A` is marked local when this holds on each piece of a countable cover
  and `A ⊇ ℍ` almost surely off the cover;
* `disjoint_iff_forall_posRatDisc`, **`measurableSet_disjoint_invHull_rdrv`**, **`measurable_invHull_rdrv`**: the
  inverted hull `−1/K_s` of the driver read from a record is a hitting-measurable function of the record (the hull
  avoids an open set iff it avoids every rational closed disc of positive radius inside it,
  `Sec7.Lemma72D.measurableSet_disjoint_closedBall_fwdHull_real`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Metric TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Supp8.GB6LineL

open LocalSets Theorem14.WalkLaw

/-! ### `aeSigma` helpers -/

section AeSigma

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem mem_aeSigma_of_ae_eq {m : MeasurableSpace Ω} {S T : Set Ω} (hT : MeasurableSet[aeSigma m P] T)
    (h : S =ᵐ[P] T) : MeasurableSet[aeSigma m P] S := by
  obtain ⟨T', hT', he⟩ := hT
  exact ⟨T', hT', h.trans he⟩

theorem mem_aeSigma_of_null {m : MeasurableSpace Ω} {S : Set Ω} (h : P S = 0) : MeasurableSet[aeSigma m P] S :=
  ⟨∅, @MeasurableSet.empty _ m, by rw [ae_eq_empty]; exact h⟩

end AeSigma

/-! ### The Markov decomposition of the empty set -/

section Empty

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The harmonic part of a Markov decomposition of the empty set vanishes** (`h_∅ = 0` on `D \ cl ∅ = D`). -/
theorem ae_eq_zero_of_isMarkovDecomposition_empty {U : Opens ℂ} (hU : (U : Set ℂ) = ∅)
    {h hU' : Ω → DistOn upperHalfPlaneOpens} (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h hU' P) :
    ∀ᵐ ω ∂P, hU' ω = 0 := by
  filter_upwards [hd.ae_restrictDist_outside_eq_zero] with ω hω
  ext φ
  have hsub : tsupport φ ⊆ (GFF.outsideOpens U upperHalfPlaneOpens : Set ℂ) := by
    intro z hz
    refine ⟨φ.tsupport_subset hz, ?_⟩
    show z ∉ closure (U : Set ℂ)
    rw [hU, closure_empty]
    exact notMem_empty z
  have := congrArg (fun S => S (testOnOfSubset φ hsub)) hω
  simp only [GFF.restrictDist_apply, testIncl_testOnOfSubset (GFF.outsideOpens_le _ _)] at this
  rw [this]
  rfl

/-- **For `U = ∅`, every field-determined event is an event of the complementary projection.** -/
theorem aeSigma_le_complSigma_of_empty {h : Ω → DistOn upperHalfPlaneOpens} {U : Opens ℂ}
    (hU : (U : Set ℂ) = ∅) {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P) :
    aeSigma (MeasurableSpace.comap h inferInstance) P ≤ complSigma P G h := by
  have h0 := ae_eq_zero_of_isMarkovDecomposition_empty hU hd
  have he : (fun ω => markovCompl G (h ω)) =ᵐ[P] h := by
    filter_upwards [h0] with ω hω
    simp only [markovCompl, hω, sub_zero]
  exact Supp8.Q3Chain.aeSigma_le_of_le (Theorem14.StagedReg.comap_le_aeSigma he)

end Empty

/-! ### Gluing on a countable cover -/

section Glue

variable {Ω : Type*} {ℋ 𝒦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistOn upperHalfPlaneOpens}

variable (ℋ) in
/-- The piece property: on `E`, the marked avoidance events of `A` are events of the complementary projection. -/
def PieceDet (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (P : Measure Ω)
    (E : Set Ω) : Prop :=
  ∀ (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
    (U : Set ℂ) ⊆ H → Measurable G →
    GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P →
    ∀ F : Set Ω, MeasurableSet[ℋ] F →
      MeasurableSet[complSigma P G h] ({ω | Disjoint (A ω) U} ∩ F ∩ E)

variable [IsProbabilityMeasure P]

/-- **A piece from a marked local set.** If `A = A'` almost surely on `E`, `A'` is marked local for marks `𝒦` with
`F ∩ E ∈ 𝒦` for every mark `F` of `ℋ`, and all marks and the avoidance events of `A` are field-determined, then
`PieceDet ℋ A h P E`. -/
theorem pieceDet_of_local (hhm : Measurable h) {A A' : Ω → Set ℂ} {E : Set Ω}
    (hℋ : ℋ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (h𝒦 : 𝒦 ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hA : ∀ U : Set ℂ, IsOpen U → U ⊆ H →
      MeasurableSet[aeSigma (MeasurableSpace.comap h inferInstance) P] {ω | Disjoint (A ω) U})
    (hloc : WholeField.IsHistoryAvoidanceLocal 𝒦 A' h P)
    (hE : ∀ F, MeasurableSet[ℋ] F → MeasurableSet[𝒦] (F ∩ E))
    (hAE : ∀ᵐ ω ∂P, ω ∈ E → A ω = A' ω) : PieceDet ℋ A h P E := by
  intro U G hUH hG hd F hF
  have hF' : MeasurableSet[𝒦] (F ∩ E) := hE F hF
  have hE𝒦 : MeasurableSet[𝒦] E := by simpa only [univ_inter] using hE univ (@MeasurableSet.univ _ ℋ)
  have heq : {ω | Disjoint (A' ω) U} ∩ (F ∩ E) =ᵐ[P] {ω | Disjoint (A ω) U} ∩ F ∩ E := by
    filter_upwards [hAE] with ω hω
    by_cases hωE : ω ∈ E
    · simp only [mem_inter_iff, mem_ofPred_eq, hω hωE, hωE, and_true]
    · simp only [mem_inter_iff, hωE, and_false]
  have hdet : MeasurableSet[aeSigma (MeasurableSpace.comap h inferInstance) P]
      ({ω | Disjoint (A' ω) U} ∩ (F ∩ E)) :=
    mem_aeSigma_of_ae_eq (((hA U U.isOpen hUH).inter (hℋ F hF)).inter (h𝒦 E hE𝒦)) heq
  exact mem_aeSigma_of_ae_eq (mem_aeSigma_of_isHistoryAvoidanceLocal hhm hloc hUH hG hd hF' hdet) heq.symm

/-- **Gluing determined marked locality on a countable cover.** If `A` satisfies the piece property on each `E n`,
the marks and the pieces are field-determined, and `A ⊇ ℍ` almost surely off `⋃ E n`, then `A` satisfies the
history-marked avoidance criterion for the marks `ℋ`. -/
theorem isHistoryAvoidanceLocal_glue_det (hhm : Measurable h) {A : Ω → Set ℂ}
    {E : ℕ → Set Ω} (hℋ : ℋ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hEd : ∀ n, MeasurableSet[aeSigma (MeasurableSpace.comap h inferInstance) P] (E n))
    (hpiece : ∀ n, PieceDet ℋ A h P (E n)) (hoff : ∀ᵐ ω ∂P, (∀ n, ω ∉ E n) → H ⊆ A ω) :
    WholeField.IsHistoryAvoidanceLocal ℋ A h P := by
  refine isHistoryAvoidanceLocal_of_mem_aeSigma hhm fun U G hUH hG hd F hF => ?_
  set Ev : Set Ω := {ω | Disjoint (A ω) U} with hEv
  have hsplit : Ev ∩ F = (⋃ n, Ev ∩ F ∩ E n) ∪ (Ev ∩ F ∩ (⋃ n, E n)ᶜ) := by
    ext ω
    simp only [mem_union, mem_iUnion, mem_inter_iff, mem_compl_iff, not_exists]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hω : ∃ n, ω ∈ E n
      · obtain ⟨n, hn⟩ := hω
        exact Or.inl ⟨n, ⟨h1, h2⟩, hn⟩
      · exact Or.inr ⟨⟨h1, h2⟩, fun n hn => hω ⟨n, hn⟩⟩
    · rintro (⟨n, ⟨h1, h2⟩, -⟩ | ⟨⟨h1, h2⟩, -⟩) <;> exact ⟨h1, h2⟩
  rw [hsplit]
  refine (MeasurableSet.iUnion fun n => hpiece n U G hUH hG hd F hF).union ?_
  by_cases hU0 : (U : Set ℂ) = ∅
  · -- `U = ∅`: everything field-determined is an event of the complementary projection
    have hle := aeSigma_le_complSigma_of_empty hU0 hd
    have hEvu : Ev = univ := by
      ext ω
      simp only [hEv, mem_ofPred_eq, hU0, disjoint_empty, mem_univ]
    rw [hEvu, univ_inter]
    exact (hle F (hℋ F hF)).inter (MeasurableSet.iUnion fun n => hle _ (hEd n)).compl
  · -- `U ≠ ∅`: off the cover `A ⊇ ℍ` meets `U`
    obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.2 hU0
    refine mem_aeSigma_of_null (measure_eq_zero_iff_ae_notMem.2 ?_)
    filter_upwards [hoff] with ω hω hmem
    have hnot : ∀ n, ω ∉ E n := fun n hn => hmem.2 (mem_iUnion.2 ⟨n, hn⟩)
    exact Set.disjoint_left.1 hmem.1.1 (hω hnot (hUH hz)) hz

end Glue

/-! ### The inverted hull read from a record -/

section RecHull

open Exist.StagedLaw

/-- **Avoidance of an open set through rational closed discs of positive radius.** -/
theorem disjoint_iff_forall_posRatDisc {K U : Set ℂ} (hU : IsOpen U) :
    Disjoint K U ↔ ∀ p : ℚ × ℚ × ℚ, 0 < p.2.2 →
      closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ) ⊆ U →
      Disjoint (closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ)) K := by
  constructor
  · intro hd p _ hp
    exact (hd.mono_right hp).symm
  · intro hall
    refine Set.disjoint_left.2 fun z hzK hzU => ?_
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hzU
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - ε / 8 < z.re by linarith)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.im - ε / 8 < z.im by linarith)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
    set q : ℂ := (a : ℂ) + (b : ℂ) * Complex.I with hq
    have hqre : q.re = a := by simp [hq]
    have hqim : q.im = b := by simp [hq]
    have hdist : dist z q < ε / 4 := by
      rw [Complex.dist_eq]
      calc ‖z - q‖ ≤ |(z - q).re| + |(z - q).im| := Complex.norm_le_abs_re_add_abs_im _
        _ < ε / 8 + ε / 8 := by
          refine add_lt_add ?_ ?_
          · rw [Complex.sub_re, hqre, abs_lt]; constructor <;> linarith
          · rw [Complex.sub_im, hqim, abs_lt]; constructor <;> linarith
        _ = ε / 4 := by ring
    have hsub : closedBall q (r : ℝ) ⊆ U := by
      intro w hw
      refine hεU ?_
      rw [mem_ball]
      calc dist w z ≤ dist w q + dist q z := dist_triangle _ _ _
        _ < (r : ℝ) + ε / 4 + ε / 4 := by
          rw [dist_comm q z]
          have := mem_closedBall.1 hw
          linarith
        _ ≤ ε := by linarith
    have hzq : z ∈ closedBall q (r : ℝ) := by
      rw [mem_closedBall]
      linarith
    have hr0 : (0 : ℚ) < r := by
      have : (0 : ℝ) < r := by linarith
      exact_mod_cast this
    exact Set.disjoint_left.1 (hall (a, b, r) hr0 hsub) hzq hzK

/-- The record driver as a process on the record space. -/
theorem drive_rdrv : (QuantumZipper.drive 1 (fun t (r : RecData) => rdrv r (t : ℝ))) = rdrv := by
  funext r x
  simp only [QuantumZipper.drive, Real.sqrt_one, one_mul, rdrv, Real.toNNReal_coe]

/-- **The avoidance events of the hull of the record driver at a fixed time are measurable.** -/
theorem measurableSet_disjoint_fwdHull_rdrv (s : ℝ≥0) {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) :
    MeasurableSet {r : RecData | Disjoint (fwdHull (rdrv r) s) U} := by
  have e : {r : RecData | Disjoint (fwdHull (rdrv r) s) U} =
      ⋂ p : ℚ × ℚ × ℚ, ⋂ (_ : 0 < p.2.2),
        ⋂ (_ : closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ) ⊆ U),
          {r : RecData | Disjoint (closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ))
            (fwdHull (rdrv r) s)} := by
    ext r
    simp only [mem_ofPred_eq, mem_iInter]
    exact disjoint_iff_forall_posRatDisc hU
  rw [e]
  refine MeasurableSet.iInter fun p => MeasurableSet.iInter fun hp => MeasurableSet.iInter fun hsub => ?_
  set c : ℂ := (p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I with hc
  have hε : (0 : ℝ) < (p.2.2 : ℝ) := by exact_mod_cast hp
  have hcε : (p.2.2 : ℝ) < c.im := by
    have hmem : c - ((p.2.2 : ℝ) : ℂ) * Complex.I ∈ closedBall c (p.2.2 : ℝ) := by
      rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    have h1 : 0 < (c - ((p.2.2 : ℝ) : ℂ) * Complex.I).im := hUH (hsub hmem)
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero] at h1
    linarith
  have h := Sec7.Lemma72D.measurableSet_disjoint_closedBall_fwdHull_real (m := inferInstance)
    (B := fun t (r : RecData) => rdrv r (t : ℝ)) (fun r => (continuous_rdrv r).comp NNReal.continuous_coe)
    s.coe_nonneg (fun t _ => measurable_rdrv_apply (t : ℝ)) hε hcε
  rw [drive_rdrv] at h
  exact h

/-- **The hull of the record driver at a fixed time is a hitting-measurable function of the record.** -/
theorem measurable_fwdHull_rdrv (s : ℝ≥0) :
    Measurable[inferInstance, hittingSigma] fun r : RecData => fwdHull (rdrv r) s := by
  refine @measurable_generateFrom _ _ inferInstance _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have e : (fun r : RecData => fwdHull (rdrv r) s) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      {r : RecData | Disjoint (fwdHull (rdrv r) s) U}ᶜ := by
    ext r
    simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, Set.not_disjoint_iff_nonempty_inter]
  rw [e]
  exact (measurableSet_disjoint_fwdHull_rdrv s hU hUH).compl

/-- **The inverted hull `−1/K_s` of the record driver is a hitting-measurable function of the record.** -/
theorem measurable_invHull_rdrv (s : ℝ≥0) :
    Measurable[inferInstance, hittingSigma] fun r : RecData => Q3Rel.invHull (rdrv r) s :=
  WangWu.measurable_image_negInv.comp (measurable_fwdHull_rdrv s)

end RecHull

end InteractingSLE.Supp8.GB6LineL
