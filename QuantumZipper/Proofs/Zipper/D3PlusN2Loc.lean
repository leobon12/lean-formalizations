import QuantumZipper.Proofs.Zipper.D3PlusN2CM
import QuantumZipper.Proofs.Zipper.D3PlusN1Core

/-!
# D3⁺(i), node N2-loc: locality of the zoom (proved)

Task D3P-N2. Proves `D3PlusIN2FixLocRichStmt` (`D3PlusN2CM.lean`), deterministically: for every
field sample `y` with `0 < s := scaleParamOn γ y (halfDisc r) < ε/(R+2)` (`0 < ε ≤ r`),

`locFieldFull R (canonicalOn γ y (halfDisc r)) = TmRichN1 γ ε R 0 (resField ε y, 0)`,

a measurable function (`measurable_TmRichN1`, node N1) of the restriction of `y` to the
`ε`-local measures. Steps (own elementary arguments):

* `isVagueLimitOn_restrict`: a vague limit on `U` restricts to a vague limit on an open `V ⊆ U`;
  with `LocalRule.qAreaMeasureOn_eq` (uniqueness), the local area measure on `halfDisc ε` is the
  restriction of the one on `halfDisc r` as soon as the latter is a genuine limit, which
  `s > 0` forces (`exists_isVagueLimitOn_of_scale_pos`);
* `sInf_eq_of_agree_below`: the defining sets of the two scales agree below `ε`, so the scales
  coincide (`scaleParamOn_halfDisc_restrict`);
* on `halfDisc ε`, `y` agrees at every dyadic circle with the N1 local model
  `locModel γ 0 ε (resField ε y, 0)`, and N1's locality lemmas (`scaleParamOn_halfDisc_congr`,
  `locFieldFull_rescale_congr`, `scaleSur_eq`) identify the rescaled readings.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

theorem isVagueLimitOn_restrict {U V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U)
    {μs : ℕ → Measure ℂ} {m : Measure ℂ} (hm : IsVagueLimitOn U μs m) :
    IsVagueLimitOn V μs (m.restrict V) := by
  obtain ⟨-, h2, h3⟩ := hm
  refine ⟨?_, fun K hK hKV => ?_, fun f hf hfc hfV => ?_⟩
  · rw [Measure.restrict_apply hV.measurableSet.compl, compl_inter_self, measure_empty]
  · exact (Measure.restrict_apply_le _ _).trans_lt (h2 K hK (hKV.trans hVU))
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => image_eq_zero_of_notMem_tsupport fun hz' => hz (hfV hz'))]
    exact h3 f hf hfc (hfV.trans hVU)

theorem exists_isVagueLimitOn_of_scale_pos {γ : ℝ} {y : FieldSample} {U : Set ℂ}
    (h : 0 < scaleParamOn γ y U) : ∃ m, IsVagueLimitOn U (areaApprox γ y) m := by
  by_contra hne
  have h0 : qAreaMeasureOn γ y U = 0 := Prop16Area.Meas.qAreaMeasureOn_of_not hne
  unfold scaleParamOn at h
  rw [h0] at h
  simp at h

/-- Two sets of positive reals that agree below `ε`, one with infimum `< ε`, have the same
infimum. -/
theorem sInf_eq_of_agree_below {S T : Set ℝ} {ε : ℝ} (hS : ∀ a ∈ S, 0 < a)
    (hT : ∀ a ∈ T, 0 < a) (hST : ∀ a < ε, a ∈ S ↔ a ∈ T) (hSne : S.Nonempty)
    (hlt : sInf S < ε) : sInf T = sInf S := by
  have hSb : BddBelow S := ⟨0, fun a ha => (hS a ha).le⟩
  have hTb : BddBelow T := ⟨0, fun a ha => (hT a ha).le⟩
  obtain ⟨a0, ha0S, ha0⟩ := exists_lt_of_csInf_lt hSne hlt
  have hTne : T.Nonempty := ⟨a0, (hST a0 ha0).1 ha0S⟩
  have key : ∀ {A B : Set ℝ}, (∀ a < ε, a ∈ A → a ∈ B) → A.Nonempty → sInf A < ε →
      BddBelow B → sInf B ≤ sInf A := by
    intro A B hAB hAne hAlt hB
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    obtain ⟨a, haA, hal⟩ := exists_lt_of_csInf_lt hAne
      (show sInf A < min (sInf A + δ) ε from lt_min (by linarith) hAlt)
    exact (csInf_le hB (hAB a (hal.trans_le (min_le_right _ _)) haA)).trans_lt
      (hal.trans_le (min_le_left _ _))
  have h1 : sInf T ≤ sInf S := key (fun a ha h => (hST a ha).1 h) hSne hlt hTb
  exact le_antisymm h1 (key (fun a ha h => (hST a ha).2 h) hTne (h1.trans_lt hlt) hSb)

/-- The local scale on `halfDisc ε` equals the one on `halfDisc r` when the latter is in
`(0, ε)`. -/
theorem scaleParamOn_halfDisc_restrict {γ r ε : ℝ} {y : FieldSample} (hεr : ε ≤ r)
    (h0 : 0 < scaleParamOn γ y (halfDisc r)) (hlt : scaleParamOn γ y (halfDisc r) < ε) :
    scaleParamOn γ y (halfDisc ε) = scaleParamOn γ y (halfDisc r) := by
  obtain ⟨m, hm⟩ := exists_isVagueLimitOn_of_scale_pos h0
  have hsub : halfDisc ε ⊆ halfDisc r :=
    inter_subset_inter_left _ (Metric.ball_subset_ball hεr)
  have e1 := LocalRule.qAreaMeasureOn_eq (isOpen_halfDisc r) hm
  have e2 := LocalRule.qAreaMeasureOn_eq (isOpen_halfDisc ε)
    (isVagueLimitOn_restrict (isOpen_halfDisc ε) hsub hm)
  unfold scaleParamOn at h0 hlt ⊢
  rw [e1] at h0 hlt ⊢
  rw [e2]
  refine sInf_eq_of_agree_below (fun a ha => ha.1) (fun a ha => ha.1) (fun a ha => ?_) ?_ hlt
  · have hsub' : Metric.ball (0 : ℂ) a ∩ H ⊆ halfDisc ε :=
      inter_subset_inter_left _ (Metric.ball_subset_ball ha.le)
    have e : m.restrict (halfDisc ε) (Metric.ball 0 a ∩ H) = m (Metric.ball 0 a ∩ H) := by
      rw [Measure.restrict_apply (Metric.isOpen_ball.inter isOpen_H).measurableSet,
        inter_eq_left.2 hsub']
    simp only [mem_setOf_eq, e]
  · by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sInf_empty] at h0
    exact lt_irrefl _ h0

/-- **Locality of the zoom, deterministic form.** -/
theorem locFieldFull_canonicalOn_eq_local {γ r ε : ℝ} {R : ℕ} {y : FieldSample}
    (hε : 0 < ε) (hεr : ε ≤ r) (h0 : 0 < scaleParamOn γ y (halfDisc r))
    (hlt : scaleParamOn γ y (halfDisc r) < ε / (R + 2)) :
    locFieldFull R (canonicalOn γ y (halfDisc r)) = TmRichN1 γ ε R 0 (resField ε y, 0) := by
  classical
  have hR1 : ε / (R + 2) ≤ ε / (R + 1) :=
    div_le_div_of_nonneg_left hε.le (by positivity) (by linarith)
  have hR0 : ε / (R + 1) ≤ ε := div_le_self hε.le (by linarith [(R.cast_nonneg : (0 : ℝ) ≤ R)])
  have hs := scaleParamOn_halfDisc_restrict hεr h0 ((hlt.trans_le hR1).trans_le hR0)
  have hag : AgreeNear y (locModel γ 0 ε (resField ε y, 0)) ε := by
    intro n k z hz
    have hmem : foldedCircle (dyadicRoundC n z) (radius k) ∈ circSet ε := ⟨n, k, z, hz, rfl⟩
    simp [locModel, dif_pos hmem, resField]
  have hsc := scaleParamOn_halfDisc_congr (γ := γ) hag
  have hpos : 0 < scaleParamOn γ (locModel γ 0 ε (resField ε y, 0)) (halfDisc ε) := by
    rw [← hsc, hs]; exact h0
  have hgood := mem_goodN1_of_pos hpos
  unfold TmRichN1 zoomN1 canonicalOn
  rw [scaleSur_eq hgood, ← hsc, hs]
  exact locFieldFull_rescale_congr hag h0 (mul_lt_of_lt_div_succ h0 (hlt.trans_le hR1))

end D3Plus
end QuantumZipper
