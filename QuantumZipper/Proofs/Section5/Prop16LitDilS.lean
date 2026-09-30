import QuantumZipper.Proofs.Section5.Prop16LitRegPalm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: a measurable version of the canonical scale (D98)

`massB γ Z r a = ⨆ₙ lim_k ∫ χ_{a ∧ r, n} d(areaApprox γ Z k)` (cutoffs of `B(0, a ∧ r) ∩ ℍ`) and
`scaleQ γ Z r = inf {b ∈ ℚ, b > 0 : massB ≥ 1}`. For a measurable family they are measurable
(`measurable_scaleQ`), and when the local area limit on `B(0, r) ∩ ℍ` exists they are the local
mass `μ(B(0,a) ∩ ℍ)` and the canonical scale `scaleParamOn` (`scaleQ_eq_scaleParamOn`). Own
bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open ExA

/-- The mass of `B(0, a) ∩ ℍ` read through the cutoffs. -/
def massB (γ : ℝ) (Z : FieldSample) (r a : ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (limUnder atTop fun k => ∫ z, hbCut (min a r) n z ∂areaApprox γ Z k)

/-- The canonical scale through rational radii. -/
def scaleQ (γ : ℝ) (Z : FieldSample) (r : ℝ) : ℝ :=
  sInf {a : ℝ | ∃ b : ℚ, (b : ℝ) = a ∧ 0 < (b : ℝ) ∧ 1 ≤ massB γ Z r b}

theorem hbCut_mono {b : ℝ} (z : ℂ) : Monotone fun n : ℕ => hbCut b n z := by
  intro n n' hnn
  simp only [hbCut]
  by_cases hm : 0 ≤ min (b - ‖z‖) z.im
  · have : (n : ℝ) ≤ n' := by exact_mod_cast hnn
    gcongr
  · push_neg at hm
    have h1 : (n : ℝ) * min (b - ‖z‖) z.im - 1 < 0 := by
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [max_eq_left h1.le]
    exact min_le_min le_rfl (le_max_left _ _)

theorem iSup_hbCut {b : ℝ} (z : ℂ) :
    ⨆ n : ℕ, ENNReal.ofReal (hbCut b n z) = (ball 0 b ∩ H).indicator 1 z := by
  by_cases hz : z ∈ ball (0 : ℂ) b ∩ H
  · rw [indicator_of_mem hz, Pi.one_apply]
    have hm : 0 < min (b - ‖z‖) z.im := by
      obtain ⟨h1, h2⟩ := hz
      rw [mem_ball, dist_zero_right] at h1
      exact lt_min (by linarith) h2
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / min (b - ‖z‖) z.im)
    refine le_antisymm (iSup_le fun k => ?_) ?_
    · rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hbCut_le_one _ _ _)
    · refine le_iSup_of_le n ?_
      have h2 : 2 ≤ (n : ℝ) * min (b - ‖z‖) z.im := by
        rw [div_lt_iff₀ hm] at hn; linarith
      have : hbCut b n z = 1 := by
        simp only [hbCut]; rw [max_eq_right (by linarith), min_eq_left (by linarith)]
      rw [this, ENNReal.ofReal_one]
  · rw [indicator_of_notMem hz]
    refine le_antisymm (iSup_le fun n => ?_) (zero_le)
    have : hbCut b n z = 0 := by
      by_contra hne
      exact hz (tsupport_hbCut b n (subset_tsupport _ hne))
    rw [this, ENNReal.ofReal_zero]

/-- **The mass read through the cutoffs is the local mass.** -/
theorem massB_eq {γ : ℝ} {Z : FieldSample} {r : ℝ} {μ : Measure ℂ}
    (hμ : IsVagueLimitOn (ball 0 r ∩ H) (areaApprox γ Z) μ) (a : ℝ) :
    massB γ Z r a = μ (ball 0 a ∩ H) := by
  have hsub : ball (0 : ℂ) (min a r) ∩ H ⊆ ball 0 r ∩ H :=
    inter_subset_inter_left _ (ball_subset_ball (min_le_right _ _))
  have hlim : ∀ n : ℕ, limUnder atTop (fun k => ∫ z, hbCut (min a r) n z ∂areaApprox γ Z k) =
      ∫ z, hbCut (min a r) n z ∂μ := by
    intro n
    have hs : HasCompactSupport (hbCut (min a r) n) :=
      (isCompact_closedBall (0 : ℂ) (min a r)).of_isClosed_subset (isClosed_tsupport _)
        ((tsupport_hbCut _ n).trans (inter_subset_left.trans ball_subset_closedBall))
    exact (hμ.2.2 _ (continuous_hbCut _ n) hs ((tsupport_hbCut _ n).trans hsub)).limUnder_eq
  have hint : ∀ n : ℕ, ENNReal.ofReal (∫ z, hbCut (min a r) n z ∂μ) =
      ∫⁻ z, ENNReal.ofReal (hbCut (min a r) n z) ∂μ := by
    intro n
    have hs : HasCompactSupport (hbCut (min a r) n) :=
      (isCompact_closedBall (0 : ℂ) (min a r)).of_isClosed_subset (isClosed_tsupport _)
        ((tsupport_hbCut _ n).trans (inter_subset_left.trans ball_subset_closedBall))
    refine ofReal_integral_eq_lintegral_ofReal (VagueOpen.integrable_of_testFun
      (continuous_hbCut _ n) hs (hμ.2.1 _ hs ((tsupport_hbCut _ n).trans hsub)))
      (ae_of_all _ fun z => hbCut_nonneg _ n z)
  unfold massB
  simp_rw [hlim, hint]
  rw [← lintegral_iSup (fun n => ((continuous_hbCut _ n).measurable).ennreal_ofReal)
    (fun n n' h z => ENNReal.ofReal_le_ofReal (hbCut_mono z h))]
  simp_rw [iSup_hbCut]
  rw [lintegral_indicator_one (measurableSet_ball.inter isOpen_H.measurableSet)]
  -- the mass outside `B(0,r) ∩ ℍ` vanishes
  have e : ball (0 : ℂ) (min a r) ∩ H = (ball 0 a ∩ H) ∩ (ball 0 r ∩ H) := by
    ext z; simp only [mem_inter_iff, mem_ball, lt_min_iff]; tauto
  rw [e]
  exact measure_inter_conull' (measure_mono_null (diff_subset_compl _ _) hμ.1)

theorem scaleQ_set_bdd {γ : ℝ} {Z : FieldSample} {r : ℝ} :
    BddBelow {a : ℝ | ∃ b : ℚ, (b : ℝ) = a ∧ 0 < (b : ℝ) ∧ 1 ≤ massB γ Z r b} :=
  ⟨0, fun a ⟨b, hb, hb0, _⟩ => hb ▸ hb0.le⟩

/-- **The rational scale is the canonical scale** when the local limit exists. -/
theorem scaleQ_eq_scaleParamOn {γ : ℝ} {Z : FieldSample} {r : ℝ} {μ : Measure ℂ}
    (hμ : IsVagueLimitOn (ball 0 r ∩ H) (areaApprox γ Z) μ) :
    scaleQ γ Z r = scaleParamOn γ Z (ball 0 r ∩ H) := by
  have hq : qAreaMeasureOn γ Z (ball 0 r ∩ H) = μ :=
    LocalRule.qAreaMeasureOn_eq (isOpen_ball.inter isOpen_H) hμ
  unfold scaleQ scaleParamOn
  rw [hq]
  simp_rw [massB_eq hμ]
  set A := {a : ℝ | 0 < a ∧ 1 ≤ μ (ball 0 a ∩ H)} with hA
  set B := {a : ℝ | ∃ b : ℚ, (b : ℝ) = a ∧ 0 < (b : ℝ) ∧ 1 ≤ μ (ball 0 (b : ℝ) ∩ H)} with hB
  have hBA : B ⊆ A := fun a ⟨b, hb, hb0, h1⟩ => hb ▸ ⟨hb0, h1⟩
  have hbddA : BddBelow A := ⟨0, fun a ha => ha.1.le⟩
  have hbddB : BddBelow B := ⟨0, fun a ⟨b, hb, hb0, _⟩ => hb ▸ hb0.le⟩
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · have hBe : B = ∅ := eq_empty_of_subset_empty (hAe ▸ hBA)
    rw [hAe, hBe]
  -- every element of `A` is approached from above by rational elements of `B`
  have happ : ∀ a ∈ A, ∀ ε > 0, ∃ b ∈ B, b < a + ε := by
    intro a ha ε hε
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (by linarith : a < a + ε)
    refine ⟨q, ⟨q, rfl, ha.1.trans hq1, ha.2.trans (measure_mono ?_)⟩, hq2⟩
    exact inter_subset_inter_left _ (ball_subset_ball hq1.le)
  have hBne : B.Nonempty := by
    obtain ⟨a, ha⟩ := hAne
    obtain ⟨b, hb, -⟩ := happ a ha 1 one_pos
    exact ⟨b, hb⟩
  refine le_antisymm (le_csInf hAne fun a ha => ?_) (csInf_le_csInf hbddA hBne hBA)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨b, hb, hbε⟩ := happ a ha ε hε
  exact lt_of_le_of_lt (csInf_le hbddB hb) hbε

theorem measurable_massB {α : Type*} [MeasurableSpace α] {Z : α → FieldSample}
    (hZ : Measurable Z) {r : α → ℝ} (hr : Measurable r) (γ a : ℝ) :
    Measurable fun q => massB γ (Z q) (r q) a := by
  unfold massB
  refine Measurable.iSup fun n => ENNReal.measurable_ofReal.comp ?_
  have hT : Measurable fun p : α × ℂ => hbCut (min a (r p.1)) n p.2 := by
    unfold hbCut
    have h1 : Measurable fun p : α × ℂ => min a (r p.1) := measurable_const.min (hr.comp measurable_fst)
    exact measurable_const.min (measurable_const.max ((measurable_const.mul
      ((h1.sub (measurable_snd.norm)).min (Complex.measurable_im.comp measurable_snd))).sub
      measurable_const))
  exact (StronglyMeasurable.limUnder fun k =>
    (measurable_integral_areaApprox_fam hZ γ k (T := fun q z => hbCut (min a (r q)) n z)
      hT).stronglyMeasurable).measurable

/-- **Measurability of the rational scale.** -/
theorem measurable_scaleQ {α : Type*} [MeasurableSpace α] {Z : α → FieldSample}
    (hZ : Measurable Z) {r : α → ℝ} (hr : Measurable r) (γ : ℝ) :
    Measurable fun q => scaleQ γ (Z q) (r q) := by
  have hm := measurable_massB hZ hr γ
  refine measurable_of_Iio fun t => ?_
  have e : (fun q => scaleQ γ (Z q) (r q)) ⁻¹' Iio t =
      ({q | ∀ b : ℚ, ¬ (0 < (b : ℝ) ∧ 1 ≤ massB γ (Z q) (r q) b)} ∩ {_q | 0 < t}) ∪
        ⋃ b : ℚ, {q | (b : ℝ) < t ∧ 0 < (b : ℝ) ∧ 1 ≤ massB γ (Z q) (r q) b} := by
    ext q
    simp only [mem_preimage, mem_Iio, mem_union, mem_inter_iff, mem_setOf_eq, mem_iUnion]
    set S := {a : ℝ | ∃ b : ℚ, (b : ℝ) = a ∧ 0 < (b : ℝ) ∧ 1 ≤ massB γ (Z q) (r q) b} with hS
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · have hall : ∀ b : ℚ, ¬ (0 < (b : ℝ) ∧ 1 ≤ massB γ (Z q) (r q) b) := fun b hb =>
        (hSe ▸ (⟨b, rfl, hb.1, hb.2⟩ : (b : ℝ) ∈ S) : (b : ℝ) ∈ (∅ : Set ℝ))
      have h0 : scaleQ γ (Z q) (r q) = 0 := by
        show sInf S = 0; rw [hSe, Real.sInf_empty]
      rw [h0]
      constructor
      · intro ht; exact Or.inl ⟨hall, ht⟩
      · rintro (⟨-, ht⟩ | ⟨b, -, hb0, hb1⟩)
        · exact ht
        · exact absurd ⟨hb0, hb1⟩ (hall b)
    · constructor
      · intro ht
        obtain ⟨a, ⟨b, rfl, hb0, hb1⟩, hat⟩ := exists_lt_of_csInf_lt hSne ht
        exact Or.inr ⟨b, hat, hb0, hb1⟩
      · rintro (⟨hall, -⟩ | ⟨b, hbt, hb0, hb1⟩)
        · obtain ⟨a, b, rfl, hb0, hb1⟩ := hSne
          exact absurd ⟨hb0, hb1⟩ (hall b)
        · exact csInf_lt_of_lt scaleQ_set_bdd ⟨b, rfl, hb0, hb1⟩ hbt
  rw [e]
  refine MeasurableSet.union (MeasurableSet.inter ?_ (MeasurableSet.const _)) ?_
  · have : {q | ∀ b : ℚ, ¬ (0 < (b : ℝ) ∧ 1 ≤ massB γ (Z q) (r q) b)} =
        ⋂ b : ℚ, {q | ¬ (0 < (b : ℝ) ∧ 1 ≤ massB γ (Z q) (r q) b)} := by
      ext q; simp only [mem_setOf_eq, mem_iInter]
    rw [this]
    exact MeasurableSet.iInter fun b => ((MeasurableSet.const _).inter
      (measurableSet_le measurable_const (hm b))).compl
  · exact MeasurableSet.iUnion fun b => (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
      (measurableSet_le measurable_const (hm b)))

end Prop16Lit
end QuantumZipper
