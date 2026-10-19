import GaussianLQG.LQG.Scaling.Measurability
import LQGMetric.LFPP.ContMetric
import LQGMetric.Field.ExistGFF
import LQGMetric.Papers.GM.S1.FieldAux

/-!
# Passage to the limit (blueprint A.7), part 1: tools

Deterministic and measure-theoretic tools for the passage from uniform LFPP moment bounds (★) to
the canonical γ-LQG metric (blueprint Appendix A.7, as corrected by audit A5; Route U step U16 of
`planning/audits/B1-S6-feasibility.md`).

* Comparison under pointwise domination: `holderConst_le_ofReal_mul` (`d ≤ a d'` on `K × K` gives
  `A_d(K) ≤ a A_{d'}(K)`) and `sepInf_inv_le_ofReal_mul` (`d' ≤ a d` on the `δ`-separated pairs
  gives `I_d(K, δ)⁻¹ ≤ a I_{d'}(K, δ)⁻¹`).
* Semicontinuity under pointwise convergence: `holderConst_le_liminf` (a supremum of pointwise
  limits is at most the `liminf` of the suprema) and `sepInf_inv_le_liminf` (the same for the
  inverse of an infimum).
* `exists_subseq_ae_tendsto`: convergence in probability for the local uniform topology
  (`LQGMetric.TendstoInProbLU`) gives almost sure pointwise convergence along a subsequence
  (Borel–Cantelli on the squares `B̄_{k+1} × B̄_{k+1}`).
* A.e.-measurability: `aemeasurable_holderConst`, `aemeasurable_sepInf` for random functions that
  are a.s. continuous and a.e.-measurable at each point (the supremum and infimum may be taken over
  a countable dense set of pairs), and their LFPP instances `aemeasurable_holderConst_lfppDist`,
  `aemeasurable_sepInf_lfppDist` under `normGFFLaw`.
* `isProbabilityMeasure_normGFFLaw`, `isWholePlaneGFF_id_normGFFLaw`: the canonical probability
  space `(𝒟'(ℂ), normGFFLaw)` of the normalized whole-plane GFF.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG
namespace UniformLimit

/-! ## Elementary bounds for the Hölder constant and the separated infimum -/

theorem ofReal_le_holderConst {d : ℂ × ℂ → ℝ} {K : Set ℂ} {z w : ℂ} (hz : z ∈ K) (hw : w ∈ K)
    (hzw : z ≠ w) : ENNReal.ofReal (d (z, w) / ‖z - w‖ ^ (1 / 2 : ℝ)) ≤ holderConst d K :=
  le_iSup₂_of_le z hz (le_iSup₂_of_le w hw (le_iSup_of_le hzw le_rfl))

theorem holderConst_le {d : ℂ × ℂ → ℝ} {K : Set ℂ} {b : ℝ≥0∞}
    (h : ∀ z ∈ K, ∀ w ∈ K, z ≠ w → ENNReal.ofReal (d (z, w) / ‖z - w‖ ^ (1 / 2 : ℝ)) ≤ b) :
    holderConst d K ≤ b :=
  iSup₂_le fun z hz => iSup₂_le fun w hw => iSup_le fun hzw => h z hz w hw hzw

theorem sepInf_le_ofReal {d : ℂ × ℂ → ℝ} {K : Set ℂ} {δ : ℝ} {z w : ℂ} (hz : z ∈ K) (hw : w ∈ K)
    (hzw : δ ≤ ‖z - w‖) : sepInf d K δ ≤ ENNReal.ofReal (d (z, w)) :=
  iInf₂_le_of_le z hz (iInf₂_le_of_le w hw (iInf_le_of_le hzw le_rfl))

theorem le_sepInf {d : ℂ × ℂ → ℝ} {K : Set ℂ} {δ : ℝ} {b : ℝ≥0∞}
    (h : ∀ z ∈ K, ∀ w ∈ K, δ ≤ ‖z - w‖ → b ≤ ENNReal.ofReal (d (z, w))) : b ≤ sepInf d K δ :=
  le_iInf₂ fun z hz => le_iInf₂ fun w hw => le_iInf fun hzw => h z hz w hw hzw

theorem sepInf_inv_le {d : ℂ × ℂ → ℝ} {K : Set ℂ} {δ : ℝ} {b : ℝ≥0∞}
    (h : ∀ z ∈ K, ∀ w ∈ K, δ ≤ ‖z - w‖ → (ENNReal.ofReal (d (z, w)))⁻¹ ≤ b) :
    (sepInf d K δ)⁻¹ ≤ b :=
  ENNReal.inv_le_iff_inv_le.2 (le_sepInf fun z hz w hw hzw =>
    ENNReal.inv_le_iff_inv_le.1 (h z hz w hw hzw))

/-! ## Comparison under pointwise domination -/

/-- If `d ≤ a d'` on `K × K` then `A_d(K) ≤ a A_{d'}(K)`. -/
theorem holderConst_le_ofReal_mul {d d' : ℂ × ℂ → ℝ} {K : Set ℂ} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ z ∈ K, ∀ w ∈ K, d (z, w) ≤ a * d' (z, w)) :
    holderConst d K ≤ ENNReal.ofReal a * holderConst d' K := by
  refine holderConst_le fun z hz w hw hzw => ?_
  calc ENNReal.ofReal (d (z, w) / ‖z - w‖ ^ (1 / 2 : ℝ))
      ≤ ENNReal.ofReal (a * (d' (z, w) / ‖z - w‖ ^ (1 / 2 : ℝ))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (h z hz w hw) (Real.rpow_nonneg (norm_nonneg _) _)
    _ = ENNReal.ofReal a * ENNReal.ofReal (d' (z, w) / ‖z - w‖ ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_mul ha
    _ ≤ ENNReal.ofReal a * holderConst d' K := by
        gcongr
        exact ofReal_le_holderConst hz hw hzw

/-- If `d' ≤ a d` on the `δ`-separated pairs of `K` (with `a > 0`) then
`I_d(K, δ)⁻¹ ≤ a I_{d'}(K, δ)⁻¹`. -/
theorem sepInf_inv_le_ofReal_mul {d d' : ℂ × ℂ → ℝ} {K : Set ℂ} {δ a : ℝ} (ha : 0 < a)
    (h : ∀ z ∈ K, ∀ w ∈ K, δ ≤ ‖z - w‖ → d' (z, w) ≤ a * d (z, w)) :
    (sepInf d K δ)⁻¹ ≤ ENNReal.ofReal a * (sepInf d' K δ)⁻¹ := by
  have ha0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.2 ha).ne'
  refine sepInf_inv_le fun z hz w hw hzw => ?_
  have h1 : sepInf d' K δ ≤ ENNReal.ofReal a * ENNReal.ofReal (d (z, w)) := by
    rw [← ENNReal.ofReal_mul ha.le]
    exact (sepInf_le_ofReal hz hw hzw).trans (ENNReal.ofReal_le_ofReal (h z hz w hw hzw))
  have h2 : (ENNReal.ofReal a * ENNReal.ofReal (d (z, w)))⁻¹ ≤ (sepInf d' K δ)⁻¹ :=
    ENNReal.inv_le_inv.2 h1
  rw [ENNReal.mul_inv (Or.inl ha0) (Or.inl ENNReal.ofReal_ne_top)] at h2
  calc (ENNReal.ofReal (d (z, w)))⁻¹
      = ENNReal.ofReal a * ((ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal (d (z, w)))⁻¹) :=
        (ENNReal.mul_inv_cancel_left ha0 ENNReal.ofReal_ne_top).symm
    _ ≤ ENNReal.ofReal a * (sepInf d' K δ)⁻¹ := by gcongr

/-! ## Semicontinuity under pointwise convergence -/

/-- **Lower semicontinuity of the Hölder constant**: if `f_k → d` pointwise and
`A_{f_k}(K) ≤ b_k`, then `A_d(K) ≤ liminf b_k`. -/
theorem holderConst_le_liminf {f : ℕ → ℂ × ℂ → ℝ} {d : ℂ × ℂ → ℝ} {K : Set ℂ}
    (hf : ∀ q, Tendsto (fun k => f k q) atTop (𝓝 (d q))) {b : ℕ → ℝ≥0∞}
    (hb : ∀ k, holderConst (f k) K ≤ b k) : holderConst d K ≤ liminf b atTop := by
  refine holderConst_le fun z hz w hw hzw => ?_
  have ht : Tendsto (fun k => ENNReal.ofReal (f k (z, w) / ‖z - w‖ ^ (1 / 2 : ℝ))) atTop
      (𝓝 (ENNReal.ofReal (d (z, w) / ‖z - w‖ ^ (1 / 2 : ℝ)))) :=
    ENNReal.tendsto_ofReal ((hf (z, w)).div_const _)
  rw [← ht.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun k =>
    (ofReal_le_holderConst hz hw hzw).trans (hb k))

/-- **Upper semicontinuity of the separated infimum**, in inverse form: if `f_k → d` pointwise
and `I_{f_k}(K, δ)⁻¹ ≤ b_k`, then `I_d(K, δ)⁻¹ ≤ liminf b_k`. -/
theorem sepInf_inv_le_liminf {f : ℕ → ℂ × ℂ → ℝ} {d : ℂ × ℂ → ℝ} {K : Set ℂ} {δ : ℝ}
    (hf : ∀ q, Tendsto (fun k => f k q) atTop (𝓝 (d q))) {b : ℕ → ℝ≥0∞}
    (hb : ∀ k, (sepInf (f k) K δ)⁻¹ ≤ b k) : (sepInf d K δ)⁻¹ ≤ liminf b atTop := by
  refine sepInf_inv_le fun z hz w hw hzw => ?_
  have ht : Tendsto (fun k => (ENNReal.ofReal (f k (z, w)))⁻¹) atTop
      (𝓝 (ENNReal.ofReal (d (z, w)))⁻¹) :=
    (ENNReal.tendsto_ofReal (hf (z, w))).inv
  rw [← ht.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun k =>
    (ENNReal.inv_le_inv.2 (sepInf_le_ofReal hz hw hzw)).trans (hb k))

/-! ## Almost sure convergence along a subsequence -/

/-- **Convergence in probability for the local uniform topology gives almost sure pointwise
convergence along a subsequence** (Borel–Cantelli on the squares `B̄_{k+1} × B̄_{k+1}`). -/
theorem exists_subseq_ae_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℂ × ℂ → ℝ} {Y : Ω → ℂ × ℂ → ℝ} (hT : LQGMetric.TendstoInProbLU P X atTop Y) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂P, ∀ q : ℂ × ℂ,
      Tendsto (fun k => X (ns k) ω q) atTop (𝓝 (Y ω q)) := by
  set r : ℝ≥0∞ := 2⁻¹ with hr
  have hr0 : ∀ k : ℕ, 0 < r ^ k := fun k =>
    ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) k
  let B : ℕ → Set (ℂ × ℂ) := fun k =>
    Metric.closedBall (0 : ℂ) ((k : ℝ) + 1) ×ˢ Metric.closedBall (0 : ℂ) ((k : ℝ) + 1)
  let E : ℕ → ℕ → Set Ω := fun k n =>
    {ω | ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k) ≤ ⨆ q ∈ B k, edist (X n ω q) (Y ω q)}
  have hev : ∀ k : ℕ, ∀ᶠ n in atTop, P (E k n) < r ^ k := fun k =>
    (tendsto_order.1 (hT ((k : ℝ) + 1) (by positivity) ((2 : ℝ)⁻¹ ^ k) (by positivity))).2 _
      (hr0 k)
  obtain ⟨ns, hns, hP⟩ := extraction_forall_of_eventually hev
  refine ⟨ns, hns, ?_⟩
  have hgeo : (∑' k : ℕ, r ^ k) ≠ ∞ := by
    rw [ENNReal.tsum_geometric, hr, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  have hsum : (∑' k : ℕ, P (E k (ns k))) ≠ ∞ :=
    ne_top_of_le_ne_top hgeo (ENNReal.tsum_le_tsum fun k => (hP k).le)
  have hδ : Tendsto (fun k : ℕ => ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num))
    rwa [ENNReal.ofReal_zero] at this
  filter_upwards [ae_eventually_notMem hsum] with ω hω q
  rw [tendsto_iff_edist_tendsto_0]
  obtain ⟨k₀, hk₀⟩ := exists_nat_ge (max ‖q.1‖ ‖q.2‖)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hδ
    (Eventually.of_forall fun k => zero_le) ?_
  filter_upwards [hω, eventually_ge_atTop k₀] with k hk hkk
  have hkR : max ‖q.1‖ ‖q.2‖ ≤ (k : ℝ) + 1 := by
    have : (k₀ : ℝ) ≤ k := by exact_mod_cast hkk
    linarith
  have hq : q ∈ B k := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (le_max_left _ _).trans hkR
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (le_max_right _ _).trans hkR
  have hk' : ¬ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k) ≤ ⨆ q ∈ B k, edist (X (ns k) ω q) (Y ω q) := hk
  exact ((le_iSup₂ (f := fun q (_ : q ∈ B k) => edist (X (ns k) ω q) (Y ω q)) q hq).trans
    (not_le.1 hk').le)

/-! ## A.e.-measurability of the Hölder constant and the separated infimum -/

section AEMeas

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {X : α → ℂ × ℂ → ℝ}

/-- `a ↦ A_{X(a)}(K)` is a.e.-measurable if `X(a)` is a.s. continuous and `a ↦ X(a)(q)` is
a.e.-measurable for every `q`: the supremum may be taken over a countable dense set of pairs. -/
theorem aemeasurable_holderConst (hc : ∀ᵐ a ∂μ, Continuous (X a))
    (hm : ∀ q, AEMeasurable (fun a => X a q) μ) (K : Set ℂ) :
    AEMeasurable (fun a => holderConst (X a) K) μ := by
  set S : Set (ℂ × ℂ) := {q | q.1 ∈ K ∧ q.2 ∈ K ∧ q.1 ≠ q.2}
  obtain ⟨T, hTc, hTS, hST⟩ := TopologicalSpace.exists_countable_dense_subset S
  have : Countable T := hTc.to_subtype
  have hF : AEMeasurable (fun a => ⨆ q : T,
      ENNReal.ofReal (X a q / ‖(q : ℂ × ℂ).1 - (q : ℂ × ℂ).2‖ ^ (1 / 2 : ℝ))) μ :=
    AEMeasurable.iSup fun q => ((hm q).div_const _).ennreal_ofReal
  refine hF.congr ?_
  filter_upwards [hc] with a ha
  have hcont : ContinuousOn (fun q : ℂ × ℂ =>
      ENNReal.ofReal (X a q / ‖q.1 - q.2‖ ^ (1 / 2 : ℝ))) S := by
    refine ENNReal.continuous_ofReal.comp_continuousOn
      (ContinuousOn.div ha.continuousOn ?_ fun p hp => ?_)
    · exact (Continuous.continuousOn (by fun_prop)).rpow_const fun _ _ => Or.inr (by norm_num)
    · exact (Real.rpow_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hp.2.2)) _).ne'
  rw [holderConst_eq_biSup_pairs, biSup_eq_biSup_of_subset_closure hTS hST hcont, iSup_subtype']

/-- `a ↦ I_{X(a)}(K, δ)` is a.e.-measurable under the same hypotheses. -/
theorem aemeasurable_sepInf (hc : ∀ᵐ a ∂μ, Continuous (X a))
    (hm : ∀ q, AEMeasurable (fun a => X a q) μ) (K : Set ℂ) (δ : ℝ) :
    AEMeasurable (fun a => sepInf (X a) K δ) μ := by
  set S : Set (ℂ × ℂ) := {q | q.1 ∈ K ∧ q.2 ∈ K ∧ δ ≤ ‖q.1 - q.2‖}
  obtain ⟨T, hTc, hTS, hST⟩ := TopologicalSpace.exists_countable_dense_subset S
  have : Countable T := hTc.to_subtype
  have hF : AEMeasurable (fun a => ⨅ q : T, ENNReal.ofReal (X a q)) μ :=
    AEMeasurable.iInf fun q => (hm q).ennreal_ofReal
  refine hF.congr ?_
  filter_upwards [hc] with a ha
  rw [sepInf_eq_biInf_pairs, biInf_eq_biInf_of_subset_closure
    (F := fun q => ENNReal.ofReal (X a q)) hTS hST
    (ENNReal.continuous_ofReal.comp ha).continuousOn, iInf_subtype']

end AEMeas

/-! ## The canonical space of the normalized GFF and the LFPP functionals -/

/-- `normGFFLaw` is a probability measure. -/
theorem isProbabilityMeasure_normGFFLaw : IsProbabilityMeasure LQGMetric.normGFFLaw := by
  obtain ⟨Ω, _, P, hP, h, hh⟩ := LQGMetric.GFFExist.exists_normalizedWPGFF
  rw [LQGMetric.GM.normGFFLaw_eq hh]
  infer_instance

/-- The identity on `(𝒟'(ℂ), normGFFLaw)` is a whole-plane GFF. -/
theorem isWholePlaneGFF_id_normGFFLaw : LQGMetric.IsWholePlaneGFF id LQGMetric.normGFFLaw := by
  obtain ⟨Ω, _, P, hP, h, hh⟩ := LQGMetric.GFFExist.exists_normalizedWPGFF
  rw [LQGMetric.GM.normGFFLaw_eq hh]
  exact LQGMetric.GM.isWholePlaneGFF_id_map hh.1

/-- A rescaled LFPP distance is a.s. continuous under `normGFFLaw`. -/
theorem ae_continuous_lfppDist {ξ ε : ℝ} (hε : ε ≠ 0) (a : ℝ) :
    ∀ᵐ g ∂LQGMetric.normGFFLaw, Continuous fun q => a * LQGMetric.lfppDist ξ ε g q := by
  filter_upwards [LQGMetric.LFPP.ae_continuous_heatMollify_normGFFLaw hε] with g hg
  rw [LQGMetric.LFPP.lfppDist_eq_lfppDReal]
  exact continuous_const.mul (LQGMetric.LFPP.continuous_lfppDReal hg)

/-- A rescaled LFPP distance between two fixed points is a.e.-measurable under `normGFFLaw`. -/
theorem aemeasurable_lfppDist_apply {ξ ε : ℝ} (hε : ε ≠ 0) (a : ℝ) (q : ℂ × ℂ) :
    AEMeasurable (fun g => a * LQGMetric.lfppDist ξ ε g q) LQGMetric.normGFFLaw :=
  ((LQGMetric.LFPP.aemeasurable_lfppDistE
    (LQGMetric.LFPP.ae_continuous_heatMollify_normGFFLaw hε) q.1 q.2).ennreal_toReal).const_mul a

/-- The Hölder constant of a rescaled LFPP distance is a.e.-measurable under `normGFFLaw`. -/
theorem aemeasurable_holderConst_lfppDist {ξ ε : ℝ} (hε : ε ≠ 0) (a : ℝ) (K : Set ℂ) :
    AEMeasurable (fun g => holderConst (fun q => a * LQGMetric.lfppDist ξ ε g q) K)
      LQGMetric.normGFFLaw :=
  aemeasurable_holderConst (ae_continuous_lfppDist hε a) (aemeasurable_lfppDist_apply hε a) K

/-- The separated infimum of a rescaled LFPP distance is a.e.-measurable under `normGFFLaw`. -/
theorem aemeasurable_sepInf_lfppDist {ξ ε : ℝ} (hε : ε ≠ 0) (a : ℝ) (K : Set ℂ) (δ : ℝ) :
    AEMeasurable (fun g => sepInf (fun q => a * LQGMetric.lfppDist ξ ε g q) K δ)
      LQGMetric.normGFFLaw :=
  aemeasurable_sepInf (ae_continuous_lfppDist hε a) (aemeasurable_lfppDist_apply hε a) K δ

end UniformLimit
end GaussianLQG
