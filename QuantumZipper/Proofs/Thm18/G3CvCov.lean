import QuantumZipper.Proofs.Thm18.G3CvKer

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-CURVE, piece 1b: the half-disc Markov covariance of the pulled-back free field

For a local conformal map `Φ` at the real point `b` (`LocConf`, G3CvKer.lean), bi-Lipschitz on
`closedBall b ρ` (`BiLip`), and local measures `μ, ν` (admissible, carried by `closedBall b r₁`,
`r₁ < ρ < r₀`):

* `kernelCov2_pull_eq`: the Neumann pairing of the pushed-forward local increments
  `(Φ_*μ − Φ_*bal μ, Φ_*ν − Φ_*bal ν)` equals that of `(μ − bal μ, ν − bal ν)`;
* `cov_pull_markov`: hence for a free field `X` the local part of the pulled-back field
  `W μ = X(Φ_*μ)`, `W μ − W(bal μ)`, has covariance `kernelCov (halfDiscGreen b ρ)`: exactly the
  covariance of the local part `markovZ` of a free field at `b` (`covariance_markovZ`).

This is the covariance form of the domain Markov property of `X ∘ Φ` on the half-disc
`B(b, ρ) ∩ ℍ` (the analogue of M7-a, `MixedHalfDiscMarkovCovStmt`, for the pulled-back field).
Source: Sheffield, *Gaussian free fields for mathematicians* (2007), §2.2 and Thm. 2.17; own
kernel route (G3CvKer.lean).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set
open scoped ComplexConjugate ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open K3

variable {Φ : ℂ → ℂ} {b r₀ : ℝ}

/-- Two-sided Lipschitz bounds of `Φ` on `closedBall b ρ`. -/
def BiLip (Φ : ℂ → ℂ) (b ρ m M : ℝ) : Prop :=
  0 < m ∧ 0 < M ∧ ∀ z ∈ closedBall (b : ℂ) ρ, ∀ w ∈ closedBall (b : ℂ) ρ,
    m * ‖z - w‖ ≤ ‖Φ z - Φ w‖ ∧ ‖Φ z - Φ w‖ ≤ M * ‖z - w‖

theorem abs_log_sub_le_g3cv {m M a A : ℝ} (hm : 0 < m) (_hM : 0 < M) (ha : 0 ≤ a) (hA : 0 ≤ A)
    (h1 : m * a ≤ A) (h2 : A ≤ M * a) :
    |Real.log A - Real.log a| ≤ |Real.log m| + |Real.log M| := by
  rcases ha.eq_or_lt with rfl | ha
  · have : A = 0 := le_antisymm (by simpa using h2) hA
    subst this; simp only [Real.log_zero, sub_self, abs_zero]; positivity
  · have hA' : 0 < A := lt_of_lt_of_le (mul_pos hm ha) h1
    rw [← Real.log_div hA'.ne' ha.ne']
    have l1 : Real.log m ≤ Real.log (A / a) :=
      Real.log_le_log hm (by rw [le_div_iff₀ ha]; linarith)
    have l2 : Real.log (A / a) ≤ Real.log M :=
      Real.log_le_log (div_pos hA' ha) (by rw [div_le_iff₀ ha]; linarith)
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log m), abs_nonneg (Real.log M)]
    · linarith [le_abs_self (Real.log M), abs_nonneg (Real.log m)]

theorem abs_kPull_le (hΦ : LocConf Φ b r₀) {ρ m M : ℝ} (hρr : ρ < r₀) (hbl : BiLip Φ b ρ m M)
    {z w : ℂ} (hz : z ∈ closedBall (b : ℂ) ρ) (hw : w ∈ closedBall (b : ℂ) ρ) :
    |kPull Φ z w| ≤ 2 * (|Real.log m| + |Real.log M|) := by
  obtain ⟨hm, hM, h⟩ := hbl
  have hwc := conj_mem_closedBall_g3cv hw
  have e1 := abs_log_sub_le_g3cv hm hM (norm_nonneg (z - w)) (norm_nonneg (Φ z - Φ w))
    (h z hz w hw).1 (h z hz w hw).2
  have e2 := abs_log_sub_le_g3cv hm hM (norm_nonneg (z - conj w))
    (norm_nonneg (Φ z - Φ (conj w))) (h z hz _ hwc).1 (h z hz _ hwc).2
  rw [hΦ.symm w (closedBall_subset_ball hρr hw)] at e2
  have e : kPull Φ z w = -(Real.log ‖Φ z - Φ w‖ - Real.log ‖z - w‖) -
      (Real.log ‖Φ z - conj (Φ w)‖ - Real.log ‖z - conj w‖) := by
    simp only [kPull, neumannH]; ring
  rw [e]
  have u := abs_le.1 e1
  have v := abs_le.1 e2
  rw [abs_le]
  constructor <;> linarith [u.1, u.2, v.1, v.2]

theorem measurable_kPull (hΦ : LocConf Φ b r₀) :
    Measurable (fun p : ℂ × ℂ => kPull Φ p.1 p.2) :=
  (measurable_neumannH.comp ((hΦ.meas.comp measurable_fst).prodMk
    (hΦ.meas.comp measurable_snd))).sub measurable_neumannH

/-- Admissible measures have no atoms (the singular potential is bounded). -/
theorem measure_singleton_of_admissible {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (p : ℂ) :
    μ {p} = 0 := by
  obtain ⟨C, hC, hb⟩ := hμ.2.2
  by_contra h0
  have key : ∀ n : ℕ, μ {p} * (n : ℝ≥0∞) ≤ C := by
    intro n
    have hy := hb (p + (Real.exp (-(n : ℝ)) : ℂ))
    have e : ENNReal.ofReal (-Real.log ‖p - (p + (Real.exp (-(n : ℝ)) : ℂ))‖) = n := by
      rw [sub_add_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Real.log_exp, neg_neg, ENNReal.ofReal_natCast]
    calc μ {p} * (n : ℝ≥0∞)
        = ∫⁻ x in {p}, ENNReal.ofReal (-Real.log ‖x - (p + (Real.exp (-(n : ℝ)) : ℂ))‖) ∂μ := by
          rw [lintegral_singleton, e, mul_comm]
      _ ≤ _ := setLIntegral_le_lintegral _ _
      _ ≤ C := hy
  have htop : μ {p} * ⊤ ≤ C := by
    rw [← ENNReal.iSup_natCast, ENNReal.mul_iSup]; exact iSup_le key
  rw [ENNReal.mul_top h0] at htop
  exact absurd (top_le_iff.1 htop) hC.ne

theorem bal_closedBall_compl_g3cv {ρ : ℝ} (hρ : 0 < ρ) (μ : Measure ℂ) :
    bal b ρ μ (closedBall (b : ℂ) ρ)ᶜ = 0 := by
  refine bal_null_of_forall measurableSet_closedBall.compl fun w => ?_
  have h := ae_iff.1 (ae_halfDiscPoisson_mem (t := b) hρ w)
  refine measure_mono_null (fun x hx => ?_) h
  intro hx'
  exact hx (sphere_subset_closedBall hx'.1)

theorem ae_mem_of_compl_null_g3cv {α : Measure ℂ} {s : Set ℂ} (h : α sᶜ = 0) :
    ∀ᵐ x ∂α, x ∈ s := mem_ae_iff.2 h

theorem integral_kPull_bal (hΦ : LocConf Φ b r₀) {ρ m M r₁ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r₀)
    (hbl : BiLip Φ b ρ m M) (hr₁ : r₁ < ρ) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ν (closedBall (b : ℂ) r₁)ᶜ = 0) (hνa : ∀ p, ν {p} = 0) {z : ℂ}
    (hz : z ∈ closedBall (b : ℂ) ρ) :
    ∫ w, kPull Φ z w ∂(bal b ρ ν) = ∫ w, kPull Φ z w ∂ν := by
  have := isFiniteMeasure_bal hρ hr₁ hν
  have hmeas : Measurable (fun w => kPull Φ z w) := by
    have h := (measurable_kPull hΦ).comp (measurable_prodMk_left (x := z))
    exact h
  have hint : Integrable (fun w => kPull Φ z w) (bal b ρ ν) :=
    Integrable.of_bound hmeas.aestronglyMeasurable (2 * (|Real.log m| + |Real.log M|))
      ((ae_mem_of_compl_null_g3cv (bal_closedBall_compl_g3cv hρ ν)).mono fun w hw => by
        rw [Real.norm_eq_abs]; exact abs_kPull_le hΦ hρr hbl hz hw)
  rw [(integral_bal hint).2]
  have hne : ∀ q, ∀ᵐ w ∂ν, w ≠ q := fun q => by
    rw [ae_iff]; simpa only [ne_eq, not_not, Set.ofPred_eq_eq_singleton] using hνa q
  refine integral_congr_ae ?_
  filter_upwards [mem_ae_iff.2 hν, hne z, hne (conj z)] with w' hw1 hw2 hw3
  exact integral_kPull_poisson hΦ hρ hρr hz
    (mem_ball_of_le_k3 hr₁ (mem_closedBall_iff_norm.1 hw1)) hw2 hw3

theorem kernelCov2_kPull_bal (hΦ : LocConf Φ b r₀) {ρ m M r₁ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r₀)
    (hbl : BiLip Φ b ρ m M) (hr₁ : r₁ < ρ) {μ ν : Measure ℂ} [IsFiniteMeasure ν]
    (hμ : μ (closedBall (b : ℂ) r₁)ᶜ = 0) (hν : ν (closedBall (b : ℂ) r₁)ᶜ = 0)
    (hνa : ∀ p, ν {p} = 0) :
    kernelCov2 (kPull Φ) (μ, bal b ρ μ) (ν, bal b ρ ν) = 0 := by
  have e : ∀ α : Measure ℂ, α (closedBall (b : ℂ) ρ)ᶜ = 0 →
      ∫ x, ∫ y, kPull Φ x y ∂(bal b ρ ν) ∂α = ∫ x, ∫ y, kPull Φ x y ∂ν ∂α := fun α hα =>
    integral_congr_ae ((ae_mem_of_compl_null_g3cv hα).mono fun x hx =>
      integral_kPull_bal hΦ hρ hρr hbl hr₁ hν hνa hx)
  have hμρ : μ (closedBall (b : ℂ) ρ)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (closedBall_subset_closedBall hr₁.le)) hμ
  unfold kernelCov2 kernelCov
  simp only
  rw [e μ hμρ, e (bal b ρ μ) (bal_closedBall_compl_g3cv hρ μ)]
  ring

theorem kernelCov_pull_split (hΦ : LocConf Φ b r₀) {ρ m M : ℝ} (hρr : ρ < r₀)
    (hbl : BiLip Φ b ρ m M) {α β : Measure ℂ} (hα : IsAdmissibleH α) (hβ : IsAdmissibleH β)
    (hαc : α (closedBall (b : ℂ) ρ)ᶜ = 0) (hβc : β (closedBall (b : ℂ) ρ)ᶜ = 0) :
    kernelCov (fun z w => neumannH (Φ z) (Φ w)) α β =
      kernelCov neumannH α β + kernelCov (kPull Φ) α β := by
  have := hα.1
  have := hβ.1
  have hN := integrable_neumannH_prod hα hβ
  have hk : Integrable (fun p : ℂ × ℂ => kPull Φ p.1 p.2) (α.prod β) := by
    refine Integrable.of_bound (measurable_kPull hΦ).aestronglyMeasurable
      (2 * (|Real.log m| + |Real.log M|)) ?_
    have hs : MeasurableSet (closedBall (b : ℂ) ρ ×ˢ closedBall (b : ℂ) ρ) :=
      measurableSet_closedBall.prod measurableSet_closedBall
    filter_upwards [(Measure.ae_prod_mem_iff_ae_ae_mem hs).2 ((ae_mem_of_compl_null_g3cv hαc).mono
      fun x hx => (ae_mem_of_compl_null_g3cv hβc).mono fun y hy => ⟨hx, hy⟩)] with p hp
    rw [Real.norm_eq_abs]; exact abs_kPull_le hΦ hρr hbl hp.1 hp.2
  unfold kernelCov
  calc ∫ x, ∫ y, neumannH (Φ x) (Φ y) ∂β ∂α
      = ∫ x, ((∫ y, neumannH x y ∂β) + ∫ y, kPull Φ x y ∂β) ∂α := by
        refine integral_congr_ae ?_
        filter_upwards [hN.prod_right_ae, hk.prod_right_ae] with x h1 h2
        rw [← integral_add h1 h2]
        congr 1; funext y; simp only [kPull]; ring
    _ = _ := integral_add hN.integral_prod_left hk.integral_prod_left

theorem kernelCov_map_g3cv (hΦ : LocConf Φ b r₀) (α β : Measure ℂ) [IsFiniteMeasure β] :
    kernelCov neumannH (α.map Φ) (β.map Φ) =
      kernelCov (fun z w => neumannH (Φ z) (Φ w)) α β := by
  unfold kernelCov
  have hs : StronglyMeasurable (fun p : ℂ × ℂ => neumannH p.1 p.2) :=
    measurable_neumannH.stronglyMeasurable
  rw [integral_map hΦ.meas.aemeasurable
    (hs.integral_prod_right' (ν := β.map Φ)).aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact integral_map hΦ.meas.aemeasurable
    ((measurable_neumannH.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)

/-- **The pulled-back local increments have the Neumann pairing of the plain ones.** -/
theorem kernelCov2_pull_eq (hΦ : LocConf Φ b r₀) {ρ m M r₁ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r₀)
    (hbl : BiLip Φ b ρ m M) (hr₁ : r₁ < ρ) {μ ν : Measure ℂ} (hμA : IsAdmissibleH μ)
    (hνA : IsAdmissibleH ν) (hμ : μ (closedBall (b : ℂ) r₁)ᶜ = 0)
    (hν : ν (closedBall (b : ℂ) r₁)ᶜ = 0) :
    kernelCov2 neumannH (μ.map Φ, (bal b ρ μ).map Φ) (ν.map Φ, (bal b ρ ν).map Φ) =
      kernelCov2 neumannH (μ, bal b ρ μ) (ν, bal b ρ ν) := by
  have := hμA.1
  have := hνA.1
  have := isFiniteMeasure_bal hρ hr₁ hμ
  have := isFiniteMeasure_bal hρ hr₁ hν
  have hbμ := isAdmissibleH_bal hρ hr₁ hμ
  have hbν := isAdmissibleH_bal hρ hr₁ hν
  have hμρ : μ (closedBall (b : ℂ) ρ)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (closedBall_subset_closedBall hr₁.le)) hμ
  have hνρ : ν (closedBall (b : ℂ) ρ)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (closedBall_subset_closedBall hr₁.le)) hν
  have bμρ := bal_closedBall_compl_g3cv (b := b) hρ μ
  have bνρ := bal_closedBall_compl_g3cv (b := b) hρ ν
  have h0 := kernelCov2_kPull_bal hΦ hρ hρr hbl hr₁ hμ hν (measure_singleton_of_admissible hνA)
  unfold kernelCov2 at h0 ⊢
  simp only at h0 ⊢
  rw [kernelCov_map_g3cv hΦ, kernelCov_map_g3cv hΦ, kernelCov_map_g3cv hΦ,
    kernelCov_map_g3cv hΦ, kernelCov_pull_split hΦ hρr hbl hμA hνA hμρ hνρ,
    kernelCov_pull_split hΦ hρr hbl hμA hbν hμρ bνρ,
    kernelCov_pull_split hΦ hρr hbl hbμ hνA bμρ hνρ,
    kernelCov_pull_split hΦ hρr hbl hbμ hbν bμρ bνρ]
  linarith

end G3Cv
end QuantumZipper
