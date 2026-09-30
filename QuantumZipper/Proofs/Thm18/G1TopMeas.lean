import QuantumZipper.Proofs.Thm18.R18ZipFacCore
import QuantumZipper.Proofs.Thm18.G1RegRepMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1TOP (1): the area of the side domain as a measurable function of (path, wedge data)

For the scaling argument behind `G1Z2SideTopSelStmt` (Sheffield, arXiv:1012.4797, §1.6, proof of
Theorem 1.8: `law(μ_h(D)) = law(e^{γC} μ_h(D))`) the side area `μ_h(ψ_a(ℍ))` must be a measurable
function of the path `a` and of the data of `h`. Here:

* `imgSet ψ`: a measurable subset of `path × ℂ` whose section at `a` is `ψ a '' ℍ` whenever
  `ψ a` is continuous on `ℍ` and maps `ℍ` into `ℍ` (`imgSet_section`): the image is the union over
  rational closed discs `K ⊆ ℍ` of the closures `ψ_a(K ∩ ℚ²)`‾ (compactness);
* `areaFn γ ψ (a, y)`: the measurable functional `⨆ₙ (1 + mₙ(y)) κₙ(y)(ψ_a(ℍ))` with the finite
  kernels `κₙ(y) = (1 + mₙ(y))⁻¹ μ_y|Kₙ` (`Kₙ` a compact exhaustion of `ℍ`, `mₙ(y) = μ_y(Kₙ)`), equal
  to `μ_y(ψ_a(ℍ))` (`areaFn_eq`), where `μ_y` is the area measure of the field reconstructed from
  the data `y` (`ZipFac.muD`).

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Top

/-- Rational points of `ℂ`. -/
def qc (q : ℚ × ℚ) : ℂ := ⟨q.1, q.2⟩

theorem exists_qc_near (w : ℂ) {ε : ℝ} (hε : 0 < ε) : ∃ u : ℚ × ℚ, ‖qc u - w‖ < ε := by
  obtain ⟨q1, h1, h1'⟩ := exists_rat_btwn (show w.re - ε / 2 < w.re + ε / 2 by linarith)
  obtain ⟨q2, h2, h2'⟩ := exists_rat_btwn (show w.im - ε / 2 < w.im + ε / 2 by linarith)
  refine ⟨(q1, q2), lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_⟩
  have e1 : (qc (q1, q2) - w).re = q1 - w.re := by simp [qc]
  have e2 : (qc (q1, q2) - w).im = q2 - w.im := by simp [qc]
  rw [e1, e2]
  have a1 : |(q1 : ℝ) - w.re| < ε / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
  have a2 : |(q2 : ℝ) - w.im| < ε / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
  linarith

/-- The measurable image set: its section at `a` is `ψ a '' ℍ` (for continuous `ψ a`). -/
def imgSet (ψ : (ℝ≥0 → ℝ) → ℂ → ℂ) : Set ((ℝ≥0 → ℝ) × ℂ) :=
  {p | p.2 ∈ H ∧ ∃ q : ℚ × ℚ, ∃ r : ℚ, (0 < r ∧ closedBall (qc q) r ⊆ H) ∧
    ∀ m : ℕ, ∃ u : ℚ × ℚ, qc u ∈ ball (qc q) r ∧ ‖ψ p.1 (qc u) - p.2‖ < 1 / ((m : ℝ) + 1)}

theorem measurableSet_imgSet {ψ : (ℝ≥0 → ℝ) → ℂ → ℂ} (hψ : ∀ w : ℂ, Measurable fun a => ψ a w) :
    MeasurableSet (imgSet ψ) := by
  have e : imgSet ψ = (Prod.snd ⁻¹' H) ∩ ⋃ q : ℚ × ℚ, ⋃ r : ℚ,
      ({_p | 0 < r ∧ closedBall (qc q) r ⊆ H} ∩ ⋂ m : ℕ, ⋃ u : ℚ × ℚ,
        ({_p | qc u ∈ ball (qc q) r} ∩
          {p : (ℝ≥0 → ℝ) × ℂ | ‖ψ p.1 (qc u) - p.2‖ < 1 / ((m : ℝ) + 1)})) := by
    ext p
    simp only [imgSet, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_iUnion, mem_iInter]
  rw [e]
  refine (isOpen_H.measurableSet.preimage measurable_snd).inter
    (MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun r => (MeasurableSet.const _).inter
      (MeasurableSet.iInter fun m => MeasurableSet.iUnion fun u => (MeasurableSet.const _).inter ?_))
  exact measurableSet_lt (((hψ (qc u)).comp measurable_fst).sub measurable_snd).norm
    measurable_const

theorem imgSet_section {ψ : (ℝ≥0 → ℝ) → ℂ → ℂ} {a : ℝ≥0 → ℝ} (hc : ContinuousOn (ψ a) H)
    (hH : MapsTo (ψ a) H H) : Prod.mk a ⁻¹' imgSet ψ = ψ a '' H := by
  ext z
  simp only [mem_preimage, imgSet, mem_setOf_eq, mem_image]
  constructor
  · rintro ⟨-, q, r, ⟨-, hsub⟩, hm⟩
    choose u hu hd using hm
    obtain ⟨v, hv, φ, hφ, hlim⟩ := (isCompact_closedBall (qc q) (r : ℝ)).tendsto_subseq
      (x := fun m => qc (u m)) (fun m => ball_subset_closedBall (hu m))
    have hvH : v ∈ H := hsub hv
    have h1 : Tendsto (fun m => ψ a (qc (u (φ m)))) atTop (𝓝 (ψ a v)) :=
      ((hc v hvH).continuousAt (isOpen_H.mem_nhds hvH)).tendsto.comp hlim
    have h2 : Tendsto (fun m => ψ a (qc (u (φ m)))) atTop (𝓝 z) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun m => (hd (φ m)).le) ?_
      exact (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
    exact ⟨v, hvH, tendsto_nhds_unique h1 h2⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨hH hw, ?_⟩
    have him : 0 < w.im := hw
    obtain ⟨q, hq⟩ := exists_qc_near w (show 0 < w.im / 4 by positivity)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show w.im / 4 < 2 * (w.im / 4) by linarith)
    have hwb : ‖w - qc q‖ < r := by rw [norm_sub_rev]; linarith
    have hsub : closedBall (qc q) (r : ℝ) ⊆ H := fun z hz => by
      have h1 : ‖z - qc q‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hz
      have h4 : ‖z - w‖ ≤ ‖z - qc q‖ + ‖qc q - w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      have h5 := (abs_le.1 (Complex.abs_im_le_norm (z - w))).1
      simp only [Complex.sub_im] at h5
      show 0 < z.im
      linarith
    refine ⟨q, r, ⟨by exact_mod_cast (show (0 : ℝ) < r by linarith), hsub⟩, fun m => ?_⟩
    obtain ⟨ε, hε, hεd⟩ := Metric.continuousOn_iff.1 hc w hw (1 / ((m : ℝ) + 1)) (by positivity)
    obtain ⟨u, hu⟩ := exists_qc_near w (lt_min hε (sub_pos.2 hwb))
    have hu1 : ‖qc u - w‖ < ε := lt_of_lt_of_le hu (min_le_left _ _)
    have hu2 : ‖qc u - w‖ < r - ‖w - qc q‖ := lt_of_lt_of_le hu (min_le_right _ _)
    have hub : qc u ∈ ball (qc q) r := by
      rw [mem_ball, dist_eq_norm]
      linarith [norm_sub_le_norm_sub_add_norm_sub (qc u) w (qc q)]
    refine ⟨u, hub, ?_⟩
    have := hεd (qc u) (hsub (ball_subset_closedBall hub)) (by rwa [dist_eq_norm])
    rwa [dist_eq_norm] at this

/-! ## The area functional -/

/-- A compact exhaustion of `ℍ`. -/
def Kx (n : ℕ) : Set ℂ := {z | ‖z‖ ≤ n ∧ 1 / ((n : ℝ) + 1) ≤ z.im}

theorem isCompact_Kx (n : ℕ) : IsCompact (Kx n) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_im)
  · exact (isBounded_closedBall (x := (0 : ℂ)) (r := n)).subset fun z hz => by
      simpa [mem_closedBall, dist_zero_right] using hz.1

theorem Kx_sub_H (n : ℕ) : Kx n ⊆ H := fun z hz =>
  lt_of_lt_of_le (by positivity) hz.2

theorem Kx_mono : Monotone Kx := fun m n hmn z hz => by
  have h : (m : ℝ) ≤ n := by exact_mod_cast hmn
  refine ⟨hz.1.trans h, le_trans ?_ hz.2⟩
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem iUnion_Kx : ⋃ n, Kx n = H := by
  refine subset_antisymm (iUnion_subset Kx_sub_H) fun z hz => ?_
  have him : 0 < z.im := hz
  obtain ⟨n, hn⟩ := exists_nat_gt (‖z‖ + 1 / z.im)
  refine mem_iUnion.2 ⟨n, ?_, ?_⟩
  · have : 0 < 1 / z.im := by positivity
    linarith
  · rw [div_le_iff₀ (by positivity)]
    have h1 : 1 / z.im < n := by linarith [norm_nonneg z]
    rw [div_lt_iff₀ him] at h1
    nlinarith

/-- The area measure of the field reconstructed from wedge data (`0` off good fields). -/
def muY (γ : ℝ) (y : (ℕ → ℝ) × (TestFun H → ℝ)) : Measure ℂ :=
  R18.ZipFac.muD γ (y, fun _ => 0)

theorem measurable_muY (γ : ℝ) : Measurable (muY γ) :=
  (R18.ZipFac.measurable_muD γ).comp (measurable_id.prodMk measurable_const)

theorem muY_Kx_lt_top (γ : ℝ) (y : (ℕ → ℝ) × (TestFun H → ℝ)) (n : ℕ) : muY γ y (Kx n) < ⊤ :=
  R18.ZipFac.muD_isLocFin γ _ _ (isCompact_Kx n) (Kx_sub_H n)

theorem muY_dataFull {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x) :
    muY γ (WedgeMeas.dataFull H x) = qAreaMeasure γ x :=
  R18.ZipFac.muD_cfgData (x := (x, fun _ => 0)) hx

/-- The finite kernels `(1 + μ_y(Kₙ))⁻¹ μ_y|Kₙ`. -/
def kerN (γ : ℝ) (n : ℕ) : Kernel ((ℝ≥0 → ℝ) × ((ℕ → ℝ) × (TestFun H → ℝ))) ℂ where
  toFun p := (1 + muY γ p.2 (Kx n))⁻¹ • (muY γ p.2).restrict (Kx n)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
    have hK := (isCompact_Kx n).measurableSet
    exact ((((Measure.measurable_coe hK).comp (measurable_muY γ)).comp
      measurable_snd).const_add 1).inv.mul
      (((Measure.measurable_coe (hs.inter hK)).comp (measurable_muY γ)).comp measurable_snd)

instance (γ : ℝ) (n : ℕ) : IsFiniteKernel (kerN γ n) := by
  refine ⟨⟨1, ENNReal.one_lt_top, fun p => ?_⟩⟩
  show ((1 + muY γ p.2 (Kx n))⁻¹ • (muY γ p.2).restrict (Kx n)) univ ≤ 1
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul,
    mul_comm, ← div_eq_mul_inv]
  exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_add_self)

/-- **The measurable side-area functional.** -/
def areaFn (γ : ℝ) (ψ : (ℝ≥0 → ℝ) → ℂ → ℂ)
    (p : (ℝ≥0 → ℝ) × ((ℕ → ℝ) × (TestFun H → ℝ))) : ℝ≥0∞ :=
  ⨆ n : ℕ, (1 + muY γ p.2 (Kx n)) * kerN γ n p (Prod.mk p.1 ⁻¹' imgSet ψ)

theorem measurable_areaFn (γ : ℝ) {ψ : (ℝ≥0 → ℝ) → ℂ → ℂ}
    (hψ : ∀ w : ℂ, Measurable fun a => ψ a w) : Measurable (areaFn γ ψ) := by
  refine Measurable.iSup fun n => ?_
  have hK := (isCompact_Kx n).measurableSet
  refine ((((Measure.measurable_coe hK).comp (measurable_muY γ)).comp measurable_snd).const_add
    1).mul ?_
  exact Kernel.measurable_kernel_prodMk_left (κ := kerN γ n)
    (t := {x : ((ℝ≥0 → ℝ) × ((ℕ → ℝ) × (TestFun H → ℝ))) × ℂ | (x.1.1, x.2) ∈ imgSet ψ})
    ((measurableSet_imgSet hψ).preimage (measurable_fst.fst.prodMk measurable_snd))

theorem areaFn_eq (γ : ℝ) {ψ : (ℝ≥0 → ℝ) → ℂ → ℂ}
    (p : (ℝ≥0 → ℝ) × ((ℕ → ℝ) × (TestFun H → ℝ))) :
    areaFn γ ψ p = muY γ p.2 (Prod.mk p.1 ⁻¹' imgSet ψ) := by
  set S := Prod.mk p.1 ⁻¹' imgSet ψ with hS
  have hSH : S ⊆ H := fun z hz => hz.1
  have hn : ∀ n : ℕ, (1 + muY γ p.2 (Kx n)) * kerN γ n p S = muY γ p.2 (S ∩ Kx n) := by
    intro n
    have hK := (isCompact_Kx n).measurableSet
    show (1 + muY γ p.2 (Kx n)) * ((1 + muY γ p.2 (Kx n))⁻¹ • (muY γ p.2).restrict (Kx n)) S = _
    rw [Measure.smul_apply, Measure.restrict_apply' hK, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel (ne_of_gt (lt_of_lt_of_le zero_lt_one le_self_add))
        (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, (muY_Kx_lt_top γ p.2 n).ne⟩), one_mul]
  unfold areaFn
  simp only [← hS, hn]
  have hmono : Monotone fun n => S ∩ Kx n := fun m n hmn => inter_subset_inter_right _ (Kx_mono hmn)
  rw [← hmono.measure_iUnion, ← inter_iUnion, iUnion_Kx, inter_eq_left.2 hSH]

end G1Top
end QuantumZipper
