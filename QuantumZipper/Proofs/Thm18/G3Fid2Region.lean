import QuantumZipper.Proofs.Thm18.G3Fid2Geom
import QuantumZipper.Proofs.Thm18.G3Fid2Cut
import QuantumZipper.Proofs.Zipper.E1TransferM4Cert

/-!
# G3 fidelity F2 (part 3): boundary measures of the region and gap fields (deterministic)

Let `y` be a field sample whose boundary approximations are finite on compacts and converge
vaguely to an atomless `ν` (`γ > 0`). Then (`regionCut`, `gapCut`):

* the region field `restrictField (circIn t r) y` has `BCert`, and its boundary measure is
  `ν` restricted to `(t − r, t + r)`;
* the gap field `restrictField (circOut t₁ r₁ t₂ r₂) y` (`r₁, r₂ > 0`) has `BCert`, and its
  boundary measure is `ν` restricted to the complement of `[t₁ − r₁, t₁ + r₁] ∪ [t₂ − r₂, t₂ + r₂]`.

At scale `2^{-k}` the approximation of the restricted field is exactly that of `y` on the points
whose circles are read (`G3Fid2Geom`), and the constant `2^{-kγ²/4}` on the points whose circles
are discarded (junk value `0`), up to finitely many tangency points; the limit follows from the
cut lemma (`G3Fid2Cut`), the tangential circles at the disc edges being handled by the absence
of atoms. This is the locality of the Duplantier–Sheffield boundary measure (Duplantier–Sheffield,
*Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), (1.2) and §6: `ν` is the limit of
`ε^{γ²/4} e^{γ h_ε/2} dx` and `h_ε(x)` only depends on `h` near `B_ε(x)`); the bookkeeping is our
own (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Fid

/-! ## Two more circle facts (circles enclosing a disc) -/

theorem norm_circleMap_sub_ge (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (θ t : ℝ) :
    ρ - ‖c - t‖ ≤ ‖circleMap c ρ θ - t‖ := by
  rw [circleMap_sub_real]
  have h := norm_sub_norm_le (circleMap (c - t) ρ θ - (c - t)) (-(c - t))
  have e : circleMap (c - t) ρ θ - (c - t) = ρ * Complex.exp (θ * Complex.I) := by
    simp only [circleMap]; ring
  rw [sub_neg_eq_add, sub_add_cancel, norm_neg, e, norm_mul, Complex.norm_exp_ofReal_mul_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ] at h
  exact h

theorem fc_ball_null' {t r ρ : ℝ} (hρ : 0 ≤ ρ) {c : ℂ} (h : ‖c - t‖ + r ≤ ρ) :
    foldedCircle c ρ (ball (t : ℂ) r) = 0 := by
  rw [ball_eq]
  refine fc_dist_null c ρ t measurableSet_Iio fun θ hθ => ?_
  have := norm_circleMap_sub_ge c hρ θ t
  rw [mem_Iio] at hθ
  linarith

theorem fc_ball_pos' {t r ρ : ℝ} {c : ℂ} (h₁ : ρ - r < ‖c - t‖) (h₂ : ‖c - t‖ < r + ρ) :
    0 < foldedCircle c ρ (ball (t : ℂ) r) := by
  rw [ball_eq]
  refine fc_dist_pos c ρ t isOpen_Iio ((c - t).arg + Real.pi) ?_
  rw [norm_circleMap_near, mem_Iio, abs_lt]
  constructor <;> linarith

/-- The circle misses the disc `B(t, r)`. -/
def Miss (t r ρ d : ℝ) : Prop := r + ρ < d ∨ d + r < ρ

/-- The circle meets the disc `B(t, r)`. -/
def Hit (r ρ d : ℝ) : Prop := ρ - r < d ∧ d < r + ρ

variable {y : FieldSample} {k : ℕ} {s : ℝ}

theorem avgReg_gap_miss {t₁ r₁ t₂ r₂ : ℝ} (h₁ : Miss t₁ r₁ (radius k) |s - t₁|)
    (h₂ : Miss t₂ r₂ (radius k) |s - t₂|) :
    avgReg (restrictField (circOut t₁ r₁ t₂ r₂) y) k s = avgReg y k s := by
  classical
  have hρ := radius_pos k
  -- a margin `m > 0` such that all centres within `m` still miss both discs
  have hm : ∀ {t r : ℝ}, Miss t r (radius k) |s - t| → ∃ m > 0, ∀ c : ℂ, ‖c - s‖ < m →
      foldedCircle c (radius k) (ball (t : ℂ) r) = 0 := by
    intro t r h
    rcases h with h | h
    · refine ⟨|s - t| - r - radius k, by linarith, fun c hc => fc_ball_null hρ.le ?_⟩
      have := abs_sub_le_norm c s t; linarith
    · refine ⟨radius k - |s - t| - r, by linarith, fun c hc => fc_ball_null' hρ.le ?_⟩
      have := norm_sub_real_le c s t; linarith
  obtain ⟨m₁, hm₁, H₁⟩ := hm h₁
  obtain ⟨m₂, hm₂, H₂⟩ := hm h₂
  refine LocalRule.avgReg_congr_local k (ρ := min m₁ m₂) (lt_min hm₁ hm₂)
    (fun c _ hc => ?_) (GaussTK.ofReal_mem_Hbar s)
  rw [dist_eq_norm] at hc
  have hmem : foldedCircle c (radius k) ∈ circOut t₁ r₁ t₂ r₂ :=
    ⟨c, radius k, hρ, rfl, measure_union_null (H₁ c (hc.trans_le (min_le_left _ _)))
      (H₂ c (hc.trans_le (min_le_right _ _)))⟩
  simp only [restrictField, if_pos hmem]

theorem avgReg_gap_hit {t₁ r₁ t₂ r₂ : ℝ} (h : Hit r₁ (radius k) |s - t₁| ∨
    Hit r₂ (radius k) |s - t₂|) :
    avgReg (restrictField (circOut t₁ r₁ t₂ r₂) y) k s = 0 := by
  classical
  rw [← avgReg_zero k (s : ℂ)]
  have hm : ∀ {t r : ℝ}, Hit r (radius k) |s - t| → ∃ m > 0, ∀ c : ℂ, ‖c - s‖ < m →
      0 < foldedCircle c (radius k) (ball (t : ℂ) r) := by
    intro t r h
    refine ⟨min (|s - t| - (radius k - r)) (r + radius k - |s - t|),
      lt_min (by linarith [h.1]) (by linarith [h.2]), fun c hc => fc_ball_pos' ?_ ?_⟩
    · have := abs_sub_le_norm c s t
      have := min_le_left (|s - t| - (radius k - r)) (r + radius k - |s - t|); linarith
    · have := norm_sub_real_le c s t
      have := min_le_right (|s - t| - (radius k - r)) (r + radius k - |s - t|); linarith
  obtain ⟨m, hm0, H⟩ : ∃ m > 0, ∀ c : ℂ, ‖c - s‖ < m →
      0 < foldedCircle c (radius k) (ball (t₁ : ℂ) r₁ ∪ ball (t₂ : ℂ) r₂) := by
    rcases h with h | h
    · obtain ⟨m, hm0, H⟩ := hm h
      exact ⟨m, hm0, fun c hc => (H c hc).trans_le (measure_mono subset_union_left)⟩
    · obtain ⟨m, hm0, H⟩ := hm h
      exact ⟨m, hm0, fun c hc => (H c hc).trans_le (measure_mono subset_union_right)⟩
  refine LocalRule.avgReg_congr_local k (ρ := m) hm0 (fun c _ hc => ?_)
    (GaussTK.ofReal_mem_Hbar s)
  rw [dist_eq_norm] at hc
  have hnot : foldedCircle c (radius k) ∉ circOut t₁ r₁ t₂ r₂ := by
    rintro ⟨d, ρ', -, -, hμ⟩
    exact (H c hc).ne' hμ
  simp only [restrictField, Pi.zero_apply, if_neg hnot]

/-! ## The approximations of a cut field -/

/-- The approximation density. -/
def bDens (γ : ℝ) (x : FieldSample) (k : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg x k (t : ℂ)))

theorem measurable_bDens (γ : ℝ) (x : FieldSample) (k : ℕ) : Measurable (bDens γ x k) :=
  ENNReal.measurable_ofReal.comp (measurable_const.mul
    (((RegClosure.measurable_avgReg_slice x k).comp
      Complex.continuous_ofReal.measurable).const_mul _).exp)

theorem bdryApprox_eq_bDens (γ : ℝ) (x : FieldSample) (k : ℕ) :
    bdryApprox γ x k = volume.withDensity (bDens γ x k) := rfl

/-- If `y'` reads `y` on `A`, junk `0` on `B`, and `A ∪ B` is conull, its approximation is
`νₖ|_A + 2^{-kγ²/4} Leb|_B`. -/
theorem bdryApprox_eq_cut (γ : ℝ) {y y' : FieldSample} {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B) (hnull : volume (A ∪ B)ᶜ = 0)
    (hin : ∀ s ∈ A, avgReg y' k s = avgReg y k s) (hout : ∀ s ∈ B, avgReg y' k s = 0) :
    bdryApprox γ y' k = (bdryApprox γ y k).restrict A +
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 4)) • volume.restrict B := by
  have hae : bDens γ y' k =ᵐ[volume] A.indicator (bDens γ y k) +
      B.indicator (fun _ => ENNReal.ofReal (radius k ^ (γ ^ 2 / 4))) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with s hs
    simp only [mem_compl_iff, not_not] at hs
    simp only [Pi.add_apply]
    rcases hs with hs | hs
    · rw [indicator_of_mem hs, indicator_of_notMem (hAB.notMem_of_mem_left hs), add_zero]
      simp only [bDens, hin s hs]
    · rw [indicator_of_notMem (hAB.notMem_of_mem_right hs), indicator_of_mem hs, zero_add]
      simp only [bDens, hout s hs, mul_zero, Real.exp_zero, mul_one]
  rw [bdryApprox_eq_bDens, withDensity_congr_ae hae, withDensity_add_left
    ((measurable_bDens γ y k).indicator hA), withDensity_indicator hA, withDensity_indicator hB,
    withDensity_const, bdryApprox_eq_bDens, restrict_withDensity hA]

theorem tendsto_radius_rpow {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun k : ℕ => radius k ^ (γ ^ 2 / 4)) atTop (𝓝 0) := by
  have hr : Tendsto radius atTop (𝓝 0) := by
    unfold radius
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hp : 0 < γ ^ 2 / 4 := by positivity
  have := ((Real.continuousAt_rpow_const 0 (γ ^ 2 / 4) (Or.inr hp.le)).tendsto).comp hr
  rwa [Real.zero_rpow hp.ne'] at this

/-- **The cut limit.** -/
theorem isVagueLimitR_cut {γ : ℝ} (hγ : 0 < γ) {y y' : FieldSample} {ν : Measure ℝ}
    (hν : IsVagueLimitR (bdryApprox γ y) ν)
    (hfin : ∀ k, IsFiniteMeasureOnCompacts (bdryApprox γ y k))
    {A B : ℕ → Set ℝ} (hA : ∀ k, MeasurableSet (A k)) (hB : ∀ k, MeasurableSet (B k))
    (heq : ∀ k, bdryApprox γ y' k = (bdryApprox γ y k).restrict (A k) +
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 4)) • volume.restrict (B k))
    {F : Finset ℝ} (hF : ∀ p ∈ F, ν {p} = 0) {S : Set ℝ} (hSm : MeasurableSet S)
    (hfr : frontier S ⊆ ↑F)
    (hcut : ∀ δ > 0, ∀ᶠ k in atTop, ∀ t, (∀ p ∈ F, δ < |t - p|) → (t ∈ A k ↔ t ∈ S)) :
    IsVagueLimitR (bdryApprox γ y') (ν.restrict S) ∧
      ∀ k (N : ℕ), bdryApprox γ y' k (Icc (-(N : ℝ)) N) < ⊤ := by
  have := hν.1
  refine ⟨⟨inferInstance, fun f hf hfc => ?_⟩, fun k N => ?_⟩
  · have hint : ∀ k, Integrable f (bdryApprox γ y k) := fun k => by
      have := hfin k; exact hf.integrable_of_hasCompactSupport hfc
    have hvol : Integrable f volume := hf.integrable_of_hasCompactSupport hfc
    have e : ∀ k, ∫ t, f t ∂bdryApprox γ y' k = ∫ t in A k, f t ∂bdryApprox γ y k +
        (radius k ^ (γ ^ 2 / 4)) * ∫ t in B k, f t := by
      intro k
      rw [heq k, integral_add_measure (hint k).restrict
        (hvol.restrict.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
        ENNReal.toReal_ofReal (Real.rpow_nonneg (radius_pos k).le _), smul_eq_mul]
    simp_rw [e]
    rw [← add_zero (∫ t in S, f t ∂ν)]
    refine (tendsto_integral_cut hν hfin hF hSm hfr hA hcut hf hfc).add ?_
    refine squeeze_zero_norm (a := fun k => radius k ^ (γ ^ 2 / 4) * ∫ t, ‖f t‖) (fun k => ?_)
      (by simpa using (tendsto_radius_rpow hγ).mul_const (∫ t, ‖f t‖))
    rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (radius_pos k).le _)]
    exact mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans
      (setIntegral_le_integral hvol.norm (ae_of_all _ fun _ => norm_nonneg _)))
      (Real.rpow_nonneg (radius_pos k).le _)
  · have := hfin k
    rw [heq k, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.add_lt_top.2 ⟨(Measure.restrict_apply_le _ _).trans_lt
      (isCompact_Icc.measure_lt_top), ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((Measure.restrict_apply_le _ _).trans_lt (by simp))⟩

/-- From the cut limit: `BCert` and the identification of the boundary measure. -/
theorem bCert_and_eq_of_cut {γ : ℝ} {y' : FieldSample} {μ : Measure ℝ}
    (h : IsVagueLimitR (bdryApprox γ y') μ ∧
      ∀ k (N : ℕ), bdryApprox γ y' k (Icc (-(N : ℝ)) N) < ⊤) :
    E1.M4.BCert γ y' ∧ qBoundaryMeasure γ y' = μ :=
  ⟨E1.M4.bCert_of_isVagueLimitR h.2 h.1, qBoundaryMeasure_eq h.1⟩

end G3Fid
end Thm18Asm
end QuantumZipper
