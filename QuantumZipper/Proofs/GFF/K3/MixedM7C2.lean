import QuantumZipper.Proofs.GFF.K3.MixedM7C1

/-!
# K3-mixed M7-a3, step 2: on the half-disc itself the local Gram matrix is the covariance

For the half-disc `U = ball t r ∩ H` with free diameter (`V₀ = mixedSpace U (realSet (Icc (t - r)
(t + r)))`), every element of `V₀` vanishes on the closed semicircle `sphere t r ∩ Hbar` (on the
open semicircle by definition, at the endpoints `t ± r` by continuity), so the balayage `bal μ`
has Riesz vector `0` and the local generator is `v_μ` itself. Hence M7-a3 for `U` is the explicit
covariance statement `HalfDiscMixedCovStmt`:

  `dualCov U V₀ μ ν = kernelCov (halfDiscGreen t r) μ ν` for local `μ, ν`,

i.e. the covariance of the mixed GFF of the half-disc (Neumann on the diameter, Dirichlet on the
arc) is the half-disc Green kernel (Sheffield 2007, §2.2, for the Dirichlet case; the Neumann
diameter is the reflection principle).

Main result: `mixedLocalGram_of_localMem_halfDiscCov`: M7-a3 for `(D, c, d)` from M7-a2 for
`(D, c, d)` and for `U`, and `HalfDiscMixedCovStmt`. Own elementary arguments.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace Real

namespace QuantumZipper.K3

/-- **The explicit half-disc covariance (remaining node of M7-a3).** For measures carried by
`closedBall t r'`, the covariance of the mixed space of the half-disc `ball t r ∩ H` (free on the
closed diameter) is the half-disc Green kernel. -/
def HalfDiscMixedCovStmt (t r r' : ℝ) : Prop :=
  0 < r' → r' < r → ∀ μ ν : Measure ℂ, IsAdmissibleH μ → μ (closedBall (t : ℂ) r')ᶜ = 0 →
    IsAdmissibleH ν → ν (closedBall (t : ℂ) r')ᶜ = 0 →
      dualCov (ball (t : ℂ) r ∩ H) (mixedSpace (ball (t : ℂ) r ∩ H)
        (realSet (Icc (t - r) (t + r)))) μ ν = kernelCov (halfDiscGreen t r) μ ν

/-- The closed semicircle lies in the closure of the open one. -/
theorem sphere_inter_Hbar_subset_closure_m7c {t r : ℝ} (hr : 0 < r) :
    sphere (t : ℂ) r ∩ Hbar ⊆ closure (sphere (t : ℂ) r ∩ H) := by
  have hsub : circleMap (t : ℂ) r '' Ioo 0 π ⊆ sphere (t : ℂ) r ∩ H := by
    rintro _ ⟨θ, hθ, rfl⟩
    refine ⟨circleMap_mem_sphere _ hr.le θ, ?_⟩
    show 0 < (circleMap (t : ℂ) r θ).im
    simp only [circleMap, Complex.add_im, Complex.ofReal_im, zero_add]
    rw [show ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im = r * Real.sin θ by
      rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]]
    exact mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  have hcl : circleMap (t : ℂ) r '' Icc 0 π ⊆ closure (sphere (t : ℂ) r ∩ H) := by
    rw [← closure_Ioo Real.pi_pos.ne]
    exact (image_closure_subset_closure_image (continuous_circleMap _ _)).trans
      (closure_mono hsub)
  rintro z ⟨hz, hzH⟩
  rcases lt_or_eq_of_le (show 0 ≤ z.im from hzH) with h | h
  · exact subset_closure ⟨hz, h⟩
  · have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← h])
    rw [mem_sphere, hzr, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at hz
    rcases (abs_eq hr.le).1 hz with h1 | h1
    · refine hcl ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, ?_⟩
      rw [hzr]
      simp only [circleMap, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
      apply Complex.ext <;> simp; linarith
    · refine hcl ⟨π, ⟨Real.pi_pos.le, le_rfl⟩, ?_⟩
      rw [hzr]
      simp only [circleMap, Complex.exp_pi_mul_I, mul_neg, mul_one]
      apply Complex.ext <;> simp; linarith

/-- Elements of the half-disc mixed space vanish on the closed semicircle. -/
theorem eq_zero_of_mem_sphere_halfDisc_m7c {t r : ℝ} (hr : 0 < r) {f : ℂ → ℝ}
    (hf : f ∈ mixedSpace (ball (t : ℂ) r ∩ H) (realSet (Icc (t - r) (t + r)))) {z : ℂ}
    (hz : z ∈ sphere (t : ℂ) r ∩ Hbar) : f z = 0 := by
  obtain ⟨hfs, -, N, -, hNf, hf0⟩ := hf
  have hopen : IsOpen (ball (t : ℂ) r ∩ H) := isOpen_ball.inter isOpen_H
  have hN : sphere (t : ℂ) r ∩ H ⊆ {z | f z = 0} := by
    rintro w ⟨hw, hwH⟩
    refine hf0 w (hNf ⟨?_, ?_⟩)
    · rw [hopen.frontier_eq]
      refine ⟨closedBall_inter_Hbar_subset_closure_m7a hr
        ⟨sphere_subset_closedBall hw, le_of_lt (show 0 < w.im from hwH)⟩, fun h => ?_⟩
      have := h.1
      rw [mem_ball, ← mem_sphere.1 hw] at this
      exact lt_irrefl _ this
    · rintro ⟨s, -, rfl⟩
      simp [H] at hwH
  exact closure_minimal hN (isClosed_eq hfs.continuous continuous_const)
    (sphere_inter_Hbar_subset_closure_m7c hr hz)

/-- On the half-disc, the Riesz vector of a balayage is `0`. -/
theorem rieszVec_bal_halfDisc_eq_zero_m7c {t r r' : ℝ} (hr' : 0 < r') (hr'r : r' < r)
    {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (hμK : μ (closedBall (t : ℂ) r')ᶜ = 0) :
    rieszVec (ball (t : ℂ) r ∩ H) (mixedSpace (ball (t : ℂ) r ∩ H)
      (realSet (Icc (t - r) (t + r)))) (bal t r μ) = 0 := by
  have hr : 0 < r := hr'.trans hr'r
  set U := ball (t : ℂ) r ∩ H
  set V₀ := mixedSpace U (realSet (Icc (t - r) (t + r)))
  have hDN : IsDNSpace U V₀ := isDNSpace_mixedSpace U _
  have hg₀ := prop16Geometry_halfDisc_m7c (t := t) hr
  have ht₀ : t ∈ Ioo (t - r) (t + r) := ⟨by linarith, by linarith⟩
  by_cases hpos : ∃ g ∈ V₀, 0 < dirichletEnergyOn U g
  swap
  · exact eq_zero_of_mem_gradClosure_of_nopos hDN hpos rieszVec_mem
  obtain ⟨C, hC⟩ := mixedPoissonBound_holds U (t - r) (t + r) t r r' hg₀ ht₀ hr' hr'r subset_rfl
  have hbA := isAdmissibleDual_bal_of_bound_m7a hDN hr hr'r subset_rfl hC hμ hμK
  have hae : ∀ᵐ x ∂bal t r μ, x ∈ sphere (t : ℂ) r ∩ Hbar :=
    mem_ae_iff.2 (bal_null_of_forall
      (isClosed_sphere.measurableSet.inter isClosed_Hbar.measurableSet).compl
      fun z => halfDiscPoisson_compl_eq_zero hr z)
  have hperp : ∀ f : V₀, ⟪rieszVec U V₀ (bal t r μ), gradFeat U f.1⟫ = 0 := by
    intro f
    rw [pair_rieszVec hDN hbA hpos f.1 f.2]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with x hx
    exact eq_zero_of_mem_sphere_halfDisc_m7c hr f.2 hx
  have hmem : rieszVec U V₀ (bal t r μ) ∈
      (Submodule.span ℝ (Set.range fun f : V₀ => gradFeat U f.1)).topologicalClosure := by
    have h := rieszVec_mem (D := U) (V := V₀) (μ := bal t r μ)
    unfold gradClosure at h
    rwa [Set.image_eq_range] at h
  exact inner_self_eq_zero.1 (inner_eq_zero_of_mem_closure_span_of_forall hperp hmem)

/-- **M7-a3 on the half-disc from the explicit covariance.** -/
theorem mixedLocalGram_halfDisc_of_cov {t r r' : ℝ} (h : HalfDiscMixedCovStmt t r r') :
    MixedLocalGramStmt (ball (t : ℂ) r ∩ H) (t - r) (t + r) t r r' := by
  intro hg₀ _ht hr' hr'r _hsub μ ν hμ hμK hν hνK
  have hDN := isDNSpace_mixedSpace (ball (t : ℂ) r ∩ H) (realSet (Icc (t - r) (t + r)))
  rw [mixedLocVec, mixedLocVec, rieszVec_bal_halfDisc_eq_zero_m7c hr' hr'r hμ hμK,
    rieszVec_bal_halfDisc_eq_zero_m7c hr' hr'r hν hνK, sub_zero, sub_zero,
    ← dualCov_eq_inner_rieszVec hDN (isAdmissibleDual_mixed_halfDisc_local hg₀ hr'r subset_rfl hμ hμK)
      (isAdmissibleDual_mixed_halfDisc_local hg₀ hr'r subset_rfl hν hνK)]
  exact h hr' hr'r μ ν hμ hμK hν hνK

/-- **M7-a3 from M7-a2 (for `D` and for the half-disc) and the explicit half-disc covariance.** -/
theorem mixedLocalGram_of_localMem_halfDiscCov {D : Set ℂ} {c d t r r' : ℝ}
    (h2 : MixedLocalMemStmt D c d t r r')
    (h2₀ : MixedLocalMemStmt (ball (t : ℂ) r ∩ H) (t - r) (t + r) t r r')
    (hcov : HalfDiscMixedCovStmt t r r') :
    MixedLocalGramStmt D c d t r r' :=
  mixedLocalGram_of_localMem_halfDisc h2 h2₀ (mixedLocalGram_halfDisc_of_cov hcov)

/-- **M7-a from M7-a2′ (for `D` and for the half-disc) and the explicit half-disc covariance.** -/
theorem mixedHalfDiscMarkovCov_of_pairing_halfDiscCov {D : Set ℂ} {c d t r r' : ℝ}
    (h2 : MixedHarmonicPairingStmt D c d t r r')
    (h2₀ : MixedHarmonicPairingStmt (ball (t : ℂ) r ∩ H) (t - r) (t + r) t r r')
    (hcov : HalfDiscMixedCovStmt t r r') :
    MixedHalfDiscMarkovCovStmt D c d t r r' :=
  mixedHalfDiscMarkovCov_of_pairing_gram h2
    (mixedLocalGram_of_localMem_halfDiscCov (mixedLocalMem_of_harmonicPairing h2)
      (mixedLocalMem_of_harmonicPairing h2₀) hcov)

end QuantumZipper.K3
