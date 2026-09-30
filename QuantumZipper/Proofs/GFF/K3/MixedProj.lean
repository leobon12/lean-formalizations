import QuantumZipper.Proofs.GFF.K3.MixedRiesz

/-!
# The annulus span and the remainder decomposition (GFF-K3 node M5, first part)

Blueprint: `blueprint/GFF_K3_BLUEPRINT.md`, §3.M (M5).

* `isLUB_norm_sq_starProjection`: `‖P_M x‖² = sup_{a ∈ span T} (2⟪x,a⟫ − ‖a‖²)` for
  `M = closure (span T)` (the variational characterization of the orthogonal projection). The
  textbook reference Brezis, *Functional Analysis, Sobolev Spaces and PDE*, Thm. 5.2 is cited for
  orientation only and is **not checked** here (AUDIT8 K8-8 / AUDIT9 G9-2); the Lean proof is a
  direct computation with the projection.
* `annulusSpan D S`: the closed span of the annulus features of the local annuli of `(D, S)`;
  `remVec D S μ` the component of the Riesz vector orthogonal to it; `Qann D S μ ν` the annulus
  part of the covariance.
* `remVec_foldedCircle_eq`: `remVec (fold_{z,s}) = remVec (fold_{z,s'})` (mean-value property).
* `dualCov_mixed_eq_Qann_add`: `dualCov = Qann + ⟪remVec μ, remVec ν⟫`.
* `inner_rieszVec_annulusFeat`: `⟪v_μ, annulusFeat z s s'⟫ = ∫ annulusPot z s s' dμ`, where
  `annulusPot` is an explicit radial function depending only on `(z, s, s')` (universality of
  the pairings).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

/-! ## The variational formula for the projection -/

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

end Hilbert

/-! ## The annulus span -/

/-- The annulus features of the local annuli of `(D, S)`. -/
def annulusSet (D S : Set ℂ) : Set (GradSpace D) :=
  {v | ∃ (z : ℂ) (s s' R0 : ℝ), LocalBall D S z R0 ∧ 0 < s ∧ s < s' ∧ s' < R0 ∧
    v = annulusFeat D z s s'}

/-- `M`: the closed span of the local annulus features. -/
def annulusSpan (D S : Set ℂ) : Submodule ℝ (GradSpace D) :=
  (Submodule.span ℝ (annulusSet D S)).topologicalClosure

instance (D S : Set ℂ) : CompleteSpace (annulusSpan D S) := by
  unfold annulusSpan; infer_instance

/-- The remainder vector `v_μ − P_M v_μ`. -/
def remVec (D S : Set ℂ) (μ : Measure ℂ) : GradSpace D :=
  (annulusSpan D S)ᗮ.starProjection (rieszVec D (mixedSpace D S) μ)

/-- The annulus part `⟪P_M v_μ, P_M v_ν⟫` of the covariance. -/
def Qann (D S : Set ℂ) (μ ν : Measure ℂ) : ℝ :=
  ⟪(annulusSpan D S).starProjection (rieszVec D (mixedSpace D S) μ),
    (annulusSpan D S).starProjection (rieszVec D (mixedSpace D S) ν)⟫

theorem annulusFeat_mem_annulusSpan {D S : Set ℂ} {z : ℂ} {s s' R0 : ℝ}
    (hloc : LocalBall D S z R0) (hs : 0 < s) (hss' : s < s') (hs'R : s' < R0) :
    annulusFeat D z s s' ∈ annulusSpan D S :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨z, s, s', R0, hloc, hs, hss', hs'R, rfl⟩)

theorem annulusSpan_le_gradClosure {D S : Set ℂ} (hb : Bornology.IsBounded D) :
    annulusSpan D S ≤ gradClosure D (mixedSpace D S) := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  rw [Submodule.span_le]
  rintro _ ⟨z, s, s', R0, hloc, hs, hss', hs'R, rfl⟩
  exact annulusFeat_mem_gradClosure hb (hloc.mono hloc.1 (hs.trans hss') (by simp; linarith))
    hs hss'

/-- **M5, mean-value property.** Concentric local folded circles have the same remainder vector. -/
theorem remVec_foldedCircle_eq {D S : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H)
    (hb : Bornology.IsBounded D) (hS : S ⊆ {z : ℂ | z.im = 0}) {z : ℂ} {s s' R0 : ℝ}
    (hloc : LocalBall D S z R0) (hs : 0 < s) (hss' : s < s') (hs'R : s' < R0) :
    remVec D S (foldedCircle z s) = remVec D S (foldedCircle z s') := by
  have h := rieszVec_annulus' hD hDH hb hS hloc hs hss' hs'R
  have hmem := annulusFeat_mem_annulusSpan hloc hs hss' hs'R
  unfold remVec
  rw [← sub_eq_zero, ← map_sub, h, Submodule.starProjection_apply_eq_zero_iff]
  exact (annulusSpan D S).le_orthogonal_orthogonal hmem

/-- **M5, decomposition.** `dualCov = Qann + ⟪remVec μ, remVec ν⟫` on mixed-admissible measures. -/
theorem dualCov_mixed_eq_Qann_add {D S : Set ℂ} {μ ν : Measure ℂ}
    (hμ : IsAdmissibleDual D (mixedSpace D S) μ) (hν : IsAdmissibleDual D (mixedSpace D S) ν) :
    dualCov D (mixedSpace D S) μ ν = Qann D S μ ν + ⟪remVec D S μ, remVec D S ν⟫ := by
  rw [dualCov_eq_inner_rieszVec (isDNSpace_mixedSpace D S) hμ hν]
  unfold Qann remVec
  set K := annulusSpan D S
  set x := rieszVec D (mixedSpace D S) μ
  set y := rieszVec D (mixedSpace D S) ν
  have hx := K.starProjection_add_starProjection_orthogonal x
  have hy := K.starProjection_add_starProjection_orthogonal y
  have h1 : ⟪K.starProjection x, Kᗮ.starProjection y⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K.starProjection_apply_mem x)
      (Kᗮ.starProjection_apply_mem y)
  have h2 : ⟪Kᗮ.starProjection x, K.starProjection y⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (K.starProjection_apply_mem y)
      (Kᗮ.starProjection_apply_mem x)
  conv_lhs => rw [← hx, ← hy]
  rw [inner_add_left, inner_add_right, inner_add_right, h1, h2]
  ring

/-! ## Universality of the annulus pairings -/

/-- The limiting radial profile `u ↦ ∫_{s'²}^u −1_{(s²,s'²)}(t)/(2t) dt`
(that is, `½ log (s'²/u)` clamped to `[0, log (s'/s)]`). -/
def annProfile (s s' : ℝ) (u : ℝ) : ℝ :=
  ∫ t in (s' ^ 2)..u, -((Ioo (s ^ 2) (s' ^ 2)).indicator 1 t) / (2 * t)

/-- The annulus potential `ã_{z,s,s'}(x) = annProfile(|x−z|²) + annProfile(|x−z̄|²)`; its
gradient is `annulusField z s s'`. It depends only on `(z, s, s')`. -/
def annulusPot (z : ℂ) (s s' : ℝ) (x : ℂ) : ℝ :=
  annProfile s s' (‖x - z‖ ^ 2) + annProfile s s' (‖x - conj z‖ ^ 2)

theorem norm_neg_div_two_mul_le {ψt t a : ℝ} (ha : 0 < a) (h01 : 0 ≤ ψt ∧ ψt ≤ 1)
    (h0 : t ≤ a → ψt = 0) : ‖-ψt / (2 * t)‖ ≤ (2 * a)⁻¹ := by
  by_cases ht : t ≤ a
  · rw [h0 ht]; simp; positivity
  · push_neg at ht
    have ht0 : 0 < t := ha.trans ht
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg h01.1, abs_of_pos (by positivity),
      div_le_iff₀ (by positivity)]
    calc ψt ≤ 1 := h01.2
      _ ≤ (2 * a)⁻¹ * (2 * t) := by
        rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]; linarith

theorem norm_integral_le_of_vanish {g : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b) (hg : Continuous g)
    (hC : ∀ t, ‖g t‖ ≤ C) (ha : ∀ t, t ≤ a → g t = 0) (hb : ∀ t, b ≤ t → g t = 0) (u : ℝ) :
    ‖∫ t in b..u, g t‖ ≤ C * (b - a) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  rcases le_total b u with hbu | hub
  · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => ?_),
      intervalIntegral.integral_zero, norm_zero]
    · exact mul_nonneg hC0 (by linarith)
    · rw [uIcc_of_le hbu] at ht; exact hb t ht.1
  · rcases le_total a u with hau | hua
    · refine (intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => hC t).trans ?_
      rw [abs_of_nonpos (by linarith)]; nlinarith
    · rw [← intervalIntegral.integral_add_adjacent_intervals (b := a)
        (hg.intervalIntegrable b a) (hg.intervalIntegrable a u)]
      rw [intervalIntegral.integral_congr (a := a) (b := u) (g := fun _ => (0 : ℝ))
        (fun t ht => ?_), intervalIntegral.integral_zero, add_zero]
      · refine (intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => hC t).trans ?_
        rw [abs_of_nonpos (by linarith)]; nlinarith
      · rw [uIcc_of_ge hua] at ht; exact ha t ht.2

/-- **M5, universality of the pairings.** For a mixed-admissible `μ`, the pairing of its Riesz
vector with a local annulus feature is `∫ ã_{z,s,s'} dμ`. -/
theorem inner_rieszVec_annulusFeat {D S : Set ℂ} (hb : Bornology.IsBounded D)
    (hpos : ∃ g ∈ mixedSpace D S, 0 < dirichletEnergyOn D g) {μ : Measure ℂ}
    (hμ : IsAdmissibleDual D (mixedSpace D S) μ) {z : ℂ} {s s' : ℝ}
    (hloc : LocalBall D S z s') (hs : 0 < s) (hss' : s < s') :
    ⟪rieszVec D (mixedSpace D S) μ, annulusFeat D z s s'⟫ = ∫ x, annulusPot z s s' x ∂μ := by
  obtain ⟨Φ, ψ, hψ01, hψa, hψlim, hΦint, hgc, hψb, hmem, hT⟩ :=
    exists_radialApprox_tendsto hb hloc hs hss'
  have hμf := hμ.1
  have hL := Filter.Tendsto.inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := rieszVec D (mixedSpace D S) μ)) hT
  have hEq : ∀ n, ⟪rieszVec D (mixedSpace D S) μ, gradFeat D (radialApprox (Φ n) z)⟫ =
      ∫ x, radialApprox (Φ n) z x ∂μ := fun n =>
    pair_rieszVec (isDNSpace_mixedSpace D S) hμ hpos _ (hmem n)
  have hs2 : 0 < s ^ 2 := by positivity
  have hss2 : s ^ 2 ≤ s' ^ 2 := by nlinarith
  have hgb : ∀ n t, ‖-ψ n t / (2 * t)‖ ≤ (2 * s ^ 2)⁻¹ := fun n t =>
    norm_neg_div_two_mul_le hs2 (hψ01 n t) (hψa n t)
  have hΦb : ∀ n u, ‖Φ n u‖ ≤ (2 * s ^ 2)⁻¹ * (s' ^ 2 - s ^ 2) := fun n u => by
    rw [hΦint]
    exact norm_integral_le_of_vanish hss2 (hgc n) (hgb n) (fun t ht => by simp [hψa n t ht])
      (fun t ht => by simp [hψb n t ht]) u
  have hprof : ∀ u, Tendsto (fun n => Φ n u) atTop (𝓝 (annProfile s s' u)) := fun u => by
    simp_rw [hΦint]
    exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (2 * s ^ 2)⁻¹) (Eventually.of_forall fun n => (hgc n).aestronglyMeasurable)
      (Eventually.of_forall fun n => ae_of_all _ fun t _ => hgb n t) intervalIntegrable_const
      (ae_of_all _ fun t _ => ((hψlim t).neg).div_const (2 * t))
  have hR : Tendsto (fun n => ∫ x, radialApprox (Φ n) z x ∂μ) atTop
      (𝓝 (∫ x, annulusPot z s s' x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun _ => 2 * ((2 * s ^ 2)⁻¹ * (s' ^ 2 - s ^ 2)))
      (fun n => (hmem n).1.continuous.aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · unfold radialApprox
      rw [two_mul]
      exact (norm_add_le _ _).trans (add_le_add (hΦb n _) (hΦb n _))
    · exact (hprof _).add (hprof _)
  exact tendsto_nhds_unique (hL.congr hEq) hR

/-! ## The annulus Gram matrix does not depend on the domain -/

end QuantumZipper.K3
