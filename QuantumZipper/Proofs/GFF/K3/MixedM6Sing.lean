import QuantumZipper.Proofs.GFF.K3.MixedM6Pre

/-!
# M6, singular part: `⟪v_ρ, v_ν − v_{ν_s}⟫` as a kernel integral (GFF-K3 node M6)

Blueprint: `blueprint/GFF_K3_BLUEPRINT.md`, §3.M (M6); handoff `handoff/K3-MIXED.md`, route (ii).

For `0 < t < s < R`, `v_{fold_{y,t}} − v_{fold_{y,s}}` is the annulus feature `A_{y,t,s}`, whose
pairing with `v_ρ` is `∫ ã_{y,t,s} dρ` (M5). Integrating over `ν` (M5(b), weak Bochner form) and
letting `t → 0` (M4(ii) weak convergence on the left, dominated convergence with the admissible
logarithmic bound on the right) gives

  `⟪v_ρ, v_ν − v_{ν_s}⟫ = ∬ singKer s y x dρ(x) dν(y)`,
  `singKer s y x = log⁺(s/|x−y|) + log⁺(s/|x−ȳ|) = neumannH x y + log max(s,|x−y|) + log max(s,|x−ȳ|)`.

This is the classical fact that the logarithmic potential of `δ_y − (circle average)` is the
truncated logarithm (Adams–Hedberg, *Function Spaces and Potential Theory*, eq. (1.2.4) p. 8 and
the mean value property), carried out here in the dual-norm framework (own assembly).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

variable {D S K : Set ℂ} {R : ℝ}

/-- The truncated singular kernel `ã_{y,0,s}(x) = log⁺(s/|x−y|) + log⁺(s/|x−ȳ|)`. -/
def singKer (s : ℝ) (y x : ℂ) : ℝ :=
  neumannH x y + Real.log (max s ‖x - y‖) + Real.log (max s ‖x - conj y‖)

/-- Closed form of the annulus potential `ã_{y,t,s}(x)`. -/
def annPotT (s t : ℝ) (y x : ℂ) : ℝ :=
  (Real.log (max s ‖x - y‖) - Real.log (max t ‖x - y‖)) +
    (Real.log (max s ‖x - conj y‖) - Real.log (max t ‖x - conj y‖))

theorem annulusPot_eq_annPotT {s t : ℝ} (ht : 0 < t) (hts : t < s) (y x : ℂ) :
    annulusPot y t s x = annPotT s t y x := by
  rw [annulusPot, annProfile_eq ht hts (sq_nonneg _), annProfile_eq ht hts (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _), annPotT]

theorem continuous_log_max_K3 {c : ℝ} (hc : 0 < c) {g : ℂ × ℂ → ℂ} (hg : Continuous g) :
    Continuous fun p => Real.log (max c ‖g p‖) :=
  (continuous_const.max hg.norm).log fun _ => (lt_max_of_lt_left hc).ne'

theorem continuous_annPotT {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Continuous fun p : ℂ × ℂ => annPotT s t p.1 p.2 := by
  have h1 : Continuous fun p : ℂ × ℂ => p.2 - p.1 := continuous_snd.sub continuous_fst
  have h2 : Continuous fun p : ℂ × ℂ => p.2 - conj p.1 :=
    continuous_snd.sub (Complex.continuous_conj.comp continuous_fst)
  exact ((continuous_log_max_K3 hs h1).sub (continuous_log_max_K3 ht h1)).add
    ((continuous_log_max_K3 hs h2).sub (continuous_log_max_K3 ht h2))

/-- The continuous part `log max(s,|x−y|) + log max(s,|x−ȳ|)` of `singKer`. -/
theorem continuous_singKer_sub {s : ℝ} (hs : 0 < s) :
    Continuous fun p : ℂ × ℂ => Real.log (max s ‖p.2 - p.1‖) + Real.log (max s ‖p.2 - conj p.1‖) :=
  (continuous_log_max_K3 hs (continuous_snd.sub continuous_fst)).add
    (continuous_log_max_K3 hs (continuous_snd.sub (Complex.continuous_conj.comp continuous_fst)))

theorem abs_log_max_sub_le {s t r : ℝ} (ht : 0 < t) (hts : t ≤ s) (hr : 0 < r) :
    |Real.log (max s r) - Real.log (max t r)| ≤ |Real.log s| + |Real.log r| := by
  have h1 : Real.log (max t r) ≤ Real.log (max s r) :=
    Real.log_le_log (lt_max_of_lt_left ht) (max_le_max hts le_rfl)
  rw [abs_of_nonneg (sub_nonneg.2 h1)]
  have h2 : Real.log r ≤ Real.log (max t r) := Real.log_le_log hr (le_max_right _ _)
  have a1 := abs_nonneg (Real.log s)
  have a2 := neg_abs_le (Real.log r)
  have a3 := le_abs_self (Real.log s)
  have a4 := abs_nonneg (Real.log r)
  rcases le_total s r with hsr | hrs
  · rw [max_eq_right hsr]; linarith
  · rw [max_eq_left hrs]; linarith

theorem annPotT_eq_singKer {s t : ℝ} {y x : ℂ} (h1 : t < ‖x - y‖) (h2 : t < ‖x - conj y‖) :
    annPotT s t y x = singKer s y x := by
  rw [annPotT, singKer, neumannH, max_eq_right h1.le, max_eq_right h2.le]; ring

/-- A function continuous on `A × B` is integrable against a product of finite measures carried
by the compact sets `A`, `B`. -/
theorem integrable_prod_of_continuousOn_K3 {μ ν : Measure ℂ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B) (hμA : μ Aᶜ = 0)
    (hνB : ν Bᶜ = 0) {f : ℂ × ℂ → ℝ} (hf : ContinuousOn f (A ×ˢ B)) :
    Integrable f (μ.prod ν) := by
  have hnull : (μ.prod ν) (A ×ˢ B)ᶜ = 0 := by
    rw [compl_prod_eq_union]
    refine measure_union_null ?_ ?_
    · rw [Measure.prod_prod, hμA, zero_mul]
    · rw [Measure.prod_prod, hνB, mul_zero]
  have hae : ∀ᵐ p ∂(μ.prod ν), p ∈ A ×ˢ B := ae_iff.2 hnull
  have h := hf.integrableOn_compact (μ := μ.prod ν) (hA.prod hB)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h

theorem integrable_prod_of_continuous_adm {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hν : IsAdmissibleH ν) {f : ℂ × ℂ → ℝ} (hf : Continuous f) : Integrable f (μ.prod ν) := by
  obtain ⟨hμf, ⟨A, hA, -, hμA⟩, -⟩ := hμ
  obtain ⟨hνf, ⟨B, hB, -, hνB⟩, -⟩ := hν
  exact integrable_prod_of_continuousOn_K3 hA hB hμA hνB hf.continuousOn

/-- `|log|x−y|| + |log|x−ȳ||` is integrable against a product of admissible measures. -/
theorem integrable_absLog_prod {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν) :
    Integrable (fun p : ℂ × ℂ => |Real.log ‖p.2 - p.1‖| + |Real.log ‖p.2 - conj p.1‖|)
      (μ.prod ν) := by
  have hm1 : Measurable fun p : ℂ × ℂ => Real.log ‖p.2 - p.1‖ :=
    Real.measurable_log.comp (measurable_snd.sub measurable_fst).norm
  have hm2 : Measurable fun p : ℂ × ℂ => Real.log ‖p.2 - conj p.1‖ :=
    Real.measurable_log.comp
      (measurable_snd.sub (Complex.continuous_conj.measurable.comp measurable_fst)).norm
  refine admissible_integrable_of_bound (G := fun y x => |Real.log ‖x - y‖| +
    |Real.log ‖x - conj y‖|) hμ hν
    ((continuous_abs.measurable.comp hm1).add (continuous_abs.measurable.comp hm2)) ?_
  intro R' x y hx hy hxR hyR hxy
  have hab := le_log_norm_sub_conj_of_ne hy hx (Ne.symm hxy)
  have hb := log_norm_sub_conj_le_of_compact (K := closedBall 0 R') subset_rfl
    (mem_closedBall_zero_iff.2 hyR) (mem_closedBall_zero_iff.2 hxR)
  have m1 := le_max_left 0 (-Real.log ‖x - y‖)
  have m2 := le_max_right 0 (-Real.log ‖x - y‖)
  rw [norm_sub_rev x y] at m1 m2
  have hL : 0 ≤ Real.log (max (2 * R') 1) := Real.log_nonneg (le_max_right _ _)
  have e1 : |Real.log ‖y - x‖| ≤ Real.log (max (2 * R') 1) + max 0 (-Real.log ‖y - x‖) :=
    abs_le.2 ⟨by linarith, by linarith⟩
  have e2 : |Real.log ‖y - conj x‖| ≤ Real.log (max (2 * R') 1) + max 0 (-Real.log ‖y - x‖) :=
    abs_le.2 ⟨by linarith, by linarith⟩
  rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)), norm_sub_rev x y]
  linarith

/-- **M6, singular part.** For `ρ` admissible (and `D`-admissible), `ν` admissible and carried by
`K`, and `0 < s < R`: `⟪v_ρ, v_ν − v_{ν_s}⟫ = ∬ singKer s y x dρ(x) dν(y)`. -/
theorem inner_rieszVec_sub_bind_eq_integral_singKer (h : MixedLocalHyp D S K R)
    (hpos : ∃ g ∈ mixedSpace D S, 0 < dirichletEnergyOn D g) {ρ ν : Measure ℂ}
    (hρ : IsAdmissibleH ρ) (hρD : IsAdmissibleDual D (mixedSpace D S) ρ)
    (hν : IsAdmissibleH ν) (hνK : ν Kᶜ = 0) {s : ℝ} (hs : 0 < s) (hsR : s < R) :
    ⟪rieszVec D (mixedSpace D S) ρ, rieszVec D (mixedSpace D S) ν -
        rieszVec D (mixedSpace D S) (ν.bind fun w => foldedCircle w s)⟫ =
      ∫ p, singKer s p.1 p.2 ∂(ν.prod ρ) := by
  set V := mixedSpace D S with hV
  have hνf := hν.1
  have hρf := hρ.1
  set u := rieszVec D V ρ with hu_def
  have hu : u ∈ gradClosure D V := rieszVec_mem
  have hKae : ∀ᵐ y ∂ν, y ∈ K := ae_iff.2 hνK
  -- (1) the pre-limit identity
  have hpre : ∀ t, 0 < t → t < s →
      ⟪u, rieszVec D V (ν.bind fun w => foldedCircle w t)⟫ -
        ⟪u, rieszVec D V (ν.bind fun w => foldedCircle w s)⟫ =
        ∫ p, annPotT s t p.1 p.2 ∂(ν.prod ρ) := by
    intro t ht hts
    have htR : t < R := hts.trans hsR
    obtain ⟨m1, e1⟩ := inner_rieszVec_bind_eq_integral h hpos hν hνK ht htR hu
    obtain ⟨m2, e2⟩ := inner_rieszVec_bind_eq_integral h hpos hν hνK hs hsR hu
    obtain ⟨B1, hB1⟩ := exists_norm_rieszVec_foldedCircle_le h.isOpen h.subset_H h.bounded
      h.free_real h.pos h.local_ ht htR
    obtain ⟨B2, hB2⟩ := exists_norm_rieszVec_foldedCircle_le h.isOpen h.subset_H h.bounded
      h.free_real h.pos h.local_ hs hsR
    have i1 : Integrable (fun y => ⟪rieszVec D V (foldedCircle y t), u⟫) ν :=
      Integrable.of_bound m1 (B1 * ‖u‖) (hKae.mono fun y hy => by
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hB1 y hy) (norm_nonneg _)))
    have i2 : Integrable (fun y => ⟪rieszVec D V (foldedCircle y s), u⟫) ν :=
      Integrable.of_bound m2 (B2 * ‖u‖) (hKae.mono fun y hy => by
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hB2 y hy) (norm_nonneg _)))
    rw [← real_inner_comm u (rieszVec D V (ν.bind fun w => foldedCircle w t)),
      ← real_inner_comm u (rieszVec D V (ν.bind fun w => foldedCircle w s)), e1, e2,
      ← integral_sub i1 i2,
      integral_prod _ (integrable_prod_of_continuous_adm hν hρ (continuous_annPotT hs ht))]
    refine integral_congr_ae (hKae.mono fun y hy => ?_)
    have hloc := h.local_ y hy
    have hloc' : LocalBall D S y s := hloc.mono hloc.1 hs (by rw [dist_self, add_zero]; linarith)
    simp only
    rw [← inner_sub_left, rieszVec_annulus' h.isOpen h.subset_H h.bounded h.free_real hloc ht hts
      (by linarith), real_inner_comm, inner_rieszVec_annulusFeat h.bounded hpos hρD hloc' ht hts]
    exact integral_congr_ae (ae_of_all _ fun x => annulusPot_eq_annPotT ht hts y x)
  -- (2) the limit of the left side
  have hL : Tendsto (fun t => ⟪u, rieszVec D V (ν.bind fun w => foldedCircle w t)⟫ -
      ⟪u, rieszVec D V (ν.bind fun w => foldedCircle w s)⟫) (𝓝[>] 0)
      (𝓝 (⟪u, rieszVec D V ν⟫ - ⟪u, rieszVec D V (ν.bind fun w => foldedCircle w s)⟫)) := by
    refine Tendsto.sub_const ?_ _
    simpa only [real_inner_comm u] using tendsto_inner_rieszVec_bind h hpos hν hνK hu
  -- (3) dominated convergence on the right side
  have hgood : ∀ᵐ p ∂(ν.prod ρ), p.2 ≠ p.1 ∧ p.2 ≠ conj p.1 := by
    have hmeas : MeasurableSet {p : ℂ × ℂ | p.2 ≠ p.1 ∧ p.2 ≠ conj p.1} :=
      ((measurableSet_eq_fun measurable_snd measurable_fst).compl).inter
        ((measurableSet_eq_fun measurable_snd
          (Complex.continuous_conj.measurable.comp measurable_fst)).compl)
    refine (Measure.ae_prod_mem_iff_ae_ae_mem hmeas).2 (ae_of_all _ fun y => ?_)
    have n1 : ∀ᵐ x ∂ρ, x ≠ y := by
      rw [ae_iff]; simpa using noAtoms_of_isAdmissibleH hρ y
    have n2 : ∀ᵐ x ∂ρ, x ≠ conj y := by
      rw [ae_iff]; simpa using noAtoms_of_isAdmissibleH hρ (conj y)
    filter_upwards [n1, n2] with x h1 h2
    exact ⟨h1, h2⟩
  have hR : Tendsto (fun t => ∫ p, annPotT s t p.1 p.2 ∂(ν.prod ρ)) (𝓝[>] 0)
      (𝓝 (∫ p, singKer s p.1 p.2 ∂(ν.prod ρ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun p => 2 * |Real.log s| + (|Real.log ‖p.2 - p.1‖| + |Real.log ‖p.2 - conj p.1‖|))
      ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact (continuous_annPotT hs ht).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT hs] with t ht
      filter_upwards [hgood] with p hp
      have r1 : 0 < ‖p.2 - p.1‖ := norm_pos_iff.2 (sub_ne_zero.2 hp.1)
      have r2 : 0 < ‖p.2 - conj p.1‖ := norm_pos_iff.2 (sub_ne_zero.2 hp.2)
      rw [Real.norm_eq_abs, annPotT]
      have b1 := abs_log_max_sub_le ht.1 ht.2.le r1
      have b2 := abs_log_max_sub_le ht.1 ht.2.le r2
      exact (abs_add_le _ _).trans (by linarith)
    · exact (integrable_const _).add (integrable_absLog_prod hν hρ)
    · filter_upwards [hgood] with p hp
      have r1 : 0 < ‖p.2 - p.1‖ := norm_pos_iff.2 (sub_ne_zero.2 hp.1)
      have r2 : 0 < ‖p.2 - conj p.1‖ := norm_pos_iff.2 (sub_ne_zero.2 hp.2)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (lt_min r1 r2)] with t ht
      exact (annPotT_eq_singKer (lt_of_lt_of_le ht.2 (min_le_left _ _))
        (lt_of_lt_of_le ht.2 (min_le_right _ _))).symm
  -- (4) conclusion
  have hev : (fun t => ⟪u, rieszVec D V (ν.bind fun w => foldedCircle w t)⟫ -
      ⟪u, rieszVec D V (ν.bind fun w => foldedCircle w s)⟫) =ᶠ[𝓝[>] 0]
      fun t => ∫ p, annPotT s t p.1 p.2 ∂(ν.prod ρ) := by
    filter_upwards [Ioo_mem_nhdsGT hs] with t ht
    exact hpre t ht.1 ht.2
  rw [inner_sub_right]
  exact tendsto_nhds_unique (hL.congr' hev) hR

end QuantumZipper.K3
