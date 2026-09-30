import QuantumZipper.Proofs.GFF.K3.MixedM6Sing

/-!
# M6, assembly: the mixed covariance is `neumannH + k` near the free arc (GFF-K3 node M6)

Blueprint: `blueprint/GFF_K3_BLUEPRINT.md`, §3.M (M6); handoff `handoff/K3-MIXED.md`, route (ii)
(the `D`-only route). With `v_ρ := rieszVec D (mixedSpace D S) ρ`, `μ_s := μ.bind fold_{·,s}`:

  `⟪v_μ, v_ν⟫ = ⟪v_μ, v_ν − v_{ν_s}⟫ + ∫ ⟪v_{fold_{y,s}}, v_μ⟫ dν(y)`,
  `⟪v_{fold_{y,s}}, v_μ⟫ = ⟪v_{fold_{y,s}}, v_μ − v_{μ_s}⟫ + ∫ ⟪v_{fold_{y,s}}, v_{fold_{x,s}}⟫ dμ(x)`,

and both `⟪·, v − v_s⟫` terms are `singKer` integrals (`MixedM6Sing`). Hence
`dualCov μ ν = ∬ (neumannH x y + mixedK x y) dν dμ` with

  `mixedK x y = log max(s,|x−y|) + log max(s,|x−ȳ|) + ∫ singKer s x · dfold_{y,s}
               + ⟪v_{fold_{y,s}}, v_{fold_{x,s}}⟫`,

continuous on `K × K` as soon as `z ↦ v_{fold_{z,s}}` is norm continuous on `K`
(the integral term is explicit by the mean value formula `integral_neumannH_foldedCircle`).
Own assembly of the M5 ingredients (the blueprint's route is the free-field comparison).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

variable {D S K : Set ℂ} {R : ℝ}

/-! ## Integrability and continuity helpers -/

theorem integrable_log_norm_sub_K3 {ν : Measure ℂ} (hν : IsAdmissibleH ν) (x : ℂ) :
    Integrable (fun y => Real.log ‖y - x‖) ν := by
  obtain ⟨hνf, ⟨K, hK, -, hKc⟩, C, hC, hbd⟩ := hν
  have := hνf
  obtain ⟨ρ, hρ⟩ := hK.isBounded.exists_norm_le
  set D := max 1 (ρ + ‖x‖) with hD
  have hmeas : Measurable fun y : ℂ => Real.log ‖y - x‖ :=
    Real.measurable_log.comp (measurable_id.sub_const x).norm
  have hneg : Integrable (fun y => (ENNReal.ofReal (-Real.log ‖y - x‖)).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top
      (ENNReal.measurable_ofReal.comp hmeas.neg).aemeasurable ((hbd x).trans_lt hC).ne
  refine ((integrable_const (Real.log D)).add hneg).mono' hmeas.aestronglyMeasurable ?_
  have hKae : ∀ᵐ y ∂ν, y ∈ K := ae_iff.2 hKc
  filter_upwards [hKae] with y hy
  simp only [Pi.add_apply]
  have hD1 : 0 ≤ Real.log D := Real.log_nonneg (le_max_left _ _)
  have hrD : ‖y - x‖ ≤ D :=
    calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ ρ + ‖x‖ := by linarith [hρ y hy]
      _ ≤ D := le_max_right _ _
  have hup : Real.log ‖y - x‖ ≤ Real.log D := by
    rcases (norm_nonneg (y - x)).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; exact hD1
    · exact Real.log_le_log h0 hrD
  rw [Real.norm_eq_abs, ENNReal.toReal_ofReal']
  have m1 := le_max_left (-Real.log ‖y - x‖) 0
  have m2 := le_max_right (-Real.log ‖y - x‖) 0
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem integrable_neumannH_right_K3 {ν : Measure ℂ} (hν : IsAdmissibleH ν) (x : ℂ) :
    Integrable (fun y => neumannH y x) ν := by
  unfold neumannH
  exact (integrable_log_norm_sub_K3 hν x).neg.sub (integrable_log_norm_sub_K3 hν (conj x))

theorem integrable_continuous_adm_K3 {ν : Measure ℂ} (hν : IsAdmissibleH ν) {f : ℂ → ℝ}
    (hf : Continuous f) : Integrable f ν := by
  obtain ⟨hνf, ⟨K, hK, -, hKc⟩, -⟩ := hν
  have := hνf
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hKae : ∀ᵐ y ∂ν, y ∈ K := ae_iff.2 hKc
  exact Integrable.of_bound hf.aestronglyMeasurable C (hKae.mono fun y hy => hC y hy)

theorem integrable_singKer_prod {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν)
    {s : ℝ} (hs : 0 < s) : Integrable (fun p : ℂ × ℂ => singKer s p.1 p.2) (μ.prod ν) := by
  refine ((integrable_neumannH_prod hμ hν).add
    (integrable_prod_of_continuous_adm hμ hν (continuous_singKer_sub hs))).congr
    (ae_of_all _ fun p => ?_)
  simp only [Pi.add_apply]
  rw [singKer, neumannH_symm p.2 p.1]; ring

/-- Parametric continuity of folded-circle averages. -/
theorem continuous_integral_foldedCircle_param {g : ℂ × ℂ → ℝ} (hg : Continuous g) (r : ℝ) :
    Continuous fun p : ℂ × ℂ => ∫ u, g (p.2, u) ∂foldedCircle p.1 r := by
  have e : (fun p : ℂ × ℂ => ∫ u, g (p.2, u) ∂foldedCircle p.1 r) = fun p =>
      (2 * π)⁻¹ * ∫ θ in Icc (-π) π, g (p.2, foldH (circleMap p.1 r θ)) := by
    funext p
    have hc : Continuous fun u => g (p.2, u) := hg.comp (continuous_const.prodMk continuous_id)
    rw [integral_foldedCircle_eq hc, integral_circleUnif_eq (hc.comp CircleFubini.continuous_foldH'),
      integral_Icc_eq_integral_Ioo]
    rfl
  rw [e]
  have hc : Continuous (fun q : (ℂ × ℂ) × ℝ => circleMap q.1.1 r q.2) := by
    simp only [circleMap]; fun_prop
  exact continuous_const.mul (continuous_parametric_integral_of_continuous
    (f := fun (p : ℂ × ℂ) (θ : ℝ) => g (p.2, foldH (circleMap p.1 r θ)))
    (hg.comp ((continuous_snd.comp continuous_fst).prodMk
      (CircleFubini.continuous_foldH'.comp hc))) isCompact_Icc)

/-- The folded-circle average of `singKer` in closed form (mean value formula). -/
theorem integral_singKer_foldedCircle {y : ℂ} (hy : y ∈ Hbar) {s : ℝ} (hs : 0 < s) (x : ℂ) :
    ∫ x', singKer s x x' ∂foldedCircle y s =
      (-Real.log (max s ‖y - x‖) - Real.log (max s ‖y - conj x‖)) +
        ∫ x', (Real.log (max s ‖x' - x‖) + Real.log (max s ‖x' - conj x‖)) ∂foldedCircle y s := by
  have hadm := isAdmissibleH_foldedCircle hy hs
  have hc : Continuous fun x' : ℂ =>
      Real.log (max s ‖x' - x‖) + Real.log (max s ‖x' - conj x‖) :=
    (continuous_singKer_sub hs).comp (continuous_const.prodMk continuous_id)
  rw [← integral_neumannH_foldedCircle y x hs,
    ← integral_add (integrable_neumannH_right_K3 hadm x) (integrable_continuous_adm_K3 hadm hc)]
  congr 1; funext x'; rw [singKer]; ring

/-! ## The kernel -/

/-- The regular part in the variables `p = (y, x)`. -/
def mixedG (D S : Set ℂ) (s : ℝ) (p : ℂ × ℂ) : ℝ :=
  (∫ x', singKer s p.2 x' ∂foldedCircle p.1 s) +
    ⟪rieszVec D (mixedSpace D S) (foldedCircle p.1 s),
      rieszVec D (mixedSpace D S) (foldedCircle p.2 s)⟫

/-- **M6 kernel.** `mixedK x y = log max(s,|x−y|) + log max(s,|x−ȳ|) + mixedG (y, x)`. -/
def mixedK (D S : Set ℂ) (s : ℝ) (x y : ℂ) : ℝ :=
  (Real.log (max s ‖x - y‖) + Real.log (max s ‖x - conj y‖)) + mixedG D S s (y, x)

theorem continuousOn_mixedG (hKH : K ⊆ Hbar) {s : ℝ} (hs : 0 < s)
    (hcont : ContinuousOn (fun z => rieszVec D (mixedSpace D S) (foldedCircle z s)) K) :
    ContinuousOn (mixedG D S s) (K ×ˢ K) := by
  have h1 : ContinuousOn (fun p : ℂ × ℂ => ∫ x', singKer s p.2 x' ∂foldedCircle p.1 s)
      (K ×ˢ K) := by
    have hc : Continuous fun p : ℂ × ℂ =>
        (-Real.log (max s ‖p.1 - p.2‖) - Real.log (max s ‖p.1 - conj p.2‖)) +
          ∫ x', (Real.log (max s ‖x' - p.2‖) + Real.log (max s ‖x' - conj p.2‖))
            ∂foldedCircle p.1 s := by
      refine Continuous.add ?_ (continuous_integral_foldedCircle_param
        (g := fun q : ℂ × ℂ => Real.log (max s ‖q.2 - q.1‖) + Real.log (max s ‖q.2 - conj q.1‖))
        (continuous_singKer_sub hs) s)
      have h := (continuous_singKer_sub hs).comp continuous_swap
      have e : (fun p : ℂ × ℂ => -Real.log (max s ‖p.1 - p.2‖) -
          Real.log (max s ‖p.1 - conj p.2‖)) = fun p => -((fun p : ℂ × ℂ =>
            Real.log (max s ‖p.2 - p.1‖) + Real.log (max s ‖p.2 - conj p.1‖)) ∘ Prod.swap) p := by
        funext p; simp only [Function.comp, Prod.fst_swap, Prod.snd_swap]; ring
      rw [e]; exact h.neg
    refine hc.continuousOn.congr fun p hp => ?_
    exact integral_singKer_foldedCircle (hKH hp.1) hs p.2
  have h2 : ContinuousOn (fun p : ℂ × ℂ =>
      ⟪rieszVec D (mixedSpace D S) (foldedCircle p.1 s),
        rieszVec D (mixedSpace D S) (foldedCircle p.2 s)⟫) (K ×ˢ K) :=
    (hcont.comp continuousOn_fst fun p hp => hp.1).inner
      (hcont.comp continuousOn_snd fun p hp => hp.2)
  exact h1.add h2

theorem continuousOn_mixedK (hKH : K ⊆ Hbar) {s : ℝ} (hs : 0 < s)
    (hcont : ContinuousOn (fun z => rieszVec D (mixedSpace D S) (foldedCircle z s)) K) :
    ContinuousOn (Function.uncurry (mixedK D S s)) (K ×ˢ K) := by
  have h1 := ((continuous_singKer_sub hs).comp continuous_swap).continuousOn (s := K ×ˢ K)
  have h2 := (continuousOn_mixedG hKH hs hcont).comp continuous_swap.continuousOn
    (fun p (hp : p ∈ K ×ˢ K) => ⟨hp.2, hp.1⟩)
  exact h1.add h2

/-! ## Nondegeneracy of the mixed space -/

/-- A nonempty open `D` carries a smooth bump in `mixedSpace D S` with positive energy. -/
theorem exists_pos_energy_mixedSpace {D S : Set ℂ} (hD : IsOpen D) (hne : D.Nonempty) :
    ∃ g ∈ mixedSpace D S, 0 < dirichletEnergyOn D g := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hD p hp
  let β : ContDiffBump p := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (β : ℂ → ℝ) := β.contDiff
  have hsuppD : tsupport (β : ℂ → ℝ) ⊆ D := by
    rw [β.tsupport_eq]
    exact (closedBall_subset_ball (by show r / 2 < r; linarith)).trans hball
  have hF : Continuous fun z => ‖fderiv ℝ (β : ℂ → ℝ) z‖ ^ 2 :=
    ((hgs.continuous_fderiv (by simp)).norm).pow 2
  have hFc : HasCompactSupport fun z => ‖fderiv ℝ (β : ℂ → ℝ) z‖ ^ 2 :=
    (β.hasCompactSupport.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℝ => ‖L‖ ^ 2)
      (by simp)
  have hout : ∀ z, z ∉ D → ‖fderiv ℝ (β : ℂ → ℝ) z‖ ^ 2 = 0 := by
    intro z hz
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hz (hsuppD h))]; simp
  refine ⟨β, ⟨hgs, (hF.integrable_of_hasCompactSupport hFc).integrableOn,
    (tsupport (β : ℂ → ℝ))ᶜ, (isClosed_tsupport _).isOpen_compl, fun z hz hzs => ?_,
    fun z hz => image_eq_zero_of_notMem_tsupport hz⟩, ?_⟩
  · rw [hD.frontier_eq] at hz
    exact hz.1.2 (hsuppD hzs)
  · have hex : ∃ x, ‖fderiv ℝ (β : ℂ → ℝ) x‖ ^ 2 ≠ 0 := by
      by_contra hall
      push Not at hall
      have h0 : ∀ x, fderiv ℝ (β : ℂ → ℝ) x = 0 := fun x => by simpa using hall x
      have hc := is_const_of_fderiv_eq_zero (hgs.differentiable (by simp)) h0 p (p + r)
      have h1 : (β : ℂ → ℝ) p = 1 := β.one_of_mem_closedBall (mem_closedBall_self (by
        show (0 : ℝ) ≤ r / 4; positivity))
      have h2 : (β : ℂ → ℝ) (p + r) = 0 := β.zero_of_le_dist (by
        rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hr.le]
        show r / 2 ≤ r; linarith)
      rw [h1, h2] at hc; exact one_ne_zero hc
    obtain ⟨x, hx⟩ := hex
    have hpos := hF.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) hFc
      (fun _ => by positivity) hx
    unfold dirichletEnergyOn
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout]
    exact mul_pos (by positivity) hpos

/-! ## Assembly -/

/-- **M6 (conditional on norm continuity).** -/
theorem dualCov_mixed_eq_kernelCov_mixedK (h : MixedLocalHyp D S K R)
    (hpos : ∃ g ∈ mixedSpace D S, 0 < dirichletEnergyOn D g) {s : ℝ} (hs : 0 < s) (hsR : s < R)
    (hcont : ContinuousOn (fun z => rieszVec D (mixedSpace D S) (foldedCircle z s)) K)
    {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ) (hμK : μ Kᶜ = 0) (hν : IsAdmissibleH ν)
    (hνK : ν Kᶜ = 0) :
    dualCov D (mixedSpace D S) μ ν =
      kernelCov (fun x y => neumannH x y + mixedK D S s x y) μ ν := by
  set V := mixedSpace D S with hV
  have hμf := hμ.1
  have hνf := hν.1
  have hKH : K ⊆ Hbar := fun z hz => (h.local_ z hz).1
  have hμD := isAdmissibleDual_mixed_of_local h.isOpen h.subset_H h.bounded h.free_real
    h.compact h.pos h.local_ hμ hμK
  have hνD := isAdmissibleDual_mixed_of_local h.isOpen h.subset_H h.bounded h.free_real
    h.compact h.pos h.local_ hν hνK
  have hKae : ∀ᵐ y ∂ν, y ∈ K := ae_iff.2 hνK
  obtain ⟨Bs, hBs⟩ := exists_norm_rieszVec_foldedCircle_le h.isOpen h.subset_H h.bounded
    h.free_real h.pos h.local_ hs hsR
  have hGint : Integrable (mixedG D S s) (ν.prod μ) :=
    integrable_prod_of_continuousOn_K3 h.compact h.compact hνK hμK (continuousOn_mixedG hKH hs hcont)
  -- the pairing with a local folded circle
  have eC : ∀ y ∈ K, ⟪rieszVec D V (foldedCircle y s), rieszVec D V μ⟫ =
      ∫ x, mixedG D S s (y, x) ∂μ := by
    intro y hy
    have hloc := h.local_ y hy
    have hρ := isAdmissibleH_foldedCircle hloc.1 hs
    have hρf := hρ.1
    have hρD := isAdmissibleDual_foldedCircle_of_local h.isOpen h.subset_H h.bounded h.free_real
      hloc hs (by linarith)
    have e1 := inner_rieszVec_sub_bind_eq_integral_singKer h hpos hρ hρD hμ hμK hs hsR
    obtain ⟨m2, e2⟩ := inner_rieszVec_bind_eq_integral h hpos hμ hμK hs hsR
      (rieszVec_mem (μ := foldedCircle y s))
    have eq0 : ⟪rieszVec D V (foldedCircle y s), rieszVec D V μ⟫ =
        ⟪rieszVec D V (foldedCircle y s), rieszVec D V μ -
          rieszVec D V (μ.bind fun w => foldedCircle w s)⟫ +
        ⟪rieszVec D V (μ.bind fun w => foldedCircle w s), rieszVec D V (foldedCircle y s)⟫ := by
      rw [inner_sub_right, real_inner_comm (rieszVec D V (foldedCircle y s))
        (rieszVec D V (μ.bind fun w => foldedCircle w s))]; ring
    have hS := integrable_singKer_prod hμ hρ hs
    have i2 : Integrable (fun z => ⟪rieszVec D V (foldedCircle z s),
        rieszVec D V (foldedCircle y s)⟫) μ :=
      Integrable.of_bound m2 (Bs * Bs) ((ae_iff.2 hμK).mono fun z hz => by
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hBs z hz) (hBs y hy)
          (norm_nonneg _) ((norm_nonneg _).trans (hBs z hz))))
    rw [eq0, e1, e2, integral_prod _ hS, ← integral_add hS.integral_prod_left i2]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [mixedG]
    rw [real_inner_comm]
  -- the four-term expansion
  have eA : ⟪rieszVec D V μ, rieszVec D V ν⟫ =
      ⟪rieszVec D V μ, rieszVec D V ν - rieszVec D V (ν.bind fun w => foldedCircle w s)⟫ +
        ⟪rieszVec D V (ν.bind fun w => foldedCircle w s), rieszVec D V μ⟫ := by
    rw [inner_sub_right, real_inner_comm (rieszVec D V μ)
      (rieszVec D V (ν.bind fun w => foldedCircle w s))]; ring
  obtain ⟨-, eB⟩ := inner_rieszVec_bind_eq_integral h hpos hν hνK hs hsR (rieszVec_mem (μ := μ))
  have hSint := integrable_singKer_prod hν hμ hs
  have hNk : Integrable (fun p : ℂ × ℂ => neumannH p.1 p.2 + mixedK D S s p.1 p.2) (μ.prod ν) :=
    (integrable_neumannH_prod hμ hν).add (integrable_prod_of_continuousOn_K3 h.compact h.compact
      hμK hνK (continuousOn_mixedK hKH hs hcont))
  have eN : kernelCov (fun x y => neumannH x y + mixedK D S s x y) μ ν =
      ∫ p, neumannH p.1 p.2 + mixedK D S s p.1 p.2 ∂(μ.prod ν) := by
    rw [kernelCov]; exact (integral_prod _ hNk).symm
  have eS : ∫ p, neumannH p.1 p.2 + mixedK D S s p.1 p.2 ∂(μ.prod ν) =
      ∫ p, neumannH p.2 p.1 + mixedK D S s p.2 p.1 ∂(ν.prod μ) :=
    (integral_prod_swap (fun p : ℂ × ℂ => neumannH p.1 p.2 + mixedK D S s p.1 p.2)).symm
  have eG : ∫ y, ∫ x, mixedG D S s (y, x) ∂μ ∂ν = ∫ p, mixedG D S s p ∂(ν.prod μ) :=
    (integral_prod _ hGint).symm
  rw [dualCov_eq_inner_rieszVec (isDNSpace_mixedSpace D S) hμD hνD, eA,
    inner_rieszVec_sub_bind_eq_integral_singKer h hpos hμ hμD hν hνK hs hsR, eB,
    integral_congr_ae (hKae.mono eC), eG, ← integral_add hSint hGint, eN, eS]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [mixedK, singKer]
  rw [neumannH_symm p.2 p.1]
  ring

end QuantumZipper.K3
