import QuantumZipper.Proofs.Thm18.G3Za7
import QuantumZipper.Proofs.Thm18.G3Za5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-A, items (a) + (b): the Palm-case one-point core with the Palm gauge

`exists_g0Setup_palm`: for an admissible local map `ψ` of G0, `0 < γ < 2`, a profile
`f = γ(−log ‖·‖) + h` near `0` (radius `ρf`; `h` continuous, harmonic and
conjugation-invariant there; `f` measurable) and an admissible probability measure `S` carried by
`{‖y‖ > ρf}` (the Palm normalizing circle, far from the zoom point), there are `0 < r < s`
and, on one probability space, a free field `W` and **D3⁺ `Setup` data with `α = γ`** such that
almost surely, for every level `L`,

  `AgreeNear (addConst (coordChange (ofFun f + W) ψ Q) (L/γ − W(S))) (zoomModel γ γ L fc(0,s) X' g) r`.

The left side is the zoom through `ψ`, at level `L`, of `ofFun f + W` normalized by the raw
value of `W` at `S` (the Palm normalization `normAt S` of `G3WedgePalmIdStmt`, up to the
deterministic constant `∫ f dS`, which shifts the level). No re-normalization at `fc(0,s)` is
needed: the gauge constant `W(Ψ_*ρ₀) − W(S)` is, in the coupling, `X'(ρ₀) − X'(bal ρ₀)` plus a
`σ(Ξ)`-measurable variable (`exists_pullSetupFar`), and it is absorbed into the model function
`g`, which stays `condSigma`-measurable. Sources: Sheffield arXiv:1012.4797 pp. 70–71;
Sheffield 2007 §2.2, Thm. 2.17. Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology ComplexConjugate
open scoped ENNReal NNReal

namespace QuantumZipper
namespace G3Za

open G3Cv K3 GFFExist LQGDimension.ExistAsm D3Plus InnerProductSpace

/-- **The Palm-case one-point core with the Palm gauge.** -/
theorem exists_g0Setup_palm {r₀ : ℝ} {ψ : ℂ → ℂ} (hr₀ : 0 < r₀)
    (hψ : Thm18Asm.IsG0Map r₀ ψ) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρf : ℝ} (hρf : 0 < ρf)
    {f h : ℂ → ℝ} (hf : ∀ u ∈ closedBall (0 : ℂ) ρf ∩ Hbar, f u = γ * -Real.log ‖u‖ + h u)
    (hh : Continuous h) (hfm : Measurable f) (hhh : HarmonicOnNhd h (ball (0 : ℂ) ρf))
    (hhc : ∀ u ∈ ball (0 : ℂ) ρf, h (conj u) = h u)
    {S : Measure ℂ} (hS : IsAdmissibleH S) (hS1 : S Set.univ = 1)
    (hSf : ∀ᵐ y ∂S, ρf < ‖y‖) :
    ∃ r s : ℝ, 0 < r ∧ r < s ∧ ∃ (E' : Type) (_ : MeasurableSpace E')
      (W X' : (ℕ → ℝ) → FieldSample) (Ξ : (ℕ → ℝ) → E') (g : (ℕ → ℝ) → ℂ → ℝ),
      IsFreeGFFModConstH W stdP ∧ Setup γ γ r (foldedCircle 0 s) stdP X' Ξ g ∧
      ∀ᵐ ω ∂stdP, ∀ L : ℝ,
        AgreeNear (addConst (coordChange (ofFun f + W ω) ψ (Qc γ)) (L / γ - W ω S))
          (zoomModel γ γ L (foldedCircle 0 s) (X' ω) (g ω)) r := by
  obtain ⟨Ψ, r₀', ρ, r₁, m, M, hr₁0, hD, heq⟩ := pullData_of_isG0Map hr₀ hψ
  have hr₀'0 : 0 < r₀' := hD.conf.pos
  have hΨ0 : Ψ 0 = 0 := by
    rw [heq (mem_ball_self hr₀'0)]; exact hψ.2.2.2.1
  have hM := hD.bl.2.1
  set ρ' := min ρ (ρf / (2 * M)) with hρ'
  have hρ'0 : 0 < ρ' := lt_min hD.hρ (by positivity)
  have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
  have hMρ' : M * ρ' < ρf := by
    have h1 : ρ' ≤ ρf / (2 * M) := min_le_right _ _
    have h2 : M * ρ' ≤ M * (ρf / (2 * M)) := mul_le_mul_of_nonneg_left h1 hM.le
    have h3 : M * (ρf / (2 * M)) = ρf / 2 := by field_simp
    linarith
  have hD' : PullData Ψ 0 r₀' ρ' (ρ' / 2) m M :=
    G3Za.PullData.shrink hD (by positivity) (by linarith) hρ'ρ
  set r' := ρ' / 4 with hr'
  have hr'0 : 0 < r' := by positivity
  obtain ⟨W, X', Ξ, gS, hW, hX, hΞ, hind, hgh, hgm, hid, hfar⟩ :=
    exists_pullSetupFar hD' (by positivity) hr'0 (by linarith)
  set s := r' / 2 with hs
  set r := r' / 4 with hr
  have hs0 : 0 < s := by positivity
  have hr0 : 0 < r := by positivity
  have hrs : r < s := by linarith
  set ρ₀ := foldedCircle 0 s with hρ₀
  have hρ₀A : IsAdmissibleH ρ₀ := isAdmissibleH_foldedCircle_g3cv2 0 hs0
  have hρ₀c : ρ₀ (closedBall ((0 : ℝ) : ℂ) (ρ' / 2))ᶜ = 0 := by
    have := foldedCircle_compl_null0 (c := 0) (R := ρ' / 2) hs0 (by rw [norm_zero]; linarith)
    exact measure_mono_null (compl_subset_compl.2 inter_subset_left) (by simpa using this)
  have hρ₀B : ρ₀ (ball (0 : ℂ) r) = 0 := by
    rw [hρ₀, foldedCircle, Measure.map_apply measurable_foldH measurableSet_ball]
    have h := ae_iff.1 (K3.ae_mem_sphere_circleUnif_k3 (0 : ℂ) hs0)
    refine measure_mono_null (fun v hv => ?_) h
    intro hv'
    have h1 : ‖foldH v‖ = s := by
      have e : ‖foldH v‖ = ‖v‖ := by unfold foldH; split_ifs <;> simp
      rw [e]; simpa using mem_sphere_iff_norm.1 hv'
    have h2 := mem_ball_zero_iff.1 hv
    linarith
  -- the far gauge constant
  have hSy : ∀ᵐ y ∂S, ∀ w ∈ closedBall ((0 : ℝ) : ℂ) ρ', Ψ w ≠ y ∧ Ψ w ≠ conj y := by
    filter_upwards [hSf] with y hy w hw
    have h00 : ((0 : ℝ) : ℂ) ∈ closedBall ((0 : ℝ) : ℂ) ρ' := mem_closedBall_self hρ'0.le
    have hb := (hD'.bl.2.2 w hw _ h00).2
    simp only [Complex.ofReal_zero, sub_zero, hΨ0] at hb
    have hw' : ‖w‖ ≤ ρ' := by simpa using hw
    have hΨw : ‖Ψ w‖ < ‖y‖ := by nlinarith
    refine ⟨fun e => by rw [e] at hΨw; exact lt_irrefl _ hΨw, fun e => ?_⟩
    rw [e, Complex.norm_conj] at hΨw; exact lt_irrefl _ hΨw
  obtain ⟨D, hDm, hDae⟩ := hfar ⟨ρ₀, hρ₀A, hρ₀c⟩ S hS (by rw [measure_univ, hS1]) hSy
  -- deterministic pieces
  set Q := Qc γ with hQ
  set lg : ℂ → ℝ := fun z => Q * Real.log ‖deriv Ψ (foldH z)‖ with hlg
  have hlgh : HarmonicOnNhd lg (ball ((0 : ℝ) : ℂ) r₀') := by
    have := harmonicOnNhd_logDeriv_foldH hD'.conf Q
    simpa using this
  have hk := harmonicOnNhd_remK_foldH (γ := γ) hD' hΨ0 hhh hhc hMρ'
  set k := remK γ Ψ h with hkdef
  have hsr' : r' < ρ' := by linarith
  have hr'r₀ : r' < r₀' := by linarith [hD'.hρr]
  have hgSc : ∀ ω, ContinuousOn (gS ω) (closedBall ((0 : ℝ) : ℂ) s ∩ Hbar) := fun ω =>
    continuousOn_of_harmonic_foldH (fun z hz => hgh ω z (ball_subset_closedBall
      (by simpa using hz))) (by linarith : s < r')
  have hlgc : ContinuousOn lg (closedBall ((0 : ℝ) : ℂ) s ∩ Hbar) := fun z hz =>
    (hlgh z (closedBall_subset_ball (by linarith : s < r₀') hz.1)).1.continuousAt.continuousWithinAt
  have hkc : ContinuousOn k (closedBall ((0 : ℝ) : ℂ) s ∩ Hbar) :=
    continuousOn_of_harmonic_foldH hk (by linarith)
  -- the reference constant
  set G : (ℕ → ℝ) → ℝ := fun ω => ∫ z, gS ω z ∂ρ₀ with hG
  have hle0 : MeasurableSpace.comap Ξ inferInstance ⊔ outsideSigma X' ((0 : ℝ)) ρ' ≤
      condSigma Ξ X' r := sup_le_sup_left (outsideSigma_anti_radius X' 0 (by linarith)) _
  have hGm : Measurable[condSigma Ξ X' r] G := by
    have hret := continuous_retr_m7b 0 hs0
    have hretK : ∀ v, retr 0 s v ∈ closedBall ((0 : ℝ) : ℂ) s ∩ Hbar := fun v =>
      ⟨mem_closedBall_iff_norm.2 (norm_retr_sub_le hs0 v), retr_mem_Hbar hs0 v⟩
    set u : ℂ → (ℕ → ℝ) → ℝ := fun v ω => gS ω (retr 0 s v) with hu
    have hfc0 : ρ₀ (closedBall ((0 : ℝ) : ℂ) s ∩ Hbar)ᶜ = 0 :=
      foldedCircle_compl_null (b := 0) hs0 (by simp)
    have heqG : G = fun ω => ∫ v, u v ω ∂ρ₀ := by
      funext ω
      refine integral_congr_ae ((ae_mem_of_compl_null_g3cv hfc0).mono fun z hz => ?_)
      simp only [hu, retr_eq_self hz.2 (mem_closedBall_iff_norm.1 hz.1)]
    rw [heqG]
    exact @measurable_integral_family (ℕ → ℝ) (condSigma Ξ X' r) u
      (fun ω => (hgSc ω).comp_continuous hret hretK) (fun v => (hgm _).mono hle0 le_rfl) ρ₀ _
  have hbal := isAdmissibleH_bal (μ := ρ₀) (t := 0) hD'.hρ (by linarith : ρ' / 2 < ρ') hρ₀c
  have hOm : Measurable[condSigma Ξ X' r] fun ω => X' ω ρ₀ - X' ω (bal 0 ρ' ρ₀) :=
    (measurable_outsideSigma hρ₀A hbal (bal_univ hD'.hρ (by linarith) hρ₀c).symm
      (by simpa using hρ₀B)
      (measure_mono_null (ball_subset_ball (by linarith)) (bal_ball hD'.hρ))).mono
      le_sup_right le_rfl
  set cst : (ℕ → ℝ) → ℝ := fun ω => D ω + (X' ω ρ₀ - X' ω (bal 0 ρ' ρ₀)) - G ω with hcst
  have hcm : Measurable[condSigma Ξ X' r] cst :=
    ((hDm.mono le_sup_left le_rfl).add hOm).sub hGm
  set g : (ℕ → ℝ) → ℂ → ℝ := fun ω z => gS ω z + lg z + k z + cst ω with hg
  refine ⟨r, s, hr0, hrs, _, inferInstance, W, X', Ξ, g, hW, ?_, ?_⟩
  · have hα : γ < Qc γ := by
      unfold Qc
      have : γ / 2 < 2 / γ := by
        rw [div_lt_div_iff₀ (by norm_num) hγ]; nlinarith
      linarith
    refine ⟨hγ, hγ2, hα, hr0, hX, hΞ, hind, hρ₀A, measure_univ, hρ₀B, fun ω => ?_,
      fun z => ?_⟩
    · intro z hz
      have hz1 : z ∈ closedBall ((0 : ℝ) : ℂ) r' := by
        have h := mem_ball_zero_iff.1 hz
        rw [Complex.ofReal_zero, mem_closedBall_zero_iff]; linarith
      have h1 := hgh ω z hz1
      have h2 : HarmonicAt (fun z => lg (foldH z)) z := by
        have e : (fun z => lg (foldH z)) = lg := by
          funext v
          simp only [hlg, CircleFubini.foldH_of_mem' (CircleFubini.foldH_mem_Hbar' v)]
        rw [e]; exact hlgh z (by
          have : z ∈ ball (0 : ℂ) r₀' := ball_subset_ball (by linarith) hz
          simpa using this)
      have h3 := hk z (ball_subset_ball (by linarith) hz)
      exact ((h1.add h2).add h3).add (harmonicAt_const (cst ω))
    · exact ((((hgm z).mono hle0 le_rfl).add_const (lg z)).add_const (k z)).add hcm
  · -- agreement near `0`
    have hc : ∀ n : ℕ, (Set.range (dyadicRoundC n)).Countable := fun n => by
      have hsub : Set.range (dyadicRoundC n) ⊆
          Set.range (fun p : ℤ × ℤ =>
            (⟨(p.1 : ℝ) / (2 : ℝ) ^ n, (p.2 : ℝ) / (2 : ℝ) ^ n⟩ : ℂ)) := by
        rintro _ ⟨z, rfl⟩
        exact ⟨(⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋), rfl⟩
      exact (Set.countable_range _).mono hsub
    have hall : ∀ᵐ ω ∂stdP, ∀ n k', ∀ d ∈ Set.range (dyadicRoundC n),
        ‖d‖ + radius k' < r →
        (W ω ((foldedCircle d (radius k')).map Ψ) - W ω (ρ₀.map Ψ) =
          X' ω (foldedCircle d (radius k')) - X' ω ρ₀ +
            ((∫ z, gS ω z ∂foldedCircle d (radius k')) - ∫ z, gS ω z ∂ρ₀)) ∧
        coordChange (ofFun f + W ω) Ψ Q (foldedCircle d (radius k')) =
          coordChange (W ω) Ψ Q (foldedCircle d (radius k')) +
            ∫ u, f (Ψ u) ∂foldedCircle d (radius k') ∧
        coordChange (W ω) Ψ Q (foldedCircle d (radius k')) =
          W ω (pullCircle Ψ d (radius k')) +
            Q * ∫ z, Real.log ‖deriv Ψ z‖ ∂(foldedCircle d (radius k')) := by
      rw [ae_all_iff]; intro n
      rw [ae_all_iff]; intro k'
      rw [ae_ball_iff (hc n)]
      intro d _
      by_cases hd : ‖d‖ + radius k' < r
      · have hk0 := radius_pos k'
        have hfcb : foldedCircle d (radius k') (closedBall ((0 : ℝ) : ℂ) r')ᶜ = 0 := by
          have := foldedCircle_compl_null0 (R := r') hk0 (by linarith)
          exact measure_mono_null (compl_subset_compl.2 inter_subset_left) (by simpa using this)
        have hρ₀b : ρ₀ (closedBall ((0 : ℝ) : ℂ) r')ᶜ = 0 := by
          have := foldedCircle_compl_null0 (c := 0) (R := r') hs0 (by rw [norm_zero]; linarith)
          exact measure_mono_null (compl_subset_compl.2 inter_subset_left) (by simpa using this)
        filter_upwards [hid _ _ (isAdmissibleH_foldedCircle_g3cv2 d hk0) hρ₀A
            (by simp [measure_univ]) hfcb hρ₀b,
          ae_coordChange_ofFun_add_pullCircle hW hD' hΨ0 hf hh hfm hMρ' Q hk0
            (by linarith : ‖d‖ + radius k' ≤ ρ'),
          ae_coordChange_pullCircle hW hD' Q hk0 (by simp; linarith)] with ω h1 h2 h3 _
        exact ⟨h1, h2, h3⟩
      · exact ae_of_all _ fun ω h => absurd h hd
    filter_upwards [hall, hDae] with ω hω hDω L n k' z hz
    set d := dyadicRoundC n z
    set fcd := foldedCircle d (radius k') with hfcd
    have hk0 := radius_pos k'
    obtain ⟨h1, h2, h3⟩ := hω n k' d ⟨z, rfl⟩ hz
    have hnull : fcd (closedBall ((0 : ℝ) : ℂ) s ∩ Hbar)ᶜ = 0 :=
      foldedCircle_compl_null (b := 0) hk0 (by simp; linarith)
    have hae := ae_mem_of_compl_null_g3cv hnull
    have hball : ∀ᵐ u ∂fcd, u ∈ ball (0 : ℂ) r₀' := hae.mono fun u hu => by
      have h1 : ‖u‖ ≤ s := by simpa using hu.1
      rw [mem_ball, dist_zero_right]; linarith
    have hgSi := integrable_of_continuousOn_closedBall_Hbar (hgSc ω) hnull
    have hlgi := integrable_of_continuousOn_closedBall_Hbar hlgc hnull
    have hki := integrable_of_continuousOn_closedBall_Hbar hkc hnull
    have hli : Integrable (fun u : ℂ => γ * -Real.log ‖u‖) fcd :=
      (CoordReg.integrable_log_norm_foldedCircle d (radius k')).neg.const_mul γ
    -- `f ∘ Ψ = γ(−log) + k` on the circle
    have hsplit : ∫ u, f (Ψ u) ∂fcd = (∫ u, γ * -Real.log ‖u‖ ∂fcd) + ∫ u, k u ∂fcd := by
      rw [← integral_add hli hki]
      refine integral_congr_ae ?_
      filter_upwards [hae, F1.ae_ne_zero_fc d hk0] with u hu hu0
      have hu1 : u ∈ closedBall (0 : ℂ) s := by simpa using hu.1
      have hu' : u ∈ closedBall (0 : ℂ) ρ' ∩ Hbar :=
        ⟨closedBall_subset_closedBall (show s ≤ ρ' by linarith) hu1, hu.2⟩
      exact comp_eq_remK hD' hΨ0 hf hMρ'.le hu' hu0
    have hlgI : ∫ u, lg u ∂fcd = Q * ∫ u, Real.log ‖deriv Ψ u‖ ∂fcd := by
      rw [← integral_const_mul]
      refine integral_congr_ae (hae.mono fun u hu => ?_)
      simp only [hlg, CircleFubini.foldH_of_mem' hu.2]
    have hgI : ∫ u, g ω u ∂fcd = (∫ u, gS ω u ∂fcd) + (∫ u, lg u ∂fcd) + (∫ u, k u ∂fcd) +
        cst ω := by
      simp only [hg]
      rw [integral_add (f := fun u => gS ω u + lg u + k u) (g := fun _ => cst ω)
          ((hgSi.add hlgi).add hki) (integrable_const _),
        integral_add (f := fun u => gS ω u + lg u) (g := k) (hgSi.add hlgi) hki,
        integral_add (f := gS ω) (g := lg) hgSi hlgi, integral_const,
        measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    have hgi : Integrable (g ω) fcd := ((hgSi.add hlgi).add hki).add (integrable_const _)
    rw [addConst_apply_fc, zoomModel_apply_fc hgi, coordChange_congr_ball heq hball, h2, h3,
      hsplit, hgI, hlgI]
    simp only [pullCircle, hcst] at *
    linarith

end G3Za
end QuantumZipper
