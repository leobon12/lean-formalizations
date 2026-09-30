import QuantumZipper.Proofs.GFF.K3.MixedM7AsmVer2

/-!
# K3-mixed M7-b (proved): harmonic versions, `PoissonHarmonicVersionStmt`

`poissonHarmonicVersion_holds t r r' : PoissonHarmonicVersionStmt t r r'` (the node M7-b of
`MixedM7Nodes.lean`, for all `t r r'`).

Proof (radii `r' < ρ₁ < s < ρ < r`):

1. The curve `u` is bounded and Lipschitz on `closedBall t ρ ∩ Hbar` (`MixedM7AsmVer1`), so the
   process `Z w = F (retr t ρ w)` satisfies the eighth-moment Kolmogorov bound, and its explicit
   Kolmogorov modification `kolY Z` (`HalfDiscMarkov.lean`; Revuz–Yor, *Continuous martingales
   and Brownian motion*, Ch. I, Thm (2.1)) is continuous on `Hbar` for every `ω` and measurable
   for every σ-algebra for which all `Z w` are measurable. Put `Hc ω x = kolY Z (foldH x) ω`.
2. For a fixed circle inside `ball t ρ`, stochastic Fubini (`procFubini_core`) and the weak
   mean-value property of `u ∘ foldH` give the mean-value property of `Hc` a.s.; by continuity
   this holds a.s. for all circles, so `Hc ω` is a.s. harmonic on `ball t ρ` (Weyl's lemma,
   `harmonicOnNhd_of_meanValue`), as in `ae_harmonicOnNhd_harmH`.
3. `G ω = poisSm t s ρ₁ (Hc ω)` (`MixedM7AsmPois`) is harmonic for **every** `ω`, has the same
   measurability as `Hc`, and equals `Hc ω` (hence `F z`) on `closedBall t r' ∩ Hbar` wherever
   `Hc ω` is harmonic (half-disc Poisson reproduction).

Source for the statement: Werner–Powell, *Lecture notes on the Gaussian free field*,
arXiv:2004.04720, Prop. 4.3 (a harmonic version of the harmonic part). The route (Kolmogorov
version, stochastic Fubini, Weyl's lemma, Poisson smoothing) is an own elementary assembly.
-/

noncomputable section

open MeasureTheory Filter Set Metric ProbabilityTheory Function
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

/-- **M7-b holds.** -/
theorem poissonHarmonicVersion_holds (t r r' : ℝ) : PoissonHarmonicVersionStmt t r r' := by
  intro hr' hr'r E _ _ _ Ω _ P _ u F hw hFm hlaw
  set δ : ℝ := (r - r') / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set ρ₁ : ℝ := r' + δ with hρ₁
  set s : ℝ := r' + 2 * δ with hs
  set ρ : ℝ := r' + 3 * δ with hρ
  have hr'ρ₁ : r' < ρ₁ := by linarith
  have hρ₁0 : 0 < ρ₁ := by linarith
  have hρ₁s : ρ₁ < s := by linarith
  have hsρ : s < ρ := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hρr : ρ < r := by rw [hρ, hδ]; linarith
  -- bounds on the curve
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_of_weakHarmonic hρr hw
  obtain ⟨L, hL0, hL⟩ := exists_lip_of_weakHarmonic hρ0 hρr hw
  have hretrK : ∀ w, retr t ρ w ∈ closedBall (t : ℂ) ρ ∩ Hbar := fun w =>
    ⟨mem_closedBall_iff_norm.2 (norm_retr_sub_le hρ0 w), retr_mem_Hbar hρ0 w⟩
  -- the process
  set Z : ℂ → Ω → ℝ := fun w => F (retr t ρ w) with hZdef
  set v : ℂ → E := fun w => u (retr t ρ w) with hvdef
  have hZm : ∀ w, Measurable (Z w) := fun w => hFm _
  have hZlaw : ∀ {ι : Type} [Fintype ι] (τ : ι → ℂ) (a : ι → ℝ),
      HasLaw (fun ω => ∑ i, a i * Z (τ i) ω) (gaussianReal 0 (‖∑ i, a i • v (τ i)‖ ^ 2).toNNReal)
        P := fun τ a => hlaw (fun i => retr t ρ (τ i)) a
  have hvB : ∀ w, ‖v w‖ ≤ B := fun w => hB _ (hretrK w)
  have hvc : Continuous v := by
    have hcont : ContinuousOn u (closedBall (t : ℂ) ρ ∩ Hbar) := by
      refine fun x hx => (LipschitzOnWith.continuousOn (K := L.toNNReal) ?_) x hx
      refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL0]
      exact hL a ha b hb
    exact hcont.comp_continuous (continuous_retr_m7b t hρ0) hretrK
  -- the moment bound
  set c : ℝ := 4 * ρ * L ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hmom : CircleCont.MomentBound Z P (c ^ 4 * gaussianAbsMoment 8) := by
    intro z _ w _
    have hl := hZlaw ![z, w] ![1, -1]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, 
      one_mul, neg_mul, one_smul, neg_smul, ← sub_eq_add_neg] at hl
    rw [CircleCont.lintegral_pow8_of_map_eq (U := fun ω => Z z ω - Z w ω) ((hZm z).sub (hZm w))
      hl.map_eq]
    apply ENNReal.ofReal_le_ofReal
    have hd := hL _ (hretrK z) _ (hretrK w)
    have hr1 := norm_retr_sub_retr_le (t := t) hρ0 z w
    have hr2 : ‖retr t ρ z - retr t ρ w‖ ≤ 2 * ρ := by
      have h1 := norm_retr_sub_le (t := t) hρ0 z
      have h2 := norm_retr_sub_le (t := t) hρ0 w
      calc ‖retr t ρ z - retr t ρ w‖ = ‖(retr t ρ z - t) - (retr t ρ w - t)‖ := by ring_nf
        _ ≤ ‖retr t ρ z - t‖ + ‖retr t ρ w - t‖ := norm_sub_le _ _
        _ ≤ 2 * ρ := by linarith
    have hvar : ‖v z - v w‖ ^ 2 ≤ c * ‖z - w‖ := by
      have hn := norm_nonneg (retr t ρ z - retr t ρ w)
      calc ‖v z - v w‖ ^ 2 ≤ (L * ‖retr t ρ z - retr t ρ w‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hd 2
        _ = L ^ 2 * (‖retr t ρ z - retr t ρ w‖ * ‖retr t ρ z - retr t ρ w‖) := by ring
        _ ≤ L ^ 2 * ((2 * ρ) * (2 * ‖z - w‖)) := by gcongr
        _ = c * ‖z - w‖ := by rw [hc]; ring
    have hv' : ((‖v z - v w‖ ^ 2).toNNReal : ℝ) ≤ c * ‖z - w‖ := by
      rw [Real.coe_toNNReal _ (sq_nonneg _)]; exact hvar
    calc ((‖v z - v w‖ ^ 2).toNNReal : ℝ) ^ 4 * gaussianAbsMoment 8 ≤
          (c * ‖z - w‖) ^ 4 * gaussianAbsMoment 8 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (NNReal.coe_nonneg _) hv' 4)
          (gaussianAbsMoment_nonneg 8)
      _ = c ^ 4 * gaussianAbsMoment 8 * ‖z - w‖ ^ 4 := by ring
  obtain ⟨hYc, hYv⟩ := kolY_spec (fun z => (hZm z).aemeasurable)
    (mul_nonneg (pow_nonneg hc0 4) (gaussianAbsMoment_nonneg 8)) hmom
  set Hc : Ω → ℂ → ℝ := fun ω x => kolY Z (foldH x) ω with hHcdef
  have hHcc : ∀ ω, Continuous (Hc ω) := fun ω =>
    (hYc ω).comp_continuous CircleFubini.continuous_foldH' CircleFubini.foldH_mem_Hbar'
  have hHcv : ∀ x, (fun ω => Hc ω x) =ᵐ[P] Z (foldH x) := fun x =>
    hYv _ (CircleFubini.foldH_mem_Hbar' x)
  have hHcm : Measurable (uncurry Hc) := by
    have hm : Measurable (uncurry fun (x : ℂ) (ω : Ω) => Hc ω x) :=
      measurable_uncurry_of_continuous_of_measurable (fun ω => hHcc ω)
        fun x => measurable_kolY hZm (CircleFubini.foldH_mem_Hbar' x)
    exact hm.comp measurable_swap
  have hHconj : ∀ ω x, Hc ω (conj x) = Hc ω x := fun ω x => by simp only [hHcdef, foldH_conj_k3]
  -- step 2: a.s. mean value on a fixed circle
  have hretr_fold : ∀ x : ℂ, ‖x - t‖ ≤ ρ → retr t ρ x = foldH x := fun x hx => by
    rw [← retr_foldH_m7b, retr_eq_self (CircleFubini.foldH_mem_Hbar' x)
      (by rw [norm_foldH_sub_ofReal]; exact hx)]
  have hmv1 : ∀ {z : ℂ} {σ : ℝ}, 0 < σ → ‖z - t‖ + σ < ρ →
      ∀ᵐ ω ∂P, ∫ x, Hc ω x ∂circleUnif z σ = Hc ω z := by
    intro z σ hσ hzσ
    have hk : ∀ e : E, ⟪v (foldH z), e⟫ = ∫ i, ⟪v (foldH i), e⟫ ∂circleUnif z σ := by
      intro e
      set f' : ℂ → ℝ := fun y => ⟪v (foldH y), e⟫ with hf'
      have hf'c : Continuous f' := (hvc.comp CircleFubini.continuous_foldH').inner
        continuous_const
      have heq : ∀ y ∈ ball (t : ℂ) ρ, f' y = ⟪u (foldH y), e⟫ := fun y hy => by
        simp only [hf', hvdef]
        rw [retr_eq_self (CircleFubini.foldH_mem_Hbar' y)
          (by rw [norm_foldH_sub_ofReal]; exact (mem_ball_iff_norm.1 hy).le)]
      have hharm : InnerProductSpace.HarmonicOnNhd f' (closedBall z |σ|) := by
        intro x hx
        rw [mem_closedBall_iff_norm, abs_of_pos hσ] at hx
        have hxt : ‖x - t‖ < ρ := by
          have := norm_sub_le_of_sphere (t := t) (z := z) (w := x) (s := ‖x - z‖) rfl
          linarith
        have hev : f' =ᶠ[𝓝 x] fun y => ⟪u (foldH y), e⟫ :=
          Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_iff_norm.2 hxt)) heq
        exact (InnerProductSpace.harmonicAt_congr_nhds hev).2
          (hw e x (mem_ball_iff_norm.2 (hxt.trans hρr)))
      rw [circleUnif_eq_circMeas_k3, LQGDimension.Coupling.integral_circMeas_eq_circleAverage
        (f := f') hf'c.measurable.aestronglyMeasurable]
      exact hharm.circleAverage_eq.symm
    have hcv : Continuous fun i : ℂ => v (foldH i) := hvc.comp CircleFubini.continuous_foldH'
    have hF := procFubini_core hZlaw (circleUnif z σ) foldH (M := B) (fun i => hvB _)
      ((hcv.comp continuous_fst).inner (hcv.comp continuous_snd)).measurable
      (fun x => (hcv.inner continuous_const).measurable) Hc hHcm hHcv hZm (foldH z) hk
    filter_upwards [hF, hHcv z] with ω h1 h2
    rw [h1, h2]
  -- step 2b: a.s. harmonic on `ball t ρ`
  have hharm_ae : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (Hc ω) (ball (t : ℂ) ρ) := by
    set Q : (ℚ × ℚ) × ℚ → ℂ × ℝ :=
      Prod.map (Complex.equivRealProdCLM.symm ∘ Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ))
        ((↑) : ℚ → ℝ) with hQ
    have hdense : DenseRange Q := by
      refine DenseRange.prodMap ?_ Rat.denseRange_cast
      exact (Complex.equivRealProdCLM.symm.surjective.denseRange).comp
        (Rat.denseRange_cast.prodMap Rat.denseRange_cast)
        Complex.equivRealProdCLM.symm.continuous
    set Es : Set (ℂ × ℝ) := {p | 0 < p.2 ∧ ‖p.1 - t‖ + p.2 < ρ} with hEs
    have hEo : IsOpen Es := (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt (((continuous_fst.sub continuous_const).norm).add continuous_snd)
        continuous_const)
    have hall : ∀ᵐ ω ∂P, ∀ q, Q q ∈ Es →
        ∫ w, Hc ω w ∂circleUnif (Q q).1 (Q q).2 = Hc ω (Q q).1 := by
      rw [ae_all_iff]
      intro q
      by_cases hq : Q q ∈ Es
      · filter_upwards [hmv1 hq.1 hq.2] with ω h _ using h
      · exact ae_of_all _ fun ω h => absurd h hq
    filter_upwards [hall] with ω hω
    have hu := hHcc ω
    have heq : Set.EqOn (fun p : ℂ × ℝ => ∫ w, Hc ω w ∂circleUnif p.1 p.2)
        (fun p => Hc ω p.1) Es := by
      refine Set.EqOn.of_subset_closure (s := Es ∩ Set.range Q) ?_
        (continuous_circleUnif_average hu).continuousOn (hu.comp continuous_fst).continuousOn
        Set.inter_subset_left (hdense.open_subset_closure_inter hEo)
      rintro p ⟨hpE, q, rfl⟩
      exact hω q hpE
    refine harmonicOnNhd_of_meanValue hu isOpen_ball fun z _ σ hσ hsub => ?_
    exact heq (x := (z, σ)) ⟨hσ, add_lt_of_closedBall_subset_ball hσ hsub⟩
  -- step 3: Poisson smoothing
  refine ⟨fun ω z => poisSm t s ρ₁ (Hc ω) z, fun ω => harmonicOnNhd_poisSm_foldH (hHcc ω) hρ₁0
    hρ₁s hr'ρ₁, fun z hz => ?_, fun m hm z => ?_⟩
  · have hzt := mem_closedBall_iff_norm.1 hz.1
    filter_upwards [hharm_ae, hHcv z] with ω h1 h2
    rw [poisSm_eq_of_harmonic hρ₁s (fun x hx => h1 x (closedBall_subset_ball hsρ hx))
      (fun x _ => hHconj ω x) hz.2 (by linarith), h2]
    simp only [hZdef, retr_foldH_m7b]
    rw [retr_eq_self hz.2 (by linarith)]
  · have hZm' : ∀ w, Measurable[m] (Z w) := fun w =>
      hm _ ⟨closedBall_subset_ball hρr (hretrK w).1, (hretrK w).2⟩
    exact measurable_poisSm m hHcc
      (fun w => @measurable_kolY Ω m Z hZm' (foldH w) (CircleFubini.foldH_mem_Hbar' w)) t s ρ₁ z

end QuantumZipper.K3
