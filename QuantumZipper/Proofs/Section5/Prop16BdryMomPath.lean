import QuantumZipper.Proofs.Section5.Prop16ActRegCouple

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, node B′-MOM: the pathwise comparison on the M7 coupling

On the half-disc coupling of `K3.MixedFreeCouplingHalfDiscStmt` (a mixed GFF `Y` and a free GFF
`X` with `Y = X − X(ρ₀)·mass + ∫ g` on measures carried by `closedBall t r'`, `g ∘ foldH`
harmonic), almost surely, simultaneously for all scales `k ≥ n` and all `s ∈ [t − η, t + η]`
(`η + 2^{-n} < r'`),

  `avgReg (h0 + Y) k s = ∫ h0 d fc(s, 2^{-k}) + avgReg (Z) k s + V(s)`,
  `V(s) = g(s) − X(ρ₀) + X(fc(0,R))`, `Z = zField X R = X − X(fc(0,R))`,

so the boundary masses satisfy (`ae_bdryApprox_le_bdryMom`)

  `bdryApprox_k(h0 + Y)([t−η,t+η]) ≤ e^{|γ| C_H / 2} · W · bdryApprox_k(Z)([t−η,t+η])`

for any `W ≥ sup_{s} e^{(γ/2) V(s)}` and `C_H ≥ sup |∫ h0 d fc(s, 2^{-k})|`. This is the domain
Markov comparison in the proof of Prop. 1.6 (Sheffield arXiv:1012.4797 p. 25: near a point of the
free arc the field is a free field plus a harmonic function), in the form used by
Duplantier–Sheffield (Invent. Math. 185 (2011), §6) to transfer boundary-measure estimates.
Own elementary argument, same scheme as `ae_avgReg_coupling`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal Real

namespace QuantumZipper

namespace Prop16Asm

/-- The dyadic centres at scale `k` whose folded circle stays inside `closedBall t r'`. -/
def cSetBdryMom (t r' : ℝ) (k : ℕ) : Set ℂ :=
  {c | c ∈ (⋃ n, Set.range (dyadicRoundC n)) ∧ c ∈ Hbar ∧ dist c (t : ℂ) + radius k < r'}

theorem countable_cSetBdryMom (t r' : ℝ) (k : ℕ) : (cSetBdryMom t r' k).Countable :=
  (Set.countable_iUnion countable_range_dyadicRoundC_ar).mono fun _ hc => hc.1

theorem eventually_mem_cSetBdryMom {t r' : ℝ} {k : ℕ} {s : ℂ} (hs : s ∈ Hbar)
    (hst : dist s (t : ℂ) + radius k < r') :
    ∀ᶠ j in atTop, dyadicRoundC j s ∈ cSetBdryMom t r' k := by
  set ε := r' - (dist s (t : ℂ) + radius k) with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hclose : ∀ᶠ n in atTop, dist (dyadicRoundC n s) s < ε :=
    (RegClosure.tendsto_dyadicRoundC s).eventually (Metric.ball_mem_nhds s hε)
  exact hclose.mono fun n hn => ⟨mem_iUnion.2 ⟨n, s, rfl⟩, CircleCont.dyadicRoundC_mem_Hbar hs n,
    by linarith [dist_triangle (dyadicRoundC n s) s (t : ℂ)]⟩

/-- The coupling representation on all dyadic circles of all scales, almost surely. -/
theorem ae_rep_cSet_bdryMom {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {Y X : Ω₀ → FieldSample} {g : Ω₀ → ℂ → ℝ} {t r' : ℝ} {ρ₀ : Measure ℂ}
    (hgh : ∀ ω, InnerProductSpace.HarmonicOnNhd (fun z => g ω (foldH z)) (closedBall (t : ℂ) r'))
    (hrep : ∀ μ : Measure ℂ, IsAdmissibleH μ → μ (closedBall (t : ℂ) r')ᶜ = 0 →
      ∀ᵐ ω ∂P₀, Y ω μ = X ω μ - (μ Set.univ).toReal * X ω ρ₀ + ∫ z, g ω z ∂μ) :
    ∀ᵐ ω ∂P₀, ∀ k, ∀ c ∈ cSetBdryMom t r' k, Y ω (foldedCircle c (radius k)) =
      X ω (foldedCircle c (radius k)) - X ω ρ₀ + g ω c := by
  rw [ae_all_iff]
  intro k
  have hr : 0 < radius k := radius_pos k
  have hball : ∀ c ∈ cSetBdryMom t r' k,
      closedBall c (radius k) ∩ Hbar ⊆ closedBall (t : ℂ) r' := fun c hc u hu => by
    have h1 : dist u c ≤ radius k := hu.1
    rw [mem_closedBall]
    linarith [dist_triangle u c (t : ℂ), hc.2.2]
  rw [ae_ball_iff (countable_cSetBdryMom t r' k)]
  intro c hc
  filter_upwards [hrep _ (isAdmissibleH_foldedCircle hc.2.1 hr)
    (measure_mono_null (compl_subset_compl.2 (hball c hc))
      (K3.foldedCircle_compl_eq_zero hc.2.1 hr.le))] with ω hω
  rw [hω, measure_univ, ENNReal.toReal_one, one_mul,
    integral_foldedCircle_of_harm_center ((hgh ω).mono ball_subset_closedBall) hc.2.1 hr
      (by rw [← dist_eq_norm]; exact hc.2.2)]

/-- Folded-circle averages of `h0` agree with those of a continuous `mc` inside the disc. -/
theorem integral_h0_eq_mc_bdryMom {h0 mc : ℂ → ℝ} {t r' : ℝ}
    (hEq : EqOn h0 mc (closedBall (t : ℂ) r' ∩ Hbar)) {k : ℕ} {c : ℂ} (hc : c ∈ Hbar)
    (hct : dist c (t : ℂ) + radius k < r') :
    ∫ u, h0 u ∂foldedCircle c (radius k) = ∫ u, mc u ∂foldedCircle c (radius k) := by
  refine integral_congr_ae ((Prop16Area.G.ae_fc_mem_ball_inter hc (radius_pos k)).mono fun u hu =>
    hEq ⟨?_, hu.2⟩)
  have h1 : dist u c ≤ radius k := hu.1
  rw [mem_closedBall]; linarith [dist_triangle u c (t : ℂ)]

/-- The `h0` part of the dyadic averages converges. -/
theorem tendsto_h0_dyadic_bdryMom {h0 mc : ℂ → ℝ} (hmc : Continuous mc) {t r' : ℝ}
    (hEq : EqOn h0 mc (closedBall (t : ℂ) r' ∩ Hbar)) {k : ℕ} {s : ℂ} (hs : s ∈ Hbar)
    (hst : dist s (t : ℂ) + radius k < r') :
    Tendsto (fun j => ∫ u, h0 u ∂foldedCircle (dyadicRoundC j s) (radius k)) atTop
      (𝓝 (∫ u, h0 u ∂foldedCircle s (radius k))) := by
  rw [integral_h0_eq_mc_bdryMom hEq hs hst]
  have h1 := (TwoPoint.continuous_integral_foldedCircle hmc).tendsto (s, radius k)
  have h2 : Tendsto (fun j : ℕ => (dyadicRoundC j s, radius k)) atTop (𝓝 (s, radius k)) :=
    (RegClosure.tendsto_dyadicRoundC s).prodMk_nhds tendsto_const_nhds
  refine (h1.comp h2).congr' ((eventually_mem_cSetBdryMom hs hst).mono fun j hj => ?_)
  exact (integral_h0_eq_mc_bdryMom hEq hj.2.1 hj.2.2).symm

/-- **The regularized averages of `h0 + Y` on the coupling** (pathwise, on the good event). -/
theorem avgReg_mixed_eq_bdryMom {Y X : FieldSample} {g : ℂ → ℝ} {t r' : ℝ} {ρ₀ : Measure ℂ}
    (hgh : InnerProductSpace.HarmonicOnNhd (fun z => g (foldH z)) (closedBall (t : ℂ) r'))
    {h0 mc : ℂ → ℝ} (hmc : Continuous mc) (hEq : EqOn h0 mc (closedBall (t : ℂ) r' ∩ Hbar))
    {k : ℕ} (hω : ∀ c ∈ cSetBdryMom t r' k, Y (foldedCircle c (radius k)) =
      X (foldedCircle c (radius k)) - X ρ₀ + g c)
    {s : ℂ} (hs : s ∈ Hbar) (hst : dist s (t : ℂ) + radius k < r')
    (hA : Tendsto (fun n => X (foldedCircle (dyadicRoundC n s) (radius k))) atTop
      (𝓝 (avgReg X k s))) :
    avgReg (ofFun h0 + Y) k s =
      ∫ u, h0 u ∂foldedCircle s (radius k) + avgReg X k s - X ρ₀ + g s := by
  have hr := radius_pos k
  have hmem := eventually_mem_cSetBdryMom hs hst
  have hg : Tendsto (fun n => g (dyadicRoundC n s)) atTop (𝓝 (g s)) := by
    have hcont := K3.continuousOn_of_harmonic_foldH hgh
    have hsK : s ∈ closedBall (t : ℂ) r' ∩ Hbar :=
      ⟨by rw [mem_closedBall]; linarith, hs⟩
    refine (hcont s hsK).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨RegClosure.tendsto_dyadicRoundC s, hmem.mono fun n hn => ⟨?_, hn.2.1⟩⟩)
    rw [mem_closedBall]; linarith [hn.2.2]
  have hlim : Tendsto (fun n => (ofFun h0 + Y) (foldedCircle (dyadicRoundC n s) (radius k)))
      atTop (𝓝 (∫ u, h0 u ∂foldedCircle s (radius k) + (avgReg X k s - X ρ₀ + g s))) := by
    refine Tendsto.congr' (hmem.mono fun n hn => ?_)
      ((tendsto_h0_dyadic_bdryMom hmc hEq hs hst).add ((hA.sub tendsto_const_nhds).add hg))
    simp only [Pi.add_apply, ofFun, hω _ hn]
  exact (hlim.limUnder_eq : avgReg (ofFun h0 + Y) k s = _).trans (by ring)

/-- The density of `bdryApprox` is measurable in the point. -/
theorem measurable_bdryDens_bdryMom (γ : ℝ) (x : FieldSample) (k : ℕ) :
    Measurable fun s : ℝ =>
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg x k (s : ℂ))) := by
  have hav : Measurable fun s : ℝ => avgReg x k (s : ℂ) :=
    (measurable_avgReg k).comp (measurable_const.prodMk Complex.measurable_ofReal)
  exact (measurable_const.mul (hav.const_mul _).exp).ennreal_ofReal

/-- **Pathwise comparison of the boundary masses on the coupling.** -/
theorem ae_bdryApprox_le_bdryMom {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    [IsProbabilityMeasure P₀] {Y X : Ω₀ → FieldSample} {g : Ω₀ → ℂ → ℝ} {t r' : ℝ}
    {ρ₀ : Measure ℂ} (hX : IsFreeGFFModConstH X P₀)
    (hgh : ∀ ω, InnerProductSpace.HarmonicOnNhd (fun z => g ω (foldH z)) (closedBall (t : ℂ) r'))
    (hrep : ∀ μ : Measure ℂ, IsAdmissibleH μ → μ (closedBall (t : ℂ) r')ᶜ = 0 →
      ∀ᵐ ω ∂P₀, Y ω μ = X ω μ - (μ Set.univ).toReal * X ω ρ₀ + ∫ z, g ω z ∂μ)
    {h0 mc : ℂ → ℝ} (hmc : Continuous mc) (hEq : EqOn h0 mc (closedBall (t : ℂ) r' ∩ Hbar))
    {η : ℝ} {n : ℕ} (hn : η + radius n < r') (γ R CH : ℝ)
    (hCH : ∀ k ≥ n, ∀ s ∈ Icc (t - η) (t + η),
      |∫ u, h0 u ∂foldedCircle (s : ℂ) (radius k)| ≤ CH)
    {W : Ω₀ → ℝ≥0∞}
    (hW : ∀ ω, ∀ s ∈ Icc (t - η) (t + η),
      ENNReal.ofReal (Real.exp (γ / 2 * (g ω s - X ω ρ₀ + X ω (foldedCircle 0 R)))) ≤ W ω) :
    ∀ᵐ ω ∂P₀, ∀ k ≥ n, bdryApprox γ (ofFun h0 + Y ω) k (Icc (t - η) (t + η)) ≤
      ENNReal.ofReal (Real.exp (|γ| / 2 * CH)) * W ω *
        bdryApprox γ (BdryExist.zField X R ω) k (Icc (t - η) (t + η)) := by
  have hA : ∀ᵐ ω ∂P₀, ∀ k, ∀ z ∈ Hbar,
      Tendsto (fun n => X ω (foldedCircle (dyadicRoundC n z) (radius k))) atTop
        (𝓝 (avgReg (X ω) k z)) :=
    ae_all_iff.2 fun k => (BdryExist.ae_avgReg_spec hX k).1
  filter_upwards [ae_rep_cSet_bdryMom hgh hrep, hA] with ω hω hAω k hk
  unfold bdryApprox
  rw [withDensity_apply _ measurableSet_Icc, withDensity_apply _ measurableSet_Icc,
    ← lintegral_const_mul'' _ (measurable_bdryDens_bdryMom γ _ k).aemeasurable]
  refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
  have hsH : (s : ℂ) ∈ Hbar := GaussTK.ofReal_mem_Hbar s
  have hdist : dist (s : ℂ) (t : ℂ) ≤ η := by
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hst : dist (s : ℂ) (t : ℂ) + radius k < r' := by
    have : radius k ≤ radius n := by
      unfold radius; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
    linarith
  rw [avgReg_mixed_eq_bdryMom (hgh ω) hmc hEq (hω k) hsH hst (hAω k _ hsH)]
  have hZ : avgReg (BdryExist.zField X R ω) k (s : ℂ) =
      avgReg (X ω) k (s : ℂ) + -X ω (foldedCircle 0 R) :=
    LocalRule.avgReg_addConst_of_tendsto ⟨_, hAω k _ hsH⟩ _
  rw [hZ]
  set H := ∫ u, h0 u ∂foldedCircle (s : ℂ) (radius k) with hH
  set a := avgReg (X ω) k (s : ℂ)
  set V := g ω (s : ℂ) - X ω ρ₀ + X ω (foldedCircle 0 R) with hV
  have e : radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * (H + a - X ω ρ₀ + g ω (s : ℂ))) =
      Real.exp (γ / 2 * H) * Real.exp (γ / 2 * V) *
        (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * (a + -X ω (foldedCircle 0 R)))) := by
    rw [hV, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
    ring_nf
  rw [e, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  refine mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    (hW ω s hs)) le_rfl
  have h1 := hCH k hk s hs
  have h2 : γ / 2 * H ≤ |γ / 2 * H| := le_abs_self _
  rw [abs_mul, abs_div, abs_two] at h2
  have h3 : |γ| / 2 * |H| ≤ |γ| / 2 * CH :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

end Prop16Asm

end QuantumZipper
