import QuantumZipper.Proofs.Section5.Prop16BdryMomLaw
import QuantumZipper.Proofs.Section5.Prop16BdryMomPath
import QuantumZipper.Proofs.Section5.Prop16BdryMomJensen
import QuantumZipper.Proofs.Section5.Prop16BdryL1Mom
import QuantumZipper.Proofs.Section5.Prop16ActReg
import QuantumZipper.Proofs.GMC.InnerMomentPalm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, node B′-MOM: the uniform moment bound near the free arc

`prop16BdryMomStmt_of_gauss : Prop16BdryMomGaussStmt → Prop16BdryMomStmt`.

Fix `t ∈ (a,b)`, `G = palmGap(t)`, a dyadic scale `2^{-n} < G/16`, the window
`K = [t − 2·2^{-n}, t + 2·2^{-n}]`, and exponents `1 < p < q < q' < min(2, 4/γ²)`.

1. **Coupling** (M7, `K3.mixedFreeCouplingHalfDisc_holds`; Sheffield, *Gaussian free fields for
   mathematicians*, PTRF 139 (2007), Thm 2.17, half-disc form): a mixed GFF `Y` and a free GFF `X`
   on one space with `Y = X − X(ρ₀) + ∫ g` near `t`, `g ∘ foldH` harmonic.
2. **Pathwise comparison** (`ae_bdryApprox_le_bdryMom`): `m_k^{h0+Y}(K) ≤ e^{|γ|C/2} W m_k^Z(K)`,
   `Z = X − X(fc(0,R))`, with `W = (4U)^{(q−p)/(pq)}` and `U = ∫ e^{λ V} d fc(t, G/2)`,
   `V = g − X(ρ₀) + X(fc(0,R))`, by the Poisson–Jensen bound
   (`ofReal_exp_le_poissonJensen_bdryMom`).
3. **Hölder** (`lintegral_mul_rpow_le_bdryMom`) with the free-field moment of order `q`
   (`GMCMoments.momentDyadic_of_innerMomentStmt`, `GMCMoments.innerMomentStmt_holds`) and the
   exponential moment `E U < ∞` (node `Prop16BdryMomGaussStmt`).
4. **Law transfer** (`lintegral_eq_of_isMixedGFF_bdryMom`, `bdryApprox_congr_bdryMom`): the
   masses of `h0 + X` and `h0 + Y` on `K` are the same functional of the field read along a
   countable admissible family of circles, whose laws agree.

This is the route of Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185
(2011) (arXiv:0808.1560), proof of Prop. 1.2 and §6 (moments/uniform integrability of the boundary
masses, transferred to other fields by absolute continuity/Markov decomposition), in the form
needed for the mixed field of Prop. 1.6 of Sheffield arXiv:1012.4797 (p. 25). The assembly and the
Poisson–Jensen treatment of the harmonic correction are our own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal Real

namespace QuantumZipper

namespace Prop16Asm

/-- Hölder's inequality in the form used for the moment transfer. -/
theorem lintegral_mul_rpow_le_bdryMom {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W M : Ω → ℝ≥0∞} (hW : AEMeasurable W P) (hM : AEMeasurable M P) {p q : ℝ} (hp : 1 < p)
    (hpq : p < q) :
    ∫⁻ ω, (W ω * M ω) ^ p ∂P ≤
      (∫⁻ ω, W ω ^ (p * q / (q - p)) ∂P) ^ ((q - p) / q) * (∫⁻ ω, M ω ^ q ∂P) ^ (p / q) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hqp : 0 < q - p := by linarith
  set r := q / (q - p) with hr
  set r' := q / p with hr'
  have hconj : r.HolderConjugate r' := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [hr, one_lt_div hqp]; linarith
    · rw [hr, hr', inv_div, inv_div]; field_simp; ring
  have e1 : ∀ ω, (W ω * M ω) ^ p = W ω ^ p * M ω ^ p := fun ω =>
    ENNReal.mul_rpow_of_nonneg _ _ hp0.le
  simp_rw [e1]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hconj (hW.pow_const p) (hM.pow_const p)
  simp only [Pi.mul_apply] at h
  refine h.trans (le_of_eq ?_)
  have e2 : ∀ ω, (W ω ^ p) ^ r = W ω ^ (p * q / (q - p)) := fun ω => by
    rw [← ENNReal.rpow_mul, hr, ← mul_div_assoc]
  have e3 : ∀ ω, (M ω ^ p) ^ r' = M ω ^ q := fun ω => by
    rw [← ENNReal.rpow_mul, hr', mul_div_cancel₀ _ hp0.ne']
  simp_rw [e2, e3]
  rw [hr, hr', one_div_div, one_div_div]

/-- `palmGap(t) ≤ t − a`. -/
theorem palmGap_le_sub_left_bdryMom {D : Set ℂ} {a b t : ℝ} (hDH : D ⊆ H) (ht : t ∈ Ioo a b) :
    palmGap D a b t ≤ t - a := by
  have hmem : (a : ℂ) ∈ palmOutside D a b := by
    refine ⟨show (0 : ℝ) ≤ (a : ℂ).im by simp, ?_⟩
    rintro (h | ⟨u, hu, hua⟩)
    · have : 0 < ((a : ℂ)).im := hDH h
      simp at this
    · have : u = a := Complex.ofReal_injective hua
      exact (lt_irrefl a) (this ▸ hu.1)
  refine (infDist_le_dist_of_mem hmem).trans (le_of_eq ?_)
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith [ht.1])]

/-- `palmGap(t) ≤ b − t`. -/
theorem palmGap_le_sub_right_bdryMom {D : Set ℂ} {a b t : ℝ} (hDH : D ⊆ H) (ht : t ∈ Ioo a b) :
    palmGap D a b t ≤ b - t := by
  have hmem : (b : ℂ) ∈ palmOutside D a b := by
    refine ⟨show (0 : ℝ) ≤ (b : ℂ).im by simp, ?_⟩
    rintro (h | ⟨u, hu, hub⟩)
    · have : 0 < ((b : ℂ)).im := hDH h
      simp at this
    · have : u = b := Complex.ofReal_injective hub
      exact (lt_irrefl b) (this ▸ hu.2)
  refine (infDist_le_dist_of_mem hmem).trans (le_of_eq ?_)
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_neg (by linarith [ht.2])]
  ring

/-- Points of the window are well inside the coupling disc at every scale `k ≥ n`. -/
theorem dist_add_radius_lt_bdryMom {t η r' : ℝ} {n k : ℕ} (hk : n ≤ k)
    (hn : η + radius n < r') {s : ℝ} (hs : s ∈ Icc (t - η) (t + η)) :
    dist (s : ℂ) (t : ℂ) + radius k < r' := by
  have hdist : dist (s : ℂ) (t : ℂ) ≤ η := by
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have : radius k ≤ radius n := by
    unfold radius; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  linarith

/-- **Node B′-MOM-GAUSS (exponential moment of the harmonic correction on the coupling).** On
the M7 coupling, `ω ↦ ∫ e^{λ V_ω} d fc(t, s0)` (`V = g − X(ρ₀) + X(fc(0,R))`) is measurable and
integrable. Proof in `Prop16BdryMomGauss.lean` (Poisson reproduction, Gaussian bounds). -/
def Prop16BdryMomGaussStmt : Prop :=
  ∀ {D : Set ℂ} {c d t r r' s0 s1 R : ℝ}, K3.Prop16Geometry D c d → t ∈ Set.Ioo c d →
    0 < s0 → s0 < s1 → s1 ≤ r' → r' < r → Metric.ball (t : ℂ) r ∩ H ⊆ D → 0 < R →
    ∀ {ρ₀ : Measure ℂ} {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
      [IsProbabilityMeasure P₀] {Y Xf : Ω₀ → FieldSample} {g : Ω₀ → ℂ → ℝ},
      IsMixedGFF D (realSet (Set.Icc c d)) Y P₀ → IsFreeGFFModConstH Xf P₀ →
      (∀ ω, InnerProductSpace.HarmonicOnNhd (fun z => g ω (foldH z))
        (Metric.closedBall (t : ℂ) r')) →
      (∀ z, Measurable fun ω => g ω z) →
      (∀ μ : Measure ℂ, IsAdmissibleH μ → μ (Metric.closedBall (t : ℂ) r')ᶜ = 0 →
        ∀ᵐ ω ∂P₀, Y ω μ = Xf ω μ - (μ Set.univ).toReal * Xf ω ρ₀ + ∫ z, g ω z ∂μ) →
      ∀ lam : ℝ, Measurable (fun ω => ∫⁻ w, ENNReal.ofReal (Real.exp (lam * (g ω w - Xf ω ρ₀ +
          Xf ω (foldedCircle 0 R)))) ∂foldedCircle (t : ℂ) s0) ∧
        ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∫⁻ ω, ∫⁻ w, ENNReal.ofReal (Real.exp (lam * (g ω w - Xf ω ρ₀ +
          Xf ω (foldedCircle 0 R)))) ∂foldedCircle (t : ℂ) s0 ∂P₀ ≤ M

/-- **Node B′-MOM from the exponential moment of the harmonic correction.** -/
theorem prop16BdryMomStmt_of_gauss (hGs : Prop16BdryMomGaussStmt) : Prop16BdryMomStmt := by
  intro γ D c d a b h0 Ω _ P X hH t ht
  obtain ⟨⟨hγ, hγ2, hgeom, -, hca, hbd, hh0, hP, hX, -, -⟩, -, -⟩ := hH
  have := hP
  obtain ⟨-, -, -, hDH, -, -, hhd⟩ := id hgeom
  set G := palmGap D a b t with hGdef
  have hG0 : 0 < G := palmGap_pos hDH hhd hca hbd ht
  have hGa : G ≤ t - a := palmGap_le_sub_left_bdryMom hDH ht
  have hGb : G ≤ b - t := palmGap_le_sub_right_bdryMom hDH ht
  obtain ⟨n, hn⟩ : ∃ n : ℕ, radius n < G / 16 :=
    exists_pow_lt_of_lt_one (show 0 < G / 16 by positivity) (show (2 : ℝ)⁻¹ < 1 by norm_num)
  have hrn := radius_pos n
  set η := 2 * radius n with hηdef
  set r' := 3 * G / 4 with hr'def
  set s0 := G / 2 with hs0def
  set R := |t| + 4 with hRdef
  have hR : 0 < R := by positivity
  have hηr' : η + radius n < r' := by rw [hηdef, hr'def]; linarith
  -- exponents
  set Q := min 2 (4 / γ ^ 2) with hQ
  have hγ4 : 1 < 4 / γ ^ 2 := by
    rw [one_lt_div (by positivity)]; nlinarith
  have hQ1 : 1 < Q := lt_min (by norm_num) hγ4
  set q' := (1 + Q) / 2 with hq'def
  set q := (1 + q') / 2 with hqdef
  set p := (1 + q) / 2 with hpdef
  have hq'Q : q' < Q := by rw [hq'def]; linarith
  have hq'2 : q' ≤ 2 := hq'Q.le.trans (min_le_left _ _)
  have hq'γ : q' < 4 / γ ^ 2 := hq'Q.trans_le (min_le_right _ _)
  have h1q' : 1 < q' := by rw [hq'def]; linarith
  have hqq' : q < q' := by rw [hqdef]; linarith
  have h1q : 1 < q := by rw [hqdef]; linarith
  have hpq : p < q := by rw [hpdef]; linarith
  have hp1 : 1 < p := by rw [hpdef]; linarith
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hqp : q - p ≠ 0 := (sub_pos.2 hpq).ne'
  -- the M7 coupling at `t`
  have htcd : t ∈ Ioo c d := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨ρ₀, hρadm, hρ1, hρB⟩ := exists_rho0_far t hG0
  obtain ⟨Ω₀, _, P₀, Y, Xf, g, E', _, Ξ, hP₀, hY, hXf, hΞ, -, hgh, hgmeas, hrep⟩ :=
    K3.mixedFreeCouplingHalfDisc_holds D c d t G r' ρ₀ hgeom htcd (by positivity)
      (by rw [hr'def]; linarith) (ball_inter_H_subset_D le_rfl) hρadm hρ1 hρB
  have := hP₀
  have hle : MeasurableSpace.comap Ξ inferInstance ⊔ K3.outsideSigma Xf t G ≤
      ‹MeasurableSpace Ω₀› :=
    sup_le hΞ.comap_le
      (iSup_le fun _ => ((hXf.measurable_coord _).sub (hXf.measurable_coord _)).comap_le)
  have hgm : ∀ z, Measurable fun ω => g ω z := fun z => (hgmeas z).mono hle le_rfl
  -- the exponential moment (node GAUSS)
  set lam := γ * p * q / (2 * (q - p)) with hlam
  obtain ⟨hUm, M, hMtop, hMle⟩ := hGs (s0 := s0) (s1 := r') (R := R) hgeom htcd
    (by rw [hs0def]; positivity) (by rw [hs0def, hr'def]; linarith) le_rfl
    (by rw [hr'def]; linarith) (ball_inter_H_subset_D le_rfl) hR hY hXf hgh hgm hrep lam
  set U : Ω₀ → ℝ≥0∞ := fun ω => ∫⁻ w, ENNReal.ofReal (Real.exp (lam * (g ω w - Xf ω ρ₀ +
    Xf ω (foldedCircle 0 R)))) ∂foldedCircle (t : ℂ) s0 with hUdef
  set e := (q - p) / (p * q) with hedef
  have he0 : 0 ≤ e := by rw [hedef]; exact div_nonneg (by linarith) (by positivity)
  set W : Ω₀ → ℝ≥0∞ := fun ω => (4 * U ω) ^ e with hWdef
  have hW : ∀ ω, ∀ s ∈ Icc (t - η) (t + η),
      ENNReal.ofReal (Real.exp (γ / 2 * (g ω s - Xf ω ρ₀ + Xf ω (foldedCircle 0 R)))) ≤
        W ω := by
    intro ω s hs
    have hharm : InnerProductSpace.HarmonicOnNhd
        (fun z => (fun z => g ω z - Xf ω ρ₀ + Xf ω (foldedCircle 0 R)) (foldH z))
        (closedBall (t : ℂ) s0) := fun x hx =>
      ((hgh ω x (closedBall_subset_closedBall (by rw [hs0def, hr'def]; linarith) hx)).sub
        (InnerProductSpace.harmonicAt_const _)).add (InnerProductSpace.harmonicAt_const _)
    have hdist : ‖(s : ℂ) - (t : ℂ)‖ ≤ s0 / 2 := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le, hs0def]
      constructor <;> linarith [hs.1, hs.2]
    have hJ := ofReal_exp_le_poissonJensen_bdryMom
      (F := fun z => g ω z - Xf ω ρ₀ + Xf ω (foldedCircle 0 R)) (by rw [hs0def]; positivity)
      hharm lam
      (GaussTK.ofReal_mem_Hbar s) hdist
    have e1 : ENNReal.ofReal (Real.exp (γ / 2 * (g ω s - Xf ω ρ₀ + Xf ω (foldedCircle 0 R)))) =
        ENNReal.ofReal (Real.exp (lam * (g ω s - Xf ω ρ₀ + Xf ω (foldedCircle 0 R)))) ^ e := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le he0, ← Real.exp_mul]
      congr 2
      rw [hlam, hedef]
      field_simp
    rw [e1]
    exact ENNReal.rpow_le_rpow hJ he0
  -- the `h0` part
  have hKV : closedBall (t : ℂ) r' ∩ Hbar ⊆ D ∪ realSet (Ioo a b) := fun u hu =>
    mem_union_of_dist_lt_palmGap hu.2 (lt_of_le_of_lt hu.1 (by rw [hr'def]; linarith))
  obtain ⟨mc, hmc, hmcEq⟩ := exists_continuous_eqOn (isClosed_closedBall.inter isClosed_Hbar)
    (hh0.mono hKV)
  obtain ⟨B0, hB0⟩ := ((isCompact_closedBall (t : ℂ) r').inter_right isClosed_Hbar).exists_bound_of_continuousOn
    hmc.continuousOn
  have hCH : ∀ k ≥ n, ∀ s ∈ Icc (t - η) (t + η),
      |∫ u, h0 u ∂foldedCircle (s : ℂ) (radius k)| ≤ B0 := by
    intro k hk s hs
    have hst := dist_add_radius_lt_bdryMom hk hηr' hs
    rw [integral_h0_eq_mc_bdryMom hmcEq.symm (GaussTK.ofReal_mem_Hbar s) hst,
      ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := B0) ?_).trans (by simp)
    filter_upwards [Prop16Area.G.ae_fc_mem_ball_inter (GaussTK.ofReal_mem_Hbar s)
      (radius_pos k)] with u hu
    refine hB0 u ⟨?_, hu.2⟩
    have h1 : dist u (s : ℂ) ≤ radius k := hu.1
    rw [mem_closedBall]; linarith [dist_triangle u (s : ℂ) (t : ℂ)]
  -- the pathwise comparison
  have hpath := ae_bdryApprox_le_bdryMom hXf hgh hrep hmc hmcEq.symm hηr' γ R B0 hCH hW
  set K := Icc (t - η) (t + η) with hKdef
  set cH := ENNReal.ofReal (Real.exp (|γ| / 2 * B0)) with hcH
  -- the free-field moment of order `q`
  obtain ⟨C, -, hCmom⟩ := GMCMoments.momentDyadic_of_innerMomentStmt hγ hγ2 hR h1q.le hqq'
    (GMCMoments.innerMomentStmt_holds hγ hγ2 h1q' hq'2 hq'γ) hXf
  set B2 := ENNReal.ofReal (C * 2 ^ (-(n : ℝ) * q * (1 + γ ^ 2 / 4) + n * (γ ^ 2 * q ^ 2 / 4)))
    with hB2def
  have hKbI : K = FracMom.bI t (4 * radius n) := by
    rw [hKdef, FracMom.bI, hηdef]; congr 1 <;> ring
  have hmZ : ∀ k, Measurable fun ω => bdryApprox γ (BdryExist.zField Xf R ω) k K := fun k =>
    (Measure.measurable_coe measurableSet_Icc).comp
      ((measurable_bdryApprox γ k).comp (BdryExist.measurable_zField hXf R))
  have hB2 : ∀ k ≥ n, ∫⁻ ω, bdryApprox γ (BdryExist.zField Xf R ω) k K ^ q ∂P₀ ≤ B2 := by
    intro k hk
    have hrn1 : radius n ≤ 1 := BdryExist.radius_le_one n
    have hT := (hCmom n t (by rw [hRdef]; linarith)).1
    refine le_trans (lintegral_mono fun ω => ENNReal.rpow_le_rpow ?_ hq0.le) hT
    rw [hKbI]
    refine le_iSup_of_le (k - n) ?_
    rw [Nat.add_sub_cancel' hk]
  have hU4 : ∫⁻ ω, W ω ^ (p * q / (q - p)) ∂P₀ ≤ 4 * M := by
    have e4 : ∀ ω, W ω ^ (p * q / (q - p)) = 4 * U ω := fun ω => by
      rw [hWdef, ← ENNReal.rpow_mul,
        show e * (p * q / (q - p)) = 1 by
          rw [hedef]; field_simp,
        ENNReal.rpow_one]
    simp_rw [e4]
    rw [lintegral_const_mul _ hUm]
    gcongr
  set A := cH ^ p * ((4 * M) ^ ((q - p) / q) * B2 ^ (p / q)) with hAdef
  have hAtop : A ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (div_nonneg (by linarith) hq0.le)
        (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hMtop))
        (ENNReal.rpow_ne_top_of_nonneg (div_nonneg hp0.le hq0.le) ENNReal.ofReal_ne_top))
  have hcoup : ∀ k ≥ n, ∫⁻ ω, bdryApprox γ (ofFun h0 + Y ω) k K ^ p ∂P₀ ≤ A := by
    intro k hk
    have hWm : AEMeasurable W P₀ := ((hUm.const_mul 4).pow_const e).aemeasurable
    calc ∫⁻ ω, bdryApprox γ (ofFun h0 + Y ω) k K ^ p ∂P₀
        ≤ ∫⁻ ω, cH ^ p * (W ω * bdryApprox γ (BdryExist.zField Xf R ω) k K) ^ p ∂P₀ := by
          refine lintegral_mono_ae (hpath.mono fun ω hω => ?_)
          rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← mul_assoc]
          exact ENNReal.rpow_le_rpow (hω k hk) hp0.le
      _ = cH ^ p * ∫⁻ ω, (W ω * bdryApprox γ (BdryExist.zField Xf R ω) k K) ^ p ∂P₀ :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)
      _ ≤ cH ^ p * ((∫⁻ ω, W ω ^ (p * q / (q - p)) ∂P₀) ^ ((q - p) / q) *
            (∫⁻ ω, bdryApprox γ (BdryExist.zField Xf R ω) k K ^ q ∂P₀) ^ (p / q)) :=
          by gcongr; exact lintegral_mul_rpow_le_bdryMom hWm (hmZ k).aemeasurable hp1 hpq
      _ ≤ A := by
          refine mul_le_mul' le_rfl (mul_le_mul' ?_ ?_)
          · exact ENNReal.rpow_le_rpow hU4 (div_nonneg (by linarith) hq0.le)
          · exact ENNReal.rpow_le_rpow (hB2 k hk) (div_nonneg hp0.le hq0.le)
  -- the law transfer
  obtain ⟨Wo, hWo, hWV⟩ := locGood_exists_open hgeom hca hbd
  have htrans : ∀ k ≥ n, ∫⁻ ω, bdryApprox γ (ofFun h0 + X ω) k K ^ p ∂P =
      ∫⁻ ω, bdryApprox γ (ofFun h0 + Y ω) k K ^ p ∂P₀ := by
    intro k hk
    refine lintegral_eq_of_isMixedGFF_bdryMom (F := fun x => bdryApprox γ (ofFun h0 + x) k K ^ p)
      hX hY ((fun c => foldedCircle c (radius k)) '' cSetBdryMom t r' k)
      ((countable_cSetBdryMom t r' k).image _) ?_ ?_ ?_
    · rintro _ ⟨c', hc', rfl⟩
      exact locGood_isAdmissible_circle hgeom hca hbd hWo hWV hc'.2.1 (radius_pos k)
        (closedBall_subset_of_gap hWV (by linarith [hc'.2.2]))
    · exact ((Measure.measurable_coe measurableSet_Icc).comp ((measurable_bdryApprox γ k).comp
        (measurable_pi_iff.2 fun μ => measurable_const.add (measurable_pi_apply μ)))).pow_const p
    · intro x x' hxx
      rw [bdryApprox_congr_bdryMom γ h0 k measurableSet_Icc (Cs := cSetBdryMom t r' k)
        (fun s hs => eventually_mem_cSetBdryMom (GaussTK.ofReal_mem_Hbar s)
          (dist_add_radius_lt_bdryMom hk hηr' hs))
        (fun c' hc' => hxx _ ⟨c', hc', rfl⟩)]
  refine ⟨η, by positivity, by linarith, by linarith, n, p, hp1, A, hAtop, fun k hk => ?_⟩
  rw [htrans k hk]
  exact hcoup k hk

end Prop16Asm

end QuantumZipper
