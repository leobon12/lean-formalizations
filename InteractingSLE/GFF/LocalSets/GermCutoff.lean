import InteractingSLE.GFF.LocalSets.MarkovNesting
import QuantumZipper.Proofs.GFF.K3.BubbleCutoff
import QuantumZipper.Proofs.GFF.K3.MixedM7D2

/-!
# The germ lemma: `h − G_W h` is determined by `h` near `ℍ ∖ W`

Specification §3.2, p. 50 ("The random projection `Q_{C_n} h` is measurable from `A` and the field
germ on `C_n`, and therefore from `A` and the field in every sufficiently slightly larger
neighborhood of `C_n`"; Proposition 3.2 identifies the sigma-algebra of `Q_C h` with the germ of
`h` on `C`). Here only the inclusion used in Lemma 3.6 is proved, for an open `W ⊆ ℍ` and an
open `O` that contains the closure of `ℍ ∖ W` relative to a smooth cutoff `χ` with compact
support in `W` (`1 − χ` supported in `O`): the projection `h − G_W h` onto `H^⊥(W)` is a function
of `(h(ψ))_{supp ψ ⊆ O}` (`exists_measurable_markovCompl_germ`).

Own proof (the obstruction recorded by PROVE-LS-A for Proposition 3.2 in general concerns
cutoffs near `∂ℍ`; here `∇χ` has compact support in `ℍ`). With `g_n ∈ C_c^∞(W)`,
`∇g_n → covVec_W Φ` and `Δ̃g = −Δg/2π`:
`(h − G_W h)(Φ) = lim h(Φ − Δ̃g_n) = lim [h((1 − χ)(Φ − Δ̃g_n)) + h(χ(Φ − Δ̃g_n))]`.
The first term only sees `h` on `O`. For the second, by the variance formula
`σ²_ℍ(ψ) = sup_f (∫ψf)²/E(f)` and Green's identity, `∫ χ(Φ − Δ̃g_n) f = ⟨covVec_W Φ − ∇g_n, ∇(χ f)⟩`,
and `E(χ f) ≤ K E(f)` by the vertical Poincaré inequality on a ball containing `supp ∇χ`
(QuantumZipper `K3.integral_sq_ball_le`), so `E|h(χ(Φ − Δ̃g_n))|² ≤ K ‖covVec_W Φ − ∇g_n‖² → 0`.

## Main results

* `energyC_mul_le` : `E(χ f) ≤ (2 + 4L²R(|Im p| + R)) E(f)`;
* `zeroGFFTestCov_smulTest_le` : the variance bound for the cut-off residual;
* `fieldSigmaOn`, `exists_measurable_markovCompl_germ` : the germ lemma.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper QuantumZipper.K3 QuantumZipper.Thm11Asm LQGMetric LQGMetric.MarkovZB

/-- **Energy of a cut-off function** (vertical Poincaré): for a smooth `χ` with `|χ| ≤ 1`,
`‖∇χ‖ ≤ L` and `∇χ = 0` off a ball `B(p, R)`, and `f ∈ C_c^∞(ℍ)`,
`E(χ f) ≤ (2 + 4 L² R (|Im p| + R)) E(f)`. -/
theorem energyC_mul_le {χ : ℂ → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχ1 : ∀ z, |χ z| ≤ 1) {L : ℝ} (hL : ∀ z, ‖fderiv ℝ χ z‖ ≤ L) {p : ℂ} {R : ℝ} (hR : 0 < R)
    (hχK : ∀ z, z ∉ Metric.ball p R → fderiv ℝ χ z = 0) {f : ℂ → ℝ} (hf : f ∈ zeroSpace H) :
    energyC (fun z => χ z * f z) ≤ (2 + 4 * L ^ 2 * R * (|p.im| + R)) * energyC f := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hf1 : ContDiff ℝ 1 f := hf.1.of_le (by exact_mod_cast le_top)
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hfd : Differentiable ℝ f := hf1.differentiable one_ne_zero
  have hf0 : ∀ z : ℂ, z.im ≤ 0 → f z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h' => by
      have := hf.2.2 h'
      simp only [H, mem_ofPred_eq] at this
      linarith
  have hDf : Continuous fun z => ‖fderiv ℝ f z‖ ^ 2 :=
    ((hf1.continuous_fderiv one_ne_zero).norm).pow 2
  have hDfc : HasCompactSupport fun z => ‖fderiv ℝ f z‖ ^ 2 :=
    (hf.2.1.fderiv (𝕜 := ℝ)).norm.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
  have iDf : Integrable (fun z => ‖fderiv ℝ f z‖ ^ 2) := hDf.integrable_of_hasCompactSupport hDfc
  have hfc : Continuous f := hf1.continuous
  have hfsq : HasCompactSupport (fun z => f z ^ 2) := by
    have := hf.2.1.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
    exact this
  have ifsq : Integrable (fun z => f z ^ 2) := (hfc.pow 2).integrable_of_hasCompactSupport hfsq
  have iball : IntegrableOn (fun z => f z ^ 2) (Metric.ball p R) := ifsq.integrableOn
  have hpt : ∀ z, ‖fderiv ℝ (fun z => χ z * f z) z‖ ^ 2 ≤
      2 * ‖fderiv ℝ f z‖ ^ 2 + 2 * L ^ 2 * (Metric.ball p R).indicator (fun z => f z ^ 2) z := by
    intro z
    rw [fderiv_fun_mul (hχd z) (hfd z)]
    have h1 : ‖χ z • fderiv ℝ f z + f z • fderiv ℝ χ z‖ ≤
        ‖fderiv ℝ f z‖ + |f z| * ‖fderiv ℝ χ z‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hχ1 z))
      · rw [norm_smul, Real.norm_eq_abs]
    by_cases hz : z ∈ Metric.ball p R
    · rw [indicator_of_mem hz]
      have h2 : |f z| * ‖fderiv ℝ χ z‖ ≤ |f z| * L := mul_le_mul_of_nonneg_left (hL z) (abs_nonneg _)
      have h3 := h1.trans (add_le_add le_rfl h2)
      have h4 : (‖fderiv ℝ f z‖ + |f z| * L) ^ 2 ≤ 2 * ‖fderiv ℝ f z‖ ^ 2 + 2 * L ^ 2 * f z ^ 2 := by
        nlinarith [sq_nonneg (‖fderiv ℝ f z‖ - |f z| * L), sq_abs (f z)]
      calc ‖χ z • fderiv ℝ f z + f z • fderiv ℝ χ z‖ ^ 2
          ≤ (‖fderiv ℝ f z‖ + |f z| * L) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h3 2
        _ ≤ _ := h4
    · rw [indicator_of_notMem hz, hχK z hz, smul_zero, add_zero, norm_smul, Real.norm_eq_abs]
      have := hχ1 z
      have h5 : (|χ z| * ‖fderiv ℝ f z‖) ^ 2 ≤ ‖fderiv ℝ f z‖ ^ 2 := by
        rw [mul_pow]
        exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith [abs_nonneg (χ z)])
      nlinarith [sq_nonneg ‖fderiv ℝ f z‖]
  have hPoinc := integral_sq_ball_le hf1 hf.2.1 hf0 p hR
  have iind : Integrable ((Metric.ball p R).indicator fun z => f z ^ 2) :=
    iball.integrable_indicator measurableSet_ball
  have hmono : ∫ z, ‖fderiv ℝ (fun z => χ z * f z) z‖ ^ 2 ≤
      ∫ z, (2 * ‖fderiv ℝ f z‖ ^ 2 + 2 * L ^ 2 * (Metric.ball p R).indicator (fun z => f z ^ 2) z) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _)
      ((iDf.const_mul 2).add (iind.const_mul _)) (Eventually.of_forall hpt)
  rw [integral_add (iDf.const_mul 2) (iind.const_mul _), integral_const_mul, integral_const_mul,
    integral_indicator measurableSet_ball] at hmono
  unfold energyC
  have hpi : 0 < (2 * Real.pi)⁻¹ := by positivity
  have hI0 : 0 ≤ ∫ z, ‖fderiv ℝ f z‖ ^ 2 := integral_nonneg fun z => sq_nonneg _
  calc (2 * Real.pi)⁻¹ * ∫ z, ‖fderiv ℝ (fun z => χ z * f z) z‖ ^ 2
      ≤ (2 * Real.pi)⁻¹ * (2 * (∫ z, ‖fderiv ℝ f z‖ ^ 2) +
          2 * L ^ 2 * (∫ z in Metric.ball p R, f z ^ 2)) := mul_le_mul_of_nonneg_left hmono hpi.le
    _ ≤ (2 * Real.pi)⁻¹ * (2 * (∫ z, ‖fderiv ℝ f z‖ ^ 2) +
          2 * L ^ 2 * (2 * R * (|p.im| + R) * (∫ z, ‖fderiv ℝ f z‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hPoinc
          (by positivity : (0 : ℝ) ≤ 2 * L ^ 2))) hpi.le
    _ = (2 + 4 * L ^ 2 * R * (|p.im| + R)) * ((2 * Real.pi)⁻¹ * ∫ z, ‖fderiv ℝ f z‖ ^ 2) := by
        ring

/-- `χ ψ` for a smooth `χ` and a test function `ψ` on `ℍ`. -/
def smulTest (χ : ℂ → ℝ) (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (ψ : TestOn upperHalfPlaneOpens) : TestOn upperHalfPlaneOpens where
  toFun z := χ z * ψ z
  contDiff' := hχ.mul ψ.contDiff
  hasCompactSupport' := ψ.hasCompactSupport.mul_left
  tsupport_subset' := (tsupport_mul_subset_right).trans ψ.tsupport_subset

@[simp] lemma smulTest_apply (χ : ℂ → ℝ) (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (ψ : TestOn upperHalfPlaneOpens) (z : ℂ) : smulTest χ hχ ψ z = χ z * ψ z := rfl

lemma norm_gradFeat_sq_eq_energyC {V : Set ℂ} {f : ℂ → ℝ} (hf : f ∈ zeroSpace V) :
    ‖gradFeat V f‖ ^ 2 = energyC f := by
  rw [norm_gradFeat_sq ((isDNSpace_zeroSpace V).smooth f hf) ((isDNSpace_zeroSpace V).energy f hf),
    energy_eq_of_tsupport_subset hf.2.2]
  rfl

/-- **Variance of a cut-off residual.** For `g ∈ C_c^∞(W)` and a cutoff `χ` supported in `W`,
`σ²_ℍ(χ(Φ − Δ̃g)) ≤ K ‖covVec_W Φ − ∇g‖²` with the constant `K` of `energyC_mul_le`. -/
theorem zeroGFFTestCov_smulTest_le {W : Opens ℂ} (hW : (W : Set ℂ) ⊆ H) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχ1 : ∀ z, |χ z| ≤ 1) {L : ℝ}
    (hL : ∀ z, ‖fderiv ℝ χ z‖ ≤ L) {p : ℂ} {R : ℝ} (hR : 0 < R)
    (hχK : ∀ z, z ∉ Metric.ball p R → fderiv ℝ χ z = 0) (hχW : tsupport χ ⊆ W)
    (Φ : TestOn upperHalfPlaneOpens) (g : zsSub (W : Set ℂ)) :
    zeroGFFTestCov H (smulTest χ hχ (Φ - lapTest W g)) (smulTest χ hχ (Φ - lapTest W g)) ≤
      (2 + 4 * L ^ 2 * R * (|p.im| + R)) * ‖covVec W Φ - gradFeat W g.1‖ ^ 2 := by
  set K := 2 + 4 * L ^ 2 * R * (|p.im| + R) with hK
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hK0 : 0 ≤ K := by positivity
  set b := smulTest χ hχ (Φ - lapTest W g)
  have hWle : W ≤ upperHalfPlaneOpens := hW
  by_cases hne : (W : Set ℂ).Nonempty
  · have hpos := exists_pos_energy_zeroSpace_m7d W.isOpen hne
    have hkW : ∀ f ∈ zeroSpace H, (fun z => χ z * f z) ∈ zeroSpace W := fun f hf =>
      ⟨hχ.mul hf.1, hf.2.1.mul_left, (tsupport_mul_subset_left).trans hχW⟩
    have hpair : ∀ f ∈ zeroSpace H, ∫ z, b z * f z =
        ⟪covVec W Φ - gradFeat W g.1, gradFeat W (fun z => χ z * f z)⟫ := by
      intro f hf
      have hk := hkW f hf
      have e1 : ⟪covVec W Φ, gradFeat W (fun z => χ z * f z)⟫ =
          ∫ z in (W : Set ℂ), Φ z * (χ z * f z) :=
        inner_covVec_gradFeat W.isOpen hW (toTestFunH Φ) hpos hk
      rw [inner_sub_left, e1, inner_gradFeat_gradFeat W.isOpen hW hpos g.2 hk]
      have hint1 : ∫ z in (W : Set ℂ), Φ z * (χ z * f z) = ∫ z, Φ z * (χ z * f z) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
          rw [image_eq_zero_of_notMem_tsupport (f := fun z => χ z * f z) fun h' => hz (hk.2.2 h'),
            mul_zero]
      have hlap : ∀ z, cmTest (zsTest g.2) z = lapTest W g z := fun z => by
        rw [coe_lapTest hWle]
      rw [hint1]
      have hc1 : Integrable fun z => Φ z * (χ z * f z) :=
        (Φ.continuous.mul (hχ.continuous.mul hf.1.continuous)).integrable_of_hasCompactSupport
          (Φ.hasCompactSupport.mul_right)
      have hc2 : Integrable fun z => (χ z * f z) * cmTest (zsTest g.2) z :=
        ((hχ.continuous.mul hf.1.continuous).mul (cmTest (zsTest g.2)).continuous)
          |>.integrable_of_hasCompactSupport (hf.2.1.mul_left.mul_right)
      rw [← integral_sub hc1 hc2]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [b, smulTest_apply, hlap, FunLike.coe_sub, Pi.sub_apply]
      ring
    have hle : ENNReal.ofReal (zeroGFFTestCov H b b) ≤
        ENNReal.ofReal (K * ‖covVec W Φ - gradFeat W g.1‖ ^ 2) := by
      rw [ofReal_zeroGFFTestCov_eq_iSup isOpen_H subset_rfl b]
      refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_
      obtain ⟨hfH, hE⟩ := hf
      rw [div_le_iff₀ hE, hpair f hfH]
      have hk := hkW f hfH
      have hcs := abs_real_inner_le_norm (covVec W Φ - gradFeat W g.1)
        (gradFeat W (fun z => χ z * f z))
      have hnk : ‖gradFeat W (fun z => χ z * f z)‖ ^ 2 ≤ K * energyC f := by
        rw [norm_gradFeat_sq_eq_energyC hk]
        exact energyC_mul_le hχ hχ1 hL hR hχK hfH
      calc ⟪covVec W Φ - gradFeat W g.1, gradFeat W (fun z => χ z * f z)⟫ ^ 2
          = |⟪covVec W Φ - gradFeat W g.1, gradFeat W (fun z => χ z * f z)⟫| ^ 2 := (sq_abs _).symm
        _ ≤ (‖covVec W Φ - gradFeat W g.1‖ * ‖gradFeat W (fun z => χ z * f z)‖) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hcs 2
        _ = ‖covVec W Φ - gradFeat W g.1‖ ^ 2 * ‖gradFeat W (fun z => χ z * f z)‖ ^ 2 := mul_pow _ _ _
        _ ≤ ‖covVec W Φ - gradFeat W g.1‖ ^ 2 * (K * energyC f) :=
            mul_le_mul_of_nonneg_left hnk (sq_nonneg _)
        _ = K * ‖covVec W Φ - gradFeat W g.1‖ ^ 2 * energyC f := by ring
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle
  · have hχ0 : ∀ z, χ z = 0 := fun z => image_eq_zero_of_notMem_tsupport fun h' =>
      hne ⟨z, hχW h'⟩
    have hb0 : b = 0 := by
      ext z
      simp [b, hχ0]
    rw [hb0, show ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = 0 from rfl,
      GFF.zeroGFFTestCov_zero_zero]
    positivity

section GermLemma

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The σ-algebra of the restriction of the random distribution `h` to the set `O`: generated by
the pairings `h(ψ)` with `supp ψ ⊆ O`. -/
@[instance_reducible]
def fieldSigmaOn (h : Ω → DistOn upperHalfPlaneOpens) (O : Set ℂ) : MeasurableSpace Ω :=
  ⨆ (ψ : TestOn upperHalfPlaneOpens) (_ : tsupport ψ ⊆ O),
    MeasurableSpace.comap (fun ω => h ω ψ) inferInstance

omit mΩ in
theorem measurable_fieldSigmaOn_apply (h : Ω → DistOn upperHalfPlaneOpens) {O : Set ℂ}
    {ψ : TestOn upperHalfPlaneOpens} (hψ : tsupport ψ ⊆ O) :
    Measurable[fieldSigmaOn h O] fun ω => h ω ψ :=
  Measurable.of_comap_le (le_iSup₂ (f := fun (ψ : TestOn upperHalfPlaneOpens)
    (_ : tsupport ψ ⊆ O) => MeasurableSpace.comap (fun ω => h ω ψ) inferInstance) ψ hψ)

theorem fieldSigmaOn_le {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (O : Set ℂ) :
    fieldSigmaOn h O ≤ mΩ :=
  iSup₂_le fun ψ _ => ((measurable_distOn_apply ψ).comp hh).comap_le

/-- **The germ lemma** (the direction of Proposition 3.2 used in Lemma 3.6). Let `h = G_W h + (h −
G_W h)` be the Markov decomposition on an open `W ⊆ ℍ`, and let `χ` be a smooth `[0,1]`-valued
cutoff with compact support in `W` such that `1 − χ` is supported (inside `ℍ`) in the open set
`O`. Then the projection `h − G_W h` onto `H^⊥(W)` is a function of the restriction of `h` to `O`.
Proof: with `g_n ∈ C_c^∞(W)` approximating the Gram vector of `G_W h(Φ)`,
`(h − G_W h)(Φ) ≈ h(Φ − Δ̃g_n) = h((1 − χ)(Φ − Δ̃g_n)) + h(χ(Φ − Δ̃g_n))`; the first term only sees
`h` on `O` and the second tends to `0` in `L²` (`zeroGFFTestCov_smulTest_le`). -/
theorem exists_measurable_markovCompl_germ {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {W : Opens ℂ} (hW : (W : Set ℂ) ⊆ H)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hd : GFF.IsMarkovDecomposition W upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    {O : Set ℂ} {χ : ℂ → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχ01 : ∀ z, χ z ∈ Icc (0 : ℝ) 1) (hχc : HasCompactSupport χ) (hχW : tsupport χ ⊆ W)
    (hχO : tsupport (fun z => 1 - χ z) ∩ H ⊆ O) (Φ : TestOn upperHalfPlaneOpens) :
    ∃ Z : Ω → ℝ, Measurable[fieldSigmaOn h O] Z ∧
      (fun ω => markovCompl G (h ω) Φ) =ᵐ[P] Z := by
  have hhm := hh.measurable
  have hWle : W ≤ upperHalfPlaneOpens := hW
  -- the Poincaré data of the cutoff
  have hχ1 : ∀ z, |χ z| ≤ 1 := fun z => abs_le.2 ⟨by linarith [(hχ01 z).1], (hχ01 z).2⟩
  obtain ⟨L, hL⟩ := (hχc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hχ.continuous_fderiv (by simp))
  obtain ⟨R, hR, hRsub⟩ := (hχc.isCompact.isBounded.subset_ball_lt 0 (0 : ℂ))
  have hχK : ∀ z, z ∉ Metric.ball (0 : ℂ) R → fderiv ℝ χ z = 0 := fun z hz =>
    Function.notMem_support.1 fun h' => hz (hRsub (support_fderiv_subset ℝ h'))
  have h1χ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun z => 1 - χ z := contDiff_const.sub hχ
  -- the approximating sequence
  obtain ⟨g, hg1, hg2⟩ := exists_tendsto_integral_sq_of_isMarkovDecomposition hWle hd Φ
  set a : ℕ → TestOn upperHalfPlaneOpens := fun n =>
    smulTest (fun z => 1 - χ z) h1χ (Φ - lapTest W (g n))
  set b : ℕ → TestOn upperHalfPlaneOpens := fun n => smulTest χ hχ (Φ - lapTest W (g n))
  have hab : ∀ n, Φ = lapTest W (g n) + a n + b n := fun n => by
    ext z
    simp only [a, b, smulTest_apply, FunLike.coe_add, FunLike.coe_sub, Pi.add_apply,
      Pi.sub_apply]
    ring
  have ha : ∀ n, tsupport (a n) ⊆ O := fun n =>
    subset_inter (tsupport_mul_subset_left) ((tsupport_mul_subset_right).trans
      (Φ - lapTest W (g n)).tsupport_subset) |>.trans hχO
  set F : ℕ → Ω → ℝ := fun n ω => h ω (a n)
  have hF : ∀ n, Measurable[fieldSigmaOn h O] (F n) := fun n =>
    measurable_fieldSigmaOn_apply h (ha n)
  set e : ℕ → Ω → ℝ := fun n ω => G (h ω) Φ - h ω (lapTest W (g n))
  set c : ℕ → Ω → ℝ := fun n ω => h ω (b n)
  have he : ∀ n ω, markovCompl G (h ω) Φ - F n ω = -e n ω + c n ω := fun n ω => by
    have := congrArg (h ω) (hab n)
    simp only [map_add] at this
    simp only [markovCompl, F, e, c, sub_apply]
    linarith
  have hem : ∀ n, MemLp (e n) 2 P := fun n => memLp_markov_sub_lapTest hWle hd Φ (g n)
  have hcm : ∀ n, MemLp (c n) 2 P := fun n =>
    (hh.process.gaussian.hasGaussianLaw_eval (b n)).memLp_two
  have hc2 : ∀ n, ∫ ω, c n ω ^ 2 ∂P = zeroGFFTestCov H (b n) (b n) := fun n => by
    have hm : AEMeasurable (fun ω => h ω (b n)) P :=
      ((measurable_distOn_apply (b n)).comp hhm).aemeasurable
    rw [← variance_of_integral_eq_zero hm (hh.process.centered (b n)), ← covariance_self hm,
      hh.process.covariance_eq (b n) (b n)]
    rfl
  set K := 2 + 4 * L ^ 2 * R * (|(0 : ℂ).im| + R)
  have hcb : ∀ n, ∫ ω, c n ω ^ 2 ∂P ≤ K * ‖covVec W Φ - gradFeat W (g n).1‖ ^ 2 := fun n => by
    rw [hc2]
    exact zeroGFFTestCov_smulTest_le hW hχ hχ1 hL hR hχK hχW Φ (g n)
  refine exists_measurable_ae_eq_of_tendsto_integral_sq hF (fieldSigmaOn_le hhm O) ?_ ?_ ?_
  · exact ((measurable_distOn_apply Φ).comp (measurable_markovCompl_comp hhm
      hd.isZBGFFExtOn.measurable)).aestronglyMeasurable
  · intro n
    exact (((hem n).neg.add (hcm n)).integrable_sq).congr
      (Eventually.of_forall fun ω => by simp only [he n ω, Pi.add_apply, Pi.neg_apply])
  · have hbd : ∀ n, ∫ ω, (markovCompl G (h ω) Φ - F n ω) ^ 2 ∂P ≤
        2 * (∫ ω, e n ω ^ 2 ∂P) + 2 * (K * ‖covVec W Φ - gradFeat W (g n).1‖ ^ 2) := by
      intro n
      have i1 := integral_add (μ := P) (f := fun ω => e n ω ^ 2) (g := fun ω => c n ω ^ 2)
        (hem n).integrable_sq (hcm n).integrable_sq
      have i3 := integral_const_mul (μ := P) (2 : ℝ) fun ω => e n ω ^ 2 + c n ω ^ 2
      calc ∫ ω, (markovCompl G (h ω) Φ - F n ω) ^ 2 ∂P
          ≤ ∫ ω, 2 * (e n ω ^ 2 + c n ω ^ 2) ∂P := by
            refine integral_mono ?_ ?_ fun ω => ?_
            · exact (((hem n).neg.add (hcm n)).integrable_sq).congr
                (Eventually.of_forall fun ω => by simp only [he n ω, Pi.add_apply, Pi.neg_apply])
            · exact (((hem n).integrable_sq).add ((hcm n).integrable_sq)).const_mul 2
            · simp only [he n ω]
              nlinarith [sq_nonneg (e n ω + c n ω)]
        _ = 2 * (∫ ω, e n ω ^ 2 ∂P) + 2 * (∫ ω, c n ω ^ 2 ∂P) := by rw [i3, i1]; ring
        _ ≤ _ := by gcongr; exact hcb n
    refine squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) hbd ?_
    have t1 : Tendsto (fun n => ‖covVec (W : Set ℂ) Φ - gradFeat W (g n).1‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero).1 hg1
      simpa [norm_sub_rev] using this
    have : Tendsto (fun n => 2 * (∫ ω, e n ω ^ 2 ∂P) +
        2 * (K * ‖covVec W Φ - gradFeat W (g n).1‖ ^ 2)) atTop (𝓝 (2 * 0 + 2 * (K * 0 ^ 2))) :=
      (tendsto_const_nhds.mul hg2).add (tendsto_const_nhds.mul (tendsto_const_nhds.mul (t1.pow 2)))
    simpa using this

end GermLemma

end LocalSets
end InteractingSLE
