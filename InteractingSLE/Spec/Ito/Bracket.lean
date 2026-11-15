import InteractingSLE.Spec.Ito.Martingale

/-!
# `d𝔥_t(z) = Im(2/f_t(z)) dB_t`: the brackets of the mean

Packet PROVE-T11-ITO (Specification L505, (3.15); L509: `d⟨𝔥_t(z), 𝔥_t(z)⟩ = −dC_t(z)`). A continuous local martingale
`M` with `M² − ∫ H² ds` and `M B − ∫ H ds` local martingales is `∫ H dB` (Revuz–Yor IV.1–IV.2: `⟨M − ∫H dB⟩ = 0`). For the
mean `𝔥_t(z)` with `H_s = Im(2/f_s(z))`:

* `exists_martingale_couplingMean_sq`: `𝔥_{t∧σ}(z)² − ∫₀^{t∧σ} Im(2/f_s(z))² ds` agrees a.s. with a martingale;
* `exists_martingale_couplingMean_mul_B`: `𝔥_{t∧σ}(z) B_{t∧σ} − ∫₀^{t∧σ} Im(2/f_s(z)) ds` agrees a.s. with a
  martingale;

for every protected stopping time `σ` (as in `exists_martingale_couplingMean`). The proofs use the product rule for the
Itô generator (`itoGen_mul`: `itoGen (F₁F₂) = F₁ itoGen F₂ + F₂ itoGen F₁ + ∂_xF₁ ∂_xF₂`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Ito

/-! ### The product rule for the generator -/

section Product

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F F₁ F₂ : E × ℝ → ℝ} {p : E × ℝ}

theorem hasDerivAt_snd_line (hF : DifferentiableAt ℝ F p) :
    HasDerivAt (fun y : ℝ => F (p.1, y)) (partialSnd F p) p.2 := by
  have hline : HasDerivAt (fun y : ℝ => ((p.1, y) : E × ℝ)) ((0, 1) : E × ℝ) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact (show HasFDerivAt F (fderiv ℝ F p) (p.1, p.2) from hF.hasFDerivAt).comp_hasDerivAt p.2 hline

theorem hasDerivAt_partialSnd (hF : ContDiffAt ℝ 2 F p) :
    HasDerivAt (fun y : ℝ => partialSnd F (p.1, y)) (partialSndSnd F p) p.2 := by
  have hF1 : ContDiffAt ℝ 1 (fderiv ℝ F) p := hF.fderiv_right (by norm_num)
  have hD : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) p) (p.1, p.2) :=
    (hF1.differentiableAt (by norm_num)).hasFDerivAt
  have hline : HasDerivAt (fun y : ℝ => ((p.1, y) : E × ℝ)) ((0, 1) : E × ℝ) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hc := (hD.comp_hasDerivAt p.2 hline).clm_apply (hasDerivAt_const p.2 ((0, 1) : E × ℝ))
  simp only [Function.comp_def, map_zero, add_zero] at hc
  exact hc

theorem partialFst_mul (hF₁ : DifferentiableAt ℝ F₁ p) (hF₂ : DifferentiableAt ℝ F₂ p) (v : E) :
    partialFst (fun q => F₁ q * F₂ q) p v = F₁ p * partialFst F₂ p v + F₂ p * partialFst F₁ p v := by
  simp only [partialFst_apply, fderiv_fun_mul hF₁ hF₂, add_apply,
    smul_apply, smul_eq_mul]

theorem partialSnd_mul (hF₁ : DifferentiableAt ℝ F₁ p) (hF₂ : DifferentiableAt ℝ F₂ p) :
    partialSnd (fun q => F₁ q * F₂ q) p = F₁ p * partialSnd F₂ p + F₂ p * partialSnd F₁ p := by
  simp only [partialSnd, fderiv_fun_mul hF₁ hF₂, add_apply,
    smul_apply, smul_eq_mul]

/-- **The product rule for the Itô generator**:
`itoGen (F₁ F₂) = F₁ itoGen F₂ + F₂ itoGen F₁ + ∂_x F₁ ∂_x F₂`. -/
theorem itoGen_mul (hF₁ : ContDiffAt ℝ 2 F₁ p) (hF₂ : ContDiffAt ℝ 2 F₂ p) (v : E) :
    itoGen (fun q => F₁ q * F₂ q) p v =
      F₁ p * itoGen F₂ p v + F₂ p * itoGen F₁ p v + partialSnd F₁ p * partialSnd F₂ p := by
  have hd₁ := hF₁.differentiableAt (by norm_num)
  have hd₂ := hF₂.differentiableAt (by norm_num)
  have hline : ContinuousAt (fun y : ℝ => ((p.1, y) : E × ℝ)) p.2 :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hev₁ : ∀ᶠ y in 𝓝 p.2, DifferentiableAt ℝ F₁ (p.1, y) :=
    hline.eventually ((hF₁.eventually (by simp)).mono fun q hq => hq.differentiableAt (by norm_num))
  have hev₂ : ∀ᶠ y in 𝓝 p.2, DifferentiableAt ℝ F₂ (p.1, y) :=
    hline.eventually ((hF₂.eventually (by simp)).mono fun q hq => hq.differentiableAt (by norm_num))
  have hSS : partialSndSnd (fun q => F₁ q * F₂ q) p =
      partialSnd F₁ p * partialSnd F₂ p + F₁ p * partialSndSnd F₂ p +
        (partialSnd F₂ p * partialSnd F₁ p + F₂ p * partialSndSnd F₁ p) := by
    refine partialSndSnd_eq_of_hasDerivAt (hF₁.mul hF₂)
      (g := fun y => F₁ (p.1, y) * partialSnd F₂ (p.1, y) + F₂ (p.1, y) * partialSnd F₁ (p.1, y))
      ((hev₁.and hev₂).mono fun y hy => partialSnd_mul hy.1 hy.2) ?_
    exact ((hasDerivAt_snd_line hd₁).mul (hasDerivAt_partialSnd hF₂)).add
      ((hasDerivAt_snd_line hd₂).mul (hasDerivAt_partialSnd hF₁))
  unfold itoGen
  rw [partialFst_mul hd₁ hd₂, hSS]
  ring

/-- The coordinate `x` (the Brownian slot) as an observable. -/
def obsX (p : E × ℝ) : ℝ := p.2

theorem contDiff_obsX {n : WithTop ℕ∞} : ContDiff ℝ n (obsX : E × ℝ → ℝ) := contDiff_snd

theorem fderiv_obsX (q : E × ℝ) : fderiv ℝ (obsX : E × ℝ → ℝ) q = ContinuousLinearMap.snd ℝ E ℝ :=
  (ContinuousLinearMap.snd ℝ E ℝ).fderiv

theorem itoGen_obsX (q : E × ℝ) (v : E) : itoGen (obsX : E × ℝ → ℝ) q v = 0 := by
  have h : fderiv ℝ (fderiv ℝ (obsX : E × ℝ → ℝ)) q = 0 := by
    have : fderiv ℝ (obsX : E × ℝ → ℝ) = fun _ => ContinuousLinearMap.snd ℝ E ℝ :=
      funext fderiv_obsX
    rw [this]; exact fderiv_const_apply _
  simp only [itoGen, partialFst_apply, partialSndSnd, fderiv_obsX, h,
    ContinuousLinearMap.coe_snd', zero_apply, mul_zero, add_zero]

theorem partialSnd_obsX (q : E × ℝ) : partialSnd (obsX : E × ℝ → ℝ) q = 1 := by
  simp only [partialSnd, fderiv_obsX, ContinuousLinearMap.coe_snd']

end Product

/-! ### The generators along the path -/

section Path

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {z : ℂ} {T : ℝ≥0}

theorem integral_congr_of_ae_Ioc {g h : ℝ → ℝ} {T a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T)
    (hgh : ∀ᵐ s : ℝ, s ∈ Ioc (0 : ℝ) T → g s = h s) :
    ∫ s in (0 : ℝ)..a, g s = ∫ s in (0 : ℝ)..a, h s := by
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hgh] with s hs hsa
  rw [uIoc_of_le ha] at hsa
  exact hs ⟨hsa.1, hsa.2.trans haT⟩

/-- Along the path, `itoGen (meanObs²) = Im(2/f_s)²` for a.e. `s ∈ (0, T]`. -/
theorem ae_itoGen_meanObs_sq_coordAt (hκ : 0 < κ)
    (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hT : (T : ℝ≥0∞) < ζ) (hz : 0 < z.im)
    (hsol : ∃ u, QuantumZipper.IsForwardSol (rpath w) z T u) :
    ∀ᵐ s : ℝ, s ∈ Ioc (0 : ℝ) T → itoGen (fun q => meanObs κ ρL ρR q * meanObs κ ρL ρR q)
      (coordAt κ z w vL vR b s.toNNReal, b s.toNNReal) (densityAt z ρL ρR w vL vR s) =
      ((2 / QuantumZipper.fwdMap (rpath w) s z).im) ^ 2 := by
  filter_upwards [ae_itoGen_meanObs_coordAt (b := b) hκ hP hT hz hsol] with s hs hsI
  have hsT : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hsI.2
  have hmem := mem_obsRegion_coordAt (κ := κ) (b := b) hP hT hz hsol hsT
  rw [itoGen_mul (contDiffAt_meanObs κ ρL ρR hmem) (contDiffAt_meanObs κ ρL ρR hmem), hs hsI,
    partialSnd_meanObs_eq hκ ρL ρR hmem, coordF_coordAt, Real.coe_toNNReal _ hsI.1.le]
  ring

/-- Along the path, `itoGen (meanObs · x) = Im(2/f_s)` for a.e. `s ∈ (0, T]`. -/
theorem ae_itoGen_meanObs_mul_obsX_coordAt (hκ : 0 < κ)
    (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hT : (T : ℝ≥0∞) < ζ) (hz : 0 < z.im)
    (hsol : ∃ u, QuantumZipper.IsForwardSol (rpath w) z T u) :
    ∀ᵐ s : ℝ, s ∈ Ioc (0 : ℝ) T → itoGen (fun q => meanObs κ ρL ρR q * obsX q)
      (coordAt κ z w vL vR b s.toNNReal, b s.toNNReal) (densityAt z ρL ρR w vL vR s) =
      (2 / QuantumZipper.fwdMap (rpath w) s z).im := by
  filter_upwards [ae_itoGen_meanObs_coordAt (b := b) hκ hP hT hz hsol] with s hs hsI
  have hsT : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hsI.2
  have hmem := mem_obsRegion_coordAt (κ := κ) (b := b) hP hT hz hsol hsT
  rw [itoGen_mul (contDiffAt_meanObs κ ρL ρR hmem) contDiff_obsX.contDiffAt, hs hsI,
    itoGen_obsX, partialSnd_meanObs_eq hκ ρL ρR hmem, partialSnd_obsX, coordF_coordAt,
    Real.coe_toNNReal _ hsI.1.le]
  ring

end Path

/-! ### The brackets -/

section Brackets

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **`d⟨𝔥(z)⟩_t = Im(2/f_t(z))² dt`**: for every protected stopping time `σ`,
`𝔥_{t∧σ}(z)² − ∫₀^{t∧σ} Im(2/f_s(z))² ds` agrees almost surely, at every time, with a martingale. -/
theorem exists_martingale_couplingMean_sq
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ) {z : ℂ}
    (hz : 0 < z.im) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0)) {δ R N : ℝ}
    (hδ : 0 < δ)
    (hσp : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      ∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (nullAugmented 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
      M t ω = couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
          (u ω (min t (σ ω))) z ^ 2 -
        ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
          ((2 / QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) s z).im) ^ 2 := by
  obtain ⟨M, hM, hae⟩ := exists_martingale_coordObs hE hz hσ hδ hσp
    (Φ := fun q => meanObs κ ρL ρR q * meanObs κ ρL ρR q)
    ((contDiffOn_meanObs κ ρL ρR (n := 3)).mul (contDiffOn_meanObs κ ρL ρR (n := 3)))
  refine ⟨M, hM, ?_⟩
  filter_upwards [hae, hE.2.2.2.2, hσp] with ω hMω hPω hσω t
  obtain ⟨hσζ, hsol, -⟩ := hσω
  have h0 := integral_congr_of_ae_Ioc (min t (σ ω)).coe_nonneg
    (by exact_mod_cast min_le_right t (σ ω)) (ae_itoGen_meanObs_sq_coordAt hκ hPω hσζ hz hsol)
  rw [hMω t]
  rw [show (∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), itoGen (fun q => meanObs κ ρL ρR q *
      meanObs κ ρL ρR q) (coordProc κ z W VL VR B s.toNNReal ω, B s.toNNReal ω)
      (densityAt z ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s)) = _ from h0]
  have hm : couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
      (u ω (min t (σ ω))) z =
      meanObs κ ρL ρR (coordProc κ z W VL VR B (min t (σ ω)) ω, B (min t (σ ω)) ω) :=
    couplingMean_eq_meanObs hPω hσζ hz hsol (min_le_right t (σ ω)) (hu ω _)
  rw [hm, sq]
  rfl

/-- **`d⟨𝔥(z), B⟩_t = Im(2/f_t(z)) dt`**: for every protected stopping time `σ`,
`𝔥_{t∧σ}(z) B_{t∧σ} − ∫₀^{t∧σ} Im(2/f_s(z)) ds` agrees almost surely, at every time, with a martingale.
Together with `exists_martingale_couplingMean` and `exists_martingale_couplingMean_sq` this is
`d𝔥_t(z) = Im(2/f_t(z)) dB_t` ((3.15)). -/
theorem exists_martingale_couplingMean_mul_B
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ) {z : ℂ}
    (hz : 0 < z.im) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0)) {δ R N : ℝ}
    (hδ : 0 < δ)
    (hσp : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      ∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (nullAugmented 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
      M t ω = couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
          (u ω (min t (σ ω))) z * B (min t (σ ω)) ω -
        ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
          (2 / QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) s z).im := by
  obtain ⟨M, hM, hae⟩ := exists_martingale_coordObs hE hz hσ hδ hσp
    (Φ := fun q => meanObs κ ρL ρR q * obsX q)
    ((contDiffOn_meanObs κ ρL ρR (n := 3)).mul contDiff_obsX.contDiffOn)
  refine ⟨M, hM, ?_⟩
  filter_upwards [hae, hE.2.2.2.2, hσp] with ω hMω hPω hσω t
  obtain ⟨hσζ, hsol, -⟩ := hσω
  have h0 := integral_congr_of_ae_Ioc (min t (σ ω)).coe_nonneg
    (by exact_mod_cast min_le_right t (σ ω))
    (ae_itoGen_meanObs_mul_obsX_coordAt hκ hPω hσζ hz hsol)
  rw [hMω t]
  rw [show (∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), itoGen (fun q => meanObs κ ρL ρR q * obsX q)
      (coordProc κ z W VL VR B s.toNNReal ω, B s.toNNReal ω)
      (densityAt z ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s)) = _ from h0]
  have hm : couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
      (u ω (min t (σ ω))) z =
      meanObs κ ρL ρR (coordProc κ z W VL VR B (min t (σ ω)) ω, B (min t (σ ω)) ω) :=
    couplingMean_eq_meanObs hPω hσζ hz hsol (min_le_right t (σ ω)) (hu ω _)
  rw [hm]
  rfl

end Brackets

end Ito

end InteractingSLE
