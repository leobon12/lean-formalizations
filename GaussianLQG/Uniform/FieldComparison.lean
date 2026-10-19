import GaussianLQG.Uniform.FieldComparison.Identify
import GaussianLQG.Uniform.FieldComparison.Bounds
import GaussianLQG.Uniform.FieldComparison.SupTail

/-!
# U14: the ξ-free field comparison (source (A.20)–(A.21), blueprint Appendix A.6)

Route U, step U14 of the uniform ledger (`blueprint/phaseB/uniform-ledger.tex`, statement
`exists_heatMollify_phiMN_tail`; audit A5 §4, Lemmas A6.1–A6.3). Let `W` be a white noise,
`h₀` the whole-plane GFF built from it (`h₀(φ) = W(testL2 φ)` a.s., as produced by
`LQGMetric.DG.exists_wn_wholePlaneGFF`), and `h̊₀ = h₀ − (h₀)_1(0)` the field normalized by its
unit-circle average. For `n ∈ ℕ` let `ε = 2^{-n}` and let `W'_n = W ∘ shiftL2 (ε²)` be the white
noise shifted in time by `ε² = 4^{-n}` (`LQGMetric.DDDF.P29WN.shiftL2`). Then
(`heatMollify_phiMN_tail_unif`): for every compact `V` there are `C, c > 0`, depending only on `V`,
such that for every such `(Ω, P, W, h₀)`, every `n` and every `t ≥ 0`,

  `P[sup_{z ∈ V} |h̊₀*_ε(z) − φ_{0,n}[W'_n](z)| ≥ t] ≤ C e^{−c t²}`.

Proof (blueprint A.6, audit A5 Lemmas A6.2–A6.3):
1. a.s., for each `z`, `h̊₀*_ε(z) − φ_{0,n}[W'_n](z) = W(cmpL2 ε z − circKerL2)` (OP-4,
   `ae_heatMollify_norm_eq_wn`, and `φ_{0,n}[W'_n](z) = √π W(shiftL2 ε² k_z)`), `ae_diff_eq`;
2. the Gaussian process `z ↦ W(cmpL2 ε z − circKerL2)` has increments
   `E(G v − G u)² ≤ |v − u|²/2` and variances `≤ (|v| + 1 + ‖circKerL2‖)²`, uniformly in `n`
   (`norm_cmpL2_sub_sq_le`, `norm_cmpL2_sub_circKerL2_le`): the time shift makes the small
   scales cancel exactly;
3. Kolmogorov + Fernique + Borell–TIS with constants before the probability space
   (`exists_version_tail_unif`), and a.s. equality on `V` of the two continuous versions.

The source's centred Gaussian constant `Z` (the normalization `C_ε`) is absorbed into the
difference field (its variance is bounded uniformly), so no `Z` is subtracted; `n = 0` is
included (audit A5-06 is moot). The ledger form on the coordinate space is
`exists_heatMollify_phiMN_tail`; the time-shifted noise is a white noise
(`isWhiteNoise_shiftWN`) and the laws of `φ`-functionals are the same for `W'_n` and `W`
(`FieldCmp.lambdaN_shiftWN`, `map_comp_contPhiMN_eq`, …; OP-3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal RealInnerProductSpace

universe u

namespace GaussianLQG
namespace FieldCmp

open LQGMetric LQGMetric.WhiteNoise LQGMetric.GFFExist LQGMetric.DDDF

/-! ### The difference process -/

section Process

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
  {h₀ : Ω → DistC}

/-- The white-noise process of the difference `h̊₀*_δ − φ_{0,n}[W'_n]`:
`z ↦ W(cmpL2 δ z − circKerL2)`. -/
def diffProc (W : WNSpace → Ω → ℝ) (δ : ℝ) (z : ℂ) (ω : Ω) : ℝ := W (cmpL2 δ z - circKerL2) ω

/-- The normalized field is a normalized whole-plane GFF. -/
theorem isNormalizedWPGFF_norm (hh : IsWholePlaneGFF h₀ P) :
    IsNormalizedWPGFF (fun ω => addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) P := by
  refine ⟨isWholePlaneGFF_norm hh, ?_⟩
  filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hh] with ω hω
  rw [hω]; ring

/-- **Step 1**: a.s., `h̊₀*_δ(z) − φ_{0,n}[W'_n](z) = W(cmpL2 δ z − circKerL2)`, `δ = 2^{-n}`. -/
theorem ae_diff_eq (hW : IsWhiteNoise P W) (hh : IsWholePlaneGFF h₀ P)
    (hae : ∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (testL2 φ)) (n : ℕ) (z : ℂ) :
    (fun ω => heatMollify ((2 : ℝ)⁻¹ ^ n) (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z -
      phiMN (shiftWN (((2 : ℝ)⁻¹ ^ n) ^ 2) W) P 0 n z ω) =ᵐ[P]
      diffProc W ((2 : ℝ)⁻¹ ^ n) z := by
  have hδ : 0 < (2 : ℝ)⁻¹ ^ n := by positivity
  have hW' := isWhiteNoise_shiftWN hW (((2 : ℝ)⁻¹ ^ n) ^ 2)
  have hphi := (isPhiVersion_phiMN hW' (Nat.zero_le n)).ae_eq z
  set k : WNSpace := DDDF.P29WN.shiftL2 (((2 : ℝ)⁻¹ ^ n) ^ 2) (phiKernelL2 ((2 : ℝ)⁻¹ ^ n) 1 z)
    with hk
  filter_upwards [ae_heatMollify_norm_eq_wn hW hh hae hδ.ne' z, hphi,
    wn_sub_ae hW (molKerL2 ((2 : ℝ)⁻¹ ^ n) z - circKerL2) (Real.sqrt Real.pi • k),
    hW.smul_ae (Real.sqrt Real.pi) k] with ω h1 h2 h3 h4
  have e : cmpL2 ((2 : ℝ)⁻¹ ^ n) z - circKerL2 =
      (molKerL2 ((2 : ℝ)⁻¹ ^ n) z - circKerL2) - Real.sqrt Real.pi • k := by
    rw [hk]; unfold cmpL2; abel
  have h2' : phiMN (shiftWN (((2 : ℝ)⁻¹ ^ n) ^ 2) W) P 0 n z ω =
      Real.sqrt Real.pi * W k ω := by
    rw [h2]; simp only [phi, pow_zero, shiftWN, hk]
  rw [h1, h2']
  show _ = W (cmpL2 ((2 : ℝ)⁻¹ ^ n) z - circKerL2) ω
  rw [e, h3, h4]

/-- **Step 1'**: the difference is a.s. continuous in `z`. -/
theorem ae_continuous_diff (hW : IsWhiteNoise P W) (hh : IsWholePlaneGFF h₀ P) (n : ℕ) :
    ∀ᵐ ω ∂P, Continuous fun z =>
      heatMollify ((2 : ℝ)⁻¹ ^ n) (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z -
        phiMN (shiftWN (((2 : ℝ)⁻¹ ^ n) ^ 2) W) P 0 n z ω := by
  have hδ : (2 : ℝ)⁻¹ ^ n ≠ 0 := by positivity
  have hW' := isWhiteNoise_shiftWN hW (((2 : ℝ)⁻¹ ^ n) ^ 2)
  filter_upwards [ae_continuous_heatMollify_norm hh hδ] with ω hω
  exact hω.2.sub ((isPhiVersion_phiMN hW' (Nat.zero_le n)).cont ω)

/-- **Step 2**: the difference process is a centred Gaussian process with the uniform
increment and variance bounds. -/
theorem diffProc_props (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    IsGaussianProcess (diffProc W δ) P ∧ (∀ v, ∫ ω, diffProc W δ v ω ∂P = 0) ∧
      (∀ u v, ∫ ω, (diffProc W δ v ω - diffProc W δ u ω) ^ 2 ∂P ≤ ‖v - u‖ ^ 2 / 2) ∧
      ∀ v, Var[diffProc W δ v; P] ≤ (‖v‖ + 1 + ‖circKerL2‖) ^ 2 := by
  refine ⟨hW.isGaussianProcess_comp (fun z => cmpL2 δ z - circKerL2),
    fun v => QuantumZipper.GFFExist.gs_integral_eq_zero (hW.hasLaw_single _),
    fun u v => ?_, fun v => ?_⟩
  · simp only [diffProc]
    rw [DG.integral_sq_wn_sub hW, sub_sub_sub_cancel_right]
    exact norm_cmpL2_sub_sq_le hδ hδ1 u v
  · change Var[W (cmpL2 δ v - circKerL2); P] ≤ _
    rw [← covariance_self (hW.measurable _).aemeasurable, hW.cov_eq, real_inner_self_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_cmpL2_sub_circKerL2_le hδ hδ1 v) 2

end Process

/-! ### U14 -/

/-- **U14, field comparison (source (A.21)), constants before the probability space.** For every
compact `V` there are `C, c > 0` such that for every white noise `W` on any probability space,
the whole-plane GFF `h₀` built from it (`h₀(φ) = W(testL2 φ)` a.s.), its normalization
`h̊₀ = h₀ − (h₀)_1(0)`, every `n` and every `t ≥ 0`:
`P[sup_{z∈V} |h̊₀*_{2^{-n}}(z) − φ_{0,n}[W'_n](z)| ≥ t] ≤ C e^{−ct²}`, where
`W'_n = W ∘ shiftL2 (4^{-n})` is the white noise shifted in time by `4^{-n}`. -/
theorem heatMollify_phiMN_tail_unif {V : Set ℂ} (hV : IsCompact V) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ} {h₀ : Ω → DistC}, IsWhiteNoise P W → IsWholePlaneGFF h₀ P →
      (∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (testL2 φ)) →
      ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
        P {ω | ENNReal.ofReal t ≤ ⨆ z ∈ V, ENNReal.ofReal
          |heatMollify ((2 : ℝ)⁻¹ ^ n) (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z -
            phiMN (fun f => W (DDDF.P29WN.shiftL2 (((2 : ℝ)⁻¹ ^ n) ^ 2) f)) P 0 n z ω|} ≤
          ENNReal.ofReal (C * Real.exp (-c * t ^ 2)) := by
  obtain ⟨R, hR⟩ := hV.isBounded.subset_closedBall 0
  set R₀ : ℝ := max R 0 with hR₀def
  have hR₀ : 0 ≤ R₀ := le_max_right _ _
  have hVR : V ⊆ closedBall (0 : ℂ) R₀ := hR.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hth : cthickening 1 V ⊆ closedBall (0 : ℂ) (1 + R₀) := by
    refine (cthickening_subset_of_subset 1 hVR).trans (le_of_eq ?_)
    exact cthickening_closedBall zero_le_one hR₀ 0
  set A : ℝ := R₀ + 1 with hAdef
  set σ : ℝ := R₀ + 2 + ‖circKerL2‖ with hσdef
  have hA : 0 < A := by positivity
  have hσ : 0 < σ := by positivity
  obtain ⟨C, c, hC, hc, hT⟩ := exists_version_tail_unif.{u} hV one_pos hA hσ
  refine ⟨C, c, hC, hc, fun {Ω} _ {P} {W} {h₀} hW hh hae n t ht => ?_⟩
  have hδ : 0 < (2 : ℝ)⁻¹ ^ n := by positivity
  have hδ1 : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨hG, h0, hinc, hvar⟩ := diffProc_props hW hδ hδ1
  have hnorm : ∀ v ∈ cthickening 1 V, ‖v‖ ≤ R₀ + 1 := fun v hv => by
    have := hth hv
    rw [mem_closedBall_zero_iff] at this
    linarith
  have hinc' : ∀ u' ∈ cthickening 1 V, ∀ v ∈ cthickening 1 V,
      ∫ ω, (diffProc W ((2 : ℝ)⁻¹ ^ n) v ω - diffProc W ((2 : ℝ)⁻¹ ^ n) u' ω) ^ 2 ∂P ≤
        A * ‖u' - v‖ := by
    intro u' hu v hv
    refine (hinc u' v).trans ?_
    have hd : ‖u' - v‖ ≤ 2 * A := by
      have := norm_sub_le u' v
      have := hnorm u' hu
      have := hnorm v hv
      simp only [hAdef]; linarith
    rw [norm_sub_rev v u']
    have h0' := norm_nonneg (u' - v)
    nlinarith
  have hvar' : ∀ v ∈ cthickening 1 V, Var[diffProc W ((2 : ℝ)⁻¹ ^ n) v; P] ≤ σ ^ 2 := by
    intro v hv
    refine (hvar v).trans (pow_le_pow_left₀ (by positivity) ?_ 2)
    have := hnorm v hv
    simp only [hσdef]; linarith
  obtain ⟨Y, hYG, hYc, hYt⟩ := hT _ hG h0 hinc' hvar'
  set X : ℂ → Ω → ℝ := fun z ω =>
    heatMollify ((2 : ℝ)⁻¹ ^ n) (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z -
      phiMN (shiftWN (((2 : ℝ)⁻¹ ^ n) ^ 2) W) P 0 n z ω with hXdef
  have hX : ∀ z ∈ V, X z =ᵐ[P] Y z := fun z hz =>
    (ae_diff_eq hW hh hae n z).trans (hYG z hz).symm
  have hXc : ∀ᵐ ω ∂P, ContinuousOn (fun z => X z ω) V :=
    (ae_continuous_diff hW hh n).mono fun ω hω => hω.continuousOn
  have heq : ∀ᵐ ω ∂P, ∀ z ∈ V, X z ω = Y z ω :=
    ae_eqOn_of_ae_eq hXc (Eventually.of_forall hYc) hX
  show P {ω | ENNReal.ofReal t ≤ ⨆ z ∈ V, ENNReal.ofReal |X z ω|} ≤ _
  refine le_trans (measure_mono_ae ?_) (hYt t ht)
  filter_upwards [heq] with ω hω hmem
  have e : (⨆ z ∈ V, ENNReal.ofReal |X z ω|) = ⨆ z ∈ V, ENNReal.ofReal |Y z ω| :=
    iSup_congr fun z => iSup_congr fun hz => by rw [hω z hz]
  show ENNReal.ofReal t ≤ ⨆ z ∈ V, ENNReal.ofReal |Y z ω|
  rw [← e]
  exact hmem

/-- **U14 for bounded sets** (for instance bounded boxes): the same bound with `V` bounded. -/
theorem heatMollify_phiMN_tail_unif_of_isBounded {V : Set ℂ} (hV : Bornology.IsBounded V) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ} {h₀ : Ω → DistC}, IsWhiteNoise P W → IsWholePlaneGFF h₀ P →
      (∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (testL2 φ)) →
      ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
        P {ω | ENNReal.ofReal t ≤ ⨆ z ∈ V, ENNReal.ofReal
          |heatMollify ((2 : ℝ)⁻¹ ^ n) (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z -
            phiMN (fun f => W (DDDF.P29WN.shiftL2 (((2 : ℝ)⁻¹ ^ n) ^ 2) f)) P 0 n z ω|} ≤
          ENNReal.ofReal (C * Real.exp (-c * t ^ 2)) := by
  obtain ⟨C, c, hC, hc, hT⟩ := heatMollify_phiMN_tail_unif.{u} hV.isCompact_closure
  refine ⟨C, c, hC, hc, fun {Ω} _ {P} {W} {h₀} hW hh hae n t ht => ?_⟩
  refine le_trans (measure_mono fun ω hω => ?_) (hT hW hh hae n t ht)
  simp only [mem_ofPred_eq] at hω ⊢
  exact hω.trans (biSup_mono fun z hz => subset_closure hz)

/-- **U14 on the coordinate space** (statement `exists_heatMollify_phiMN_tail` of the uniform
ledger): there are a white noise `W` on `(ℕ → ℝ, stdP)` and a normalized whole-plane GFF `h`
(built from `W`) such that for every compact `K` the comparison of `h*_{2^{-n}}` with
`φ_{0,n}` of the shifted noise `W ∘ shiftL2 (4^{-n})` has a Gaussian tail uniformly in `n`. -/
theorem exists_heatMollify_phiMN_tail :
    ∃ (W : WNSpace → (ℕ → ℝ) → ℝ) (h : (ℕ → ℝ) → DistC),
      IsWhiteNoise LQGDimension.ExistAsm.stdP W ∧ IsNormalizedWPGFF h LQGDimension.ExistAsm.stdP ∧
      ∀ K : Set ℂ, IsCompact K → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (n : ℕ) (u : ℝ), 0 ≤ u → LQGDimension.ExistAsm.stdP {ω | ENNReal.ofReal u ≤
          ⨆ z ∈ K, ENNReal.ofReal |heatMollify ((2 : ℝ)⁻¹ ^ n) (h ω) z -
            phiMN (fun f => W (DDDF.P29WN.shiftL2 (((2 : ℝ)⁻¹ ^ n) ^ 2) f))
              LQGDimension.ExistAsm.stdP 0 n z ω|} ≤
          ENNReal.ofReal (C * Real.exp (-c * u ^ 2)) := by
  obtain ⟨W, h₀, hW, hh, hae⟩ := DG.exists_wn_wholePlaneGFF
  refine ⟨W, fun ω => addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0), hW, isNormalizedWPGFF_norm hh,
    fun K hK => ?_⟩
  obtain ⟨C, c, hC, hc, hT⟩ := heatMollify_phiMN_tail_unif.{0} hK
  exact ⟨C, c, hC, hc, fun n u hu => hT hW hh hae n u hu⟩

/-- **U14 on the coordinate space, with the construction exposed**: the white noise `W` and the
GFF `h₀` of `LQGMetric.DG.exists_wn_wholePlaneGFF`, the normalized field
`h = h₀ − (h₀)_1(0)`, the white-noise representation of `h*_ε` (OP-4), the shifted noises, and the
Gaussian tail of the comparison on every compact set. -/
theorem exists_heatMollify_phiMN_tail' :
    ∃ (W : WNSpace → (ℕ → ℝ) → ℝ) (h₀ : (ℕ → ℝ) → DistC),
      IsWhiteNoise LQGDimension.ExistAsm.stdP W ∧ IsWholePlaneGFF h₀ LQGDimension.ExistAsm.stdP ∧
      (∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[LQGDimension.ExistAsm.stdP] W (testL2 φ)) ∧
      IsNormalizedWPGFF (fun ω => addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0))
        LQGDimension.ExistAsm.stdP ∧
      (∀ (ε : ℝ), ε ≠ 0 → ∀ z : ℂ,
        (fun ω => heatMollify ε (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z)
          =ᵐ[LQGDimension.ExistAsm.stdP] W (molKerL2 ε z - circKerL2)) ∧
      (∀ a : ℝ, IsWhiteNoise LQGDimension.ExistAsm.stdP
        (fun f => W (DDDF.P29WN.shiftL2 a f))) ∧
      ∀ K : Set ℂ, IsCompact K → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (n : ℕ) (u : ℝ), 0 ≤ u → LQGDimension.ExistAsm.stdP {ω | ENNReal.ofReal u ≤
          ⨆ z ∈ K, ENNReal.ofReal |heatMollify ((2 : ℝ)⁻¹ ^ n)
            (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z -
            phiMN (fun f => W (DDDF.P29WN.shiftL2 (((2 : ℝ)⁻¹ ^ n) ^ 2) f))
              LQGDimension.ExistAsm.stdP 0 n z ω|} ≤
          ENNReal.ofReal (C * Real.exp (-c * u ^ 2)) := by
  obtain ⟨W, h₀, hW, hh, hae⟩ := DG.exists_wn_wholePlaneGFF
  refine ⟨W, h₀, hW, hh, hae, isNormalizedWPGFF_norm hh,
    fun ε hε z => ae_heatMollify_norm_eq_wn hW hh hae hε z,
    fun a => isWhiteNoise_shiftWN hW a, fun K hK => ?_⟩
  obtain ⟨C, c, hC, hc, hT⟩ := heatMollify_phiMN_tail_unif.{0} hK
  exact ⟨C, c, hC, hc, fun n u hu => hT hW hh hae n u hu⟩

end FieldCmp
end GaussianLQG
