import QuantumZipper.Proofs.Thm11.MainMart
import QuantumZipper.Proofs.Thm11.ClockIntegrable
import QuantumZipper.Proofs.Thm11.PushTameAS
import QuantumZipper.Proofs.Thm11.PushTameNA

/-!
# Theorem 1.1 (main statement) for `κ ∈ (0,4]`

Blueprint `THM11_BLUEPRINT.md` §8, AS-4, including `κ = 4`. The assembly of
`Thm11Main.theorem1_1_main_lt_four` uses admissibility of the pushforward test measures
`ν_T^± = pushTest W T ρ^±` (via `TameCond`, which contains the log hypothesis coming from clock
integrability, available only for `κ < 4`). Here that step is replaced by the
admissibility-free RG-2 of `ZeroRegBoundaryNA`:

* `TameCondNA` = barriers + strip decay (no log hypothesis); it gives
  `ZeroRegBdryNA.TameBdry ν_T^±` (`PushTameNA.tameBdry_pushTest`);
* `cond_charFun_path_NA`: the conditional Gaussian step, from
  `ZeroRegBdryNA.integral_cexp_evalReg_sub_NA` and the energy identity
  `kernelCov2_pushTest_NA` (integrability of `greenH` from bounded potentials);
* `lin_path_NA`: a.s. linearity of the pairing, from linearity of `evalReg` in the measure
  (`FoldBound.RegConv.add_measure`) and a.s. convergence (`ae_regConv_NA`);
* the rest of AS-1 (`charFun_rhs_fwd_NA`, `rhs_fwd_version_NA`) is the proof of
  `CharFunRhs` with these substitutions.

Main result: `theorem1_1_main_proof : theorem1_1_main`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm11MainFull

open CharFun CharFunFwd CharFunRhs PushTame ZeroRegBdryNA FoldBound

/-! ## Admissibility-free inputs from RG-2 -/

/-- `greenH` is integrable against the product of two tame measures (bounded potentials). -/
theorem integrable_greenH_tame {μ ν : Measure ℂ} (hμ : TameBdry μ) (hν : TameBdry ν) :
    Integrable (fun p : ℂ × ℂ => greenH p.1 p.2) (μ.prod ν) := by
  have := hμ.finite
  have := hν.finite
  obtain ⟨U, hU⟩ := hν.pot_le
  have hpot : ∀ x ∈ Hbar, fbPot ν x ≤ U := fun x hx => by simpa using hU univ x hx
  have hμH := compl_Hbar_null hμ.im_nonpos
  have hνH := compl_Hbar_null hν.im_nonpos
  have hnn : 0 ≤ᵐ[μ.prod ν] fun p : ℂ × ℂ => greenH p.1 p.2 := by
    refine (Measure.ae_prod_iff_ae_ae
      (measurableSet_le measurable_const measurable_greenH)).2 ?_
    filter_upwards [(ae_iff.2 hμH : ∀ᵐ x ∂μ, x ∈ Hbar)] with x hx
    have hne : ∀ᵐ y ∂ν, y ≠ x := by rw [ae_iff]; simpa using hν.atom x
    filter_upwards [(ae_iff.2 hνH : ∀ᵐ y ∂ν, y ∈ Hbar), hne] with y hy hyx
    exact greenH_nonneg hx hy hyx.symm
  refine ⟨measurable_greenH.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 ?_⟩
  rw [lintegral_prod (fun p : ℂ × ℂ => ENNReal.ofReal (greenH p.1 p.2))
    (ENNReal.measurable_ofReal.comp measurable_greenH).aemeasurable]
  exact (lintegral_pot_le hμH hpot).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _))

section RegConvSection

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- For a tame measure the regularized evaluation is a.s. a genuine limit (`RegConv`). -/
theorem ae_regConv_NA (hX : IsZeroBoundaryGFFH X P) {μ : Measure ℂ} (hμ : TameBdry μ) :
    ∀ᵐ ω ∂P, RegConv (X ω) μ := by
  have := hμ.finite
  obtain ⟨K, hK, hKH, hμK⟩ := hμ.support
  have hc : ∀ᵐ ω ∂P, ∀ k, ContinuousOn (fun z => avgReg (X ω) k z) Hbar :=
    ae_all_iff.2 fun k => ZeroReg.ae_continuousOn_avgReg_zero hX k
  have hre : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hμK)
  filter_upwards [hc, ae_tendsto_evalReg_NA hX hμ] with ω hω h
  refine ⟨fun k => ?_, _, h.2⟩
  have hi := ((hω k).mono hKH).integrableOn_compact (μ := μ) hK
  rw [IntegrableOn, hre] at hi
  exact hi

end RegConvSection

theorem nnreal_smul_measure (b : ℝ≥0) (μ : Measure ℂ) : b • μ = (b : ℝ≥0∞) • μ := by
  ext s _
  rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def]

/-- Linearity of `evalReg` along a measure identity, given convergence at all six measures. -/
theorem evalReg_lin_core {x : FieldSample} {m3p m3m mu mv m2p m2m : Measure ℂ}
    (h3p : RegConv x m3p) (h3m : RegConv x m3m) (hmu : RegConv x mu) (hmv : RegConv x mv)
    (h2p : RegConv x m2p) (h2m : RegConv x m2m) (b : ℝ≥0)
    (hid : m3p + b • mv + m2m = m3m + b • mu + m2p) :
    evalReg x m3p - evalReg x m3m =
      b * (evalReg x mu - evalReg x mv) + (evalReg x m2p - evalReg x m2m) := by
  obtain ⟨r1, e1⟩ := hmv.smul_measure (c := (b : ℝ≥0∞)) ENNReal.coe_ne_top
  obtain ⟨r2, e2⟩ := h3p.add_measure r1
  obtain ⟨-, e3⟩ := r2.add_measure h2m
  obtain ⟨s1, f1⟩ := hmu.smul_measure (c := (b : ℝ≥0∞)) ENNReal.coe_ne_top
  obtain ⟨s2, f2⟩ := h3m.add_measure s1
  obtain ⟨-, f3⟩ := s2.add_measure h2p
  rw [nnreal_smul_measure, nnreal_smul_measure] at hid
  have := congrArg (evalReg x) hid
  rw [e3, e2, e1, f3, f2, f1] at this
  simp only [ENNReal.coe_toReal] at this
  linarith

/-- `lin_map` for `evalReg` (replaces `CharFunRhs.ae_lin_map`). -/
theorem lin_map_evalReg {x : FieldSample} {F : ℂ → ℂ} (hF : Measurable F) {b₁ b₂ b₃ : ℂ → ℝ}
    (m₁ : Measurable b₁) (m₂ : Measurable b₂) (m₃ : Measurable b₃) (a : ℝ)
    (h : ∀ z, b₃ z = a * b₁ z + b₂ z)
    (A₁ : RegConv x ((tdens b₁).map F)) (A₁' : RegConv x ((tdens fun z => -b₁ z).map F))
    (A₂ : RegConv x ((tdens b₂).map F)) (A₂' : RegConv x ((tdens fun z => -b₂ z).map F))
    (A₃ : RegConv x ((tdens b₃).map F)) (A₃' : RegConv x ((tdens fun z => -b₃ z).map F)) :
    evalReg x ((tdens b₃).map F) - evalReg x ((tdens fun z => -b₃ z).map F) =
      a * (evalReg x ((tdens b₁).map F) - evalReg x ((tdens fun z => -b₁ z).map F)) +
      (evalReg x ((tdens b₂).map F) - evalReg x ((tdens fun z => -b₂ z).map F)) := by
  have hreal : ∀ z, max (b₃ z) 0 - max (-b₃ z) 0 -
      a * (max (b₁ z) 0 - max (-b₁ z) 0) - (max (b₂ z) 0 - max (-b₂ z) 0) = 0 := by
    intro z
    rw [max_sub_max_neg, max_sub_max_neg, max_sub_max_neg, h z]
    ring
  rcases le_total 0 a with ha | ha
  · have hb : ((a.toNNReal : ℝ≥0) : ℝ) = a := Real.coe_toNNReal a ha
    have hid := tdens_map_comb hF a.toNNReal m₃ m₁.neg m₂ m₁
      (fun z => by rw [hb]; linear_combination hreal z)
    rw [evalReg_lin_core A₃ A₃' A₁ A₁' A₂ A₂' a.toNNReal hid, hb]
  · have hb : (((-a).toNNReal : ℝ≥0) : ℝ) = -a := Real.coe_toNNReal (-a) (by linarith)
    have hid := tdens_map_comb hF (-a).toNNReal m₃ m₁ m₂ m₁.neg
      (fun z => by rw [hb]; linear_combination hreal z)
    rw [evalReg_lin_core A₃ A₃' A₁' A₁ A₂ A₂' (-a).toNNReal hid, hb]
    ring

/-! ## Energies without admissibility -/

theorem kernelCov_map_greenH_NA {F : ℂ → ℂ} (hF : Measurable F) {a b : ℂ → ℝ} (ha : Measurable a)
    (hb : Measurable b)
    (hN : Integrable (fun p : ℂ × ℂ => greenH p.1 p.2) (((tdens a).map F).prod ((tdens b).map F))) :
    Integrable (fun p : ℂ × ℂ => max (a p.1) 0 * max (b p.2) 0 * greenH (F p.1) (F p.2))
        (volume.prod volume) ∧
      kernelCov greenH ((tdens a).map F) ((tdens b).map F) =
        ∫ p, max (a p.1) 0 * max (b p.2) 0 * greenH (F p.1) (F p.2) ∂(volume.prod volume) := by
  have hma : Measurable fun z => ENNReal.ofReal (a z) := ENNReal.measurable_ofReal.comp ha
  have hmb : Measurable fun z => ENNReal.ofReal (b z) := ENNReal.measurable_ofReal.comp hb
  have hN1 : Integrable (fun p : ℂ × ℂ => greenH p.1 p.2)
      (((tdens a).prod (tdens b)).map (Prod.map F F)) := by
    rwa [← Measure.map_prod_map _ _ hF hF]
  have hN2 := (integrable_map_measure measurable_greenH.aestronglyMeasurable
    (hF.prodMap hF).aemeasurable).1 hN1
  rw [tdens, tdens, prod_withDensity hma hmb] at hN2
  have hlt : ∀ᵐ p ∂(volume.prod volume : Measure (ℂ × ℂ)),
      ENNReal.ofReal (a p.1) * ENNReal.ofReal (b p.2) < ⊤ :=
    ae_of_all _ fun p => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hm2 : Measurable fun p : ℂ × ℂ => ENNReal.ofReal (a p.1) * ENNReal.ofReal (b p.2) :=
    (hma.comp measurable_fst).mul (hmb.comp measurable_snd)
  rw [integrable_withDensity_iff_integrable_smul' hm2 hlt] at hN2
  have heq : ∀ p : ℂ × ℂ, (ENNReal.ofReal (a p.1) * ENNReal.ofReal (b p.2)).toReal •
      ((fun p : ℂ × ℂ => greenH p.1 p.2) ∘ Prod.map F F) p =
      max (a p.1) 0 * max (b p.2) 0 * greenH (F p.1) (F p.2) := by
    intro p
    simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal', smul_eq_mul]
  refine ⟨hN2.congr (ae_of_all _ heq), ?_⟩
  calc kernelCov greenH ((tdens a).map F) ((tdens b).map F)
        = ∫ p, greenH p.1 p.2 ∂(((tdens a).map F).prod ((tdens b).map F)) :=
          (integral_prod _ hN).symm
    _ = ∫ p, greenH p.1 p.2 ∂(((tdens a).prod (tdens b)).map (Prod.map F F)) := by
          rw [Measure.map_prod_map _ _ hF hF]
    _ = ∫ p, ((fun p : ℂ × ℂ => greenH p.1 p.2) ∘ Prod.map F F) p
          ∂((tdens a).prod (tdens b)) := by
          rw [integral_map (hF.prodMap hF).aemeasurable
            measurable_greenH.aestronglyMeasurable]
          rfl
    _ = _ := by
          rw [tdens, tdens, prod_withDensity hma hmb,
            integral_withDensity_eq_integral_toReal_smul hm2 hlt]
          exact integral_congr_ae (ae_of_all _ heq)

theorem kernelCov2_map_greenH_NA {F : ℂ → ℂ} (hF : Measurable F) {b : ℂ → ℝ} (hb : Measurable b)
    (h11 : Integrable (fun p : ℂ × ℂ => greenH p.1 p.2) (((tdens b).map F).prod ((tdens b).map F)))
    (h12 : Integrable (fun p : ℂ × ℂ => greenH p.1 p.2)
      (((tdens b).map F).prod ((tdens fun z => -b z).map F)))
    (h21 : Integrable (fun p : ℂ × ℂ => greenH p.1 p.2)
      (((tdens fun z => -b z).map F).prod ((tdens b).map F)))
    (h22 : Integrable (fun p : ℂ × ℂ => greenH p.1 p.2)
      (((tdens fun z => -b z).map F).prod ((tdens fun z => -b z).map F))) :
    kernelCov2 greenH ((tdens b).map F, (tdens fun z => -b z).map F)
        ((tdens b).map F, (tdens fun z => -b z).map F) =
      ∫ x, ∫ y, b x * b y * greenH (F x) (F y) := by
  have hbn : Measurable fun z => -b z := hb.neg
  obtain ⟨i1, e1⟩ := kernelCov_map_greenH_NA hF hb hb h11
  obtain ⟨i2, e2⟩ := kernelCov_map_greenH_NA hF hb hbn h12
  obtain ⟨i3, e3⟩ := kernelCov_map_greenH_NA hF hbn hb h21
  obtain ⟨i4, e4⟩ := kernelCov_map_greenH_NA hF hbn hbn h22
  have hpt : ∀ p : ℂ × ℂ, b p.1 * b p.2 * greenH (F p.1) (F p.2) =
      max (b p.1) 0 * max (b p.2) 0 * greenH (F p.1) (F p.2) -
      max (b p.1) 0 * max (-b p.2) 0 * greenH (F p.1) (F p.2) -
      max (-b p.1) 0 * max (b p.2) 0 * greenH (F p.1) (F p.2) +
      max (-b p.1) 0 * max (-b p.2) 0 * greenH (F p.1) (F p.2) := by
    intro p
    have h1 := max_sub_max_neg (b p.1)
    have h2 := max_sub_max_neg (b p.2)
    calc b p.1 * b p.2 * greenH (F p.1) (F p.2)
        = (max (b p.1) 0 - max (-b p.1) 0) * (max (b p.2) 0 - max (-b p.2) 0) *
            greenH (F p.1) (F p.2) := by rw [h1, h2]
      _ = _ := by ring
  have hint : Integrable (fun p : ℂ × ℂ => b p.1 * b p.2 * greenH (F p.1) (F p.2))
      (volume.prod volume) :=
    (((i1.sub i2).sub i3).add i4).congr (ae_of_all _ fun p => (hpt p).symm)
  have i12 : Integrable (fun p : ℂ × ℂ =>
      max (b p.1) 0 * max (b p.2) 0 * greenH (F p.1) (F p.2) -
      max (b p.1) 0 * max (-b p.2) 0 * greenH (F p.1) (F p.2)) (volume.prod volume) :=
    i1.sub i2
  have i123 : Integrable (fun p : ℂ × ℂ =>
      max (b p.1) 0 * max (b p.2) 0 * greenH (F p.1) (F p.2) -
      max (b p.1) 0 * max (-b p.2) 0 * greenH (F p.1) (F p.2) -
      max (-b p.1) 0 * max (b p.2) 0 * greenH (F p.1) (F p.2)) (volume.prod volume) :=
    i12.sub i3
  have hprod : ∫ x, ∫ y, b x * b y * greenH (F x) (F y) =
      ∫ p, b p.1 * b p.2 * greenH (F p.1) (F p.2) ∂(volume.prod volume) :=
    (integral_prod _ hint).symm
  unfold kernelCov2
  simp only
  rw [e1, e2, e3, e4, hprod, integral_congr_ae (ae_of_all _ hpt), integral_add i123 i4,
    integral_sub i12 i3, integral_sub i1 i2]

/-! ## Pathwise conditions without the log hypothesis -/

/-- Barriers and strip decay (no log hypothesis). -/
def TameCondNA (W : ℝ → ℝ) (T : ℝ) (ρ : ℂ → ℝ) : Prop :=
  Barrier W T ρ ∧ ∃ C η : ℝ, 0 ≤ C ∧ 0 < η ∧ ∀ t : ℝ, 1 ≤ t →
    pushTest W T (fun z => ENNReal.ofReal (ρ z)) {z | z.im < Real.exp (-Real.exp t)} ≤
      ENNReal.ofReal (C * t ^ (-(1 + η)))

/-- All pathwise conditions for one test function (no log hypothesis). -/
def GoodPathNA (κ : ℝ) (W : ℝ → ℝ) (T : ℝ) (ρ : TestFun H) : Prop :=
  (TameCondNA W T ρ.1 ∧ TameCondNA W T fun z => -ρ.1 z) ∧
    Integrable fun z => ρ.1 z * hTfwd κ W T z

section Congr

variable {W W' : ℝ → ℝ} {T : ℝ}

theorem tameCondNA_of_eqOn (hW : Continuous W) (hW' : Continuous W') (hT : 0 ≤ T)
    (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r) {ρ : ℂ → ℝ} (hc : TameCondNA W T ρ) :
    TameCondNA W' T ρ := by
  unfold TameCondNA Barrier at *
  simp only [pushTest_eq_of_eqOn hW hW' hT h, isForwardSol_iff_of_eqOn h] at hc
  exact hc

theorem goodPathNA_of_eqOn (hW : Continuous W) (hW' : Continuous W') (hT : 0 ≤ T)
    (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r) {κ : ℝ} {ρ : TestFun H} (hg : GoodPathNA κ W T ρ) :
    GoodPathNA κ W' T ρ :=
  ⟨⟨tameCondNA_of_eqOn hW hW' hT h hg.1.1, tameCondNA_of_eqOn hW hW' hT h hg.1.2⟩, by
    rw [← hTfwd_eq_of_eqOn hW hW' hT h]; exact hg.2⟩

end Congr

theorem TameCondNA.tame {W : ℝ → ℝ} {T : ℝ} {a : ℂ → ℝ} (h : TameCondNA W T a)
    (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 < T)
    (hreg : Continuous a ∧ HasCompactSupport a ∧ tsupport a ⊆ H) :
    TameBdry (pushTest W T fun z => ENNReal.ofReal (a z)) := by
  obtain ⟨ha, hac, haH⟩ := hreg
  obtain ⟨⟨R, hR, hKR, hp, hm⟩, C, η, hC, hη, hS⟩ := h
  obtain ⟨M, hM⟩ := ha.bounded_above_of_compact_support hac
  exact PushTameNA.tameBdry_pushTest hW hW0 hT ha.measurable.ennreal_ofReal
    (c := ENNReal.ofReal M) ENNReal.ofReal_lt_top
    (fun z => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸
      hM z))) hac haH
    (fun z hz => by rw [image_eq_zero_of_notMem_tsupport hz, ENNReal.ofReal_zero])
    hR hKR hp hm hC hη hS

/-- Pathwise formula for the pairing of the right-hand field (no GFF input needed). -/
theorem cond_pair_NA (κ : ℝ) {W : ℝ → ℝ} {T : ℝ} (ρ : TestFun H)
    (hi : Integrable fun z => ρ.1 z * hTfwd κ W T z) (x : FieldSample) :
    pairRaw (Yfwd κ W T x) ρ.1 = (∫ z, ρ.1 z * hTfwd κ W T z) +
      (evalReg x (pushTest W T fun z => ENNReal.ofReal (ρ.1 z)) -
        evalReg x (pushTest W T fun z => ENNReal.ofReal (-ρ.1 z))) := by
  rw [pairRaw_Yfwd, pairRaw_ofFun_of_integrable (tf_continuous ρ) hi]

section Path

variable {T : ℝ}

/-- **PUSH without admissibility.** The energy of `ν_T^±` is `E_T(ρ)`. -/
theorem kernelCov2_pushTest_NA (κ : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) {a : ℂ → ℝ}
    (ha : Measurable a)
    (hA : TameBdry (pushTest (drive κ (Bc hT) f) T fun z => ENNReal.ofReal (a z)))
    (hB : TameBdry (pushTest (drive κ (Bc hT) f) T fun z => ENNReal.ofReal (-a z))) :
    kernelCov2 greenH (pushTest (drive κ (Bc hT) f) T (fun z => ENNReal.ofReal (a z)),
        pushTest (drive κ (Bc hT) f) T fun z => ENNReal.ofReal (-a z))
      (pushTest (drive κ (Bc hT) f) T (fun z => ENNReal.ofReal (a z)),
        pushTest (drive κ (Bc hT) f) T fun z => ENNReal.ofReal (-a z)) =
      Efwd (drive κ (Bc hT) f) T a := by
  have hD := measurableSet_sec κ hT f
  have i11 := integrable_greenH_tame hA hA
  have i12 := integrable_greenH_tame hA hB
  have i21 := integrable_greenH_tame hB hA
  have i22 := integrable_greenH_tame hB hB
  rw [pushTest_eq_FmF_neg κ hT f a] at i12 i21 i22 ⊢
  rw [pushTest_eq_FmF κ hT f a] at i11 i12 i21 ⊢
  rw [kernelCov2_map_greenH_NA (measurable_FmF_sec κ hT f) (ha.indicator hD) i11 i12 i21 i22]
  unfold Efwd
  congr 1
  funext x
  congr 1
  funext y
  by_cases hx : x ∈ H \ fwdHull (drive κ (Bc hT) f) T
  · by_cases hy : y ∈ H \ fwdHull (drive κ (Bc hT) f) T
    · simp only [indicator_of_mem hx, indicator_of_mem hy, Pi.one_apply]
      rw [FmF_eq κ hT (p := (f, x)) hx, FmF_eq κ hT (p := (f, y)) hy]
      ring
    · simp [indicator_of_notMem hy]
  · simp [indicator_of_notMem hx]

/-- **Conditional characteristic function** for a fixed driver path, without admissibility. -/
theorem cond_charFun_path_NA (κ : ℝ) (hT : 0 < T) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → FieldSample} (hX : IsZeroBoundaryGFFH X P) (ρ : TestFun H)
    (f : C(Icc (0 : ℝ) T, ℝ)) (hW0 : drive κ (Bc hT.le) f 0 = 0)
    (hg : GoodPathNA κ (drive κ (Bc hT.le) f) T ρ) :
    ∫ ω, cexp (I * (pairRaw (Yfwd κ (drive κ (Bc hT.le) f) T (X ω)) ρ.1 : ℂ)) ∂P =
      cexp (I * ((∫ z, ρ.1 z * hTfwd κ (drive κ (Bc hT.le) f) T z : ℝ) : ℂ) -
        (Efwd (drive κ (Bc hT.le) f) T ρ.1 : ℂ) / 2) := by
  have hW := continuous_drive_Bc κ hT.le f
  have hA := hg.1.1.tame hW hW0 hT (tf_reg ρ)
  have hB := hg.1.2.tame hW hW0 hT (tf_reg_neg ρ)
  simp_rw [cond_pair_NA κ ρ hg.2]
  simp_rw [ofReal_add, mul_add, Complex.exp_add]
  rw [integral_const_mul, integral_cexp_evalReg_sub_NA hX hA hB,
    kernelCov2_pushTest_NA κ hT.le f (tf_continuous ρ).measurable hA hB, ← Complex.exp_add]
  congr 1
  ring

/-- Linearity of the pairing for a fixed driver path, almost surely in the GFF. -/
theorem lin_path_NA (κ : ℝ) (hT : 0 < T) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} (hX : IsZeroBoundaryGFFH X P) (f : C(Icc (0 : ℝ) T, ℝ))
    (hW0 : drive κ (Bc hT.le) f 0 = 0) (ρ₁ ρ₂ ρ₃ : TestFun H) (a : ℝ)
    (h : ∀ z, ρ₃.1 z = a * ρ₁.1 z + ρ₂.1 z) (g₁ : GoodPathNA κ (drive κ (Bc hT.le) f) T ρ₁)
    (g₂ : GoodPathNA κ (drive κ (Bc hT.le) f) T ρ₂)
    (g₃ : GoodPathNA κ (drive κ (Bc hT.le) f) T ρ₃) :
    ∀ᵐ ω ∂P, pairRaw (Yfwd κ (drive κ (Bc hT.le) f) T (X ω)) ρ₃.1 =
      a * pairRaw (Yfwd κ (drive κ (Bc hT.le) f) T (X ω)) ρ₁.1 +
        pairRaw (Yfwd κ (drive κ (Bc hT.le) f) T (X ω)) ρ₂.1 := by
  have hW := continuous_drive_Bc κ hT.le f
  have hD := measurableSet_sec κ hT.le f
  have hR : ∀ ρ : TestFun H, GoodPathNA κ (drive κ (Bc hT.le) f) T ρ → ∀ᵐ ω ∂P,
      RegConv (X ω) ((tdens ((H \ fwdHull (drive κ (Bc hT.le) f) T).indicator ρ.1)).map
        fun z => FmF κ hT.le (f, z)) ∧
      RegConv (X ω) ((tdens fun z => -((H \ fwdHull (drive κ (Bc hT.le) f) T).indicator
        ρ.1 z)).map fun z => FmF κ hT.le (f, z)) := fun ρ hg => by
    have t1 := hg.1.1.tame hW hW0 hT (tf_reg ρ)
    have t2 := hg.1.2.tame hW hW0 hT (tf_reg_neg ρ)
    rw [pushTest_eq_FmF] at t1
    rw [pushTest_eq_FmF_neg] at t2
    filter_upwards [ae_regConv_NA hX t1, ae_regConv_NA hX t2] with ω r1 r2 using ⟨r1, r2⟩
  filter_upwards [hR ρ₁ g₁, hR ρ₂ g₂, hR ρ₃ g₃] with ω r1 r2 r3
  rw [cond_pair_NA κ ρ₁ g₁.2, cond_pair_NA κ ρ₂ g₂.2, cond_pair_NA κ ρ₃ g₃.2]
  rw [pushTest_eq_FmF_neg κ hT.le f ρ₁.1, pushTest_eq_FmF_neg κ hT.le f ρ₂.1,
    pushTest_eq_FmF_neg κ hT.le f ρ₃.1, pushTest_eq_FmF κ hT.le f ρ₁.1,
    pushTest_eq_FmF κ hT.le f ρ₂.1, pushTest_eq_FmF κ hT.le f ρ₃.1,
    lin_map_evalReg (measurable_FmF_sec κ hT.le f)
      ((tf_continuous ρ₁).measurable.indicator hD) ((tf_continuous ρ₂).measurable.indicator hD)
      ((tf_continuous ρ₃).measurable.indicator hD) a
      (fun z => by
        by_cases hz : z ∈ H \ fwdHull (drive κ (Bc hT.le) f) T <;> simp [hz, h z])
      r1.1 r1.2 r2.1 r2.2 r3.1 r3.2,
    integral_lin_int g₁.2 g₂.2 a h]
  ring

end Path

/-! ## AS-1 without admissibility -/

theorem linear_Yc_NA (κ : ℝ) {T : ℝ} (hT : 0 < T) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsZeroBoundaryGFFH X P)
    {g : Ω → C(Icc (0 : ℝ) T, ℝ)} (hg : Measurable g) (hind : IndepFun g X P)
    (hW0 : ∀ᵐ ω ∂P, drive κ (Bc hT.le) (g ω) 0 = 0)
    (hgood : ∀ ρ : TestFun H, ∀ᵐ ω ∂P, GoodPathNA κ (drive κ (Bc hT.le) (g ω)) T ρ) :
    LinearPairingH (fun ω => Yfwd κ (drive κ (Bc hT.le) (g ω)) T (X ω)) P := by
  intro ρ₁ ρ₂ ρ₃ a h
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hE : MeasurableSet {p : C(Icc (0 : ℝ) T, ℝ) × FieldSample |
      pairRaw (Yfwd κ (drive κ (Bc hT.le) p.1) T p.2) ρ₃.1 =
        a * pairRaw (Yfwd κ (drive κ (Bc hT.le) p.1) T p.2) ρ₁.1 +
          pairRaw (Yfwd κ (drive κ (Bc hT.le) p.1) T p.2) ρ₂.1} :=
    measurableSet_eq_fun (measurable_pair_Yc κ hT.le ρ₃.1)
      ((measurable_const.mul (measurable_pair_Yc κ hT.le ρ₁.1)).add
        (measurable_pair_Yc κ hT.le ρ₂.1))
  refine ae_indep_ae hg hXm hind hE ?_
  filter_upwards [hW0, hgood ρ₁, hgood ρ₂, hgood ρ₃] with ω h0 g1 g2 g3
  exact lin_path_NA κ hT hX (g ω) h0 ρ₁ ρ₂ ρ₃ a h g1 g2 g3

theorem charFun_rhs_fwd_NA (κ T : ℝ) (hT : 0 < T) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample)
    (hB : IsBrownianReal B P) (hX : IsZeroBoundaryGFFH X P) (hind : IndepFun (pathOf B) X P)
    (ρ : TestFun H)
    (hTame : ∀ᵐ ω ∂P, TameCondNA (drive κ B ω) T ρ.1 ∧ TameCondNA (drive κ B ω) T fun z => -ρ.1 z)
    (hInt : ∀ᵐ ω ∂P, Integrable fun z => ρ.1 z * hTfwd κ (drive κ B ω) T z) :
    ∫ ω, cexp (I * (pairRaw (ofFun (hTfwd κ (drive κ B ω) T) +
        coordChangeOn (X ω) (fwdMap (drive κ B ω) T) (H \ fwdHull (drive κ B ω) T)) ρ.1 : ℂ))
        ∂P =
      ∫ ω, cexp (I * ((∫ z, ρ.1 z * hTfwd κ (drive κ B ω) T z : ℝ) : ℂ) -
        (Efwd (drive κ B ω) T ρ.1 : ℂ) / 2) ∂P := by
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := exists_good_version hB
  have hdrive : ∀ᵐ ω ∂P, drive κ B' ω = drive κ B ω :=
    hB'eq.mono fun ω h => funext fun t => by simp [drive, h]
  have hind' : IndepFun (pathOf B') X P :=
    hind.congr (hB'eq.mono fun ω h => (funext fun t => (h t).symm : pathOf B ω = pathOf B' ω))
      (ae_eq_refl _)
  set g := pathC T B' hB'c with hg_def
  have hgm : Measurable g := measurable_pathC T hB'm hB'c
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hig : IndepFun g X P := indepFun_pathC T hind' hB'c
  have hdc : ∀ ω, Continuous (drive κ B' ω) := fun ω =>
    continuous_const.mul ((hB'c ω).comp continuous_real_toNNReal)
  have hag : ∀ ω, ∀ r ∈ Icc (0 : ℝ) T, drive κ B' ω r = drive κ (Bc hT.le) (g ω) r :=
    drive_eq_drive_Bc κ hT.le hB'c
  have hWc : ∀ ω, Continuous (drive κ (Bc hT.le) (g ω)) := fun ω =>
    continuous_drive_Bc κ hT.le (g ω)
  have hB0 : ∀ᵐ ω ∂P, drive κ (Bc hT.le) (g ω) 0 = 0 := by
    filter_upwards [hB.eval_zero_ae_eq_zero, hB'eq] with ω h0 h'
    rw [← hag ω 0 ⟨le_rfl, hT.le⟩]
    simp [drive, h' 0, h0]
  set G : C(Icc (0 : ℝ) T, ℝ) × FieldSample → ℂ :=
    fun p => cexp (I * (pairRaw (Yfwd κ (drive κ (Bc hT.le) p.1) T p.2) ρ.1 : ℂ)) with hG_def
  have hGm : Measurable G := Complex.measurable_exp.comp (measurable_const.mul
    (Complex.measurable_ofReal.comp (measurable_pair_Yc κ hT.le ρ.1)))
  have hGb : ∀ p, ‖G p‖ ≤ 1 := fun p => by
    simp [G, Complex.norm_exp, Complex.mul_re]
  calc _ = ∫ ω, G (g ω, X ω) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hdrive] with ω h
        show cexp (I * (pairRaw (Yfwd κ (drive κ B ω) T (X ω)) ρ.1 : ℂ)) = G (g ω, X ω)
        rw [← h, Yfwd_eq_of_eqOn (hdc ω) (hWc ω) hT.le (hag ω)]
    _ = ∫ ω, (∫ ω', G (g ω, X ω') ∂P) ∂P := integral_indep hgm hXm hig hGm hGb
    _ = ∫ ω, cexp (I * ((∫ z, ρ.1 z * hTfwd κ (drive κ (Bc hT.le) (g ω)) T z : ℝ) : ℂ) -
          (Efwd (drive κ (Bc hT.le) (g ω)) T ρ.1 : ℂ) / 2) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hTame, hInt, hdrive, hB0] with ω ht hi hd h0
        rw [← hd] at ht hi
        have hgood : GoodPathNA κ (drive κ B' ω) T ρ := ⟨ht, hi⟩
        exact cond_charFun_path_NA κ hT hX ρ (g ω) h0
          (goodPathNA_of_eqOn (hdc ω) (hWc ω) hT.le (hag ω) hgood)
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [hdrive] with ω h
        show _ = cexp (I * ((∫ z, ρ.1 z * hTfwd κ (drive κ B ω) T z : ℝ) : ℂ) -
          (Efwd (drive κ B ω) T ρ.1 : ℂ) / 2)
        rw [← h, hTfwd_eq_of_eqOn (hdc ω) (hWc ω) hT.le (hag ω),
          Efwd_eq_of_eqOn (hdc ω) (hWc ω) hT.le (hag ω)]

theorem rhs_fwd_version_NA (κ T : ℝ) (hT : 0 < T) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsZeroBoundaryGFFH X P) (hind : IndepFun (pathOf B) X P)
    (hTame : ∀ ρ : TestFun H,
      ∀ᵐ ω ∂P, TameCondNA (drive κ B ω) T ρ.1 ∧ TameCondNA (drive κ B ω) T fun z => -ρ.1 z)
    (hInt : ∀ ρ : TestFun H,
      ∀ᵐ ω ∂P, Integrable fun z => ρ.1 z * hTfwd κ (drive κ B ω) T z) :
    ∃ Y : Ω → FieldSample,
      (∀ᵐ ω ∂P, Y ω = ofFun (hTfwd κ (drive κ B ω) T) +
        coordChangeOn (X ω) (fwdMap (drive κ B ω) T) (H \ fwdHull (drive κ B ω) T)) ∧
      (∀ ρ : TestFun H, Measurable fun ω => pairRaw (Y ω) ρ.1) ∧ LinearPairingH Y P := by
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := exists_good_version hB
  have hdrive : ∀ᵐ ω ∂P, drive κ B' ω = drive κ B ω :=
    hB'eq.mono fun ω h => funext fun t => by simp [drive, h]
  have hind' : IndepFun (pathOf B') X P :=
    hind.congr (hB'eq.mono fun ω h => (funext fun t => (h t).symm : pathOf B ω = pathOf B' ω))
      (ae_eq_refl _)
  set g := pathC T B' hB'c with hg_def
  have hgm : Measurable g := measurable_pathC T hB'm hB'c
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hig : IndepFun g X P := indepFun_pathC T hind' hB'c
  have hdc : ∀ ω, Continuous (drive κ B' ω) := fun ω =>
    continuous_const.mul ((hB'c ω).comp continuous_real_toNNReal)
  have hag : ∀ ω, ∀ r ∈ Icc (0 : ℝ) T, drive κ B' ω r = drive κ (Bc hT.le) (g ω) r :=
    drive_eq_drive_Bc κ hT.le hB'c
  have hWc : ∀ ω, Continuous (drive κ (Bc hT.le) (g ω)) := fun ω =>
    continuous_drive_Bc κ hT.le (g ω)
  have hB0 : ∀ᵐ ω ∂P, drive κ (Bc hT.le) (g ω) 0 = 0 := by
    filter_upwards [hB.eval_zero_ae_eq_zero, hB'eq] with ω h0 h'
    rw [← hag ω 0 ⟨le_rfl, hT.le⟩]
    simp [drive, h' 0, h0]
  have hmeas : ∀ ρ : TestFun H,
      Measurable fun ω => pairRaw (Yfwd κ (drive κ (Bc hT.le) (g ω)) T (X ω)) ρ.1 :=
    fun ρ => by
      have h := (measurable_pair_Yc κ hT.le ρ.1).comp (hgm.prodMk hXm)
      exact h
  refine ⟨fun ω => Yfwd κ (drive κ (Bc hT.le) (g ω)) T (X ω), ?_, hmeas, ?_⟩
  · filter_upwards [hdrive] with ω h
    show _ = Yfwd κ (drive κ B ω) T (X ω)
    rw [← h, Yfwd_eq_of_eqOn (hdc ω) (hWc ω) hT.le (hag ω)]
  · refine linear_Yc_NA κ hT hX hgm hig hB0 fun ρ => ?_
    filter_upwards [hTame ρ, hInt ρ, hdrive] with ω ht hi hd
    rw [← hd] at ht hi
    exact goodPathNA_of_eqOn (hdc ω) (hWc ω) hT.le (hag ω) ⟨ht, hi⟩

/-! ## AS-4 -/

section Standing

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Barriers and strip decay hold almost surely, for `κ ∈ (0,4]`. -/
theorem ae_tameCondNA (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {T : ℝ}
    (hT : 0 < T) {a : ℂ → ℝ} (hac : HasCompactSupport a)
    (hS : ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      PushTame.pushTest (drive κ B ω) T (fun z => ENNReal.ofReal (a z))
        {z | z.im < Real.exp (-Real.exp t)} ≤ ENNReal.ofReal (C * t ^ (-(1 + (1 : ℝ))))) :
    ∀ᵐ ω ∂P, TameCondNA (drive κ B ω) T a := by
  obtain ⟨Rk, hRk⟩ := hac.isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt Rk
  filter_upwards [ClockInt.ae_barriers hB hBm hBc hκ hκ4 hT.le, hS] with ω hbar hSω
  obtain ⟨-, hbar⟩ := hbar
  obtain ⟨C, hC, hSC⟩ := hSω
  refine ⟨⟨(n : ℝ) + 1, by positivity, fun z hz => ?_, (hbar n).1, (hbar n).2⟩,
    C, 1, hC, one_pos, hSC⟩
  exact (Complex.abs_re_le_norm z).trans_lt ((hRk z hz).trans_lt (hn.trans (lt_add_one _)))

end Standing

theorem chiC_four : chiC 4 = 0 := by
  have h : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  simp only [chiC, h]; norm_num

/-- **Theorem 1.1, main statement, `κ ∈ (0,4]`.** -/
theorem theorem1_1_main_proof : theorem1_1_main := by
  intro κ T hκ hκ4 hT Ω _ P _ B X hB hX hind
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := exists_good_version hB
  have hB' : IsPreBrownianReal B' P :=
    hB.toIsPreBrownianReal.congr fun t => hB'eq.mono fun ω h => (h t).symm
  have hdrive : ∀ᵐ ω ∂P, drive κ B' ω = drive κ B ω :=
    hB'eq.mono fun ω h => funext fun t => by simp [drive, h]
  have hTT : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal _ hT.le
  have hTame : ∀ ρ : TestFun H, ∀ᵐ ω ∂P,
      TameCondNA (drive κ B ω) T ρ.1 ∧ TameCondNA (drive κ B ω) T fun z => -ρ.1 z := by
    intro ρ
    have hS := PushTameAS.ae_strip_decay_testFun hB' hB'm hB'c hκ hκ4 T.toNNReal ρ
    rw [hTT] at hS
    have h1 := ae_tameCondNA hB' hB'm hB'c hκ hκ4 hT (tf_reg ρ).2.1 (hS.mono fun _ h => h.1)
    have h2 := ae_tameCondNA hB' hB'm hB'c hκ hκ4 hT (tf_reg_neg ρ).2.1
      (hS.mono fun _ h => h.2)
    filter_upwards [h1, h2, hdrive] with ω e1 e2 hd
    rw [← hd]
    exact ⟨e1, e2⟩
  have hInt : ∀ ρ : TestFun H, ∀ᵐ ω ∂P,
      Integrable fun z => ρ.1 z * hTfwd κ (drive κ B ω) T z := by
    intro ρ
    filter_upwards [ClockInt.ae_integrable_mul_hTfwd hB' hB'm hB'c hκ hκ4 hT.le ρ, hdrive]
      with ω h hd
    rw [← hd]
    exact h
  obtain ⟨Y, hYae, hYm, hYlin⟩ := rhs_fwd_version_NA κ T hT hB hX hind hTame hInt
  rw [fieldLaw_congr_ae (hYae.mono fun ω h => h.symm)]
  refine fieldLaw_eq_of_charFun (measurable_pairRaw_lhs_fwd κ hX) hYm (linear_lhs_fwd κ hX)
    hYlin fun ρ => ?_
  have hclock : ∀ᵐ ω ∂P, chiC κ = 0 ∨ ∫⁻ a in H \ fwdHull (drive κ B ω) T,
      ENNReal.ofReal |ρ.1 a| * ENNReal.ofReal (FwdClock.fwdClock (drive κ B ω) T a) < ⊤ := by
    rcases hκ4.lt_or_eq with hlt | heq
    · obtain ⟨Cρ, hCρ⟩ := (tf_reg ρ).1.bounded_above_of_compact_support (tf_reg ρ).2.1
      have hcl := ClockInt.ae_lintegral_clock_lt_top' hB' hB'm hB'c hκ hlt hT.le
        (φ := fun a => ENNReal.ofReal |ρ.1 a|)
        ((continuous_abs.comp (tf_reg ρ).1).measurable.ennreal_ofReal)
        (cφ := ENNReal.ofReal Cρ) ENNReal.ofReal_lt_top (fun z => ENNReal.ofReal_le_ofReal (by
          have := hCρ z; rwa [Real.norm_eq_abs] at this))
        (K := tsupport ρ.1) (tf_reg ρ).2.1 (tf_reg ρ).2.2 (fun z hz => by
          simp [image_eq_zero_of_notMem_tsupport hz])
      filter_upwards [hcl, hdrive] with ω h hd
      rw [← hd]
      exact Or.inr h
    · exact ae_of_all _ fun _ => Or.inl (heq ▸ chiC_four)
  have hYc : ∫ ω, cexp (I * (pairRaw (Y ω) ρ.1 : ℂ)) ∂P =
      ∫ ω, cexp (I * (pairRaw (ofFun (hTfwd κ (drive κ B ω) T) +
        coordChangeOn (X ω) (fwdMap (drive κ B ω) T) (H \ fwdHull (drive κ B ω) T)) ρ.1 : ℂ))
        ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hYae] with ω h
    rw [h]
  rw [charFun_lhs_fwd κ P X hX ρ, hYc,
    charFun_rhs_fwd_NA κ T hT P B X hB hX hind ρ (hTame ρ) (hInt ρ),
    MainMart.main_mart hB hκ hκ4 hT ρ hclock]

end Thm11MainFull
end QuantumZipper
