import QuantumZipper.Proofs.Zipper.AreaWinMkPath
import QuantumZipper.Proofs.Zipper.AreaWinMkCov

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-WINMARKOV (A1): the hypotheses `WinHypC` for the free field normalized at `fc(0,R)`

Source: S. Sheffield, M. Wang, arXiv:1605.06171, proof of Theorem 1.1, p. 9 (the window factor
`G = C(N) sup e^{γ B_t − γ² t/2} − 1` is centred, has a bounded second moment, is independent of
`h_{2^{-j/N}}(z)` and of everything at points `2 · 2^{-j/N}` away), with B. Duplantier,
S. Sheffield (2011), §3.1 (Markov property of circle averages).

For a set `S` of points `z` with `‖z‖ + 1 ≤ R` and `Im z ≥ d ≥ 2^{-j/N}`, and the field
normalized by `X(fc(0,R)) = 0`:
* `mkG_scalar`: for `Y ≥ 0` with `c E Y = 1`, `E Y² < ∞`: `cY − 1` is in `L²`, centred, with
  `E (cY − 1)² ≤ 2 c² E Y² + 2`.
* `mkWinHypC`: `WinHypC` for `U = mkU`, `G = mkG c (mkPhi γ X N b j)`, `δ = 2 · 2^{-j/N}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Real
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

open GaussTK LQGDimension.ExistAsm

/-! ## The scalar part -/

theorem mkG_scalar {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ≥0∞} (hY : Measurable Y) {c : ℝ} (h1 : ∫⁻ ω, Y ω ∂P ≠ ∞)
    (hc : c * (∫⁻ ω, Y ω ∂P).toReal = 1) (h2 : ∫⁻ ω, Y ω ^ 2 ∂P ≠ ∞) :
    MemLp (fun ω => c * (Y ω).toReal - 1) 2 P ∧ ∫ ω, (c * (Y ω).toReal - 1) ∂P = 0 ∧
      ∫ ω, (c * (Y ω).toReal - 1) ^ 2 ∂P ≤ 2 * c ^ 2 * (∫⁻ ω, Y ω ^ 2 ∂P).toReal + 2 := by
  have hi1 : Integrable (fun ω => (Y ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hY.aemeasurable h1
  have hi2 : Integrable (fun ω => (Y ω).toReal ^ 2) P := by
    have := integrable_toReal_of_lintegral_ne_top (hY.pow_const 2).aemeasurable h2
    simpa [ENNReal.toReal_pow] using this
  have hm : MemLp (fun ω => (Y ω).toReal) 2 P :=
    (memLp_two_iff_integrable_sq hY.ennreal_toReal.aestronglyMeasurable).2 hi2
  have hmG : MemLp (fun ω => c * (Y ω).toReal - 1) 2 P := (hm.const_mul c).sub (memLp_const 1)
  refine ⟨hmG, ?_, ?_⟩
  · rw [integral_sub (hi1.const_mul c) (integrable_const 1), integral_const_mul,
      integral_toReal hY.aemeasurable (ae_lt_top hY h1), hc]
    simp
  · have hsq : ∫ ω, (Y ω).toReal ^ 2 ∂P = (∫⁻ ω, Y ω ^ 2 ∂P).toReal := by
      rw [← integral_toReal (hY.pow_const 2).aemeasurable (ae_lt_top (hY.pow_const 2) h2)]
      simp [ENNReal.toReal_pow]
    calc ∫ ω, (c * (Y ω).toReal - 1) ^ 2 ∂P
        ≤ ∫ ω, (2 * c ^ 2 * (Y ω).toReal ^ 2 + 2) ∂P := by
          refine integral_mono hmG.integrable_sq ((hi2.const_mul _).add (integrable_const _))
            fun ω => ?_
          nlinarith [sq_nonneg (c * (Y ω).toReal + 1)]
      _ = _ := by
          rw [integral_add (hi2.const_mul _) (integrable_const _), integral_const_mul, hsq]
          simp

/-! ## Measurability -/

theorem measurable_mkF (γ : ℝ) (N : ℕ) (b : Bool) : Measurable (mkF γ N b) := by
  cases b
  · exact measurable_winExpInf γ (swWinSet_countable N)
  · exact measurable_winExpSup γ (swWinSet_countable N)

section Field

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

set_option linter.unusedSectionVars false

theorem mk_measurable_X (hX : IsFreeGFFModConstH X P) : Measurable X :=
  measurable_pi_iff.mpr hX.measurable_coord

theorem mk_measurable_evalReg (hX : IsFreeGFFModConstH X P) (ρ : ℝ) :
    Measurable (fun p : ℂ × Ω => evalReg (X p.2) (foldedCircle p.1 ρ)) := by
  have h1 : Measurable (fun p : ℂ × Ω => (X p.2, p.1)) :=
    ((mk_measurable_X hX).comp measurable_snd).prodMk measurable_fst
  exact Measurable.comp (g := fun q : FieldSample × ℂ => evalReg q.1 (foldedCircle q.2 ρ))
    (f := fun p : ℂ × Ω => (X p.2, p.1)) (AreaOffsets.measurable_evalReg_fc ρ) h1

theorem mk_measurable_U (hX : IsFreeGFFModConstH X P) (N j : ℕ) :
    Measurable (fun p : ℂ × Ω => mkU X N j p.1 p.2) :=
  mk_measurable_evalReg hX _

theorem mk_measurable_G (hX : IsFreeGFFModConstH X P) (γ c : ℝ) (N : ℕ) (b : Bool) (j : ℕ) :
    Measurable (fun p : ℂ × Ω => mkG c (mkPhi γ X N b j) p.1 p.2) := by
  have hfam : Measurable (fun p : ℂ × Ω => mkFam X N j p.1 p.2) :=
    measurable_pi_iff.mpr fun q =>
      (mk_measurable_evalReg hX _).sub (mk_measurable_evalReg hX _)
  exact ((((measurable_mkF γ N b).comp hfam).ennreal_toReal).const_mul c).sub_const 1

theorem mk_measurable_famRaw (hX : IsFreeGFFModConstH X P) (N j : ℕ) (t : ℂ) :
    Measurable (mkFamRaw X N j t) :=
  measurable_pi_iff.mpr fun _ => measurable_fcPairVal hX _

/-! ## Almost sure identifications -/

theorem mk_fam_ae (hX : IsFreeGFFModConstH X P) (N j : ℕ) {t : ℂ} (ht : t ∈ Hbar) :
    mkFam X N j t =ᵐ[P] mkFamRaw X N j t := by
  have : Countable (swWinSet N) := (swWinSet_countable N).to_subtype
  have h : ∀ᵐ ω ∂P, ∀ q : swWinSet N, mkIncrR X N j t q ω = mkIncr X N j t q ω := by
    rw [ae_all_iff]
    intro q
    filter_upwards [AllOffsets.ae_evalReg_fc_eq hX ht (mkRad_pos N j q),
      AllOffsets.ae_evalReg_fc_eq hX ht (winHi_pos N j)] with ω h1 h2
    simp only [mkIncrR, mkIncr, fcPairVal, h1, h2]
  filter_upwards [h] with ω hω
  funext q
  exact hω q

theorem mk_U_ae (hX : IsFreeGFFModConstH X P) {R : ℝ} (h0 : ∀ ω, X ω (foldedCircle 0 R) = 0)
    (N j : ℕ) {t : ℂ} (ht : t ∈ Hbar) :
    mkU X N j t =ᵐ[P] fcPairVal X (t, winHi N j, 0, R) := by
  filter_upwards [AllOffsets.ae_evalReg_fc_eq hX ht (winHi_pos N j)] with ω h
  simp only [mkU, fcPairVal, h, h0 ω, sub_zero]

/-- The window factor as a function of the raw increment path. -/
def mkGfun (γ c : ℝ) (N : ℕ) (b : Bool) (v : swWinSet N → ℝ) : ℝ := c * (mkF γ N b v).toReal - 1

theorem measurable_mkGfun (γ c : ℝ) (N : ℕ) (b : Bool) : Measurable (mkGfun γ c N b) :=
  (((measurable_mkF γ N b).ennreal_toReal).const_mul c).sub_const 1

theorem mk_G_ae (hX : IsFreeGFFModConstH X P) (γ c : ℝ) (N : ℕ) (b : Bool) (j : ℕ) {t : ℂ}
    (ht : t ∈ Hbar) :
    mkG c (mkPhi γ X N b j) t =ᵐ[P] fun ω => mkGfun γ c N b (mkFamRaw X N j t ω) := by
  filter_upwards [mk_fam_ae hX N j ht] with ω hω
  simp only [mkG, mkPhi, mkGfun, hω]

/-- The moments of the window functional are those of SW's Brownian motion. -/
theorem mk_lintegral_F_pow (hX : IsFreeGFFModConstH X P) (γ : ℝ) (N : ℕ) (b : Bool) (j : ℕ)
    {t : ℂ} (ht : winHi N j ≤ t.im) (n : ℕ) :
    ∫⁻ ω, mkF γ N b (mkFamRaw X N j t ω) ^ n ∂P =
      ∫⁻ ω, mkF γ N b (fun q : swWinSet N => swBM q ω) ^ n ∂stdP :=
  lintegral_comp_preBM_eq (isPreBrownianReal_mkIncr hX ht) isBrownianReal_swBM.toIsPreBrownianReal
    (swWinSet_countable N) ((measurable_mkF γ N b).pow_const n)

end Field

end QuantumZipper.E6
