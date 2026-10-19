import GaussianLQG.Uniform.Star.Holder
import GaussianLQG.Uniform.InverseMoments.Unconditional

/-!
# Route U, step U15 (★), part 3: the inverse half

The inverse half of the ledger statement `star_bound` (`blueprint/phaseB/uniform-ledger.tex`,
U15; audit B-0b, M-2 (b)). Pathwise (`sepInf_inv_lfppDist_le`): if `|h*_ε − φ| ≤ s` on
`V_R = boxOut R`, `K ⊆ boxIn R` and `0 < δ ≤ 1`, then

  `I_X(K, δ)⁻¹ ≤ e^{ξ s} · c / min_{𝓡} L_φ`,   `X = c⁻¹ D^ε_g`,

where `𝓡` is the family of strips `RS (k δ) j`, `j ∈ shortJ (k δ) b`, `b ∈ blockSet K (k δ)`, of
the U13 packet (`Uniform.kDelta`, `Uniform.blockSet`), and `L_φ` the short-way crossing length.

Proof: the planar part of U13 for the weight `h*_ε` (`Uniform.min_strips_le_lfppDOn`, any weight)
gives `D^ε_g(z, w) ≥ min_𝓡 L_{h*_ε}`; every strip lies in its box `\hat P` (`RS_subset_hatBox`),
which lies in `V_R` (`hatBox_subset_boxOut`, `k(δ) ≥ 2`), so the comparison of weights on the
strips gives `L_φ ≤ e^{ξ s} L_{h*_ε}`. The global distance is finite, since
`D^ε_g ≤ e^{ξ s} D_φ(·, ·; V_R) < ∞` (`V_R` convex, `φ` continuous), so the `toReal` in
`lfppDist` is exact.

Probabilistic (`inv_half`, U-form): as in the Hölder half, AM–GM gives
`I^{-p} ≤ e^{2pξ S_n} + (λ_n / min_𝓡 L_{φ_{0,n}[W'_n]})^{2p}`; the first term is bounded through
the Gaussian tail of `S_n` (U14), the second by U13 at order `2p` applied at the noise `W'_n`
(`Uniform.inv_moment_unif_holds`, proved, U-form) with `λ_n(W'_n) = λ_n(W)`. For `δ > 1` the
bound at `δ` follows from the bound at `1` (`sepInf_inv_anti`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace GaussianLQG
namespace StarBound

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

/-! ### The strips lie in `\hat P`, and `\hat P` in the outer box -/

/-- Every short strip `R_i^S(P)` of a block `P` lies in its box `\hat P`. -/
theorem RS_subset_hatBox {K : ℕ} {b : ℤ × ℤ} {j : Circle × ℂ} (hj : j ∈ T20D.shortJ K b) :
    T20D.RS K j ⊆ T20D.hatBox K b := by
  classical
  rintro _ ⟨x, hx, rfl⟩
  simp only [MarkedRect.toSet, rectAB, Complex.mem_reProdIm, mem_Icc, zero_add] at hx
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  simp only [T20D.shortJ, Finset.mem_insert, Finset.mem_singleton] at hj
  simp only [T20D.hatBox, Complex.mem_reProdIm, mem_Icc, T20D.mot_apply]
  generalize (2 : ℝ)⁻¹ ^ K = r at hp hj ⊢
  rcases hj with rfl | rfl | rfl | rfl
  · simp only [Circle.coe_one, one_mul, Complex.add_re, Complex.add_im, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  · simp only [Circle.coe_mul, coe_circI, Complex.I_mul_I, neg_one_mul, Complex.add_re,
      Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  · simp only [coe_circI, Complex.add_re, Complex.add_im, Complex.I_mul_re, Complex.I_mul_im,
      Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  · simp only [Circle.coe_inv, coe_circI, Complex.inv_I, neg_mul, Complex.add_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im, Complex.I_mul_re, Complex.I_mul_im, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

/-- For `k ≥ 1`, the box `\hat P` of a block of level `k` meeting `K₀ ⊆ boxIn R` lies in
`boxOut R`. -/
theorem hatBox_subset_boxOut {K₀ : Set ℂ} {R : ℝ} (hK₀ : K₀ ⊆ Uniform.boxIn R) {k : ℕ}
    (hk : 1 ≤ k) {b : ℤ × ℤ} (hb : b ∈ Uniform.blockSet K₀ k) :
    T20D.hatBox k b ⊆ Uniform.boxOut R := by
  obtain ⟨y, hyb, hyK⟩ := hb
  obtain ⟨hyre, hyim⟩ := hK₀ hyK
  simp only [T20.dyBlock, Complex.mem_reProdIm, mem_Icc] at hyb
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hyb
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  have hh : (2 : ℝ)⁻¹ ^ k ≤ 2⁻¹ := by
    calc (2 : ℝ)⁻¹ ^ k ≤ (2 : ℝ)⁻¹ ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ = 2⁻¹ := pow_one _
  intro z hz
  simp only [T20D.hatBox, Complex.mem_reProdIm, mem_Icc] at hz
  obtain ⟨⟨z1, z2⟩, z3, z4⟩ := hz
  rw [abs_le] at hyre hyim
  refine ⟨abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩⟩ <;> nlinarith

/-! ### The pathwise inverse bound -/

/-- **Pathwise inverse comparison.** If `|h*_ε − φ| ≤ s` on `V_R = boxOut R`, with `φ`
continuous, `K ⊆ boxIn R`, `0 < δ ≤ 1`, `ξ ≥ 0` and `c > 0`, then
`I_X(K, δ)⁻¹ ≤ e^{ξ s} · c / min_𝓡 L_φ` for `X = c⁻¹ D^ε_g`. -/
theorem sepInf_inv_lfppDist_le {ξ ε c : ℝ} (hξ : 0 ≤ ξ) (hc : 0 < c) {g : DistC}
    {φ : ℂ → ℝ} (hφ : Continuous φ) {R : ℝ} {K : Set ℂ} (hK : K ⊆ Uniform.boxIn R) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {s : ℝ}
    (hs : ∀ x ∈ Uniform.boxOut R, |heatMollify ε g x - φ x| ≤ s) :
    (sepInf (fun q => c⁻¹ * lfppDist ξ ε g q) K δ)⁻¹ ≤
      ENNReal.ofReal (Real.exp (ξ * s)) * (ENNReal.ofReal c /
        ⨅ b ∈ Uniform.blockSet K (Uniform.kDelta δ), ⨅ j ∈ T20D.shortJ (Uniform.kDelta δ) b,
          crossLenIn ξ φ (T20D.RS (Uniform.kDelta δ) j) (T20D.RS₁ (Uniform.kDelta δ) j)
            (T20D.RS₂ (Uniform.kDelta δ) j)) := by
  set k := Uniform.kDelta δ with hk
  set f : ℂ → ℝ := heatMollify ε g with hf
  set E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (ξ * s)) with hE
  have hE0 : E ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hEt : E ≠ ⊤ := ENNReal.ofReal_ne_top
  have hk2 : 1 ≤ k := le_trans (by norm_num) (Uniform.two_le_kDelta hδ hδ1)
  set mφ : ℝ≥0∞ := ⨅ b ∈ Uniform.blockSet K k, ⨅ j ∈ T20D.shortJ k b,
    crossLenIn ξ φ (T20D.RS k j) (T20D.RS₁ k j) (T20D.RS₂ k j) with hmφ
  -- the comparison on the strips: `E⁻¹ min L_φ ≤ min L_f`
  have hstrip : E⁻¹ * mφ ≤ ⨅ b ∈ Uniform.blockSet K k, ⨅ j ∈ T20D.shortJ k b,
      crossLenIn ξ f (T20D.RS k j) (T20D.RS₁ k j) (T20D.RS₂ k j) := by
    refine le_iInf₂ fun b hb => le_iInf₂ fun j hj => ?_
    have hsub : T20D.RS k j ⊆ Uniform.boxOut R :=
      (RS_subset_hatBox hj).trans (hatBox_subset_boxOut hK hk2 hb)
    have hcmp : crossLenIn ξ φ (T20D.RS k j) (T20D.RS₁ k j) (T20D.RS₂ k j) ≤
        E * crossLenIn ξ f (T20D.RS k j) (T20D.RS₁ k j) (T20D.RS₂ k j) := by
      have := crossLenIn_le_of_abs_sub_le (ξ := ξ) (f := φ) (g := f) (A := T20D.RS₁ k j)
        (B := T20D.RS₂ k j) (c := s) fun x hx => by
          rw [abs_sub_comm]; exact hs x (hsub hx)
      rwa [abs_of_nonneg hξ] at this
    calc E⁻¹ * mφ ≤ E⁻¹ * crossLenIn ξ φ (T20D.RS k j) (T20D.RS₁ k j) (T20D.RS₂ k j) :=
          mul_le_mul_right (iInf₂_le_of_le b hb (iInf₂_le j hj)) _
      _ ≤ E⁻¹ * (E * crossLenIn ξ f (T20D.RS k j) (T20D.RS₁ k j) (T20D.RS₂ k j)) :=
          mul_le_mul_right hcmp _
      _ = crossLenIn ξ f (T20D.RS k j) (T20D.RS₁ k j) (T20D.RS₂ k j) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hE0 hEt, one_mul]
  refine UniformLimit.sepInf_inv_le fun z hz w hw hzw => ?_
  set D : ℝ≥0∞ := LFPP.lfppDOn ξ f univ z w with hD
  -- the global distance is finite
  have hDfin : D ≠ ⊤ := by
    have hz' := boxIn_subset_boxOut R (hK hz)
    have hw' := boxIn_subset_boxOut R (hK hw)
    have h1 : D ≤ ENNReal.ofReal (Real.exp (|ξ| * s)) * LFPP.lfppDOn ξ φ (Uniform.boxOut R) z w :=
      (lfppDOn_univ_le _ z w).trans (DFGPS.lfppDOn_le_of_abs_sub_le hs z w)
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (lfppDOn_ne_top (ξ := ξ) hφ (convex_boxOut R) hz' hw')) h1
  -- the planar part of U13 and the comparison: `E⁻¹ min L_φ ≤ D`
  have hlow : E⁻¹ * mφ ≤ D :=
    hstrip.trans (Uniform.min_strips_le_lfppDOn ξ f K hδ hz hzw)
  have hval : ENNReal.ofReal (c⁻¹ * lfppDist ξ ε g (z, w)) = ENNReal.ofReal c⁻¹ * D := by
    show ENNReal.ofReal (c⁻¹ * (lfppDistE ξ ε g z w).toReal) = _
    rw [LFPP.lfppDistE_eq_lfppDOn, ENNReal.ofReal_mul (inv_pos.2 hc).le,
      ENNReal.ofReal_toReal hDfin]
  have hc0 : ENNReal.ofReal c⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
  rw [hval]
  calc (ENNReal.ofReal c⁻¹ * D)⁻¹ ≤ (ENNReal.ofReal c⁻¹ * (E⁻¹ * mφ))⁻¹ :=
        ENNReal.inv_le_inv.2 (mul_le_mul_right hlow _)
    _ = ENNReal.ofReal c * (E * mφ⁻¹) := by
        rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl ENNReal.ofReal_ne_top),
          ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 hEt)) (Or.inl (ENNReal.inv_ne_top.2 hE0)),
          inv_inv, ← ENNReal.ofReal_inv_of_pos (inv_pos.2 hc), inv_inv]
    _ = E * (ENNReal.ofReal c / mφ) := by
        rw [div_eq_mul_inv, mul_left_comm]

/-! ### The inverse half of `star_bound` -/

/-- **The inverse half of (★), U-form.** For `p ≥ 1` there is `ξ₀ ∈ (0, 1]` such that for every
compact `K` and `δ > 0` there is `C < ∞` such that, for every white noise `W` on any probability
space, the normalized whole-plane GFF `h = h₀ − (h₀)_1(0)` built from it
(`h₀(φ) = W(testL2 φ)` a.s.), every `ξ ∈ (0, ξ₀]` and every `n`: `E[I_X(K, δ)^{-p}] ≤ C` for
`X = λ_n⁻¹ D^{2⁻ⁿ}_h`, `λ_n = lambdaN ξ W P n`. No hypothesis: U13 is
`Uniform.inv_moment_unif_holds`. -/
theorem inv_half {p : ℝ} (hp : 1 ≤ p) :
    ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ ≤ 1 ∧ ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ, 0 < δ →
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {h₀ : Ω → DistC},
        IsWhiteNoise P W → IsWholePlaneGFF h₀ P →
        (∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (GFFExist.testL2 φ)) →
        ∀ ξ ∈ Set.Ioc (0 : ℝ) ξ₀, ∀ n : ℕ,
          ∫⁻ ω, (sepInf (fun z => (lambdaN ξ W P n)⁻¹ *
              lfppDist ξ ((2 : ℝ)⁻¹ ^ n) (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z) K δ)⁻¹ ^ p
            ∂P ≤ C := by
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨ξq, hξq, hU⟩ := Uniform.inv_moment_unif_holds (2 * p) (by linarith)
  refine ⟨min ξq 1, lt_min hξq one_pos, min_le_right _ _, fun K hK δ hδ => ?_⟩
  set δ' : ℝ := min δ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  obtain ⟨R, -, hKR⟩ := exists_subset_boxIn hK.isBounded
  obtain ⟨C₁₃, hC₁₃, hU'⟩ := hU K hK δ' hδ'0 hδ'1
  obtain ⟨Cv, cv, hCv, hcv, hT⟩ := FieldCmp.heatMollify_phiMN_tail_unif.{0} (isCompact_boxOut R)
  set M : ℝ≥0∞ := ENNReal.ofReal
    (2 * Cv * Real.exp (2 * p + (2 * p + Real.log 2) ^ 2 / (4 * cv))) with hM
  refine ⟨M + C₁₃, ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hC₁₃⟩,
    fun {Ω} _ {P} {W} {h₀} hW hh hae ξ hξ n => ?_⟩
  -- the shifted noise `W'_n`, the field `φ_{0,n}[W'_n]` and the comparison supremum `S_n`
  set a : ℝ := ((2 : ℝ)⁻¹ ^ n) ^ 2 with ha
  have hW' : IsWhiteNoise P (FieldCmp.shiftWN a W) := FieldCmp.isWhiteNoise_shiftWN hW a
  have hφc : ∀ ω, Continuous fun x => phiMN (FieldCmp.shiftWN a W) P 0 n x ω :=
    (isPhiVersion_phiMN hW' (Nat.zero_le n)).cont
  set Y : Ω → ℝ≥0∞ := fun ω => ⨆ z ∈ Uniform.boxOut R, ENNReal.ofReal
    |heatMollify ((2 : ℝ)⁻¹ ^ n) (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z -
      phiMN (FieldCmp.shiftWN a W) P 0 n z ω| with hY
  have htail : ∀ k : ℕ, P {ω | ENNReal.ofReal k ≤ Y ω} ≤
      ENNReal.ofReal (Cv * Real.exp (-cv * (k : ℝ) ^ 2)) :=
    fun k => hT hW hh hae n k (Nat.cast_nonneg k)
  obtain ⟨G, hGm, hGY, hGint⟩ :=
    exists_measurable_exp_majorant P Y (a := 2 * p) (by positivity) hCv.le hcv htail
  have hfin : ∀ᵐ ω ∂P, Y ω ≠ ⊤ := by
    refine ae_iff.2 ?_
    simpa only [ne_eq, not_not] using measure_eq_top_eq_zero_of_tail P Y hcv htail
  -- the normalization
  have hc : 0 < lambdaN ξ W P n := lambdaN_pos hW n
  have hlam : lambdaN ξ (FieldCmp.shiftWN a W) P n = lambdaN ξ W P n :=
    FieldCmp.lambdaN_shiftWN hW a ξ n
  have hξ0 : 0 ≤ ξ := hξ.1.le
  have hξ1 : ξ ≤ 1 := hξ.2.trans (min_le_right _ _)
  -- the U13 bound at `W'_n`
  have h13 := hU' hW' ξ ⟨hξ.1, hξ.2.trans (min_le_left _ _)⟩ n
  rw [hlam] at h13
  set H : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (lambdaN ξ W P n) /
    ⨅ b ∈ Uniform.blockSet K (Uniform.kDelta δ'), ⨅ j ∈ T20D.shortJ (Uniform.kDelta δ') b,
      crossLenIn ξ (fun x => phiMN (FieldCmp.shiftWN a W) P 0 n x ω)
        (T20D.RS (Uniform.kDelta δ') j) (T20D.RS₁ (Uniform.kDelta δ') j)
        (T20D.RS₂ (Uniform.kDelta δ') j) with hH
  -- the pathwise bound
  have hpt : ∀ᵐ ω ∂P, (sepInf (fun z => (lambdaN ξ W P n)⁻¹ *
      lfppDist ξ ((2 : ℝ)⁻¹ ^ n) (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z) K δ)⁻¹ ^ p ≤
      G ω + H ω ^ (2 * p) := by
    filter_upwards [hfin] with ω hω
    have hs : ∀ x ∈ Uniform.boxOut R,
        |heatMollify ((2 : ℝ)⁻¹ ^ n) (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) x -
          phiMN (FieldCmp.shiftWN a W) P 0 n x ω| ≤ (Y ω).toReal :=
      fun x hx => abs_le_toReal_iSup hω hx
    have hI := sepInf_inv_lfppDist_le hξ0 hc (hφc ω) hKR hδ'0 hδ'1 hs
    have hE := ofReal_exp_rpow_le hξ0 hξ1 (ENNReal.toReal_nonneg (a := Y ω)) hp0
    rw [abs_of_nonneg hξ0] at hE
    calc (sepInf (fun z => (lambdaN ξ W P n)⁻¹ *
          lfppDist ξ ((2 : ℝ)⁻¹ ^ n) (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z) K δ)⁻¹ ^ p
        ≤ (ENNReal.ofReal (Real.exp (ξ * (Y ω).toReal)) * H ω) ^ p :=
          ENNReal.rpow_le_rpow ((sepInf_inv_anti _ K (min_le_left δ 1)).trans hI) hp0
      _ ≤ ENNReal.ofReal (Real.exp (ξ * (Y ω).toReal)) ^ (2 * p) + H ω ^ (2 * p) :=
          mul_rpow_le_add _ _ hp0
      _ ≤ G ω + H ω ^ (2 * p) := add_le_add_left (hE.trans (hGY ω hω)) _
  calc ∫⁻ ω, (sepInf (fun z => (lambdaN ξ W P n)⁻¹ *
        lfppDist ξ ((2 : ℝ)⁻¹ ^ n) (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z) K δ)⁻¹ ^ p ∂P
      ≤ ∫⁻ ω, (G ω + H ω ^ (2 * p)) ∂P := lintegral_mono_ae hpt
    _ = ∫⁻ ω, G ω ∂P + ∫⁻ ω, H ω ^ (2 * p) ∂P := lintegral_add_left' hGm.aemeasurable _
    _ ≤ M + C₁₃ := add_le_add hGint h13

end StarBound
end GaussianLQG
