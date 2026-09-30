import QuantumZipper.Proofs.Zipper.AreaWinMkHyp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-WINMARKOV (A2): `WinMarkovData` for the free field normalized at a large circle

Source: S. Sheffield, M. Wang, arXiv:1605.06171, proof of Theorem 1.1, p. 9, and the Markov
property of circle averages (B. Duplantier, S. Sheffield 2011, §3.1).

For the free field normalized by `X(fc(0,R)) = 0` and a compact `S ⊆ ℍ` with `‖z‖ + 1 ≤ R` on
`S`, every grid disc `B_{2^{-j/N}}(z)`, `z ∈ S`, lies inside `B(0,R)`, so the normalizing
variable is harmonic there and no exceptional strip is needed (`T_j = ∅`).

* `mkWinHypC`: the hypotheses `WinHypC` for `U = h_{2^{-j/N}}`, `G = c Φ − 1`.
* `mkWinMarkovData`: `WinMarkovData` for the window `mkWin γ N b` (sup for `b = true`, inf for
  `b = false`), given the constant `c` with `c · E Φ_{BM} = 1` and `E Φ_{BM}² < ∞`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Real
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

open GaussTK LQGDimension.ExistAsm

theorem log_one_div_winHi (N j : ℕ) : Real.log (1 / winHi N j) = 2 * Lw N j := by
  rw [one_div, Real.log_inv, winHi, Real.log_rpow two_pos, Lw]
  ring

theorem winHi_rpow (N j : ℕ) (a : ℝ) : winHi N j ^ a = rexp (-(2 * a) * Lw N j) := by
  rw [Real.rpow_def_of_pos (winHi_pos N j)]
  have h := log_one_div_winHi N j
  rw [one_div, Real.log_inv] at h
  congr 1
  linear_combination (-a) * h

section Field

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- **`WinHypC` for the normalized free field** (SW p. 9, DS §3.1). -/
theorem mkWinHypC (hX : IsFreeGFFModConstH X P) {R : ℝ} (hR1 : 1 ≤ R)
    (h0 : ∀ ω, X ω (foldedCircle 0 R) = 0) (γ c : ℝ) (N : ℕ) (b : Bool) (j : ℕ) {S : Set ℂ}
    {d : ℝ} (hd : 0 < d) (hd1 : 2 * d ≤ 1) (hSd : ∀ z ∈ S, d ≤ z.im)
    (hSR : ∀ z ∈ S, ‖z‖ + 1 ≤ R) (hj : winHi N j ≤ d)
    (hI1 : ∫⁻ ω, mkF γ N b (fun q : swWinSet N => swBM q ω) ∂stdP ≠ ∞)
    (hc : c * (∫⁻ ω, mkF γ N b (fun q : swWinSet N => swBM q ω) ∂stdP).toReal = 1)
    (hI2 : ∫⁻ ω, mkF γ N b (fun q : swWinSet N => swBM q ω) ^ 2 ∂stdP ≠ ∞) :
    WinHypC P S (2 * winHi N j) (2 * Real.log R - Real.log (2 * d))
      (2 * c ^ 2 * (∫⁻ ω, mkF γ N b (fun q : swWinSet N => swBM q ω) ^ 2 ∂stdP).toReal + 2)
      (fun _ => Lw N j)
      (fun t => (fcPairCov (t, winHi N j, 0, R) (t, winHi N j, 0, R)).toNNReal)
      (mkU X N j) (mkG c (mkPhi γ X N b j)) := by
  have hr := winHi_pos N j
  have hrz : ∀ z ∈ S, winHi N j ≤ z.im := fun z hz => hj.trans (hSd z hz)
  have hzH : ∀ z ∈ S, z ∈ Hbar := fun z hz => AreaExist.mem_Hbar_of_le_im hr (hrz z hz)
  have hr1 : winHi N j ≤ 1 := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hoff : ∀ z ∈ S, mkOff R z (winHi N j) := fun z hz => Or.inl (by linarith [hSR z hz])
  have hρ : ∀ q : swWinSet N, 0 < mkRad N j q ∧ mkRad N j q ≤ winHi N j :=
    fun q => ⟨mkRad_pos N j q, mkRad_le N j q⟩
  have hs : ∀ z ∈ S, _ := fun z hz =>
    mkG_scalar (P := P) (Y := fun ω => mkF γ N b (mkFamRaw X N j z ω)) (c := c)
      ((measurable_mkF γ N b).comp (mk_measurable_famRaw hX N j z))
      (by simpa using (mk_lintegral_F_pow hX γ N b j (hrz z hz) 1).trans_ne (by simpa using hI1))
      (by simpa using (show _ = _ by simpa using mk_lintegral_F_pow hX γ N b j (hrz z hz) 1) ▸ hc)
      ((mk_lintegral_F_pow hX γ N b j (hrz z hz) 2).trans_ne hI2)
  refine
    { measU := mk_measurable_U hX N j
      measG := mk_measurable_G hX γ c N b j
      measL := measurable_const
      lawU := fun t ht => (AreaExist.hasLaw_fcPairVal' hX (good_Z (hzH t ht) hr hR0)).congr
        (mk_U_ae hX h0 N j (hzH t ht))
      varU := ?_, memG := ?_, meanG := ?_, sqG := ?_, indep := ?_, decor := ?_ }
  · intro t ht
    have := AreaOffsets.var_zVc_le hr hr1 (hrz t ht) (by linarith [hSR t ht]) hd hd1 (hSd t ht)
      hR1
    rw [log_one_div_winHi] at this
    linarith
  · intro t ht
    exact (hs t ht).1.ae_eq (mk_G_ae hX γ c N b j (hzH t ht)).symm
  · intro t ht
    rw [integral_congr_ae (mk_G_ae hX γ c N b j (hzH t ht))]
    exact (hs t ht).2.1
  · intro t ht
    rw [integral_congr_ae (g := fun ω => (mkGfun γ c N b (mkFamRaw X N j t ω)) ^ 2)
      ((mk_G_ae hX γ c N b j (hzH t ht)).mono fun ω h => by rw [h])]
    have h := (hs t ht).2.2
    rw [mk_lintegral_F_pow hX γ N b j (hrz t ht) 2] at h
    exact h
  · intro t ht
    have hI := mk_indepFun_self hX (ι := swWinSet N) (fun q => mkRad N j q) hρ hr (hrz t ht) hR0
      (hoff t ht)
    have hI2 := hI.comp (measurable_mkGfun γ c N b) (measurable_pi_apply ())
    exact hI2.congr (mk_G_ae hX γ c N b j (hzH t ht)).symm (mk_U_ae hX h0 N j (hzH t ht)).symm
  · intro t ht u hu htu
    have hI := mk_indepFun_far hX (ι := swWinSet N) (κ := swWinSet N) (fun q => mkRad N j q)
      (fun q => mkRad N j q) hρ hρ hr (hrz t ht) (hrz u hu) hR0 (hoff t ht) htu
    have hφ : Measurable (fun v : Unit ⊕ (Unit ⊕ swWinSet N) → ℝ =>
        (v (Sum.inl ()), v (Sum.inr (Sum.inl ())),
          mkGfun γ c N b (fun k => v (Sum.inr (Sum.inr k))))) :=
      (measurable_pi_apply _).prodMk ((measurable_pi_apply _).prodMk
        ((measurable_mkGfun γ c N b).comp (measurable_pi_iff.mpr fun k => measurable_pi_apply _)))
    have hI2 := hI.comp (measurable_mkGfun γ c N b) hφ
    refine hI2.congr (mk_G_ae hX γ c N b j (hzH t ht)).symm ?_
    filter_upwards [mk_U_ae hX h0 N j (hzH t ht), mk_U_ae hX h0 N j (hzH u hu),
      mk_G_ae hX γ c N b j (hzH u hu)] with ω h1 h2 h3
    simp only [Function.comp_apply, mkFarIdx, Sum.elim_inl, Sum.elim_inr, h1, h2, h3]
    rfl

/-- **`WinMarkovData` for the free field normalized at `fc(0,R)`** (SW p. 9), with `T_j = ∅`. -/
theorem mkWinMarkovData (hX : IsFreeGFFModConstH X P) {R : ℝ} (hR1 : 1 ≤ R)
    (h0 : ∀ ω, X ω (foldedCircle 0 R) = 0) (γ c : ℝ) (hc0 : 0 ≤ c) {N : ℕ} (hN : 1 ≤ N)
    (b : Bool)
    (hI1 : ∫⁻ ω, mkF γ N b (fun q : swWinSet N => swBM q ω) ∂stdP ≠ ∞)
    (hc : c * (∫⁻ ω, mkF γ N b (fun q : swWinSet N => swBM q ω) ∂stdP).toReal = 1)
    (hI2 : ∫⁻ ω, mkF γ N b (fun q : swWinSet N => swBM q ω) ^ 2 ∂stdP ≠ ∞)
    {S : Set ℂ} (hS : IsCompact S) (hSH : S ⊆ H) (hSR : ∀ z ∈ S, ‖z‖ + 1 ≤ R) :
    WinMarkovData P X γ c N (fun x j w => mkWin γ N b x j w) S := by
  obtain ⟨d, hd, hd1, hSd⟩ := AreaExist.exists_im_lower_bound hS hSH
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (awt_winHi_lt hN hd)
  refine ⟨2 * Real.log R - Real.log (2 * d),
    2 * c ^ 2 * (∫⁻ ω, mkF γ N b (fun q : swWinSet N => swBM q ω) ^ 2 ∂stdP).toReal + 2,
    j₀, fun _ => ∅, mkU X N, fun j => mkG c (mkPhi γ X N b j),
    fun j t => (fcPairCov (t, winHi N j, 0, R) (t, winHi N j, 0, R)).toNNReal,
    by positivity, fun _ => MeasurableSet.empty, ?_, ?_, ?_⟩
  · intro j hj
    rw [diff_empty]
    exact mkWinHypC hX hR1 h0 γ c N b j hd hd1 hSd hSR (hj₀ j hj).le hI1 hc hI2
  · intro j hj
    filter_upwards [RegSample.ae_isRegularSample hX] with ω hreg w hw
    have hwH : w ∈ Hbar := AreaExist.mem_Hbar_of_le_im hd (hSd w hw)
    obtain ⟨heq, hfin⟩ := mkWin_eq_of_regular hreg γ N b j hwH
    have hA : 0 ≤ areaDens γ (X ω) (winHi N j) w := by
      unfold areaDens
      exact mul_nonneg (Real.rpow_nonneg (winHi_pos N j).le _) (Real.exp_pos _).le
    have e : mkG c (mkPhi γ X N b j) w ω =
        c * (mkF γ N b (fun q => mkPath (X ω) N j w q)).toReal - 1 := rfl
    rw [e]
    refine ⟨?_, ?_, ?_⟩
    · rw [areaDens, winHi_rpow, ← Real.exp_add]
      congr 1
      simp only [mkU]
      ring
    · have := mul_nonneg hc0 (ENNReal.toReal_nonneg (a := mkF γ N b (fun q => mkPath (X ω) N j w q)))
      linarith
    · rw [heq, show 1 + (c * (mkF γ N b (fun q => mkPath (X ω) N j w q)).toReal - 1) =
          c * (mkF γ N b (fun q => mkPath (X ω) N j w q)).toReal by ring,
        ENNReal.ofReal_mul hA, ENNReal.ofReal_mul hc0, ENNReal.ofReal_toReal hfin]
      ring
  · simp only [inter_empty, Measure.restrict_empty, lintegral_zero_measure, lintegral_zero,
      tsum_zero]
    exact ENNReal.zero_ne_top

end Field

end QuantumZipper.E6
