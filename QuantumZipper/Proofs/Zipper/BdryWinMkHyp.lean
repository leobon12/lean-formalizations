import QuantumZipper.Proofs.Zipper.BdryWinMkMarkov

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-W1 (H): `WinHypB` and `BdryWinMarkovData` for the free field normalized at `fc(0,R)`

Source: S. Sheffield, M. Wang, arXiv:1605.06171, proof of Theorem 4.2, pp. 18–19 (the window
factor `C(N) sup e^{γ' B_s − γ'² s/2} − 1` is centred, has a bounded second moment, is
independent of `h_{2^{-j/N}}(x)` and of everything at points `2 · 2^{-j/N}` away), with the
Markov property of semicircle averages (B. Duplantier, S. Sheffield 2011, §6) in the kernel
form of `GaussTK` (`fcPairCov_incr_Zsame`, `fcPairCov_incr_Zfar`, `fcPairCov_incr_incr_far`).

For `S ⊆ ℝ` with `|t| + 1 ≤ R` on `S` and the normalization `X(fc(0,R)) = 0`:
* `bWinHypB`: `WinHypB` for `U = h_{2^{-j/N}}`, `G = c Φ − 1`, `Φ = mkF (γ/√2)` of the
  normalized increment path.
* `bWinMarkovData`: `BdryWinMarkovData` (for all `j`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Real
open scoped Topology NNReal ENNReal

namespace QuantumZipper.F1

open E6 GaussTK LQGDimension.ExistAsm

/-- The raw normalized increment path at `t`. -/
def bFamRaw {Ω : Type} (X : Ω → FieldSample) (N j : ℕ) (t : ℝ) (ω : Ω) : swWinSet N → ℝ :=
  fun q => (√2)⁻¹ * mkIncr X N j (t : ℂ) q ω

/-- The window factor as a function of the raw (unnormalized) increment path. -/
def bGfun (γ c : ℝ) (N : ℕ) (b : Bool) (v : swWinSet N → ℝ) : ℝ :=
  c * (mkF (γ / √2) N b (fun q => (√2)⁻¹ * v q)).toReal - 1

/-- `U`: the coarse value `h_{2^{-j/N}}(t)`. -/
def bU {Ω : Type} (X : Ω → FieldSample) (N j : ℕ) (t : ℝ) (ω : Ω) : ℝ := mkU X N j (t : ℂ) ω

/-- `G = c Φ − 1`. -/
def bG {Ω : Type} (γ c : ℝ) (X : Ω → FieldSample) (N : ℕ) (b : Bool) (j : ℕ) (t : ℝ)
    (ω : Ω) : ℝ :=
  bGfun γ c N b (fun q => mkIncrR X N j (t : ℂ) q ω)

theorem measurable_bGfun (γ c : ℝ) (N : ℕ) (b : Bool) : Measurable (bGfun γ c N b) :=
  ((((measurable_mkF (γ / √2) N b).comp
    (measurable_pi_iff.mpr fun q => (measurable_pi_apply q).const_mul _)).ennreal_toReal).const_mul
      c).sub_const 1

/-- The index family of `(U t, U u, increments at u)` for real centres. -/
def bFarIdx {κ : Type} (t u r R : ℝ) (ρ' : κ → ℝ) : Unit ⊕ (Unit ⊕ κ) → FcIdx :=
  Sum.elim (fun _ => ((t : ℂ), r, 0, R))
    (Sum.elim (fun _ => ((u : ℂ), r, 0, R)) fun k => ((u : ℂ), ρ' k, (u : ℂ), r))

section Field

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

set_option linter.unusedSectionVars false

theorem measurable_ofReal_prod : Measurable (fun p : ℝ × Ω => ((p.1 : ℂ), p.2)) :=
  (Complex.measurable_ofReal.comp measurable_fst).prodMk measurable_snd

theorem b_measurable_U (hX : IsFreeGFFModConstH X P) (N j : ℕ) :
    Measurable (fun p : ℝ × Ω => bU X N j p.1 p.2) :=
  Measurable.comp (g := fun p : ℂ × Ω => mkU X N j p.1 p.2)
    (f := fun p : ℝ × Ω => ((p.1 : ℂ), p.2)) (mk_measurable_U hX N j) measurable_ofReal_prod

theorem b_measurable_G (hX : IsFreeGFFModConstH X P) (γ c : ℝ) (N : ℕ) (b : Bool) (j : ℕ) :
    Measurable (fun p : ℝ × Ω => bG γ c X N b j p.1 p.2) := by
  have hq : ∀ q : swWinSet N, Measurable (fun p : ℝ × Ω => mkIncrR X N j (p.1 : ℂ) q p.2) := by
    intro q
    have h1 := mk_measurable_evalReg hX (P := P) (mkRad N j q)
    have h2 := mk_measurable_evalReg hX (P := P) (winHi N j)
    exact Measurable.comp (g := fun p : ℂ × Ω => evalReg (X p.2) (foldedCircle p.1 (mkRad N j q)) -
      evalReg (X p.2) (foldedCircle p.1 (winHi N j)))
      (f := fun p : ℝ × Ω => ((p.1 : ℂ), p.2)) (h1.sub h2) measurable_ofReal_prod
  have hfam : Measurable (fun p : ℝ × Ω => fun q : swWinSet N => mkIncrR X N j (p.1 : ℂ) q p.2) :=
    measurable_pi_iff.mpr hq
  exact Measurable.comp (g := bGfun γ c N b)
    (f := fun p : ℝ × Ω => fun q : swWinSet N => mkIncrR X N j (p.1 : ℂ) q p.2)
    (measurable_bGfun γ c N b) hfam

theorem b_G_ae (hX : IsFreeGFFModConstH X P) (γ c : ℝ) (N : ℕ) (b : Bool) (j : ℕ) (t : ℝ) :
    bG γ c X N b j t =ᵐ[P] fun ω => bGfun γ c N b (mkFamRaw X N j (t : ℂ) ω) := by
  filter_upwards [mk_fam_ae hX N j (ofReal_mem_Hbar t)] with ω hω
  simp only [bG, bGfun]
  have : ∀ q : swWinSet N, mkIncrR X N j (t : ℂ) q ω = mkFamRaw X N j (t : ℂ) ω q :=
    fun q => congrFun hω q
  simp only [this]

theorem b_lintegral_F_pow (hX : IsFreeGFFModConstH X P) (γ : ℝ) (N : ℕ) (b : Bool) (j : ℕ)
    (t : ℝ) (n : ℕ) :
    ∫⁻ ω, mkF (γ / √2) N b (bFamRaw X N j t ω) ^ n ∂P =
      ∫⁻ ω, mkF (γ / √2) N b (fun q : swWinSet N => swBM q ω) ^ n ∂stdP :=
  lintegral_comp_preBM_eq (isPreBrownianReal_bIncr hX N j t)
    isBrownianReal_swBM.toIsPreBrownianReal (swWinSet_countable N)
    ((measurable_mkF (γ / √2) N b).pow_const n)

/-- **`WinHypB` for the normalized free field** (SW pp. 18–19). -/
theorem bWinHypB (hX : IsFreeGFFModConstH X P) {R : ℝ} (hR1 : 1 ≤ R)
    (h0 : ∀ ω, X ω (foldedCircle 0 R) = 0) (γ c : ℝ) (N : ℕ) (b : Bool) (j : ℕ) {S : Set ℝ}
    (hSR : ∀ t ∈ S, |t| + 1 ≤ R)
    (hI1 : ∫⁻ ω, mkF (γ / √2) N b (fun q : swWinSet N => swBM q ω) ∂stdP ≠ ∞)
    (hc : c * (∫⁻ ω, mkF (γ / √2) N b (fun q : swWinSet N => swBM q ω) ∂stdP).toReal = 1)
    (hI2 : ∫⁻ ω, mkF (γ / √2) N b (fun q : swWinSet N => swBM q ω) ^ 2 ∂stdP ≠ ∞) :
    WinHypB P S (2 * winHi N j) (2 * Real.log R)
      (2 * c ^ 2 * (∫⁻ ω, mkF (γ / √2) N b (fun q : swWinSet N => swBM q ω) ^ 2 ∂stdP).toReal
        + 2)
      (fun _ => 2 * Lw N j)
      (fun t => (fcPairCov ((t : ℂ), winHi N j, 0, R) ((t : ℂ), winHi N j, 0, R)).toNNReal)
      (bU X N j) (bG γ c X N b j) := by
  have hr := winHi_pos N j
  have hr1 := winHi_le_one N j
  have hR0 : (0 : ℝ) < R := by linarith
  have hRt : ∀ t ∈ S, |t| + winHi N j ≤ R := fun t ht => by linarith [hSR t ht]
  have hρ : ∀ q : swWinSet N, 0 < mkRad N j q ∧ mkRad N j q ≤ winHi N j :=
    fun q => ⟨mkRad_pos N j q, mkRad_le N j q⟩
  have hs : ∀ t : ℝ, _ := fun t =>
    mkG_scalar (P := P) (Y := fun ω => mkF (γ / √2) N b (bFamRaw X N j t ω)) (c := c)
      ((measurable_mkF (γ / √2) N b).comp (measurable_pi_iff.mpr fun q =>
        (measurable_fcPairVal hX _).const_mul _))
      (by simpa using (b_lintegral_F_pow hX γ N b j t 1).trans_ne (by simpa using hI1))
      (by simpa using (show _ = _ by simpa using b_lintegral_F_pow hX γ N b j t 1) ▸ hc)
      ((b_lintegral_F_pow hX γ N b j t 2).trans_ne hI2)
  have hGe : ∀ t : ℝ, bG γ c X N b j t =ᵐ[P]
      fun ω => c * (mkF (γ / √2) N b (bFamRaw X N j t ω)).toReal - 1 :=
    fun t => b_G_ae hX γ c N b j t
  have hU : ∀ t : ℝ, bU X N j t =ᵐ[P] fcPairVal X ((t : ℂ), winHi N j, 0, R) :=
    fun t => mk_U_ae hX h0 N j (ofReal_mem_Hbar t)
  refine
    { measU := b_measurable_U hX N j
      measG := b_measurable_G hX γ c N b j
      measL := measurable_const
      lawU := fun t _ => (AreaExist.hasLaw_fcPairVal' hX (good_Z (ofReal_mem_Hbar t) hr hR0)).congr
        (hU t)
      varU := ?_, memG := ?_, meanG := ?_, sqG := ?_, indep := ?_, decor := ?_ }
  · intro t ht
    have hn : ‖(t : ℂ)‖ + winHi N j ≤ R := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hRt t ht
    rw [Real.coe_toNNReal', fcPairCov_Z hr hr hn hn, kernelCov_fc_real_sameCenter hr hr, max_self]
    have hL : Real.log (winHi N j) = -(2 * Lw N j) := by
      have := log_one_div_winHi N j
      rw [one_div, Real.log_inv] at this
      linarith
    have hLw : 0 ≤ Lw N j := by unfold Lw; positivity
    have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
    rw [hL]
    exact max_le (by linarith) (by linarith)
  · intro t _
    exact (hs t).1.ae_eq (hGe t).symm
  · intro t _
    rw [integral_congr_ae (hGe t)]
    exact (hs t).2.1
  · intro t _
    rw [integral_congr_ae (g := fun ω => (c * (mkF (γ / √2) N b (bFamRaw X N j t ω)).toReal - 1) ^ 2)
      ((hGe t).mono fun ω h => by rw [h])]
    have h := (hs t).2.2
    rw [b_lintegral_F_pow hX γ N b j t 2] at h
    exact h
  · intro t ht
    have hI := indepFun_fcPair hX
      (fun q : swWinSet N => (⟨((t : ℂ), mkRad N j q, (t : ℂ), winHi N j),
        good_real (mkRad_pos N j q) hr⟩ : {p : FcIdx // p.Good}))
      (fun _ : Unit => (⟨((t : ℂ), winHi N j, 0, R), good_Z (ofReal_mem_Hbar t) hr hR0⟩ :
        {p : FcIdx // p.Good}))
      (fun q _ => fcPairCov_incr_Zsame (hρ q).1 (hρ q).2 (hRt t ht))
    have hI2 := hI.comp (measurable_bGfun γ c N b) (measurable_pi_apply ())
    refine hI2.congr ((b_G_ae hX γ c N b j t).symm) (hU t).symm
  · intro t ht u hu htu
    have hg : ∀ k, (bFarIdx t u (winHi N j) R (fun q : swWinSet N => mkRad N j q) k).Good := by
      rintro (_ | _ | k)
      · exact good_Z (ofReal_mem_Hbar t) hr hR0
      · exact good_Z (ofReal_mem_Hbar u) hr hR0
      · exact good_real (mkRad_pos N j k) hr
    have hI := indepFun_fcPair hX
      (fun q : swWinSet N => (⟨((t : ℂ), mkRad N j q, (t : ℂ), winHi N j),
        good_real (mkRad_pos N j q) hr⟩ : {p : FcIdx // p.Good}))
      (fun k => (⟨_, hg k⟩ : {p : FcIdx // p.Good})) (by
        rintro q (_ | _ | k)
        · exact fcPairCov_incr_Zsame (hρ q).1 (hρ q).2 (hRt t ht)
        · exact fcPairCov_incr_Zfar (hρ q).1 (hρ q).2 hr (hRt t ht) (hRt u hu) (by linarith)
        · exact fcPairCov_incr_incr_far (hρ q).1 (hρ q).2 (hρ k).1 (hρ k).2 (by linarith))
    have hφ : Measurable (fun v : Unit ⊕ (Unit ⊕ swWinSet N) → ℝ =>
        (v (Sum.inl ()), v (Sum.inr (Sum.inl ())),
          bGfun γ c N b (fun k => v (Sum.inr (Sum.inr k))))) :=
      (measurable_pi_apply _).prodMk ((measurable_pi_apply _).prodMk
        ((measurable_bGfun γ c N b).comp (measurable_pi_iff.mpr fun k => measurable_pi_apply _)))
    have hI2 := hI.comp (measurable_bGfun γ c N b) hφ
    refine hI2.congr (b_G_ae hX γ c N b j t).symm ?_
    filter_upwards [hU t, hU u, b_G_ae hX γ c N b j u] with ω h1 h2 h3
    simp only [Function.comp_apply, bFarIdx, Sum.elim_inl, Sum.elim_inr, h1, h2, h3]
    rfl

/-- **`BdryWinMarkovData` for the free field normalized at `fc(0,R)`** (SW pp. 18–19). -/
theorem bWinMarkovData (hX : IsFreeGFFModConstH X P) {R : ℝ} (hR1 : 1 ≤ R)
    (h0 : ∀ ω, X ω (foldedCircle 0 R) = 0) (γ c : ℝ) (hc0 : 0 ≤ c) (N : ℕ) (b : Bool)
    (hI1 : ∫⁻ ω, mkF (γ / √2) N b (fun q : swWinSet N => swBM q ω) ∂stdP ≠ ∞)
    (hc : c * (∫⁻ ω, mkF (γ / √2) N b (fun q : swWinSet N => swBM q ω) ∂stdP).toReal = 1)
    (hI2 : ∫⁻ ω, mkF (γ / √2) N b (fun q : swWinSet N => swBM q ω) ^ 2 ∂stdP ≠ ∞)
    {S : Set ℝ} (hSR : ∀ t ∈ S, |t| + 1 ≤ R) :
    BdryWinMarkovData P X γ c N (fun x j u => bWin γ N b x j u) S := by
  refine ⟨2 * Real.log R,
    2 * c ^ 2 * (∫⁻ ω, mkF (γ / √2) N b (fun q : swWinSet N => swBM q ω) ^ 2 ∂stdP).toReal + 2,
    0, bU X N, fun j => bG γ c X N b j,
    fun j t => (fcPairCov ((t : ℂ), winHi N j, 0, R) ((t : ℂ), winHi N j, 0, R)).toNNReal,
    by positivity, fun j _ => bWinHypB hX hR1 h0 γ c N b j hSR hI1 hc hI2, ?_⟩
  intro j _
  filter_upwards [RegSample.ae_isRegularSample hX] with ω hreg u _
  obtain ⟨heq, hfin⟩ := bWin_eq_of_regular hreg γ N b j u
  have hA := GoodSample.bdryDens_nonneg γ (X ω) (winHi_pos N j) u
  have e : bG γ c X N b j u ω =
      c * (mkF (γ / √2) N b (fun q => (√2)⁻¹ * mkPath (X ω) N j (u : ℂ) q)).toReal - 1 := rfl
  rw [e]
  refine ⟨?_, ?_, ?_⟩
  · rw [bdryDens, winHi_rpow, ← Real.exp_add]
    congr 1
    simp only [bU, mkU]
    ring
  · have := mul_nonneg hc0 (ENNReal.toReal_nonneg
      (a := mkF (γ / √2) N b (fun q => (√2)⁻¹ * mkPath (X ω) N j (u : ℂ) q)))
    linarith
  · rw [heq, show 1 + (c * (mkF (γ / √2) N b
          (fun q => (√2)⁻¹ * mkPath (X ω) N j (u : ℂ) q)).toReal - 1) =
        c * (mkF (γ / √2) N b (fun q => (√2)⁻¹ * mkPath (X ω) N j (u : ℂ) q)).toReal by ring,
      ENNReal.ofReal_mul hA, ENNReal.ofReal_mul hc0, ENNReal.ofReal_toReal hfin]
    ring

end Field

end QuantumZipper.F1
