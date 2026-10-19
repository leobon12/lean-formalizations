import HigherDimLFPP.Lower.Lemma53WN

/-!
# Lemma 5.3, the probabilistic core (source §5.2, Steps 2 and 4)

Packet P-L3, target T3 (audit HA4, "Details for later use" D6, Steps 1, 2 and 4).

`LowerData.lp D δ N` is P-L4's construction `lowerParams` (P-L2a's `LParams` with the selector
(5.7)) for the data `D` (definitionally equal to `lowerParams d n N δ (D.vert δ)` when
`D.g = g_n` and `D.e = e_{n,d}`).  For a finitely supported probability `μ = Σ_{z ∈ Sμ} w z δ_z`:

* `lp_tiltMass_le` (Step 4, the gain): with `s ≥ ‖⟨H, ν_{j,μ} - ν_j^N⟩‖` for all `j`,
  `E ∫ e^{ζH} dν_{I,μ} ≤ 1 - δ² w^N + ζ s √(2 log 2(J+1)) + (J+1)(e^{ζ² log(1/q)/2} - 1)`
  (`J + 1` profiles).
  Proof: `eᵗ = 1 + t + R(t)`; the linear term at the selected index is
  `⟨H, ν_I^N⟩ + ⟨H, ν_{I,μ} - ν_I^N⟩ = ⟨H, ν₀^N⟩ - δ^{1/2} max_j stat_j + …` (the selector is the
  argmax, so no independence between `I` and the field is used, source after (5.23)); its
  expectation is `-δ^{1/2} w^N` plus a finite Gaussian maximum; the remainder at the selected
  index is dominated by the sum over all profiles, whose expectation is explicit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

open LQGDimension (gaussianExpectedMax)

variable {d : ℕ} {κ : Rd d → ℝ}

namespace LowerData

variable (D : LowerData d)

/-- **P-L4's construction for the data `D`**: `J + 1` equal-edge polygons `D.vert δ`, `K` edges
of length `q`, `ζ = δ^{3/2}`, root band `(ρq, ρ)`, and the selector (5.7) (P-L4's `selStat`). -/
abbrev lp (δ : ℝ) (N : ℕ) : LParams d :=
  ⟨D.J, D.K, N, δ ^ (3 / 2 : ℝ), D.ρ δ, D.q δ, D.vert δ, selPts D.K N (D.q δ) (D.vert δ),
    selStat D.K N δ (D.q δ) (D.vert δ)⟩

theorem lp_good (hd : 0 < d) (he : 0 ≤ D.e) (hn : 1 ≤ D.n) (hg : 1 ≤ D.g) {δ : ℝ} (hδ : 0 < δ)
    (hδE : δ ^ 2 * D.E₀ ≤ 1) {N : ℕ} (hN : 0 < N) {M₀ c : ℝ}
    (hE : ∀ j, EqualEdgeData D.K δ (D.q δ) D.E₀ M₀ c (D.vert δ j)) : (D.lp δ N).Good :=
  LParams.Good.of_equalEdgeData (P := D.lp δ N) hd D.K_pos hN (mul_pos hδ D.L_pos)
    (D.q_pos he δ) (D.q_lt_one hn hg hδE).le hE
    (fun j => measurable_selStat _ _ _ _ _ j) (fun j => selStat_congr _ _ _ _ _ j)

theorem rpow_three_halves_mul_sqrt {δ : ℝ} (hδ : 0 ≤ δ) :
    δ ^ (3 / 2 : ℝ) * Real.sqrt δ = δ ^ 2 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add' hδ (by norm_num)]
  norm_num

theorem rpow_three_halves_sq {δ : ℝ} (hδ : 0 ≤ δ) : (δ ^ (3 / 2 : ℝ)) ^ 2 = δ ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hδ]
  norm_num

/-- The selector vector is `-δ^{-1/2}(⟨H, ν_j^N⟩ - ⟨H, ν₀^N⟩)` as white-noise pairings. -/
theorem ae_W_selVecR (hκ : IsLFPPKernel κ) {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    {W : WN d → Ω → ℝ} (hW : IsWhiteNoise Pr W) {δ : ℝ} (hρq : 0 < D.ρ δ * D.q δ) (N : ℕ)
    (j : Fin (D.J + 1)) :
    ∀ᵐ ω ∂Pr, W (D.selVecR κ δ N j) ω = -(Real.sqrt δ)⁻¹ *
      (W (bandVecM κ (D.band δ) (D.νR δ N j) 0) ω - W (bandVecM κ (D.band δ) (refM d N) 0) ω) := by
  have hsel : D.selVecR κ δ N j = -(Real.sqrt δ)⁻¹ • (bandVecM κ (D.band δ) (D.νR δ N j) 0 -
      bandVecM κ (D.band δ) (refM d N) 0) := by
    rw [selVecR, band, bandVecM_Ioo_sub hκ hρq, neg_smul]
  filter_upwards [hW.smul_ae (-(Real.sqrt δ)⁻¹) (bandVecM κ (D.band δ) (D.νR δ N j) 0 -
      bandVecM κ (D.band δ) (refM d N) 0),
    hW.sub_ae (bandVecM κ (D.band δ) (D.νR δ N j) 0) (bandVecM κ (D.band δ) (refM d N) 0)]
    with ω h1 h2
  rw [hsel, h1, h2]

/-- **The gain after refinement** (source (5.15), HA4 D6 Step 4): for `μ` a finitely supported
probability and `s` bounding the norms of the white-noise vectors of `⟨H, ν_{j,μ} - ν_j^N⟩`,
`E ∫ e^{ζH} dν_{I,μ} ≤ 1 - δ² w^N + ζ s √(2 log 2(J+1)) + (J+1)(e^{δ³ log(1/q)/2} - 1)`. -/
theorem lp_tiltMass_le (hκ : IsLFPPKernel κ) {δ : ℝ} (hδ : 0 < δ) {N : ℕ}
    (hG : (D.lp δ N).Good) {Sμ : Finset (Rd d)} {w : Rd d → ℝ} (hμ : IsFinProb Sμ w)
    {s : ℝ} (hs0 : 0 ≤ s)
    (hs : ∀ j, ‖bandVecM κ (D.band δ) ((D.lp δ N).replM Sμ w (fun _ => 1) j) (D.νR δ N j)‖ ≤ s) :
    ∫ Y, (D.lp δ N).tiltMass Sμ w Y ∂gLawD κ ((D.lp δ N).stepTris Sμ) ≤
      1 - δ ^ 2 * D.wR κ δ N +
        δ ^ (3 / 2 : ℝ) * (s * Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1)))) +
        ((D.J : ℝ) + 1) * (Real.exp (δ ^ 3 * Real.log (1 / D.q δ) / 2) - 1) := by
  have hW := isWhiteNoise_W₀ d
  have := hW.isProbabilityMeasure
  have hρ : 0 < D.ρ δ := hG.ρ_pos
  have hq0 : 0 < D.q δ := hG.q_pos
  have hq1 : D.q δ ≤ 1 := hG.q_le_one
  have hρq : 0 < D.ρ δ * D.q δ := mul_pos hρ hq0
  have hK : 0 < D.K := hG.K_pos
  have hζ0 : 0 ≤ δ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hδ.le _
  rw [hG.integral_tiltMass_eq_whiteNoise κ hκ hW Sμ w]
  -- notation
  set c : ℝ := (Real.sqrt δ)⁻¹ with hc
  have hcs : Real.sqrt δ * c = 1 := mul_inv_cancel₀ (Real.sqrt_pos.2 hδ).ne'
  set A : Fin (D.J + 1) → (ℕ → ℝ) → ℝ := fun j ω =>
    W₀ d (bandVecM κ (D.band δ) (D.νR δ N j) 0) ω with hA
  set A0 : (ℕ → ℝ) → ℝ := fun ω => W₀ d (bandVecM κ (D.band δ) (refM d N) 0) ω with hA0
  set u : Fin (D.J + 1) → WN d := fun j =>
    bandVecM κ (D.band δ) ((D.lp δ N).replM Sμ w (fun _ => 1) j) (D.νR δ N j) with hu
  set st : Fin (D.J + 1) → (ℕ → ℝ) → ℝ := fun j ω =>
    selStat D.K N δ (D.q δ) (D.vert δ) j (fun z => W₀ d (bandVec κ (D.ρ δ * D.q δ) (D.ρ δ) z) ω)
    with hst
  -- the a.s. identities
  have h1 : ∀ᵐ ω ∂LQGDimension.ExistAsm.stdP, ∀ j,
      (D.lp δ N).linW Sμ w (fun _ => 1) j (fun t => W₀ d (triVec κ t) ω) =
        W₀ d (bandVecM κ (D.band δ) ((D.lp δ N).replM Sμ w (fun _ => 1) j) 0) ω :=
    ae_all_iff.2 fun j => (D.lp δ N).ae_linW_eq hκ hW hρq hμ.1 (fun _ => zero_le_one) j
  have h2 : ∀ᵐ ω ∂LQGDimension.ExistAsm.stdP, ∀ j, st j ω = W₀ d (D.selVecR κ δ N j) ω :=
    D.ae_selStat_eq hκ hW hδ hρq N
  have h3 : ∀ᵐ ω ∂LQGDimension.ExistAsm.stdP, ∀ j,
      W₀ d (D.selVecR κ δ N j) ω = -c * (A j ω - A0 ω) :=
    ae_all_iff.2 fun j => D.ae_W_selVecR hκ hW hρq N j
  have h4 : ∀ᵐ ω ∂LQGDimension.ExistAsm.stdP, ∀ j, W₀ d (u j) ω =
      W₀ d (bandVecM κ (D.band δ) ((D.lp δ N).replM Sμ w (fun _ => 1) j) 0) ω - A j ω := by
    refine ae_all_iff.2 fun j => ?_
    have e : u j = bandVecM κ (D.band δ) ((D.lp δ N).replM Sμ w (fun _ => 1) j) 0 -
        bandVecM κ (D.band δ) (D.νR δ N j) 0 :=
      bandVecM_Ioo_sub (b := D.ρ δ) hκ hρq ((D.lp δ N).replM Sμ w (fun _ => 1) j) (D.νR δ N j)
    rw [e]
    exact hW.sub_ae _ _
  -- the pointwise bound
  set g : (ℕ → ℝ) → ℝ := fun ω => 1 + δ ^ (3 / 2 : ℝ) *
      (A0 ω - Real.sqrt δ * (⨆ j, st j ω) + ⨆ j, |W₀ d (u j) ω|) +
      ∑ j, (D.lp δ N).remW Sμ w (fun _ => 1) j (fun t => W₀ d (triVec κ t) ω) with hg
  have hpt : ∀ᵐ ω ∂LQGDimension.ExistAsm.stdP,
      (D.lp δ N).tiltMass Sμ w (fun t => W₀ d (triVec κ t) ω) ≤ g ω := by
    filter_upwards [h1, h2, h3, h4] with ω e1 e2 e3 e4
    set I := (D.lp δ N).sel (fun t => W₀ d (triVec κ t) ω) with hI
    have hIdef : I = lamax (fun j => st j ω) := rfl
    have hsup : st I ω = ⨆ j, st j ω := by
      rw [hIdef]
      exact (iSup_eq_lamax (fun j => st j ω)).symm
    have hAI : A I ω = A0 ω - Real.sqrt δ * st I ω := by
      rw [e2 I, e3 I]
      have : Real.sqrt δ * (-c * (A I ω - A0 ω)) = -(Real.sqrt δ * c) * (A I ω - A0 ω) := by ring
      rw [this, hcs]
      ring
    have hlin : (D.lp δ N).linW Sμ w (fun _ => 1) I (fun t => W₀ d (triVec κ t) ω) ≤
        A0 ω - Real.sqrt δ * (⨆ j, st j ω) + ⨆ j, |W₀ d (u j) ω| := by
      rw [e1 I, ← hsup]
      have e5 := e4 I
      have hle : W₀ d (u I) ω ≤ ⨆ j, |W₀ d (u j) ω| :=
        (le_abs_self _).trans (le_ciSup (f := fun j => |W₀ d (u j) ω|)
          (Finite.bddAbove_range _) I)
      linarith
    have hrem := (D.lp δ N).remW_sel_le hμ.1 (h := fun _ => 1) (fun _ => le_rfl)
      (fun t => W₀ d (triVec κ t) ω)
    rw [← (D.lp δ N).tiltH_one, (D.lp δ N).tiltH_eq, (D.lp δ N).cdfW_one hμ hK]
    have hζ : (D.lp δ N).ζ = δ ^ (3 / 2 : ℝ) := rfl
    rw [hζ]
    have := mul_le_mul_of_nonneg_left hlin hζ0
    simp only [hg]
    linarith
  have hnn : 0 ≤ᵐ[LQGDimension.ExistAsm.stdP]
      fun ω => (D.lp δ N).tiltMass Sμ w (fun t => W₀ d (triVec κ t) ω) :=
    Eventually.of_forall fun ω => LParams.tiltMass_nonneg hμ.1 _
  -- integrability
  have iA0 : Integrable A0 LQGDimension.ExistAsm.stdP := integrable_W hW _
  have ist : ∀ j, Integrable (st j) LQGDimension.ExistAsm.stdP := fun j =>
    (integrable_W hW (D.selVecR κ δ N j)).congr ((ae_all_iff.1 h2 j).mono fun ω h => h.symm)
  have isup : Integrable (fun ω => ⨆ j, st j ω) LQGDimension.ExistAsm.stdP :=
    integrable_iSup_fintype ist
  have iabs : Integrable (fun ω => ⨆ j, |W₀ d (u j) ω|) LQGDimension.ExistAsm.stdP :=
    integrable_iSup_abs_W₀ u
  have irem : ∀ j, Integrable (fun ω => (D.lp δ N).remW Sμ w (fun _ => 1) j
      (fun t => W₀ d (triVec κ t) ω)) LQGDimension.ExistAsm.stdP := fun j =>
    (D.lp δ N).integrable_remW Sμ w hW _ j
  have iL : Integrable (fun ω => A0 ω - Real.sqrt δ * (⨆ j, st j ω) + ⨆ j, |W₀ d (u j) ω|)
      LQGDimension.ExistAsm.stdP := (iA0.sub' (isup.const_mul _)).fun_add iabs
  have iR : Integrable (fun ω => ∑ j, (D.lp δ N).remW Sμ w (fun _ => 1) j
      (fun t => W₀ d (triVec κ t) ω)) LQGDimension.ExistAsm.stdP :=
    integrable_finsetSum _ fun j _ => irem j
  have ig : Integrable g LQGDimension.ExistAsm.stdP :=
    ((integrable_const 1).fun_add (iL.const_mul _)).fun_add iR
  have eA0 : ∫ ω, A0 ω ∂LQGDimension.ExistAsm.stdP = 0 := hW.integral_eq_zero _
  have est : ∫ ω, (⨆ j, st j ω) ∂LQGDimension.ExistAsm.stdP = D.wR κ δ N :=
    D.integral_iSup_selStat hκ hW hδ hρq N
  have eabs : ∫ ω, (⨆ j, |W₀ d (u j) ω|) ∂LQGDimension.ExistAsm.stdP ≤
      s * Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) := by
    have h := integral_iSup_abs_W_le hW u hs0 hs
    rwa [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at h
  have erem : ∀ j : Fin (D.J + 1), ∫ ω, (D.lp δ N).remW Sμ w (fun _ => 1) j
      (fun t => W₀ d (triVec κ t) ω) ∂LQGDimension.ExistAsm.stdP =
      Real.exp (δ ^ 3 * Real.log (1 / D.q δ) / 2) - 1 := by
    intro j
    rw [(D.lp δ N).integral_remW_one hκ hW hμ hK hρ hq0 hq1 j]
    have hζ2 : (D.lp δ N).ζ ^ 2 = δ ^ 3 := rpow_three_halves_sq hδ.le
    rw [hζ2]
  have eg : ∫ ω, g ω ∂LQGDimension.ExistAsm.stdP =
      1 + δ ^ (3 / 2 : ℝ) * (0 - Real.sqrt δ * D.wR κ δ N +
        ∫ ω, (⨆ j, |W₀ d (u j) ω|) ∂LQGDimension.ExistAsm.stdP) +
      ((D.J : ℝ) + 1) * (Real.exp (δ ^ 3 * Real.log (1 / D.q δ) / 2) - 1) := by
    simp only [hg]
    rw [integral_add ((integrable_const 1).fun_add (iL.const_mul _)) iR,
      integral_add (integrable_const 1) (iL.const_mul _), integral_const_mul,
      integral_add (iA0.sub' (isup.const_mul _)) iabs, integral_sub iA0 (isup.const_mul _),
      integral_const_mul, integral_finsetSum _ fun j _ => irem j, eA0, est,
      Finset.sum_congr rfl fun j _ => erem j, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, integral_const, probReal_univ, one_smul]
    push_cast
    ring
  have hint : ∫ ω, g ω ∂LQGDimension.ExistAsm.stdP ≤
      1 - δ ^ 2 * D.wR κ δ N +
        δ ^ (3 / 2 : ℝ) * (s * Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1)))) +
        ((D.J : ℝ) + 1) * (Real.exp (δ ^ 3 * Real.log (1 / D.q δ) / 2) - 1) := by
    rw [eg]
    have hsq : δ ^ (3 / 2 : ℝ) * Real.sqrt δ = δ ^ 2 := rpow_three_halves_mul_sqrt hδ.le
    have h5 : δ ^ (3 / 2 : ℝ) * (Real.sqrt δ * D.wR κ δ N) = δ ^ 2 * D.wR κ δ N := by
      rw [← mul_assoc, hsq]
    have := mul_le_mul_of_nonneg_left eabs hζ0
    have e6 : δ ^ (3 / 2 : ℝ) * (0 - Real.sqrt δ * D.wR κ δ N +
        ∫ ω, (⨆ j, |W₀ d (u j) ω|) ∂LQGDimension.ExistAsm.stdP) =
        -(δ ^ (3 / 2 : ℝ) * (Real.sqrt δ * D.wR κ δ N)) +
          δ ^ (3 / 2 : ℝ) * ∫ ω, (⨆ j, |W₀ d (u j) ω|) ∂LQGDimension.ExistAsm.stdP := by ring
    rw [e6, h5]
    linarith
  exact (integral_mono_of_nonneg hnn ig hpt).trans hint

end LowerData

end HigherDimLFPP.Lower
