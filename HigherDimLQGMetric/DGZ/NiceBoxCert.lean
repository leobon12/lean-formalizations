import HigherDimLQGMetric.DGZ.NiceBoxConst

/-!
# DGZ §5.1: the certificate `Cert_{j-1}(z)` and the deterministic consequence of `𝒞(x,z)`
(packet L4a1)

Source: [2] Definition 5.3(c), (5.9), Lemma 5.6 (TeX l. 2103–2260); planning audit MA7 D-5.3
("Deterministic consequence (replaces the comparison (5.9) of two random variables)"), G11;
blueprint Definition `r2:def:nice` and the paragraph *Deterministic consequence* after it; L3c3's
certificate API (`aroundCertAt`, `aroundGood_of_aroundCertAt`, `prob_not_aroundCertAt_le`).

* `exp_mul_tStar`: `e^{K^{3/2} √a_j} t* = 2^{-n+(ξQ-θ)a_j}` (the arithmetic of [2] (5.11)).
* `aroundGood_of_niceCEvent` (MA7 D-5.3, deterministic consequence): there is `N₀ = N₀(d, ξ, Q, θ,
  R)` such that whenever `a_{j-1} ≥ N₀`, `a_{j-1} ≤ a_j ≤ n`, `4R ≤ 2/s_{j-1}` and `z = s_{j-1} w ∈
  B₂(0)`, the event `𝒞(s_j u, z)` gives `AroundGood(h_{n-a_j,n}, z, 4R s_{j-1}, 2R s_{j-1}, B₂(0),
  t*)` and `D_{n-a_j,n}(across B_{4s_j}(s_j u) \ B_{2s_j}(s_j u)) > e^{K^{3/2}√a_j} t*`, with `t* =
  e^{ξ s_j*} 2^{-n+(ξQ+θ)a_{j-1}}` (`NiceParams.tStar`).
* `prob_not_niceCert_le` (for L4a2, Lemma 5.6): `P[Cert_i(z) fails] ≤ C e^{-a_i log a_i}` uniformly,
  for every dyadic realization, from L3c3's `prob_not_aroundCertAt_le` applied to the rescaled bands
  (versions of `H_{2^{-m(a_i)},1}` and `H_{2^{-a_i},2^{-m(a_i)}}` for the white noise `W ∘
  V_{z,s_i}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox obox_subset_cbox)

variable {d : ℕ}

/-! ## The threshold `t*` -/

/-- **The arithmetic of [2] (5.11)**: `e^{K^{3/2} √a_j} t* = 2^{-n+(ξQ-θ)a_j}` (`ξ ≠ 0`). -/
theorem exp_mul_tStar (p : NiceParams) (hξ : p.ξ ≠ 0) (j : ℕ) :
    Real.exp ((p.K : ℝ) ^ ((3 : ℝ) / 2) * √(p.a j : ℝ)) * p.tStar j =
      (2 : ℝ) ^ (-(p.n : ℝ) + (p.ξ * p.Q - p.θ) * p.a j) := by
  unfold NiceParams.tStar NiceParams.supLevel
  rw [Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos two_pos, ← mul_assoc, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  field_simp
  ring

theorem tStar_pos (p : NiceParams) (j : ℕ) : 0 < p.tStar j := by
  unfold NiceParams.tStar
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos two_pos _)

/-! ## The deterministic consequence of `𝒞(x,z)` -/

/-- The rescaled cube: the image of `B_{2/s}(-w)` under `v ↦ s w + s v` is `B₂(0)`. -/
theorem image_cube_eq (s : ℝ) (hs : 0 < s) (w : Zd d) (ρ : ℕ) (hρ : s * ρ = 2) :
    (fun v => latPt s w + s • v) '' obox (latPt 1 (-w)) ρ = obox (0 : Rd d) 2 := by
  rw [image_obox_smul_add (latPt s w) (latPt 1 (-w)) hs (ρ : ℝ), hρ]
  congr 1
  ext i
  rw [smul_add_apply, latPt_apply, latPt_apply]
  simp only [Pi.neg_apply, Int.cast_neg, PiLp.zero_apply]
  ring

/-- `z = s_i w ∈ B₂(0)` gives `0 ∈ B_{2/s_i}(-w)`. -/
theorem zero_mem_niceCube (p : NiceParams) (i : ℕ) {w : Zd d}
    (hw : latPt (p.s i) w ∈ obox (0 : Rd d) 2) :
    (0 : Rd d) ∈ obox (latPt 1 (-w)) ((2 ^ (p.n - p.a i + 1) : ℕ) : ℝ) := by
  intro k
  have h1 : |latPt (p.s i) w k - (0 : Rd d) k| < 2 := hw k
  rw [latPt_apply, PiLp.zero_apply, sub_zero, abs_mul, abs_of_pos (p.s_pos i)] at h1
  rw [latPt_apply, PiLp.zero_apply, zero_sub, abs_neg, one_mul, Pi.neg_apply, Int.cast_neg,
    abs_neg]
  have h2 := NiceParams.s_mul_two_pow p i
  have hs := p.s_pos i
  nlinarith

/-- `s_i 2^{-(1-ξQ-θ)a_i} = 2^{-n+(ξQ+θ)a_i}` (`a_i ≤ n`). -/
theorem s_mul_rpow_eq (p : NiceParams) {i : ℕ} (hi : p.a i ≤ p.n) (ξ Q θ : ℝ) :
    p.s i * (2 : ℝ) ^ (-(1 - ξ * Q - θ) * p.a i) =
      (2 : ℝ) ^ (-(p.n : ℝ) + (ξ * Q + θ) * p.a i) := by
  unfold NiceParams.s
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg two_pos.le, ← Real.rpow_add two_pos,
    Nat.cast_sub hi]
  congr 1
  ring

/-- The certificate gives the around-good property of `h_{n-a_i,n}` around `z = s_i w` in `B₂(0)`,
with threshold `t_i = 2^{-n+(ξQ+θ)a_i}`, once `a_i ≥ N₀` (`N₀` from L3c3's
`aroundGood_of_aroundCertAt`). -/
theorem aroundGood_of_niceCert (p : NiceParams) {N₀ : ℕ}
    (hN₀ : ∀ n : ℕ, N₀ ≤ n → ∀ ψ g : Rd d → ℝ, Continuous ψ → Continuous g →
      aroundCertAt p.ξ p.Q p.θ (4 * p.R) (2 * p.R) n ψ g → ∀ (b : Zd d) (ρ : ℕ),
        4 * (p.R : ℝ) ≤ ρ → (0 : Rd d) ∈ obox (latPt 1 b) ρ →
          AroundGood p.ξ (fun z => ψ z + g z) 0 (4 * p.R) (2 * p.R) (obox (latPt 1 b) ρ)
            ((2 : ℝ) ^ (-(1 - p.ξ * p.Q - p.θ) * n)))
    (H : ℕ → Rd d → ℝ) (hc : ∀ q, Continuous (H q)) {i : ℕ} (hN : N₀ ≤ p.a i)
    (hin : p.a i ≤ p.n) (hcube : 4 * p.R ≤ 2 ^ (p.n - p.a i + 1)) {w : Zd d}
    (hw : latPt (p.s i) w ∈ obox (0 : Rd d) 2) (hcert : NiceCert p H i (latPt (p.s i) w)) :
    AroundGood p.ξ (fun y => H p.n y - H (p.n - p.a i) y) (latPt (p.s i) w)
      (p.s i * (4 * p.R)) (p.s i * (2 * p.R)) (obox (0 : Rd d) 2)
      ((2 : ℝ) ^ (-(p.n : ℝ) + (p.ξ * p.Q + p.θ) * p.a i)) := by
  have hs0 : 0 < p.s i := p.s_pos i
  have hcont : ∀ q, Continuous fun v : Rd d => H q (latPt (p.s i) w + p.s i • v) := fun q =>
    (hc q).comp (continuous_const.add (continuous_const_smul _))
  have hρ : (4 * (p.R : ℝ)) ≤ ((2 ^ (p.n - p.a i + 1) : ℕ) : ℝ) := by exact_mod_cast hcube
  have hAG := hN₀ (p.a i) hN (certCoarse p H i (latPt (p.s i) w))
    (certFine p H i (latPt (p.s i) w)) ((hcont _).sub (hcont _)) ((hcont _).sub (hcont _))
    hcert (-w) (2 ^ (p.n - p.a i + 1)) hρ (zero_mem_niceCube p i hw)
  have hsum : (fun v => certCoarse p H i (latPt (p.s i) w) v + certFine p H i (latPt (p.s i) w) v) =
      fun v => (fun y => H p.n y - H (p.n - p.a i) y) (latPt (p.s i) w + p.s i • v) := by
    funext v
    simp only [certCoarse, certFine]
    ring
  rw [hsum] at hAG
  have hAG2 := AroundGood.smul_add (φ := fun y => H p.n y - H (p.n - p.a i) y)
    (latPt (p.s i) w) hs0 hAG
  rwa [smul_zero, add_zero, image_cube_eq (p.s i) hs0 w _ (NiceParams.s_mul_two_pow p i),
    s_mul_rpow_eq p hin p.ξ p.Q p.θ] at hAG2

/-- The deterministic consequence of `𝒞(x,z)` for fixed parameters (see
`aroundGood_of_niceCEvent`). -/
theorem aroundGood_of_niceCEvent_of (p : NiceParams) (hξ : 0 < p.ξ) {N₀ : ℕ}
    (hN₀ : ∀ n : ℕ, N₀ ≤ n → ∀ ψ g : Rd d → ℝ, Continuous ψ → Continuous g →
      aroundCertAt p.ξ p.Q p.θ (4 * p.R) (2 * p.R) n ψ g → ∀ (b : Zd d) (ρ : ℕ),
        4 * (p.R : ℝ) ≤ ρ → (0 : Rd d) ∈ obox (latPt 1 b) ρ →
          AroundGood p.ξ (fun z => ψ z + g z) 0 (4 * p.R) (2 * p.R) (obox (latPt 1 b) ρ)
            ((2 : ℝ) ^ (-(1 - p.ξ * p.Q - p.θ) * n)))
    (H : ℕ → Rd d → ℝ) (hc : ∀ q, Continuous (H q)) {j : ℕ} (hN : N₀ ≤ p.a (j - 1))
    (hjn : p.a (j - 1) ≤ p.n) (hcube : 4 * p.R ≤ 2 ^ (p.n - p.a (j - 1) + 1)) {u w : Zd d}
    (hw : latPt (p.s (j - 1)) w ∈ obox (0 : Rd d) 2) (hC : NiceCEvent p H j u w) :
    AroundGood p.ξ (fun z => H p.n z - H (p.n - p.a j) z) (latPt (p.s (j - 1)) w)
        (4 * p.R * p.s (j - 1)) (2 * p.R * p.s (j - 1)) (obox (0 : Rd d) 2) (p.tStar j) ∧
      Real.exp ((p.K : ℝ) ^ ((3 : ℝ) / 2) * √(p.a j : ℝ)) * p.tStar j <
        acrossDist p.ξ (fun z => H p.n z - H (p.n - p.a j) z) (latPt (p.s j) u)
          (4 * p.s j) (2 * p.s j) := by
  obtain ⟨hacross, hcert, hsup⟩ := hC
  have hAG2 := aroundGood_of_niceCert p hN₀ H hc hN hjn hcube hw hcert
  have hφ : Continuous fun y => H p.n y - H (p.n - p.a j) y := (hc _).sub (hc _)
  have hφ₁ : Continuous fun y => H p.n y - H (p.n - p.a (j - 1)) y := (hc _).sub (hc _)
  have hAG3 := hAG2.mono_field hξ.le hφ₁ hφ (M := p.supLevel j) fun y hy => by
    have hy' : y ∈ cbox (latPt (p.s (j - 1)) w) (4 * p.R * p.s (j - 1)) := by
      intro k
      have := hy.1.1 k
      linarith
    have := hsup y hy'
    linarith
  refine ⟨?_, ?_⟩
  · have e1 : p.s (j - 1) * (4 * (p.R : ℝ)) = 4 * p.R * p.s (j - 1) := by ring
    have e2 : p.s (j - 1) * (2 * (p.R : ℝ)) = 2 * p.R * p.s (j - 1) := by ring
    rw [e1, e2] at hAG3
    exact hAG3
  · rw [exp_mul_tStar p hξ.ne' j]
    exact hacross

/-- **The deterministic consequence of `𝒞(x,z)`** (MA7 D-5.3; blueprint, after Definition
`r2:def:nice`; replaces DGZ (5.9)). There is `N₀ = N₀(d, ξ, Q, θ, R)` such that for all parameters
with these values of `ξ, Q, θ, R`, every family of continuous fields, every `j` with
`N₀ ≤ a_{j-1} ≤ n` and `4R ≤ 2/s_{j-1}`, and every `z = s_{j-1} w ∈ B₂(0)`: on `𝒞(s_j u, z)`,
* `AroundGood(h_{n-a_j,n}, z, 4R s_{j-1}, 2R s_{j-1}, B₂(0), t*)`, and
* `e^{K^{3/2}√a_j} t* < D_{n-a_j,n}(across B_{4s_j}(s_j u) \ B_{2s_j}(s_j u))`. -/
theorem aroundGood_of_niceCEvent (hd : 2 ≤ d) {ξ Q θ : ℝ} (hξ : 0 < ξ) (hθ : 0 < θ) {R : ℕ}
    (hR : 1 ≤ R) :
    ∃ N₀ : ℕ, ∀ p : NiceParams, p.ξ = ξ → p.Q = Q → p.θ = θ → p.R = R →
      ∀ H : ℕ → Rd d → ℝ, (∀ q, Continuous (H q)) → ∀ j : ℕ,
        N₀ ≤ p.a (j - 1) → p.a (j - 1) ≤ p.n →
        4 * R ≤ 2 ^ (p.n - p.a (j - 1) + 1) → ∀ u w : Zd d,
          latPt (p.s (j - 1)) w ∈ obox (0 : Rd d) 2 → NiceCEvent p H j u w →
            AroundGood ξ (fun z => H p.n z - H (p.n - p.a j) z) (latPt (p.s (j - 1)) w)
                (4 * R * p.s (j - 1)) (2 * R * p.s (j - 1)) (obox (0 : Rd d) 2) (p.tStar j) ∧
              Real.exp ((p.K : ℝ) ^ ((3 : ℝ) / 2) * √(p.a j : ℝ)) * p.tStar j <
                acrossDist ξ (fun z => H p.n z - H (p.n - p.a j) z) (latPt (p.s j) u)
                  (4 * p.s j) (2 * p.s j) := by
  have hR0 : (0 : ℝ) < 2 * R := by
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  obtain ⟨N₀, hN₀⟩ := aroundGood_of_aroundCertAt hd hξ hθ (Q := Q) (r₁ := 4 * (R : ℝ))
    (r₂ := 2 * R) hR0 (by linarith)
  refine ⟨N₀, fun p hpξ hpQ hpθ hpR => ?_⟩
  subst hpξ hpQ hpθ hpR
  intro H hc j hN hjn hcube u w hw hC
  exact aroundGood_of_niceCEvent_of p hξ hN₀ H hc hN hjn hcube hw hC

/-! ## The probability of the certificate -/

/-- **`P[Cert_i(z) fails] ≤ C e^{-a_i log a_i}`** (MA7 D-5.6; blueprint Lemma `r2:lem:56`,
*Certificate*): uniformly in the dyadic realization, the parameters with the given `ξ, Q, θ, R`, the
level `i` (with `m(a_i) ≤ a_i ≤ n`) and the point `z`. -/
theorem prob_not_niceCert_le {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {θ : ℝ} (hθ : 0 < θ)
    {R : ℕ} (hR : 1 ≤ R) :
    ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, p.ξ = ξ → p.Q = Q → p.θ = θ → p.R = R →
          ∀ i : ℕ, p.a i ≤ p.n → superScale (p.a i) ≤ p.a i → ∀ z : Rd d,
            P {ω | ¬ NiceCert p (fun q y => H q y ω) i z} ≤
              ENNReal.ofReal (C * Real.exp (-(p.a i : ℝ) * Real.log (p.a i))) := by
  have hR0 : (0 : ℝ) < 2 * R := by
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  obtain ⟨C, hC, hbound⟩ := prob_not_aroundCertAt_le h hθ (r₁ := 4 * (R : ℝ)) (r₂ := 2 * R)
    hR0 (by linarith)
  refine ⟨C, hC, fun Ω _ P W H hH p hpξ hpQ hpθ hpR i hin hsS z => ?_⟩
  have hκ := h.kernel
  set s := p.s i with hsdef
  have hs : 0 < s := p.s_pos i
  set N := p.a i with hN
  set ci := p.certIdx i with hci
  have hci' : ci = p.n - N + superScale N := rfl
  have h1 : p.n - N ≤ ci := by omega
  have h2 : ci ≤ p.n := by omega
  -- the transformed white noise
  set W' : WN d → Ω → ℝ := fun f => W (simL2 (LinearIsometryEquiv.refl ℝ (Rd d)) z hs f)
    with hW'
  have hW'w : IsWhiteNoise P W' := hH.whiteNoise.comp_simL2 _ z hs
  -- `s = 2^{-(n-N)}`, so the rescaled bands are `H_{2^{-m(N)},1}` and `H_{2^{-N},2^{-m(N)}}`
  have hsdef' : s = (2 : ℝ)⁻¹ ^ (p.n - N) := rfl
  have e1 : (2 : ℝ)⁻¹ ^ ci / s = (2 : ℝ)⁻¹ ^ superScale N := by
    rw [hsdef', hci', pow_add, mul_div_cancel_left₀ _ (by positivity)]
  have e2 : (2 : ℝ)⁻¹ ^ (p.n - N) / s = 1 := by rw [hsdef', div_self (by positivity)]
  have e3 : (2 : ℝ)⁻¹ ^ p.n / s = (2 : ℝ)⁻¹ ^ N := by
    rw [hsdef', div_eq_iff (by positivity), ← pow_add, Nat.add_sub_cancel' hin]
  have hψ := ((isBandVersion_sub_of_realization hκ hH h1).comp_sim hκ
    (LinearIsometryEquiv.refl ℝ (Rd d)) z hs (by positivity)).congr_band e1 e2
  have hg := ((isBandVersion_sub_of_realization hκ hH h2).comp_sim hκ
    (LinearIsometryEquiv.refl ℝ (Rd d)) z hs (by positivity)).congr_band e3 e1
  have hb := hbound Ω P W' _ _ hW'w N hψ hg
  refine le_trans (le_of_eq ?_) hb
  congr 1
  ext ω
  simp only [mem_ofPred_eq]
  unfold NiceCert
  rw [hpξ, hpQ, hpθ, hpR]
  rfl

end DGZ

end HigherDimLQGMetric
