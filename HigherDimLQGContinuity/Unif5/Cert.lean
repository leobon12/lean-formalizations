import HigherDimLQGContinuity.Unif4.SuperExpAround
import HigherDimLQGMetric.DGZ.NiceBoxCert

/-!
# The uniform nice-box certificate (packet U2)

Blueprint Part D, `d:conv-coarse` ("the certificate form of `𝒞(x,z)`") and `d:lem-u56` (*Certificate*); NA3 §2.5,
§4.1 (`NiceBoxCert` in the U2 row). Port of `HigherDimLQGMetric.DGZ.prob_not_niceCert_le` and
`DGZ.aroundGood_of_niceCEvent` (`DGZ/NiceBoxCert.lean`, MA7 D-5.3, D-5.6).

* `prob_not_niceCert_le_unif` (port of `DGZ.prob_not_niceCert_le`): `P[Cert_i(z) fails] ≤ C e^{-a_i log a_i}` with
  `C = C(d, κ, b, μ, θ, R)`, for every `ξ` with `UHyp d κ b μ ξ`, every dyadic realization, every level `i` with
  `m(a_i) ≤ a_i ≤ n` and every `z`. The proof of the fixed-`ξ` lemma (rescaling of the coarse and fine bands of
  `h_{n-a_i,n}` by `s_i` around `z`, a white noise `W ∘ V_{z,s_i}`) is repeated with U1's uniform certificate bound
  `prob_not_aroundCertAt_le_unif` (`d:lem-u49`).
* `aroundGood_of_niceCEvent_unif` (port of `DGZ.aroundGood_of_niceCEvent`): the deterministic consequence of `𝒞(x,z)`
  with a threshold `N₀ = N₀(d, θ, R)` chosen **before** `(ξ, Q)`: from U1's `aroundGood_of_aroundCertAt_unif`, whose
  `n₀` depends only on `(d, δ, r₁, r₂)`, and the fixed-parameter consequence `DGZ.aroundGood_of_niceCEvent_of`
  (reused verbatim).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

variable {d : ℕ}

/-- **Uniform certificate bound** (`d:lem-u56`, *Certificate*; port of `DGZ.prob_not_niceCert_le`): for `d ≥ 2`,
`κ` admissible, `b, μ, θ > 0` and `R ≥ 1` there is `C > 0` (depending only on `d, κ, b, μ, θ, R`) such that
`P*[Cert_i(z) fails] ≤ C e^{-a_i log a_i}` for every `ξ` with `UHyp d κ b μ ξ`, every dyadic realization, all
parameters with `p.ξ = ξ`, `p.Q = Q(ξ)`, `p.θ = θ`, `p.R = R`, every level `i` with `m(a_i) ≤ a_i ≤ n` and every
point `z`. -/
theorem prob_not_niceCert_le_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {θ : ℝ} (hθ : 0 < θ) {R : ℕ} (hR : 1 ≤ R) :
    ∃ C > 0, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, p.ξ = ξ → p.Q = distExp d ξ → p.θ = θ → p.R = R →
          ∀ i : ℕ, p.a i ≤ p.n → superScale (p.a i) ≤ p.a i → ∀ z : Rd d,
            P {ω | ¬ NiceCert p (fun q y => H q y ω) i z} ≤
              ENNReal.ofReal (C * Real.exp (-(p.a i : ℝ) * Real.log (p.a i))) := by
  have hR0 : (0 : ℝ) < 2 * R := by
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  obtain ⟨C, hC, hbound⟩ := prob_not_aroundCertAt_le_unif hd hκ hb hμ hθ (r₁ := 4 * (R : ℝ))
    (r₂ := 2 * R) hR0 (by linarith)
  refine ⟨C, hC, fun ξ hξh Ω _ P W H hH p hpξ hpQ hpθ hpR i hin hsS z => ?_⟩
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
  have hb' := hbound ξ hξh Ω P W' _ _ hW'w N hψ hg
  refine le_trans (le_of_eq ?_) hb'
  congr 1
  ext ω
  simp only [mem_ofPred_eq]
  unfold NiceCert
  rw [hpξ, hpQ, hpθ, hpR]
  rfl

/-- **The deterministic consequence of `𝒞(x,z)`, uniformly** (`d:conv-coarse`; port of
`DGZ.aroundGood_of_niceCEvent`). For `d ≥ 2`, `θ > 0` and `R ≥ 1` there is `N₀ = N₀(d, θ, R)` such that for every
`ξ > 0` and every `Q`, all parameters with these values of `ξ, Q, θ, R`, every family of continuous fields, every
`j` with `N₀ ≤ a_{j-1} ≤ n` and `4R ≤ 2/s_{j-1}`, and every `z = s_{j-1} w ∈ B₂(0)`: on `𝒞(s_j u, z)`,
* `AroundGood(h_{n-a_j,n}, z, 4R s_{j-1}, 2R s_{j-1}, B₂(0), t*)`, and
* `e^{K^{3/2}√a_j} t* < D_{n-a_j,n}(across B_{4s_j}(s_j u) \ B_{2s_j}(s_j u))`. -/
theorem aroundGood_of_niceCEvent_unif (hd : 2 ≤ d) {θ : ℝ} (hθ : 0 < θ) {R : ℕ} (hR : 1 ≤ R) :
    ∃ N₀ : ℕ, ∀ ξ Q : ℝ, 0 < ξ → ∀ p : NiceParams, p.ξ = ξ → p.Q = Q → p.θ = θ → p.R = R →
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
  obtain ⟨N₀, hN₀⟩ := aroundGood_of_aroundCertAt_unif hd hθ (r₁ := 4 * (R : ℝ)) (r₂ := 2 * R) hR0
    (by linarith)
  refine ⟨N₀, fun ξ Q hξ p hpξ hpQ hpθ hpR => ?_⟩
  subst hpξ hpQ hpθ hpR
  intro H hc j hN hjn hcube u w hw hC
  exact aroundGood_of_niceCEvent_of p hξ (hN₀ p.ξ p.Q hξ) H hc hN hjn hcube hw hC

end HigherDimLQGContinuity
