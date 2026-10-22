import HigherDimLQGContinuity.Unif5.Cert
import HigherDimLQGMetric.DGZ.Cover

/-!
# The bypass cover with a threshold uniform in `ξ` (packet U2)

Blueprint Part D, `d:lem-u510` (consumer of the uniform nice-box certificate of `d:conv-coarse`). The deterministic
Proposition 5.10 of [1] in the repository, `HigherDimLQGMetric.DGZ.exists_bypassCover` (`DGZ/Cover.lean`), takes
`(ξ, Q, θ)` before its threshold `∃ N₀`; that `N₀` comes only from the deterministic consequence of `𝒞(x,z)`
(`DGZ.aroundGood_of_niceCEvent`, whose `N₀` is L3c3's `aroundGood_of_aroundCertAt` threshold). Since U1's
`aroundGood_of_aroundCertAt_unif` chooses that threshold before `(ξ, Q)`, so does `aroundGood_of_niceCEvent_unif`
(`Unif5/Cert.lean`), and the proof of `DGZ.exists_bypassCover` gives the cover with `N₀ = N₀(d, θ, R)`:

* `exists_bypassCover_unif`: the statement of `DGZ.exists_bypassCover` with `∃ N₀` moved in front of `∀ ξ Q, 0 < ξ`.
  The cover construction (`DGZ.coverState_all`, `DGZ.CoverState.isBypassCover`, `DGZ.coverState_siteGood`) is reused
  verbatim.

The consumers `DGZ.prop513`, `DGZ.prop513_setDist`, `DGZ.cmp_lfppDistance_le` take their `N₀` from
`DGZ.exists_bypassCover`; their uniform ports repeat their proofs with this lemma.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-- **DGZ Proposition 5.10 (the bypass cover) with a threshold uniform in `ξ`** (port of `DGZ.exists_bypassCover`;
`d:lem-u510`). For `d ≥ 2`, `θ > 0` and `R ≥ 1` there is `N₀ = N₀(d, θ, R)` such that for every `ξ > 0` and `Q`: on
`𝒥₁ ∩ 𝒥₂′` and under the explicit size inequalities for `K`, `n` and successive scales, there are finite, separated
bypass centres on the fine lattices, and every mesh site outside their union satisfies (A″) and (C). -/
theorem exists_bypassCover_unif (hd : 2 ≤ d) {θ : ℝ} (hθ : 0 < θ) {R : ℕ} (hR : 1 ≤ R) :
    ∃ N₀ : ℕ, ∀ ξ Q : ℝ, 0 < ξ → ∀ p : NiceParams,
      p.ξ = ξ → p.Q = Q → p.θ = θ → p.R = R →
      ∀ H : ℕ → Rd d → ℝ, (∀ q, Continuous (H q)) → ∀ m : ℕ, 1 ≤ m →
      ∀ {lam : ℝ}, 0 ≤ lam → 2 ≤ p.K → p.a = dgzSeq lam p.K →
      ∀ {g : ℕ}, 3 ≤ g → (g : ℝ) ≤ lam * (p.K : ℝ) ^ 4 →
      p.a m ≤ p.n → N₀ ≤ p.a 1 →
      4 * R ≤ 2 ^ (p.n - p.a m + 1) →
      (∀ j, 1 ≤ j → j < m → 40 * (p.R : ℝ) * p.s j ≤ p.s (j + 1)) →
      6 * p.ξ * p.K + p.K ≤ (p.K : ℝ) ^ ((3 : ℝ) / 2) →
      EventJ1 p H m → EventJ2' p H m →
      ∃ X : ℕ → Set (Rd d),
        (∀ j, ∀ z ∈ X j, ∃ u : Zd d, z = latPt (p.s j) u) ∧
        IsBypassCover p.ξ (H p.n) (p.R : ℝ) m p.s (coverWeight p) X ∧
        ∀ w : Zd d,
          obox (latPt (p.s 0) w) (p.s 0) ⊆ obox (0 : Rd d) 2 →
          latPt (p.s 0) w ∉ coverU (p.R : ℝ) m p.s X →
          (∀ v ∈ cbox (latPt (p.s 0) w) (2 * p.s 0),
            ∀ v' ∈ cbox (latPt (p.s 0) w) (2 * p.s 0),
              |H p.n v - H p.n v'| ≤ p.L + 1) ∧
            p.L⁻¹ * (2 : ℝ) ^ (-(p.n : ℝ) - (1 - p.ξ * p.Q + p.ε) * p.k) <
              acrossDist p.ξ (fun v => H (p.n + p.k) v - H p.n v)
                (latPt (p.s 0) w) (2 * p.s 0) (p.s 0) := by
  obtain ⟨N₀, hcert₀⟩ := aroundGood_of_niceCEvent_unif hd hθ hR
  refine ⟨N₀, fun ξ Q hξ => ?_⟩
  have hcert := hcert₀ ξ Q hξ
  intro p hpξ hpQ hpθ hpR H hc m hm lam hlam hK ha g hg3 hg ham hN hCube hgap
    hKmargin hJ1 hJ2
  have hmono : Monotone p.a := by
    rw [ha]
    exact dgzSeq_monotone hlam (by omega : 1 ≤ p.K)
  have hAround : ∀ j, 2 ≤ j → j ≤ m → ∀ u w : Zd d,
      latPt (p.s (j - 1)) w ∈ obox (0 : Rd d) 2 → NiceCEvent p H j u w →
        AroundGood p.ξ (fun v => H p.n v - H (p.n - p.a j) v)
          (latPt (p.s (j - 1)) w) (4 * p.R * p.s (j - 1))
          (2 * p.R * p.s (j - 1)) (obox (0 : Rd d) 2) (p.tStar j) ∧
        Real.exp ((p.K : ℝ) ^ ((3 : ℝ) / 2) * √(p.a j : ℝ)) * p.tStar j <
          acrossDist p.ξ (fun v => H p.n v - H (p.n - p.a j) v)
            (latPt (p.s j) u) (4 * p.s j) (2 * p.s j) := by
    intro j hj2 hjm u w hw hC
    have hN' : N₀ ≤ p.a (j - 1) :=
      hN.trans (hmono (by omega : 1 ≤ j - 1))
    have hjn : p.a (j - 1) ≤ p.n :=
      (hmono (by omega : j - 1 ≤ m)).trans ham
    have he : p.n - p.a m + 1 ≤ p.n - p.a (j - 1) + 1 := by
      have h := hmono (by omega : j - 1 ≤ m)
      omega
    have hCube' : 4 * R ≤ 2 ^ (p.n - p.a (j - 1) + 1) :=
      hCube.trans (pow_le_pow_right₀ (by omega : (1 : ℕ) ≤ 2) he)
    have h := hcert p hpξ hpQ hpθ hpR H hc j hN' hjn hCube' u w hw hC
    simpa only [hpξ, hpR] using h
  let st := coverState_all p H hc m hm hJ1 hmono ham
    (by simpa only [hpR] using hR) (by simpa only [hpξ] using hξ)
    hgap hlam hK ha hg3 hg hKmargin hJ2 hAround
  refine ⟨st.X, st.lattice, st.isBypassCover, ?_⟩
  intro w hsmall hout
  exact coverState_siteGood p H hm st hmono ham hlam hK ha hg3 hg hJ2 w hsmall hout

end HigherDimLQGContinuity
