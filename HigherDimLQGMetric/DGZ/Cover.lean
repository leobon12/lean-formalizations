import HigherDimLQGMetric.DGZ.CoverFinish

/-!
# DGZ Proposition 5.10: the bypass cover

The downward induction starts with `𝒥₁`, selects one bad box at a time at each lower level, and
ends with a finite separated bypass cover.  The site consequences are (A″) and (C).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric.DGZ

open Set HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-- Iterate the one-level construction from `m` down to level `1`. -/
def coverState_all (p : NiceParams) (H : ℕ → Rd d → ℝ) (hc : ∀ q, Continuous (H q))
    (m : ℕ) (hm : 1 ≤ m) (hJ1 : EventJ1 p H m)
    (hmono : Monotone p.a) (ham : p.a m ≤ p.n)
    (hR : 1 ≤ p.R) (hξ : 0 < p.ξ)
    (hgap : ∀ j, 1 ≤ j → j < m → 40 * (p.R : ℝ) * p.s j ≤ p.s (j + 1))
    {lam : ℝ} (hlam : 0 ≤ lam) (hK : 2 ≤ p.K) (ha : p.a = dgzSeq lam p.K)
    {g : ℕ} (hg3 : 3 ≤ g) (hg : (g : ℝ) ≤ lam * (p.K : ℝ) ^ 4)
    (hKmargin : 6 * p.ξ * p.K + p.K ≤ (p.K : ℝ) ^ ((3 : ℝ) / 2))
    (hJ2 : EventJ2' p H m)
    (hAround : ∀ j, 2 ≤ j → j ≤ m → ∀ u w : Zd d,
      latPt (p.s (j - 1)) w ∈ obox (0 : Rd d) 2 → NiceCEvent p H j u w →
        AroundGood p.ξ (fun v => H p.n v - H (p.n - p.a j) v)
          (latPt (p.s (j - 1)) w) (4 * p.R * p.s (j - 1))
          (2 * p.R * p.s (j - 1)) (obox (0 : Rd d) 2) (p.tStar j) ∧
        Real.exp ((p.K : ℝ) ^ ((3 : ℝ) / 2) * √(p.a j : ℝ)) * p.tStar j <
          acrossDist p.ξ (fun v => H p.n v - H (p.n - p.a j) v)
            (latPt (p.s j) u) (4 * p.s j) (2 * p.s j)) :
    CoverState p H m 1 := by
  have hstates : ∀ k : ℕ, k ≤ m - 1 → CoverState p H m (m - k) := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa only [Nat.sub_zero] using coverState_top p H m hJ1
    | succ k ih =>
      intro hk
      have hk' : k ≤ m - 1 := by omega
      let i := m - (k + 2)
      have him : i + 2 ≤ m := by dsimp [i]; omega
      have heq : i + 2 = m - k := by dsimp [i]; omega
      have heq' : i + 1 = m - (k + 1) := by dsimp [i]; omega
      have old : CoverState p H m (i + 2) := by simpa only [heq] using ih hk'
      have hgap' : 40 * (p.R : ℝ) * p.s (i + 1) ≤ p.s (i + 2) :=
        hgap (i + 1) (by omega) (by omega)
      have new := coverState_step p H hc m i him old hmono ham hR hξ hgap'
        hlam hK ha hg3 hg hKmargin hJ2 hAround
      simpa only [heq'] using new
  have heq : m - (m - 1) = 1 := by omega
  simpa only [heq] using hstates (m - 1) le_rfl

/-- **DGZ Proposition 5.10, corrected covering form.** On `𝒥₁ ∩ 𝒥₂′` and under the explicit
size inequalities for `K`, `n`, and successive scales, there are finite, separated bypass centres
on the fine lattices.  Every mesh site outside their union satisfies (A″) and (C). -/
theorem exists_bypassCover (hd : 2 ≤ d) {ξ Q θ : ℝ} (hξ : 0 < ξ) (hθ : 0 < θ)
    {R : ℕ} (hR : 1 ≤ R) :
    ∃ N₀ : ℕ, ∀ p : NiceParams,
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
  obtain ⟨N₀, hcert⟩ := aroundGood_of_niceCEvent hd hξ hθ hR
  refine ⟨N₀, ?_⟩
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

end HigherDimLQGMetric.DGZ
