import HigherDimLQGMetric.DGZ.CoverStep

/-!
# The site consequences of the DGZ bypass cover

Outside the final union, the level-one box containing a mesh site is nice.  Its condition (3)
gives the lower across bound, while the nested nice boxes and `𝒥₂′` give (A″).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric.DGZ

open Set HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-- A completed cover state has precisely the interface consumed by the bypass lemma. -/
theorem CoverState.isBypassCover {p : NiceParams} {H : ℕ → Rd d → ℝ} {m : ℕ}
    (st : CoverState p H m 1) :
    IsBypassCover p.ξ (H p.n) (p.R : ℝ) m p.s (coverWeight p) st.X :=
  ⟨st.finite, st.sub, st.sep, st.ctrl⟩

/-- Conditions (A″) and (C) at a mesh site outside the final union. -/
theorem coverState_siteGood (p : NiceParams) (H : ℕ → Rd d → ℝ)
    {m : ℕ} (hm : 1 ≤ m) (st : CoverState p H m 1)
    (hmono : Monotone p.a) (ham : p.a m ≤ p.n)
    {lam : ℝ} (hlam : 0 ≤ lam) (hK : 2 ≤ p.K) (ha : p.a = dgzSeq lam p.K)
    {g : ℕ} (hg3 : 3 ≤ g) (hg : (g : ℝ) ≤ lam * (p.K : ℝ) ^ 4)
    (hJ2 : EventJ2' p H m)
    (w : Zd d)
    (hsmall : obox (latPt (p.s 0) w) (p.s 0) ⊆ obox (0 : Rd d) 2)
    (hout : latPt (p.s 0) w ∉ coverU (p.R : ℝ) m p.s st.X) :
    (∀ v ∈ cbox (latPt (p.s 0) w) (2 * p.s 0),
      ∀ v' ∈ cbox (latPt (p.s 0) w) (2 * p.s 0),
        |H p.n v - H p.n v'| ≤ p.L + 1) ∧
      p.L⁻¹ * (2 : ℝ) ^ (-(p.n : ℝ) - (1 - p.ξ * p.Q + p.ε) * p.k) <
        acrossDist p.ξ (fun v => H (p.n + p.k) v - H p.n v)
          (latPt (p.s 0) w) (2 * p.s 0) (p.s 0) := by
  have h1n : p.a 1 ≤ p.n := (hmono hm).trans ham
  obtain ⟨u₁, hparent, hbig, _⟩ := exists_niceParent p hmono h1n w hsmall
  have hwself : latPt (p.s 0) w ∈ obox (latPt (p.s 0) w) (p.s 0) :=
    HigherDimLFPP.DGZ.mem_obox_self _ (p.s_pos 0)
  have hu₁ : latPt (p.s 0) w ∈ obox (latPt (p.s 1) u₁) (p.s 1) :=
    hparent hwself
  have hnotParent : ¬ obox (latPt (p.s 1) u₁) (p.s 1) ⊆
      coverU (p.R : ℝ) m p.s st.X := by
    intro h
    exact hout (h hu₁)
  have hnice₁ : NiceBox p H 1 u₁ := st.niceOutside 1 le_rfl hm u₁ hbig hnotParent
  obtain ⟨hOscOne, hAcrossOne⟩ := (niceBox_one_iff p H u₁).mp hnice₁
  have hbox : ∀ l, 1 < l → l ≤ m → ∃ u : Zd d,
      latPt (p.s 0) w ∈ obox (latPt (p.s l) u) (4 * p.s l) ∧
        NiceOscCond p H l u := by
    intro l h1l hlm
    obtain ⟨u, hsub, hbigl⟩ :=
      exists_niceParent_chain p hmono h1l.le ((hmono hlm).trans ham) u₁ hbig
    have hnot : ¬ obox (latPt (p.s l) u) (p.s l) ⊆
        coverU (p.R : ℝ) m p.s st.X := by
      intro h
      exact hout (h (hsub hu₁))
    have hnice : NiceBox p H l u := st.niceOutside l (by omega) hlm u hbigl hnot
    have hw : latPt (p.s 0) w ∈ obox (latPt (p.s l) u) (4 * p.s l) := by
      intro k
      have h := (hsub hu₁) k
      linarith [p.s_pos l]
    have heq : l - 2 + 2 = l := by omega
    rw [← heq] at hnice
    have hosc := ((niceBox_add_two_iff p H (l - 2) u).mp hnice).1
    exact ⟨u, hw, by simpa only [heq] using hosc⟩
  have hw2 : latPt (p.s 0) w ∈ obox (0 : Rd d) 2 := hsmall hwself
  have hw3 : latPt (p.s 0) w ∈ obox (0 : Rd d) 3 := by
    intro k
    have h := hw2 k
    linarith
  have hosc := osc_le_add_one_of_niceOscOne p H hlam hK ha hg3 hg hm w
    (r := 2 * p.s 0) (by linarith [p.s_pos 0]) hu₁ hOscOne hbox hJ2 hw3
  exact ⟨hosc, hAcrossOne w hu₁⟩

end HigherDimLQGMetric.DGZ
