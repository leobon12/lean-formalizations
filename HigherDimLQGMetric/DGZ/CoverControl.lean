import HigherDimLQGMetric.DGZ.CoverGreedy
import HigherDimLQGMetric.DGZ.NiceBoxCert
import HigherDimLQGMetric.DGZ.Crossing

/-!
# Field transfer for the DGZ bypass cover

The certificate controls the fine band.  Oscillation of the coarse field on the containing box
transfers its around threshold and across distance to the full field, with the factor in (5.25).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric.DGZ

open Set HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-- A certificate plus the coarse-field oscillation bound supplies `IsBypassCover.ctrl` for
one selected centre. -/
theorem coverEntry_ctrl_of_osc (p : NiceParams) (H : ℕ → Rd d → ℝ)
    (hc : ∀ q, Continuous (H q)) (hξ : 0 < p.ξ) {i : ℕ}
    (e : CoverEntry p H i)
    (hgap : 40 * (p.R : ℝ) * p.s (i + 1) ≤ p.s (i + 2))
    (ha : p.a (i + 1) ≤ p.a (i + 2))
    (hK : 6 * p.ξ * p.K + p.K ≤ (p.K : ℝ) ^ ((3 : ℝ) / 2))
    (hFine : AroundGood p.ξ
        (fun v => H p.n v - H (p.n - p.a (i + 2)) v)
        (latPt (p.s (i + 1)) e.z) (4 * p.R * p.s (i + 1))
        (2 * p.R * p.s (i + 1)) (obox (0 : Rd d) 2) (p.tStar (i + 2)) ∧
      Real.exp ((p.K : ℝ) ^ ((3 : ℝ) / 2) * √(p.a (i + 2) : ℝ)) * p.tStar (i + 2) <
        acrossDist p.ξ (fun v => H p.n v - H (p.n - p.a (i + 2)) v)
          (latPt (p.s (i + 2)) e.u) (4 * p.s (i + 2)) (2 * p.s (i + 2)))
    (hOsc : ∀ v ∈ cbox (latPt (p.s (i + 2)) e.u) (4 * p.s (i + 2)),
      |H (p.n - p.a (i + 2)) v -
        H (p.n - p.a (i + 2)) (latPt (p.s (i + 2)) e.u)| ≤
          3 * p.K * √(p.a (i + 2) : ℝ)) :
    ∃ x ∈ cbox (latPt (p.s (i + 1)) e.z) (p.s (i + 2)), ∃ t : ℝ,
      AroundGood p.ξ (H p.n) (latPt (p.s (i + 1)) e.z)
        (4 * p.R * p.s (i + 1)) (2 * p.R * p.s (i + 1))
        (obox (0 : Rd d) 2) t ∧
      t < Real.exp (-(p.K * √(p.a (i + 1) : ℝ))) *
        acrossDist p.ξ (H p.n) x (4 * p.s (i + 2)) (2 * p.s (i + 2)) := by
  let sf := p.s (i + 1)
  let sc := p.s (i + 2)
  let z := latPt sf e.z
  let x := latPt sc e.u
  let g := H (p.n - p.a (i + 2))
  let f : Rd d → ℝ := fun v => H p.n v - g v
  let M : ℝ := 3 * p.K * √(p.a (i + 2) : ℝ)
  let μ : ℝ := g x
  let up := Real.exp (p.ξ * (μ + M))
  let down := Real.exp (p.ξ * (M - μ))
  let E := Real.exp ((p.K : ℝ) ^ ((3 : ℝ) / 2) * √(p.a (i + 2) : ℝ))
  let w := Real.exp (-(p.K * √(p.a (i + 1) : ℝ)))
  have hsc : 0 < sc := p.s_pos (i + 2)
  have hsf : 0 < sf := p.s_pos (i + 1)
  have hrad : 4 * (p.R : ℝ) * sf ≤ sc := by linarith [hgap, hsc]
  have hx : x ∈ cbox z sc := by
    intro k
    simpa only [abs_sub_comm] using (e.zmem k).le
  have hsmall : cbox z (4 * p.R * sf) ⊆ cbox x (4 * sc) := by
    intro v hv k
    have h1 : |v k - z k| ≤ 4 * p.R * sf := hv k
    have h2 : |z k - x k| < sc := e.zmem k
    have h3 := abs_sub_le (v k) (z k) (x k)
    linarith
  have hμ : x ∈ cbox x (4 * sc) := by
    intro k
    simp only [sub_self, abs_zero]
    positivity
  have hG (v : Rd d) (hv : v ∈ cbox x (4 * sc)) : |g v - μ| ≤ M := hOsc v hv
  have hFcont : Continuous f := (hc _).sub (hc _)
  have hUp : AroundGood p.ξ (H p.n) z (4 * p.R * sf) (2 * p.R * sf)
      (obox (0 : Rd d) 2) (up * p.tStar (i + 2)) := by
    have h := hFine.1.mono_field hξ.le hFcont (hc _) (M := μ + M) (fun v hv => by
      have hg := hG v (hsmall hv.1.1)
      have hg' := (abs_le.mp hg).2
      dsimp [f, g, μ] at hg' ⊢
      linarith)
    exact h
  have hDown : acrossDist p.ξ f x (4 * sc) (2 * sc) ≤
      down * acrossDist p.ξ (H p.n) x (4 * sc) (2 * sc) := by
    have hr : 2 * sc < 4 * sc := by linarith
    refine acrossDist_le_mul_of_exp_le hFcont (hc _) hr (Real.exp_pos _).le ?_
    intro v hv
    have hg := hG v hv.1
    have hg' := (abs_le.mp hg).1
    change Real.exp (p.ξ * f v) ≤
      Real.exp (p.ξ * (M - μ)) * Real.exp (p.ξ * H p.n v)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlow : μ - M ≤ g v := by linarith
    have hmul := mul_le_mul_of_nonneg_left hlow hξ.le
    dsimp [f]
    nlinarith
  have hweight : up * down ≤ w * E := by
    have hsqrt : √(p.a (i + 1) : ℝ) ≤ √(p.a (i + 2) : ℝ) := by
      exact Real.sqrt_le_sqrt (by exact_mod_cast ha)
    have hK0 : (0 : ℝ) ≤ p.K := Nat.cast_nonneg _
    have hs0 : 0 ≤ √(p.a (i + 2) : ℝ) := Real.sqrt_nonneg _
    have h1 : (6 * p.ξ * p.K + p.K) * √(p.a (i + 2) : ℝ) ≤
        (p.K : ℝ) ^ ((3 : ℝ) / 2) * √(p.a (i + 2) : ℝ) :=
      mul_le_mul_of_nonneg_right hK hs0
    have h2 : (p.K : ℝ) * √(p.a (i + 1) : ℝ) ≤
        p.K * √(p.a (i + 2) : ℝ) := mul_le_mul_of_nonneg_left hsqrt hK0
    have he : p.ξ * (μ + M) + p.ξ * (M - μ) ≤
        -(p.K * √(p.a (i + 1) : ℝ)) +
          (p.K : ℝ) ^ ((3 : ℝ) / 2) * √(p.a (i + 2) : ℝ) := by
      dsimp [M]
      nlinarith [h1, h2]
    dsimp [up, down, w, E]
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr he
  have hD : 0 ≤ acrossDist p.ξ (H p.n) x (4 * sc) (2 * sc) := acrossDist_nonneg _ _ _ _ _
  have hE : 0 < E := Real.exp_pos _
  have hup : 0 < up := Real.exp_pos _
  have hstrict : (up * p.tStar (i + 2)) * E <
      (w * acrossDist p.ξ (H p.n) x (4 * sc) (2 * sc)) * E := by
    have h1 := mul_lt_mul_of_pos_left (hFine.2.trans_le hDown) hup
    have h2 := mul_le_mul_of_nonneg_right hweight hD
    nlinarith [h1, h2]
  refine ⟨x, hx, up * p.tStar (i + 2), hUp, ?_⟩
  exact lt_of_mul_lt_mul_right hstrict hE.le

/-- The nice containing boxes at higher levels supply the coarse-field oscillation used in
the control transfer. -/
theorem coverEntry_osc_of_higherNice (p : NiceParams) (H : ℕ → Rd d → ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) (hK : 1 ≤ p.K) (ha : p.a = dgzSeq lam p.K)
    {g : ℕ} (hg3 : 3 ≤ g) (hg : (g : ℝ) ≤ lam * (p.K : ℝ) ^ 4)
    {i m : ℕ} (him : i + 2 ≤ m) (e : CoverEntry p H i)
    (hJ : EventJ2' p H m)
    (hhigher : ∀ l : ℕ, i + 2 < l → l ≤ m → ∃ u : Zd d,
      obox (latPt (p.s (i + 2)) e.u) (p.s (i + 2)) ⊆
        obox (latPt (p.s l) u) (p.s l) ∧ NiceBox p H l u) :
    ∀ v ∈ cbox (latPt (p.s (i + 2)) e.u) (4 * p.s (i + 2)),
      |H (p.n - p.a (i + 2)) v -
        H (p.n - p.a (i + 2)) (latPt (p.s (i + 2)) e.u)| ≤
          3 * p.K * √(p.a (i + 2) : ℝ) := by
  let x := latPt (p.s (i + 2)) e.u
  have hx : x ∈ obox x (p.s (i + 2)) := HigherDimLFPP.DGZ.mem_obox_self _ (p.s_pos _)
  have hx2 : x ∈ obox (0 : Rd d) 2 := e.big hx
  have hx3 : x ∈ obox (0 : Rd d) 3 := by
    intro k
    have h := hx2 k
    linarith
  have hbox : ∀ l, i + 2 < l → l ≤ m → ∃ u : Zd d,
      x ∈ obox (latPt (p.s l) u) (4 * p.s l) ∧ NiceOscCond p H l u := by
    intro l hil hlm
    obtain ⟨u, hsub, hnice⟩ := hhigher l hil hlm
    have hxsub := hsub hx
    have hxl : x ∈ obox (latPt (p.s l) u) (4 * p.s l) := by
      intro k
      have h := hxsub k
      linarith [p.s_pos l]
    have heq : l - 2 + 2 = l := by omega
    rw [← heq] at hnice
    have hosc := ((niceBox_add_two_iff p H (l - 2) u).mp hnice).1
    exact ⟨u, hxl, by simpa only [heq] using hosc⟩
  have hraw := osc_le_three_of_niceOscCond p H hlam hK ha hg3 hg (by omega) him e.u
    (r := 4 * p.s (i + 2)) (by linarith [p.s_pos (i + 2)]) hbox hJ hx3
  intro v hv
  exact hraw v hv x (by
    intro k
    change |x k - x k| ≤ 4 * p.s (i + 2)
    simp only [sub_self, abs_zero]
    linarith [p.s_pos (i + 2)])

/-- A box contained in `B₂(0)` has nested containing boxes at every higher dyadic level. -/
theorem exists_niceParent_chain (p : NiceParams) (hmono : Monotone p.a)
    {j l : ℕ} (hjl : j ≤ l) (hln : p.a l ≤ p.n)
    (u : Zd d)
    (hu : obox (latPt (p.s j) u) (p.s j) ⊆ obox (0 : Rd d) 2) :
    ∃ v : Zd d,
      obox (latPt (p.s j) u) (p.s j) ⊆
        obox (latPt (p.s l) v) (p.s l) ∧
      obox (latPt (p.s l) v) (p.s l) ⊆ obox (0 : Rd d) 2 := by
  induction l, hjl using Nat.le_induction with
  | base => exact ⟨u, Subset.rfl, hu⟩
  | succ l hjl ih =>
    obtain ⟨v, hsub, hbig⟩ := ih ((hmono (Nat.le_succ l)).trans hln)
    obtain ⟨v', hparent, hbig', _⟩ :=
      exists_niceParent p hmono hln v hbig
    exact ⟨v', hsub.trans hparent, hbig'⟩

end HigherDimLQGMetric.DGZ
