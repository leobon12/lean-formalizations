/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFusedRegular

/-!
# A uniform source scale and smaller protected boxes for the opposite view

Packet PROVE-ZHAN-GT4-A22. The constants are selected before the paths,
times and spatial centers. A neighborhood of radius at most `c / 8`
preserves half of the original source clearance `c`.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex
namespace InteractingSLE.ZhanGT4

/-- Shrinking a regular box preserves its derivatives and continuity. -/
theorem IsLogField.mono_radius {f fx fxx fxxx ft : ℝ → ℝ → ℝ} {b c y ρ ρ' K : ℝ}
    (h : IsLogField f fx fxx fxxx ft b c y ρ K) (hρ' : 0 < ρ') (hle : ρ' ≤ ρ) :
    IsLogField f fx fxx fxxx ft b c y ρ' K := by
  have hlt : ∀ x : ℝ, |x - y| < 3 * ρ' → |x - y| < 3 * ρ :=
    fun _ hx => lt_of_lt_of_le hx (mul_le_mul_of_nonneg_left hle (by norm_num))
  have hs : Icc b c ×ˢ {x : ℝ | |x - y| < 3 * ρ'} ⊆ Icc b c ×ˢ {x : ℝ | |x - y| < 3 * ρ} :=
    fun z hz => ⟨hz.1, hlt z.2 hz.2⟩
  exact ⟨hρ', h.Knonneg, fun t ht x hx => h.dx t ht x (hlt x hx),
    fun t ht x hx => h.dxx t ht x (hlt x hx), fun t ht x hx => h.dxxx t ht x (hlt x hx),
    fun t ht x hx => h.dt t ht x (hlt x hx), h.cont.mono hs, h.contX.mono hs,
    h.contXX.mono hs, h.contT.mono hs, fun t ht x hx => h.bound t ht x (hlt x hx)⟩

/-- Subtracting the frozen entrance normalizer preserves regularity,
with the explicit additional bound on its absolute value. -/
theorem IsLogField.sub_const {f fx fxx fxxx ft : ℝ → ℝ → ℝ} {b c y ρ K : ℝ}
    (h : IsLogField f fx fxx fxxx ft b c y ρ K) (a : ℝ) :
    IsLogField (fun t x => f t x - a) fx fxx fxxx ft b c y ρ (K + |a|) := by
  have hK : K ≤ K + |a| := le_add_of_nonneg_right (abs_nonneg _)
  refine ⟨h.pos, add_nonneg h.Knonneg (abs_nonneg _),
    fun t ht x hx => (h.dx t ht x hx).sub_const a, h.dxx, h.dxxx,
    fun t ht x hx => (h.dt t ht x hx).sub_const a, h.cont.sub continuousOn_const,
    h.contX, h.contXX, h.contT, ?_⟩
  intro t ht x hx
  obtain ⟨b0, b1, b2, b3, bt⟩ := h.bound t ht x hx
  exact ⟨(abs_sub _ _).trans (add_le_add b0 le_rfl), b1.trans hK, b2.trans hK,
    b3.trans hK, bt.trans hK⟩

/-- A protected source gap survives throughout the smaller spatial box. -/
theorem seedAccess_gap_on_piece {w v x y ρ c C : ℝ} (hρ : ρ ≤ c / 8)
    (hw : |w - y| < ρ) (hx : |x - y| < 3 * ρ) (hgap : c ≤ |v - w| ∧ |v - w| ≤ C) :
    c / 2 ≤ |x - v| ∧ |x - v| ≤ C + c / 2 := by
  have hnear : |x - w| < c / 2 := by
    have hh : |x - w| ≤ |x - y| + |w - y| := by
      simpa only [abs_sub_comm w y] using (abs_sub_le x y w)
    linarith only [hh, hx, hw, hρ]
  have hlow : |v - w| ≤ |x - v| + |x - w| := by
    simpa only [abs_sub_comm v x] using abs_sub_le v x w
  have hhigh : |x - v| ≤ |x - w| + |v - w| := by
    simpa only [abs_sub_comm w v] using abs_sub_le x w v
  exact ⟨by linarith only [hgap.1, hlow, hnear], by linarith only [hgap.2, hhigh, hnear]⟩

/-- One logarithmic source scale works for all protected paths, horizons
bounded by `Tm`, and points in the smaller boxes. -/
theorem exists_seedAccessScale {c C : ℝ} (hc : 0 < c) (hC : 0 < C + c / 2) (Tm : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ 2 * Tm / (c / 2) ^ 2 ≤ L ∧
      ∀ {w v x y ρ : ℝ}, ρ ≤ c / 8 → |w - y| < ρ → |x - y| < 3 * ρ →
        c ≤ |v - w| → |v - w| ≤ C → c / 2 ≤ |x - v| ∧ InScale L (x - v) := by
  obtain ⟨L₀, hL₀, hs⟩ := exists_inScale_of_abs_bounds (half_pos hc) hC
  let L := max L₀ (2 * Tm / (c / 2) ^ 2)
  refine ⟨L, hL₀.trans (le_max_left _ _), le_max_right _ _, ?_⟩
  intro w v x y ρ hρ hw hx hlo hhi
  have hg := seedAccess_gap_on_piece hρ hw hx ⟨hlo, hhi⟩
  exact ⟨hg.1, FrzData.inScale_mono (hs (x - v) hg.1 hg.2) (le_max_left _ _)⟩

end InteractingSLE.ZhanGT4
