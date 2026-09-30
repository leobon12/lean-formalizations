import QuantumZipper.Proofs.Zipper.UnifRC3Split

/-!
# UNIF-RC3-RSTAB (decision D33): deterministic stability of the second unzip map

The second unzip map at parameters `p = (u, s) ∈ tri T` is
`R_{u,s} = revMap (vrev W (u + s)) s` (see `UnifRC3Split.alphaUS`, `RegCont.fwdMapInv_add`).

This file proves the **horizon direction** of the D33 item RSTAB: for a driver `W` whose
oscillation on `[0,T]` at scale `h = s' − s` is at most `ε`, and `z ∈ ℍ` with `‖z‖ ≤ R`, `Im z ≥ τ`,

`‖R_{u,s'} z − R_{u,s} z‖ ≤ (ε + 2h/τ)·√(R² + 8T)/τ`,   hence for an `a`-Hölder driver
`∃ C, ‖R_{u,s'} z − R_{u,s} z‖ ≤ C·τ^{-2}·|s' − s|^{a/2}` — a *polynomial* modulus in `1/τ`, as
D33 requires. No Gronwall bound is used (`ReverseFlow.norm_revMap_sub_revMap_le`, which would
give `exp(2T/τ²)`, is never invoked). The chain is the flow decomposition of D33, with
`a = u + s`, `h = s' − s ≥ 0` and `w = revMap (vrev W (a+h)) h z`:

* `revMap_vrev_split` (from `ReverseFlow.revMap_add` plus the driver-shift identity `vrev_shift`):
  `R_{u,s+h} z = R_{u,s} w` — cocycle `R_{u,s+h} = R_{u,s} ∘ R_{u+s,h}`;
* `norm_revMap_vrev_sub_self_le` (from `RegCont.norm_revMap_sub_self_le`, with the driver bound
  `abs_vrev_le_of_osc`): `‖w − z‖ ≤ ε + 2h/Im z`;
* `TwoPoint.norm_revMap_sub_mul_le_upper` applied to the map `R_{u,s}` at the two points `z, w`,
  whose imaginary parts both lie in `[τ, √(R² + 4T)]` (`im_le_im_revMap`, `im_revMap_sq_le`).

**The `u`-direction** and the two-parameter bound are in `UnifUC1Stab.lean`
(`norm_RUS_u_le`, `norm_RUS_sub_le`, `norm_RUS_sub_le_holder`), by the cocycle
`R_{u,g} ∘ R_{u+g,s} = R_{u,s+g}` and this file's horizon direction.

Sources: D33 (`handoff/REG-UNIF.md`, section UNIF-RC3) and the flow-decomposition lemmas of
`RegCont.lean`/`RegContEnergy.lean` (`fwdMapInv_add`, `revMap_add`, `norm_revMap_sub_self_le`,
`TwoPoint.norm_revMap_sub_mul_le_upper`). Own elementary argument for the bookkeeping; no
published source treats the stability of the double unzip map in its two time parameters.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint B2

variable {W : ℝ → ℝ}

/-- The second unzip map `R_{u,s} = revMap (vrev W (u+s)) s` (as a function of the point). -/
def RUS (W : ℝ → ℝ) (p : ℝ × ℝ) (z : ℂ) : ℂ := revMap (vrev W (p.1 + p.2)) p.2 z

theorem RUS_apply (W : ℝ → ℝ) (p : ℝ × ℝ) (z : ℂ) :
    RUS W p z = revMap (vrev W (p.1 + p.2)) p.2 z := rfl

/-! ## Shift identity for the reversed driver -/

/-- `vrev W (a+g)` shifted back by `g` is `vrev W a`: for `0 ≤ r ≤ a`,
`vrev W (a+g) (g+r) − vrev W (a+g) g = vrev W a r`. -/
theorem vrev_shift {a g r : ℝ} (ha : 0 ≤ a) (hg : 0 ≤ g) (hr : r ∈ Icc (0 : ℝ) a) :
    vrev W (a + g) (g + r) - vrev W (a + g) g = vrev W a r := by
  have h1 : max (g + r) 0 = g + r := max_eq_left (by linarith [hr.1])
  have h2 : min (g + r) (a + g) = g + r := min_eq_left (by linarith [hr.2])
  have h3 : max r 0 = r := max_eq_left hr.1
  have h4 : min r a = r := min_eq_left hr.2
  simp only [vrev, h1, h2, h3, h4]
  rw [max_eq_left hg, min_eq_left (by linarith : g ≤ a + g)]
  rw [show a + g - (g + r) = a - r by ring, show a + g - g = a by ring]
  ring

/-- On `[0,g]` the driver `vrev W (a+g)` is bounded by the oscillation of `W` on `[a, a+g]`. -/
theorem abs_vrev_le_of_osc {a g ε : ℝ} (ha : 0 ≤ a) (hg : 0 ≤ g)
    (hosc : ∀ t ∈ Icc a (a + g), ∀ t' ∈ Icc a (a + g), |W t - W t'| ≤ ε) :
    ∀ r ∈ Icc (0 : ℝ) g, |vrev W (a + g) r| ≤ ε := by
  intro r hr
  have h1 : max r 0 = r := max_eq_left hr.1
  have h2 : min r (a + g) = r := min_eq_left (by linarith [hr.2])
  simp only [vrev, h1, h2]
  exact hosc (a + g - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩ (a + g)
    ⟨by linarith, le_rfl⟩

/-! ## Displacement of the `h`-step of the reverse flow -/

/-- **Displacement of an `h`-step of the reverse flow**: if the oscillation of `W` on `[a, a+h]`
is at most `ε`, then `‖revMap (vrev W (a+h)) h z − z‖ ≤ ε + 2h/Im z`
(`RegCont.norm_revMap_sub_self_le` with the driver `vrev W (a+h)`, bounded by `ε`). -/
theorem norm_revMap_vrev_sub_self_le (hW : Continuous W) {a h ε : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hosc : ∀ t ∈ Icc a (a + h), ∀ t' ∈ Icc a (a + h), |W t - W t'| ≤ ε) {z : ℂ} (hz : z ∈ H) :
    ‖revMap (vrev W (a + h)) h z - z‖ ≤ ε + 2 * h / z.im :=
  norm_revMap_sub_self_le (continuous_vrev hW (a + h)) hz hh (M := ε)
    (abs_vrev_le_of_osc ha hh hosc)

/-! ## Flow decomposition of the second unzip map -/

/-- **Flow decomposition / cocycle.** For `h ≤ a`, `s ≤ a` and `z ∈ ℍ`,
`revMap (vrev W (a+h)) (s+h) z = revMap (vrev W a) s (revMap (vrev W (a+h)) h z)`, i.e.
`R_{a-s, s+h} = R_{a-s, s} ∘ R_{a, h}`: the `h`-step of the reverse flow followed by the
`s`-step. The driver shift `vrev_shift` turns the shifted driver `vrev W (a+h)(h+·) − vrev W (a+h) h`
into `vrev W a`. -/
theorem revMap_vrev_split (hW : Continuous W) {a s h : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hh : 0 ≤ h)
    (hsa : s ≤ a) {z : ℂ} (hz : z ∈ H) :
    revMap (vrev W (a + h)) (s + h) z = revMap (vrev W a) s (revMap (vrev W (a + h)) h z) := by
  have hV : Continuous (vrev W (a + h)) := continuous_vrev hW (a + h)
  have h1 := ReverseFlow.revMap_add (vrev W (a + h)) hV z hz hh hs
  rw [add_comm h s] at h1
  refine h1.trans ?_
  exact (ReverseFlow.revMap_congr_drive (revMap (vrev W (a + h)) h z)
    (fun r hr => vrev_shift ha hh ⟨hr.1, hr.2.trans hsa⟩)).trans rfl

/-! ## RSTAB in the horizon direction -/

/-- **UNIF-RC3-RSTAB (horizon direction).** For `(u,s), (u,s') ∈ tri T` with `s ≤ s'`, a driver
whose oscillation at scale `s' − s` on `[0,T]` is at most `ε`, and `z ∈ ℍ` with `τ ≤ Im z` and
`‖z‖ ≤ R`,

`‖R_{u,s'} z − R_{u,s} z‖ ≤ (ε + 2(s'−s)/τ)·√(R² + 8T)/τ`.

The proof is the flow decomposition `R_{u,s'} = R_{u,s} ∘ R_{u+s,s'−s}` with the displacement
bound `norm_revMap_vrev_sub_self_le` and the two-point upper bound
`TwoPoint.norm_revMap_sub_mul_le_upper` for `R_{u,s}`; no Gronwall estimate is used. -/
theorem norm_RUS_s_le (hW : Continuous W) {T τ R u s s' ε : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (hu : 0 ≤ u) (hs : 0 ≤ s) (hss : s ≤ s') (hus' : u + s' ≤ T)
    (hosc : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T,
      |t - t'| ≤ s' - s → |W t - W t'| ≤ ε)
    {z : ℂ} (hz : z ∈ H) (hzim : τ ≤ z.im) (hzR : ‖z‖ ≤ R) :
    ‖RUS W (u, s') z - RUS W (u, s) z‖ ≤
      (ε + 2 * (s' - s) / τ) * Real.sqrt (R ^ 2 + 8 * T) / τ := by
  have hε0 : 0 ≤ ε := by
    have h0 := hosc 0 ⟨le_rfl, hT⟩ 0 ⟨le_rfl, hT⟩ (by simp; linarith)
    simpa using h0
  have hh : 0 ≤ s' - s := sub_nonneg.2 hss
  have ha : 0 ≤ u + s := by linarith
  have hsr : s ≤ u + s := by linarith
  have hzR' : z.im ≤ R := (le_abs_self z.im).trans ((Complex.abs_im_le_norm z).trans hzR)
  -- the intermediate point `w = R_{u+s, s'-s} z`
  set w : ℂ := revMap (vrev W (u + s + (s' - s))) (s' - s) z with hw
  have hwH : w ∈ H := im_revMap_pos (continuous_vrev hW _) hz hh
  have hWc : Continuous (vrev W (u + s)) := continuous_vrev hW (u + s)
  -- displacement `‖z - w‖ ≤ ε + 2h/τ`
  have hdisp : ‖z - w‖ ≤ ε + 2 * (s' - s) / τ := by
    rw [norm_sub_rev, hw]
    refine (norm_revMap_vrev_sub_self_le (W := W) hW ha hh (fun t ht t' ht' => ?_) hz).trans
      (add_le_add le_rfl (div_le_div_of_nonneg_left (by linarith : (0 : ℝ) ≤ 2 * (s' - s))
        hτ hzim))
    exact hosc t ⟨by linarith [ht.1], by linarith [ht.2]⟩ t' ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
      (by rw [abs_sub_le_iff]; constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2])
  -- the flow decomposition
  have hsplit : RUS W (u, s') z = RUS W (u, s) w := by
    have h := revMap_vrev_split (W := W) hW ha hs hh hsr hz
    rw [show s + (s' - s) = s' by ring] at h
    show revMap (vrev W (u + s')) s' z = revMap (vrev W (u + s)) s w
    rw [hw, ← h, show u + s + (s' - s) = u + s' by ring]
  -- the two-point upper bound for `R_{u,s}` at the points `z` and `w`
  have hzR0 : z.im ≤ Real.sqrt (R ^ 2 + 4 * T) := by
    refine (le_abs_self z.im).trans (Real.abs_le_sqrt ?_)
    nlinarith [hzR', (show (0 : ℝ) < z.im from hz).le, sq_nonneg T, sq_nonneg R]
  have hwR0 : w.im ≤ Real.sqrt (R ^ 2 + 4 * T) := by
    rw [hw]
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    have h1 := im_revMap_sq_le (continuous_vrev hW (u + s + (s' - s))) hz hh
    have h2 : z.im ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hz.le hzR' 2
    have h3 : s' - s ≤ T := by linarith
    nlinarith [h1, h2, h3]
  have hwτ : τ ≤ w.im := hzim.trans (im_le_im_revMap _ (continuous_vrev hW _) z hz hh)
  have hkey := norm_revMap_sub_mul_le_upper (W := vrev W (u + s)) hWc (T := s) hs hτ hzim hwτ
    hzR0 hwR0
  have hsqrt : Real.sqrt (Real.sqrt (R ^ 2 + 4 * T) ^ 2 + 4 * s) ≤ Real.sqrt (R ^ 2 + 8 * T) := by
    refine Real.sqrt_le_sqrt ?_
    rw [Real.sq_sqrt (by positivity)]
    linarith
  have hmain : ‖RUS W (u, s') z - RUS W (u, s) z‖ * τ ≤
      (ε + 2 * (s' - s) / τ) * Real.sqrt (R ^ 2 + 8 * T) := by
    rw [hsplit, norm_sub_rev]
    simp only [RUS_apply]
    refine hkey.trans ?_
    exact mul_le_mul hdisp hsqrt (Real.sqrt_nonneg _)
      (add_nonneg hε0 (div_nonneg (by linarith) hτ.le))
  rw [le_div_iff₀ hτ]
  exact hmain

end RegUnif
end QuantumZipper
