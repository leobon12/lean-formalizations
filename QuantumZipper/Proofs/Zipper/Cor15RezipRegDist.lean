import QuantumZipper.Proofs.Zipper.Cor15PosRezip

/-!
# Corollary 1.5, input R: boundary distance and pushed measures (deterministic part)

Task COR15-R (`Cor15Group.Cor15RezipRegStmt`, `Cor15PosRezip.lean`). The measures in (R) are
`ν = σ.map f`, `σ` a dyadic folded circle and `f = revMapInv V t` the inverse of the reverse
map `F = revMap V t : ℍ → D := F(ℍ) = ℍ \ K`. Unlike the measures of `CoordRegComp`, `ν`
reaches `ℝ`: `Im f(z) → 0` as `z → ∂D`. This file gives the deterministic estimates that turn a
Hölder bound on `F` into the hypotheses of the general RC3 theorem
(`CoordReg.ae_evalReg_coordChange_revMap_gen`):

* `measurable_revMapInv`: `f` is Borel (continuous on the open set `D`, `0` off it), so the
  pushforward `σ.map f` is not a junk measure.
* `infDist_compl_le_of_holder` (**boundary distance**): if `F` is `C, β`-Hölder on
  `{u ∈ ℍ, ‖u‖ ≤ ρ}`, then `dist(F u, Dᶜ) ≤ C (Im u)^β` for such `u`. Hence
  `min(Im z, dist(z, S)) ≤ C (Im f z)^β` for `z ∈ D`, `S ⊇ ℍ \ D` (`min_im_infDist_le_of_holder`).
* `map_revMapInv_im_le` (**strip transfer**): `ν{Im ≤ s} ≤ σ{Im ≤ C s^β} + σ{dist(·, S) ≤ C s^β}`
  for any `S ⊇ ℍ \ D` (e.g. the SLE trace),
  so a strip bound for `ν` follows from the geometry of `σ` near `ℝ` and a bound on the
  `σ`-mass of neighbourhoods of the hull (the SLE one-point estimate, Beffara 2008, Prop. 4).
* `map_revMapInv_closedBall_le` (**Frostman transfer**): `ν(B(w,r)) ⊆` the `σ`-mass of a ball of
  radius `C (2r)^β`.

The Hölder bound on `F` is Rohde–Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005),
Thm 5.2 (p. 21), in the reverse-time form `RS.ae_revMap_holder`. The boundary-distance argument
is an **own elementary argument** (compactness of `f` on a closed ball inside `D` along the
vertical segment below `u`); the standard route would be the Koebe/Schwarz estimate
`dist(F u, ∂D) ≤ 4 |F'(u)| Im u` plus a Cauchy estimate, which is longer here.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

variable {V : ℝ → ℝ} {t : ℝ}

theorem continuousOn_revMapInv (hV : Continuous V) (ht : 0 ≤ t) :
    ContinuousOn (revMapInv V t) (revMap V t '' H) := by
  rintro _ ⟨z, hz, rfl⟩
  exact (hasStrictDerivAt_revMapInv hV ht hz).hasDerivAt.continuousAt.continuousWithinAt

theorem revMapInv_eq_zero_of_notMem {w : ℂ} (hw : w ∉ revMap V t '' H) :
    revMapInv V t w = 0 := by
  unfold revMapInv
  rw [dif_neg]
  rintro ⟨z, ⟨hz, hzw⟩, -⟩
  exact hw ⟨z, hz, hzw⟩

theorem revMapInv_mem_H (hV : Continuous V) (ht : 0 ≤ t) {w : ℂ} (hw : w ∈ revMap V t '' H) :
    revMapInv V t w ∈ H ∧ revMap V t (revMapInv V t w) = w := by
  obtain ⟨z, hz, rfl⟩ := hw
  rw [revMapInv_revMap hV ht hz]
  exact ⟨hz, rfl⟩

/-- `f = revMapInv V t` is Borel measurable. -/
theorem measurable_revMapInv (hV : Continuous V) (ht : 0 ≤ t) : Measurable (revMapInv V t) := by
  classical
  have hD := isOpen_revMap_image hV ht
  have he : revMapInv V t = (revMap V t '' H).piecewise (revMapInv V t) (fun _ => 0) := by
    funext w
    by_cases hw : w ∈ revMap V t '' H
    · simp [Set.piecewise, hw]
    · simp [Set.piecewise, hw, revMapInv_eq_zero_of_notMem hw]
  rw [he]
  exact (continuousOn_revMapInv hV ht).measurable_piecewise continuous_const.continuousOn
    hD.measurableSet

/-- **Boundary distance from Hölder continuity** (own elementary argument). If
`F = revMap V t` is `C, β`-Hölder on `{u ∈ ℍ, ‖u‖ ≤ ρ}`, then `dist(F u, Dᶜ) ≤ C (Im u)^β`. -/
theorem infDist_compl_le_of_holder (hV : Continuous V) (ht : 0 ≤ t) {ρ C β : ℝ} (hC : 0 ≤ C)
    (hβ : 0 < β)
    (hHol : ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖revMap V t z - revMap V t w‖ ≤ C * ‖z - w‖ ^ β)
    {u : ℂ} (hu : u ∈ H) (huρ : ‖u‖ ≤ ρ) :
    infDist (revMap V t u) (revMap V t '' H)ᶜ ≤ C * u.im ^ β := by
  have hu0 : 0 < u.im := hu
  set D := revMap V t '' H with hDdef
  set r := C * u.im ^ β with hr
  by_contra hlt
  push Not at hlt
  have hKD : closedBall (revMap V t u) r ⊆ D := by
    intro y hy
    by_contra hyD
    have h1 := infDist_le_dist_of_mem (x := revMap V t u) (show y ∈ Dᶜ from hyD)
    rw [dist_comm] at h1
    exact absurd (h1.trans (mem_closedBall.1 hy)) (not_le.2 hlt)
  have hcomp : IsCompact (revMapInv V t '' closedBall (revMap V t u) r) :=
    (isCompact_closedBall _ _).image_of_continuousOn
      ((continuousOn_revMapInv hV ht).mono hKD)
  have hr0 : 0 ≤ r := mul_nonneg hC (Real.rpow_nonneg hu0.le _)
  have hne : (revMapInv V t '' closedBall (revMap V t u) r).Nonempty :=
    ⟨_, mem_image_of_mem _ (mem_closedBall_self hr0)⟩
  obtain ⟨p, hp, hpmin⟩ := hcomp.exists_isMinOn hne Complex.continuous_im.continuousOn
  have hpH : 0 < p.im := by
    obtain ⟨y, hy, rfl⟩ := hp
    exact (revMapInv_mem_H hV ht (hKD hy)).1
  set s := min u.im (p.im / 2) with hs
  have hs0 : 0 < s := lt_min hu0 (by linarith)
  have hsu : s ≤ u.im := min_le_left _ _
  set us : ℂ := ⟨u.re, s⟩ with hus
  have husH : us ∈ H := hs0
  have hsq : ‖us‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [hus]
    nlinarith
  have husρ : ‖us‖ ≤ ρ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq |>.trans huρ
  have hdiff : ‖us - u‖ ≤ u.im := by
    have : us - u = ((s - u.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hus]
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have hmem : revMap V t us ∈ closedBall (revMap V t u) r := by
    rw [mem_closedBall, dist_eq_norm]
    refine (hHol us husH u hu husρ huρ).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hdiff hβ.le) hC
  have h2 := hpmin (mem_image_of_mem (revMapInv V t) hmem)
  rw [revMapInv_revMap hV ht husH] at h2
  have : s ≤ p.im / 2 := min_le_right _ _
  change p.im ≤ s at h2
  linarith

/-- `min(Im z, dist(z, S)) ≤ dist(z, Dᶜ)` for any `S ⊇ ℍ \ D`. -/
theorem min_im_infDist_le_infDist_compl {D S : Set ℂ} (hDH : D ⊆ H) (hS : H \ D ⊆ S) (z : ℂ) :
    min z.im (infDist z S) ≤ infDist z Dᶜ := by
  have hne : (Dᶜ).Nonempty := ⟨0, fun h0 => by
    have h := hDH h0
    change (0 : ℝ) < (0 : ℂ).im at h
    simp at h⟩
  refine (le_infDist hne).2 fun y hy => ?_
  by_cases hyH : y ∈ H
  · exact (min_le_right _ _).trans (infDist_le_dist_of_mem (hS ⟨hyH, hy⟩))
  · refine (min_le_left _ _).trans ?_
    have hy0 : y.im ≤ 0 := not_lt.1 hyH
    have h1 : |(z - y).im| ≤ ‖z - y‖ := Complex.abs_im_le_norm _
    rw [dist_eq_norm]
    simp only [Complex.sub_im] at h1
    linarith [le_abs_self (z.im - y.im)]

theorem revMap_image_subset_H (hV : Continuous V) (ht : 0 ≤ t) : revMap V t '' H ⊆ H := by
  rintro _ ⟨z, hz, rfl⟩
  exact TwoPoint.im_revMap_pos hV hz ht

/-- **Boundary distance, pulled back.** For `z ∈ D` with `‖f z‖ ≤ ρ`:
`min(Im z, dist(z, S)) ≤ C (Im f z)^β` for any `S ⊇ ℍ \ D` (e.g. the SLE trace). -/
theorem min_im_infDist_le_of_holder (hV : Continuous V) (ht : 0 ≤ t) {ρ C β : ℝ} {S : Set ℂ}
    (hS : H \ revMap V t '' H ⊆ S) (hC : 0 ≤ C)
    (hβ : 0 < β)
    (hHol : ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖revMap V t z - revMap V t w‖ ≤ C * ‖z - w‖ ^ β)
    {z : ℂ} (hz : z ∈ revMap V t '' H) (hzρ : ‖revMapInv V t z‖ ≤ ρ) :
    min z.im (infDist z S) ≤ C * (revMapInv V t z).im ^ β := by
  obtain ⟨hfH, hFf⟩ := revMapInv_mem_H hV ht hz
  have h := infDist_compl_le_of_holder hV ht hC hβ hHol hfH hzρ
  rw [hFf] at h
  exact (min_im_infDist_le_infDist_compl (revMap_image_subset_H hV ht) hS z).trans h

section Transfer

variable {ρ C β : ℝ} {σ : Measure ℂ}

/-- **Strip transfer.** Under the Hölder bound, for `σ` carried by `D` with `‖f‖ ≤ ρ` a.e.,
`(σ.map f){Im ≤ s} ≤ σ{Im ≤ C s^β} + σ{dist(·, S) ≤ C s^β}` for any `S ⊇ ℍ \ D`. -/
theorem map_revMapInv_im_le (hV : Continuous V) (ht : 0 ≤ t) {S : Set ℂ}
    (hS : H \ revMap V t '' H ⊆ S) (hC : 0 ≤ C) (hβ : 0 < β)
    (hHol : ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖revMap V t z - revMap V t w‖ ≤ C * ‖z - w‖ ^ β)
    (hσD : ∀ᵐ z ∂σ, z ∈ revMap V t '' H) (hσρ : ∀ᵐ z ∂σ, ‖revMapInv V t z‖ ≤ ρ) (s : ℝ) :
    σ.map (revMapInv V t) {w | w.im ≤ s} ≤
      σ {z | z.im ≤ C * s ^ β} + σ {z | infDist z S ≤ C * s ^ β} := by
  rw [Measure.map_apply (measurable_revMapInv hV ht)
    (measurableSet_le Complex.measurable_im measurable_const)]
  refine (measure_mono_ae ?_).trans (measure_union_le _ _)
  filter_upwards [hσD, hσρ] with z hzD hzρ hz
  have hz' : (revMapInv V t z).im ≤ s := hz
  have h := min_im_infDist_le_of_holder hV ht hS hC hβ hHol hzD hzρ
  have hfs : C * (revMapInv V t z).im ^ β ≤ C * s ^ β :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (revMapInv_mem_H hV ht hzD).1.le hz' hβ.le) hC
  show z ∈ {z | z.im ≤ C * s ^ β} ∪ {z | infDist z S ≤ C * s ^ β}
  rcases min_le_iff.1 (h.trans hfs) with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

/-- **Frostman transfer.** Under the Hölder bound, for `σ` carried by `D` with `‖f‖ ≤ ρ` a.e.,
each ball `B(w, r)` has `(σ.map f)`-mass at most the `σ`-mass of a ball of radius `C (2r)^β`. -/
theorem map_revMapInv_closedBall_le (hV : Continuous V) (ht : 0 ≤ t) (hC : 0 ≤ C) (hβ : 0 < β)
    (hHol : ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖revMap V t z - revMap V t w‖ ≤ C * ‖z - w‖ ^ β)
    (hσD : ∀ᵐ z ∂σ, z ∈ revMap V t '' H) (hσρ : ∀ᵐ z ∂σ, ‖revMapInv V t z‖ ≤ ρ)
    (w : ℂ) (r : ℝ) :
    ∃ z₀ : ℂ, σ.map (revMapInv V t) (closedBall w r) ≤ σ (closedBall z₀ (C * (2 * r) ^ β)) := by
  classical
  rw [Measure.map_apply (measurable_revMapInv hV ht) isClosed_closedBall.measurableSet]
  by_cases h : ∃ z₀, z₀ ∈ revMap V t '' H ∧ ‖revMapInv V t z₀‖ ≤ ρ ∧
      revMapInv V t z₀ ∈ closedBall w r
  · obtain ⟨z₀, h0D, h0ρ, h0B⟩ := h
    refine ⟨z₀, measure_mono_ae ?_⟩
    filter_upwards [hσD, hσρ] with z hzD hzρ hz
    have hz' : revMapInv V t z ∈ closedBall w r := hz
    obtain ⟨hfH, hFf⟩ := revMapInv_mem_H hV ht hzD
    obtain ⟨hf0H, hFf0⟩ := revMapInv_mem_H hV ht h0D
    have hd : ‖revMapInv V t z - revMapInv V t z₀‖ ≤ 2 * r := by
      have h3 := dist_triangle_right (revMapInv V t z) (revMapInv V t z₀) w
      rw [dist_eq_norm] at h3
      linarith [mem_closedBall.1 hz', mem_closedBall.1 h0B]
    show z ∈ closedBall z₀ _
    rw [mem_closedBall, dist_eq_norm]
    calc ‖z - z₀‖ = ‖revMap V t (revMapInv V t z) - revMap V t (revMapInv V t z₀)‖ := by
          rw [hFf, hFf0]
      _ ≤ C * ‖revMapInv V t z - revMapInv V t z₀‖ ^ β := hHol _ hfH _ hf0H hzρ h0ρ
      _ ≤ C * (2 * r) ^ β :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hd hβ.le) hC
  · refine ⟨0, le_trans (measure_mono_ae (t := (∅ : Set ℂ)) ?_) (by simp)⟩
    filter_upwards [hσD, hσρ] with z hzD hzρ hz
    exact h ⟨z, hzD, hzρ, hz⟩

end Transfer

end Cor15Group
end QuantumZipper
