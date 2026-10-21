import SmallGammaGeodesics.CC.ChainDet
import LQGMetric.Papers.GM.S3.GoodAnnulusMeas

/-!
# Deterministic steps of [3] Thm 3.4 / Prop 3.1 on the domain (track CC, packet CC8)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D13**, steps 1–4, for an
extended-valued `d : ℂ → ℂ → [0,∞]` with the triangle inequality (in the application
`d = D^ϕ = confMetric D ϕ V h̄ f`) and a continuous metric `Dm` (in the application `D_h`).

* `diagZero d`: `d` with the diagonal set to `0` (CC2 pitfall 1: `ChainDetExt` needs `d x x = 0`,
  while `confMetric` is `∞` on the diagonal outside `V`); `diagZero_triangle`.
* `exists_geod_confined` (D13.1, confinement): `Dm`-geodesics between close points of a compact
  `K` stay in `B̄_δ` of their starting point.
* `exists_near_le_of_cover` (D13.2–3, chaining): if every point of a set `S` containing a geodesic
  from `z₁` to `z₂` is in `B_{r/2}(w)` for a good `(w, r)` with `r ∈ [ε², ε]`, and good annuli
  satisfy `d(u, v) ≤ C · Dm(∂B_{r/2}(w), ∂B_r(w))` on `∂B_r(w)`, then `d(x, y) ≤ C · Dm(z₁, z₂)` for
  some `x, y` within `2ε` of `z₁, z₂` (via `chainDetExt`).
* `le_of_forall_near` (D13.4, limits): continuity of `d` on `V × V`.
* `local_le_of_covers`: the three steps together: covers at arbitrarily small scales give
  `d(x, y) ≤ C · Dm(x, y)` for close points of `K`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.Blueprint

/-! ## 1. The function with zero diagonal -/

/-- `d` with the diagonal set to `0` -/
def diagZero (d : ℂ → ℂ → ℝ≥0∞) (x y : ℂ) : ℝ≥0∞ := if x = y then 0 else d x y

lemma diagZero_self (d : ℂ → ℂ → ℝ≥0∞) (x : ℂ) : diagZero d x x = 0 := by
  simp [diagZero]

lemma diagZero_of_ne (d : ℂ → ℂ → ℝ≥0∞) {x y : ℂ} (h : x ≠ y) : diagZero d x y = d x y := by
  simp [diagZero, h]

lemma diagZero_le (d : ℂ → ℂ → ℝ≥0∞) (x y : ℂ) : diagZero d x y ≤ d x y := by
  by_cases h : x = y
  · simp [diagZero, h]
  · rw [diagZero_of_ne d h]

lemma diagZero_triangle {d : ℂ → ℂ → ℝ≥0∞} (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (x y z : ℂ) : diagZero d x z ≤ diagZero d x y + diagZero d y z := by
  by_cases hxz : x = z
  · rw [hxz, diagZero_self]
    exact zero_le
  rw [diagZero_of_ne d hxz]
  by_cases hxy : x = y
  · subst hxy
    rw [diagZero_self, zero_add, diagZero_of_ne d hxz]
  by_cases hyz : y = z
  · subst hyz
    rw [diagZero_self, add_zero, diagZero_of_ne d hxy]
  rw [diagZero_of_ne d hxy, diagZero_of_ne d hyz]
  exact htri x y z

/-! ## 2. Confinement of geodesics (CC0 D13.1) -/

/-- **Confinement** (CC0 D13 step 1, deterministic): for a continuous metric `Dm`, a compact `K` and
`δ > 0` there is `ρ > 0` such that every `Dm`-geodesic between points `z₁, z₂ ∈ K` with
`|z₁ − z₂| ≤ ρ` stays in `B̄_δ(z₁)`. (`Dm` is bounded below by `m > 0` on pairs `(x, y)`, `x ∈ K`,
`|y − x| = δ`, and `Dm(z₁, z₂) < m` for close points by uniform continuity.) -/
theorem exists_geod_confined (Dm : ContMetric) {K : Set ℂ} (hK : IsCompact K) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z₁ ∈ K, ∀ z₂ ∈ K, ‖z₁ - z₂‖ ≤ ρ → ∀ η : C(unitInterval, ℂ),
      IsGeod01 Dm z₁ z₂ η → ∀ t, η t ∈ closedBall z₁ δ := by
  rcases K.eq_empty_or_nonempty with hKe | ⟨x₀, hx₀⟩
  · refine ⟨1, one_pos, fun z₁ hz₁ => ?_⟩
    rw [hKe] at hz₁
    exact absurd hz₁ (notMem_empty z₁)
  -- the compact set of pairs at distance `δ`
  set T : Set (ℂ × ℂ) := {p | p.1 ∈ K ∧ ‖p.2 - p.1‖ = δ} with hTdef
  have hTc : IsCompact T := by
    refine (hK.prod (hK.cthickening (r := δ))).of_isClosed_subset ?_ ?_
    · exact (hK.isClosed.preimage continuous_fst).inter
        (isClosed_eq (continuous_snd.sub continuous_fst).norm continuous_const)
    · rintro ⟨x, y⟩ ⟨hx, hxy⟩
      exact ⟨hx, mem_cthickening_of_dist_le y x δ K hx (by rw [dist_eq_norm, hxy])⟩
  have hTne : T.Nonempty := ⟨(x₀, x₀ + (δ : ℂ)), hx₀, by
    simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]⟩
  obtain ⟨p₀, hp₀, hmin⟩ := hTc.exists_isMinOn hTne Dm.1.continuous.continuousOn
  have hm : 0 < Dm.1 p₀ := by
    refine lt_of_le_of_ne (Dm.nonneg p₀.1 p₀.2) fun h0 => ?_
    have he := Dm.2.eq_of_eq_zero p₀.1 p₀.2 h0.symm
    have h2 := hp₀.2
    rw [he, sub_self, norm_zero] at h2
    linarith
  -- uniform continuity near the diagonal
  obtain ⟨ρ', hρ', hρK⟩ := Metric.uniformContinuousOn_iff.1
    ((hK.prod hK).uniformContinuousOn_of_continuous Dm.1.continuous.continuousOn) _ hm
  refine ⟨ρ' / 2, by positivity, fun z₁ hz₁ z₂ hz₂ hz η hη t => ?_⟩
  have hD12 : Dm.1 (z₁, z₂) < Dm.1 p₀ := by
    have hd : dist (z₁, z₂) (z₁, z₁) < ρ' := by
      rw [Prod.dist_eq, dist_self, dist_eq_norm, max_eq_right (norm_nonneg _), norm_sub_rev]
      linarith
    have := hρK (z₁, z₂) ⟨hz₁, hz₂⟩ (z₁, z₁) ⟨hz₁, hz₁⟩ hd
    rw [Real.dist_eq, Dm.2.self_eq_zero, sub_zero] at this
    exact lt_of_abs_lt this
  by_contra hout
  rw [mem_closedBall, dist_eq_norm, not_le] at hout
  -- intermediate value theorem on the unit interval
  have hcont : Continuous fun s : unitInterval => ‖η s - z₁‖ :=
    (η.continuous.sub continuous_const).norm
  have hδmem : δ ∈ Icc (‖η 0 - z₁‖) (‖η t - z₁‖) := by
    rw [hη.1, sub_self, norm_zero]
    exact ⟨hδ.le, hout.le⟩
  obtain ⟨s, hs⟩ := intermediate_value_univ 0 t hcont hδmem
  have h1 : Dm.1 p₀ ≤ Dm.1 (z₁, η s) := isMinOn_iff.1 hmin (z₁, η s) ⟨hz₁, hs⟩
  have h2 : Dm.1 (z₁, η s) ≤ Dm.1 (z₁, z₂) := by
    have he := hη.2.2 0 s
    rw [hη.1] at he
    rw [he]
    have hs1 : |(s : ℝ) - ((0 : unitInterval) : ℝ)| ≤ 1 := by
      rw [Set.Icc.coe_zero, sub_zero, abs_of_nonneg s.2.1]
      exact s.2.2
    calc |(s : ℝ) - ((0 : unitInterval) : ℝ)| * Dm.1 (z₁, z₂) ≤ 1 * Dm.1 (z₁, z₂) :=
          mul_le_mul_of_nonneg_right hs1 (Dm.nonneg _ _)
      _ = Dm.1 (z₁, z₂) := one_mul _
  linarith

/-! ## 3. Chaining along a geodesic (CC0 D13.2–3) -/

/-- **Chaining along a geodesic** (CC0 D13 steps 2–3, deterministic): `chainDetExt` applied to
`diagZero d`, the geodesic `P(t) = η(t)` and `ℓ(t) = t · Dm(z₁, z₂)`. For a good `(w, r)` and a
crossing of `A_{r/2,r}(w)` by `P` on `[a, b]`, the intermediate value theorem gives a sub-crossing
from `∂B_{r/2}(w)` to `∂B_r(w)`, so `Dm(∂B_{r/2}(w), ∂B_r(w)) ≤ ℓ(b) − ℓ(a)`. -/
theorem exists_near_le_of_cover (Dm : ContMetric) {d : ℂ → ℂ → ℝ≥0∞}
    (htri : ∀ x y z, d x z ≤ d x y + d y z) {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (good : ℂ → ℝ → Prop)
    (hgood : ∀ w r, good w r → ∀ u ∈ sphere w r, ∀ v ∈ sphere w r,
      d u v ≤ ENNReal.ofReal C * setDist Dm (sphere w (r / 2)) (sphere w r))
    {S : Set ℂ} (hcov : ∀ x ∈ S, ∃ w r, ε ^ 2 ≤ r ∧ r ≤ ε ∧ ‖x - w‖ < r / 2 ∧ good w r)
    {z₁ z₂ : ℂ} {η : C(unitInterval, ℂ)} (hη : IsGeod01 Dm z₁ z₂ η) (hηS : ∀ t, η t ∈ S) :
    ∃ x y, ‖x - z₁‖ ≤ 2 * ε ∧ ‖y - z₂‖ ≤ 2 * ε ∧
      diagZero d x y ≤ ENNReal.ofReal (C * Dm.1 (z₁, z₂)) := by
  set L := Dm.1 (z₁, z₂) with hLdef
  have hL : 0 ≤ L := Dm.nonneg _ _
  set P : ℝ → ℂ := fun t => η (projIcc 0 1 zero_le_one t) with hPdef
  have hPc : Continuous P := η.continuous.comp continuous_projIcc
  have hPgeo : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, Dm.1 (P a, P b) = |b - a| * L := by
    intro a ha b hb
    simp only [hPdef, projIcc_of_mem _ ha, projIcc_of_mem _ hb]
    exact hη.2.2 ⟨a, ha⟩ ⟨b, hb⟩
  have hP0 : P 0 = z₁ := by
    simp only [hPdef, projIcc_left]
    exact hη.1
  have hP1 : P 1 = z₂ := by
    simp only [hPdef, projIcc_right]
    exact hη.2.1
  have hgood' : ∀ w r, good w r → ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b →
      ‖P a - w‖ < r / 2 → ‖P b - w‖ = r → ∀ u ∈ sphere w r, ∀ v ∈ sphere w r,
      diagZero d u v ≤ ENNReal.ofReal (C * (b * L - a * L)) := by
    intro w r hg a ha b hb hab hPa hPb u hu v hv
    refine (diagZero_le d u v).trans ((hgood w r hg u hu v hv).trans ?_)
    have hr : 0 ≤ r := hPb ▸ norm_nonneg _
    have hcont : ContinuousOn (fun t => ‖P t - w‖) (Icc a b) :=
      (hPc.sub continuous_const).norm.continuousOn
    obtain ⟨a', ha', hPa'⟩ := intermediate_value_Icc hab hcont
      (show r / 2 ∈ Icc ‖P a - w‖ ‖P b - w‖ from ⟨hPa.le, by rw [hPb]; linarith⟩)
    have ha'01 : a' ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans ha'.1, ha'.2.trans hb.2⟩
    have hsd : setDist Dm (sphere w (r / 2)) (sphere w r) ≤ ENNReal.ofReal (Dm.1 (P a', P b)) := by
      rw [GM.setDist_eq_iInf]
      exact iInf₂_le_of_le (P a') (mem_sphere_iff_norm.2 hPa')
        (iInf₂_le (P b) (mem_sphere_iff_norm.2 hPb))
    rw [hPgeo a' ha'01 b hb, abs_of_nonneg (sub_nonneg.2 ha'.2)] at hsd
    have hmono : a * L ≤ a' * L := mul_le_mul_of_nonneg_right ha'.1 hL
    calc ENNReal.ofReal C * setDist Dm (sphere w (r / 2)) (sphere w r)
        ≤ ENNReal.ofReal C * ENNReal.ofReal ((b - a') * L) := by gcongr
      _ = ENNReal.ofReal (C * ((b - a') * L)) := (ENNReal.ofReal_mul hC).symm
      _ ≤ ENNReal.ofReal (C * (b * L - a * L)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith) hC)
  obtain ⟨x, y, hx, hy, hxy⟩ := chainDetExt (diagZero d) (diagZero_triangle htri)
    (diagZero_self d) (C := C) (ε := ε) (ρ := ε ^ 2) hC (by positivity) P hPc.continuousOn
    (fun t => t * L) (fun a _ b _ hab => mul_le_mul_of_nonneg_right hab hL) good
    (fun s _ => hcov (P s) (hηS _)) hgood'
  refine ⟨x, y, hP0 ▸ hx, hP1 ▸ hy, hxy.trans (le_of_eq ?_)⟩
  congr 1
  ring

/-! ## 4. Limits (CC0 D13.4) -/

/-- **Passing to the limit** (CC0 D13 step 4): if `d` is continuous on `V × V` and, for every
`ε > 0`, `diagZero d x y ≤ c` for some `x, y` within `ε` of distinct points `z₁, z₂ ∈ V`, then
`d z₁ z₂ ≤ c`. -/
theorem le_of_forall_near {d : ℂ → ℂ → ℝ≥0∞} {V : Set ℂ} (hV : IsOpen V)
    (hd : ContinuousOn (fun p : ℂ × ℂ => d p.1 p.2) (V ×ˢ V)) {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ V)
    (hz₂ : z₂ ∈ V) (hne : z₁ ≠ z₂) {c : ℝ≥0∞}
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ x y, ‖x - z₁‖ ≤ ε ∧ ‖y - z₂‖ ≤ ε ∧ diagZero d x y ≤ c) :
    d z₁ z₂ ≤ c := by
  by_contra hlt
  rw [not_le] at hlt
  have hev : ∀ᶠ p in 𝓝 (z₁, z₂), c < d p.1 p.2 := by
    have h1 := hd (z₁, z₂) ⟨hz₁, hz₂⟩
    rw [ContinuousWithinAt, (hV.prod hV).nhdsWithin_eq ⟨hz₁, hz₂⟩] at h1
    exact h1 (Ioi_mem_nhds hlt)
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hpos : 0 < ‖z₁ - z₂‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨x, y, hx, hy, hxy⟩ := hnear (min (ε₁ / 2) (‖z₁ - z₂‖ / 3)) (by positivity)
  have hm1 := min_le_left (ε₁ / 2) (‖z₁ - z₂‖ / 3)
  have hm2 := min_le_right (ε₁ / 2) (‖z₁ - z₂‖ / 3)
  have hc : c < d x y := hball (show dist (x, y) (z₁, z₂) < ε₁ by
    rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]
    exact max_lt (by linarith) (by linarith))
  have hne' : x ≠ y := by
    rintro rfl
    have : ‖z₁ - z₂‖ ≤ ‖x - z₂‖ + ‖x - z₁‖ := by
      calc ‖z₁ - z₂‖ = ‖(x - z₂) - (x - z₁)‖ := by ring_nf
        _ ≤ ‖x - z₂‖ + ‖x - z₁‖ := norm_sub_le _ _
    linarith
  rw [diagZero_of_ne d hne'] at hxy
  exact absurd hxy (not_le.2 hc)

/-! ## 5. Local comparison from covers at small scales -/

/-- **Local comparison from covers at arbitrarily small scales** (CC0 D13 steps 1–4,
deterministic): `d(x, y) ≤ C · Dm(x, y)` for points of `K` at distance `≤ ρ`, if `d` has the
triangle inequality, is continuous on `V × V` and zero on its diagonal, `Dm`-geodesics exist, good
annuli satisfy the `E^{LM}` bound, and for arbitrarily small `ε` every point of the
`δ`-neighbourhood of `K` is covered by a good `B_{r/2}(w)` with `r ∈ [ε², ε]`. -/
theorem local_le_of_covers (Dm : ContMetric) {d : ℂ → ℂ → ℝ≥0∞}
    (htri : ∀ x y z, d x z ≤ d x y + d y z) {V : Set ℂ} (hVo : IsOpen V)
    (hd : ContinuousOn (fun p : ℂ × ℂ => d p.1 p.2) (V ×ˢ V)) (hd0 : ∀ x ∈ V, d x x = 0)
    (hgeo : ∀ z w : ℂ, ∃ η, IsGeod01 Dm z w η) {K : Set ℂ} (hK : IsCompact K) (hKV : K ⊆ V)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (good : ℂ → ℝ → Prop)
    (hgood : ∀ w r, good w r → ∀ u ∈ sphere w r, ∀ v ∈ sphere w r,
      d u v ≤ ENNReal.ofReal C * setDist Dm (sphere w (r / 2)) (sphere w r))
    (hcovers : ∀ ε₀ : ℝ, 0 < ε₀ → ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ ∧ ∀ x ∈ cthickening δ K,
      ∃ w r, ε ^ 2 ≤ r ∧ r ≤ ε ∧ ‖x - w‖ < r / 2 ∧ good w r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ ρ →
      d x y ≤ ENNReal.ofReal (C * Dm.1 (x, y)) := by
  obtain ⟨ρ, hρ, hconf⟩ := exists_geod_confined Dm hK hδ
  refine ⟨ρ, hρ, fun x hx y hy hxy => ?_⟩
  by_cases hne : x = y
  · rw [hne, hd0 y (hKV hy)]
    exact zero_le
  obtain ⟨η, hη⟩ := hgeo x y
  have hηS : ∀ t, η t ∈ cthickening δ K := fun t =>
    closedBall_subset_cthickening hx δ (hconf x hx y hy hxy η hη t)
  refine le_of_forall_near hVo hd (hKV hx) (hKV hy) hne fun ε₀ hε₀ => ?_
  obtain ⟨ε, hε, hεε₀, hcov⟩ := hcovers (ε₀ / 2) (by positivity)
  obtain ⟨x', y', hx', hy', hxy'⟩ :=
    exists_near_le_of_cover Dm htri hC hε good hgood hcov hη hηS
  exact ⟨x', y', by linarith, by linarith, hxy'⟩

end SmallGammaGeodesics.CC
