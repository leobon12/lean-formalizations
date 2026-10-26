import SupercriticalLFPPAS.Core.Interfaces
import SupercriticalLFPPAS.Main.Transfer
import SupercriticalLFPPAS.Main.LowerLimit
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS1S2.Bridges
import SupercriticalLQGUniqueness.Uniqueness.Geodesics.SetGeodesics.SetGeoExists

/-!
# (5.6) and its q′ analogue: the deterministic part (packet UND)

Paper §5, l. 543–568; SB2 §2.6 bullets "(5.6)" and "q′ direction", D9 steps 3–4, M9. We use the concentric rational
circles `O = ∂B₁(0)`, `O′ = ∂B₂(0)` (any disjoint positive-radius rational circles are allowed, D9 step 3) and the slightly
displaced rational circles `O_n = ∂B_{a_n}(0)`, `O′_n = ∂B_{b_n}(0)`, `a_n = 1 + 1/(n+3)`, `b_n = 2 − 1/(n+3)`.

* **Crossing** (`und_setDist_sphere_le_internalSetDist`): for any lsc metric `d` and bounded `W`, if `‖x‖ + ρ ≤ a ≤ b ≤
  ‖y‖ − ρ`, every curve in `W` from `B_ρ(x)` to `B_ρ(y)` crosses the closed annulus `Ā_{a,b}(0)`, so
  `d(∂B_a(0), ∂B_b(0)) ≤ d(B_ρ(x), B_ρ(y); W)` (sealed `acr_le_internalSetDist`, `ambientAcross_le_acr`).
* **Lower semicontinuity on compacts** (`und_lt_apply_of_mem_thickening`, `und_eventually_le_mul`): below `d(K₁, K₂)` the
  metric stays above on a uniform thickening of `K₁ × K₂`; hence `d(O,O′) ≤ κ d(O_n, O′_n)` for large `n`, for every
  `κ > 1` when `0 < d(O,O′) < ∞` (the "monotone limit by compactness and lsc" of SB2 §2.6).
* **The two contradictions** (`und_not_compIn_dsource`, `und_not_compIn_xsource`): on the deterministic content of the good
  events, a comparison `CompIn` with a constant `c ≤ c₀` and `c₀κ² < 1` is impossible, in each direction. The `D`-source
  uses a `D`-geodesic realizing `D(O,O′)` (barrier and length space, `exists_setGeodesic_of_finite`) confined to `B_{R₁}(0)`
  by `D(O,O′) < D(O, ∂B_{R₁}(0))`; the `X̂`-source uses an LFPP geodesic realizing `X̂(O,O′)` (`LFPPGeodesicStmt`) confined
  by the escape distance.

With these, (5.6) needs neither ordinary LFPP nor (2.1): the circle comparison (2.9) is applied to `O_n, O′_n` (`D`-source)
and to `O, O′` (`X̂`-source), and the crossing replaces the moving-endpoint lower limit.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Identification

open SupercriticalLQGUniqueness (LSCMetric)
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios (setDist)

/-! ### Circles and set distances -/

/-- The rational circle with centre `0` is the Euclidean sphere. -/
theorem und_rationalCircle_zero (r : ℚ) : rationalCircle (0, 0) r = sphere (0 : ℂ) (r : ℝ) := by
  simp [rationalCircle]

/-- Concentric spheres with different radii are disjoint. -/
theorem und_disjoint_sphere {r r' : ℝ} (h : r ≠ r') : Disjoint (sphere (0 : ℂ) r) (sphere 0 r') :=
  Set.disjoint_left.2 fun _ hx hy => h ((mem_sphere_zero_iff_norm.1 hx).symm.trans (mem_sphere_zero_iff_norm.1 hy))

/-- `setDist` is antitone in both sets. -/
theorem und_setDist_mono (d : LSCMetric) {A A' B B' : Set ℂ} (hA : A ⊆ A') (hB : B ⊆ B') :
    setDist d A' B' ≤ setDist d A B :=
  le_iInf₂ fun x hx => le_iInf₂ fun y hy => iInf₂_le_of_le x (hA hx) (iInf₂_le y (hB hy))

/-- **Crossing.** If `‖x‖ + ρ ≤ a ≤ b ≤ ‖y‖ − ρ`, the internal distance in a bounded `W` between the balls `B_ρ(x)` and
`B_ρ(y)` dominates the distance between the spheres `∂B_a(0)` and `∂B_b(0)`. -/
theorem und_setDist_sphere_le_internalSetDist (d : LSCMetric) {W : Set ℂ} (hW : Bornology.IsBounded W) {x y : ℂ}
    {ρ a b : ℝ} (hab : a ≤ b) (hx : ‖x‖ + ρ ≤ a) (hy : b ≤ ‖y‖ - ρ) :
    setDist d (sphere 0 a) (sphere 0 b) ≤
      d.internalSetDist W {z | (z : ℂ) ∈ ball x ρ} {z | (z : ℂ) ∈ ball y ρ} := by
  refine (SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS1S2.ambientAcross_le_acr d 0 a b).trans ?_
  refine SupercriticalLQGUniqueness.B2.Polylog.acr_le_internalSetDist d hW hab _ _ ?_ ?_
  · intro z hz
    have hz' : dist (z : ℂ) x < ρ := hz
    have htri := dist_triangle (z : ℂ) x 0
    simp only [dist_zero_right] at htri ⊢
    linarith
  · intro z hz
    have hz' : dist (z : ℂ) y < ρ := hz
    have htri := dist_triangle y (z : ℂ) 0
    have hzy : dist y (z : ℂ) = dist (z : ℂ) y := dist_comm _ _
    simp only [dist_zero_right] at htri ⊢
    linarith

/-! ### Lower semicontinuity on compacts -/

/-- **Uniform thickening.** Below the set distance of two compact sets, an lsc metric stays above on a uniform
thickening of both sets. -/
theorem und_lt_apply_of_mem_thickening (d : LSCMetric) {K₁ K₂ : Set ℂ} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    {v : ℝ≥0∞} (hv : v < setDist d K₁ K₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ thickening δ K₁, ∀ y ∈ thickening δ K₂, v < d (x, y) := by
  have hopen : IsOpen ((⇑d) ⁻¹' Ioi v) := d.lowerSemicontinuous.isOpen_preimage v
  have hsub : K₁ ×ˢ K₂ ⊆ (⇑d) ⁻¹' Ioi v := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact hv.trans_le (iInf₂_le_of_le x hx (iInf₂_le y hy))
  obtain ⟨δ, hδ, hthick⟩ := (hK₁.prod hK₂).exists_thickening_subset_open hopen hsub
  refine ⟨δ, hδ, fun x hx y hy => ?_⟩
  obtain ⟨x', hx', hxx'⟩ := mem_thickening_iff.1 hx
  obtain ⟨y', hy', hyy'⟩ := mem_thickening_iff.1 hy
  have hmem : (x, y) ∈ thickening δ (K₁ ×ˢ K₂) :=
    mem_thickening_iff.2 ⟨(x', y'), ⟨hx', hy'⟩, by rw [Prod.dist_eq]; exact max_lt hxx' hyy'⟩
  exact hthick hmem

/-- A sphere of nearby positive radius lies in a thickening of the sphere. -/
theorem und_sphere_subset_thickening {r r' δ : ℝ} (hr : 0 < r) (hr' : 0 < r') (h : |r' - r| < δ) :
    sphere (0 : ℂ) r' ⊆ thickening δ (sphere 0 r) := by
  intro z hz
  have hzn : ‖z‖ = r' := mem_sphere_zero_iff_norm.1 hz
  refine mem_thickening_iff.2 ⟨((r / r' : ℝ) : ℂ) * z, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hr hr'), hzn,
      div_mul_cancel₀ _ hr'.ne']
  · have hcoef : (1 : ℝ) - r / r' = (r' - r) / r' := by field_simp
    have heq : z - ((r / r' : ℝ) : ℂ) * z = (((r' - r) / r' : ℝ) : ℂ) * z := by
      rw [← hcoef]; push_cast; ring
    rw [dist_eq_norm, heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, hzn, abs_div, abs_of_pos hr',
      div_mul_cancel₀ _ hr'.ne']
    exact h

/-- The inner displaced radius `a_n = 1 + 1/(n+3)`. -/
def undA (n : ℕ) : ℝ := 1 + 1 / ((n : ℝ) + 3)

/-- The outer displaced radius `b_n = 2 − 1/(n+3)`. -/
def undB (n : ℕ) : ℝ := 2 - 1 / ((n : ℝ) + 3)

theorem und_gap_pos (n : ℕ) : 0 < 1 / ((n : ℝ) + 3) := by positivity

theorem und_gap_le (n : ℕ) : 1 / ((n : ℝ) + 3) ≤ 1 / 3 :=
  one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

theorem undA_pos (n : ℕ) : 0 < undA n := by unfold undA; linarith [und_gap_pos n]

theorem undB_pos (n : ℕ) : 0 < undB n := by unfold undB; linarith [und_gap_le n]

theorem undA_lt_undB (n : ℕ) : undA n < undB n := by unfold undA undB; linarith [und_gap_le n]

/-- The displaced circles are rational circles. -/
theorem und_rationalCircle_undA (n : ℕ) :
    rationalCircle (0, 0) (1 + 1 / ((n : ℚ) + 3)) = sphere (0 : ℂ) (undA n) := by
  rw [und_rationalCircle_zero]
  congr 1
  unfold undA
  push_cast
  ring

theorem und_rationalCircle_undB (n : ℕ) :
    rationalCircle (0, 0) (2 - 1 / ((n : ℚ) + 3)) = sphere (0 : ℂ) (undB n) := by
  rw [und_rationalCircle_zero]
  congr 1
  unfold undB
  push_cast
  ring

theorem und_ratA_pos (n : ℕ) : (0 : ℚ) < 1 + 1 / ((n : ℚ) + 3) := by positivity

theorem und_ratB_pos (n : ℕ) : (0 : ℚ) < 2 - 1 / ((n : ℚ) + 3) := by
  have h : 1 / ((n : ℚ) + 3) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℚ) ≤ n)])
  linarith

/-- **The lsc limit along the displaced circles.** If `0 < d(O, O′) < ∞` and `κ > 1`, then eventually
`d(O, O′) ≤ κ d(O_n, O′_n)`. -/
theorem und_eventually_le_mul (d : LSCMetric) (h0 : setDist d (sphere 0 1) (sphere 0 2) ≠ 0)
    (htop : setDist d (sphere 0 1) (sphere 0 2) ≠ ⊤) {κ : ℝ} (hκ : 1 < κ) :
    ∀ᶠ n : ℕ in atTop, setDist d (sphere 0 1) (sphere 0 2) ≤
      ENNReal.ofReal κ * setDist d (sphere 0 (undA n)) (sphere 0 (undB n)) := by
  set t := setDist d (sphere (0 : ℂ) 1) (sphere 0 2) with ht
  set τ : ℝ := t.toReal with hτ
  have htτ : ENNReal.ofReal τ = t := ENNReal.ofReal_toReal htop
  have hτpos : 0 < τ := ENNReal.toReal_pos h0 htop
  have hκpos : 0 < κ := by linarith
  have hv : ENNReal.ofReal (τ / κ) < t := by
    rw [← htτ, ENNReal.ofReal_lt_ofReal_iff hτpos, div_lt_iff₀ hκpos]
    nlinarith
  obtain ⟨δ, hδ, hthick⟩ := und_lt_apply_of_mem_thickening d (isCompact_sphere 0 1) (isCompact_sphere 0 2) hv
  have hn : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 3) < δ :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hδ)).mono fun n hn =>
      lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by linarith)) hn
  filter_upwards [hn] with n hn
  have h1 : sphere (0 : ℂ) (undA n) ⊆ thickening δ (sphere 0 1) := by
    refine und_sphere_subset_thickening one_pos (undA_pos n) ?_
    rw [show undA n - 1 = 1 / ((n : ℝ) + 3) by unfold undA; ring, abs_of_pos (und_gap_pos n)]
    exact hn
  have h2 : sphere (0 : ℂ) (undB n) ⊆ thickening δ (sphere 0 2) := by
    refine und_sphere_subset_thickening two_pos (undB_pos n) ?_
    rw [show undB n - 2 = -(1 / ((n : ℝ) + 3)) by unfold undB; ring, abs_neg, abs_of_pos (und_gap_pos n)]
    exact hn
  have hle : ENNReal.ofReal (τ / κ) ≤ setDist d (sphere 0 (undA n)) (sphere 0 (undB n)) :=
    le_iInf₂ fun x hx => le_iInf₂ fun y hy => (hthick x (h1 hx) y (h2 hy)).le
  calc t = ENNReal.ofReal κ * ENNReal.ofReal (τ / κ) := by
        rw [← ENNReal.ofReal_mul hκpos.le, mul_div_cancel₀ _ hκpos.ne', htτ]
    _ ≤ ENNReal.ofReal κ * setDist d (sphere 0 (undA n)) (sphere 0 (undB n)) := by gcongr

/-! ### The two deterministic contradictions -/

/-- `t ≤ k t` with `0 < t < ∞` forces `k ≥ 1`. -/
theorem und_false_of_le_mul {t : ℝ≥0∞} (h0 : t ≠ 0) (htop : t ≠ ⊤) {k : ℝ} (hk : k < 1)
    (h : t ≤ ENNReal.ofReal k * t) : False := by
  have hk' : ENNReal.ofReal k < 1 := ENNReal.ofReal_lt_one.2 hk
  have hlt := ENNReal.mul_lt_mul_right h0 htop hk'
  rw [mul_one, mul_comm] at hlt
  exact absurd h (not_le.2 hlt)

/-- The constant bound of a subsegment comparison on the whole geodesic, with the constant raised to `c₀ ≥ c`. -/
theorem und_ofReal_mul_le {c c₀ T : ℝ} (hc : c ≤ c₀) (hc₀ : 0 ≤ c₀) (hT : 0 ≤ T) :
    ENNReal.ofReal (c * (T - 0)) ≤ ENNReal.ofReal c₀ * ENNReal.ofReal T := by
  rw [sub_zero, ← ENNReal.ofReal_mul hc₀]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc hT)

/-- The three-factor constant `c₀ κ²`. -/
theorem und_three_mul (c₀ κ : ℝ) (hc₀ : 0 ≤ c₀) (hκ : 0 ≤ κ) (t : ℝ≥0∞) :
    ENNReal.ofReal κ * (ENNReal.ofReal κ * (ENNReal.ofReal c₀ * t)) = ENNReal.ofReal (c₀ * κ * κ) * t := by
  rw [ENNReal.ofReal_mul (mul_nonneg hc₀ hκ), ENNReal.ofReal_mul hc₀]
  ring

/-- **The `D`-source contradiction** (D9 step 3, first claim, with (5.6)): on the deterministic content of the good event,
no comparison `CompIn d d'` with a constant `c ≤ c₀`, `c₀κ² < 1` and radius `ρ`, `1 + ρ ≤ a ≤ b ≤ 2 − ρ`, holds. -/
theorem und_not_compIn_dsource (d d' : LSCMetric)
    (hB : SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier d) (hL : d.IsLengthSpace)
    {R₁ R c c₀ κ ρ a b : ℝ} (hR₁ : 1 < R₁) (hR : R₁ ≤ R) (hc : c ≤ c₀) (hc₀ : 0 ≤ c₀) (hκ : 0 ≤ κ)
    (hck : c₀ * κ * κ < 1) (hab : a ≤ b) (ha : 1 + ρ ≤ a) (hb : b ≤ 2 - ρ)
    (hpos : setDist d (sphere 0 1) (sphere 0 2) ≠ 0) (hfin : setDist d (sphere 0 1) (sphere 0 2) < ⊤)
    (hesc : setDist d (sphere 0 1) (sphere 0 2) < setDist d (sphere 0 1) (sphere 0 R₁))
    (hlsc : setDist d (sphere 0 1) (sphere 0 2) ≤ ENNReal.ofReal κ * setDist d (sphere 0 a) (sphere 0 b))
    (hloc : setDist d (sphere 0 a) (sphere 0 b) ≤ ENNReal.ofReal κ * setDist d' (sphere 0 a) (sphere 0 b)) :
    ¬ Core.CompIn d d' (ball 0 (R + 2)) R c ρ := by
  intro hcomp
  obtain ⟨γ, T, hsg⟩ := SupercriticalLQGUniqueness.Uniqueness.Geodesics.SetGeodesics.exists_setGeodesic_of_finite d
    (sphere 0 1) (sphere 0 2) (isCompact_sphere 0 1) (isCompact_sphere 0 2)
    (NormedSpace.sphere_nonempty.2 zero_le_one) (NormedSpace.sphere_nonempty.2 zero_le_two) hB hL hfin
  have hgeod :=
    SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.SetGeodesic.isGeodesic _ _ _ _ _ hsg
  obtain ⟨⟨hcurve, hunit, hlen, -⟩, h0, hT, hTval⟩ := hsg
  have hcont : ContinuousOn γ (Icc 0 T) :=
    SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.continuousOn_of_barrier_of_length d hB hL hcurve
  have hT0 : 0 ≤ T := hgeod.1
  have hlenEq : d.len γ 0 T = setDist d (sphere 0 1) (sphere 0 2) := by
    rw [hlen, ← Main.ofReal_eq_of_unitSpeed_geodesic d hgeod hunit, hTval]
  have hin : ∀ t ∈ Icc 0 T, γ t ∈ ball (0 : ℂ) R₁ :=
    Main.mem_ball_of_len_lt_setDist d (sphere_subset_ball hR₁) hcont h0 (hlenEq ▸ hesc)
  have hgeo : Core.IsGeodIn d γ T R := Main.isGeodIn_mono ⟨hgeod, hunit, hcont, hin⟩ hR
  have hcmp := hcomp γ T hgeo 0 T le_rfl hT0 le_rfl
  have hx : ‖γ 0‖ = 1 := mem_sphere_zero_iff_norm.1 h0
  have hy : ‖γ T‖ = 2 := mem_sphere_zero_iff_norm.1 hT
  have hcross := und_setDist_sphere_le_internalSetDist d' (isBounded_ball (x := (0 : ℂ)) (r := R + 2))
    (x := γ 0) (y := γ T) (ρ := ρ) hab (by rw [hx]; exact ha) (by rw [hy]; exact hb)
  set t := setDist d (sphere (0 : ℂ) 1) (sphere 0 2) with ht
  have hd' : setDist d' (sphere 0 a) (sphere 0 b) ≤ ENNReal.ofReal c₀ * t := by
    rw [← hTval]
    exact (hcross.trans hcmp).trans (und_ofReal_mul_le hc hc₀ hT0)
  have hchain : t ≤ ENNReal.ofReal (c₀ * κ * κ) * t := by
    calc t ≤ ENNReal.ofReal κ * setDist d (sphere 0 a) (sphere 0 b) := hlsc
      _ ≤ ENNReal.ofReal κ * (ENNReal.ofReal κ * setDist d' (sphere 0 a) (sphere 0 b)) := by gcongr
      _ ≤ ENNReal.ofReal κ * (ENNReal.ofReal κ * (ENNReal.ofReal c₀ * t)) := by gcongr
      _ = ENNReal.ofReal (c₀ * κ * κ) * t := und_three_mul c₀ κ hc₀ hκ t
  exact und_false_of_le_mul hpos hfin.ne hck hchain

/-- **The `X̂`-source contradiction** (D9 step 3, the `q′` claim): for an LFPP metric `X = a₀⁻¹ D^φ` on the deterministic
content of the good event (circle comparison, `d(O,O′) ≤ M`, escape distance of `X` above `κM + 1`), no comparison
`CompIn X d` with a constant `c ≤ c₀`, `c₀κ² < 1` and radius `ρ`, `1 + ρ ≤ a ≤ b ≤ 2 − ρ`, holds. -/
theorem und_not_compIn_xsource (hG : Core.LFPPGeodesicStmt) (d : LSCMetric) (ξ : ℝ) (a₀ : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) {R c c₀ κ ρ a b M : ℝ} (hR : 1 < R) (hc : c ≤ c₀) (hc₀ : 0 ≤ c₀) (hκ : 0 ≤ κ)
    (hM0 : 0 ≤ M) (hck : c₀ * κ * κ < 1) (hab : a ≤ b) (ha : 1 + ρ ≤ a) (hb : b ≤ 2 - ρ)
    (hpos : setDist d (sphere 0 1) (sphere 0 2) ≠ 0) (hfin : setDist d (sphere 0 1) (sphere 0 2) < ⊤)
    (hM : setDist d (sphere 0 1) (sphere 0 2) ≤ ENNReal.ofReal M)
    (hloc : setDist (SupercriticalLQGUniqueness.B2.Median.lfppMetric ξ a₀ φ) (sphere 0 1) (sphere 0 2) ≤
      ENNReal.ofReal κ * setDist d (sphere 0 1) (sphere 0 2))
    (hconf : ENNReal.ofReal (κ * M + 1) <
      setDist (SupercriticalLQGUniqueness.B2.Median.lfppMetric ξ a₀ φ) (sphere 0 1) (sphere 0 R))
    (hlsc : setDist d (sphere 0 1) (sphere 0 2) ≤ ENNReal.ofReal κ * setDist d (sphere 0 a) (sphere 0 b)) :
    ¬ Core.CompIn (SupercriticalLQGUniqueness.B2.Median.lfppMetric ξ a₀ φ) d (ball 0 (R + 2)) R c ρ := by
  intro hcomp
  set X := SupercriticalLQGUniqueness.B2.Median.lfppMetric ξ a₀ φ with hXdef
  set t := setDist d (sphere (0 : ℂ) 1) (sphere 0 2) with ht
  obtain ⟨x, hxO, y, hyO, hxy⟩ := SupercriticalLQGUniqueness.Uniqueness.Geodesics.SetGeodesics.setDist_attained X
    (sphere 0 1) (sphere 0 2) (isCompact_sphere 0 1) (isCompact_sphere 0 2)
    (NormedSpace.sphere_nonempty.2 zero_le_one) (NormedSpace.sphere_nonempty.2 zero_le_two)
  have hx : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 hxO
  have hy : ‖y‖ = 2 := mem_sphere_zero_iff_norm.1 hyO
  have hM' : X (x, y) ≤ ENNReal.ofReal (κ * M) := by
    rw [← hxy, ENNReal.ofReal_mul hκ]
    exact hloc.trans (by gcongr)
  have hlt : X (x, y) < setDist X {x} (sphere 0 R) := by
    calc X (x, y) ≤ ENNReal.ofReal (κ * M) := hM'
      _ < ENNReal.ofReal (κ * M + 1) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
      _ < setDist X (sphere 0 1) (sphere 0 R) := hconf
      _ ≤ setDist X {x} (sphere 0 R) := Main.setDist_le_setDist_singleton X hxO
  obtain ⟨γ, T, h0, hT, hgeo⟩ := hG ξ a₀ φ x y R (by rw [hx]; exact hR) hlt
  have hT0 : 0 ≤ T := hgeo.1.1
  have hTval : ENNReal.ofReal T = setDist X (sphere 0 1) (sphere 0 2) := by
    rw [Main.ofReal_eq_of_unitSpeed_geodesic X hgeo.1 hgeo.2.1, h0, hT, hxy]
  have hcmp := hcomp γ T hgeo 0 T le_rfl hT0 le_rfl
  have hcross := und_setDist_sphere_le_internalSetDist d (isBounded_ball (x := (0 : ℂ)) (r := R + 2))
    (x := γ 0) (y := γ T) (ρ := ρ) hab (by rw [h0, hx]; exact ha) (by rw [hT, hy]; exact hb)
  have hd : setDist d (sphere 0 a) (sphere 0 b) ≤ ENNReal.ofReal c₀ * setDist X (sphere 0 1) (sphere 0 2) := by
    rw [← hTval]
    exact (hcross.trans hcmp).trans (und_ofReal_mul_le hc hc₀ hT0)
  have hchain : t ≤ ENNReal.ofReal (c₀ * κ * κ) * t := by
    calc t ≤ ENNReal.ofReal κ * setDist d (sphere 0 a) (sphere 0 b) := hlsc
      _ ≤ ENNReal.ofReal κ * (ENNReal.ofReal c₀ * setDist X (sphere 0 1) (sphere 0 2)) := by gcongr
      _ ≤ ENNReal.ofReal κ * (ENNReal.ofReal c₀ * (ENNReal.ofReal κ * t)) := by gcongr
      _ = ENNReal.ofReal κ * (ENNReal.ofReal κ * (ENNReal.ofReal c₀ * t)) := by ring
      _ = ENNReal.ofReal (c₀ * κ * κ) * t := und_three_mul c₀ κ hc₀ hκ t
  exact und_false_of_le_mul hpos hfin.ne hck hchain

end SupercriticalLFPPAS.Identification
