import HigherDimLQGContinuity.UnifNondeg.SmallShell
import HigherDimLQGMetric.DGZ.NondegDistanceCompare

/-!
# Uniform nondegeneracy (A.3) and comparability of quantiles (A.4) from the uniform inputs (packet U5)

Blueprint Part D, `d:prop-u64` (NA3 §2.8, §2.9, R11; [8]-bp `r2:prop:64`).

**The inputs.** `UNondegInputs d κ`: for every `b, μ > 0` there are a quantile `q ∈ (0, 1)` and `β > 0` at which
the three uniform inputs hold — Hölder tightness (`UHolderTightAt`, Part D `d:lem-u61`(b)), distance to infinity
(`UDistInfAt`, `d:lem-u65`(c)) and positive crossings (`UCrossPosAt`, `d:lem-u65`(b)). Packet U4 proves them at every
`q` close to `1` (`holderTightAQ_unif`, `distInf_aq_unif`, `nondeg_cross_pos_unif`); `UnifNondeg/Exports.lean`
assembles them.

**Results.**
* `u5_smallShell_nondeg_center`: small shells at every centre (translation of the realization).
* `u5_nondeg_at`: every cubical shell `B_{r₁}(c) \ B_{r₂}(c)`, every depth, normalized by `a^ξ_n(q)` (finite cover of
  the middle sphere by small shells and a union bound; port of `DGZ.nondegShape`).
* **`uNondeg_of_inputs : UNondegInputs d κ → UNondegShape d κ`** (interface I9; `a^ξ_n(½) ≤ a^ξ_n(q)` for `q ≥ ½`).
* **`uQuantComp_of_inputs : UNondegInputs d κ → UQuantCompShape d κ`** (interface I7): `a_n(p) ≥ δ a_n(q)` from
  (A.3) (every path from `0` to `e₁` crosses `B_{1/2}(0) \ B_{1/4}(0)`) and `a_n(p) ≤ M a_n(q)` from the Hölder bound
  at `(0, e₁)` (Part D `d:prop-u64`(b)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-- **The uniform inputs of the nondegeneracy argument** (Part D `d:lem-u61`(b), `d:lem-u65`(b), (c)): for every
`b, μ > 0`, one quantile `q ∈ [½, 1)` and one exponent `β > 0` at which the Hölder bound, the distance to infinity
and the positive crossings hold uniformly in `ξ ∈ S(b, μ)`. -/
def UNondegInputs (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∀ b μ : ℝ, 0 < b → 0 < μ → ∃ q : ℝ≥0∞, 2⁻¹ ≤ q ∧ q < 1 ∧ ∃ β : ℝ, 0 < β ∧
    UHolderTightAt d κ b μ q β ∧ UDistInfAt d κ b μ q ∧ UCrossPosAt d κ b μ q

section General

variable {κ : Rd d → ℝ} {b μ β : ℝ} {q : ℝ≥0∞}

/-- **Small shells at every centre** (port of `DGZ.nd_smallShell_median_center` at the quantile `q`): the
translated realization `H(c + ·)` is a dyadic realization with the same quantiles. -/
theorem u5_smallShell_nondeg_center (hκ : IsLFPPKernel κ) (hq0 : 0 < q) (hq1 : q < 1)
    (hT : UHolderTightAt d κ b μ q β) (hβ : 0 < β) (hI : UDistInfAt d κ b μ q)
    (hW : UCrossPosAt d κ b μ q) {r : ℝ} (hr : 0 < r) (hrd : r * (10 * Real.sqrt d) ≤ 1)
    (hd : 0 < d) {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (c : Rd d) (ξ : ℝ), UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        IsDyadicRealization κ P W H → ∀ n : ℕ,
          P {ω | acrossDist ξ (fun z => H n z ω) c (2 * r) r ≤ δ * aQ P H ξ n q} ≤
            ENNReal.ofReal θ := by
  obtain ⟨δ, hδ, hN⟩ := u5_smallShell_nondeg hκ hq0 hq1 hT hβ hI hW hr hrd hd hθ
  refine ⟨δ, hδ, fun c ξ hξ Ω _ P W H hH n => ?_⟩
  have hH' := isDyadicRealization_translate_tight hκ hH c
  have hq : aQ P (fun k z ω => H k (c + z) ω) ξ n q = aQ P H ξ n q :=
    aQ_eq_of_isDyadicRealization hH' hH ξ n q
  have hc : ∀ ω, acrossDist ξ (fun z => H n z ω) c (2 * r) r =
      acrossDist ξ (fun z => H n (c + z) ω) 0 (2 * r) r := by
    intro ω
    have hh := acrossDist_smul_add c ξ (fun z => H n z ω) one_pos 0 (2 * r) r
    simpa only [smul_zero, add_zero, one_mul, one_smul] using hh
  simp_rw [hc, ← hq]
  exact hN ξ hξ Ω P _ _ hH' n

/-- **(A.3) for every cubical shell, every centre and every depth, at the quantile `q`** (Part D `d:prop-u64`(a);
port of `DGZ.nondegShape`): `ρ := min((r₁ - r₂)/8, 1/(10√d + 4))`, a finite cover of `∂B_{(r₁+r₂)/2}(c)` by boxes
`B_ρ(g)`, every crossing of `B_{r₁}(c) \ B_{r₂}(c)` crosses some `B_{2ρ}(g) \ B_ρ(g)`
(`DGZ.nd_across_general_ge_inf`), and a union bound. -/
theorem u5_nondeg_at (hκ : IsLFPPKernel κ) (hq0 : 0 < q) (hq1 : q < 1)
    (hT : UHolderTightAt d κ b μ q β) (hβ : 0 < β) (hI : UDistInfAt d κ b μ q)
    (hW : UCrossPosAt d κ b μ q) (hd : 0 < d) (c : Rd d) (r₁ r₂ : ℝ) (hr₂ : 0 < r₂) (hr : r₂ < r₁)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        IsDyadicRealization κ P W H → ∀ n : ℕ,
          P {ω | acrossDist ξ (fun z => H n z ω) c r₁ r₂ ≤ δ * aQ P H ξ n q} ≤ ENNReal.ofReal θ := by
  let ρ : ℝ := min ((r₁ - r₂) / 8) (1 / (10 * Real.sqrt d + 4))
  have hρ : 0 < ρ := lt_min (by linarith) (by positivity)
  have hρgap : 2 * ρ ≤ (r₁ - r₂) / 2 := by
    have hh : ρ ≤ (r₁ - r₂) / 8 := min_le_left _ _
    linarith
  have hrd : ρ * (10 * Real.sqrt d) ≤ 1 := by
    have hh : ρ ≤ 1 / (10 * Real.sqrt d + 4) := min_le_right _ _
    have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    have hden : 0 < 10 * Real.sqrt d + 4 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ 10 * Real.sqrt d)
    have hratio : (1 / (10 * Real.sqrt d + 4)) * (10 * Real.sqrt d) ≤ 1 := by
      calc (1 / (10 * Real.sqrt d + 4)) * (10 * Real.sqrt d) ≤
            (1 / (10 * Real.sqrt d + 4)) * (10 * Real.sqrt d + 4) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 1 := by field_simp
    linarith
  obtain ⟨Z, hZs, hZcov⟩ := tn_exists_obox_cover (tn_isCompact_lsph c ((r₁ + r₂) / 2)) hρ
  have hZne : Z.Nonempty := by
    obtain ⟨p, hp⟩ := lsph_nonempty hd c (by linarith : 0 ≤ (r₁ + r₂) / 2)
    obtain ⟨g, hg, -⟩ := mem_iUnion₂.1 (hZcov hp)
    exact ⟨g, hg⟩
  have hden : 0 < (Z.card : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ, hsmall⟩ := u5_smallShell_nondeg_center hκ hq0 hq1 hT hβ hI hW hρ hrd hd
    (θ := θ / (Z.card + 1)) (div_pos hθ hden)
  refine ⟨δ, hδ, fun ξ hξ Ω _ P W H hH n => ?_⟩
  let E : Rd d → Set Ω := fun g =>
    {ω | acrossDist ξ (fun z => H n z ω) g (2 * ρ) ρ ≤ δ * aQ P H ξ n q}
  have hsub : {ω | acrossDist ξ (fun z => H n z ω) c r₁ r₂ ≤ δ * aQ P H ξ n q} ⊆
      ⋃ g ∈ Z, E g := by
    intro ω hω
    have hinf := nd_across_general_ge_inf (ξ := ξ) hd ((hH.band n).continuous ω)
      hr₂ hr hρ hρgap hZne hZs hZcov
    have hle : Z.inf' hZne (fun g => acrossDist ξ (fun z => H n z ω) g (2 * ρ) ρ) ≤
        δ * aQ P H ξ n q := hinf.trans hω
    obtain ⟨g, hg, hgeq⟩ := Finset.exists_mem_eq_inf' hZne
      (fun g => acrossDist ξ (fun z => H n z ω) g (2 * ρ) ρ)
    rw [hgeq] at hle
    exact mem_iUnion₂.2 ⟨g, hg, hle⟩
  have hreal : (Z.card : ℝ) * (θ / (Z.card + 1)) ≤ θ := by
    rw [mul_div_assoc', div_le_iff₀ hden]
    nlinarith
  calc P {ω | acrossDist ξ (fun z => H n z ω) c r₁ r₂ ≤ δ * aQ P H ξ n q}
      ≤ P (⋃ g ∈ Z, E g) := measure_mono hsub
    _ ≤ ∑ g ∈ Z, P (E g) := measure_biUnion_finset_le Z E
    _ ≤ ∑ _g ∈ Z, ENNReal.ofReal (θ / (Z.card + 1)) :=
        Finset.sum_le_sum fun g _ => hsmall g ξ hξ Ω P W H hH n
    _ = ENNReal.ofReal ((Z.card : ℝ) * (θ / (Z.card + 1))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal θ := ENNReal.ofReal_le_ofReal hreal

end General

/-! ### The interfaces I9 and I7 -/

section Interfaces

variable {κ : Rd d → ℝ}

/-- `a^ξ_n(½) ≤ a^ξ_n(q)` for `½ ≤ q < 1`. -/
theorem u5_aQ_half_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} (hH : IsDyadicRealization κ P W H) (ξ : ℝ) (n : ℕ) {q : ℝ≥0∞}
    (hq : 2⁻¹ ≤ q) (hq1 : q < 1) : aQ P H ξ n 2⁻¹ ≤ aQ P H ξ n q :=
  tight_aQ_mono hH ξ n (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) hq hq1

/-- **U-nondegeneracy from the uniform inputs** (Part D `d:prop-u64`(a); interface I9 `UNondegShape`): (A.3) at the
quantile `q ≥ ½` of the inputs, and `λ^ξ_n = a^ξ_n(½) ≤ a^ξ_n(q)`. -/
theorem uNondeg_of_inputs (hd : 2 ≤ d) (hκ : IsLFPPKernel κ) (hin : UNondegInputs d κ) :
    UNondegShape d κ := by
  intro b μ hb hμ c r₁ r₂ hr₂ hr θ hθ
  obtain ⟨q, hqh, hq1, β, hβ, hT, hI, hW⟩ := hin b μ hb hμ
  have hd0 : 0 < d := by omega
  have hq0 : 0 < q := (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top).trans_le hqh
  obtain ⟨δ, hδ, hb'⟩ := u5_nondeg_at hκ hq0 hq1 hT hβ hI hW hd0 c r₁ r₂ hr₂ hr hθ
  refine ⟨δ, hδ, fun ξ hξ Ω _ P W H hH n => le_trans (measure_mono fun ω hω => ?_)
    (hb' ξ hξ Ω P W H hH n)⟩
  simp only [mem_ofPred_eq] at hω ⊢
  exact hω.trans (mul_le_mul_of_nonneg_left (u5_aQ_half_le hH ξ n hqh hq1) hδ.le)

/-- `X_n ≥ D_n(across B_{1/2}(0) \ B_{1/4}(0))` (`DGZ.nd_across_le_lfppDistance` at `r = ¼`). -/
theorem u5_across_quarter_le_lfppDistance (hd : 0 < d) {ξ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ) :
    acrossDist ξ φ 0 (2 * (1 / 4)) (1 / 4) ≤ lfppDistance d ξ φ :=
  nd_across_le_lfppDistance hd hφ (by norm_num) (by norm_num)

/-- **Lower comparability** (Part D `d:prop-u64`(b), lower half): if (A.3) holds at the quantile `q` for the shell
`B_{1/2}(0) \ B_{1/4}(0)` with `θ < p`, then `a^ξ_n(p) ≥ δ a^ξ_n(q)`. -/
theorem u5_aQ_ge_of_nondeg (hd : 0 < d) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ} (hH : IsDyadicRealization κ P W H) (ξ : ℝ) (n : ℕ)
    {p q : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) {δ : ℝ}
    (hbad : P {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * (1 / 4)) (1 / 4) ≤ δ * aQ P H ξ n q} < p) :
    δ * aQ P H ξ n q ≤ aQ P H ξ n p := by
  have : IsProbabilityMeasure P := hH.whiteNoise.isProbabilityMeasure
  by_contra hlt
  push Not at hlt
  have hXm := (hH.band n).measurable_lfppDistance ξ
  have hle : p ≤ P {ω | lfppDistance d ξ (fun z => H n z ω) ≤ δ * aQ P H ξ n q} := by
    have hh := (LQGMetric.le_measure_Iic_iff_lowerQuantile_le
      (μ := P.map fun ω => lfppDistance d ξ (fun z => H n z ω)) hp0 hp1).2 hlt.le
    rwa [Measure.map_apply hXm measurableSet_Iic] at hh
  have hsub : {ω | lfppDistance d ξ (fun z => H n z ω) ≤ δ * aQ P H ξ n q} ⊆
      {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * (1 / 4)) (1 / 4) ≤ δ * aQ P H ξ n q} :=
    fun ω hω => (u5_across_quarter_le_lfppDistance hd ((hH.band n).continuous ω)).trans hω
  exact absurd (hle.trans (measure_mono hsub)) (not_le_of_gt hbad)

/-- **Upper comparability** (Part D `d:prop-u64`(b), upper half): the Hölder bound at the quantile `q` for
`U = B₂(0)`, `V = 𝔹_{3/2}(0)` at the pair `(0, e₁)` gives `a^ξ_n(p) ≤ max(M, 0) a^ξ_n(q)` when
`P[M a_n(q) < X_n] ≤ 1 - p`. -/
theorem u5_aQ_le_of_holder {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ} (hH : IsDyadicRealization κ P W H) (ξ : ℝ) (n : ℕ)
    {p q : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) {M : ℝ}
    (hgood : P {ω | M * aQ P H ξ n q < lfppDistance d ξ (fun z => H n z ω)} ≤ 1 - p) :
    aQ P H ξ n p ≤ M * aQ P H ξ n q := by
  have : IsProbabilityMeasure P := hH.whiteNoise.isProbabilityMeasure
  have hXm := (hH.band n).measurable_lfppDistance ξ
  unfold aQ
  rw [← LQGMetric.le_measure_Iic_iff_lowerQuantile_le hp0 hp1, Measure.map_apply hXm measurableSet_Iic]
  have hcov : (univ : Set Ω) ⊆
      (fun ω => lfppDistance d ξ (fun z => H n z ω)) ⁻¹' Iic (M * aQ P H ξ n q) ∪
        {ω | M * aQ P H ξ n q < lfppDistance d ξ (fun z => H n z ω)} := by
    intro ω _
    by_cases hω : lfppDistance d ξ (fun z => H n z ω) ≤ M * aQ P H ξ n q
    · exact Or.inl hω
    · exact Or.inr (lt_of_not_ge hω)
  have h1 : (1 : ℝ≥0∞) ≤
      P ((fun ω => lfppDistance d ξ (fun z => H n z ω)) ⁻¹' Iic (M * aQ P H ξ n q)) + (1 - p) := by
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ ≤ _ := measure_mono hcov
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := add_le_add le_rfl hgood
  calc p = 1 - (1 - p) := (ENNReal.sub_sub_cancel ENNReal.one_ne_top hp1.le).symm
    _ ≤ _ := tsub_le_iff_right.2 h1

/-- The Hölder input at the pair `(0, e₁)`: `X_n = D_n(0, e₁; B₂(0)) ≤ M a^ξ_n(q)` with probability `≥ 1 - θ`. -/
theorem u5_holder_unit {b μ β : ℝ} {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (hT : UHolderTightAt d κ b μ q β) (hd : 0 < d) {θ : ℝ} (hθ : 0 < θ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        IsDyadicRealization κ P W H → ∀ n : ℕ,
          P {ω | M * aQ P H ξ n q < lfppDistance d ξ (fun z => H n z ω)} ≤ ENNReal.ofReal θ := by
  have hV : IsConnected (ball (0 : Rd d) (3 / 2)) :=
    ⟨nonempty_ball.2 (by norm_num), (convex_ball _ _).isPreconnected⟩
  have hVU : closure (ball (0 : Rd d) (3 / 2)) ⊆ HigherDimLFPP.cube d := by
    intro z hz i
    have hz' : ‖z‖ ≤ 3 / 2 := by
      have := closure_ball_subset_closedBall hz
      simpa only [mem_closedBall, dist_zero_right] using this
    have hzi := HigherDimLFPP.DGZ.abs_apply_le_norm z i
    linarith
  obtain ⟨M, hM⟩ := hT (HigherDimLFPP.cube d) (ball (0 : Rd d) (3 / 2)) (HigherDimLFPP.isOpen_cube d)
    isOpen_ball hV isBounded_ball hVU θ hθ
  refine ⟨max M 0, le_max_right _ _, fun ξ hξ Ω _ P W H hH n => le_trans (measure_mono ?_)
    (hM ξ hξ Ω P W H hH n)⟩
  intro ω hω
  simp only [mem_ofPred_eq] at hω
  have h0 : (0 : Rd d) ∈ ball (0 : Rd d) (3 / 2) := mem_ball_self (by norm_num)
  have he : e₁ d ∈ ball (0 : Rd d) (3 / 2) := by
    rw [mem_ball, dist_zero_right, HigherDimLFPP.norm_e₁ hd]
    norm_num
  refine ⟨0, h0, e₁ d, he, ?_⟩
  have hnorm : ‖(0 : Rd d) - e₁ d‖ ^ β = 1 := by
    rw [zero_sub, norm_neg, HigherDimLFPP.norm_e₁ hd, Real.one_rpow]
  rw [hnorm, mul_one, ← lfppDistance_eq_lfppDistOn]
  have ha : 0 ≤ aQ P H ξ n q := (tight_aQ_pos hd hH ξ n hq0 hq1).le
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left _ _) ha) hω

/-- **Comparability of quantiles from the uniform inputs** (Part D `d:prop-u64`(b); interface I7
`UQuantCompShape`): with `q` the quantile of the inputs, `a^ξ_n(p) ≤ M a^ξ_n(q)` (Hölder bound at `(0, e₁)`, failure
probability `1 - p`) and `δ a^ξ_n(q) ≤ a^ξ_n(p')` ((A.3) for `B_{1/2}(0) \ B_{1/4}(0)` at level `p'/2`), so
`a^ξ_n(p) ≤ (M/δ + 1) a^ξ_n(p')`. -/
theorem uQuantComp_of_inputs (hd : 2 ≤ d) (hκ : IsLFPPKernel κ) (hin : UNondegInputs d κ) :
    UQuantCompShape d κ := by
  intro b μ hb hμ p p' hp0 hp1 hp'0 hp'1
  obtain ⟨q, hqh, hq1, β, hβ, hT, hI, hW⟩ := hin b μ hb hμ
  have hd0 : 0 < d := by omega
  have hq0 : 0 < q := (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top).trans_le hqh
  -- the upper half
  have hp1' : (1 : ℝ≥0∞) - p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  obtain ⟨M, hM0, hMb⟩ := u5_holder_unit hq0 hq1 hT hd0 (θ := ((1 : ℝ≥0∞) - p).toReal)
    (ENNReal.toReal_pos (tsub_pos_of_lt hp1).ne' hp1')
  -- the lower half
  have hp'ne : p' ≠ ⊤ := ne_top_of_lt hp'1
  have hp'r : 0 < p'.toReal := ENNReal.toReal_pos hp'0.ne' hp'ne
  obtain ⟨δ, hδ, hbad⟩ := u5_nondeg_at hκ hq0 hq1 hT hβ hI hW hd0 0 (2 * (1 / 4)) (1 / 4)
    (by norm_num) (by norm_num) (θ := p'.toReal / 2) (by positivity)
  have hlt : ENNReal.ofReal (p'.toReal / 2) < p' := by
    calc ENNReal.ofReal (p'.toReal / 2) < ENNReal.ofReal p'.toReal :=
          (ENNReal.ofReal_lt_ofReal_iff hp'r).2 (by linarith)
      _ = p' := ENNReal.ofReal_toReal hp'ne
  refine ⟨M / δ + 1, by positivity, fun ξ hξ Ω _ P W H hH n => ?_⟩
  have h1 : aQ P H ξ n p ≤ M * aQ P H ξ n q := by
    refine u5_aQ_le_of_holder hH ξ n hp0 hp1 ?_
    rw [← ENNReal.ofReal_toReal hp1']
    exact hMb ξ hξ Ω P W H hH n
  have h2 : δ * aQ P H ξ n q ≤ aQ P H ξ n p' :=
    u5_aQ_ge_of_nondeg hd0 hH ξ n hp'0 hp'1 ((hbad ξ hξ Ω P W H hH n).trans_lt hlt)
  have ha' : 0 ≤ aQ P H ξ n p' := (tight_aQ_pos hd0 hH ξ n hp'0 hp'1).le
  calc aQ P H ξ n p ≤ M * aQ P H ξ n q := h1
    _ = M / δ * (δ * aQ P H ξ n q) := by field_simp
    _ ≤ M / δ * aQ P H ξ n p' := mul_le_mul_of_nonneg_left h2 (div_nonneg hM0 hδ.le)
    _ ≤ (M / δ + 1) * aQ P H ξ n p' :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) ha'

end Interfaces

end HigherDimLQGContinuity
