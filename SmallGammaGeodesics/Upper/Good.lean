import SmallGammaGeodesics.Upper.Basic
import SmallGammaGeodesics.Variance.Residual

/-!
# §5: the good event and the a priori bounds (packet P-U0)

Blueprint `blueprint/sections/s5-upper.tex`, §`ssec:good`; statements of
`planning/packets/BP2-planned-statements.md` (§5 block), rulings G16, G23 (`a = 99/100`) and G27;
BP2 details D1, D11.

The good event is `𝒢_γ = {Δ₈ ≤ ξ^{99/100}}` (`goodEv`), with `Δ₈ = S.euclidErr γ 8 = E_{b_γ,8}(S.D γ)`.

* `approxGeod_of_good` (Lemma `lem:good-geometry`): for small `γ`, `ξ^{99/100} ≤ 1/100`, and on `𝒢_γ` every
  constant-speed `S.D γ ω`-geodesic `η` from `0` to `1` is a `Δ₈`-Euclidean geodesic for `e^{-b_γ} S.D γ ω`
  (`ApproxGeod`), with `Δ₈ ≤ ξ^{99/100}` and `M(η) ≤ √3 ξ^{99/200}`.
* `good_compl_le`, `lintegral_maxDev_compl_good_le` (Lemma `lem:good-compl`): `P[𝒢ᶜ] ≤ C ξ^{20}` and
  `E[M(η) 1_{𝒢ᶜ}] ≤ C ξ^{10}`.
* `bandEv_of_lt_maxDev` (Corollary `cor:band-inclusion`, source (5.12)): for small `γ`, on `𝒢_γ`,
  `M(η) < 2ξ^{99/200}`, and `M(η) > R ≥ δ` forces the band event `ℬ_γ(R)`.

Proof of the second bound of `lem:good-compl` (written out; the blueprint uses Cauchy–Schwarz). A.s.
`M(η) ≤ T` with `T = S.locT γ B̄₁(0)` finite (`ae_localization_zero_one`), and for every real `t` and
`a > 0`, `t ≤ a t² + a⁻¹` (since `a t² + a⁻¹ − t = a⁻¹ (a t − 1/2)² + (3/4) a⁻¹`). With `a = ξ^{10}`:
`E[M 1_{𝒢ᶜ}] ≤ ξ^{10} E[T²] + ξ^{−10} P[𝒢ᶜ] ≤ ξ^{10} C_T + ξ^{−10} C_c ξ^{20}`.

Reusable deterministic helpers: `euclidErr_eq_euclidErrF`, `abs_sub_le_toReal_euclidErrF`,
`approxGeod_of_euclidErrF_le` (the good-event geometry for an arbitrary continuous metric, e.g.
`D^γ_{nrm h}` on a coupling space), `exists_xiGamma_pos_le`, `rpow_ninetyNine_hundredths_le`,
`sqrt_rpow_ninetyNine_hundredths`, `le_ofReal_mul_rpow_two_add_inv`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open GaussianLQG LQGMetric LQGMetric.Blueprint

/-! ## The Euclidean error of a single metric -/

/-- `S.euclidErr γ R ω = E_{b_γ,R}(S.D γ ω)` (definitional). -/
theorem euclidErr_eq_euclidErrF (S : Setup) (γ R : ℝ) (ω : Coord) :
    S.euclidErr γ R ω = euclidErrF (S.b γ) R (S.D γ ω) := rfl

/-- Pointwise form of `E_{b,R}(d)`: if `E_{b,R}(d) < ∞`, then `|e^{-b} d(z,w) − |z − w|| ≤ E_{b,R}(d)` for
`|z|, |w| ≤ R`. -/
theorem abs_sub_le_toReal_euclidErrF {b R : ℝ} {d : ContMetric} (hfin : euclidErrF b R d ≠ ⊤)
    {z w : ℂ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    |Real.exp (-b) * d.1 (z, w) - ‖z - w‖| ≤ (euclidErrF b R d).toReal := by
  refine (ENNReal.ofReal_le_iff_le_toReal hfin).1 ?_
  exact le_iSup₂_of_le (f := fun z (_ : z ∈ Metric.closedBall (0 : ℂ) R) =>
      ⨆ w ∈ Metric.closedBall (0 : ℂ) R, ENNReal.ofReal |Real.exp (-b) * d.1 (z, w) - ‖z - w‖|)
    z (mem_closedBall_zero_iff.2 hz)
    (le_iSup₂_of_le (f := fun w (_ : w ∈ Metric.closedBall (0 : ℂ) R) =>
        ENNReal.ofReal |Real.exp (-b) * d.1 (z, w) - ‖z - w‖|)
      w (mem_closedBall_zero_iff.2 hw) le_rfl)

/-- **Lemma `lem:good-geometry` (i)–(iii), deterministic form.** If `E_{b,8}(D) ≤ x` with `0 ≤ x ≤ 1/100`
and `η` is a constant-speed `D`-geodesic from `0` to `1`, then `η` is a `Δ`-Euclidean geodesic for
`e^{-b} D` with `Δ = E_{b,8}(D) ≤ x` (only `B̄₃ ⊆ B̄₈` is used), and `M(η) ≤ √(3Δ) ≤ √3 √x`. -/
theorem approxGeod_of_euclidErrF_le {b x : ℝ} {D : ContMetric} {η : C(unitInterval, ℂ)}
    (hE : euclidErrF b 8 D ≤ ENNReal.ofReal x) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 100)
    (hη : IsGeod01 D 0 1 η) :
    ApproxGeod (fun p => Real.exp (-b) * D.1 p) η (euclidErrF b 8 D).toReal ∧
      (euclidErrF b 8 D).toReal ≤ x ∧ maxDev η ≤ Real.sqrt 3 * Real.sqrt x := by
  have hfin : euclidErrF b 8 D ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE
  have hle : (euclidErrF b 8 D).toReal ≤ x := ENNReal.toReal_le_of_le_ofReal hx0 hE
  have hA : ApproxGeod (fun p => Real.exp (-b) * D.1 p) η (euclidErrF b 8 D).toReal :=
    { nonneg := ENNReal.toReal_nonneg
      le := hle.trans hx
      err := fun z w hz hw =>
        abs_sub_le_toReal_euclidErrF hfin (hz.trans (by norm_num)) (hw.trans (by norm_num))
      zero := hη.1
      one := hη.2.1
      geod := fun s t => by
        show Real.exp (-b) * D.1 (η s, η t) = |(t : ℝ) - s| * (Real.exp (-b) * D.1 (0, 1))
        rw [hη.2.2 s t]
        ring }
  refine ⟨hA, hle, ?_⟩
  calc maxDev η ≤ Real.sqrt (3 * (euclidErrF b 8 D).toReal) := hA.maxDev_le_sqrt
    _ ≤ Real.sqrt (3 * x) := Real.sqrt_le_sqrt (by linarith)
    _ = Real.sqrt 3 * Real.sqrt x := Real.sqrt_mul (by norm_num) x

/-! ## Small-`γ` facts about `ξ_γ` -/

/-- From `dimension_input` (source (1.12)): there is `γ₀ ∈ (0,1)` with `0 < ξ_γ ≤ γ` for `γ ∈ (0, γ₀]`. -/
theorem exists_xiGamma_pos_le :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ < 1 ∧ ∀ γ ∈ Ioc (0 : ℝ) γ₀, 0 < xiGamma γ ∧ xiGamma γ ≤ γ := by
  obtain ⟨γd, C, hγd, hdim⟩ := dimension_input
  refine ⟨min γd (1 / 2), lt_min hγd (by norm_num), (min_le_right _ _).trans_lt (by norm_num),
    fun γ hγ => ?_⟩
  obtain ⟨-, hl, hu⟩ := hdim γ ⟨hγ.1, hγ.2.trans (min_le_left _ _)⟩
  exact ⟨lt_of_lt_of_le (by linarith [hγ.1]) hl, hu⟩

/-- For `0 < ξ ≤ 10⁻⁴`: `ξ^{99/100} ≤ ξ^{1/2} ≤ 1/100`. -/
theorem rpow_ninetyNine_hundredths_le {ξ : ℝ} (h0 : 0 < ξ) (h1 : ξ ≤ 1 / 10000) :
    ξ ^ (99 / 100 : ℝ) ≤ 1 / 100 := by
  calc ξ ^ (99 / 100 : ℝ) ≤ ξ ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge h0 (by linarith) (by norm_num)
    _ = Real.sqrt ξ := (Real.sqrt_eq_rpow ξ).symm
    _ ≤ Real.sqrt (1 / 10000) := Real.sqrt_le_sqrt h1
    _ = 1 / 100 := by
        rw [show (1 / 10000 : ℝ) = (1 / 100) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `√(ξ^{99/100}) = ξ^{99/200}`. -/
theorem sqrt_rpow_ninetyNine_hundredths {ξ : ℝ} (h0 : 0 ≤ ξ) :
    Real.sqrt (ξ ^ (99 / 100 : ℝ)) = ξ ^ (99 / 200 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul h0]
  norm_num

/-! ## Lemma `lem:good-geometry` -/

/-- **Lemma `lem:good-geometry`** (source (5.1), (4.1)): there is `γ_g ∈ (0,1)` such that for
`γ ∈ (0, γ_g]`: `ξ^{99/100} ≤ 1/100`, and for every `ω ∈ 𝒢_γ` and every constant-speed
`S.D γ ω`-geodesic `η` from `0` to `1`, `η` is a `Δ₈`-Euclidean geodesic for `e^{-b_γ} S.D γ ω`,
`Δ₈ ≤ ξ^{99/100}`, and `M(η) ≤ √3 ξ^{99/200}`. -/
theorem approxGeod_of_good (G : GSetup) : ∃ γg, 0 < γg ∧ γg < 1 ∧ ∀ γ ∈ Ioc 0 γg,
    xiGamma γ ^ (99/100 : ℝ) ≤ 1/100 ∧ ∀ ω, goodEv G γ ω → ∀ η, IsGeod01 (G.S.D γ ω) 0 1 η →
      ApproxGeod (fun p => Real.exp (-G.S.b γ) * (G.S.D γ ω).1 p) η (G.S.euclidErr γ 8 ω).toReal ∧
      (G.S.euclidErr γ 8 ω).toReal ≤ xiGamma γ ^ (99/100 : ℝ) ∧
      maxDev η ≤ Real.sqrt 3 * xiGamma γ ^ (99/200 : ℝ) := by
  obtain ⟨γ₀, hγ₀, hγ₀1, hξ⟩ := exists_xiGamma_pos_le
  refine ⟨min γ₀ (1 / 10000), lt_min hγ₀ (by norm_num), (min_le_left _ _).trans_lt hγ₀1,
    fun γ hγ => ?_⟩
  obtain ⟨hξ0, hξγ⟩ := hξ γ ⟨hγ.1, hγ.2.trans (min_le_left _ _)⟩
  have hξs : xiGamma γ ≤ 1 / 10000 := hξγ.trans (hγ.2.trans (min_le_right _ _))
  have hsmall := rpow_ninetyNine_hundredths_le hξ0 hξs
  refine ⟨hsmall, fun ω hω η hη => ?_⟩
  obtain ⟨hA, hle, hM⟩ := approxGeod_of_euclidErrF_le (b := G.S.b γ) (D := G.S.D γ ω)
    (x := xiGamma γ ^ (99 / 100 : ℝ)) hω (Real.rpow_nonneg hξ0.le _) hsmall hη
  rw [sqrt_rpow_ninetyNine_hundredths hξ0.le] at hM
  exact ⟨hA, hle, hM⟩

/-! ## Lemma `lem:good-compl` -/

/-- **Lemma `lem:good-compl`, first bound** (source (5.1)): `P[𝒢_γᶜ] ≤ C ξ^{20}` for small `γ`.
This is `euclidFine_tail` with `R = 8`, `ε = 1/100`, `K = 20`, and `S.ξ γ = ξ_γ` (compatibility of `G`). -/
theorem good_compl_le (G : GSetup) : ∃ γc C, 0 < γc ∧ ∀ γ ∈ Ioc 0 γc,
    stdP {ω | ¬ goodEv G γ ω} ≤ ENNReal.ofReal (C * xiGamma γ ^ 20) := by
  obtain ⟨γs, C, hγs, h⟩ :=
    euclidFine_tail G.S 8 (by norm_num) (1 / 100) (by norm_num) 20 (by norm_num)
  refine ⟨min γs 1, C, lt_min hγs one_pos, fun γ hγ => ?_⟩
  have hγ2 : γ ∈ Ioo (0 : ℝ) 2 :=
    ⟨hγ.1, (hγ.2.trans (min_le_right _ _)).trans_lt one_lt_two⟩
  have hξ : G.S.ξ γ = xiGamma γ := (G.compat γ hγ2).1
  have hb := h γ ⟨hγ.1, hγ.2.trans (min_le_left _ _)⟩
  rw [hξ, show (1 - 1 / 100 : ℝ) = 99 / 100 by norm_num, Real.rpow_ofNat] at hb
  refine (measure_mono fun ω (hω : ¬ goodEv G γ ω) => ?_).trans hb
  exact lt_of_not_ge hω

/-- `x ≤ a x² + a⁻¹` in `ℝ≥0∞` for finite `x` and `a > 0` (from `a t² + a⁻¹ − t = a⁻¹ (a t − 1/2)² + (3/4) a⁻¹`). -/
theorem le_ofReal_mul_rpow_two_add_inv {x : ℝ≥0∞} (hx : x ≠ ⊤) {a : ℝ} (ha : 0 < a) :
    x ≤ ENNReal.ofReal a * x ^ (2 : ℝ) + ENNReal.ofReal a⁻¹ := by
  have ht0 : 0 ≤ x.toReal := ENNReal.toReal_nonneg
  have hamgm : x.toReal ≤ a * x.toReal ^ 2 + a⁻¹ := by
    have key : a * x.toReal ^ 2 + a⁻¹ - x.toReal =
        a⁻¹ * (a * x.toReal - 1 / 2) ^ 2 + 3 / 4 * a⁻¹ := by
      field_simp
      ring
    have : 0 ≤ a⁻¹ * (a * x.toReal - 1 / 2) ^ 2 + 3 / 4 * a⁻¹ := by positivity
    linarith
  calc x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hx).symm
    _ ≤ ENNReal.ofReal (a * x.toReal ^ 2 + a⁻¹) := ENNReal.ofReal_le_ofReal hamgm
    _ = ENNReal.ofReal a * x ^ (2 : ℝ) + ENNReal.ofReal a⁻¹ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul ha.le,
          ENNReal.ofReal_pow ht0, ENNReal.ofReal_toReal hx, ENNReal.rpow_two]

/-- **Lemma `lem:good-compl`, second bound** (BP2 D11): `E[M(η) 1_{𝒢_γᶜ}] ≤ C ξ^{10}` for small `γ` and
every measurable a.s. geodesic `η`. A.s. `M(η) ≤ T = S.locT γ B̄₁(0) < ∞`, and
`T ≤ ξ^{10} T² + ξ^{−10}`; integrate over `𝒢ᶜ` with `E T² ≤ C_T` and `P[𝒢ᶜ] ≤ C_c ξ^{20}`. -/
theorem lintegral_maxDev_compl_good_le (G : GSetup) : ∃ γc C, 0 < γc ∧ ∀ γ ∈ Ioc 0 γc,
    ∀ η : Coord → C(unitInterval, ℂ), Measurable η →
    (∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η ω)) →
    ∫⁻ ω in {ω | ¬ goodEv G γ ω}, ENNReal.ofReal (maxDev (η ω)) ∂stdP ≤
      ENNReal.ofReal (C * xiGamma γ ^ 10) := by
  obtain ⟨γ₁, C₁, hγ₁, hcompl⟩ := good_compl_le G
  obtain ⟨γ₂, C₂, hγ₂, hmom⟩ := exists_locMoments_closedBall_one G.S 2 one_le_two
  obtain ⟨γ₃, hγ₃, hloc⟩ := ae_localization_zero_one G.S
  obtain ⟨γ₄, hγ₄, hγ₄1, hξ⟩ := exists_xiGamma_pos_le
  refine ⟨min (min γ₁ γ₂) (min γ₃ γ₄), max C₁ 0 + max C₂ 0,
    lt_min (lt_min hγ₁ hγ₂) (lt_min hγ₃ hγ₄), fun γ hγ η _ hη => ?_⟩
  have hγ0 := hγ.1
  have hγ₁' : γ ≤ γ₁ := hγ.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγ₂' : γ ≤ γ₂ := hγ.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγ₃' : γ ≤ γ₃ := hγ.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγ₄' : γ ≤ γ₄ := hγ.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hγ2 : γ ∈ Ioo (0 : ℝ) 2 := ⟨hγ0, by linarith⟩
  obtain ⟨hξ0, -⟩ := hξ γ ⟨hγ0, hγ₄'⟩
  have ha0 : 0 < xiGamma γ ^ 10 := pow_pos hξ0 10
  -- the pointwise bound, almost surely
  have hpt : ∀ᵐ ω ∂stdP, ENNReal.ofReal (maxDev (η ω)) ≤
      ENNReal.ofReal (xiGamma γ ^ 10) * G.S.locT γ (Metric.closedBall 0 1) ω ^ (2 : ℝ) +
        ENNReal.ofReal (xiGamma γ ^ 10)⁻¹ := by
    filter_upwards [hloc γ ⟨hγ0, hγ₃'⟩, hη] with ω hω hηω
    obtain ⟨hTfin, -, -, -, -, hgeo⟩ := hω
    rw [← (G.compat γ hγ2).2 ω] at hηω
    obtain ⟨-, hM, -⟩ := hgeo (η ω) hηω
    calc ENNReal.ofReal (maxDev (η ω))
        ≤ ENNReal.ofReal (G.S.locT γ (Metric.closedBall 0 1) ω).toReal :=
          ENNReal.ofReal_le_ofReal hM
      _ = G.S.locT γ (Metric.closedBall 0 1) ω := ENNReal.ofReal_toReal hTfin
      _ ≤ _ := le_ofReal_mul_rpow_two_add_inv hTfin ha0
  have hP : stdP {ω | ¬ goodEv G γ ω} ≤ ENNReal.ofReal (C₁ * xiGamma γ ^ 20) :=
    hcompl γ ⟨hγ0, hγ₁'⟩
  have hTm : ∫⁻ ω, G.S.locT γ (Metric.closedBall 0 1) ω ^ (2 : ℝ) ∂stdP ≤ ENNReal.ofReal C₂ :=
    (hmom γ ⟨hγ0, hγ₂'⟩).1
  have hTs : ∫⁻ ω in {ω | ¬ goodEv G γ ω},
      G.S.locT γ (Metric.closedBall 0 1) ω ^ (2 : ℝ) ∂stdP ≤ ENNReal.ofReal C₂ :=
    (setLIntegral_le_lintegral _ _).trans hTm
  have e20 : (xiGamma γ ^ 10)⁻¹ * (max C₁ 0 * xiGamma γ ^ 20) = max C₁ 0 * xiGamma γ ^ 10 := by
    rw [show xiGamma γ ^ 20 = xiGamma γ ^ 10 * xiGamma γ ^ 10 by ring]
    field_simp
  calc ∫⁻ ω in {ω | ¬ goodEv G γ ω}, ENNReal.ofReal (maxDev (η ω)) ∂stdP
      ≤ ∫⁻ ω in {ω | ¬ goodEv G γ ω},
          (ENNReal.ofReal (xiGamma γ ^ 10) * G.S.locT γ (Metric.closedBall 0 1) ω ^ (2 : ℝ) +
            ENNReal.ofReal (xiGamma γ ^ 10)⁻¹) ∂stdP :=
        lintegral_mono_ae (ae_restrict_of_ae hpt)
    _ = ENNReal.ofReal (xiGamma γ ^ 10) * ∫⁻ ω in {ω | ¬ goodEv G γ ω},
            G.S.locT γ (Metric.closedBall 0 1) ω ^ (2 : ℝ) ∂stdP +
          ENNReal.ofReal (xiGamma γ ^ 10)⁻¹ * stdP {ω | ¬ goodEv G γ ω} := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, setLIntegral_const]
    _ ≤ ENNReal.ofReal (xiGamma γ ^ 10) * ENNReal.ofReal C₂ +
          ENNReal.ofReal (xiGamma γ ^ 10)⁻¹ * ENNReal.ofReal (C₁ * xiGamma γ ^ 20) := by
        gcongr
    _ = ENNReal.ofReal (xiGamma γ ^ 10 * C₂) +
          ENNReal.ofReal ((xiGamma γ ^ 10)⁻¹ * (C₁ * xiGamma γ ^ 20)) := by
        rw [ENNReal.ofReal_mul ha0.le, ENNReal.ofReal_mul (inv_pos.2 ha0).le]
    _ ≤ ENNReal.ofReal (xiGamma γ ^ 10 * max C₂ 0) +
          ENNReal.ofReal ((xiGamma γ ^ 10)⁻¹ * (max C₁ 0 * xiGamma γ ^ 20)) := by
        refine add_le_add (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_le_ofReal ?_)
        · exact mul_le_mul_of_nonneg_left (le_max_left _ _) ha0.le
        · refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 ha0).le
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = ENNReal.ofReal ((max C₁ 0 + max C₂ 0) * xiGamma γ ^ 10) := by
        rw [e20, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-! ## Corollary `cor:band-inclusion` -/

/-- **Corollary `cor:band-inclusion`** (source (5.12), first sentence; BP2 D1): there is `γ_b > 0` such that
for `γ ∈ (0, γ_b]`, `ω ∈ 𝒢_γ` and every constant-speed `S.D γ ω`-geodesic `η` from `0` to `1`:
`M(η) < 2ξ^{99/200} = R_max`, and if `δ ≤ R < M(η)` then `η ∈ ℬ_γ(R)`. -/
theorem bandEv_of_lt_maxDev (G : GSetup) : ∃ γb, 0 < γb ∧ ∀ γ ∈ Ioc 0 γb, ∀ ω, goodEv G γ ω →
    ∀ η, IsGeod01 (G.S.D γ ω) 0 1 η → maxDev η < 2 * xiGamma γ ^ (99/200 : ℝ) ∧
      ∀ R, dlt γ ≤ R → R < maxDev η → bandEv γ R η := by
  obtain ⟨γg, hγg, -, hgood⟩ := approxGeod_of_good G
  obtain ⟨ξb, hξb, -, hband⟩ := exists_band_gt_of_lt_maxDev
  obtain ⟨γ₀, hγ₀, -, hξ⟩ := exists_xiGamma_pos_le
  refine ⟨min γg (min γ₀ ξb), lt_min hγg (lt_min hγ₀ hξb), fun γ hγ ω hω η hη => ?_⟩
  have hγg' : γ ≤ γg := hγ.2.trans (min_le_left _ _)
  have hγ₀' : γ ≤ γ₀ := hγ.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγb' : γ ≤ ξb := hγ.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hξ0, hξγ⟩ := hξ γ ⟨hγ.1, hγ₀'⟩
  obtain ⟨-, hgoodγ⟩ := hgood γ ⟨hγ.1, hγg'⟩
  obtain ⟨hA, hΔ, hM⟩ := hgoodγ ω hω η hη
  refine ⟨?_, fun R hR hRM => ?_⟩
  · have hpos : 0 < xiGamma γ ^ (99 / 200 : ℝ) := Real.rpow_pos_of_pos hξ0 _
    have hs3 : Real.sqrt 3 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    calc maxDev η ≤ Real.sqrt 3 * xiGamma γ ^ (99 / 200 : ℝ) := hM
      _ < 2 * xiGamma γ ^ (99 / 200 : ℝ) := mul_lt_mul_of_pos_right hs3 hpos
  · exact hband (xiGamma γ) hξ0 (hξγ.trans hγb') _ η _ hA hΔ R hR hRM

end SmallGammaGeodesics
