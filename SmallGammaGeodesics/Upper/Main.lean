import SmallGammaGeodesics.Upper.MainMean
import SmallGammaGeodesics.Assembly.Scalar

/-!
# The upper bounds (5.14)–(5.15) on the coordinate space (packet P-U3)

Blueprint `s5-upper.tex`, Proposition `prop:tail` (source (5.15)) and Theorem `thm:upper`; BP2
detail D11; ruling G27. Both take the interface hypotheses `hCC` (one-sided conformal covariance)
and `h42` (Lemma 4.2′) of ruling G10.

* `tail_maxDev_le`: `P[M(η γ) > A ξ^{2/3}] ≤ C (A^{-3} + A^{-4}) + ε` for all small `γ`. Up to the
  null set where `η γ` is not a geodesic, `{M > Aδ} ⊆ 𝒢ᶜ ∪ (𝒢 ∩ ℬ(Aδ))` (`bandEv_of_lt_maxDev`,
  `A ≥ 1`); `P[𝒢ᶜ] ≤ C_c ξ^{20}` (`good_compl_le`), and the band event at the scale `Aδ` is
  bounded by Lemma 5.1 and the mean bound (`bandEv_scale_le_of_lemma51`, applied to `lemma51` and
  `mean_maxDev_le`).
* `upperBoundsXi_of_interfaces`: `UpperBoundsXi stdP η`, i.e. (5.14) and (5.15) with one constant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open GaussianLQG LQGMetric LQGMetric.Blueprint

/-- **Proposition `prop:tail`** (source (5.15)): for every family of measurable a.s. geodesics,
every `A ≥ 1` and `ε > 0`, `P[M(η γ) > A ξ^{2/3}] ≤ C (A^{-3} + A^{-4}) + ε` for all small
`γ > 0`. -/
theorem tail_maxDev_le (G : GSetup) (hCC : ∀ γ, 0 < γ → γ < 2 → CC.ConfCovLE γ (G.Dfam γ))
    (h42 : Lemma42) : ∃ C, ∀ η : ℝ → Coord → C(unitInterval, ℂ), (∀ γ, Measurable (η γ)) →
    (∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η γ ω)) →
    ∀ A, 1 ≤ A → ∀ ε, 0 < ε → ∀ᶠ γ in 𝓝[>] (0:ℝ),
      stdP {ω | A * dlt γ < maxDev (η γ ω)} ≤
        ENNReal.ofReal (C * (A ^ (-3:ℝ) + A ^ (-4:ℝ)) + ε) := by
  obtain ⟨C, hC⟩ := bandEv_scale_le_of_lemma51 G (lemma51 G hCC h42) (mean_maxDev_le G hCC h42)
  obtain ⟨γc, Cc, hγc, hcompl⟩ := good_compl_le G
  obtain ⟨γb, hγb, hband⟩ := bandEv_of_lt_maxDev G
  obtain ⟨γ₀, hγ₀, hγ₀1, hξ⟩ := exists_xiGamma_pos_le
  refine ⟨max C 0, fun η hm hη A hA ε hε => ?_⟩
  have hε2 : 0 < ε / 2 := by positivity
  have hmin : 0 < min (min γc γb) γ₀ := lt_min (lt_min hγc hγb) hγ₀
  filter_upwards [hC η hm hη A hA (ε / 2) hε2, Tight.eventually_mem_Ioo_zero hmin,
    Tight.eventually_mul_pow_lt (max Cc 0) (n := 20) (by norm_num) hε2] with γ hbandγ hγI hsmall
  have hγ0 : 0 < γ := hγI.1
  have hγc' : γ ∈ Ioc (0:ℝ) γc :=
    ⟨hγ0, (hγI.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le⟩
  have hγb' : γ ∈ Ioc (0:ℝ) γb :=
    ⟨hγ0, (hγI.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le⟩
  have hγ₀' : γ ∈ Ioc (0:ℝ) γ₀ := ⟨hγ0, (hγI.2.trans_le (min_le_right _ _)).le⟩
  have hγ2 : γ < 2 := by linarith [hγ₀'.2]
  obtain ⟨hξ0, hξγ⟩ := hξ γ hγ₀'
  -- the inclusion `{M > Aδ} ⊆ 𝒢ᶜ ∪ (𝒢 ∩ ℬ(Aδ))`, up to a null set
  have hδA : dlt γ ≤ A * dlt γ := le_mul_of_one_le_left (Real.rpow_nonneg hξ0.le _) hA
  have hsub : {ω | A * dlt γ < maxDev (η γ ω)} ≤ᵐ[stdP]
      ({ω | ¬ goodEv G γ ω} ∪ {ω | goodEv G γ ω ∧ bandEv γ (A * dlt γ) (η γ ω)} : Set Coord) := by
    filter_upwards [hη γ hγ0 hγ2] with ω hω hωM
    by_cases hg : goodEv G γ ω
    · have hω' : IsGeod01 (G.S.D γ ω) 0 1 (η γ ω) := by
        rw [(G.compat γ ⟨hγ0, hγ2⟩).2 ω]
        exact hω
      exact Or.inr ⟨hg, (hband γ hγb' ω hg (η γ ω) hω').2 _ hδA hωM⟩
    · exact Or.inl hg
  -- the complement of the good event is small
  have hcomp : stdP {ω | ¬ goodEv G γ ω} ≤ ENNReal.ofReal (ε / 2) := by
    refine (hcompl γ hγc').trans (ENNReal.ofReal_le_ofReal ?_)
    have h20 : xiGamma γ ^ 20 ≤ γ ^ 20 := pow_le_pow_left₀ hξ0.le hξγ 20
    calc Cc * xiGamma γ ^ 20 ≤ max Cc 0 * xiGamma γ ^ 20 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max Cc 0 * γ ^ 20 := mul_le_mul_of_nonneg_left h20 (le_max_right _ _)
      _ ≤ ε / 2 := hsmall.le
  have hA0 : 0 < A := by linarith
  have hApos : 0 ≤ A ^ (-3:ℝ) + A ^ (-4:ℝ) :=
    add_nonneg (Real.rpow_nonneg hA0.le _) (Real.rpow_nonneg hA0.le _)
  have hK : 0 ≤ max C 0 * (A ^ (-3:ℝ) + A ^ (-4:ℝ)) := mul_nonneg (le_max_right _ _) hApos
  calc stdP {ω | A * dlt γ < maxDev (η γ ω)}
      ≤ stdP ({ω | ¬ goodEv G γ ω} ∪ {ω | goodEv G γ ω ∧ bandEv γ (A * dlt γ) (η γ ω)}) :=
        measure_mono_ae hsub
    _ ≤ stdP {ω | ¬ goodEv G γ ω} + stdP {ω | goodEv G γ ω ∧ bandEv γ (A * dlt γ) (η γ ω)} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (max C 0 * (A ^ (-3:ℝ) + A ^ (-4:ℝ)) + ε / 2) := by
        refine add_le_add hcomp (hbandγ.trans (ENNReal.ofReal_le_ofReal ?_))
        have := mul_le_mul_of_nonneg_right (le_max_left C 0) hApos
        linarith
    _ = ENNReal.ofReal (max C 0 * (A ^ (-3:ℝ) + A ^ (-4:ℝ)) + ε) := by
        rw [← ENNReal.ofReal_add hε2.le (by linarith)]
        congr 1
        ring

/-- **Theorem `thm:upper`** (source (5.14)–(5.15); ruling G27): for a coordinate setup `G`, the
interfaces `hCC` and `h42`, and every family `η` of measurable maps that are a.s. constant-speed
geodesics from `0` to `1` for `γ ∈ (0,2)`, the upper bounds `UpperBoundsXi stdP η` hold. -/
theorem upperBoundsXi_of_interfaces (G : GSetup)
    (hCC : ∀ γ, 0 < γ → γ < 2 → CC.ConfCovLE γ (G.Dfam γ)) (h42 : Lemma42)
    (η : ℝ → Coord → C(unitInterval, ℂ)) (hm : ∀ γ, Measurable (η γ))
    (hη : ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η γ ω)) :
    UpperBoundsXi stdP η := by
  obtain ⟨C₆, γ₆, hγ₆, hmean⟩ := mean_maxDev_le G hCC h42
  obtain ⟨C₇, htail⟩ := tail_maxDev_le G hCC h42
  refine ⟨max C₆ C₇, min γ₆ 1, lt_min hγ₆ one_pos, fun γ hγ => ?_, fun A hA ε hε => ?_⟩
  · have hγ0 : 0 < γ := hγ.1
    have hγ1 : γ < 1 := hγ.2.trans_le (min_le_right _ _)
    have hγ2 : γ < 2 := by linarith
    refine (hmean γ ⟨hγ0, (hγ.2.trans_le (min_le_left _ _)).le⟩ (η γ) (hm γ)
      (hη γ hγ0 hγ2)).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (GM.xiGamma_pos hγ0).le _)
  · filter_upwards [htail η hm hη A hA ε hε] with γ hγ
    refine hγ.trans (ENNReal.ofReal_le_ofReal ?_)
    have hA0 : 0 < A := by linarith
    have hApos : 0 ≤ A ^ (-3:ℝ) + A ^ (-4:ℝ) :=
      add_nonneg (Real.rpow_nonneg hA0.le _) (Real.rpow_nonneg hA0.le _)
    have := mul_le_mul_of_nonneg_right (le_max_right C₆ C₇) hApos
    linarith

end SmallGammaGeodesics
