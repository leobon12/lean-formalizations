import HigherDimLQGMetric.Sec4.GoodCover

/-!
# [1] Lemma 4.4 (packet L9b; MA6 P1, P10)

`ref1_lemma44`: there is `C > 0` (depending on `ζ`, `κ` and the law of `D`) such that for every bounded `U` and every
`θ > 0`, for `ε` small (uniformly in the deterministic subset `R ⊆ N^ε` with `|N^ε| ≤ 10 |R|` and in the bounds
`m ≤ ratio ≤ M` of the ratios `r 𝔞_{ε/r}/(c_r 𝔞_ε)`, `r = 2^{-k}`, `k ∈ R`), outside probability `θ`, for all
`z, w ∈ U`:

* (4.9) `𝔞_ε⁻¹ D̂^ε(B_{ε^{1-ζ}}(z), B_{ε^{1-ζ}}(w); B_{ε^{1-ζ}}(U)) ≤ C M D(z, w; U)`;
* (4.10) `D(B_{ε^{1-ζ}}(z), B_{ε^{1-ζ}}(w); B_{ε^{1-ζ}}(U)) ≤ C m⁻¹ 𝔞_ε⁻¹ D̂^ε(z, w; U)`,

with `D̂^ε` the LFPP distance of the localized field `ĥ*_ε` (`fieldDistIn`/`fieldSetDistIn` of `locField`).
Proof: the good cover (`l9b_goodCover`) and the deterministic chaining (`l9b_chain_upper`, `l9b_chain_lower`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁ lfppDistOn)

variable {d : ℕ}

/-- the ratio `r 𝔞_{ε/r}/(c_r 𝔞_ε)` of [1] Lemma 4.4 -/
def l9bRatio (κ : Rd d → ℝ) (ξ : ℝ) (c : ℝ → ℝ) (ε r : ℝ) : ℝ :=
  r * aEps κ ξ (ε / r) / (c r * aEps κ ξ ε)

/-- **[1] Lemma 4.4** (MA6 P1, P10). -/
theorem ref1_lemma44 (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ), DGZ.RealEpsAdapterShape d κ ξ Q)
    (hd : 3 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) (hsub : Real.sqrt (2 * d) < distExp d ξ)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : Set (Rd d), Bornology.IsBounded U → ∀ θ : ℝ≥0∞, 0 < θ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ R : Finset ℕ,
        R ⊆ nIdx ζ ε → (nIdx ζ ε).card ≤ 10 * R.card → ∀ m M : ℝ, 0 < m → 0 < M →
        (∀ k ∈ R, m ≤ l9bRatio κ ξ c ε (dyad k) ∧ l9bRatio κ ξ c ε (dyad k) ≤ M) →
        P {ω | ¬ ∀ z ∈ U, ∀ w ∈ U,
          ENNReal.ofReal ((aEps κ ξ ε)⁻¹) * fieldSetDistIn ξ (locField κ ε (h ω))
              (thickening (ε ^ (1 - ζ)) U) (ball z (ε ^ (1 - ζ))) (ball w (ε ^ (1 - ζ))) ≤
            ENNReal.ofReal (C * M) * (D (h ω)).internal U z w ∧
          setDistIn (D (h ω)) (thickening (ε ^ (1 - ζ)) U) (ball z (ε ^ (1 - ζ)))
              (ball w (ε ^ (1 - ζ))) ≤
            ENNReal.ofReal (C * m⁻¹) * (ENNReal.ofReal ((aEps κ ξ ε)⁻¹) *
              fieldDistIn ξ (locField κ ε (h ω)) U z w)} ≤ θ := by
  have hd2 : 2 ≤ d := by omega
  have hK := convKernel_contDiff (d := d) (by omega) hκ
  obtain ⟨C₃, hC₃, Hcov⟩ := l9b_goodCover hL6a hB2 hd hξ hsub hκ hD hζ0 hζ1
  refine ⟨C₃ ^ 2, by positivity, fun U hU θ hθ => ?_⟩
  obtain ⟨R', hR'⟩ := hU.subset_closedBall 0
  set R₀ : ℝ := max R' 0 + 1 with hR₀
  have hR₀0 : 0 < R₀ := by positivity
  obtain ⟨ε₁, hε₁, H1⟩ := Hcov R₀ hR₀0 θ hθ
  have hev := (l9b_eventually_locHyp hd2 hκ).and ((l9b_eventually_mesh hζ0 (2 * d)).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < min (1 : ℝ) (1 / ((d : ℝ) + 1)) from
      lt_min one_pos (by positivity))))
  obtain ⟨ε₂, hε₂, H2⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro Ω _ P _ h hh ε hε R hR hRcard m M hm hM hratio
  obtain ⟨⟨hε0, hε1, hrad, -, -⟩, hmesh, hεs⟩ := H2 ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩
  have hεd : (d : ℝ) * ε < 1 := by
    have h1 : ε < 1 / ((d : ℝ) + 1) := hεs.2.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  have hcov := H1 P h hh ε ⟨hε0, hε.2.trans_le (min_le_left _ _)⟩ R hR hRcard
  refine le_trans (measure_mono fun ω hω => ?_) hcov
  -- `ω` is good: every grid point has a good radius
  by_contra hgoodcov
  simp only [mem_ofPred_eq, not_exists, not_and, not_forall, not_not] at hgoodcov
  apply hω
  set ψ := locField κ ε (h ω) with hψdef
  have hψ : Continuous ψ := continuous_locField hK hrad _
  set a := aEps κ ξ ε with ha
  have ha0 : 0 < a := l10a_aEps_pos hd2 hκ ξ hε0
  set ε' := ε ^ (1 - ζ) / 10 with hε'
  have h10 : 10 * ε' = ε ^ (1 - ζ) := by rw [hε']; ring
  set ρ := ε ^ (1 - ζ / 2) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hε0 _
  let good : Rd d → ℝ → Prop := fun u r => (∃ k ∈ R, r = dyad k) ∧
    shellGood κ ξ D c ε C₃ u r (h ω)
  let A : Rd d → ℝ → ℝ := fun u r => c r * Real.exp (ξ * sphereAvg (h ω) r u)
  let B : Rd d → ℝ → ℝ := fun u r => r * aEps κ ξ (ε / r) * Real.exp (ξ * sphereAvg (h ω) r u)
  have hgr : ∀ u r, good u r → ∃ k ∈ R, r = dyad k := fun u r hg => hg.1
  have hrε : ∀ u r, good u r → 0 < r ∧ r ≤ ε' := by
    intro u r hg
    obtain ⟨k, hk, rfl⟩ := hg.1
    exact ⟨dyad_pos k, dyad_le_of_mem_nIdx hε0 (hR hk)⟩
  have hcov' : ∀ x ∈ U, ∃ u r, ρ ≤ r ∧ r ≤ ε' ∧ ‖x - u‖ < r / 2 ∧ good u r := by
    intro x hx
    obtain ⟨u, hu, hxu⟩ := exists_gridPt_near hε0 x
    have hxR : ‖x‖ ≤ R' := by
      have := hR' hx; rwa [mem_closedBall, dist_zero_right] at this
    have huR : ‖u‖ < R₀ := by
      have : ‖u‖ ≤ ‖x‖ + ‖x - u‖ := by
        calc ‖u‖ = ‖x - (x - u)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      have := le_max_left R' 0
      linarith
    obtain ⟨k, hk, hgk⟩ := hgoodcov u (mem_l9bGrid hR₀0.le hε0 hu huR)
    refine ⟨u, dyad k, le_dyad_of_mem_nIdx hε0 hε1 hζ1 (hR hk),
      dyad_le_of_mem_nIdx hε0 (hR hk), ?_, ⟨⟨k, hk, rfl⟩, hgk⟩⟩
    have := le_dyad_of_mem_nIdx hε0 hε1 hζ1 (hR hk)
    linarith
  -- positivity of the scales
  have hBpos : ∀ u r, good u r → 0 < B u r := by
    intro u r hg
    obtain ⟨hr, -⟩ := hrε u r hg
    have := l10a_aEps_pos hd2 hκ ξ (div_pos hε0 hr)
    exact mul_pos (mul_pos hr this) (Real.exp_pos _)
  have hApos : ∀ u r, good u r → 0 < A u r := by
    intro u r hg
    exact mul_pos (hD.c_pos r (hrε u r hg).1) (Real.exp_pos _)
  -- the ratio bounds in terms of `A`, `B`
  have hratio' : ∀ u r, good u r → a * m * A u r ≤ B u r ∧ B u r ≤ a * M * A u r := by
    intro u r hg
    obtain ⟨k, hk, rfl⟩ := hg.1
    obtain ⟨hmk, hMk⟩ := hratio k hk
    have hcr := hD.c_pos (dyad k) (dyad_pos k)
    have hE := Real.exp_pos (ξ * sphereAvg (h ω) (dyad k) u)
    simp only [l9bRatio] at hmk hMk
    rw [le_div_iff₀ (by positivity)] at hmk
    rw [div_le_iff₀ (by positivity)] at hMk
    simp only [A, B]
    constructor <;> nlinarith
  intro z hz w hw
  constructor
  · have hup := l9b_chain_upper (ξ := ξ) hd2 hψ hρ0 good (A := A) (B := B) (C := C₃) (M := a * M)
      (by linarith) (by positivity) hcov' hrε (fun u r hg => (hApos u r hg).le)
      (fun u r hg => by
        have := hg.2.1
        simp only [A]
        rwa [mul_assoc] at this)
      (fun u r hg => by
        have := hg.2.2.2.2
        simp only [B]
        rwa [mul_assoc C₃] at this)
      (fun u r hg => (hratio' u r hg).2) z hz w hw
    rw [h10] at hup
    calc ENNReal.ofReal a⁻¹ * fieldSetDistIn ξ ψ (thickening (ε ^ (1 - ζ)) U)
          (ball z (ε ^ (1 - ζ))) (ball w (ε ^ (1 - ζ)))
        ≤ ENNReal.ofReal a⁻¹ * (ENNReal.ofReal (C₃ ^ 2 * (a * M)) * (D (h ω)).internal U z w) :=
          by gcongr
      _ = ENNReal.ofReal (C₃ ^ 2 * M) * (D (h ω)).internal U z w := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          field_simp
  · have hlow := l9b_chain_lower (ξ := ξ) hd2 hψ hρ0 good (A := A) (B := B) (C := C₃) (m := a * m)
      (by linarith) (by positivity) hcov' hrε
      (fun u r hg => by
        have := hg.2.2.1
        simp only [A]
        rwa [mul_assoc] at this)
      (fun u r hg => by
        have := hg.2.2.2.1
        simp only [B]
        rwa [mul_assoc C₃⁻¹] at this)
      (fun u r hg => (hratio' u r hg).1) z hz w hw
    rw [h10] at hlow
    calc setDistIn (D (h ω)) (thickening (ε ^ (1 - ζ)) U) (ball z (ε ^ (1 - ζ)))
          (ball w (ε ^ (1 - ζ)))
        ≤ ENNReal.ofReal (C₃ ^ 2 / (a * m)) * fieldDistIn ξ ψ U z w := hlow
      _ = ENNReal.ofReal (C₃ ^ 2 * m⁻¹) * (ENNReal.ofReal a⁻¹ * fieldDistIn ξ ψ U z w) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          field_simp

end HigherDimLQGMetric
