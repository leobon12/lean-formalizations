import HigherDimLQGMetric.Sec4.LfppTight

/-!
# Shell quantities of the convolution LFPP at every scale and centre (packet L9b, [1] Lemma 4.3 (3)–(4))

[1] (4.7)/(3.13): `𝔞_ε⁻¹ D^ε_h(u + r·, u + r·) = (r 𝔞_{ε/r}/𝔞_ε) e^{ξ h_r(u)} · 𝔞_{ε/r}⁻¹ D^{ε/r}_{h'}(·,·)` with
`h' = h(u + r ·) - h_r(u)` a normalized LGF, so the canonical bounds of `LfppTight` transfer to every scale and
centre, uniformly in `0 < ε < r`:

* `l9b_lfpp_across_prob`: `P[D^ε(∂B_{ar}(u), ∂B_{br}(u)) < c r 𝔞_{ε/r} e^{ξ h_r(u)}] < θ`;
* `l9b_lfpp_diam_prob`: `P[diam_{A_{r/2,2r}(u)}(∂B_r(u); D^ε) > C r 𝔞_{ε/r} e^{ξ h_r(u)}] < θ`.

(Outer measures; the law transfer is `l9b_preimage_le_normLGFLaw`.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁ lfppDistOn)

variable {d : ℕ}

/-- **LFPP across lower bound at every scale** (MA6 P2 + scaling): for `0 < a < b`, `θ > 0` there is `c > 0`
such that for every normalized LGF, every `0 < ε < r` and every centre `u`,
`P[D^ε_h(∂B_{ar}(u), ∂B_{br}(u)) < c r 𝔞_{ε/r} e^{ξ h_r(u)}] < θ`. -/
theorem l9b_lfpp_across_prob (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ), DGZ.RealEpsAdapterShape d κ ξ Q)
    (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) {ξ : ℝ} (hξ : 0 < ξ)
    (hsub : Real.sqrt (2 * d) < distExp d ξ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ c : ℝ, 0 < c ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ ε r : ℝ, 0 < ε → ε < r → ∀ u : Rd d,
        P {ω | DGZ.lfppSetDist ξ (convMollify κ ε (h ω)) univ (sphere u (a * r))
          (sphere u (b * r)) < c * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u)} < θ := by
  obtain ⟨hpos, hT⟩ := l9b_lfpp_tight hL6a hB2 hd hκ hξ hsub
  obtain ⟨c, hc, H⟩ := l9b_lfpp_across_lower hd hκ hpos hT ha hab hθ
  refine ⟨c, hc, ?_⟩
  intro Ω _ P _ h hh ε r hε hεr u
  have hr : 0 < r := hε.trans hεr
  have hδ : ε / r ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hε hr, (div_lt_one hr).2 hεr⟩
  have hN := isNormalizedLGF_recentAff hd hh.1 hr u
  let A : Set (DistRd d) := {g | DGZ.lfppSetDist ξ (convMollify κ (ε / r) g) univ
    (sphere 0 a) (sphere 0 b) < c * aEps κ ξ (ε / r)}
  calc P {ω | DGZ.lfppSetDist ξ (convMollify κ ε (h ω)) univ (sphere u (a * r))
        (sphere u (b * r)) < c * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u)}
      ≤ P ((fun ω => recentAff r u (h ω)) ⁻¹' A) := by
        refine measure_mono_ae ?_
        filter_upwards [l9b_ae_convMollify_affine hd hκ hh u hr] with ω ⟨hsc, hc'⟩ hbad
        have hid : ∀ x, convMollify κ ε (h ω) (u + r • x) =
            convMollify κ (ε / r) (recentAff r u (h ω)) x +
              sphereAvg (affineComp r u (h ω)) 1 0 := hsc ε hε
        have hscale := l9b_lfppSetDist_affine (ξ := ξ) hr hid univ (sphere 0 a) (sphere 0 b)
        rw [l9b_image_affine_univ hr, l9b_image_affine_sphere hr, l9b_image_affine_sphere hr,
          mul_comm r a, mul_comm r b, hc'] at hscale
        have hbad' : DGZ.lfppSetDist ξ (convMollify κ ε (h ω)) univ (sphere u (a * r))
            (sphere u (b * r)) < c * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) :=
          hbad
        rw [hscale] at hbad'
        show DGZ.lfppSetDist ξ (convMollify κ (ε / r) (recentAff r u (h ω))) univ
          (sphere 0 a) (sphere 0 b) < c * aEps κ ξ (ε / r)
        have hk : 0 < r * Real.exp (ξ * sphereAvg (h ω) r u) := by positivity
        have : r * Real.exp (ξ * sphereAvg (h ω) r u) *
            DGZ.lfppSetDist ξ (convMollify κ (ε / r) (recentAff r u (h ω))) univ (sphere 0 a)
              (sphere 0 b) < r * Real.exp (ξ * sphereAvg (h ω) r u) * (c * aEps κ ξ (ε / r)) := by
          calc _ < c * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) := hbad'
            _ = _ := by ring
        exact lt_of_mul_lt_mul_left this hk.le
    _ ≤ normLGFLaw d A := l9b_preimage_le_normLGFLaw hd hN A
    _ < θ := H _ hδ

/-- **LFPP sphere-diameter upper bound at every scale** (MA6 P2 + scaling): for `θ > 0` there is `C > 0`
such that for every normalized LGF, every `0 < ε < r` and every centre `u`,
`P[diam_{A_{r/2,2r}(u)}(∂B_r(u); D^ε) > C r 𝔞_{ε/r} e^{ξ h_r(u)}] < θ` (piecewise-`C¹` internal distances). -/
theorem l9b_lfpp_diam_prob (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ), DGZ.RealEpsAdapterShape d κ ξ Q)
    (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) {ξ : ℝ} (hξ : 0 < ξ)
    (hsub : Real.sqrt (2 * d) < distExp d ξ) {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ ε r : ℝ, 0 < ε → ε < r → ∀ u : Rd d,
        P {ω | C * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) <
          DGZ.lfppDiam ξ (convMollify κ ε (h ω)) (sphere u r) (ann u (r / 2) (2 * r))} < θ := by
  obtain ⟨hpos, hT⟩ := l9b_lfpp_tight hL6a hB2 hd hκ hξ hsub
  obtain ⟨C, hC, H⟩ := l9b_lfpp_diam_upper hd hκ hpos hT hθ
  refine ⟨C, hC, ?_⟩
  intro Ω _ P _ h hh ε r hε hεr u
  have hr : 0 < r := hε.trans hεr
  have hδ : ε / r ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hε hr, (div_lt_one hr).2 hεr⟩
  have hN := isNormalizedLGF_recentAff hd hh.1 hr u
  let A : Set (DistRd d) := {g | C * aEps κ ξ (ε / r) <
    DGZ.lfppDiam ξ (convMollify κ (ε / r) g) (sphere 0 1) (ann 0 (1 / 2) 2)}
  calc P {ω | C * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) <
        DGZ.lfppDiam ξ (convMollify κ ε (h ω)) (sphere u r) (ann u (r / 2) (2 * r))}
      ≤ P ((fun ω => recentAff r u (h ω)) ⁻¹' A) := by
        refine measure_mono_ae ?_
        filter_upwards [l9b_ae_convMollify_affine hd hκ hh u hr] with ω ⟨hsc, hc'⟩ hbad
        have hid : ∀ x, convMollify κ ε (h ω) (u + r • x) =
            convMollify κ (ε / r) (recentAff r u (h ω)) x +
              sphereAvg (affineComp r u (h ω)) 1 0 := hsc ε hε
        have hscale := l9b_lfppDiam_affine (ξ := ξ) hr hid (sphere 0 1) (ann 0 (1 / 2) 2)
        rw [l9b_image_affine_sphere hr, l9b_image_affine_ann hr, mul_one,
          show r * (1 / 2) = r / 2 by ring, mul_comm r 2, hc'] at hscale
        have hbad' : C * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) <
            DGZ.lfppDiam ξ (convMollify κ ε (h ω)) (sphere u r) (ann u (r / 2) (2 * r)) := hbad
        rw [hscale] at hbad'
        show C * aEps κ ξ (ε / r) < DGZ.lfppDiam ξ (convMollify κ (ε / r) (recentAff r u (h ω)))
          (sphere 0 1) (ann 0 (1 / 2) 2)
        have hk : 0 < r * Real.exp (ξ * sphereAvg (h ω) r u) := by positivity
        have : r * Real.exp (ξ * sphereAvg (h ω) r u) * (C * aEps κ ξ (ε / r)) <
            r * Real.exp (ξ * sphereAvg (h ω) r u) * DGZ.lfppDiam ξ
              (convMollify κ (ε / r) (recentAff r u (h ω))) (sphere 0 1) (ann 0 (1 / 2) 2) := by
          calc _ = C * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) := by ring
            _ < _ := hbad'
        exact lt_of_mul_lt_mul_left this hk.le
    _ ≤ normLGFLaw d A := l9b_preimage_le_normLGFLaw hd hN A
    _ < θ := H _ hδ

end HigherDimLQGMetric
