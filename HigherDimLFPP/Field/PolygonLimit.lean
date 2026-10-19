import HigherDimLFPP.Field.QPolygon
import HigherDimLFPP.Field.ExpectedSupDrift

/-!
# HA3's interface (I5): the polygon covariance limit (packet P-F3a, target T3)

Source: planning audit HA3 (`planning/audits/HA3-section-4.md`), §7, interface (I5), and
Details D5, Step 1d (`C_δ → C` uniformly on `B̂²`); source §4, Lemma 4.3, Step 1, which uses
Lemmas 3.2–3.3 through it.

**Statement** (`polygonCovLimit`).  For every `n` and `R`, uniformly for `f, g` in the vertex ball
`B̂_R = {f ∈ V_{n,d} : max_i |f(i 2⁻ⁿ)| ≤ R}`,

`δ⁻¹ Λ(ν_{Q_δ(f)} - ν_I, ν_{Q_δ(g)} - ν_I) → π ∫₀¹ (|f| + |g| - |f - g|) = gCov f g`

as `δ ↓ 0`, where `Λ = logCov` is the all-scale log covariance (3.2), `I = [0, e₁]` and `Q_δ(f)`
is the polygon of HA3 D5, Step 1a (`qMeasure`, file `QPolygon.lean`).  The all-scale covariance
form for an admissible kernel is `polygonCovLimit_scaleCov`; the uniform-convergence form is
`tendstoUniformlyOn_polygon_logCov`.

**Proof** (HA3 (I5)).  `ν_I = μ_{δ0}` (`graphMeasure_zero`), so by bilinearity
(`logCov_split4`)

`Λ(ν_f - ν_I, ν_g - ν_I) = Λ(μ_f - μ_0, μ_g - μ_0) + Λ(ν_f - μ_f, μ_g - μ_0)
  + Λ(μ_f - μ_0, ν_g - μ_g) + Λ(ν_f - μ_f, ν_g - μ_g)`

with `μ_f = μ_{δf}`.  The first term is (3.8′) (`tendstoUniformlyOn_graph_logCov`).  The others
are bounded by Lemma 3.1 (`transport_logCov_bound_of_support`), with the couplings
`W∞(ν_{Q_δ(f)}, μ_{δf}) ≤ A δ²` (`qPolygon_facts`) and `W∞(μ_{δg}, μ_{δ0}) ≤ δ R` (the same-abscissa
coupling behind (3.9)): they are `O(δ^{3/2})` and `O(δ²)`, hence `o(δ)` uniformly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP

open LQGDimension (PSDOn)

variable {d : ℕ}

/-- Bilinearity of `logCov` (pure algebra): splitting `A - Z = (A - A') + (A' - Z)` and
`B - Z = (B - B') + (B' - Z)`. -/
theorem logCov_split4 (A A' B B' Z : Measure (Rd d)) :
    logCov A Z B Z = logCov A' Z B' Z + logCov A A' B' Z + logCov A' Z B B' + logCov A A' B B' := by
  unfold logCov
  ring

/-- Below `δ₀(n, R)`, `δ R ≤ 1/2`. -/
theorem mul_le_half_of_le_qDelta0 {n : ℕ} {R δ : ℝ} (hR0 : 0 ≤ R) (hδ : 0 ≤ δ)
    (hδ0 : δ ≤ qDelta0 n R) : δ * R ≤ 1 / 2 := by
  have h := hδ0.trans (min_le_right _ _)
  have hD : (0 : ℝ) < 8 * (2 * ((2 ^ n) ^ 2 * (2 * R) ^ 2) + 2 ^ n * (2 * R) ^ 2 / 2) +
      2 * (2 * R) + 1 := by positivity
  rw [le_div_iff₀ hD] at h
  have hκ : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h1 : 0 ≤ 8 * (2 * (((2 : ℝ) ^ n) ^ 2 * (2 * R) ^ 2) + 2 ^ n * (2 * R) ^ 2 / 2) := by
    positivity
  nlinarith

/-- A vertex ball with a negative radius is empty. -/
theorem vertBall_eq_empty_of_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {R : ℝ} (hR : R < 0) : vertBall E n R = ∅ := by
  ext f
  simp only [mem_empty_iff_false, iff_false]
  intro hf
  have := hf.2 0 (Nat.zero_le _)
  rw [Nat.cast_zero, zero_div, hf.1.1, norm_zero] at this
  linarith

/-- The error terms of (I5) for fixed `f, g ∈ B̂_R` and `0 < δ ≤ δ₀(n, R)`:
`|δ⁻¹ Λ(ν_{Q_δ(f)} - ν_I, ν_{Q_δ(g)} - ν_I) - δ⁻¹ Λ(μ_{δf} - μ_{δ0}, μ_{δg} - μ_{δ0})|
  ≤ 2 C √(A R δ) + C A δ`, with `C` the Lemma 3.1 constant for growth constant `4` and
`A = qConst n R`. -/
theorem abs_polygon_logCov_sub_graph_le (hd : 0 < d) (n : ℕ) {R : ℝ} (hR0 : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ qDelta0 n R →
      ∀ f ∈ vertBall (Rd (d - 1)) n R, ∀ g ∈ vertBall (Rd (d - 1)) n R,
      |δ⁻¹ * logCov (qMeasure d n δ f) (Upper.segMeasure 0 (e₁ d)) (qMeasure d n δ g)
          (Upper.segMeasure 0 (e₁ d)) -
        δ⁻¹ * logCov (graphMeasure d δ f) (graphMeasure d δ 0) (graphMeasure d δ g)
          (graphMeasure d δ 0)| ≤
        2 * C * Real.sqrt (qConst n R * R * δ) + C * qConst n R * δ := by
  obtain ⟨C, hC0, hC⟩ := transport_logCov_bound_of_support d 4
  refine ⟨C, hC0, fun δ hδ hδ0 f hf g hg => ?_⟩
  set A := qConst n R with hA
  have hA0 : 0 ≤ A := by rw [hA, qConst]; positivity
  obtain ⟨hpf, hGf, hCf, hSf⟩ := qPolygon_facts hd hR0 hδ hδ0 hf
  obtain ⟨hpg, hGg, hCg, hSg⟩ := qPolygon_facts hd hR0 hδ hδ0 hg
  have hδR : δ * R ≤ 1 / 2 := mul_le_half_of_le_qDelta0 hR0 hδ.le hδ0
  have hfm : Measurable f := (Var.Vg_continuous hf.1).measurable
  have hgm : Measurable g := (Var.Vg_continuous hg.1).measurable
  have hfR : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ R := fun x _ => Vg_norm_le_of_verts hf.1 hf.2 x
  have hgR : ∀ x ∈ Icc (0 : ℝ) 1, ‖g x‖ ≤ R := fun x _ => Vg_norm_le_of_verts hg.1 hg.2 x
  have h0R : ∀ x ∈ Icc (0 : ℝ) 1, ‖(0 : ℝ → Rd (d - 1)) x‖ ≤ R := fun x _ => by
    simp only [Pi.zero_apply, norm_zero]; exact hR0
  -- growth bounds (constant `4`, scale `1`) and supports (radius `2`)
  have gr : ∀ h : ℝ → Rd (d - 1), Measurable h → GrowthBound (graphMeasure d δ h) 4 1 :=
    fun h hh => (graphMeasure_growthBound hd hh).mono_const one_pos (by norm_num)
  have sp : ∀ h : ℝ → Rd (d - 1), Measurable h → (∀ x ∈ Icc (0 : ℝ) 1, ‖h x‖ ≤ R) →
      ∀ᵐ z ∂(graphMeasure d δ h), ‖z‖ ≤ 2 := by
    intro h hh hhR
    filter_upwards [ae_norm_le_graphMeasure hd hh hhR] with z hz
    rw [abs_of_pos hδ] at hz
    linarith
  -- the couplings
  have c0g : CoupledWithin (graphMeasure d δ g) (graphMeasure d δ 0) (δ * R) :=
    coupledWithin_graphMeasure (f := g) (g := 0) hδ.le hgm measurable_const fun x hx => by
      simpa only [Pi.zero_apply, sub_zero] using hgR x hx
  have c0f : CoupledWithin (graphMeasure d δ f) (graphMeasure d δ 0) (δ * R) :=
    coupledWithin_graphMeasure (f := f) (g := 0) hδ.le hfm measurable_const fun x hx => by
      simpa only [Pi.zero_apply, sub_zero] using hfR x hx
  have hAδ : 0 ≤ A * δ ^ 2 := by positivity
  have hδR0 : 0 ≤ δ * R := by positivity
  -- the three error terms
  have t2 := hC (qMeasure d n δ f) (graphMeasure d δ f) (graphMeasure d δ g) (graphMeasure d δ 0)
    1 1 (A * δ ^ 2) (δ * R) 2 one_pos one_pos hAδ hδR0 hGf (gr f hfm) (gr g hgm)
    (gr 0 measurable_const) hCf c0g hSf (sp f hfm hfR) (sp g hgm hgR) (sp 0 measurable_const h0R)
  have t3 := hC (graphMeasure d δ f) (graphMeasure d δ 0) (qMeasure d n δ g) (graphMeasure d δ g)
    1 1 (δ * R) (A * δ ^ 2) 2 one_pos one_pos hδR0 hAδ (gr f hfm) (gr 0 measurable_const) hGg
    (gr g hgm) c0f hCg (sp f hfm hfR) (sp 0 measurable_const h0R) hSg (sp g hgm hgR)
  have t4 := hC (qMeasure d n δ f) (graphMeasure d δ f) (qMeasure d n δ g) (graphMeasure d δ g)
    1 1 (A * δ ^ 2) (A * δ ^ 2) 2 one_pos one_pos hAδ hAδ hGf (gr f hfm) hGg (gr g hgm) hCf hCg
    hSf (sp f hfm hfR) hSg (sp g hgm hgR)
  rw [div_one] at t2 t3 t4
  -- simplify the square roots
  have e2 : Real.sqrt (A * δ ^ 2 * (δ * R)) = δ * Real.sqrt (A * R * δ) := by
    rw [show A * δ ^ 2 * (δ * R) = δ ^ 2 * (A * R * δ) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hδ.le]
  have e3 : Real.sqrt (δ * R * (A * δ ^ 2)) = δ * Real.sqrt (A * R * δ) := by
    rw [show δ * R * (A * δ ^ 2) = δ ^ 2 * (A * R * δ) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hδ.le]
  have e4 : Real.sqrt (A * δ ^ 2 * (A * δ ^ 2)) = A * δ ^ 2 := Real.sqrt_mul_self hAδ
  rw [e2] at t2
  rw [e3] at t3
  rw [e4] at t4
  -- assemble
  rw [← graphMeasure_zero δ, logCov_split4 (qMeasure d n δ f) (graphMeasure d δ f)
    (qMeasure d n δ g) (graphMeasure d δ g) (graphMeasure d δ 0)]
  have hsplit : δ⁻¹ * (logCov (graphMeasure d δ f) (graphMeasure d δ 0) (graphMeasure d δ g)
        (graphMeasure d δ 0) +
      logCov (qMeasure d n δ f) (graphMeasure d δ f) (graphMeasure d δ g) (graphMeasure d δ 0) +
      logCov (graphMeasure d δ f) (graphMeasure d δ 0) (qMeasure d n δ g) (graphMeasure d δ g) +
      logCov (qMeasure d n δ f) (graphMeasure d δ f) (qMeasure d n δ g) (graphMeasure d δ g)) -
      δ⁻¹ * logCov (graphMeasure d δ f) (graphMeasure d δ 0) (graphMeasure d δ g)
        (graphMeasure d δ 0) =
      δ⁻¹ * (logCov (qMeasure d n δ f) (graphMeasure d δ f) (graphMeasure d δ g)
        (graphMeasure d δ 0) +
      logCov (graphMeasure d δ f) (graphMeasure d δ 0) (qMeasure d n δ g) (graphMeasure d δ g) +
      logCov (qMeasure d n δ f) (graphMeasure d δ f) (qMeasure d n δ g) (graphMeasure d δ g)) := by
    ring
  rw [hsplit, abs_mul, abs_of_pos (inv_pos.2 hδ)]
  have hsum := (abs_add_three _ _ _).trans (add_le_add (add_le_add t2 t3) t4)
  calc δ⁻¹ * |logCov (qMeasure d n δ f) (graphMeasure d δ f) (graphMeasure d δ g)
        (graphMeasure d δ 0) +
      logCov (graphMeasure d δ f) (graphMeasure d δ 0) (qMeasure d n δ g) (graphMeasure d δ g) +
      logCov (qMeasure d n δ f) (graphMeasure d δ f) (qMeasure d n δ g) (graphMeasure d δ g)|
      ≤ δ⁻¹ * (C * (δ * Real.sqrt (A * R * δ)) + C * (δ * Real.sqrt (A * R * δ)) +
          C * (A * δ ^ 2)) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hδ.le)
    _ = 2 * C * Real.sqrt (A * R * δ) + C * A * δ := by
        field_simp
        ring

/-- **HA3's interface (I5)**, `ε`-form (the hypothesis format of `LQGDimension.expectedSupLimit`):
for every `θ > 0`, for all small `δ > 0`, for all `f, g ∈ B̂_R`,
`|δ⁻¹ Λ(ν_{Q_δ(f)} - ν_I, ν_{Q_δ(g)} - ν_I) - gCov f g| ≤ θ`. -/
theorem polygonCovLimit (hd : 0 < d) (n : ℕ) (R : ℝ) :
    ∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0, ∀ f ∈ vertBall (Rd (d - 1)) n R,
      ∀ g ∈ vertBall (Rd (d - 1)) n R,
      |δ⁻¹ * logCov (qMeasure d n δ f) (Upper.segMeasure 0 (e₁ d)) (qMeasure d n δ g)
          (Upper.segMeasure 0 (e₁ d)) - gCov f g| ≤ θ := by
  intro θ hθ
  rcases lt_or_ge R 0 with hR | hR0
  · refine Eventually.of_forall fun δ f hf => ?_
    rw [vertBall_eq_empty_of_neg hR] at hf
    exact absurd hf (notMem_empty f)
  obtain ⟨C, hC0, hC⟩ := abs_polygon_logCov_sub_graph_le (d := d) hd n hR0
  set A := qConst n R with hA
  -- the error term tends to `0`
  have herr : Tendsto (fun δ : ℝ => 2 * C * Real.sqrt (A * R * δ) + C * A * δ) (𝓝[>] 0)
      (𝓝 0) := by
    have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have h1 : Tendsto (fun δ : ℝ => A * R * δ) (𝓝[>] 0) (𝓝 0) := by
      simpa using hid.const_mul (A * R)
    have h2 := ((Real.continuous_sqrt.tendsto 0).comp h1).const_mul (2 * C)
    have h3 : Tendsto (fun δ : ℝ => C * A * δ) (𝓝[>] 0) (𝓝 0) := by
      simpa using hid.const_mul (C * A)
    have := h2.add h3
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero, add_zero] using this
  have hθ2 : 0 < θ / 2 := by positivity
  have hunif := Metric.tendstoUniformlyOn_iff.1 (tendstoUniformlyOn_graph_logCov (d := d) hd n R)
    (θ / 2) hθ2
  filter_upwards [hunif, (tendsto_order.1 herr).2 (θ / 2) hθ2, self_mem_nhdsWithin,
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))) (Iio_mem_nhds (qDelta0_pos n hR0))]
    with δ h1 h2 hδ hδ0 f hf g hg
  have e1 := hC δ hδ (le_of_lt hδ0) f hf g hg
  have e2 := h1 (f, g) ⟨hf, hg⟩
  rw [Real.dist_eq, abs_sub_comm] at e2
  calc |δ⁻¹ * logCov (qMeasure d n δ f) (Upper.segMeasure 0 (e₁ d)) (qMeasure d n δ g)
          (Upper.segMeasure 0 (e₁ d)) - gCov f g|
      ≤ |δ⁻¹ * logCov (qMeasure d n δ f) (Upper.segMeasure 0 (e₁ d)) (qMeasure d n δ g)
            (Upper.segMeasure 0 (e₁ d)) -
          δ⁻¹ * logCov (graphMeasure d δ f) (graphMeasure d δ 0) (graphMeasure d δ g)
            (graphMeasure d δ 0)| +
        |δ⁻¹ * logCov (graphMeasure d δ f) (graphMeasure d δ 0) (graphMeasure d δ g)
            (graphMeasure d δ 0) - gCov f g| := abs_sub_le _ _ _
    _ ≤ θ := by simp only at e2; linarith

/-- **HA3's interface (I5)**, uniform-convergence form. -/
theorem tendstoUniformlyOn_polygon_logCov (hd : 0 < d) (n : ℕ) (R : ℝ) :
    TendstoUniformlyOn (fun δ (p : (ℝ → Rd (d - 1)) × (ℝ → Rd (d - 1))) =>
        δ⁻¹ * logCov (qMeasure d n δ p.1) (Upper.segMeasure 0 (e₁ d)) (qMeasure d n δ p.2)
          (Upper.segMeasure 0 (e₁ d)))
      (fun p => gCov p.1 p.2) (𝓝[>] 0)
      (vertBall (Rd (d - 1)) n R ×ˢ vertBall (Rd (d - 1)) n R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro θ hθ
  filter_upwards [polygonCovLimit (d := d) hd n R (θ / 2) (by positivity)] with δ h p hp
  rw [Real.dist_eq, abs_sub_comm]
  exact (h p.1 hp.1 p.2 hp.2).trans_lt (by linarith)

/-- Below `δ₀(n, R)`, the all-scale covariance of the polygon measures is the log covariance
(3.2). -/
theorem scaleCov_eq_logCov_polygon (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {n : ℕ}
    {R : ℝ} (hR0 : 0 ≤ R) {δ : ℝ} (hδ : 0 < δ) (hδ0 : δ ≤ qDelta0 n R) {f g : ℝ → Rd (d - 1)}
    (hf : f ∈ vertBall (Rd (d - 1)) n R) (hg : g ∈ vertBall (Rd (d - 1)) n R) :
    scaleCov κ (Ioi 0) (qMeasure d n δ f) (Upper.segMeasure 0 (e₁ d)) (qMeasure d n δ g)
      (Upper.segMeasure 0 (e₁ d)) =
    logCov (qMeasure d n δ f) (Upper.segMeasure 0 (e₁ d)) (qMeasure d n δ g)
      (Upper.segMeasure 0 (e₁ d)) := by
  obtain ⟨hpf, hGf, -, hSf⟩ := qPolygon_facts hd hR0 hδ hδ0 hf
  obtain ⟨hpg, hGg, -, hSg⟩ := qPolygon_facts hd hR0 hδ hδ0 hg
  have hI := (graphMeasure_growthBound (δ := δ) hd (f := 0) measurable_const).mono_const one_pos
    (show (2 : ℝ) ≤ 4 by norm_num)
  have hIs : ∀ᵐ z ∂(graphMeasure d δ 0), ‖z‖ ≤ 2 := by
    filter_upwards [ae_norm_le_graphMeasure (δ := δ) hd (f := 0) measurable_const
      (M := 0) fun x _ => by simp] with z hz
    linarith
  rw [graphMeasure_zero] at hI hIs
  exact (scaleCov_eq_logCov_of_growthBound hκ one_pos one_pos hGf hI hGg hI hSf hIs hSg hIs).2.2

/-- **HA3's interface (I5)** for the all-scale covariance of an admissible kernel `κ`. -/
theorem polygonCovLimit_scaleCov (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) (n : ℕ)
    (R : ℝ) :
    ∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0, ∀ f ∈ vertBall (Rd (d - 1)) n R,
      ∀ g ∈ vertBall (Rd (d - 1)) n R,
      |δ⁻¹ * scaleCov κ (Ioi 0) (qMeasure d n δ f) (Upper.segMeasure 0 (e₁ d))
          (qMeasure d n δ g) (Upper.segMeasure 0 (e₁ d)) - gCov f g| ≤ θ := by
  intro θ hθ
  rcases lt_or_ge R 0 with hR | hR0
  · refine Eventually.of_forall fun δ f hf => ?_
    rw [vertBall_eq_empty_of_neg hR] at hf
    exact absurd hf (notMem_empty f)
  filter_upwards [polygonCovLimit (d := d) hd n R θ hθ, self_mem_nhdsWithin,
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))) (Iio_mem_nhds (qDelta0_pos n hR0))]
    with δ h hδ hδ0 f hf g hg
  rw [scaleCov_eq_logCov_polygon hd hκ hR0 hδ (le_of_lt hδ0) hf hg]
  exact h f hf g hg

/-- The polygon covariances `δ⁻¹ Λ(ν_{Q_δ(f)} - ν_I, ν_{Q_δ(g)} - ν_I)` are PSD on finite
subfamilies of `B̂_R` for `0 < δ ≤ δ₀(n, R)` (HA3 D5, Step 1d, first hypothesis of
`expectedSupLimit`). -/
theorem psdOn_polygon_logCov (hd : 0 < d) {n : ℕ} {R : ℝ} (hR0 : 0 ≤ R) {δ : ℝ} (hδ : 0 < δ)
    (hδ0 : δ ≤ qDelta0 n R) (F : Finset (ℝ → Rd (d - 1)))
    (hF : ↑F ⊆ vertBall (Rd (d - 1)) n R) :
    PSDOn F (fun f g => δ⁻¹ * logCov (qMeasure d n δ f) (Upper.segMeasure 0 (e₁ d))
      (qMeasure d n δ g) (Upper.segMeasure 0 (e₁ d))) := by
  obtain ⟨κ, hκ⟩ := exists_isLFPPKernel d
  have h := Var.psdOn_const_mul (psdOn_scaleCov (κ := κ) (Ioi 0) F
    (fun f => qMeasure d n δ f) (fun _ => Upper.segMeasure 0 (e₁ d))) (inv_nonneg.2 hδ.le)
  refine psdOn_congr (fun f hf g hg => ?_) h
  rw [scaleCov_eq_logCov_polygon hd hκ hR0 hδ hδ0 (hF hf) (hF hg)]

end HigherDimLFPP
