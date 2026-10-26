import HigherDimLFPPAS.Coarse.ShellLFPP
import HigherDimLQGMetric.Sec4.Lemma43
import HigherDimLQGMetric.Sec4.Radii
import HigherDimLQGMetric.Sec4.Asymp

/-!
# Lemma 4.3′: good shell events for signed seeds (packet C27; MA3 P9)

[3] Lemma 4.3 with the LFPP half of the events (4.5) obtained from (1.6) instead of the DGZ tightness (MA3 S2,
Details P9). The event `E^ε_r(u; C)` is the repository's `HigherDimLQGMetric.shellGood` with the sharp scale constants
`c_r = r^{ξQ}`:

1. `D_h(∂B_{r/2}(u), ∂B_r(u)) ≥ C⁻¹ r^{ξQ} e^{ξ h_r(u)}`;
2. `sup_{v, v' ∈ ∂B_r(u)} D_h(v, v'; A_{r/2,2r}(u)) ≤ C r^{ξQ} e^{ξ h_r(u)}`;
3. `D̂^ε_h(∂B_{r/2}(u), ∂B_r(u); A_{r/3,3r}(u)) ≥ C⁻¹ r 𝔞_{ε/r} e^{ξ h_r(u)}`;
4. `sup_{v, v' ∈ ∂B_r(u)} D̂^ε_h(v, v'; A_{r/2,2r}(u)) ≤ C r 𝔞_{ε/r} e^{ξ h_r(u)}`.

`c27_lemma43_compl`: for every `p < 1` there are `C ≥ 1`, `δ₀ > 0`, `ε₀ > 0` with `P[E^ε_r(u; C)ᶜ] ≤ 1 − p` (outer
measure) for every normalized LGF, `ε ∈ (0, ε₀)`, `ε < r ≤ 1` with `ε / r < δ₀`, and every centre `u`.
The proof is the host's `ref1_lemma43_compl` with (1)–(2) from the weak-metric axioms, (3)–(4) from
`c27_lfpp_across_prob`, `c27_lfpp_diam_prob` (i.e. (1.6)), and the transfer `h*_ε → ĥ*_ε` on `B̄_4(u)` from the
sign-free localization `ref1_lemma41_uniform_seed` (no rescaled localization (3.9) is needed: the comparison is made
in the original coordinates, uniformly in the centre).

`c27_lemma43_nIdx` is MA3's shape (`r = 2^{-k}`, `k ∈ N^ε`): there `ε / r ≤ ε^{ζ/2} → 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Coarse

open HigherDimLQGMetric HigherDimLFPPAS.Signed
open HigherDimLFPP (Rd e₁ lfppDistOn)

variable {d : ℕ}

/-- **Lemma 4.3′**, complement form (MA3 P9): `P[E^ε_r(u; C)ᶜ] ≤ 1 - p` (outer measure) for `ε / r < δ₀`. -/
theorem c27_lemma43_compl (hd : 2 ≤ d) {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    (hconv : TendstoInProbLU (normLGFLaw d) (fun δ g => (aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g)
      (𝓝[>] 0) (fun g => (D g).1))
    {p : ℝ} (hp : p < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d), IsNormalizedLGF h P →
      ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ r : ℝ, ε < r → r ≤ 1 → ε / r < δ₀ → ∀ u : Rd d,
        P {ω | shellGood κ ξ D (fun r => r ^ (ξ * Q)) ε C u r (h ω)}ᶜ ≤ ENNReal.ofReal (1 - p) := by
  have hd2 : 2 ≤ d := hd
  have hK := convKernel_contDiff_seed (d := d) (by omega) hκ
  set θ : ℝ≥0∞ := ENNReal.ofReal ((1 - p) / 5) with hθdef
  have hθ : 0 < θ := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨c₃, hc₃, δ₃, hδ₃, H3⟩ := c27_lfpp_across_prob hd2 hD hκ hconv (a := 1 / 2) (b := 1)
    (by norm_num) (by norm_num) hθ
  obtain ⟨C₄, hC₄, δ₄, hδ₄, H4⟩ := c27_lfpp_diam_prob hd2 hD hκ hconv hθ
  set c : ℝ → ℝ := fun r => r ^ (ξ * Q) with hcdef
  have hDw : IsWeakExpMetric d ξ D c := hD
  obtain ⟨a₁, ha₁, H1⟩ := hDw.scaledAcrossLower hd2 hθ
  obtain ⟨C₂, hC₂, H2⟩ := hDw.scaledSphereDiamUpper hd2 hθ
  obtain ⟨ε₁, hε₁, H5⟩ := ref1_lemma41_uniform_seed hd2 hκ (η := 1) one_pos hθ
  obtain ⟨ε₂, hε₂, H6⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (l9b_eventually_locHyp_seed hd2 hκ)
  set E := Real.exp (|ξ|) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set C : ℝ := max (max 1 a₁⁻¹) (max C₂ (max (E / c₃) (E * C₄))) with hCdef
  have hC1 : 1 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC0 : 0 < C := by linarith
  refine ⟨C, hC1, min δ₃ δ₄, lt_min hδ₃ hδ₄, min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro Ω _ P _ h hh ε hε r hεr hr1 hεrδ u
  have hε0 : 0 < ε := hε.1
  have hr : 0 < r := hε0.trans hεr
  obtain ⟨-, -, hrad, -, -⟩ := H6 ⟨hε0, hε.2.trans_le (min_le_right _ _)⟩
  -- the five bad sets
  let B1 := {ω | acrossDist (weakScaledMetric ξ D c (h ω) hr u (hDw.c_pos r hr)) 0 (1 / 2) 1 <
    ENNReal.ofReal a₁}
  let B2 := {ω | ENNReal.ofReal C₂ < sphereDiam
    (weakScaledMetric ξ D c (h ω) hr u (hDw.c_pos r hr)) 0 1}
  let B3 := {ω | DGZ.lfppSetDist ξ (convMollify κ ε (h ω)) univ (sphere u (1 / 2 * r))
    (sphere u (1 * r)) < c₃ * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u)}
  let B4 := {ω | C₄ * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) <
    DGZ.lfppDiam ξ (convMollify κ ε (h ω)) (sphere u r) (ann u (r / 2) (2 * r))}
  let B5 := {ω | ∃ x ∈ closedBall u 4,
    1 < |convMollify κ ε (h ω) x - locField κ ε (h ω) x|}
  have hP1 : P B1 < θ := H1 P h hh.1 r hr u
  have hP2 : P B2 < θ := H2 P h hh.1 r hr u
  have hP3 : P B3 < θ := H3 P h hh ε r hε0 hr (hεrδ.trans_le (min_le_left _ _)) u
  have hP4 : P B4 < θ := H4 P h hh ε r hε0 hr (hεrδ.trans_le (min_le_right _ _)) u
  have hP5 : P B5 ≤ θ := H5 P h hh ε ⟨hε0, hε.2.trans_le (min_le_left _ _)⟩ u
  have hsub' : ({ω | shellGood κ ξ D c ε C u r (h ω)}ᶜ : Set Ω) ≤ᵐ[P]
      (B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 : Set Ω) := by
    filter_upwards [l2b_ae_convMollify_continuousOn_seed d hd2 κ hκ P h hh] with ω hcc hbad
    have hφc : Continuous (convMollify κ ε (h ω)) := by
      have hc : Continuous fun z : Rd d => (ε, z) := continuous_const.prodMk continuous_id
      have hf := hcc.comp_continuous hc (fun _ => ⟨hε0, mem_univ _⟩)
      simpa only [Function.comp_def] using hf
    have hψc : Continuous (locField κ ε (h ω)) := continuous_locField hK hrad _
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hnot
    apply hbad
    set hr' := sphereAvg (h ω) r u
    have hk : 0 < c r * Real.exp (ξ * hr') := mul_pos (hDw.c_pos r hr) (Real.exp_pos _)
    have hk' : (c r)⁻¹ * Real.exp (-ξ * hr') = (c r * Real.exp (ξ * hr'))⁻¹ := by
      rw [mul_inv, neg_mul, Real.exp_neg]
    -- (1)
    have e1 : ENNReal.ofReal (C⁻¹ * c r * Real.exp (ξ * hr')) ≤ acrossDist (D (h ω)) u (r / 2) r := by
      have h1' : ENNReal.ofReal a₁ ≤ ENNReal.ofReal ((c r * Real.exp (ξ * hr'))⁻¹) *
          acrossDist (D (h ω)) u (r / 2) r := by
        have := not_lt.1 (show ¬ (acrossDist (weakScaledMetric ξ D c (h ω) hr u
          (hDw.c_pos r hr)) 0 (1 / 2) 1 < ENNReal.ofReal a₁) from h1)
        rwa [weakScaledMetric_acrossDist, hk'] at this
      have hCa : C⁻¹ ≤ a₁ := by
        rw [inv_le_comm₀ hC0 ha₁]
        exact (le_max_right _ _).trans (le_max_left _ _)
      calc ENNReal.ofReal (C⁻¹ * c r * Real.exp (ξ * hr'))
          = ENNReal.ofReal (C⁻¹) * ENNReal.ofReal (c r * Real.exp (ξ * hr')) := by
            rw [mul_assoc, ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal a₁ * ENNReal.ofReal (c r * Real.exp (ξ * hr')) := by
            gcongr
        _ ≤ ENNReal.ofReal ((c r * Real.exp (ξ * hr'))⁻¹) * acrossDist (D (h ω)) u (r / 2) r *
            ENNReal.ofReal (c r * Real.exp (ξ * hr')) := by gcongr
        _ = acrossDist (D (h ω)) u (r / 2) r := by
            rw [mul_comm, ← mul_assoc, ← ENNReal.ofReal_mul hk.le, mul_inv_cancel₀ hk.ne',
              ENNReal.ofReal_one, one_mul]
    -- (2)
    have e2 : sphereDiam (D (h ω)) u r ≤ ENNReal.ofReal (C * c r * Real.exp (ξ * hr')) := by
      have h2' : ENNReal.ofReal ((c r * Real.exp (ξ * hr'))⁻¹) * sphereDiam (D (h ω)) u r ≤
          ENNReal.ofReal C₂ := by
        have := not_lt.1 (show ¬ (ENNReal.ofReal C₂ < sphereDiam
          (weakScaledMetric ξ D c (h ω) hr u (hDw.c_pos r hr)) 0 1) from h2)
        rwa [weakScaledMetric_sphereDiam, hk'] at this
      have hCC : C₂ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
      calc sphereDiam (D (h ω)) u r
          = ENNReal.ofReal (c r * Real.exp (ξ * hr')) *
              (ENNReal.ofReal ((c r * Real.exp (ξ * hr'))⁻¹) * sphereDiam (D (h ω)) u r) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hk.le, mul_inv_cancel₀ hk.ne',
              ENNReal.ofReal_one, one_mul]
        _ ≤ ENNReal.ofReal (c r * Real.exp (ξ * hr')) * ENNReal.ofReal C₂ := by gcongr
        _ ≤ ENNReal.ofReal (c r * Real.exp (ξ * hr')) * ENNReal.ofReal C := by gcongr
        _ = ENNReal.ofReal (C * c r * Real.exp (ξ * hr')) := by
            rw [← ENNReal.ofReal_mul hk.le]; ring_nf
    -- the field comparison on `B̄_4(u)`
    have hclose : ∀ x ∈ closedBall u 4,
        |convMollify κ ε (h ω) x - locField κ ε (h ω) x| ≤ 1 := by
      intro x hx
      by_contra hlt
      exact h5 ⟨x, hx, not_le.1 hlt⟩
    set V' := ann u (r / 3) (3 * r)
    set A := ann u (r / 2) (2 * r)
    have hV'B : V' ⊆ closedBall u 4 := l9b_ann_subset_closedBall (by linarith)
    have hAB : A ⊆ closedBall u 4 := l9b_ann_subset_closedBall (by linarith)
    have hS1 : sphere u (r / 2) ⊆ V' := l9b_sphere_subset_ann (by linarith) (by linarith)
    have hS2 : sphere u r ⊆ V' := l9b_sphere_subset_ann (by linarith) (by linarith)
    have hS2A : sphere u r ⊆ A := l9b_sphere_subset_ann (by linarith) (by linarith)
    have hV'o : IsOpen V' := isOpen_ann _ _ _
    have hV'c : IsPreconnected V' := (config_isConnected_ann hd2 u (by positivity)
      (by linarith)).2
    have hAo : IsOpen A := isOpen_ann _ _ _
    have hAc : IsPreconnected A := (config_isConnected_ann hd2 u (by positivity) (by linarith)).2
    have hne1 := l9b_unit_sphere_ne hd2 (by positivity : (0 : ℝ) ≤ r / 2) u
    have hne2 := l9b_unit_sphere_ne hd2 hr.le u
    have hb : 0 ≤ r * aEps κ ξ (ε / r) * Real.exp (ξ * hr') := by
      have := l10a_aEps_pos_seed hd2 hκ ξ (div_pos hε0 hr)
      positivity
    -- (3)
    have e3 : C⁻¹ * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * hr') ≤
        DGZ.lfppSetDist ξ (locField κ ε (h ω)) V' (sphere u (r / 2)) (sphere u r) := by
      have h3' : c₃ * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * hr') ≤
          DGZ.lfppSetDist ξ (convMollify κ ε (h ω)) univ (sphere u (r / 2)) (sphere u r) := by
        have := not_lt.1 (show ¬ (DGZ.lfppSetDist ξ (convMollify κ ε (h ω)) univ
          (sphere u (1 / 2 * r)) (sphere u (1 * r)) < c₃ * (r * aEps κ ξ (ε / r)) *
            Real.exp (ξ * sphereAvg (h ω) r u)) from h3)
        rwa [show 1 / 2 * r = r / 2 by ring, one_mul] at this
      have hmono := DGZ.lfppSetDist_mono_domain (ξ := ξ) (φ := convMollify κ ε (h ω)) hne1 hne2
        (subset_univ V') fun x hx y hy =>
          DGZ.pcwJoined_of_isPreconnected hV'o hV'c (hS1 hx) (hS2 hy)
      have hcmp := DGZ.lfppSetDist_le_exp_mul (ξ := ξ) (A := sphere u (r / 2)) (B := sphere u r)
        hφc hψc (V := V') (M := 1) fun z hz => hclose z (hV'B hz)
      rw [mul_one] at hcmp
      have hCc : E / c₃ ≤ C :=
        (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
      have hCinv : C⁻¹ * E ≤ c₃ := by
        rw [inv_mul_le_iff₀ hC0]
        rw [div_le_iff₀ hc₃] at hCc
        linarith
      have key : E * (C⁻¹ * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * hr')) ≤
          E * DGZ.lfppSetDist ξ (locField κ ε (h ω)) V' (sphere u (r / 2)) (sphere u r) := by
        calc E * (C⁻¹ * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * hr'))
            = (C⁻¹ * E) * (r * aEps κ ξ (ε / r) * Real.exp (ξ * hr')) := by ring
          _ ≤ c₃ * (r * aEps κ ξ (ε / r) * Real.exp (ξ * hr')) := by gcongr
          _ = c₃ * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * hr') := by ring
          _ ≤ _ := h3'.trans (hmono.trans hcmp)
      exact le_of_mul_le_mul_left key hE0
    -- (4)
    have e4 : DGZ.lfppDiam ξ (locField κ ε (h ω)) (sphere u r) A ≤
        C * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * hr') := by
      have h4' : DGZ.lfppDiam ξ (convMollify κ ε (h ω)) (sphere u r) A ≤
          C₄ * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * hr') := not_lt.1 h4
      have hbdd := DGZ.bddAbove_lfppDiam_of_isCompact hAo hAc hφc ξ (isCompact_sphere u r)
        hS2A subset_rfl
      have hcmp := DGZ.lfppDiam_le_exp_mul (ξ := ξ) (U := sphere u r) hψc hφc (V := A) (M := 1)
        (fun z hz => by rw [abs_sub_comm]; exact hclose z (hAB hz)) hbdd
      rw [mul_one] at hcmp
      have hCc : E * C₄ ≤ C :=
        (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
      calc DGZ.lfppDiam ξ (locField κ ε (h ω)) (sphere u r) A
          ≤ E * DGZ.lfppDiam ξ (convMollify κ ε (h ω)) (sphere u r) A := hcmp
        _ ≤ E * (C₄ * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * hr')) := by gcongr
        _ = (E * C₄) * (r * aEps κ ξ (ε / r) * Real.exp (ξ * hr')) := by ring
        _ ≤ C * (r * aEps κ ξ (ε / r) * Real.exp (ξ * hr')) := by gcongr
        _ = C * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * hr') := by ring
    exact ⟨e1, e2, e3, e4⟩
  calc P {ω | shellGood κ ξ D c ε C u r (h ω)}ᶜ ≤ P (B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5) :=
        measure_mono_ae hsub'
    _ ≤ P B1 + P B2 + P B3 + P B4 + P B5 := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ θ + θ + θ + θ + θ :=
        add_le_add (add_le_add (add_le_add (add_le_add hP1.le hP2.le) hP3.le) hP4.le) hP5
    _ = ENNReal.ofReal (1 - p) := by
        have ha : 0 ≤ (1 - p) / 5 := div_nonneg (by linarith) (by norm_num)
        rw [hθdef, ← ENNReal.ofReal_add ha ha, ← ENNReal.ofReal_add (by linarith) ha,
          ← ENNReal.ofReal_add (by linarith) ha, ← ENNReal.ofReal_add (by linarith) ha]
        congr 1
        ring

/-- **Lemma 4.3′** (MA3 P9): for every `p < 1` there are `C ≥ 1`, `δ₀ > 0`, `ε₀ > 0` with `P[E^ε_r(u; C)] ≥ p` for
every normalized LGF, `ε ∈ (0, ε₀)`, `ε < r ≤ 1` with `ε / r < δ₀`, and every centre `u`. -/
theorem c27_lemma43 (hd : 2 ≤ d) {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    (hconv : TendstoInProbLU (normLGFLaw d) (fun δ g => (aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g)
      (𝓝[>] 0) (fun g => (D g).1))
    {p : ℝ} (hp : p < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d), IsNormalizedLGF h P →
      ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ r : ℝ, ε < r → r ≤ 1 → ε / r < δ₀ → ∀ u : Rd d,
        ENNReal.ofReal p ≤ P {ω | shellGood κ ξ D (fun r => r ^ (ξ * Q)) ε C u r (h ω)} := by
  obtain ⟨C, hC, δ₀, hδ₀, ε₀, hε₀, H⟩ := c27_lemma43_compl hd hD hκ hconv hp
  exact ⟨C, hC, δ₀, hδ₀, ε₀, hε₀, fun P _ h hh ε hε r hεr hr hεrδ u =>
    l9b_ofReal_le_of_compl hp.le (H P h hh ε hε r hεr hr hεrδ u)⟩

/-- For `ζ > 0` and `δ₀ > 0`, eventually `ε / r < δ₀` for every `r ≥ ε^{1-ζ/2}` (so `ε / r ≤ ε^{ζ/2}`). -/
theorem c27_eventually_ratio_lt {ζ : ℝ} (hζ : 0 < ζ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ r : ℝ, ε ^ (1 - ζ / 2) ≤ r → ε / r < δ₀ := by
  have hrpow : Tendsto (fun ε : ℝ => ε ^ (ζ / 2)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const (0 : ℝ) (ζ / 2) (Or.inr (by positivity))).tendsto
    rw [Real.zero_rpow (by positivity)] at h
    exact h.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hrpow.eventually (gt_mem_nhds hδ₀)] with ε hε hsmall r hr
  have hε0 : 0 < ε := hε
  have hpos : 0 < ε ^ (1 - ζ / 2) := Real.rpow_pos_of_pos hε0 _
  have hsplit : ε = ε ^ (1 - ζ / 2) * ε ^ (ζ / 2) := by
    rw [← Real.rpow_add hε0, show 1 - ζ / 2 + ζ / 2 = 1 by ring, Real.rpow_one]
  calc ε / r ≤ ε / ε ^ (1 - ζ / 2) := div_le_div_of_nonneg_left hε0.le hpos hr
    _ = ε ^ (ζ / 2) := by
        rw [div_eq_iff hpos.ne', mul_comm]
        exact hsplit
    _ < δ₀ := hsmall

/-- **Lemma 4.3′**, MA3's shape (radii `2^{-k}`, `k ∈ N^ε`): for `ζ ∈ (0,1)` and `p < 1` there are `C ≥ 1` and
`ε₀ > 0` with `P[E^ε_{2^{-k}}(u; C)] ≥ p` for every normalized LGF, `ε ∈ (0, ε₀)`, `k ∈ N^ε` and centre `u`. -/
theorem c27_lemma43_nIdx (hd : 2 ≤ d) {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    (hconv : TendstoInProbLU (normLGFLaw d) (fun δ g => (aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g)
      (𝓝[>] 0) (fun g => (D g).1))
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {p : ℝ} (hp : p < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d), IsNormalizedLGF h P →
      ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ k ∈ nIdx ζ ε, ∀ u : Rd d,
        ENNReal.ofReal p ≤ P {ω | shellGood κ ξ D (fun r => r ^ (ξ * Q)) ε C u (dyad k) (h ω)} := by
  obtain ⟨C, hC, δ₀, hδ₀, ε₀, hε₀, H⟩ := c27_lemma43 hd hD hκ hconv hp
  have hev := (c27_eventually_ratio_lt hζ0 hδ₀).and ((l9b_eventually_mesh hζ0 1).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)))
  obtain ⟨ε₁, hε₁, H1⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨C, hC, min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
  intro Ω _ P _ h hh ε hε k hk u
  obtain ⟨hratio, hmesh, hε01⟩ := H1 ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩
  have hr := le_dyad_of_mem_nIdx hε.1 hε01.2.le hζ1 hk
  refine H P h hh ε ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩ (dyad k) ?_ (dyad_le_one k)
    (hratio _ hr) u
  have : 1 * ε < ε ^ (1 - ζ / 2) := hmesh
  linarith

end HigherDimLFPPAS.Coarse
