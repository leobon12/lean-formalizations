import HigherDimLQGMetric.Sec4.LfppScaleProb
import HigherDimLQGMetric.Sharp.TightWeak
import HigherDimLQGMetric.DGZ.FunctionalsBounds
import HigherDimLQGMetric.Main.Cor104

/-!
# [1] (4.5) and Lemma 4.3 (packet L9b; MA6 P2, P9)

The good shell event `E^ε_r(u; C)` of [1] (4.5), with the localized field `ĥ*_ε` of [1] (4.1):

1. `D_h(∂B_{r/2}(u), ∂B_r(u)) ≥ C⁻¹ c_r e^{ξ h_r(u)}` (across distance of the weak metric);
2. `sup_{v, v' ∈ ∂B_r(u)} D_h(v, v'; A_{r/2,2r}(u)) ≤ C c_r e^{ξ h_r(u)}` (sphere diameter);
3. `D̂^ε_h(∂B_{r/2}(u), ∂B_r(u); A_{r/3,3r}(u)) ≥ C⁻¹ r 𝔞_{ε/r} e^{ξ h_r(u)}`;
4. `sup_{v, v' ∈ ∂B_r(u)} D̂^ε_h(v, v'; A_{r/2,2r}(u)) ≤ C r 𝔞_{ε/r} e^{ξ h_r(u)}`.

(3)–(4) are [1]'s events multiplied by `𝔞_ε`; (3) uses the internal set distance in `A_{r/3,3r}` (which dominates
the global one, and is what the chaining argument needs) so that the event is local (`Lemma43Meas`).

**Lemma 4.3** (`ref1_lemma43`): for every `p < 1` there are `C ≥ 1`, `ε₀ > 0` such that `P[E^ε_r(u; C)] ≥ p` for every
normalized LGF, `ε ∈ (0, ε₀)`, `ε < r ≤ 1` and every centre `u`. (1)–(2) are W1's `scaledAcrossLower`,
`scaledSphereDiamUpper` (MA6 P2 for weak metrics); (3)–(4) are the LFPP bounds of `LfppScaleProb` (MA6 P2 for
the LFPP family, through [1] Lemma 3.3) transferred to `ĥ*_ε` by `ref1_lemma41_uniform` (MA6 P9).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁ lfppDistOn)

variable {d : ℕ}

/-- **The good shell event** `E^ε_r(u; C)` of [1] (4.5) (multiplied by `𝔞_ε` in (3)–(4)) -/
def shellGood (κ : Rd d → ℝ) (ξ : ℝ) (D : DistRd d → ContMetric d) (c : ℝ → ℝ) (ε C : ℝ)
    (u : Rd d) (r : ℝ) (g : DistRd d) : Prop :=
  ENNReal.ofReal (C⁻¹ * c r * Real.exp (ξ * sphereAvg g r u)) ≤ acrossDist (D g) u (r / 2) r ∧
  sphereDiam (D g) u r ≤ ENNReal.ofReal (C * c r * Real.exp (ξ * sphereAvg g r u)) ∧
  C⁻¹ * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg g r u) ≤
    DGZ.lfppSetDist ξ (locField κ ε g) (ann u (r / 3) (3 * r)) (sphere u (r / 2)) (sphere u r) ∧
  DGZ.lfppDiam ξ (locField κ ε g) (sphere u r) (ann u (r / 2) (2 * r)) ≤
    C * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg g r u)

/-- `P E ≥ p` from `P Eᶜ ≤ 1 - p` (outer measure) -/
theorem l9b_ofReal_le_of_compl {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : Set Ω} {p : ℝ} (hp : p ≤ 1)
    (h : P Eᶜ ≤ ENNReal.ofReal (1 - p)) : ENNReal.ofReal p ≤ P E := by
  rcases le_or_gt p 0 with hp0 | hp0
  · rw [ENNReal.ofReal_of_nonpos hp0]
    exact bot_le
  have h1 : (1 : ℝ≥0∞) ≤ P E + P Eᶜ := by
    rw [← measure_univ (μ := P), ← union_compl_self E]
    exact measure_union_le _ _
  have h2 : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
    rw [← ENNReal.ofReal_add hp0.le (by linarith), add_sub_cancel, ENNReal.ofReal_one]
  have h3 : ENNReal.ofReal p + ENNReal.ofReal (1 - p) ≤ P E + ENNReal.ofReal (1 - p) :=
    h2 ▸ h1.trans (add_le_add le_rfl h)
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h3

theorem l9b_unit_sphere_ne {r : ℝ} (hd : 2 ≤ d) (hr : 0 ≤ r) (u : Rd d) :
    (sphere u r).Nonempty := by
  have : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [finrank_euclideanSpace_fin]; omega)
  exact NormedSpace.sphere_nonempty.2 hr

theorem l9b_sphere_subset_ann {u : Rd d} {r a b : ℝ} (ha : a < r) (hb : r < b) :
    sphere u r ⊆ ann u a b := by
  intro x hx
  have hn : ‖x - u‖ = r := by simpa [mem_sphere, dist_eq_norm] using hx
  exact ⟨by rw [hn]; exact ha, by rw [hn]; exact hb⟩

theorem l9b_ann_subset_closedBall {u : Rd d} {a b R : ℝ} (hb : b ≤ R) :
    ann u a b ⊆ closedBall u R := by
  intro x hx
  rw [mem_closedBall, dist_eq_norm]
  exact (le_of_lt hx.2).trans hb

/-- **[1] Lemma 4.3**, complement form (MA6 P2, P9): `P[E^ε_r(u; C)ᶜ] ≤ 1 - p` (outer measure). -/
theorem ref1_lemma43_compl (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ), DGZ.RealEpsAdapterShape d κ ξ Q)
    (hd : 3 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) (hsub : Real.sqrt (2 * d) < distExp d ξ)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) {p : ℝ} (hp : p < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsNormalizedLGF h P →
      ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ r : ℝ, ε < r → r ≤ 1 → ∀ u : Rd d,
        P {ω | shellGood κ ξ D c ε C u r (h ω)}ᶜ ≤ ENNReal.ofReal (1 - p) := by
  have hd2 : 2 ≤ d := by omega
  have hK := convKernel_contDiff (d := d) (by omega) hκ
  set θ : ℝ≥0∞ := ENNReal.ofReal ((1 - p) / 5) with hθdef
  have hθ : 0 < θ := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨a₁, ha₁, H1⟩ := hD.scaledAcrossLower hd2 hθ
  obtain ⟨C₂, hC₂, H2⟩ := hD.scaledSphereDiamUpper hd2 hθ
  obtain ⟨c₃, hc₃, H3⟩ := l9b_lfpp_across_prob hL6a hB2 hd2 hκ hξ hsub (a := 1 / 2) (b := 1)
    (by norm_num) (by norm_num) hθ
  obtain ⟨C₄, hC₄, H4⟩ := l9b_lfpp_diam_prob hL6a hB2 hd2 hκ hξ hsub hθ
  obtain ⟨ε₁, hε₁, H5⟩ := ref1_lemma41_uniform hd2 hκ (η := 1) one_pos hθ
  obtain ⟨ε₂, hε₂, H6⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (l9b_eventually_locHyp hd2 hκ)
  set E := Real.exp (|ξ|) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set C : ℝ := max (max 1 a₁⁻¹) (max C₂ (max (E / c₃) (E * C₄))) with hCdef
  have hC1 : 1 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC0 : 0 < C := by linarith
  refine ⟨C, hC1, min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro Ω _ P _ h hh ε hε r hεr hr1 u
  have hε0 : 0 < ε := hε.1
  have hr : 0 < r := hε0.trans hεr
  obtain ⟨-, -, hrad, -, -⟩ := H6 ⟨hε0, hε.2.trans_le (min_le_right _ _)⟩
  -- the five bad sets
  let B1 := {ω | acrossDist (weakScaledMetric ξ D c (h ω) hr u (hD.c_pos r hr)) 0 (1 / 2) 1 <
    ENNReal.ofReal a₁}
  let B2 := {ω | ENNReal.ofReal C₂ < sphereDiam
    (weakScaledMetric ξ D c (h ω) hr u (hD.c_pos r hr)) 0 1}
  let B3 := {ω | DGZ.lfppSetDist ξ (convMollify κ ε (h ω)) univ (sphere u (1 / 2 * r))
    (sphere u (1 * r)) < c₃ * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u)}
  let B4 := {ω | C₄ * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) <
    DGZ.lfppDiam ξ (convMollify κ ε (h ω)) (sphere u r) (ann u (r / 2) (2 * r))}
  let B5 := {ω | ∃ x ∈ closedBall u 4,
    1 < |convMollify κ ε (h ω) x - locField κ ε (h ω) x|}
  have hP1 : P B1 < θ := H1 P h hh.1 r hr u
  have hP2 : P B2 < θ := H2 P h hh.1 r hr u
  have hP3 : P B3 < θ := H3 P h hh ε r hε0 hεr u
  have hP4 : P B4 < θ := H4 P h hh ε r hε0 hεr u
  have hP5 : P B5 ≤ θ := H5 P h hh ε ⟨hε0, hε.2.trans_le (min_le_left _ _)⟩ u
  have hsub' : ({ω | shellGood κ ξ D c ε C u r (h ω)}ᶜ : Set Ω) ≤ᵐ[P]
      (B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 : Set Ω) := by
    filter_upwards [l2b_ae_convMollify_continuousOn d hd2 κ hκ P h hh] with ω hcc hbad
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
    have hk : 0 < c r * Real.exp (ξ * hr') := mul_pos (hD.c_pos r hr) (Real.exp_pos _)
    have hk' : (c r)⁻¹ * Real.exp (-ξ * hr') = (c r * Real.exp (ξ * hr'))⁻¹ := by
      rw [mul_inv, neg_mul, Real.exp_neg]
    -- (1)
    have e1 : ENNReal.ofReal (C⁻¹ * c r * Real.exp (ξ * hr')) ≤ acrossDist (D (h ω)) u (r / 2) r := by
      have h1' : ENNReal.ofReal a₁ ≤ ENNReal.ofReal ((c r * Real.exp (ξ * hr'))⁻¹) *
          acrossDist (D (h ω)) u (r / 2) r := by
        have := not_lt.1 (show ¬ (acrossDist (weakScaledMetric ξ D c (h ω) hr u
          (hD.c_pos r hr)) 0 (1 / 2) 1 < ENNReal.ofReal a₁) from h1)
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
          (weakScaledMetric ξ D c (h ω) hr u (hD.c_pos r hr)) 0 1) from h2)
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
      have := l10a_aEps_pos hd2 hκ ξ (div_pos hε0 hr)
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

/-- **[1] Lemma 4.3** (MA6 P2, P9): for every `p < 1` there are `C ≥ 1`, `ε₀ > 0` with `P[E^ε_r(u; C)] ≥ p`
for every normalized LGF, `ε ∈ (0, ε₀)`, `ε < r ≤ 1` and every centre `u`. -/
theorem ref1_lemma43 (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ), DGZ.RealEpsAdapterShape d κ ξ Q)
    (hd : 3 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) (hsub : Real.sqrt (2 * d) < distExp d ξ)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) {p : ℝ} (hp : p < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsNormalizedLGF h P →
      ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ r : ℝ, ε < r → r ≤ 1 → ∀ u : Rd d,
        ENNReal.ofReal p ≤ P {ω | shellGood κ ξ D c ε C u r (h ω)} := by
  obtain ⟨C, hC, ε₀, hε₀, H⟩ := ref1_lemma43_compl hL6a hB2 hd hξ hsub hκ hD hp
  exact ⟨C, hC, ε₀, hε₀, fun P _ h hh ε hε r hεr hr u =>
    l9b_ofReal_le_of_compl hp.le (H P h hh ε hε r hεr hr u)⟩

end HigherDimLQGMetric
