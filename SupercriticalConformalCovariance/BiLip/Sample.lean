import SupercriticalConformalCovariance.BiLip.Round

/-!
# Lemma 2.1, steps 5–6 for one sample, both directions

Paper l. 139–148. One sample: the source metric `D₁ = D_h` (`d = D_h(·,·;U) = pathInf D₁ U`), the target
whole-plane metric `D₀ = D_{g₀}` with the domain correction `k` (`e = eT D₀ ξ k φ`), the conformal map `φ`, and
good covers along a deterministic `ε_j → 0`. With `ρ = r |φ′(z)|`, the good events of (4) are
* `goodPair₁` (`e ≤ K d`): `e(around A_{9ρ/8, 15ρ/8}(φ z)) < K · D_h(across A_{r/2,r}(z))`;
* `goodPair₂` (`d ≤ K e`): `D_h(around A_{r,2r}(z)) < K · e(across cl A_{5ρ/8, 7ρ/8}(φ z))`.
The target annuli are round in the target coordinates; the geometry `GeomGood` (Koebe, uniform on compact
sets, `geomGood_on_compact`) makes them comparable with the source annuli at small scales (`Round.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalLQGUniqueness (LSCMetric weylScale)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier (forget)
open SupercriticalConformalCovariance.Cover (coverFamily)

/-- the good pair of `e ≤ K d` -/
def goodPair₁ (D₁ D₀ : LSCMetric) (ξ : ℝ) {V : Set ℂ} (k : C(V, ℝ)) (φ : ℂ → ℂ) (K : ℝ≥0∞)
    (z : ℂ) (r : ℝ) : Prop :=
  tAround D₀ ξ k (φ z) (9 / 8 * (r * ‖deriv φ z‖)) (15 / 8 * (r * ‖deriv φ z‖)) <
    K * acrAt D₁ z r

/-- the good pair of `d ≤ K e` -/
def goodPair₂ (D₁ D₀ : LSCMetric) (ξ : ℝ) {V : Set ℂ} (k : C(V, ℝ)) (φ : ℂ → ℂ) (K : ℝ≥0∞)
    (z : ℂ) (r : ℝ) : Prop :=
  aroundHit D₁ z r < K * tAcr D₀ ξ k (φ z) (5 / 8 * (r * ‖deriv φ z‖)) (7 / 8 * (r * ‖deriv φ z‖))

/-- **Lemma 2.1, `e ≤ K d`, one sample.** -/
theorem sample_e_le (ξ : ℝ) (hξ : 0 ≤ ξ) {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {φ : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) (hφU : MapsTo φ U V)
    (hψc : ContinuousOn (Function.invFunOn φ U) (φ '' U))
    (D₁ : LSCMetric) (hf₁ : Continuous (forget D₁))
    (D₀ : LSCMetric) (hf₀ : Continuous (forget D₀)) (hL₀ : D₀.IsLengthSpace)
    (E : C(ℂ, ℝ) → LSCMetric) (hE : ∀ F q, E F q = weylScale ξ F D₀ q) (k : C(V, ℝ))
    {K : ℝ≥0∞} (hK0 : K ≠ 0) (hKtop : K ≠ ∞)
    (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hcover : ∀ L : Set ℂ, IsCompact L → L ⊆ U → ∀ᶠ j in atTop, ∀ x ∈ L,
      ∃ zr ∈ coverFamily L (ε j), x ∈ ball zr.1 (zr.2 / 2) ∧ goodPair₁ D₁ D₀ ξ k φ K zr.1 zr.2) :
    ∀ u ∈ U, ∀ v ∈ U, eT D₀ ξ k φ u v ≤ K * pathInf D₁ U u v := by
  have hφc : ContinuousOn φ U := hφd.continuousOn
  refine le_of_goodCovers hU (fun P a b => D₁.IsCurve P a b) (fun P a b => D₁.len P a b)
    (fun _ _ _ hP => hP.1) (fun _ _ _ hP => curve_continuousOn hf₁ hP)
    (fun P _ _ _ s t u _ hst htu _ => len_add3 D₁ P s t u hst htu)
    (pathInf D₁ U)
    (fun u _ v _ hfin δ hδ => exists_curve_le_pathInf_add D₁ U u v hfin δ hδ)
    (acrAt D₁) (eT D₀ ξ k φ) (confT D₀ ξ k φ)
    (fun _ hC hCU => isPMetricOn_confT k hξ hf₀ hL₀ hV E hE hφc hφU hC hCU)
    (fun _ _ _ _ hCC' _ x _ y _ => confT_anti k hCC' x y)
    (fun _ hC hCU x hx y hy xs ys hxs hys hxt hyt M hM =>
      confT_lsc_seq k hξ hf₀ hL₀ hV E hE hφc hφU hC hCU x hx y hy xs ys hxs hys hxt hyt M hM)
    (fun _ _ hCU x _ y _ => eT_le_confT k hf₀ hV hCU hφU x y)
    (goodPair₁ D₁ D₀ ξ k φ K) hK0 hKtop ?_ ε hεpos hεlim hcover
  intro L hL hLU
  obtain ⟨r₁, hr₁, hgeom⟩ := geomGood_on_compact hU hφd hinj hL hLU (by norm_num : (0 : ℝ) < 1 / 32)
  refine ⟨r₁, hr₁, fun z hz r hr hgood => ⟨?_, ?_, ?_⟩⟩
  · have hG := hgeom z hz r hr
    exact (closedBall_subset_closedBall (by linarith [hr.1])).trans hG.2.2.1
  · exact isGoodLoop_of_tAround_lt hf₀ k (hgeom z hz r hr) le_rfl hφc hinj hψc hgood
  · intro P a b hP τ t haτ hτt htb h1 h2
    exact acrAt_le_len hf₁ hP z r τ t haτ hτt htb h1 h2

/-- **Lemma 2.1, `d ≤ K e`, one sample** ("interchanging the two metrics gives `d ≤ C0 e`", l. 147). -/
theorem sample_d_le (ξ : ℝ) {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {φ : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ U) (hinj : InjOn φ U)
    {ψ : ℂ → ℂ} (hψV : MapsTo ψ V U) (hψc : ContinuousOn ψ V) (hφψ : ∀ y ∈ V, φ (ψ y) = y)
    (hψφ : ∀ x ∈ U, ψ (φ x) = x)
    (D₁ : LSCMetric) (hf₁ : Continuous (forget D₁))
    (D₀ : LSCMetric) (hf₀ : Continuous (forget D₀)) (k : C(V, ℝ))
    {K : ℝ≥0∞} (hK0 : K ≠ 0) (hKtop : K ≠ ∞)
    (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hcover : ∀ L : Set ℂ, IsCompact L → L ⊆ U → ∀ᶠ j in atTop, ∀ x ∈ L,
      ∃ zr ∈ coverFamily L (ε j), x ∈ ball zr.1 (zr.2 / 2) ∧ goodPair₂ D₁ D₀ ξ k φ K zr.1 zr.2) :
    ∀ u ∈ U, ∀ v ∈ U, pathInf D₁ U u v ≤ K * eT D₀ ξ k φ u v := by
  have hφc : ContinuousOn φ U := hφd.continuousOn
  refine le_of_goodCovers hU (AdmT D₀ φ U) (lenT D₀ ξ k φ)
    (fun _ _ _ hP => hP.1) (fun _ _ _ hP => hP.2.1)
    (fun P _ _ _ s t u _ hst htu _ => lenT_add k P s t u hst htu)
    (eT D₀ ξ k φ)
    (fun u hu v hv hfin δ hδ => exists_admT_le k hf₀ hV hψV hψc hφψ hψφ u hu v hv hfin δ hδ)
    (fun z r => tAcr D₀ ξ k (φ z) (5 / 8 * (r * ‖deriv φ z‖)) (7 / 8 * (r * ‖deriv φ z‖)))
    (pathInf D₁ U) (fun C => pathInf D₁ C)
    (fun C _ _ => isPMetricOn_pathInf D₁ C)
    (fun _ _ _ _ hCC' _ x _ y _ => pathInf_mono D₁ hCC' x y)
    (fun _ hC _ x hx y hy xs ys hxs hys hxt hyt M hM =>
      pathInf_lsc_seq D₁ hC x hx y hy xs ys hxs hys hxt hyt M hM)
    (fun _ _ hCU x _ y _ => pathInf_mono D₁ hCU x y)
    (goodPair₂ D₁ D₀ ξ k φ K) hK0 hKtop ?_ ε hεpos hεlim hcover
  intro L hL hLU
  obtain ⟨r₁, hr₁, hgeom⟩ := geomGood_on_compact hU hφd hinj hL hLU (by norm_num : (0 : ℝ) < 1 / 32)
  refine ⟨r₁, hr₁, fun z hz r hr hgood => ⟨?_, ?_, ?_⟩⟩
  · have hG := hgeom z hz r hr
    exact (closedBall_subset_closedBall (by linarith [hr.1])).trans hG.2.2.1
  · exact isGoodLoop_of_aroundHit_lt hf₁ z hgood
  · intro P a b hP τ t haτ hτt htb h1 h2
    exact tAcr_le_lenT k (hgeom z hz r hr) le_rfl hφc hP τ t haτ hτt htb h1 h2

end SupercriticalConformalCovariance.BiLip
