import QuantumZipper.Proofs.GFF.K3.KernelForm4

/-!
# GFF-K3, node C5′ (partial): the bubble piece, conditionally on BUB-4

Blueprint `blueprint/EXT_PP_BLUEPRINT.md` §B, node **C5′** (revised C5 of
`blueprint/GFF_K3_BLUEPRINT.md` §3): for a bubble `Ω` swallowed at time `τ`, with `t_n ↑ τ`,
`D_n := ℍ \ K_{t_n}` and `φ_n := f_{t_n}`,

`dualNorm_Ω(ρ 1_Ω) = lim_n dualNorm_{D_n}(ρ 1_Ω) = lim_n ∬ ρρ G_ℍ(φ_n x, φ_n y) = ∬ ρρ V`,

the first equality being BUB-4 (the gate lemma), the second C2 at time `t_n`
(`dualNormSq_eq_kerInt`, `KernelForm4.lean`) and the third dominated convergence along the
decreasing kernels `G_ℍ(φ_n x, φ_n y) ↓ V(x, y)` (domain monotonicity of Green's functions;
AD-4's monotone limit).  Source: Sheffield, arXiv:1012.4797, Theorem 1.1 addendum (p. 12), and
Sheffield, *Gaussian free fields for mathematicians* (2007) §2.2.

BUB-4 (`tendsto_dualNormSq_gates`, EXT_PP §B) is not yet in the repository; it enters as the
explicit hypothesis `BUB4Stmt`, which is its exact EXT_PP §B statement.
-/

noncomputable section

open MeasureTheory Set Function Filter Topology
open Classical
open scoped ENNReal

namespace QuantumZipper.K3

/-- The exact statement of **BUB-4** (`tendsto_dualNormSq_gates`, `EXT_PP_BLUEPRINT.md` §B),
taken as a hypothesis until it is proved. -/
def BUB4Stmt : Prop :=
  ∀ {D : ℕ → Set ℂ} {Ω : Set ℂ}, (∀ n, IsOpen (D n)) → (∀ n, D n ⊆ H) →
    IsOpen Ω → (∀ n, Ω ⊆ D n) → ∀ {p : ℂ} {r : ℕ → ℝ}, (∀ n, 0 < r n) →
    Tendsto r atTop (𝓝 0) → (∀ n, frontier Ω ∩ D n ⊆ Metric.closedBall p (r n)) →
    ∀ {d : ℝ}, 0 < d → (∀ n, ∀ s ∈ Set.Ioo (2 * r n) d, ∃ z, ‖z - p‖ = s ∧ z ∉ D n) →
    ∀ {g : ℂ → ℝ≥0∞}, Measurable g → (∃ M < ⊤, ∀ z, g z ≤ M) → (∀ z ∉ Ω, g z = 0) →
    Bornology.IsBounded (Function.support g) →
    Tendsto (fun n => dualNormSq (D n) (zeroSpace (D n)) (volume.withDensity g)) atTop
      (𝓝 (dualNormSq Ω (zeroSpace Ω) (volume.withDensity g)))

/-- **C5′, bubble piece.**  Given the gate geometry of BUB-4 for a bubble `Ω` inside the
decreasing conformal images `D n` of `ℍ`, and kernels `G_ℍ(φ_n x, φ_n y)` decreasing to `V` on
`Ω × Ω`, the dual norm on `Ω` of a bounded density supported in `Ω` is its `V`-energy. -/
theorem dualNormSq_bubble_eq_lintegral (hBUB4 : BUB4Stmt) {D : ℕ → Set ℂ} {φ : ℕ → ℂ → ℂ}
    (hφ : ∀ n, IsConformalOnto (φ n) (D n) H) (hDH : ∀ n, D n ⊆ H) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hΩD : ∀ n, Ω ⊆ D n) {p : ℂ} {r : ℕ → ℝ} (hr0 : ∀ n, 0 < r n)
    (hr : Tendsto r atTop (𝓝 0)) (hgate : ∀ n, frontier Ω ∩ D n ⊆ Metric.closedBall p (r n))
    {d : ℝ} (hd : 0 < d) (hfat : ∀ n, ∀ s ∈ Set.Ioo (2 * r n) d, ∃ z, ‖z - p‖ = s ∧ z ∉ D n)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) (hgM : ∃ M < ⊤, ∀ z, g z ≤ M) (hg0 : ∀ z ∉ Ω, g z = 0)
    (hgb : Bornology.IsBounded (Function.support g))
    {V : ℂ × ℂ → ℝ≥0∞}
    (hanti : ∀ q ∈ Ω ×ˢ Ω, Antitone fun n => ENNReal.ofReal (greenH (φ n q.1) (φ n q.2)))
    (hV : ∀ q ∈ Ω ×ˢ Ω,
      Tendsto (fun n => ENNReal.ofReal (greenH (φ n q.1) (φ n q.2))) atTop (𝓝 (V q))) :
    dualNormSq Ω (zeroSpace Ω) (volume.withDensity g) =
      ∫⁻ q, g q.1 * (g q.2 * V q) ∂((volume : Measure ℂ).prod volume) := by
  obtain ⟨M, hM, hle⟩ := hgM
  obtain ⟨R, hR⟩ := hgb.subset_closedBall 0
  have hu : BddDens g M R := ⟨hg, hM, hle, fun z hz => by by_contra h; exact hz (hR h)⟩
  have hlim := hBUB4 (fun n => (hφ n).isOpen) hDH hΩ hΩD hr0 hr hgate hd hfat hg ⟨M, hM, hle⟩
    hg0 hgb
  -- the sequence is the kernel integral at time `n`
  have hind : ∀ n, (D n).indicator g = g := fun n =>
    indicator_eq_self.2 fun z hz => hΩD n (by by_contra h; exact hz (hg0 z h))
  -- on `Ω × Ω` the integrand is `g g G_ℍ(φ_n, φ_n)`; off it, it vanishes
  have hker : ∀ n q, kerDens (φ n) (D n) g g q =
      g q.1 * (g q.2 * ENNReal.ofReal (greenH (φ n q.1) (φ n q.2))) := by
    intro n q
    unfold kerDens confKer
    rw [hind n]
    by_cases h1 : q.1 ∈ Ω
    · by_cases h2 : q.2 ∈ Ω
      · rw [confMod_eqOn (hΩD n h1), confMod_eqOn (hΩD n h2)]
      · simp [hg0 _ h2]
    · simp [hg0 _ h1]
  have hseq : ∀ n, dualNormSq (D n) (zeroSpace (D n)) (volume.withDensity g) =
      ∫⁻ q, g q.1 * (g q.2 * ENNReal.ofReal (greenH (φ n q.1) (φ n q.2)))
        ∂((volume : Measure ℂ).prod volume) := fun n => by
    rw [dualNormSq_eq_kerInt (hφ n) (hDH n) hu, kerInt]
    exact lintegral_congr fun q => hker n q
  -- dominated convergence along the decreasing kernels
  have hfin0 : ∫⁻ q, g q.1 * (g q.2 * ENNReal.ofReal (greenH (φ 0 q.1) (φ 0 q.2)))
      ∂((volume : Measure ℂ).prod volume) ≠ ⊤ := by
    rw [← hseq 0]; exact (dualNormSq_withDensity_lt_top (hφ 0) (hDH 0) hu).ne
  have hconv := tendsto_lintegral_of_dominated_convergence
    (μ := (volume : Measure ℂ).prod volume) (f := fun q => g q.1 * (g q.2 * V q))
    (fun q => g q.1 * (g q.2 * ENNReal.ofReal (greenH (φ 0 q.1) (φ 0 q.2))))
    (F := fun n q => g q.1 * (g q.2 * ENNReal.ofReal (greenH (φ n q.1) (φ n q.2))))
    (fun n => by
      have h := measurable_kerDens (hφ n) hg hg
      rwa [show kerDens (φ n) (D n) g g = fun q =>
        g q.1 * (g q.2 * ENNReal.ofReal (greenH (φ n q.1) (φ n q.2))) from funext (hker n)] at h)
    (fun n => Eventually.of_forall fun q => by
      by_cases hq : q ∈ Ω ×ˢ Ω
      · exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (hanti q hq (Nat.zero_le n)))
      · rcases not_and_or.1 hq with h | h
        · simp [hg0 _ h]
        · simp [hg0 _ h])
    hfin0
    (Eventually.of_forall fun q => by
      by_cases hq : q ∈ Ω ×ˢ Ω
      · exact ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul (hV q hq)
          (Or.inr (((hle q.2).trans_lt hM).ne))) (Or.inr (((hle q.1).trans_lt hM).ne))
      · rcases not_and_or.1 hq with h | h
        · simp [hg0 _ h]
        · simp [hg0 _ h])
  exact tendsto_nhds_unique (hlim.congr hseq) hconv

end QuantumZipper.K3
