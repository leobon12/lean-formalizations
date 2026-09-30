import QuantumZipper.Proofs.Thm18.ASep4Ident
import QuantumZipper.Proofs.Thm18.ASepWitD

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP4 (step 5): joint continuity of the scale engine's regularized pairings

`continuousOn_Phi_scale`: for a family of fields `x q` (`q = (τ, a, s)`) that are regular with a
witness `Z(s, τ)` jointly continuous in `(s, τ, v, ρ)`, the pairing
`(q, ρ) ↦ ∫ evalReg (x q) (fc(v, 2^{-m} ρ)) dν_q(v)` is continuous on `S × (0, 1]`, where
`ν_q = fc(d, r).map (w ↦ f_τ(a w))` (`nuA0`). Deterministic; the proof is that of
`ae_continuousOn_Phi_rho` (ASepConj1C) with the scale as an extra parameter (dominated convergence
through `fc(d, r)`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace ASep

open RegCont TwoPoint CoordReg RegUnif

/-- **Joint continuity of the scale pairings** (deterministic). -/
theorem continuousOn_Phi_scale {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T T' : ℝ}
    (hT : 0 < T) (hTT : T ≤ T') {d : ℂ} {r : ℝ} (hr : 0 < r) {a₀ a₁ s₀ s₁ : ℝ} (ha₀ : 0 < a₀)
    (hs₀ : 0 < s₀) {S : Set (Fin 3 → ℝ)}
    (hSb : ∀ q ∈ S, Fin.init q 0 ∈ Icc (0 : ℝ) T ∧ Fin.init q 1 ∈ Icc a₀ a₁ ∧
      q (Fin.last 2) ∈ Icc s₀ s₁) {δ : ℝ}
    (hgood : ∀ a ∈ Icc a₀ a₁,
      ∀ w ∈ Metric.cthickening δ (foldH '' Metric.sphere d r) ∩ {w : ℂ | 0 ≤ w.im},
      ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    {Z : ℝ × ℝ → ℂ × ℝ → ℝ}
    (hZc : ContinuousOn (fun q : (ℝ × ℝ) × (ℂ × ℝ) => Z q.1 q.2)
      ((Ioi 0 ×ˢ Icc 0 T') ×ˢ (Hbar ×ˢ Ioi 0)))
    {x : (Fin 3 → ℝ) → FieldSample}
    (hZreg : ∀ q ∈ S, IsRegularWith (x q) (Z (q (Fin.last 2), Fin.init q 0))) (m : ℕ) :
    ContinuousOn (fun z : (Fin 3 → ℝ) × ℝ =>
      ∫ v, evalReg (x z.1) (foldedCircle v (radius m * z.2)) ∂nuA0 W d r (Fin.init z.1))
      (S ×ˢ Ioc 0 1) := by
  have hgood0 := hgood0_of_hgood hgood
  have hsol : ∀ z ∈ scaledSph d r a₀ a₁, ∃ u, IsForwardSol W z T u := by
    rintro _ ⟨q, hq, rfl⟩; exact hgood0 q.1 hq.1 q.2 hq.2
  obtain ⟨mm, c, Rb, g, hm, hc, hlow, hg⟩ := exists_geo_A0 hW hW0 hT.le ha₀ hgood0
  have hrm := radius_pos m
  set σ := foldedCircle d r with hσ
  set S' : Set (Fin 2 → ℝ) := {p | p 0 ∈ Icc (0 : ℝ) T ∧ p 1 ∈ Icc a₀ a₁} with hS'
  have hSb' : ∀ p ∈ S', p 0 ∈ Icc (0 : ℝ) T ∧ p 1 ∈ Icc a₀ a₁ := fun p hp => hp
  have hsrc : ∀ᵐ w ∂σ, w ∈ foldSph d r ∧ w ∈ H ∧ ‖w‖ ≤ ‖d‖ + r := by
    filter_upwards [ae_mem_foldSph d hr.le, foldedCircle_ae_mem_H d hr,
      foldedCircle_ae_norm_le d hr.le] with w h0 h1 h2
    exact ⟨h0, h1, h2⟩
  have hmap : ∀ p ∈ S', σ.map (g p) = nuA0 W d r p :=
    fun p hp => Measure.map_congr (hsrc.mono fun w hw =>
      ((hg p hp.1 hp.2).2.2 w hw.1))
  have hpt : ∀ p ∈ S', ∀ w, w ∈ foldSph d r ∧ w ∈ H ∧ ‖w‖ ≤ ‖d‖ + r →
      g p w = fwdMap W (p 0) ((p 1 : ℂ) * w) ∧ fwdMap W (p 0) ((p 1 : ℂ) * w) ∈ H ∧
        ‖fwdMap W (p 0) ((p 1 : ℂ) * w)‖ ≤ Rb := by
    intro p hp w hw
    have hgp := hg p hp.1 hp.2
    have e := hgp.2.2 w hw.1
    obtain ⟨h1, -, h3⟩ := hgp.2.1 w hw.2.1 hw.2.2
    rw [e] at h1 h3
    exact ⟨e, h1, h3⟩
  have hinit : ∀ q ∈ S, Fin.init q ∈ S' := fun q hq => ⟨(hSb q hq).1, (hSb q hq).2.1⟩
  have hsq : ∀ q ∈ S, 0 < q (Fin.last 2) := fun q hq => hs₀.trans_le (hSb q hq).2.2.1
  set F : (Fin 3 → ℝ) × ℝ → ℂ → ℝ := fun z w =>
    Z (z.1 (Fin.last 2), Fin.init z.1 0)
      (fwdMap W (Fin.init z.1 0) ((Fin.init z.1 1 : ℂ) * w), radius m * z.2) with hF
  have hmem : ∀ q ∈ S, ∀ v ∈ Hbar, ∀ ρ : ℝ, 0 < ρ →
      ((q (Fin.last 2), Fin.init q 0), (v, ρ)) ∈ (Ioi 0 ×ˢ Icc 0 T') ×ˢ (Hbar ×ˢ Ioi 0) :=
    fun q hq v hv ρ hρ => ⟨⟨hsq q hq, (hSb q hq).1.1, (hSb q hq).1.2.trans hTT⟩, hv, hρ⟩
  have heq : EqOn (fun z : (Fin 3 → ℝ) × ℝ =>
      ∫ v, evalReg (x z.1) (foldedCircle v (radius m * z.2)) ∂nuA0 W d r (Fin.init z.1))
      (fun z => ∫ w, F z w ∂σ) (S ×ˢ Ioc 0 1) := by
    rintro ⟨q, ρ⟩ ⟨hq, hρ⟩
    have hρ' : 0 < radius m * ρ := mul_pos hrm hρ.1
    have hp := hinit q hq
    have hgp := hg (Fin.init q) hp.1 hp.2
    have hνH : ∀ᵐ v ∂nuA0 W d r (Fin.init q), v ∈ Hbar := by
      rw [← hmap _ hp]
      exact (ae_map_iff hgp.1.aemeasurable isClosed_Hbar.measurableSet).2
        (hsrc.mono fun w hw => le_of_lt (show 0 < (g (Fin.init q) w).im from
          (hgp.2.1 w hw.2.1 hw.2.2).1))
    have hZs : ContinuousOn (fun v : ℂ =>
        Z (q (Fin.last 2), Fin.init q 0) (v, radius m * ρ)) Hbar :=
      hZc.comp (Continuous.continuousOn (by fun_prop)) fun v hv => hmem q hq v hv _ hρ'
    have hAE : AEStronglyMeasurable (fun v : ℂ =>
        Z (q (Fin.last 2), Fin.init q 0) (v, radius m * ρ)) (σ.map (g (Fin.init q))) := by
      have := hZs.aestronglyMeasurable (μ := σ.map (g (Fin.init q)))
        isClosed_Hbar.measurableSet
      rw [hmap _ hp] at this ⊢
      rwa [Measure.restrict_eq_self_of_ae_mem hνH] at this
    have e1 : ∫ v, evalReg (x q) (foldedCircle v (radius m * ρ)) ∂nuA0 W d r (Fin.init q) =
        ∫ v, Z (q (Fin.last 2), Fin.init q 0) (v, radius m * ρ) ∂nuA0 W d r (Fin.init q) :=
      integral_congr_ae (hνH.mono fun v hv => (hZreg q hq).evalReg_fc_of_mem hv hρ')
    show ∫ v, evalReg (x q) (foldedCircle v (radius m * ρ)) ∂nuA0 W d r (Fin.init q) =
      ∫ w, F (q, ρ) w ∂σ
    rw [e1, ← hmap _ hp, integral_map hgp.1.aemeasurable hAE]
    exact integral_congr_ae (hsrc.mono fun w hw => by
      simp only [hF]; rw [(hpt _ hp w hw).1])
  refine ContinuousOn.congr ?_ heq
  rintro ⟨q, ρ⟩ ⟨hq, hρ⟩
  have hρ0 : 0 < ρ := hρ.1
  set S₁ : Set ((Fin 3 → ℝ) × ℝ) := S ×ˢ Icc (ρ / 2) 1 with hS₁
  have hnhds : S₁ ∈ 𝓝[S ×ˢ Ioc 0 1] (q, ρ) :=
    mem_nhdsWithin.2 ⟨univ ×ˢ Ioi (ρ / 2), isOpen_univ.prod isOpen_Ioi,
      ⟨trivial, show ρ / 2 < ρ by linarith⟩, fun x hx => ⟨hx.2.1, hx.1.2.le, hx.2.2.2⟩⟩
  refine ContinuousWithinAt.mono_of_mem_nhdsWithin ?_ hnhds
  refine ContinuousOn.continuousWithinAt ?_ ⟨hq, by linarith, hρ.2⟩
  set Kc : Set ((ℝ × ℝ) × (ℂ × ℝ)) :=
    (Icc s₀ s₁ ×ˢ Icc 0 T) ×ˢ ((Metric.closedBall (0 : ℂ) Rb ∩ Hbar) ×ˢ
      Icc (radius m * (ρ / 2)) (radius m)) with hKc
  have hKcc : IsCompact Kc :=
    (isCompact_Icc.prod isCompact_Icc).prod
      (((isCompact_closedBall _ _).inter_right isClosed_Hbar).prod isCompact_Icc)
  have hKP : Kc ⊆ (Ioi 0 ×ˢ Icc 0 T') ×ˢ (Hbar ×ˢ Ioi 0) := fun k hk =>
    ⟨⟨hs₀.trans_le hk.1.1.1, hk.1.2.1, hk.1.2.2.trans hTT⟩, hk.2.1.2,
      show (0 : ℝ) < k.2.2 from lt_of_lt_of_le (mul_pos hrm (by linarith)) hk.2.2.1⟩
  obtain ⟨C, hC⟩ := hKcc.exists_bound_of_continuousOn (hZc.mono hKP)
  have hmemK : ∀ z ∈ S₁, ∀ w, w ∈ foldSph d r ∧ w ∈ H ∧ ‖w‖ ≤ ‖d‖ + r →
      ((z.1 (Fin.last 2), Fin.init z.1 0),
        (fwdMap W (Fin.init z.1 0) ((Fin.init z.1 1 : ℂ) * w), radius m * z.2)) ∈ Kc := by
    intro z hz w hw
    obtain ⟨-, h1, h3⟩ := hpt _ (hinit z.1 hz.1) w hw
    refine ⟨⟨(hSb z.1 hz.1).2.2, (hSb z.1 hz.1).1⟩, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
    · rw [Metric.mem_closedBall, dist_zero_right]; exact h3
    · exact (show (0 : ℝ) < (fwdMap W (Fin.init z.1 0) ((Fin.init z.1 1 : ℂ) * w)).im from h1).le
    · exact mul_le_mul_of_nonneg_left hz.2.1 hrm.le
    · have := mul_le_mul_of_nonneg_left hz.2.2 hrm.le
      rwa [mul_one] at this
  refine continuousOn_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const C) ?_
  · intro z hz
    have hp := hinit z.1 hz.1
    have hgp := hg (Fin.init z.1) hp.1 hp.2
    have hρz : 0 < radius m * z.2 := mul_pos hrm (lt_of_lt_of_le (by linarith) hz.2.1)
    have hZs : ContinuousOn (fun v : ℂ =>
        Z (z.1 (Fin.last 2), Fin.init z.1 0) (v, radius m * z.2)) Hbar :=
      hZc.comp (Continuous.continuousOn (by fun_prop)) fun v hv => hmem z.1 hz.1 v hv _ hρz
    have hνH : ∀ᵐ v ∂σ.map (g (Fin.init z.1)), v ∈ Hbar :=
      (ae_map_iff hgp.1.aemeasurable isClosed_Hbar.measurableSet).2
        (hsrc.mono fun w hw => le_of_lt (show 0 < (g (Fin.init z.1) w).im from
          (hgp.2.1 w hw.2.1 hw.2.2).1))
    have hAE : AEStronglyMeasurable (fun v : ℂ =>
        Z (z.1 (Fin.last 2), Fin.init z.1 0) (v, radius m * z.2))
        (σ.map (g (Fin.init z.1))) := by
      have := hZs.aestronglyMeasurable (μ := σ.map (g (Fin.init z.1)))
        isClosed_Hbar.measurableSet
      rwa [Measure.restrict_eq_self_of_ae_mem hνH] at this
    refine (hAE.comp_measurable hgp.1).congr (hsrc.mono fun w hw => ?_)
    show Z _ (g (Fin.init z.1) w, _) = Z _ (fwdMap W (Fin.init z.1 0)
      ((Fin.init z.1 1 : ℂ) * w), _)
    rw [(hpt _ hp w hw).1]
  · intro z hz
    exact hsrc.mono fun w hw => hC _ (hmemK z hz w hw)
  · filter_upwards [hsrc] with w hw
    have hcf := continuousOn_fwdMap_param hW hW0 hT.le hm hsol hlow hSb' hw.1
    have hcf' : ContinuousOn (fun z : (Fin 3 → ℝ) × ℝ =>
        fwdMap W (Fin.init z.1 0) ((Fin.init z.1 1 : ℂ) * w)) S₁ :=
      hcf.comp ((continuous_pi fun i => (continuous_apply _).comp continuous_fst).continuousOn)
        fun z hz => hinit z.1 hz.1
    refine hZc.comp (f := fun z : (Fin 3 → ℝ) × ℝ =>
        ((z.1 (Fin.last 2), Fin.init z.1 0),
          (fwdMap W (Fin.init z.1 0) ((Fin.init z.1 1 : ℂ) * w), radius m * z.2)))
      ((Continuous.continuousOn (by fun_prop)).prodMk
        (hcf'.prodMk (Continuous.continuousOn (by fun_prop))))
      fun z hz => hKP (hmemK z hz w hw)

end ASep
end QuantumZipper
