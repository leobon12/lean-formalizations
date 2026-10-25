import SupercriticalLQGUniqueness.B2.PfeWeyl.W3XAllSample
import SupercriticalLQGUniqueness.B2.Iface.FixedFieldWeyl
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableHeatVersion

 







set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open LQGMetric (DistC normGFFLaw heatMollify)

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

theorem exists_fixedFieldWeylAllBounded_of_coupling
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {e : ℕ → Set.Ioi (0 : ℝ)} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L)
    (hAT : Final.CoupledAcrossTails P' L)
    (Φ : DistC → LSCMetric) (hΦ : Measurable Φ)
    (hII : ∀ᵐ ω ∂P', L ω = Φ (h' ω)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Iface.FixedFieldWeylAllBounded ξ m (e ∘ ψ) Φ := by
  let R : ℕ → DistC → LSCMetric := fun n g =>
    normalizedLFPPMetric (ξ : ℝ) (m (e n)) (V (e n) g)
  have hR : ∀ n, Measurable (R n) := by
    intro n
    exact PfeAxioms.measurable_normalizedLFPPMetric_comp (ξ : ℝ) _
      (fun z => (continuous_eval_const z).measurable.comp
        (hB.heat_measurable (e n)))
  have hCoupled : ∀ᵐ ω ∂P',
      Tendsto (fun n => R n (hN n ω)) atTop (𝓝 (Φ (h' ω))) := by
    filter_upwards [hB.metric_tendsto, hII] with ω hc heq
    simpa only [R, ← heq] using hc
  obtain ⟨ψ₀, hψ₀, hBase⟩ :=
    exists_subseq_ae_of_coupled_field_determined P' hB R hR Φ hCoupled
  have hB₀ := hB.comp hψ₀
  have hSA₀ := hSA.comp hψ₀
  obtain ⟨ψ₁, hψ₁, hCount⟩ :=
    exists_fixedField_weyl_countable_of_coupling P' hB₀ hSA₀ hAT Φ hII
      upperShiftFamily upperShiftBound upperShiftFamily_bound
  let ψ : ℕ → ℕ := ψ₀ ∘ ψ₁
  have hψ : StrictMono ψ := hψ₀.comp hψ₁
  refine ⟨ψ, hψ, ?_⟩
  intro Ω _ P _ h hh X hX
  have hGeo := Final.normalizedLimitGeometry_of_coupling hB Φ hII P h hh
  have hTail := Final.normalizedAcrossTails_of_coupling hB hΦ hII hAT P h hh
  have hAcross := ae_acrossUnbounded_of_acrossTail P (fun ω => Φ (h ω)) hTail
  have hBase' : ∀ᵐ ω ∂P,
      Tendsto (fun n => R (ψ n) (h ω)) atTop (𝓝 (Φ (h ω))) :=
    (hBase P h hh).mono fun _ hc => hc.comp hψ₁.tendsto_atTop
  have hCount' := hCount P h hh X hX
  have hXe := PfeAxioms.ae_heat_smoothing_sequence_eq P h hh (e ∘ ψ) X hX
  have hVe : ∀ᵐ ω ∂P, ∀ n z,
      V (e (ψ n)) (h ω) z = heatMollify (e (ψ n) : ℝ) (h ω) z := by
    rw [ae_all_iff]
    intro n
    have h2 := hB.heat_ae (e (ψ n))
    rw [PfeAxioms.normGFFLaw_eq_of_normalized P h hh] at h2
    exact ae_of_ae_map hh.1.measurable.aemeasurable h2
  filter_upwards [hGeo.1, hGeo.2, hAcross, hBase', hCount', hXe, hVe]
    with ω hLen hSmall hAcrossω hBaseω hCountω hXeω hVeω
  have hForget : Continuous (euclidForget (Φ (h ω))) :=
    B2.PfeLocal.continuous_euclidForget_of_small_metric _ hSmall
  have hEq : ∀ n, X (e (ψ n)) ω = V (e (ψ n)) (h ω) := fun n =>
    ContinuousMap.ext fun z => (hXeω n z).trans (hVeω n z).symm
  have hG : Tendsto (fun n => normalizedLFPPMetric (ξ : ℝ)
      (m (e (ψ n))) (X (e (ψ n)) ω)) atTop (𝓝 (Φ (h ω))) := by
    have hseq : (fun n => normalizedLFPPMetric (ξ : ℝ)
        (m (e (ψ n))) (X (e (ψ n)) ω)) =
        fun n => R (ψ n) (h ω) := by
      funext n
      simp only [R, hEq]
    rw [hseq]
    exact hBaseω
  have hC : ∀ j : ℕ, ∃ E : LSCMetric,
      (∀ p, E p = weylScale (ξ : ℝ) (upperShiftFamily j) (Φ (h ω)) p) ∧
      Tendsto (fun n => normalizedLFPPMetric (ξ : ℝ) (m (e (ψ n)))
        (X (e (ψ n)) ω + LQGMetric.LFPP.mollCont (e (ψ n) : ℝ)
          (e (ψ n)).property.ne' (upperShiftFamily j) (upperShiftBound j)
          (upperShiftFamily_bound j))) atTop (𝓝 E) := by
    intro j
    simpa only [ψ, Function.comp_apply] using hCountω j
  exact weyl_all_bounded_of_countable_upper (ξ : ℝ) ξ.property.le
    (fun n => m (e (ψ n))) (fun n => X (e (ψ n)) ω) (Φ (h ω))
    hG hLen hForget hAcrossω (fun n => (e (ψ n) : ℝ))
    (fun n => (e (ψ n)).property.ne')
    (hB.scale_tendsto.comp hψ.tendsto_atTop) hC

end SupercriticalLQGUniqueness.B2.PfeWeyl
