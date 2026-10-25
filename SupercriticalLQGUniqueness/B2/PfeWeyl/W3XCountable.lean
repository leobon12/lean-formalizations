import SupercriticalLQGUniqueness.B2.PfeWeyl.W3XCoupled
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3XTransfer
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableHeatVersion
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteMeasurable

 











set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open LQGMetric (DistC normGFFLaw heatMollify)

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

theorem exists_fixedField_weyl_countable_of_coupling
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
    (Φ : DistC → LSCMetric) (hII : ∀ᵐ ω ∂P', L ω = Φ (h' ω))
    (f : ℕ → C(ℂ, ℝ)) (M : ℕ → ℝ) (hM : ∀ j z, |f j z| ≤ M j) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
          (∀ δ, IsHeatSmoothing P h δ (X δ)) →
          ∀ᵐ ω ∂P, ∀ j : ℕ,
            ∃ E : LSCMetric, (∀ p, E p = weylScale (ξ : ℝ) (f j) (Φ (h ω)) p) ∧
              Tendsto (fun n => normalizedLFPPMetric (ξ : ℝ) (m (e (ψ n)))
                (X (e (ψ n)) ω + LQGMetric.LFPP.mollCont (e (ψ n) : ℝ)
                  (e (ψ n)).property.ne' (f j) (M j) (hM j))) atTop (𝓝 E) := by
  classical
  letI : IsProbabilityMeasure normGFFLaw := PfeAxioms.normalized_canonical_model.1
  let R : ℕ → DistC → (ℕ → LSCMetric) := fun n g j =>
    normalizedLFPPMetric (ξ : ℝ) (m (e n))
      (V (e n) g + LQGMetric.LFPP.mollCont (e n : ℝ) (e n).property.ne'
        (f j) (M j) (hM j))
  have hR : ∀ n, Measurable (R n) := by
    intro n
    refine Measurable.of_eval fun j => ?_
    exact PfeAxioms.measurable_normalizedLFPPMetric_comp (ξ : ℝ) _
      (fun z => ((continuous_eval_const z).measurable.comp (hB.heat_measurable (e n))).add
        measurable_const)
  let F : DistC → (ℕ → LSCMetric) := fun g j =>
    if h : ∃ E : LSCMetric, ∀ p, E p = weylScale (ξ : ℝ) (f j) (Φ g) p then
      Classical.choose h else Φ g
  have hcoupled : ∀ᵐ ω ∂P', Tendsto (fun n => R n (hN n ω)) atTop (𝓝 (F (h' ω))) := by
    filter_upwards [ae_weyl_scaling_coupled_of_identification P' hB hSA hAT Φ hII]
      with ω hw
    refine tendsto_pi_nhds.2 fun j => ?_
    obtain ⟨E, hE, hconv⟩ := hw (f j) (M j) (hM j)
    have hex : ∃ E : LSCMetric, ∀ p, E p = weylScale (ξ : ℝ) (f j) (Φ (h' ω)) p :=
      ⟨E, hE⟩
    have hFE : F (h' ω) j = E := by
      simp only [F, dif_pos hex]
      apply LSCMetric.ext
      intro p
      exact (Classical.choose_spec hex p).trans (hE p).symm
    rw [hFE]
    exact hconv
  obtain ⟨ψ, hψ, hfixed⟩ :=
    exists_subseq_ae_of_coupled_field_determined P' hB R hR F hcoupled
  refine ⟨ψ, hψ, ?_⟩
  intro Ω _ P _ h hh X hX
  have hLaw : P.map h = P'.map h' :=
    (PfeAxioms.normGFFLaw_eq_of_normalized P h hh).symm.trans
      (PfeAxioms.normGFFLaw_eq_of_normalized P' h' hB.limit_field)
  have hSource : ∀ᵐ ω ∂P', ∀ j,
      ∃ E : LSCMetric, ∀ p, E p = weylScale (ξ : ℝ) (f j) (Φ (h' ω)) p := by
    filter_upwards [ae_weyl_scaling_coupled_of_identification P' hB hSA hAT Φ hII]
      with ω hw j
    obtain ⟨E, hE, -⟩ := hw (f j) (M j) (hM j)
    exact ⟨E, hE⟩
  have hGood : ∀ᵐ ω ∂P, ∀ j,
      ∃ E : LSCMetric, ∀ p, E p = weylScale (ξ : ℝ) (f j) (Φ (h ω)) p :=
    PfeAxioms.ae_field_property_of_standardBorel_coupling P P' h h'
      hh.1.measurable hB.limit_field.1.measurable hLaw
      (fun g => ∀ j, ∃ E : LSCMetric,
        ∀ p, E p = weylScale (ξ : ℝ) (f j) (Φ g) p) hSource
  have hConv := hfixed P h hh
  have hXe := PfeAxioms.ae_heat_smoothing_sequence_eq P h hh (e ∘ ψ) X hX
  have hVe : ∀ᵐ ω ∂P, ∀ n z,
      V (e (ψ n)) (h ω) z = heatMollify (e (ψ n) : ℝ) (h ω) z := by
    rw [ae_all_iff]
    intro n
    have h2 := hB.heat_ae (e (ψ n))
    rw [PfeAxioms.normGFFLaw_eq_of_normalized P h hh] at h2
    exact ae_of_ae_map hh.1.measurable.aemeasurable h2
  filter_upwards [hGood, hConv, hXe, hVe] with ω hg hc hxe hve j
  obtain ⟨E, hE⟩ := hg j
  have hex : ∃ E : LSCMetric, ∀ p, E p = weylScale (ξ : ℝ) (f j) (Φ (h ω)) p :=
    ⟨E, hE⟩
  have hFE : F (h ω) j = E := by
    simp only [F, dif_pos hex]
    apply LSCMetric.ext
    intro p
    exact (Classical.choose_spec hex p).trans (hE p).symm
  have heq : ∀ n, X (e (ψ n)) ω = V (e (ψ n)) (h ω) := fun n =>
    ContinuousMap.ext fun z => (hxe n z).trans (hve n z).symm
  refine ⟨E, hE, ?_⟩
  have hcj := (tendsto_pi_nhds.1 hc) j
  rw [hFE] at hcj
  simpa only [R, heq] using hcj

end SupercriticalLQGUniqueness.B2.PfeWeyl
