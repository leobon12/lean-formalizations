import QuantumZipper.Proofs.Section5.TVLocal
import Mathlib.Probability.Independence.Basic

/-!
# N2-HEART, step H4: TV of an independent mixture

Task N2-HEART. Abstract mixing bound used for the heart of the D3⁺(i) zoom
(Duplantier–Miller–Sheffield arXiv:1409.7055, proof of Prop. 4.7(ii), p. 78: the lateral part is
independent of the radial part and unaffected by the rescaling, so the field law is the mixture of
the lateral law over the radial law).

`tvDist_indep_mix_le`: if `Y ⊥ R` under `P` and `Y'' ⊥ R''` under `P''`, then for measurable
`F`, `F''`, `π`,
`TV(law F(Y,R), law F''(Y'',R'')) ≤ ∫⁻ δ d(law R) + TV(π_* law R, law R'')`, where `δ t` bounds
`TV(law F(Y,t), law F''(Y'', π t))` for every fixed radial value `t` (`δ` need not be measurable).

Own elementary argument (the standard "TV of mixtures ≤ average TV of the components + TV of the
mixing laws", cf. Levin–Peres–Wilmer, *Markov Chains and Mixing Times*, §4.1; here written out with
Tonelli on the product law given by independence and the bounded duality
`TV.lintegral_le_lintegral_add_tvDist`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- Two-sided set bounds give a TV bound. -/
theorem tvDist_le_of_forall_le {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {c : ℝ≥0∞}
    (h1 : ∀ s, MeasurableSet s → μ s ≤ ν s + c) (h2 : ∀ s, MeasurableSet s → ν s ≤ μ s + c) :
    TV.tvDist μ ν ≤ c := by
  unfold TV.tvDist
  exact iSup₂_le fun s hs => sup_le (tsub_le_iff_left.2 (h1 s hs)) (tsub_le_iff_left.2 (h2 s hs))

/-- Real-valued uniform set bounds give a TV bound (probability measures). -/
theorem tvDist_le_ofReal_of_abs {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {c : ℝ}
    (h : ∀ s, MeasurableSet s → |(μ s).toReal - (ν s).toReal| ≤ c) :
    TV.tvDist μ ν ≤ ENNReal.ofReal c := by
  have hc : 0 ≤ c := (abs_nonneg _).trans (h ∅ MeasurableSet.empty)
  have key : ∀ (a b : Measure α) [IsProbabilityMeasure a] [IsProbabilityMeasure b] (s : Set α),
      (a s).toReal ≤ (b s).toReal + c → a s ≤ b s + ENNReal.ofReal c := by
    intro a b _ _ s hs
    rw [← ENNReal.ofReal_toReal (measure_ne_top a s), ← ENNReal.ofReal_toReal (measure_ne_top b s),
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg hc]
    exact ENNReal.ofReal_le_ofReal hs
  refine tvDist_le_of_forall_le (fun s hs => key μ ν s ?_) (fun s hs => key ν μ s ?_)
  · linarith [le_abs_self ((μ s).toReal - (ν s).toReal), h s hs]
  · linarith [neg_abs_le ((μ s).toReal - (ν s).toReal), h s hs]

/-- **TV of independent mixtures** (step H4 of the heart). -/
theorem tvDist_indep_mix_le {Ω Ω'' Ey Ey' Et Ep β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω''] [MeasurableSpace Ey] [MeasurableSpace Ey'] [MeasurableSpace Et]
    [MeasurableSpace Ep] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P] {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {Y : Ω → Ey} {R : Ω → Et} {Y'' : Ω'' → Ey'} {R'' : Ω'' → Ep}
    (hY : AEMeasurable Y P) (hR : AEMeasurable R P) (hY'' : AEMeasurable Y'' P'')
    (hR'' : AEMeasurable R'' P'') (hI : IndepFun Y R P) (hI'' : IndepFun Y'' R'' P'')
    {F : Ey × Et → β} {F'' : Ey' × Ep → β} (hF : Measurable F) (hF'' : Measurable F'')
    {π : Et → Ep} (hπ : Measurable π) (δ : Et → ℝ≥0∞)
    (hδ : ∀ t, TV.tvDist ((P.map Y).map fun y => F (y, t))
      ((P''.map Y'').map fun y => F'' (y, π t)) ≤ δ t) :
    TV.tvDist (P.map fun ω => F (Y ω, R ω)) (P''.map fun ω => F'' (Y'' ω, R'' ω)) ≤
      ∫⁻ t, δ t ∂(P.map R) + TV.tvDist ((P.map R).map π) (P''.map R'') := by
  set m := P.map R with hm
  set m₂ := P''.map R'' with hm₂
  set ν := P.map Y with hν
  set ν'' := P''.map Y'' with hν''
  haveI : IsProbabilityMeasure ν'' := by rw [hν'']; infer_instance
  have e1 : P.map (fun ω => F (Y ω, R ω)) = (ν.prod m).map F := by
    rw [hν, hm, ← hI.map_prod_eq_prod_map_map hY hR,
      AEMeasurable.map_map_of_aemeasurable hF.aemeasurable (hY.prodMk hR)]
    rfl
  have e2 : P''.map (fun ω => F'' (Y'' ω, R'' ω)) = (ν''.prod m₂).map F'' := by
    rw [hν'', hm₂, ← hI''.map_prod_eq_prod_map_map hY'' hR'',
      AEMeasurable.map_map_of_aemeasurable hF''.aemeasurable (hY''.prodMk hR'')]
    rfl
  rw [e1, e2]
  -- the slices
  have main : ∀ s, MeasurableSet s →
      ((ν.prod m).map F s ≤ (ν''.prod m₂).map F'' s +
        (∫⁻ t, δ t ∂m + TV.tvDist (m.map π) m₂)) ∧
      ((ν''.prod m₂).map F'' s ≤ (ν.prod m).map F s +
        (∫⁻ t, δ t ∂m + TV.tvDist (m.map π) m₂)) := by
    intro s hs
    have hT : MeasurableSet (F ⁻¹' s) := hF hs
    have hT'' : MeasurableSet (F'' ⁻¹' s) := hF'' hs
    set g₁ : Et → ℝ≥0∞ := fun t => ν ((fun y => (y, t)) ⁻¹' (F ⁻¹' s)) with hg₁
    set g₂ : Ep → ℝ≥0∞ := fun q => ν'' ((fun y => (y, q)) ⁻¹' (F'' ⁻¹' s)) with hg₂
    have hg₁m : Measurable g₁ := measurable_measure_prodMk_right hT
    have hg₂m : Measurable g₂ := measurable_measure_prodMk_right hT''
    have hg₂1 : ∀ q, g₂ q ≤ 1 := fun q => prob_le_one
    have eL : (ν.prod m).map F s = ∫⁻ t, g₁ t ∂m := by
      rw [Measure.map_apply hF hs, Measure.prod_apply_symm hT]
    have eR : (ν''.prod m₂).map F'' s = ∫⁻ q, g₂ q ∂m₂ := by
      rw [Measure.map_apply hF'' hs, Measure.prod_apply_symm hT'']
    have eg₁ : ∀ t, g₁ t = (ν.map fun y => F (y, t)) s := fun t => by
      exact (Measure.map_apply (μ := ν) (f := fun y => F (y, t))
        (hF.comp (measurable_id.prodMk measurable_const)) hs).symm
    have eg₂ : ∀ t, g₂ (π t) = (ν''.map fun y => F'' (y, π t)) s := fun t => by
      exact (Measure.map_apply (μ := ν'') (f := fun y => F'' (y, π t))
        (hF''.comp (measurable_id.prodMk measurable_const)) hs).symm
    have k1 : ∀ t, g₁ t ≤ g₂ (π t) + δ t := fun t => by
      rw [eg₁, eg₂]
      exact tsub_le_iff_left.1 ((TV.le_tvDist hs).trans (hδ t))
    have k2 : ∀ t, g₂ (π t) ≤ g₁ t + δ t := fun t => by
      rw [eg₁, eg₂]
      exact tsub_le_iff_left.1 ((TV.le_tvDist' hs).trans (hδ t))
    have eπ : ∫⁻ t, g₂ (π t) ∂m = ∫⁻ q, g₂ q ∂(m.map π) := (lintegral_map hg₂m hπ).symm
    refine ⟨?_, ?_⟩
    · rw [eL, eR]
      calc ∫⁻ t, g₁ t ∂m ≤ ∫⁻ t, (g₂ (π t) + δ t) ∂m := lintegral_mono k1
        _ = ∫⁻ t, g₂ (π t) ∂m + ∫⁻ t, δ t ∂m := lintegral_add_left (hg₂m.comp hπ) _
        _ ≤ (∫⁻ q, g₂ q ∂m₂ + TV.tvDist (m.map π) m₂) + ∫⁻ t, δ t ∂m := by
            rw [eπ]; gcongr; exact TV.lintegral_le_lintegral_add_tvDist hg₂m hg₂1
        _ = ∫⁻ q, g₂ q ∂m₂ + (∫⁻ t, δ t ∂m + TV.tvDist (m.map π) m₂) := by ring
    · rw [eL, eR]
      calc ∫⁻ q, g₂ q ∂m₂ ≤ ∫⁻ q, g₂ q ∂(m.map π) + TV.tvDist m₂ (m.map π) :=
            TV.lintegral_le_lintegral_add_tvDist hg₂m hg₂1
        _ = ∫⁻ t, g₂ (π t) ∂m + TV.tvDist (m.map π) m₂ := by rw [eπ, TV.tvDist_comm]
        _ ≤ ∫⁻ t, (g₁ t + δ t) ∂m + TV.tvDist (m.map π) m₂ := by gcongr; exact k2 _
        _ = ∫⁻ t, g₁ t ∂m + (∫⁻ t, δ t ∂m + TV.tvDist (m.map π) m₂) := by
            rw [lintegral_add_left hg₁m]; ring
  exact tvDist_le_of_forall_le (fun s hs => (main s hs).1) (fun s hs => (main s hs).2)

end D3Plus
end QuantumZipper
