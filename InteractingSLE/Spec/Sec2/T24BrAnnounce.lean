import InteractingSLE.Spec.Sec2.T24BrDescent
import InteractingSLE.Spec.Coupling.AnnounceLifetime

/-!
# Announcing-time candidates on a probability extension

The candidate stopping times are chosen on the curve space. Their pathwise exhaustion
properties may be checked on an extension: they are measurable conditions after reducing
the time quantifier to a countable dense set. The landed selection theorem then constructs
the announcing sequence on the original space.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec2.T24Bridge

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {Q : Measure Ω'} {π : Ω' → Ω}

/-- Measurable a.s. assertions can be checked on a measure-preserving extension. -/
theorem ae_of_measurable_pullback (hπ : MeasurePreserving π Q P) {p : Ω → Prop}
    (hp : MeasurableSet {ω | p ω}) (h : ∀ᵐ ω ∂Q, p (π ω)) : ∀ᵐ ω ∂P, p ω := by
  rw [← hπ.map_eq]
  exact (ae_map_iff hπ.measurable.aemeasurable hp).2 h

/-- The announcing sequence is selected on the original space, even when candidate
exhaustion is established using an evolution on a probability extension. -/
theorem exists_isAnnouncingSeq_of_pullback_candidates [IsProbabilityMeasure P]
    {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {ζ : Ω → ℝ≥0∞}
    (hπ : MeasurePreserving π Q P) (hζ : Measurable ζ)
    {a : ℕ → ℕ → Ω → WithTop ℝ≥0}
    (ha : ∀ p k, IsStoppingTime 𝓖 (a p k))
    (hmono : ∀ p ω, Monotone fun k => a p k ω)
    (hlt : ∀ᵐ ω ∂Q, ∀ p, Coupling.BddSeq (fun k => a p k ∘ π) ω →
      ∀ k, a p k (π ω) < ζ (π ω))
    (hunif : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ (π ω) → ∃ K : ℕ,
      ∀ p, Coupling.BddSeq (fun k => a p k ∘ π) ω →
        ∀ k, K ≤ k → (t : WithTop ℝ≥0) ≤ a p k (π ω))
    (hcover : ∀ᵐ ω ∂Q, ζ (π ω) ≠ ⊤ → ∃ p, Coupling.BddSeq (fun k => a p k ∘ π) ω) :
    ∃ T : ℕ → Ω → ℝ≥0, Coupling.IsAnnouncingSeq 𝓖 P ζ T ∧ ∀ n ω, T n ω ≤ n := by
  have hb (p : ℕ) : MeasurableSet {ω | Coupling.BddSeq (a p) ω} := by
    simp only [Coupling.BddSeq, ofPred_exists, ofPred_forall]
    exact MeasurableSet.iUnion fun M => MeasurableSet.iInter fun k =>
      measurableSet_le (ha p k).measurable' measurable_const
  have hltm : MeasurableSet {ω | ∀ p, Coupling.BddSeq (a p) ω → ∀ k, a p k ω < ζ ω} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun p => (hb p).imp (by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun k => measurableSet_lt (ha p k).measurable' hζ)
  have hltP := ae_of_measurable_pullback hπ hltm hlt
  have hcoverm : MeasurableSet {ω | ζ ω ≠ ⊤ → ∃ p, Coupling.BddSeq (a p) ω} := by
    apply (measurableSet_eq_fun hζ measurable_const).compl.imp
    simpa only [ofPred_exists] using MeasurableSet.iUnion hb
  have hcoverP := ae_of_measurable_pullback hπ hcoverm hcover
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have : Countable D := hDc.to_subtype
  have hunifP : ∀ᵐ ω ∂P, ∀ d : D, ((d : ℝ≥0) : ℝ≥0∞) < ζ ω → ∃ K : ℕ,
      ∀ p, Coupling.BddSeq (a p) ω → ∀ k, K ≤ k → ((d : ℝ≥0) : WithTop ℝ≥0) ≤ a p k ω := by
    rw [ae_all_iff]
    intro d
    apply ae_of_measurable_pullback hπ
    · apply (measurableSet_lt measurable_const hζ).imp
      simp only [ofPred_exists]
      exact MeasurableSet.iUnion fun K => by
        simp only [ofPred_forall]
        exact MeasurableSet.iInter fun p => (hb p).imp (by
          simp only [ofPred_forall]
          exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _hk =>
            measurableSet_le measurable_const (ha p k).measurable')
    · exact hunif.mono fun ω h => h d
  apply Coupling.exists_isAnnouncingSeq_le_of_candidates ha hmono
  · filter_upwards [hltP] with ω hω p hp k
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt (hω p hp k))
    refine ⟨t, ht.symm, ?_⟩
    have hh := hω p hp k
    rw [← ht] at hh
    exact hh
  · filter_upwards [hunifP] with ω hω t ht
    obtain ⟨u, htu, hu⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    have htu' : t < u := ENNReal.coe_lt_coe.1 htu
    obtain ⟨d, ⟨htd, hdu⟩, hdD⟩ := hDd.inter_open_nonempty (Ioo t u) isOpen_Ioo
      (nonempty_Ioo.2 htu')
    obtain ⟨K, hK⟩ := hω ⟨d, hdD⟩ (lt_trans (by exact_mod_cast hdu) hu)
    exact ⟨K, fun p hp k hk => (WithTop.coe_le_coe.2 htd.le).trans (hK p hp k hk)⟩
  · exact hcoverP

open Coupling

/-- The landed threshold candidates are stopping times in any filtration adapted to
the original coordinates; this does not require a Brownian motion in that filtration. -/
theorem isStoppingTime_candTime_on_good
    {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {G : Set Ω}
    (hWa : AdaptedBefore 𝓖 ζ W) (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i)) (hG : MeasurableSet[𝓖 0] G)
    (hGc : ∀ ω ∈ G, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVLc : ∀ ω ∈ G, ∀ i, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVRc : ∀ ω ∈ G, ∀ i, ContinuousOn (VR i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (p k : ℕ) :
    IsStoppingTime 𝓖 (fun ω => if ω ∈ G then
      candTime ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω) p k else ⊤) := by
  classical
  have hcont : ∀ ω ∈ G, ContinuousOn (fun t => stateAt W VL VR t ω)
      {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGc ω hω).prodMk ((continuousOn_pi.2 (hVLc ω hω)).prodMk (continuousOn_pi.2 (hVRc ω hω)))
  by_cases hc : (Nat.unpair p).1 < nL
  · let j : Fin nL := ⟨(Nat.unpair p).1, hc⟩
    let m := (Nat.unpair p).2
    by_cases hs : (∑ i ∈ Finset.Iic j, ρL i) ≤ -2
    · convert isStoppingTime_hitBelow_state hWa hVLa hVRa hG hcont
        ((continuous_sideVal m j).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
        (1 / ((k : ℝ) + 1)) using 1
      funext ω
      simp only [candTime, hc, ↓reduceDIte, hitL, ← show j = ⟨(Nat.unpair p).1, hc⟩ from rfl,
        hs, ↓reduceIte, stateAt, m]
      rfl
    · simpa only [candTime, hc, ↓reduceDIte, hitL, ← show j = ⟨(Nat.unpair p).1, hc⟩ from rfl,
        hs, ↓reduceIte, ite_self] using
        (isStoppingTime_top' (𝓖 := 𝓖))
  · by_cases hc' : (Nat.unpair p).1 - nL < nR
    · let j : Fin nR := ⟨(Nat.unpair p).1 - nL, hc'⟩
      let m := (Nat.unpair p).2
      by_cases hs : (∑ i ∈ Finset.Iic j, ρR i) ≤ -2
      · convert isStoppingTime_hitBelow_state hWa hVLa hVRa hG hcont
          ((continuous_sideVal m j).comp
            (continuous_fst.neg.prodMk (continuous_snd.comp continuous_snd).neg))
          (1 / ((k : ℝ) + 1)) using 1
        funext ω
        simp only [candTime, hc, hc', ↓reduceDIte, hitL,
          ← show j = ⟨(Nat.unpair p).1 - nL, hc'⟩ from rfl, hs, ↓reduceIte, stateAt, m]
        rfl
      · simpa only [candTime, hc, hc', ↓reduceDIte, hitL,
          ← show j = ⟨(Nat.unpair p).1 - nL, hc'⟩ from rfl, hs, ↓reduceIte, ite_self] using
          (isStoppingTime_top' (𝓖 := 𝓖))
    · simpa only [candTime, hc, hc', ↓reduceDIte, ite_self] using
        (isStoppingTime_top' (𝓖 := 𝓖))

/-- An evolution on an extension announces its lifetime in the original coordinate
filtration. The Brownian motion need not be adapted to the original filtration. -/
theorem exists_isAnnouncingSeq_of_evolution_pullback [IsProbabilityMeasure P]
    {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {𝓕' : Filtration ℝ≥0 mΩ'}
    {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω' → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}
    (hπ : MeasurePreserving π Q P) (hζ : Measurable ζ)
    (hWa : AdaptedBefore 𝓖 ζ W) (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i)) (hG : MeasurableSet[𝓖 0] G)
    (hGae : ∀ᵐ ω ∂P, ω ∈ G)
    (hGc : ∀ ω ∈ G, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVLc : ∀ ω ∈ G, ∀ i, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVRc : ∀ ω ∈ G, ∀ i, ContinuousOn (VR i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR Q 𝓕' (fun t ω => W t (π ω))
      (fun i t ω => VL i t (π ω)) (fun i t ω => VR i t (π ω)) B (ζ ∘ π))
    (hκ : 0 < κ) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∃ T : ℕ → Ω → ℝ≥0, IsAnnouncingSeq 𝓖 P ζ T ∧ ∀ n ω, T n ω ≤ n := by
  have : IsProbabilityMeasure Q := hE.1.isProbabilityMeasure'
  let a : ℕ → ℕ → Ω → WithTop ℝ≥0 := fun p k ω => if ω ∈ G then
    candTime ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω) p k else ⊤
  have ha : ∀ p k, IsStoppingTime 𝓖 (a p k) :=
    isStoppingTime_candTime_on_good hWa hVLa hVRa hG hGc hVLc hVRc
  have hmono : ∀ p ω, Monotone fun k => a p k ω := by
    intro p ω
    by_cases hω : ω ∈ G
    · simpa only [a, hω, ↓reduceIte] using
        (candTime_mono (ρL := ρL) (ρR := ρR) (w := (W · ω))
          (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) (ζ := ζ ω) p)
    · simp only [a, hω, ↓reduceIte]
      exact monotone_const
  have hGQ := hπ.quasiMeasurePreserving.ae hGae
  have hb (ω : Ω') (hω : π ω ∈ G) (p : ℕ) :
      BddSeq (fun k => a p k ∘ π) ω ↔ ∃ M : ℕ, ∀ k,
        candTime ρL ρR (W · (π ω)) (fun i t => VL i t (π ω)) (fun i t => VR i t (π ω))
          (ζ (π ω)) p k ≤ ((M : ℝ≥0) : WithTop ℝ≥0) := by
    simp only [BddSeq, a, Function.comp_apply, hω, ↓reduceIte]
  apply exists_isAnnouncingSeq_of_pullback_candidates hπ hζ ha hmono
  · filter_upwards [hGQ] with ω hω p hp k
    obtain ⟨t, ht, htζ⟩ := candTime_lt_of_bdd ((hb ω hω p).1 hp) k
    simp only [a, hω, ↓reduceIte]
    rw [ht]
    exact htζ
  · filter_upwards [hGQ, hE.2.2.2.2] with ω hω hpath t ht
    obtain ⟨K, hK⟩ := exists_eventually_le_candTime hpath.isForcePath ht
    refine ⟨K, fun p hp k hk => ?_⟩
    simpa only [a, hω, ↓reduceIte, Function.comp_apply] using hK p ((hb ω hω p).1 hp) k hk
  · filter_upwards [hGQ, hE.2.2.2.2, hE.ae_tendsto_threshold hκ] with ω hω hpath hterm hζtop
    have hTζ : (((ζ (π ω)).toNNReal : ℝ≥0) : ℝ≥0∞) = ζ (π ω) := ENNReal.coe_toNNReal hζtop
    have hT : 0 < (ζ (π ω)).toNNReal := by
      refine pos_iff_ne_zero.2 fun h0 => hseed (hpath.isForcePath.threshold_of_eq_zero ?_)
      change ζ (π ω) = 0
      rw [← hTζ, h0, ENNReal.coe_zero]
    obtain ⟨w₀, vL₀, vR₀, hlim, hth⟩ := hterm _ hT hTζ
    obtain ⟨p, hp⟩ := exists_bdd_candTime hpath.isForcePath hT hTζ hlim hth
    exact ⟨p, (hb ω hω p).2 hp⟩

end InteractingSLE.Sec2.T24Bridge
