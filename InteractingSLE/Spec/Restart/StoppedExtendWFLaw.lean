/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedExtendWF
import InteractingSLE.Spec.Sec4.HistBorel

/-!
# (U): the law of the history killed at a Galmarino stop

Packet PROVE-DOMAINMARKOV10. The stopped whole-field identification (`StoppedExtendWF.StoppedJointLawStatement`) has
two halves (ruling R38, Part C.5, last paragraph: "For any two candidate couplings the path marginal is the same by
Theorem 2.2"): the **history law** through the stop, and the common conditional field kernel given that history. This
file proves the history half from a continuation of the stopped evolution:

* `killAt γ t`: a history killed at the time `t` (the samples at dyadic times `≥ t` are reset to `0`);
* `StoppedContinuationStatement κ` (**named input**: the strong Markov continuation of a local evolution at its stop,
  `Sec2.Assembly3.isIntegratedSLEEvolution_contClosed` with the degenerate stops — `V = 0`, `V = ∞`, the word bad at
  `V` — treated): a local evolution before `V`, continuous at a finite `V`, is the restriction of a full integrated
  evolution on an enlargement whose lifetime is at least `V`;
* **`map_killedHistory_eq_of_continuation`** (proved): given such a continuation and a measurable Galmarino rule
  `R` with `V = R(history killed at V)`, the history killed at `V` has the law of any full evolution's history killed
  at `R(its history) ∧ ζ₀` (the continuation's killed history has the reference's law by Theorem 2.2's uniqueness,
  and the stopped history is the same measurable function of it, by Galmarino's property);
* `StoppedHistLawStatement κ` and `stoppedHistLawStatement_of_continuation`: (U) for every coupling through a Galmarino
  stop, from the continuation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE

namespace Restart

namespace StoppedExtendWF

open LawUnique StoppedExtend

variable {nL nR : ℕ}

/-! ### Killing a history at a time -/

/-- **A history killed at the time `t`**: lifetime `t`, the samples before `t` kept, the others reset to `0`. -/
def killAt (γ : HistorySpace nL nR) (t : ℝ≥0∞) : HistorySpace nL nR :=
  (t, fun p => if (dyadicTime p : ℝ≥0∞) < t then γ.2 p else 0)

theorem measurable_killAt : Measurable fun q : HistorySpace nL nR × ℝ≥0∞ => killAt q.1 q.2 := by
  refine measurable_snd.prodMk (Measurable.of_eval fun p => ?_)
  exact Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    ((measurable_pi_apply p).comp (measurable_snd.comp measurable_fst)) measurable_const

/-- Killing a killed history at an earlier time gives the history killed at that time. -/
theorem killAt_killedHistory {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ V : Ω → ℝ≥0∞} {ω : Ω} (hV : V ω ≤ ζ ω) :
    killAt (killedHistory W VL VR ζ ω) (V ω) = killedHistory W VL VR V ω := by
  refine Prod.ext rfl (funext fun p => ?_)
  by_cases hp : (dyadicTime p : ℝ≥0∞) < V ω
  · simp only [killAt, killedHistory, hp, hp.trans_le hV, ↓reduceIte]
  · simp only [killAt, killedHistory, hp, ↓reduceIte]

/-- The stop of a rule, capped at the lifetime, and the history killed there. -/
def ruleKill (R : HistorySpace nL nR → ℝ≥0∞) (γ : HistorySpace nL nR) : HistorySpace nL nR :=
  killAt γ (min (R γ) γ.1)

theorem measurable_ruleKill {R : HistorySpace nL nR → ℝ≥0∞} (hR : Measurable R) :
    Measurable (ruleKill R) :=
  measurable_killAt.comp (measurable_id.prodMk (hR.min measurable_fst))

/-! ### (U) from a continuation -/

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **(U) from a continuation.** Let `V = R(history killed at V)` almost surely for a measurable Galmarino rule `R`,
and let a full integrated evolution `X'` on `(Ω', P')`, `P'.map π = P`, have lifetime `≥ V ∘ π` and agree with the
stopped coordinates before `V ∘ π`. Then the history killed at `V` has the law of every full evolution's history killed
at `R(its history) ∧ ζ₀`. -/
theorem map_killedHistory_eq_of_continuation (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR)
    {R : HistorySpace nL nR → ℝ≥0∞} (hRm : Measurable R) (hRg : IsHistGalmarino R)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR V)
    (hV : ∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω))
    (hcS : ∀ᵐ ω ∂P, ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) {t | (t : ℝ≥0∞) < V ω})
    {Ω' : Type u} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {π : Ω' → Ω}
    (hπ : Measurable π) (hπP : P'.map π = P) {𝓕' : Filtration ℝ≥0 mΩ'} {W' : ℝ≥0 → Ω' → ℝ}
    {VL' : Fin nL → ℝ≥0 → Ω' → ℝ} {VR' : Fin nR → ℝ≥0 → Ω' → ℝ} {B' : ℝ≥0 → Ω' → ℝ} {ζ' : Ω' → ℝ≥0∞}
    (hE' : IsIntegratedSLEEvolution κ xL xR ρL ρR P' 𝓕' W' VL' VR' B' ζ')
    (hag : ∀ᵐ p ∂P', V (π p) ≤ ζ' p ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < V (π p) →
      W' t p = W t (π p) ∧ (∀ i, VL' i t p = VL i t (π p)) ∧ ∀ j, VR' j t p = VR j t (π p))
    {Ω₀ : Type v} {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ}
    {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B₀ : ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞}
    (hE₀ : IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀) :
    P.map (killedHistory W VL VR V) =
      P₀.map (killedHistory W₀ VL₀ VR₀ fun ω₀ => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω₀)) (ζ₀ ω₀)) := by
  have hX' := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hE'
  have hX₀ := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hE₀
  have hk := measurable_killedHistory hX
  have hk' := measurable_killedHistory hX'
  have hk₀ := measurable_killedHistory hX₀
  have hF' := measurable_ruleKill hRm
  -- the reference side is `ruleKill R` of its killed history
  have e₀ : (killedHistory W₀ VL₀ VR₀ fun ω₀ => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω₀)) (ζ₀ ω₀)) =
      ruleKill R ∘ killedHistory W₀ VL₀ VR₀ ζ₀ := by
    funext ω₀
    exact (killAt_killedHistory (V := fun ω₀ => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω₀)) (ζ₀ ω₀))
      (min_le_right _ _)).symm
  -- the stopped side is `ruleKill R` of the continuation's killed history (Galmarino)
  have hV' : ∀ᵐ p ∂P', V (π p) = R (killedHistory W VL VR V (π p)) := by
    rw [← hπP] at hV
    exact ae_of_ae_map hπ.aemeasurable hV
  have hcS' : ∀ᵐ p ∂P', ContinuousOn (fun t => (W t (π p), fun i => VL i t (π p), fun j => VR j t (π p)))
      {t | (t : ℝ≥0∞) < V (π p)} := by
    rw [← hπP] at hcS
    exact ae_of_ae_map hπ.aemeasurable hcS
  have hstop : ∀ᵐ p ∂P', killedHistory W VL VR V (π p) = ruleKill R (killedHistory W' VL' VR' ζ' p) := by
    filter_upwards [hV', hag, hcS', hE'.isSLEEvolutionUpTo.ae_path] with p hVp hagp hcp hp'
    obtain ⟨hVζ, hagt⟩ := hagp
    have hsq : ∀ q : ℕ × ℕ, (dyadicTime q : ℝ≥0∞) < V (π p) →
        (killedHistory W VL VR V (π p)).2 q = (killedHistory W' VL' VR' ζ' p).2 q := fun q hq => by
      have h1 := hagt (dyadicTime q) hq
      have e1 : (killedHistory W VL VR V (π p)).2 q = (W (dyadicTime q) (π p),
          (fun i => VL i (dyadicTime q) (π p)), fun j => VR j (dyadicTime q) (π p)) := by
        simp only [killedHistory, hq, ↓reduceIte]
      have e2 : (killedHistory W' VL' VR' ζ' p).2 q = (W' (dyadicTime q) p,
          (fun i => VL' i (dyadicTime q) p), fun j => VR' j (dyadicTime q) p) := by
        simp only [killedHistory, hq.trans_le hVζ, ↓reduceIte]
      rw [e1, e2]
      exact Prod.ext h1.1.symm (Prod.ext (funext fun i => (h1.2.1 i).symm) (funext fun j => (h1.2.2 j).symm))
    have hsamp : ∀ q : ℕ × ℕ, (dyadicTime q : ℝ≥0∞) < R (killedHistory W VL VR V (π p)) →
        (killedHistory W VL VR V (π p)).2 q = (killedHistory W' VL' VR' ζ' p).2 q := fun q hq =>
      hsq q (hVp ▸ hq)
    have hR1 : R (killedHistory W VL VR V (π p)) ≤ (killedHistory W VL VR V (π p)).1 := by
      rw [← hVp]; exact le_rfl
    have hR2 : R (killedHistory W VL VR V (π p)) ≤ (killedHistory W' VL' VR' ζ' p).1 := by
      rw [← hVp]; exact hVζ
    have hR' : R (killedHistory W' VL' VR' ζ' p) = V (π p) := by
      rw [hRg _ _ (isKilledContHist_killedHistory hcp)
        (isKilledContHist_killedHistory (continuousOn_state_of_isSLEPathUpTo hp')) hR1 hR2 hsamp, ← hVp]
    have hmin : min (R (killedHistory W' VL' VR' ζ' p)) (killedHistory W' VL' VR' ζ' p).1 = V (π p) := by
      rw [hR']
      exact min_eq_left hVζ
    unfold ruleKill
    rw [hmin]
    refine Prod.ext rfl (funext fun q => ?_)
    by_cases hq : (dyadicTime q : ℝ≥0∞) < V (π p)
    · have h2 := hsq q hq
      simp only [killAt, hq, ↓reduceIte]
      exact h2
    · simp only [killedHistory, killAt, hq, ↓reduceIte]
  -- Theorem 2.2's uniqueness in law
  have hlaw := map_killedHistory_eq (Sec4.killedStateLawUnique_of_isOrderedForceWord hκ ρL ρR hF) hE' hX' hE₀ hX₀
  calc P.map (killedHistory W VL VR V)
      = P'.map (killedHistory W VL VR V ∘ π) := by rw [← hπP, Measure.map_map hk hπ]
    _ = P'.map (ruleKill R ∘ killedHistory W' VL' VR' ζ') := Measure.map_congr hstop
    _ = (P'.map (killedHistory W' VL' VR' ζ')).map (ruleKill R) := (Measure.map_map hF' hk').symm
    _ = (P₀.map (killedHistory W₀ VL₀ VR₀ ζ₀)).map (ruleKill R) := by rw [hlaw]
    _ = P₀.map (killedHistory W₀ VL₀ VR₀ fun ω₀ => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω₀)) (ζ₀ ω₀)) := by
      rw [Measure.map_map hF' hk₀, e₀]

/-! ### The statements -/

/-- **Named input: the continuation of a local evolution at its stop** (the strong Markov restart of Theorem 2.2's
evolution, `Sec2.Assembly3.isIntegratedSLEEvolution_contClosed`, with the degenerate stops treated: at `V = ∞` the local
evolution is already complete, at a finite `V` where the word is bad its threshold is `V`). A local integrated evolution
before `V` whose state is continuous at a finite `V` is, on an enlargement, the restriction of a full integrated
evolution whose lifetime is at least `V`. -/
def StoppedContinuationStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (V : Ω → ℝ≥0∞),
      Sec2.IsSLEEvolutionUpTo κ xL xR ρL ρR P 𝓕 W VL VR B V →
      (∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω →
        ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (Iic T)) →
      ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P') (π : Ω' → Ω)
        (_ : Measurable π) (𝓕' : Filtration ℝ≥0 mΩ') (W' : ℝ≥0 → Ω' → ℝ) (VL' : Fin nL → ℝ≥0 → Ω' → ℝ)
        (VR' : Fin nR → ℝ≥0 → Ω' → ℝ) (B' : ℝ≥0 → Ω' → ℝ) (ζ' : Ω' → ℝ≥0∞),
        P'.map π = P ∧ IsIntegratedSLEEvolution κ xL xR ρL ρR P' 𝓕' W' VL' VR' B' ζ' ∧
          ∀ᵐ p ∂P', V (π p) ≤ ζ' p ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < V (π p) →
            W' t p = W t (π p) ∧ (∀ i, VL' i t p = VL i t (π p)) ∧ ∀ j, VR' j t p = VR j t (π p)

/-- **(U), the history half of the stopped whole-field identification**: for every coupling through a Galmarino stop
`V = R(history killed at V)` and every full integrated evolution of the word, the history killed at `V` has the law of
the full evolution's history killed at `R(its history) ∧ ζ₀`. -/
def StoppedHistLawStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → ∀ R : HistorySpace nL nR → ℝ≥0∞, Measurable R → IsHistGalmarino R →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (V : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h →
      (∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) →
    ∀ {Ω₀ : Type v} {mΩ₀ : MeasurableSpace Ω₀} (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
      (𝓕₀ : Filtration ℝ≥0 mΩ₀) (W₀ : ℝ≥0 → Ω₀ → ℝ) (VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ)
      (VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ) (B₀ : ℝ≥0 → Ω₀ → ℝ) (ζ₀ : Ω₀ → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ →
      P.map (killedHistory W VL VR V) =
        P₀.map (killedHistory W₀ VL₀ VR₀ fun ω₀ => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω₀)) (ζ₀ ω₀))

/-- **(U) from the continuation** (every `κ > 0`). -/
theorem stoppedHistLawStatement_of_continuation (hκ : 0 < κ) (hC : StoppedContinuationStatement.{u} κ) :
    StoppedHistLawStatement.{u, v} κ := by
  intro nL nR xL xR ρL ρR hF R hRm hRg Ω mΩ P _ 𝓕 W VL VR B V h hSC hV Ω₀ mΩ₀ P₀ _ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ hE₀
  obtain ⟨hEv, hcont, -, -, hX, -⟩ := hSC
  obtain ⟨Ω', mΩ', P', hP', π, hπ, 𝓕', W', VL', VR', B', ζ', hπP, hE', hag⟩ :=
    hC xL xR ρL ρR hF P 𝓕 W VL VR B V hEv hcont
  exact map_killedHistory_eq_of_continuation hκ hF hRm hRg hX hV
    (hEv.ae_path.mono fun ω hp => continuousOn_state_of_isSLEPathUpTo hp) hπ hπP hE' hag hE₀

/-! ### The joint law from (U) and the stopped kernel -/

/-- **(SR1) for the field of a coupling through a stop** (the proof of
`IsOptionalHullCoupling.lintegral_negSobolevSq_lt_top`: it uses only the measurability of the field and its GFF law). -/
theorem lintegral_negSobolevSq_lt_top_of_stopped {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hSC : IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h) {ε : ℝ} (hε : 0 < ε)
    (ζc : LQGMetric.TestOn upperHalfPlaneOpens) :
    ∫⁻ o, Sobolev.negSobolevSq ε (h o) ζc ∂P < ⊤ := by
  obtain ⟨-, -, hhm, hgff, -⟩ := hSC
  obtain ⟨u₀, hu₀⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR xL xR
  have hproc := hgff u₀ hu₀
  set m := Distribution.ofFun upperHalfPlaneOpens u₀ volume ⊤ with hmdef
  have hharm : InnerProductSpace.HarmonicOnNhd u₀ (upperHalfPlaneOpens : Set ℂ) := hu₀.1
  have hcont : ContinuousOn u₀ (upperHalfPlaneOpens : Set ℂ) := fun x hx =>
    (HarmonicAt.analyticAt (hharm x hx)).continuousAt.continuousWithinAt
  have hloc : LocallyIntegrableOn u₀ (upperHalfPlaneOpens : Set ℂ) volume :=
    hcont.locallyIntegrableOn upperHalfPlaneOpens.isOpen.measurableSet
  have hm : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, m φ = ∫ z, u₀ z * φ z := fun φ => by
    rw [hmdef, Distribution.ofFun_apply hloc]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [smul_eq_mul]
    ring
  have h0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun o => h o - m) P := by
    refine ⟨LQGMetric.measurable_distOn_iff.2 fun φ => ?_, ?_⟩
    · simp only [sub_apply]
      exact ((LQGMetric.measurable_distOn_apply φ).comp hhm).sub_const _
    · convert hproc using 2 with φ
      funext o
      rw [sub_apply, hm]
  have hsr := Sobolev.aux11_sr1 (LQGMetric.zbAdmissible_of_subset_H (U := upperHalfPlaneOpens) subset_rfl) h0 hharm
    hε ζc
  rw [← hmdef] at hsr
  simpa only [sub_add_cancel] using hsr

/-- **Named input (K): the stopped whole-field kernel off a thin set, as a Borel function of the history** (ruling R38,
Part C: (WF2) at the stop with C.4's component kernels and the Borel label means of PROVE-AUX50B, the ambient
extension across the trace by the Sobolev core of Aux. lemma 23). For an ordered word and a measurable Galmarino rule
`R` there are a relatively closed random set `A` of the history (Borel avoidance events) and a Borel functional `G`
such that: in every
coupling through a stop `V = R(history killed at V)`, given the history killed at `V`, the conditional characteristic
function of the field at every test function avoiding `A` is `G`, and `A` is thin (dimension `≤ d < 2` on compacts); and
in every full coupling the same holds at the stop `R(history) ∧ ζ₀` (without the thinness). -/
def StoppedKernelStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → ∀ R : HistorySpace nL nR → ℝ≥0∞, Measurable R → IsHistGalmarino R →
    ∃ (A : HistorySpace nL nR → Set ℂ) (G : LQGMetric.TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ) (d : ℝ),
      d < 2 ∧ (∀ γ, closure (A γ) ∩ (upperHalfPlaneOpens : Set ℂ) ⊆ A γ) ∧
      (∀ K : Set ℂ, IsCompact K → MeasurableSet {γ | Disjoint K (A γ)}) ∧ (∀ φ, Measurable (G φ)) ∧
      (∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
        (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
        (V : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h →
        (∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) →
        (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
          Disjoint (tsupport φ) (A (killedHistory W VL VR V ω)) →
            P[fun ω' => Complex.exp (↑(h ω' φ) * Complex.I) |
              MeasurableSpace.comap (killedHistory W VL VR V) inferInstance] ω =
              G φ (killedHistory W VL VR V ω)) ∧
        ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K → K ⊆ upperHalfPlaneOpens →
          dimH (A (killedHistory W VL VR V ω) ∩ K) ≤ ENNReal.ofReal d) ∧
      ∀ {Ω₀ : Type v} {mΩ₀ : MeasurableSpace Ω₀} (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
        (𝓕₀ : Filtration ℝ≥0 mΩ₀) (W₀ : ℝ≥0 → Ω₀ → ℝ) (VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ)
        (VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ) (B₀ : ℝ≥0 → Ω₀ → ℝ) (ζ₀ : Ω₀ → ℝ≥0∞)
        (h₀ : Ω₀ → LQGMetric.DistOn upperHalfPlaneOpens),
        IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ →
        ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω₀ ∂P₀,
          Disjoint (tsupport φ) (A (killedHistory W₀ VL₀ VR₀
            (fun ω₀ => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω₀)) (ζ₀ ω₀)) ω₀)) →
            P₀[fun ω' => Complex.exp (↑(h₀ ω' φ) * Complex.I) |
              MeasurableSpace.comap (killedHistory W₀ VL₀ VR₀
                (fun ω₀ => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω₀)) (ζ₀ ω₀))) inferInstance] ω₀ =
              G φ (killedHistory W₀ VL₀ VR₀ (fun ω₀ => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω₀)) (ζ₀ ω₀)) ω₀)

/-- **The stopped whole-field identification from (U) and (K)** (the Sobolev core of Aux. lemma 23,
`Sec4.map_prod_eq_of_condCharFun_off_ae`, conditioning on the killed histories themselves). -/
theorem stoppedJointLawStatement_of_histLaw_kernel (hU : StoppedHistLawStatement.{u, u} κ)
    (hK : StoppedKernelStatement.{u, u} κ) : StoppedJointLawStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF R hRm hRg Ω mΩ P _ 𝓕 W VL VR B V h hSC hV Ω₀ mΩ₀ P₀ _ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ hC₀
  obtain ⟨A, G, d, hd, hAcl, hAm, hGm, hKS, hKF⟩ := hK xL xR ρL ρR hF R hRm hRg
  obtain ⟨hcf₁, hthin⟩ := hKS P 𝓕 W VL VR B V h hSC hV
  have hcf₂ := hKF P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ hC₀
  have hlaw := hU xL xR ρL ρR hF R hRm hRg P 𝓕 W VL VR B V h hSC hV P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ hC₀.1
  set ε : ℝ := min (1 / 2) ((2 - d) / 4) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hdε : d < 2 - 2 * ε := by
    have := min_le_right (1 / 2 : ℝ) ((2 - d) / 4)
    linarith
  have hsr := fun ζc => lintegral_negSobolevSq_lt_top_of_stopped hSC hε0 ζc
  obtain ⟨-, -, hh, -, hX, -⟩ := hSC
  have hX₀ := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hC₀.1
  have hV₀m : Measurable fun ω₀ => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω₀)) (ζ₀ ω₀) :=
    (hRm.comp (measurable_killedHistory hX₀)).min (measurable_lifetime hX₀)
  have hX₀' := isMeasurableKilledDriving_of_le hX₀ hV₀m (fun ω₀ => min_le_right _ _)
  have hk := measurable_killedHistory hX
  have hk₀ := measurable_killedHistory hX₀'
  refine Sec4.map_prod_eq_of_condCharFun_off_ae (U := upperHalfPlaneOpens) hε0 hε1 hAcl hAm hGm hh hk le_rfl
    hk.comap_le hsr hcf₁ hC₀.2.1 hk₀ le_rfl hk₀.comap_le (fun ζc => hC₀.lintegral_negSobolevSq_lt_top hε0 ζc)
    hcf₂ hlaw ?_
  filter_upwards [hthin] with ω hω K hK hKH
  exact (hω K hK hKH).trans_lt (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hdε, by linarith⟩)

end StoppedExtendWF

end Restart

end InteractingSLE
