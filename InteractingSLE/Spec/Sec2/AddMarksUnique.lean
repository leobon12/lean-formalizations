/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AddMarksGirsanov
import InteractingSLE.Spec.Sec2.AddMarksInverse

/-!
# Reverse Girsanov: uniqueness in law up to a separated stopping time

Packet PROVE-SEC2-GIR2. Specification, proof of Theorem 2.2 (`source/spec/p001-048.md` L488): "One
can also reverse this procedure (starting with a process defined for multiple force points and
applying Girsanov's theorem to produce the process corresponding to one force point). If there were
multiple possibilities for the joint laws of the `W_t`, `B_t`, and `V_t^{i,q}` in the
multiple-force-point case, then this would produce multiple possibilities for the joint laws in the
single-force-point case, contradicting what we have already established."

For two local evolutions of the same force word, the weights of the marks that stay at distance
`≥ δ` from the driver before bounded stopping times `τ₁`, `τ₂` are changed (removed) by
`girsanov_changeWeights`. The observed state is `observe τ W VL VR B̂ : Ω → ObsSpace nL nR`: the
driver and the marks killed at `τ` (value `0` from `τ` on), the Brownian motion `B̂` at all times, and
`τ` itself.

* `observe_measurable`: the observed state is measurable;
* `weightDrift_eq_observe`: the Girsanov drift is a fixed functional of the observed state (the cut
  drift of the coordinate processes of `ObsSpace`, `obsDrift`), and so are its Riemann sums against
  `B̂` and its quadratic integral;
* `IsSLEEvolutionUpTo.map_observe_eq`: **uniqueness in law transfers through the reverse change**:
  if the laws of the observed states under the two changed measures agree (uniqueness in law of the
  reference word up to the localization, the input "what we have already established"), then the
  laws of the observed states under the original measures agree (`map_eq_of_girsanov`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

open Girsanov

namespace Sec2

/-- The observation space: a path of states `(w, vL, vR, b)` indexed by `ℝ≥0`, and a time. -/
abbrev ObsSpace (nL nR : ℕ) : Type :=
  (ℝ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ) × ℝ≥0∞

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}

/-- The observed state: driver and marks killed at `τ`, the Brownian motion `B` at all times, and `τ`. -/
def observe (τ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ObsSpace nL nR :=
  (fun t => (killed τ W t ω, fun i => killed τ (VL i) t ω, fun i => killed τ (VR i) t ω, B t ω),
    τ ω)

/-! ### Coordinate processes of the observation space -/

/-- The driver coordinate. -/
def obsW (t : ℝ≥0) (e : ObsSpace nL nR) : ℝ := (e.1 t).1

/-- The left-mark coordinates. -/
def obsVL (i : Fin nL) (t : ℝ≥0) (e : ObsSpace nL nR) : ℝ := (e.1 t).2.1 i

/-- The right-mark coordinates. -/
def obsVR (i : Fin nR) (t : ℝ≥0) (e : ObsSpace nL nR) : ℝ := (e.1 t).2.2.1 i

/-- The Brownian coordinate. -/
def obsB (t : ℝ≥0) (e : ObsSpace nL nR) : ℝ := (e.1 t).2.2.2

/-- The time coordinate. -/
def obsTime (e : ObsSpace nL nR) : ℝ≥0∞ := e.2

theorem measurable_obsW (t : ℝ≥0) : Measurable (obsW (nL := nL) (nR := nR) t) :=
  measurable_fst.comp ((measurable_pi_apply t).comp measurable_fst)

theorem measurable_obsVL (i : Fin nL) (t : ℝ≥0) : Measurable (obsVL (nR := nR) i t) :=
  (measurable_pi_apply i).comp
    (measurable_fst.comp (measurable_snd.comp ((measurable_pi_apply t).comp measurable_fst)))

theorem measurable_obsVR (i : Fin nR) (t : ℝ≥0) : Measurable (obsVR (nL := nL) i t) :=
  (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp
    (measurable_snd.comp ((measurable_pi_apply t).comp measurable_fst))))

theorem measurable_obsB (t : ℝ≥0) : Measurable (obsB (nL := nL) (nR := nR) t) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    ((measurable_pi_apply t).comp measurable_fst)))

theorem measurable_obsTime : Measurable (obsTime (nL := nL) (nR := nR)) := measurable_snd

/-- The constant filtration of the observation space. -/
def obsFiltration (nL nR : ℕ) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ObsSpace nL nR)) :=
  Filtration.const ℝ≥0 _ le_rfl

theorem obsTime_isStoppingTime (s : ℝ≥0) :
    MeasurableSet[obsFiltration nL nR s] {e : ObsSpace nL nR | obsTime e ≤ s} :=
  measurableSet_le measurable_obsTime measurable_const

theorem adaptedBefore_obs {X : ℝ≥0 → ObsSpace nL nR → ℝ} (hX : ∀ t, Measurable (X t)) :
    AdaptedBefore (obsFiltration nL nR) obsTime X := fun t _ hA =>
  (measurableSet_lt measurable_const measurable_obsTime).inter (hX t hA)

/-- The Girsanov drift of a change of weights, as a functional of the observed state. -/
def obsDrift (κ δ : ℝ) (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) : ℝ≥0 → ObsSpace nL nR → ℝ :=
  weightDrift κ δ ρL ρL' ρR ρR' obsTime obsTime obsW obsVL obsVR

theorem obsDrift_props (κ : ℝ) {δ : ℝ} (hδ : 0 < δ) (ρL ρL' : Fin nL → ℝ)
    (ρR ρR' : Fin nR → ℝ) :
    IsStronglyProgressive (obsFiltration nL nR) (obsDrift κ δ ρL ρL' ρR ρR') ∧
      ∀ t, Measurable (obsDrift κ δ ρL ρL' ρR ρR' t) := by
  have hp : IsStronglyProgressive (obsFiltration nL nR) (obsDrift κ δ ρL ρL' ρR ρR') :=
    isStronglyProgressive_cutDrift (continuous_shiftIntegrand κ 1 hδ _)
      (adaptedBefore_obs measurable_obsW)
      (allMarks_adaptedBefore (fun i => adaptedBefore_obs (measurable_obsVL i))
        (fun i => adaptedBefore_obs (measurable_obsVR i))) obsTime_isStoppingTime
  exact ⟨hp, fun t => (hp.stronglyAdapted t).measurable⟩

/-! ### The observed state and the drift as a functional of it -/

/-- A stopping time is measurable. -/
theorem measurable_of_stoppingTime {τ : Ω → ℝ≥0∞}
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) : Measurable τ := by
  refine measurable_of_Iic fun x => ?_
  induction x using ENNReal.recTopCoe with
  | top => simp
  | coe s => exact 𝓕.le s _ (hτ s)

/-- The observed state is measurable. -/
theorem measurable_observe {τ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) (hW : AdaptedBefore 𝓕 τ W)
    (hVL : ∀ i, AdaptedBefore 𝓕 τ (VL i)) (hVR : ∀ i, AdaptedBefore 𝓕 τ (VR i))
    (hB : ∀ t, Measurable (B t)) : Measurable (observe τ W VL VR B) := by
  have hk : ∀ {X : ℝ≥0 → Ω → ℝ}, AdaptedBefore 𝓕 τ X → ∀ t, Measurable (killed τ X t) :=
    fun hX t => (measurable_killed hX t).mono (𝓕.le t) le_rfl
  refine Measurable.prodMk (measurable_pi_iff.2 fun t => ?_) (measurable_of_stoppingTime hτ)
  exact (hk hW t).prodMk ((measurable_pi_iff.2 fun i => hk (hVL i) t).prodMk
    ((measurable_pi_iff.2 fun i => hk (hVR i) t).prodMk (hB t)))

/-- **The Girsanov drift is a functional of the observed state.** -/
theorem weightDrift_eq_observe {κ δ : ℝ} {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ}
    {τ ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (B : ℝ≥0 → Ω → ℝ) {ω : Ω} (hτζ : τ ω ≤ ζ ω) (t : ℝ≥0) :
    weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR t ω
      = obsDrift κ δ ρL ρL' ρR ρR' t (observe τ W VL VR B ω) := by
  unfold obsDrift weightDrift shiftDrift cutDrift
  congr 1
  funext n
  set s := grid n (stepIdx n (t : ℝ)) with hs
  unfold cutIntegrand
  by_cases h : (s : ℝ≥0∞) < τ ω
  · have hζ := h.trans_le hτζ
    have h' : (s : ℝ≥0∞) < obsTime (observe τ W VL VR B ω) := h
    simp only [h, h', ↓reduceIte]
    have hW : killed ζ W s ω = killed obsTime obsW s (observe τ W VL VR B ω) := by
      simp [killed, obsW, obsTime, observe, h, hζ]
    have hU : (fun j => killed ζ (allMarks VL VR j) s ω)
        = fun j => killed obsTime (allMarks obsVL obsVR j) s (observe τ W VL VR B ω) := by
      funext k
      cases k using Fin.addCases with
      | left i => simp [allMarks, killed, obsVL, obsTime, observe, h, hζ]
      | right i => simp [allMarks, killed, obsVR, obsTime, observe, h, hζ]
    rw [hW, hU]
  · have h' : ¬ (s : ℝ≥0∞) < obsTime (observe τ W VL VR B ω) := h
    simp only [h, h', ↓reduceIte]

/-- The Riemann sums of the drift against `B` are a functional of the observed state. -/
theorem riemannSum_eq_observe {κ δ : ℝ} {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ}
    {τ ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (B : ℝ≥0 → Ω → ℝ) (hτζ : ∀ ω, τ ω ≤ ζ ω) (n : ℕ) (t : ℝ≥0) :
    riemannSum B (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR) n t
      = fun ω => riemannSum obsB (obsDrift κ δ ρL ρL' ρR ρR') n t (observe τ W VL VR B ω) := by
  funext ω
  unfold riemannSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [weightDrift_eq_observe B (hτζ ω)]
  rfl

/-- The quadratic integral of the drift is a functional of the observed state. -/
theorem quadInt_eq_observe {κ δ : ℝ} {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ}
    {τ ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (B : ℝ≥0 → Ω → ℝ) (hτζ : ∀ ω, τ ω ≤ ζ ω) (t : ℝ≥0) :
    quadInt (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR) t
      = fun ω => quadInt (obsDrift κ δ ρL ρL' ρR ρR') t (observe τ W VL VR B ω) := by
  funext ω
  unfold quadInt
  simp only [weightDrift_eq_observe B (hτζ ω)]

/-! ### Uniqueness in law through the reverse change -/

section Transfer

variable {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂} {P₁ : Measure Ω₁}
  {P₂ : Measure Ω₂} {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂} {κ : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ} {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ}
  {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ τ₁ : Ω₁ → ℝ≥0∞}
  {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ} {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ}
  {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ τ₂ : Ω₂ → ℝ≥0∞}

/-- **Reverse Girsanov: uniqueness in law up to a separated stopping time** (Specification L488; the
graph node "Reverse Girsanov: uniqueness in law up to the next collision of an added point", localized
at a bounded stopping time). Let `(W_k, V_k, B_k)`, `k = 1, 2`, be local evolutions of the same force
word before `ζ_k`, with stopping times `τ_k ≤ ζ_k ∧ T`, and let `Q_k = Z_{T+1} · P_k` be the measures
of the change of weights `(ρL; ρR) → (ρL'; ρR')` cut at `τ_k` (`girsanov_changeWeights`: when the
changed marks stay at distance `≥ δ` before `τ_k`, the processes are a local evolution of the new
word under `Q_k`, with the Brownian motion `B̂_k = B_k + ∫ θ_k`). If the observed states
`observe τ_k W_k V_k B̂_k` have the same law under `Q₁` and `Q₂` (uniqueness in law for the new word up
to the localization), then they have the same law under `P₁` and `P₂`. -/
theorem IsSLEEvolutionUpTo.map_observe_eq [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (hE₁ : IsSLEEvolutionUpTo κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hE₂ : IsSLEEvolutionUpTo κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) (ρL' : Fin nL → ℝ)
    (ρR' : Fin nR → ℝ) (hτ₁ : ∀ s : ℝ≥0, MeasurableSet[𝓕₁ s] {ω | τ₁ ω ≤ s})
    (hτ₂ : ∀ s : ℝ≥0, MeasurableSet[𝓕₂ s] {ω | τ₂ ω ≤ s}) (hτ₁ζ : ∀ ω, τ₁ ω ≤ ζ₁ ω)
    (hτ₂ζ : ∀ ω, τ₂ ω ≤ ζ₂ ω) {T : ℝ≥0} (hτ₁T : ∀ ω, τ₁ ω ≤ T) (hτ₂T : ∀ ω, τ₂ ω ≤ T) {δ : ℝ}
    (hδ : 0 < δ)
    (hlaw : (girsanovMeasure P₁ 𝓕₁ B₁ (weightDrift κ δ ρL ρL' ρR ρR' τ₁ ζ₁ W₁ VL₁ VR₁) (T + 1)).map
        (observe τ₁ W₁ VL₁ VR₁ (girsanovProcess B₁ (weightDrift κ δ ρL ρL' ρR ρR' τ₁ ζ₁ W₁ VL₁ VR₁)))
      = (girsanovMeasure P₂ 𝓕₂ B₂ (weightDrift κ δ ρL ρL' ρR ρR' τ₂ ζ₂ W₂ VL₂ VR₂) (T + 1)).map
        (observe τ₂ W₂ VL₂ VR₂ (girsanovProcess B₂ (weightDrift κ δ ρL ρL' ρR ρR' τ₂ ζ₂ W₂ VL₂ VR₂)))) :
    P₁.map (observe τ₁ W₁ VL₁ VR₁ (girsanovProcess B₁ (weightDrift κ δ ρL ρL' ρR ρR' τ₁ ζ₁ W₁ VL₁ VR₁)))
      = P₂.map (observe τ₂ W₂ VL₂ VR₂
          (girsanovProcess B₂ (weightDrift κ δ ρL ρL' ρR ρR' τ₂ ζ₂ W₂ VL₂ VR₂))) := by
  obtain ⟨h1p, h1b, h1r⟩ := hE₁.weightDrift_props ρL' ρR' hτ₁ hτ₁ζ hδ
  obtain ⟨h2p, h2b, h2r⟩ := hE₂.weightDrift_props ρL' ρR' hτ₂ hτ₂ζ hδ
  obtain ⟨hop, hom⟩ := obsDrift_props (nL := nL) (nR := nR) κ hδ ρL ρL' ρR ρR'
  have hT₁ : ∀ t ω, T + 1 ≤ t → weightDrift κ δ ρL ρL' ρR ρR' τ₁ ζ₁ W₁ VL₁ VR₁ t ω = 0 :=
    fun t ω ht => cutDrift_eq_zero (lt_of_le_of_lt (hτ₁T ω)
      (by exact_mod_cast (lt_add_one T).trans_le ht))
  have hT₂ : ∀ t ω, T + 1 ≤ t → weightDrift κ δ ρL ρL' ρR ρR' τ₂ ζ₂ W₂ VL₂ VR₂ t ω = 0 :=
    fun t ω ht => cutDrift_eq_zero (lt_of_le_of_lt (hτ₂T ω)
      (by exact_mod_cast (lt_add_one T).trans_le ht))
  have hX₁ : Measurable (observe τ₁ W₁ VL₁ VR₁
      (girsanovProcess B₁ (weightDrift κ δ ρL ρL' ρR ρR' τ₁ ζ₁ W₁ VL₁ VR₁))) :=
    measurable_observe hτ₁ (hE₁.adapted_W.of_le hτ₁ hτ₁ζ) (fun i => (hE₁.adapted_VL i).of_le hτ₁ hτ₁ζ)
      (fun i => (hE₁.adapted_VR i).of_le hτ₁ hτ₁ζ) fun t =>
        ((hE₁.brownian.2.1 t).mono (𝓕₁.le t) le_rfl).add
          ((stronglyMeasurable_integral_comp h1p measurable_id t).measurable.mono (𝓕₁.le t) le_rfl)
  have hX₂ : Measurable (observe τ₂ W₂ VL₂ VR₂
      (girsanovProcess B₂ (weightDrift κ δ ρL ρL' ρR ρR' τ₂ ζ₂ W₂ VL₂ VR₂))) :=
    measurable_observe hτ₂ (hE₂.adapted_W.of_le hτ₂ hτ₂ζ) (fun i => (hE₂.adapted_VL i).of_le hτ₂ hτ₂ζ)
      (fun i => (hE₂.adapted_VR i).of_le hτ₂ hτ₂ζ) fun t =>
        ((hE₂.brownian.2.1 t).mono (𝓕₂.le t) le_rfl).add
          ((stronglyMeasurable_integral_comp h2p measurable_id t).measurable.mono (𝓕₂.le t) le_rfl)
  refine map_eq_of_girsanov hE₁.brownian hE₂.brownian h1p h2p h1b h2b h1r h2r hT₁ hT₂ hX₁ hX₂ hlaw
    (R := fun n => riemannSum obsB (obsDrift κ δ ρL ρL' ρR ρR') n (T + 1))
    (q := quadInt (obsDrift κ δ ρL ρL' ρR ρR') (T + 1)) (fun n => ?_) ?_ ?_ ?_ ?_ ?_
  · exact Finset.measurable_sum _ fun i _ => (hom _).mul
      ((measurable_obsB _).sub (measurable_obsB _))
  · exact ((stronglyMeasurable_integral_comp hop (measurable_id.pow_const 2) (T + 1)).mono
      le_rfl).measurable
  · exact fun n => EventuallyEq.of_eq (riemannSum_eq_observe _ hτ₁ζ n (T + 1))
  · exact fun n => EventuallyEq.of_eq (riemannSum_eq_observe _ hτ₂ζ n (T + 1))
  · exact EventuallyEq.of_eq (quadInt_eq_observe _ hτ₁ζ (T + 1))
  · exact EventuallyEq.of_eq (quadInt_eq_observe _ hτ₂ζ (T + 1))

/-- Undo the change of the Brownian coordinate: `b ↦ b − ∫ θ`, `θ` the drift functional. -/
def obsUnshift (κ δ : ℝ) (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) (e : ObsSpace nL nR) :
    ObsSpace nL nR :=
  (fun t => ((e.1 t).1, (e.1 t).2.1, (e.1 t).2.2.1,
    obsB t e - ∫ u in (0 : ℝ)..(t : ℝ), obsDrift κ δ ρL ρL' ρR ρR' u.toNNReal e), e.2)

theorem measurable_obsUnshift (κ : ℝ) {δ : ℝ} (hδ : 0 < δ) (ρL ρL' : Fin nL → ℝ)
    (ρR ρR' : Fin nR → ℝ) : Measurable (obsUnshift κ δ ρL ρL' ρR ρR') := by
  obtain ⟨hop, -⟩ := obsDrift_props (nL := nL) (nR := nR) κ hδ ρL ρL' ρR ρR'
  refine Measurable.prodMk (measurable_pi_iff.2 fun t => ?_) measurable_obsTime
  refine (measurable_obsW t).prodMk ((measurable_pi_iff.2 fun i => measurable_obsVL i t).prodMk
    ((measurable_pi_iff.2 fun i => measurable_obsVR i t).prodMk
      ((measurable_obsB t).sub ?_)))
  exact (stronglyMeasurable_integral_comp hop measurable_id t).measurable

/-- The observed state with the original Brownian motion is the unshifted observed state with the
changed one. -/
theorem obsUnshift_observe {κ δ : ℝ} {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ}
    {τ ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (B : ℝ≥0 → Ω → ℝ) (hτζ : ∀ ω, τ ω ≤ ζ ω) :
    obsUnshift κ δ ρL ρL' ρR ρR' ∘ observe τ W VL VR
        (girsanovProcess B (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR))
      = observe τ W VL VR B := by
  funext ω
  have key : ∀ t : ℝ≥0, ∫ u in (0 : ℝ)..(t : ℝ), weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR u.toNNReal ω
      = ∫ u in (0 : ℝ)..(t : ℝ), obsDrift κ δ ρL ρL' ρR ρR' u.toNNReal
          (observe τ W VL VR (girsanovProcess B (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR)) ω) :=
    fun t => by
      simp only [weightDrift_eq_observe (girsanovProcess B (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR))
        (hτζ ω)]
  refine Prod.ext (funext fun t => ?_) rfl
  simp only [Function.comp_apply, obsUnshift]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
  show obsB t (observe τ W VL VR (girsanovProcess B (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR)) ω)
      - ∫ u in (0 : ℝ)..(t : ℝ), obsDrift κ δ ρL ρL' ρR ρR' u.toNNReal
          (observe τ W VL VR (girsanovProcess B (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR)) ω)
      = B t ω
  rw [← key t]
  simp only [obsB, observe, girsanovProcess, drift]
  ring

/-- The killed finite-dimensional events are preimages of one set under the observed state. -/
theorem observe_preimage_killedEvent {n : ℕ} (ts : Fin n → ℝ≥0)
    (A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)) (τ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) :
    observe τ W VL VR B ⁻¹' {e | ∀ j, (ts j : ℝ≥0∞) < e.2 ∧ e.1 (ts j) ∈ A j}
      = {ω | ∀ j, (ts j : ℝ≥0∞) < τ ω ∧
        (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ A j} := by
  ext ω
  simp only [mem_preimage, mem_ofPred_eq, observe]
  refine forall_congr' fun j => and_congr_right fun hj => ?_
  simp [killed, hj]

/-- **Reverse Girsanov, with the original Brownian motions**: under the hypotheses of
`map_observe_eq`, the observed states `(W, V killed at τ, B, τ)` have the same law under `P₁` and
`P₂`. -/
theorem IsSLEEvolutionUpTo.map_observe_brownian_eq [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂]
    (hE₁ : IsSLEEvolutionUpTo κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hE₂ : IsSLEEvolutionUpTo κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) (ρL' : Fin nL → ℝ)
    (ρR' : Fin nR → ℝ) (hτ₁ : ∀ s : ℝ≥0, MeasurableSet[𝓕₁ s] {ω | τ₁ ω ≤ s})
    (hτ₂ : ∀ s : ℝ≥0, MeasurableSet[𝓕₂ s] {ω | τ₂ ω ≤ s}) (hτ₁ζ : ∀ ω, τ₁ ω ≤ ζ₁ ω)
    (hτ₂ζ : ∀ ω, τ₂ ω ≤ ζ₂ ω) {T : ℝ≥0} (hτ₁T : ∀ ω, τ₁ ω ≤ T) (hτ₂T : ∀ ω, τ₂ ω ≤ T) {δ : ℝ}
    (hδ : 0 < δ)
    (hlaw : (girsanovMeasure P₁ 𝓕₁ B₁ (weightDrift κ δ ρL ρL' ρR ρR' τ₁ ζ₁ W₁ VL₁ VR₁) (T + 1)).map
        (observe τ₁ W₁ VL₁ VR₁ (girsanovProcess B₁ (weightDrift κ δ ρL ρL' ρR ρR' τ₁ ζ₁ W₁ VL₁ VR₁)))
      = (girsanovMeasure P₂ 𝓕₂ B₂ (weightDrift κ δ ρL ρL' ρR ρR' τ₂ ζ₂ W₂ VL₂ VR₂) (T + 1)).map
        (observe τ₂ W₂ VL₂ VR₂ (girsanovProcess B₂ (weightDrift κ δ ρL ρL' ρR ρR' τ₂ ζ₂ W₂ VL₂ VR₂)))) :
    P₁.map (observe τ₁ W₁ VL₁ VR₁ B₁) = P₂.map (observe τ₂ W₂ VL₂ VR₂ B₂) := by
  have h := hE₁.map_observe_eq hE₂ ρL' ρR' hτ₁ hτ₂ hτ₁ζ hτ₂ζ hτ₁T hτ₂T hδ hlaw
  obtain ⟨h1p, -, -⟩ := hE₁.weightDrift_props ρL' ρR' hτ₁ hτ₁ζ hδ
  obtain ⟨h2p, -, -⟩ := hE₂.weightDrift_props ρL' ρR' hτ₂ hτ₂ζ hδ
  have hX₁ : Measurable (observe τ₁ W₁ VL₁ VR₁
      (girsanovProcess B₁ (weightDrift κ δ ρL ρL' ρR ρR' τ₁ ζ₁ W₁ VL₁ VR₁))) :=
    measurable_observe hτ₁ (hE₁.adapted_W.of_le hτ₁ hτ₁ζ) (fun i => (hE₁.adapted_VL i).of_le hτ₁ hτ₁ζ)
      (fun i => (hE₁.adapted_VR i).of_le hτ₁ hτ₁ζ) fun t =>
        ((hE₁.brownian.2.1 t).mono (𝓕₁.le t) le_rfl).add
          ((stronglyMeasurable_integral_comp h1p measurable_id t).measurable.mono (𝓕₁.le t) le_rfl)
  have hX₂ : Measurable (observe τ₂ W₂ VL₂ VR₂
      (girsanovProcess B₂ (weightDrift κ δ ρL ρL' ρR ρR' τ₂ ζ₂ W₂ VL₂ VR₂))) :=
    measurable_observe hτ₂ (hE₂.adapted_W.of_le hτ₂ hτ₂ζ) (fun i => (hE₂.adapted_VL i).of_le hτ₂ hτ₂ζ)
      (fun i => (hE₂.adapted_VR i).of_le hτ₂ hτ₂ζ) fun t =>
        ((hE₂.brownian.2.1 t).mono (𝓕₂.le t) le_rfl).add
          ((stronglyMeasurable_integral_comp h2p measurable_id t).measurable.mono (𝓕₂.le t) le_rfl)
  rw [← obsUnshift_observe B₁ hτ₁ζ, ← obsUnshift_observe B₂ hτ₂ζ,
    ← Measure.map_map (measurable_obsUnshift κ hδ ρL ρL' ρR ρR') hX₁,
    ← Measure.map_map (measurable_obsUnshift κ hδ ρL ρL' ρR ρR') hX₂, h]

/-- **The killed finite-dimensional laws agree** (the form of the frozen uniqueness statement
`IsIntegratedSLEEvolution.measure_killedState_eq`, with the localization `τ` in place of the
continuation threshold): under the hypotheses of `map_observe_eq`, for all times `t_1, …, t_n` and
Borel sets `A_j`, the events `{t_j < τ and (W, V^L, V^R, B)_{t_j} ∈ A_j for all j}` have the same
probability under `P₁` and `P₂`. -/
theorem IsSLEEvolutionUpTo.measure_killedState_eq_of_reverse [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂]
    (hE₁ : IsSLEEvolutionUpTo κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hE₂ : IsSLEEvolutionUpTo κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) (ρL' : Fin nL → ℝ)
    (ρR' : Fin nR → ℝ) (hτ₁ : ∀ s : ℝ≥0, MeasurableSet[𝓕₁ s] {ω | τ₁ ω ≤ s})
    (hτ₂ : ∀ s : ℝ≥0, MeasurableSet[𝓕₂ s] {ω | τ₂ ω ≤ s}) (hτ₁ζ : ∀ ω, τ₁ ω ≤ ζ₁ ω)
    (hτ₂ζ : ∀ ω, τ₂ ω ≤ ζ₂ ω) {T : ℝ≥0} (hτ₁T : ∀ ω, τ₁ ω ≤ T) (hτ₂T : ∀ ω, τ₂ ω ≤ T) {δ : ℝ}
    (hδ : 0 < δ)
    (hlaw : (girsanovMeasure P₁ 𝓕₁ B₁ (weightDrift κ δ ρL ρL' ρR ρR' τ₁ ζ₁ W₁ VL₁ VR₁) (T + 1)).map
        (observe τ₁ W₁ VL₁ VR₁ (girsanovProcess B₁ (weightDrift κ δ ρL ρL' ρR ρR' τ₁ ζ₁ W₁ VL₁ VR₁)))
      = (girsanovMeasure P₂ 𝓕₂ B₂ (weightDrift κ δ ρL ρL' ρR ρR' τ₂ ζ₂ W₂ VL₂ VR₂) (T + 1)).map
        (observe τ₂ W₂ VL₂ VR₂ (girsanovProcess B₂ (weightDrift κ δ ρL ρL' ρR ρR' τ₂ ζ₂ W₂ VL₂ VR₂))))
    (n : ℕ) (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ))
    (hA : ∀ j, MeasurableSet (A j)) :
    P₁ {ω | ∀ j, (ts j : ℝ≥0∞) < τ₁ ω ∧
        (W₁ (ts j) ω, (fun i => VL₁ i (ts j) ω), (fun i => VR₁ i (ts j) ω), B₁ (ts j) ω) ∈ A j} =
      P₂ {ω | ∀ j, (ts j : ℝ≥0∞) < τ₂ ω ∧
        (W₂ (ts j) ω, (fun i => VL₂ i (ts j) ω), (fun i => VR₂ i (ts j) ω), B₂ (ts j) ω) ∈ A j} := by
  have h := hE₁.map_observe_brownian_eq hE₂ ρL' ρR' hτ₁ hτ₂ hτ₁ζ hτ₂ζ hτ₁T hτ₂T hδ hlaw
  set S : Set (ObsSpace nL nR) := {e | ∀ j, (ts j : ℝ≥0∞) < e.2 ∧ e.1 (ts j) ∈ A j} with hS
  have hSm : MeasurableSet S := by
    rw [hS, ofPred_forall]
    exact MeasurableSet.iInter fun j => (measurableSet_lt measurable_const measurable_snd).inter
      (hA j |>.preimage ((measurable_pi_apply (ts j)).comp measurable_fst))
  have hX₁ : Measurable (observe τ₁ W₁ VL₁ VR₁ B₁) :=
    measurable_observe hτ₁ (hE₁.adapted_W.of_le hτ₁ hτ₁ζ) (fun i => (hE₁.adapted_VL i).of_le hτ₁ hτ₁ζ)
      (fun i => (hE₁.adapted_VR i).of_le hτ₁ hτ₁ζ) fun t =>
        (hE₁.brownian.2.1 t).mono (𝓕₁.le t) le_rfl
  have hX₂ : Measurable (observe τ₂ W₂ VL₂ VR₂ B₂) :=
    measurable_observe hτ₂ (hE₂.adapted_W.of_le hτ₂ hτ₂ζ) (fun i => (hE₂.adapted_VL i).of_le hτ₂ hτ₂ζ)
      (fun i => (hE₂.adapted_VR i).of_le hτ₂ hτ₂ζ) fun t =>
        (hE₂.brownian.2.1 t).mono (𝓕₂.le t) le_rfl
  rw [← observe_preimage_killedEvent ts A τ₁ W₁ VL₁ VR₁ B₁,
    ← observe_preimage_killedEvent ts A τ₂ W₂ VL₂ VR₂ B₂, ← hS, ← Measure.map_apply hX₁ hSm,
    ← Measure.map_apply hX₂ hSm, h]

end Transfer

end Sec2

end InteractingSLE
