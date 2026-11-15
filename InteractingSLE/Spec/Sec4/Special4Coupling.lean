/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Special4History
import InteractingSLE.Spec.Sec4.Special4Core
import InteractingSLE.Spec.Sec4.Special3Thin
import InteractingSLE.Spec.Ito.Loewner
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Foundations.Loewner.YuanCorollary13Slit

/-!
# Aux. lemma 23 at coupling level (Original-hull uniqueness when the finite hull is thin)

Packet PROVE-SEC4-A4, item (2). Specification Aux. lemma 23 (`source/spec/p097-144.md#aux-23`, p. 122): "Fix
`0 < κ < 4` and finite force data. Consider couplings with the original optional hull specification of Theorem 1.1,
with their own stopped driving histories retained as local marks. Fix a bounded own-filtration stopping rule `S < T_*`
whose common driving law has a continuous simple trace satisfying `η((0, S]) ⊂ ℍ`. Assume the strict interior dimension
bound of Aux. lemma 15 for this trace. Then every such coupling has the same joint law of the entire field and the
driving history through `S`."

The history through `S` is `stopHistory s (killedHistory …)` (`Special4History.lean`). The conditional characteristic
functional of the field off the hull and the hull are read from the history:

* `histDrive γ`, `histHarm κ ρL ρR γ`: the driver and the bounded harmonic extension of the boundary data at the
  recorded centred positions;
* `histCharFun κ ρL ρR φ γ = exp(i (𝔥_S, φ) − E_S(φ)/2)` and `histHull γ = closure(K_S) ∩ ℍ`;
* `IsContHist γ`: the history is recorded from a continuous driving state.

**Two deterministic measurability inputs remain** (`planning/handoffs/PROVE-SEC4-B3.md`, obstruction 1 (b) and (c)):
`HasMeasurableHistCharFun κ ρL ρR` (a Borel functional of the history agreeing with `histCharFun` on continuous
histories) and `HasMeasurableHistHull nL nR` (a relatively closed random set with Borel avoidance events agreeing with
`histHull` on continuous histories). They are measurability statements about Loewner functionals of a continuous
driving path; no probability enters.

* `IsOptionalHullCoupling.ae_condExp_hist`: in one coupling, at a stopping rule `S < ζ`, the frozen conditional-law
  clause reads `E[e^{i(h,φ)} | 𝓕_S] = histCharFun φ (history)` on the avoidance event;
* **`aux23_of_historyMeasurable`** (conditional helper; it replaces no source theorem): under Theorem 2.2's uniqueness
  in law for the word (`KilledStateLawUnique`, named until PROVE-SEC2-PATCH2 lands), the two measurability inputs, a
  common measurable stopping rule that is a stopping time `S < ζ` of each coupling's driving filtration, and, in the
  first coupling, a simple trace with `η((0, S]) ⊂ ℍ` and `dim_H(η([0, S]) ∩ ℍ) ≤ d < 2`, any two couplings with the
  frozen optional hull specification have the same joint law of the history through `S` and the field.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE

namespace Sec4

open LawUnique LQGMetric InteractingSLE.Sobolev

variable {nL nR : ℕ}

/-! ### Functionals of a history -/

/-- The driver of a history, as a real path (`histPath` at `r⁺`). -/
def histDrive (γ : HistorySpace nL nR) : ℝ → ℝ := fun r => histPath γ r.toNNReal

/-- The bounded harmonic extension of the boundary data at the recorded centred positions `V_S − W_S`. -/
def histHarm (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (γ : HistorySpace nL nR) : ℂ → ℝ :=
  Classical.choose (exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR
    (fun i => histVL γ i - histPath γ γ.1.toNNReal) (fun i => histVR γ i - histPath γ γ.1.toNNReal))

theorem histHarm_spec (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (γ : HistorySpace nL nR) :
    IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => histVL γ i - histPath γ γ.1.toNNReal)
        (fun i => histVR γ i - histPath γ γ.1.toNNReal))
      (forceJumpSet (fun i => histVL γ i - histPath γ γ.1.toNNReal)
        (fun i => histVR γ i - histPath γ γ.1.toNNReal)) (histHarm κ ρL ρR γ) :=
  Classical.choose_spec (exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR _ _)

/-- **The conditional characteristic functional off the hull, read from a history**: the right-hand side
`exp(i (𝔥_S, φ) − E_S(φ)/2)` of the frozen optional hull specification at the recorded stop. -/
def histCharFun (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (φ : TestOn upperHalfPlaneOpens)
    (γ : HistorySpace nL nR) : ℂ :=
  Complex.exp (Complex.I * ((∫ z, couplingMean κ (histDrive γ) (γ.1.toNNReal : ℝ)
      (histHarm κ ρL ρR γ) z * φ z : ℝ) : ℂ) -
    (((1 / 2 : ℝ) * loewnerGreenEnergy (histDrive γ) (γ.1.toNNReal : ℝ) φ : ℝ) : ℂ))

/-- **The hull at the recorded stop, closed in `ℍ`**. -/
def histHull (γ : HistorySpace nL nR) : Set ℂ :=
  closure (QuantumZipper.fwdHull (histDrive γ) (γ.1.toNNReal : ℝ)) ∩ (upperHalfPlaneOpens : Set ℂ)

/-- A history recorded from a continuous driving state through its (finite) recorded stop. -/
def IsContHist (γ : HistorySpace nL nR) : Prop :=
  γ.1 ≠ ⊤ ∧ ∃ f : ℝ≥0 → DrivingValue nL nR, Continuous f ∧
    ∀ p, dyadicTime p ≤ γ.1.toNNReal → γ.2 p = f (dyadicTime p)

/-- **Missing input (b)** (deterministic): a Borel functional of the history that is the conditional characteristic
functional `histCharFun` on every continuous history whose hull avoids `supp φ`. (Only there is `histCharFun` free of
junk values: every point of `supp φ` is then alive at the stop, its image lies in `ℍ`, where the bounded harmonic
extension is unique.) -/
def HasMeasurableHistCharFun (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  ∃ G : TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ, (∀ φ, Measurable (G φ)) ∧
    ∀ (φ : TestOn upperHalfPlaneOpens) (γ : HistorySpace nL nR), IsContHist γ →
      Disjoint (tsupport φ) (histHull γ) → G φ γ = histCharFun κ ρL ρR φ γ

/-- **Missing input (c)** (deterministic): a random set, relatively closed in `ℍ`, with Borel avoidance events of
compact sets, that is the hull `histHull` on every continuous history. -/
def HasMeasurableHistHull (nL nR : ℕ) : Prop :=
  ∃ A : HistorySpace nL nR → Set ℂ,
    (∀ K : Set ℂ, IsCompact K → MeasurableSet {γ | Disjoint K (A γ)}) ∧
      (∀ γ, closure (A γ) ∩ (upperHalfPlaneOpens : Set ℂ) ⊆ A γ) ∧
        ∀ γ, IsContHist γ → A γ = histHull γ

/-! ### The history of a path continuous before its lifetime -/

section Path

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {s : HistorySpace nL nR → ℝ≥0} {ω : Ω}

/-- The pathwise conditions used at a stop `S < ζ`. -/
def IsGoodStop (s : HistorySpace nL nR → ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  (s (killedHistory W VL VR ζ ω) : ℝ≥0∞) < ζ ω ∧
    ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      (∀ i, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
        ∀ i, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω}

theorem stopHistory_fst_toNNReal (γ : HistorySpace nL nR) :
    (stopHistory s γ).1.toNNReal = s γ := by
  rw [stopHistory_fst, ENNReal.toNNReal_coe]

/-- A function continuous before `ζ`, stopped at `S < ζ`, is continuous. -/
theorem continuous_stopped {f : ℝ≥0 → ℝ} {a : ℝ≥0∞} (hf : ContinuousOn f {t : ℝ≥0 | (t : ℝ≥0∞) < a})
    {S : ℝ≥0} (hS : (S : ℝ≥0∞) < a) : Continuous fun t => f (min t S) :=
  hf.comp_continuous (continuous_id.min continuous_const) fun t =>
    lt_of_le_of_lt (by exact_mod_cast min_le_right t S) hS

/-- The history through a good stop is a continuous history. -/
theorem isContHist_stopHistory (hg : IsGoodStop s W VL VR ζ ω) :
    IsContHist (stopHistory s (killedHistory W VL VR ζ ω)) := by
  obtain ⟨hlt, hWc, hVLc, hVRc⟩ := hg
  set S := s (killedHistory W VL VR ζ ω) with hSdef
  refine ⟨by rw [stopHistory_fst]; exact ENNReal.coe_ne_top,
    fun t => (W (min t S) ω, (fun i => VL i (min t S) ω), fun i => VR i (min t S) ω), ?_, ?_⟩
  · exact (continuous_stopped hWc hlt).prodMk
      ((continuous_pi fun i => continuous_stopped (hVLc i) hlt).prodMk
        (continuous_pi fun i => continuous_stopped (hVRc i) hlt))
  · intro p hp
    rw [stopHistory_fst_toNNReal] at hp
    rw [stopHistory_killedHistory_snd hp hlt]
    rw [← hSdef] at hp
    simp only [min_eq_left hp]

/-- On a good stop, the driver of the history is `W_{r⁺ ∧ S}`. -/
theorem histDrive_stopHistory (hlt : (s (killedHistory W VL VR ζ ω) : ℝ≥0∞) < ζ ω)
    (hWc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω}) :
    histDrive (stopHistory s (killedHistory W VL VR ζ ω)) =
      fun r => W (min r.toNNReal (s (killedHistory W VL VR ζ ω))) ω := by
  funext r
  exact histPath_stopHistory hlt hWc r.toNNReal

/-- On a good stop, the driver of the history agrees with `W` on `[0, S]`. -/
theorem eqOn_histDrive (hg : IsGoodStop s W VL VR ζ ω) :
    EqOn (fun r : ℝ => W r.toNNReal ω) (histDrive (stopHistory s (killedHistory W VL VR ζ ω)))
      (Icc 0 (s (killedHistory W VL VR ζ ω) : ℝ)) := by
  intro r hr
  rw [histDrive_stopHistory hg.1 hg.2.1]
  simp only
  rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]

/-- **On a good stop, the hull of the history is the hull of the driver** at `S`. -/
theorem fwdHull_histDrive (hg : IsGoodStop s W VL VR ζ ω) :
    QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) (s (killedHistory W VL VR ζ ω) : ℝ) =
      QuantumZipper.fwdHull (histDrive (stopHistory s (killedHistory W VL VR ζ ω)))
        (s (killedHistory W VL VR ζ ω) : ℝ) := by
  obtain ⟨hlt, hWc, -, -⟩ := hg
  set S := s (killedHistory W VL VR ζ ω) with hSdef
  obtain ⟨t₂, hSt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
  have hSt₂' : S < t₂ := by exact_mod_cast hSt₂
  set V : ℝ → ℝ := fun r => W (min r.toNNReal t₂) ω with hVdef
  have hVc : Continuous V := (continuous_stopped hWc ht₂ζ).comp continuous_real_toNNReal
  have h1 : QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) S = QuantumZipper.fwdHull V S := by
    refine fwdHull_eq_of_eqOn S.coe_nonneg (by exact_mod_cast hSt₂') fun r hr => ?_
    simp only [hVdef]
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]
  have hHc : Continuous (histDrive (stopHistory s (killedHistory W VL VR ζ ω))) := by
    rw [histDrive_stopHistory hlt hWc]
    exact (continuous_stopped hWc hlt).comp continuous_real_toNNReal
  rw [h1]
  refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc hVc hHc S.coe_nonneg fun r hr => ?_
  rw [histDrive_stopHistory hlt hWc]
  simp only [hVdef]
  have hrS : r.toNNReal ≤ S := Real.toNNReal_le_iff_le_coe.2 hr.2
  rw [min_eq_left (hrS.trans hSt₂'.le), min_eq_left hrS]

end Path

/-! ### The conditional-law clause in one coupling, read from the history -/

section Coupling

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- Almost every stop `S < ζ` of an evolution is good. -/
theorem ae_isGoodStop_of_evolution {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {s : HistorySpace nL nR → ℝ≥0}
    (hSζ : ∀ᵐ ω ∂P, (s (killedHistory W VL VR ζ ω) : ℝ≥0∞) < ζ ω) :
    ∀ᵐ ω ∂P, IsGoodStop s W VL VR ζ ω := by
  filter_upwards [hSζ, hE.2.2.2.2] with ω h1 hp
  exact ⟨h1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1⟩

/-- On a good stop, the frozen conditional mean and energy at `S` are those read from the history. -/
theorem integral_couplingMean_histDrive {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : HistorySpace nL nR → ℝ≥0} {ω : Ω}
    (hg : IsGoodStop s W VL VR ζ ω) (u : ℂ → ℝ) (φ : TestOn upperHalfPlaneOpens) :
    (∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) (s (killedHistory W VL VR ζ ω) : ℝ) u z * φ z) =
      ∫ z, couplingMean κ (histDrive (stopHistory s (killedHistory W VL VR ζ ω)))
        (s (killedHistory W VL VR ζ ω) : ℝ) u z * φ z := by
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [couplingMean]
  rw [Ito.fwdMap_congr_of_eqOn (eqOn_histDrive hg),
    Ito.logDerivFwd_congr_of_eqOn (eqOn_histDrive hg) (NNReal.coe_nonneg _) le_rfl]

theorem loewnerGreenEnergy_histDrive {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : HistorySpace nL nR → ℝ≥0} {ω : Ω}
    (hg : IsGoodStop s W VL VR ζ ω) (φ : ℂ → ℝ) :
    loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω) (s (killedHistory W VL VR ζ ω) : ℝ) φ =
      loewnerGreenEnergy (histDrive (stopHistory s (killedHistory W VL VR ζ ω)))
        (s (killedHistory W VL VR ζ ω) : ℝ) φ := by
  unfold loewnerGreenEnergy
  simp_rw [Ito.fwdMap_congr_of_eqOn (eqOn_histDrive hg)]

/-- On a good stop, the hull of the driver at `S` is inside the hull read from the history. -/
theorem fwdHull_subset_histHull {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : HistorySpace nL nR → ℝ≥0} {ω : Ω}
    (hg : IsGoodStop s W VL VR ζ ω) :
    QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) (s (killedHistory W VL VR ζ ω) : ℝ) ⊆
      histHull (stopHistory s (killedHistory W VL VR ζ ω)) := by
  rw [fwdHull_histDrive hg]
  intro z hz
  refine ⟨?_, hz.1⟩
  rw [stopHistory_fst_toNNReal]
  exact subset_closure hz

/-- On a good stop, the hull read from the history is the closure of the driver's hull in `ℍ`. -/
theorem histHull_stopHistory {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : HistorySpace nL nR → ℝ≥0} {ω : Ω}
    (hg : IsGoodStop s W VL VR ζ ω) :
    histHull (stopHistory s (killedHistory W VL VR ζ ω)) =
      closure (QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) (s (killedHistory W VL VR ζ ω) : ℝ)) ∩
        (upperHalfPlaneOpens : Set ℂ) := by
  rw [histHull, stopHistory_fst_toNNReal, fwdHull_histDrive hg]

/-- **The conditional-law clause read from the history.** In a coupling with the frozen optional hull
specification, at a stopping rule `S < ζ` of the driving filtration, almost surely on the event that `supp φ` avoids
the hull read from the history, `E[e^{i(h, φ)} | 𝓕_S]` is the functional `G φ` of the history through `S`, for every
`G` that is `histCharFun` on continuous histories avoiding `supp φ` and every `A` that is `histHull` on continuous
histories. -/
theorem _root_.InteractingSLE.IsOptionalHullCoupling.ae_condExp_hist {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {A : HistorySpace nL nR → Set ℂ} (hAeq : ∀ γ, IsContHist γ → A γ = histHull γ)
    {G : TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ}
    (hGeq : ∀ (φ : TestOn upperHalfPlaneOpens) (γ : HistorySpace nL nR), IsContHist γ →
      Disjoint (tsupport φ) (histHull γ) → G φ γ = histCharFun κ ρL ρR φ γ)
    {s : HistorySpace nL nR → ℝ≥0} (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hS : IsStoppingTime (drivingFiltration P hX) (ruleTime s W VL VR ζ))
    (hSζ : ∀ᵐ ω ∂P, (s (killedHistory W VL VR ζ ω) : ℝ≥0∞) < ζ ω)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ o ∂P, Disjoint (tsupport φ) (A (stopHistory s (killedHistory W VL VR ζ o))) →
      P[fun o => Complex.exp (↑(h o φ) * Complex.I) | hS.measurableSpace] o =
        G φ (stopHistory s (killedHistory W VL VR ζ o)) := by
  classical
  have hgood := ae_isGoodStop_of_evolution hC.1 hSζ
  obtain ⟨-, -, -, hX', hτ⟩ := hC
  let u : Ω → ℂ → ℝ := fun o => if IsGoodStop s W VL VR ζ o then
      histHarm κ ρL ρR (stopHistory s (killedHistory W VL VR ζ o)) else
    Classical.choose (exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR
      (fun i => VL i (s (killedHistory W VL VR ζ o)) o - W (s (killedHistory W VL VR ζ o)) o)
      (fun i => VR i (s (killedHistory W VL VR ζ o)) o - W (s (killedHistory W VL VR ζ o)) o))
  have hu : ∀ o, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR
        (fun i => VL i (s (killedHistory W VL VR ζ o)) o - W (s (killedHistory W VL VR ζ o)) o)
        (fun i => VR i (s (killedHistory W VL VR ζ o)) o - W (s (killedHistory W VL VR ζ o)) o))
      (forceJumpSet
        (fun i => VL i (s (killedHistory W VL VR ζ o)) o - W (s (killedHistory W VL VR ζ o)) o)
        (fun i => VR i (s (killedHistory W VL VR ζ o)) o - W (s (killedHistory W VL VR ζ o)) o))
      (u o) := by
    intro o
    by_cases hg : IsGoodStop s W VL VR ζ o
    · have hspec := histHarm_spec κ ρL ρR (stopHistory s (killedHistory W VL VR ζ o))
      have hW : histPath (stopHistory s (killedHistory W VL VR ζ o))
          (stopHistory s (killedHistory W VL VR ζ o)).1.toNNReal =
          W (s (killedHistory W VL VR ζ o)) o := by
        rw [stopHistory_fst_toNNReal, histPath_stopHistory hg.1 hg.2.1, min_self]
      have hL : (fun i => histVL (stopHistory s (killedHistory W VL VR ζ o)) i -
          histPath (stopHistory s (killedHistory W VL VR ζ o))
            (stopHistory s (killedHistory W VL VR ζ o)).1.toNNReal) =
          fun i => VL i (s (killedHistory W VL VR ζ o)) o - W (s (killedHistory W VL VR ζ o)) o := by
        funext i
        rw [hW, histVL_stopHistory hg.1 hg.2.2.1]
      have hR : (fun i => histVR (stopHistory s (killedHistory W VL VR ζ o)) i -
          histPath (stopHistory s (killedHistory W VL VR ζ o))
            (stopHistory s (killedHistory W VL VR ζ o)).1.toNNReal) =
          fun i => VR i (s (killedHistory W VL VR ζ o)) o - W (s (killedHistory W VL VR ζ o)) o := by
        funext i
        rw [hW, histVR_stopHistory hg.1 hg.2.2.2]
      rw [hL, hR] at hspec
      simp only [u, hg, ↓reduceIte]
      exact hspec
    · simp only [u, hg, ↓reduceIte]
      exact Classical.choose_spec (exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR _ _)
  have hcl := (hτ (ruleTime s W VL VR ζ) hS hSζ).2 u hu φ
  filter_upwards [hcl, hgood] with o ho hg hdisj
  have hcont := isContHist_stopHistory hg
  rw [hAeq _ hcont] at hdisj
  have hK := hdisj.mono_right (fwdHull_subset_histHull hg)
  have h1 := ho hK
  rw [hGeq _ _ hcont hdisj]
  have hfun : (fun o => Complex.exp (↑(h o φ) * Complex.I)) =
      fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) := by
    funext o
    rw [mul_comm]
  rw [hfun]
  refine h1.trans ?_
  have hu' : u o = histHarm κ ρL ρR (stopHistory s (killedHistory W VL VR ζ o)) := ite_eq_left hg
  unfold histCharFun
  rw [stopHistory_fst_toNNReal, ← integral_couplingMean_histDrive hg, ← loewnerGreenEnergy_histDrive hg,
    ← hu']
  rfl

end Coupling

/-! ### Aux. lemma 23 at coupling level -/

/-- **Aux. lemma 23 at coupling level** (Original-hull uniqueness when the finite hull is thin; conditional helper, it
replaces no source theorem). Assume Theorem 2.2's uniqueness in law for the word (`KilledStateLawUnique`) and the two
deterministic measurability inputs `HasMeasurableHistCharFun`, `HasMeasurableHistHull`. Fix a measurable stopping rule
`s` of the killed driving history that gives, in each coupling, a stopping time `S < ζ` of its driving filtration, and
suppose that in the first coupling the driving trace is almost surely simple on `[0, S]` with `η((0, S]) ⊂ ℍ` and
`dim_H(η([0, S]) ∩ ℍ) ≤ d < 2` (the strict interior dimension bound of Aux. lemma 15). Then any two couplings with the
frozen optional hull specification have the same joint law of the driving history through `S` and the entire field. -/
theorem aux23_of_historyMeasurable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hU : KilledStateLawUnique.{u, v} κ xL xR ρL ρR)
    (hGm : HasMeasurableHistCharFun κ ρL ρR) (hAm : HasMeasurableHistHull nL nR)
    {s : HistorySpace nL nR → ℝ≥0} (hs : Measurable s) {d : ℝ} (hd : d < 2)
    {Ω₁ : Type u} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    {h₁ : Ω₁ → DistOn upperHalfPlaneOpens}
    (hC₁ : IsOptionalHullCoupling κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (hS₁ : ∀ hX : IsMeasurableKilledDriving W₁ VL₁ VR₁ ζ₁,
      IsStoppingTime (drivingFiltration P₁ hX) (ruleTime s W₁ VL₁ VR₁ ζ₁))
    (hSζ₁ : ∀ᵐ ω ∂P₁, (s (killedHistory W₁ VL₁ VR₁ ζ₁ ω) : ℝ≥0∞) < ζ₁ ω)
    (htr₁ : ∀ᵐ ω ∂P₁, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₁ t ω) (ζ₁ ω) η ∧
      InjOn η (Icc 0 (s (killedHistory W₁ VL₁ VR₁ ζ₁ ω))) ∧
      (∀ t ∈ Ioc 0 (s (killedHistory W₁ VL₁ VR₁ ζ₁ ω)), η t ∈ QuantumZipper.H) ∧
      dimH (η '' Icc 0 (s (killedHistory W₁ VL₁ VR₁ ζ₁ ω)) ∩ QuantumZipper.H) ≤ ENNReal.ofReal d)
    {Ω₂ : Type v} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hC₂ : IsOptionalHullCoupling κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂)
    (hS₂ : ∀ hX : IsMeasurableKilledDriving W₂ VL₂ VR₂ ζ₂,
      IsStoppingTime (drivingFiltration P₂ hX) (ruleTime s W₂ VL₂ VR₂ ζ₂))
    (hSζ₂ : ∀ᵐ ω ∂P₂, (s (killedHistory W₂ VL₂ VR₂ ζ₂ ω) : ℝ≥0∞) < ζ₂ ω) :
    P₁.map (fun ω => (stopHistory s (killedHistory W₁ VL₁ VR₁ ζ₁ ω), h₁ ω)) =
      P₂.map (fun ω => (stopHistory s (killedHistory W₂ VL₂ VR₂ ζ₂ ω), h₂ ω)) := by
  obtain ⟨G, hGmeas, hGeq⟩ := hGm
  obtain ⟨A, hAmeas, hAcl, hAeq⟩ := hAm
  obtain ⟨hX₁, -⟩ := hC₁.2.2.2
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  set ε : ℝ := min (1 / 2) ((2 - d) / 4) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hdε : d < 2 - 2 * ε := by
    have := min_le_right (1 / 2 : ℝ) ((2 - d) / 4)
    linarith
  have hgood₁ := ae_isGoodStop_of_evolution hC₁.1 hSζ₁
  refine map_prod_eq_of_condCharFun_off_ae (U := upperHalfPlaneOpens) hε0 hε1 hAcl hAmeas hGmeas
    hC₁.2.1 ((measurable_stopHistory hs).comp (measurable_killedHistory hX₁))
    (measurable_stopHistory_killedHistory hX₁ (hS₁ hX₁)).comap_le (hS₁ hX₁).measurableSpace_le
    (fun ζc => hC₁.lintegral_negSobolevSq_lt_top hε0 ζc)
    (fun φ => hC₁.ae_condExp_hist hAeq hGeq hX₁ (hS₁ hX₁) hSζ₁ φ)
    hC₂.2.1 ((measurable_stopHistory hs).comp (measurable_killedHistory hX₂))
    (measurable_stopHistory_killedHistory hX₂ (hS₂ hX₂)).comap_le (hS₂ hX₂).measurableSpace_le
    (fun ζc => hC₂.lintegral_negSobolevSq_lt_top hε0 ζc)
    (fun φ => hC₂.ae_condExp_hist hAeq hGeq hX₂ (hS₂ hX₂) hSζ₂ φ)
    (map_stopHistory_eq hU hs hC₁.1 hX₁ hC₂.1 hX₂) ?_
  filter_upwards [htr₁, hgood₁] with ω hω hg K _ _
  obtain ⟨η, hη, hinj, hH, hdim⟩ := hω
  rw [Function.comp_apply, hAeq _ (isContHist_stopHistory hg), histHull_stopHistory hg]
  calc dimH (closure (QuantumZipper.fwdHull (fun r : ℝ => W₁ r.toNNReal ω)
          (s (killedHistory W₁ VL₁ VR₁ ζ₁ ω) : ℝ)) ∩ (upperHalfPlaneOpens : Set ℂ) ∩ K)
      ≤ dimH (QuantumZipper.fwdHull (fun r : ℝ => W₁ r.toNNReal ω)
          (s (killedHistory W₁ VL₁ VR₁ ζ₁ ω) : ℝ) ∩ K) :=
        dimH_mono (inter_subset_inter_left _ (closure_fwdHull_inter_H_subset hη hg.1 hinj hH))
    _ < ENNReal.ofReal (2 - 2 * ε) := dimH_fwdHull_inter_lt hη hg.1 hinj hH hdim hdε hε1 K

end Sec4

end InteractingSLE
