import InteractingSLE.Spec.Supplement.LP4HalfBallFuture
import InteractingSLE.Spec.Supplement.LP2Loc
import InteractingSLE.Spec.Supplement.LP4ZeroOne

/-!
# LP4's half-ball statement from swallowed points on both sides

Packet PROVE-LP17. Specification pp. 482–483 (proof of Proposition LP4). The proof has two halves:

1. "First obtain a positive-probability finite own stopping time at which the physical leftmost and rightmost
   swallowed real points straddle `0` strictly." — the **straddle input** `LP4StraddleStatement` (named here: with
   positive probability, some finite time has swallowed real points on both sides of `0`).
2. The collar step: at such a time, the inverse fibre of `0` is a compact subset of the open force interval; LP3,
   bounded-energy Girsanov and Zhan's stopping-time collar give a half-ball around `0` in a later hull.

This file proves **2 ⇒ `LP4HalfBallStatement`**, given the straddle input and the stopping-time collar
(`ZhanGT4.StoppingCollarStatement`, the named input of PROVE-ZHAN-GT4-A6):

* `exists_params_of_straddle` (pathwise): once real points on both sides are swallowed by `T`, at some rational
  `σ > T` with no collision the cluster condition holds with rational parameters inside the force interval
  (`LP4HB.exists_cluster_of_path`, `Swallow.clusterCondQ_of_forall`);
* the events of these rational parameters are measurable for the null-augmented filtration at `σ`
  (QuantumZipper's tamed flows, `measurableSet_clusterCondQ`, on the paths modified off a null set);
* one of them has positive probability, and `LP4HB.frequently_halfBall_of_cluster` finishes.

**`lp4HalfBallStatement_of_straddle`**: `(∀ κ > 4, StoppingCollarStatement κ) → LP4StraddleStatement →
LP4HalfBallStatement`; with PROVE-LP16's `lp4AvoidStatement_of_halfBall` and PROVE-LP14's `lp4Statement_of_avoid`,
also `LP4AvoidStatement` and `LP4Statement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper QuantumZipper.RS

universe u

namespace InteractingSLE.LP

/-! ### The straddle input -/

/-- **Named input: real points swallowed on both sides** (the first half of the proof of LP4, specification p. 482:
"a positive-probability finite own stopping time at which the physical leftmost and rightmost swallowed real points
straddle `0` strictly"). Hypotheses as in `LP4HalfBallStatement`. Conclusion: for every two-seed evolution, with
positive probability some finite time `T` has swallowed real points `y₁ < 0 < y₂`. -/
def LP4StraddleStatement : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 2 → -2 < rR → rR < κ / 2 - 2 →
    (∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
        ∃ᵐ ω ∂P, ∃ T : ℝ≥0, ∃ y₁ y₂ : ℝ, y₁ < 0 ∧ 0 < y₂ ∧
          ZhanGT4.IsSwallowedBy (fun s : ℝ => W s.toNNReal ω) y₁ T ∧
          ZhanGT4.IsSwallowedBy (fun s : ℝ => W s.toNNReal ω) y₂ T

namespace LP4HB

/-! ### Rational parameters -/

/-- The restart time of a parameter vector `p = (σ, ε, ℓq, pm, m₁, m₂, pp, rq, δ)`. -/
def sigmaOf (p : Fin 9 → ℚ) : ℝ≥0 := ((p 0 : ℚ) : ℝ).toNNReal

/-- The order conditions on a parameter vector. -/
def GoodParams (p : Fin 9 → ℚ) : Prop :=
  (0 : ℝ) < p 1 ∧ ((p 2 : ℚ) : ℝ) < p 3 ∧ ((p 3 : ℚ) : ℝ) < 0 ∧ ((p 3 : ℚ) : ℝ) < p 4 ∧
    ((p 5 : ℚ) : ℝ) < p 6 ∧ (0 : ℝ) < p 6 ∧ ((p 6 : ℚ) : ℝ) < p 7 ∧ (0 : ℝ) < p 8

/-- The pathwise event of a parameter vector: the force coordinates at `σ` lie `δ` beyond `ℓq` and `rq`, and the
countable cluster condition holds at `σ` with the interval `[m₁, m₂]`. -/
def ParamEvent (W : ℝ → ℝ) (vL vR : ℝ) (p : Fin 9 → ℚ) : Prop :=
  vL < ((p 2 : ℚ) : ℝ) - p 8 ∧ ((p 7 : ℚ) : ℝ) + p 8 < vR ∧
    ClusterCondQ W (sigmaOf p) (p 1) (-((p 4 : ℚ) : ℝ)) (-((p 5 : ℚ) : ℝ))

/-- **Rational parameters from swallowed points on both sides** (pathwise). For a frozen two-seed path with infinite
lifetime and a generating trace, if real points `y₁ < 0 < y₂` are swallowed by `T`, some good parameter vector has its
event, at a rational time `σ > T` where neither force touches the driver. -/
theorem exists_params_of_straddle {a : ℝ} {xL xR ρL ρR : Fin 1 → ℝ} (hxL : xL 0 = 0) (hxR : xR 0 = 0)
    {w : ℝ≥0 → ℝ} {vL vR : Fin 1 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ⊤) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η)
    {T : ℝ≥0} {y₁ y₂ : ℝ} (hy₁ : y₁ < 0) (hy₂ : 0 < y₂)
    (hd₁ : ZhanGT4.IsSwallowedBy (fun s : ℝ => w s.toNNReal) y₁ T)
    (hd₂ : ZhanGT4.IsSwallowedBy (fun s : ℝ => w s.toNNReal) y₂ T) :
    ∃ p : Fin 9 → ℚ, GoodParams p ∧
      ParamEvent (fun s : ℝ => w s.toNNReal) (vL 0 (sigmaOf p) - w (sigmaOf p))
        (vR 0 (sigmaOf p) - w (sigmaOf p)) p := by
  have hp' := hp
  obtain ⟨hwc, hw0⟩ := Sec7.IsIntegratedSLEPath.continuous_w_of_top hp
  obtain ⟨-, -, -, -, hvLc, hvRc, -, hvLw, hwvR, -, -, -, -, -, -, hcolL, hcolR, -⟩ := hp'
  have hvLc' : Continuous (vL 0) := continuousOn_univ.1 (by simpa using hvLc 0)
  have hvRc' : Continuous (vR 0) := continuousOn_univ.1 (by simpa using hvRc 0)
  -- a rational time after `T` without collision
  set C : Set ℝ := {s | w s.toNNReal = vL 0 s.toNNReal} ∪ {s | w s.toNNReal = vR 0 s.toNNReal} with hC
  have hCc : IsClosed C :=
    (isClosed_eq (hwc.comp continuous_real_toNNReal) (hvLc'.comp continuous_real_toNNReal)).union
      (isClosed_eq (hwc.comp continuous_real_toNNReal) (hvRc'.comp continuous_real_toNNReal))
  have hCnull : MeasureTheory.volume (C ∩ Ici 0) = 0 := by
    refine measure_mono_null (fun s hs => ?_) (measure_union_null (hcolL 0) (hcolR 0))
    rcases hs.1 with h | h
    · exact Or.inl ⟨hs.2, ENNReal.coe_lt_top, h⟩
    · exact Or.inr ⟨hs.2, ENNReal.coe_lt_top, h⟩
  set O : Set ℝ := Ioo (T : ℝ) (T + 1) \ C with hO
  have hOo : IsOpen O := isOpen_Ioo.sdiff hCc
  have hOne : O.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, hO, sdiff_eq_empty] at hne
    have hsub : Ioo (T : ℝ) (T + 1) ⊆ interior (C ∩ Ici 0) :=
      interior_maximal (fun s hs => ⟨hne hs, (T.coe_nonneg.trans hs.1.le)⟩) isOpen_Ioo
    rw [Measure.interior_eq_empty_of_null hCnull] at hsub
    exact (nonempty_Ioo.2 (lt_add_one (T : ℝ))).ne_empty (subset_empty_iff.1 hsub)
  obtain ⟨σq, hσO⟩ := Rat.denseRange_cast.exists_mem_open hOo hOne
  have hσ0 : (0 : ℝ) ≤ σq := T.coe_nonneg.trans hσO.1.1.le
  set σ : ℝ≥0 := ((σq : ℚ) : ℝ).toNNReal with hσdef
  have hσσ : (σ : ℝ) = σq := Real.coe_toNNReal _ hσ0
  have hσT : (T : ℝ) ≤ σ := by rw [hσσ]; exact hσO.1.1.le
  have hnc : w σ ≠ vL 0 σ ∧ w σ ≠ vR 0 σ := by
    have h := hσO.2
    simp only [hC, mem_union, mem_ofPred_eq, not_or] at h
    exact h
  -- the swallowed points at `σ`
  have hd₁' : ZhanGT4.IsSwallowedBy (fun s : ℝ => w s.toNNReal) y₁ σ := fun ⟨v, hv⟩ =>
    hd₁ ⟨v, QuantumZipper.isForwardSol_restrict hv T.coe_nonneg hσT⟩
  have hd₂' : ZhanGT4.IsSwallowedBy (fun s : ℝ => w s.toNNReal) y₂ σ := fun ⟨v, hv⟩ =>
    hd₂ ⟨v, QuantumZipper.isForwardSol_restrict hv T.coe_nonneg hσT⟩
  obtain ⟨ε₀, hε₀, m₁, m₂, hm₁, hm₂, hcl⟩ := exists_cluster_of_path hxL hxR hp hη σ hy₁ hy₂ hd₁' hd₂'
  set ℓ : ℝ := vL 0 σ - w σ with hℓ
  set r : ℝ := vR 0 σ - w σ with hr
  have hℓ0 : ℓ < 0 := by
    have h1 := hvLw σ (by simp) 0
    have h2 := hnc.1
    rw [hℓ]; exact sub_neg.2 (lt_of_le_of_ne h1 (Ne.symm h2))
  have hr0 : 0 < r := by
    have h1 := hwvR σ (by simp) 0
    rw [hr]; exact sub_pos.2 (lt_of_le_of_ne h1 hnc.2)
  -- the rational parameters
  obtain ⟨pm, hpm1, hpm2⟩ := exists_rat_btwn (lt_min hm₁ hℓ0)
  obtain ⟨ℓq, hℓq1, hℓq2⟩ := exists_rat_btwn hpm1
  obtain ⟨m₁q, hm₁q1, hm₁q2⟩ := exists_rat_btwn (hpm2.trans_le (min_le_left _ _))
  obtain ⟨pp, hpp1, hpp2⟩ := exists_rat_btwn (max_lt hm₂ hr0)
  obtain ⟨rq, hrq1, hrq2⟩ := exists_rat_btwn hpp2
  obtain ⟨m₂q, hm₂q1, hm₂q2⟩ := exists_rat_btwn ((le_max_left _ _).trans_lt hpp1)
  obtain ⟨δq, hδq1, hδq2⟩ := exists_rat_btwn (lt_min (sub_pos.2 hℓq1) (sub_pos.2 hrq2))
  obtain ⟨εq, hεq1, hεq2⟩ := exists_rat_btwn hε₀
  refine ⟨![σq, εq, ℓq, pm, m₁q, m₂q, pp, rq, δq], ?_, ?_⟩
  · simp only [GoodParams, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    refine ⟨by exact_mod_cast hεq1, hℓq2, hpm2.trans_le (min_le_right _ _), hm₁q1, hm₂q2,
      (le_max_right _ _).trans_lt hpp1, hrq1, by exact_mod_cast hδq1⟩
  · have hsig : sigmaOf ![σq, εq, ℓq, pm, m₁q, m₂q, pp, rq, δq] = σ := by
      simp [sigmaOf, hσdef]
    simp only [ParamEvent, hsig, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    refine ⟨by linarith [min_le_left (((ℓq : ℚ) : ℝ) - ℓ) (r - rq)],
      by linarith [min_le_right (((ℓq : ℚ) : ℝ) - ℓ) (r - rq)], ?_⟩
    refine InteractingSLE.clusterCondQ_of_forall (hwc.comp continuous_real_toNNReal) σ.coe_nonneg
      fun z hz hzn => ?_
    have h := hcl z hz (hzn.trans hεq2)
    have e : (w ∘ Real.toNNReal) = fun s : ℝ => w s.toNNReal := rfl
    simp only [e, neg_neg]
    constructor <;> linarith [h.1, h.2]


/-! ### The measurable parameter events -/

variable {κ rL rR : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The half-ball with positive probability from the straddle**, for one two-seed evolution (given the stopping-time
collar and a generating trace on the lifetime). -/
theorem frequently_halfBall_of_straddle [IsProbabilityMeasure P] (hκ : 4 < κ) (hL : -2 < rL)
    (hR : -2 < rR) (hcol : ZhanGT4.StoppingCollarStatement.{u} κ)
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    (hst : ∃ᵐ ω ∂P, ∃ T : ℝ≥0, ∃ y₁ y₂ : ℝ, y₁ < 0 ∧ 0 < y₂ ∧
      ZhanGT4.IsSwallowedBy (fun s : ℝ => W s.toNNReal ω) y₁ T ∧
      ZhanGT4.IsSwallowedBy (fun s : ℝ => W s.toNNReal ω) y₂ T) :
    ∃ᵐ ω ∂P, ∃ T : ℝ≥0, ∃ ε > (0 : ℝ), ∀ z ∈ H, ‖z‖ < ε →
      z ∈ fwdHull (fun s : ℝ => W s.toNNReal ω) T := by
  have hκ0 : 0 < κ := by linarith
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ :=
    Sec7.ae_lifetime_eq_top_twoSeed (ρL := fun _ => rL) (ρR := fun _ => rR) hκ0 hL hR
      Sec7.jacobiDiffusionExistsStatement hE
  -- a measurable good set
  obtain ⟨G, hGm, hGc, hGp⟩ := LP2.exists_measurableSet_subset_of_ae (P := P)
    (p := fun ω => ζ ω = ⊤ ∧ IsIntegratedSLEPath κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR)
      (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (fun t => B t ω) ⊤ ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η) (by
    filter_upwards [hζ, hE.2.2.2.2, htr] with ω h1 h2 h3
    rw [h1] at h2 h3
    exact ⟨h1, h2, h3⟩)
  have hGζ : ∀ ω ∈ G, ζ ω = ⊤ := fun ω hω => (hGp ω hω).1
  have hWc : ∀ ω ∈ G, Continuous (W · ω) := fun ω hω =>
    (Sec7.IsIntegratedSLEPath.continuous_w_of_top (hGp ω hω).2.1).1
  have hVLc : ∀ ω ∈ G, Continuous (VL 0 · ω) := fun ω hω =>
    continuousOn_univ.1 (by simpa using (hGp ω hω).2.1.2.2.2.2.1 0)
  have hVRc : ∀ ω ∈ G, Continuous (VR 0 · ω) := fun ω hω =>
    continuousOn_univ.1 (by simpa using (hGp ω hω).2.1.2.2.2.2.2.1 0)
  set Wm := LP2.modProc G W with hWm
  set VLm := LP2.modProc G (VL 0) with hVLm
  set VRm := LP2.modProc G (VR 0) with hVRm
  have hWmc : ∀ ω, Continuous (Wm · ω) := LP2.continuous_modProc hWc
  have hWmm : ∀ t, Measurable[Ito.nullAugmented 𝓕 P t] (Wm t) :=
    LP2.measurable_modProc hGm hGc hGζ hE.2.1
  have hVLmm : ∀ t, Measurable[Ito.nullAugmented 𝓕 P t] (VLm t) :=
    LP2.measurable_modProc hGm hGc hGζ (hE.2.2.1 0)
  have hVRmm : ∀ t, Measurable[Ito.nullAugmented 𝓕 P t] (VRm t) :=
    LP2.measurable_modProc hGm hGc hGζ (hE.2.2.2.1 0)
  have hdrive : ∀ ω ∈ G, drive 1 Wm ω = fun s : ℝ => W s.toNNReal ω := fun ω hω => by
    funext s; simp [drive, hWm, LP2.modProc_of_mem hω]
  -- the parameter events
  set Aaug : (Fin 9 → ℚ) → Set Ω := fun p => {ω | ω ∈ G ∧ ParamEvent (drive 1 Wm ω)
    (VLm (sigmaOf p) ω - Wm (sigmaOf p) ω) (VRm (sigmaOf p) ω - Wm (sigmaOf p) ω) p} with hAaug
  have hAaugm : ∀ p, MeasurableSet[Ito.nullAugmented 𝓕 P (sigmaOf p)] (Aaug p) := by
    intro p
    have h1 := LP2.measurableSet_nullAugmented_of_compl (𝓕 := 𝓕) hGm hGc (sigmaOf p)
    have h2 : MeasurableSet[Ito.nullAugmented 𝓕 P (sigmaOf p)]
        {ω | VLm (sigmaOf p) ω - Wm (sigmaOf p) ω < ((p 2 : ℚ) : ℝ) - p 8} :=
      measurableSet_lt ((hVLmm _).sub (hWmm _)) measurable_const
    have h3 : MeasurableSet[Ito.nullAugmented 𝓕 P (sigmaOf p)]
        {ω | ((p 7 : ℚ) : ℝ) + p 8 < VRm (sigmaOf p) ω - Wm (sigmaOf p) ω} :=
      measurableSet_lt measurable_const ((hVRmm _).sub (hWmm _))
    have h4 := measurableSet_clusterCondQ (m := Ito.nullAugmented 𝓕 P (sigmaOf p)) hWmc 1
      (sigmaOf p).coe_nonneg (fun r hr => (hWmm r).mono ((Ito.nullAugmented 𝓕 P).mono
        (by exact_mod_cast hr)) le_rfl) (p 1) (-((p 4 : ℚ) : ℝ)) (-((p 5 : ℚ) : ℝ))
    have e : Aaug p = G ∩ ({ω | VLm (sigmaOf p) ω - Wm (sigmaOf p) ω < ((p 2 : ℚ) : ℝ) - p 8} ∩
        ({ω | ((p 7 : ℚ) : ℝ) + p 8 < VRm (sigmaOf p) ω - Wm (sigmaOf p) ω} ∩
          {ω | ClusterCondQ (drive 1 Wm ω) (sigmaOf p) (p 1) (-((p 4 : ℚ) : ℝ)) (-((p 5 : ℚ) : ℝ))})) := by
      ext ω; exact Iff.rfl
    rw [e]
    exact h1.inter (h2.inter (h3.inter h4))
  by_cases hex : ∃ p, GoodParams p ∧ P (Aaug p) ≠ 0
  · obtain ⟨p, hp, hpP⟩ := hex
    obtain ⟨A, hAm, hAe⟩ := Ito.exists_ae_eq_of_measurableSet_nullAugmented (hAaugm p)
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hp
    refine frequently_halfBall_of_cluster hκ hL hR hcol hE (sigmaOf p) h2 h3 h6 h7 h8 h1 h4 h5 hAm
      (by rwa [← measure_congr hAe]) ?_
    filter_upwards [hAe] with ω hω hωA
    have hmem : ω ∈ Aaug p := by
      have : (ω ∈ Aaug p) = (ω ∈ A) := hω
      rw [this]; exact hωA
    obtain ⟨hωG, hev1, hev2, hev3⟩ := hmem
    simp only [hVLm, hVRm, hWm, LP2.modProc_of_mem hωG] at hev1 hev2
    rw [hdrive ω hωG] at hev3
    refine ⟨hev1.le, hev2.le, fun z hz hzn => ?_⟩
    have h := clusterCond_of_clusterCondQ ((hWc ω hωG).comp continuous_real_toNNReal)
      (sigmaOf p).coe_nonneg hev3 z hz hzn
    simp only [neg_neg] at h
    exact h
  · push Not at hex
    have hnull : P (⋃ p, ⋃ (_ : GoodParams p), Aaug p) = 0 :=
      measure_iUnion_null fun p => measure_iUnion_null fun hp => hex p hp
    have hmem : ∃ᵐ ω ∂P, ω ∈ ⋃ p, ⋃ (_ : GoodParams p), Aaug p := by
      refine (hst.and_eventually ((measure_eq_zero_iff_ae_notMem.1 hGc).mono fun ω h => by
        simpa using h)).mono ?_
      rintro ω ⟨⟨T, y₁, y₂, hy₁, hy₂, hd₁, hd₂⟩, hωG⟩
      obtain ⟨-, hpath, η, hη⟩ := hGp ω hωG
      obtain ⟨p, hp, hev⟩ := exists_params_of_straddle (xL := twoSeedXL) (xR := twoSeedXR) rfl rfl hpath hη
        hy₁ hy₂ hd₁ hd₂
      refine mem_iUnion₂.2 ⟨p, hp, hωG, ?_⟩
      simp only [hVLm, hVRm, hWm, LP2.modProc_of_mem hωG]
      rw [hdrive ω hωG]
      exact hev
    exact absurd hnull (fun h0 => (hmem.and_eventually (measure_eq_zero_iff_ae_notMem.1 h0)).exists.elim
      fun ω ⟨h1, h2⟩ => h2 h1)

end LP4HB

/-! ### The reduction -/

/-- **`LP4HalfBallStatement` from the straddle input and the stopping-time collar.** -/
theorem lp4HalfBallStatement_of_straddle (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ)
    (hS : LP4StraddleStatement.{u}) : LP4HalfBallStatement.{u} := by
  intro κ hκ rL rR hL hLc hR hRc hcont Ω mΩ P _ 𝓕 W VL VR B ζ hE
  exact LP4HB.frequently_halfBall_of_straddle hκ hL hR (hcol κ hκ) hE (hcont P 𝓕 W VL VR B ζ hE)
    (hS κ hκ rL rR hL hLc hR hRc hcont P 𝓕 W VL VR B ζ hE)

/-- **Lemma LP4 (Proposition LP4) from the straddle input and the stopping-time collar**, through PROVE-LP16's
`lp4AvoidStatement_of_halfBall` and PROVE-LP14's `lp4Statement_of_avoid`. -/
theorem lp4Statement_of_straddle (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ)
    (hS : LP4StraddleStatement.{u}) : LP4Statement.{u} :=
  lp4Statement_of_avoid (lp4AvoidStatement_of_halfBall (lp4HalfBallStatement_of_straddle hcol hS))

end InteractingSLE.LP
