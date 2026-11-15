/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.OneForceUnique
import QuantumZipper.Proofs.RS.TransienceCanon
import QuantumZipper.Proofs.Probability.StrongMarkov
import QuantumZipper.Proofs.Probability.BMExistence
import InteractingSLE.Stochastic.Bessel.Estimate
import InteractingSLE.Frozen.Spec.IsOrderedForceWord

/-!
# One force point: Theorem 2.2 (existence and uniqueness in law)

Packet PROVE-SEC2-ONE. Specification p. 21 (`source/spec/p001-048.md` L482–L484): "When there is
only a single force point, Theorem 2.2 follows from standard facts about Bessel processes (see
Chapter XI of [RY99]; recall also (2.3)) and the definition coincides with the standard definition
of `SLE_κ(ρ)`."

* `exists_filteredBrownian`: a probability space (on a `Type`) with a filtered Brownian motion
  whose paths are all continuous and start at `0` (QuantumZipper's existence and good version,
  the natural filtration).
* `exists_isIntegratedSLEEvolution_left` / `_right`: the frozen existence statement of
  Theorem 2.2 for one force point.
* `measure_killedState_eq_left` / `_right`: the frozen uniqueness-in-law statement of
  Theorem 2.2 for one force point: the finite-dimensional laws of the killed state
  `(W, V^L, V^R, B)` are the same for any two evolutions.

Uniqueness in law: almost surely the evolution is the construction (2.3) applied to a continuous
version of its Brownian motion (pathwise uniqueness, `OneForceUnique`), hence its killed state
events are preimages of one measurable set of continuous paths (adaptedness of the construction,
`OneForceExists`, on the canonical space `CPath`), whose probability is the same for every
Brownian motion (`QuantumZipper.RS.map_toCPath_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace OneForce

/-! ### A filtered Brownian motion with continuous paths -/

/-- The natural filtration makes a Brownian motion with measurable coordinates a filtered
Brownian motion. -/
theorem isFilteredBrownianReal_natFilt {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) :
    IsFilteredBrownianReal (Bessel.natFilt hBm) B P := by
  refine ⟨hB, fun t => Bessel.natFilt_adapted hBm t, fun s t hst => ?_⟩
  have h := QuantumZipper.StrongMarkov.indep_shift_of_le_past hB.toIsPreBrownianReal
    (𝓕 := Bessel.natFilt hBm) (Bessel.natFilt_le_past hBm) s
  refine (indep_of_indep_of_le_right h ?_).symm
  have hm : Measurable[MeasurableSpace.comap
      (QuantumZipper.StrongMarkov.smPath B (fun _ => s)) MeasurableSpace.pi]
      (fun ω => B t ω - B s ω) := by
    have h1 : (fun ω => B t ω - B s ω)
        = (fun f : ℝ≥0 → ℝ => f (t - s)) ∘ QuantumZipper.StrongMarkov.smPath B (fun _ => s) := by
      funext ω
      simp [QuantumZipper.StrongMarkov.smPath, QuantumZipper.StrongMarkov.smShift,
        add_tsub_cancel_of_le hst]
    rw [h1]
    exact (measurable_pi_apply _).comp (Measurable.of_comap_le le_rfl)
  exact hm.comap_le

/-- **A filtered Brownian motion with continuous paths started at `0` exists** (on a `Type`). -/
theorem exists_filteredBrownian :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ),
      IsFilteredBrownianReal 𝓕 B P ∧ (∀ ω, Continuous (B · ω)) ∧ ∀ ω, B 0 ω = 0 := by
  obtain ⟨B₀, hB₀⟩ := QuantumZipper.BMExist.exists_isBrownianReal_stdP
  obtain ⟨B, hBm, hBc, hB0, hB, -⟩ := QuantumZipper.RS.exists_good_version0 hB₀
  exact ⟨ℕ → ℝ, inferInstance, LQGDimension.ExistAsm.stdP, inferInstance, Bessel.natFilt hBm, B,
    isFilteredBrownianReal_natFilt hB hBm, hBc, hB0⟩


/-! ### Existence (frozen form, one force point) -/

/-- **Theorem 2.2, existence, one force point on the left** (the frozen statement
`exists_isIntegratedSLEEvolution` with `nL = 1`, `nR = 0`). -/
theorem exists_isIntegratedSLEEvolution_left {a : ℝ} (ha : 0 < a) (xL : Fin 1 → ℝ)
    (xR : Fin 0 → ℝ) (ρL : Fin 1 → ℝ) (ρR : Fin 0 → ℝ) (hF : IsOrderedForceWord xL xR) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 0 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, B, hB, hBc, hB0⟩ := exists_filteredBrownian
  exact ⟨Ω, mΩ, P, hP, 𝓕, _, _, fun i => i.elim0, B, _,
    isIntegratedSLEEvolution_left ha (hF.2.1 0) hB hBc hB0 fun i => i.elim0⟩

/-- **Theorem 2.2, existence, one force point on the right** (the frozen statement
`exists_isIntegratedSLEEvolution` with `nL = 0`, `nR = 1`). -/
theorem exists_isIntegratedSLEEvolution_right {a : ℝ} (ha : 0 < a) (xL : Fin 0 → ℝ)
    (xR : Fin 1 → ℝ) (ρL : Fin 0 → ℝ) (ρR : Fin 1 → ℝ) (hF : IsOrderedForceWord xL xR) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 0 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, B, hB, hBc, hB0⟩ := exists_filteredBrownian
  exact ⟨Ω, mΩ, P, hP, 𝓕, _, fun i => i.elim0, _, B, _,
    isIntegratedSLEEvolution_right ha (hF.2.2.2 0) hB hBc hB0 fun i => i.elim0⟩


/-! ### Every evolution with one force point is the construction (2.3) -/

section Identify

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {a : ℝ}

/-- **Pathwise identification, one force point on the left**: almost surely an evolution has
the lifetime of the construction (2.3) applied to a continuous version `B̃` of its Brownian
motion, and before it equals that construction. -/
theorem ae_eq_construction_left (ha : 0 < a) {xL : Fin 1 → ℝ} {xR : Fin 0 → ℝ}
    {ρL : Fin 1 → ℝ} {ρR : Fin 0 → ℝ} (hxL : xL 0 ≤ 0) {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {B' : ℝ≥0 → Ω → ℝ}
    (hB' : IsPreBrownianReal B' P) (hB'm : ∀ t, Measurable (B' t))
    (hB'c : ∀ ω, Continuous (B' · ω)) (hB'0 : ∀ ω, B' 0 ω = 0)
    (hae : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω) :
    ∀ᵐ ω ∂P, ζ ω = leftζ a (xL 0) (ρL 0) B' ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
      W t ω = leftWProc a (xL 0) (ρL 0) B' t ω ∧ VL 0 t ω = leftVProc a (xL 0) (ρL 0) B' t ω := by
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hx : 0 ≤ -xL 0 / Real.sqrt a := div_nonneg (neg_nonneg.2 hxL) hr.le
  filter_upwards [h.2.2.2.2, hae, ae_one (c := (ρL 0 + 2) / a) hB' hB'm hB'c hB'0 hx]
    with ω hpath hBeq ⟨hK, hpos, hζ0, hζT, hJ⟩
  have hb : (fun t => B t ω) = fun t => B' t ω := funext fun t => (hBeq t).symm
  rw [hb] at hpath
  set X : ℝ≥0 → ℝ := fun t => oneX ((ρL 0 + 2) / a) (-xL 0 / Real.sqrt a) B' t ω with hXdef
  obtain ⟨hζ, hform⟩ := IsIntegratedSLEPath.eq_left ha hpath (hB'c ω) hK hpos hζ0 hζT
  refine ⟨hζ, fun t ht => ?_⟩
  have hV : leftVProc a (xL 0) (ρL 0) B' t ω = leftV a (xL 0) X t := by
    rw [leftV_eq_sub, leftVProc, hJ t]
  refine ⟨?_, by rw [hV]; exact (hform t ht).2⟩
  rw [(hform t ht).1, leftW, leftWProc, hV]

/-- **Pathwise identification, one force point on the right** (as
`ae_eq_construction_left`). -/
theorem ae_eq_construction_right (ha : 0 < a) {xL : Fin 0 → ℝ} {xR : Fin 1 → ℝ}
    {ρL : Fin 0 → ℝ} {ρR : Fin 1 → ℝ} (hxR : 0 ≤ xR 0) {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 1 → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {B' : ℝ≥0 → Ω → ℝ}
    (hB' : IsPreBrownianReal B' P) (hB'm : ∀ t, Measurable (B' t))
    (hB'c : ∀ ω, Continuous (B' · ω)) (hB'0 : ∀ ω, B' 0 ω = 0)
    (hae : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω) :
    ∀ᵐ ω ∂P, ζ ω = rightζ a (xR 0) (ρR 0) B' ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
      W t ω = rightWProc a (xR 0) (ρR 0) B' t ω ∧
        VR 0 t ω = rightVProc a (xR 0) (ρR 0) B' t ω := by
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hx : 0 ≤ xR 0 / Real.sqrt a := div_nonneg hxR hr.le
  have hm : ∀ t, Measurable (negProc B' t) := fun t => (hB'm t).neg
  have hc : ∀ ω, Continuous (negProc B' · ω) := fun ω => (hB'c ω).neg
  have h0 : ∀ ω, negProc B' 0 ω = 0 := fun ω => by simp [negProc, hB'0 ω]
  have hpre : IsPreBrownianReal (negProc B') P := hB'.neg
  filter_upwards [h.2.2.2.2, hae, ae_one (c := (ρR 0 + 2) / a) hpre hm hc h0 hx]
    with ω hpath hBeq ⟨hK, hpos, hζ0, hζT, hJ⟩
  have hb : (fun t => B t ω) = fun t => B' t ω := funext fun t => (hBeq t).symm
  rw [hb] at hpath
  set X : ℝ≥0 → ℝ := fun t => oneX ((ρR 0 + 2) / a) (xR 0 / Real.sqrt a) (negProc B') t ω
    with hXdef
  obtain ⟨hζ, hform⟩ := IsIntegratedSLEPath.eq_right ha hpath (hB'c ω) hK hpos hζ0 hζT
  refine ⟨hζ, fun t ht => ?_⟩
  have hV : rightVProc a (xR 0) (ρR 0) B' t ω = rightV a (xR 0) X t := by
    rw [rightV_eq_add, rightVProc, hJ t]
  refine ⟨?_, by rw [hV]; exact (hform t ht).2⟩
  rw [(hform t ht).1, rightW, rightWProc, hV]

end Identify


/-! ### Uniqueness in law -/

section Law

open QuantumZipper.RS (CPath canonBM toCPath)

/-- The killed-state event of the left construction on the canonical space `CPath`. -/
def leftStateSet (a x₀ ρ : ℝ) {n : ℕ} (ts : Fin n → ℝ≥0)
    (A : Fin n → Set (ℝ × (Fin 1 → ℝ) × (Fin 0 → ℝ) × ℝ)) : Set CPath :=
  {f | ∀ j, (ts j : ℝ≥0∞) < leftζ a x₀ ρ canonBM f ∧
    (leftWProc a x₀ ρ canonBM (ts j) f, (fun _ => leftVProc a x₀ ρ canonBM (ts j) f),
      (fun i : Fin 0 => i.elim0), canonBM (ts j) f) ∈ A j}

/-- The killed-state event of the right construction on the canonical space `CPath`. -/
def rightStateSet (a x₀ ρ : ℝ) {n : ℕ} (ts : Fin n → ℝ≥0)
    (A : Fin n → Set (ℝ × (Fin 0 → ℝ) × (Fin 1 → ℝ) × ℝ)) : Set CPath :=
  {f | ∀ j, (ts j : ℝ≥0∞) < rightζ a x₀ ρ canonBM f ∧
    (rightWProc a x₀ ρ canonBM (ts j) f, (fun i : Fin 0 => i.elim0),
      (fun _ => rightVProc a x₀ ρ canonBM (ts j) f), canonBM (ts j) f) ∈ A j}

theorem measurableSet_leftStateSet (a x₀ ρ : ℝ) {n : ℕ} (ts : Fin n → ℝ≥0)
    {A : Fin n → Set (ℝ × (Fin 1 → ℝ) × (Fin 0 → ℝ) × ℝ)} (hA : ∀ j, MeasurableSet (A j)) :
    MeasurableSet (leftStateSet a x₀ ρ ts A) := by
  set 𝓕 := Bessel.natFilt (B := canonBM) QuantumZipper.RS.measurable_canonBM
  have hDad : ∀ t, Measurable[𝓕 t] (canonBM t) := fun t =>
    Bessel.natFilt_adapted QuantumZipper.RS.measurable_canonBM t
  set g : ℝ × ℝ × ℝ → ℝ × (Fin 1 → ℝ) × (Fin 0 → ℝ) × ℝ := fun p =>
    (x₀ - 2 / Real.sqrt a * p.2.1 + Real.sqrt a * p.1, fun _ => x₀ - 2 / Real.sqrt a * p.2.1,
      fun i : Fin 0 => i.elim0, p.2.2) with hgdef
  have hg : Measurable g := by
    refine Measurable.prodMk (by fun_prop) (Measurable.prodMk ?_ (Measurable.prodMk
      measurable_const (by fun_prop)))
    exact Measurable.of_eval fun _ => by fun_prop
  have heq : leftStateSet a x₀ ρ ts A = ⋂ j, {f | (ts j : ℝ≥0∞) <
      oneζ ((ρ + 2) / a) (-x₀ / Real.sqrt a) canonBM f ∧
      (oneX ((ρ + 2) / a) (-x₀ / Real.sqrt a) canonBM (ts j) f,
        oneJ ((ρ + 2) / a) (-x₀ / Real.sqrt a) canonBM (ts j) f, canonBM (ts j) f) ∈
          g ⁻¹' A j} := by
    ext f
    simp only [leftStateSet, mem_ofPred_eq, mem_iInter, mem_preimage, hgdef]
    rfl
  rw [heq]
  exact MeasurableSet.iInter fun j => 𝓕.le (ts j) _
    (measurableSet_one 𝓕 hDad QuantumZipper.RS.continuous_canonBM (ts j) (hg (hA j)))

theorem measurableSet_rightStateSet (a x₀ ρ : ℝ) {n : ℕ} (ts : Fin n → ℝ≥0)
    {A : Fin n → Set (ℝ × (Fin 0 → ℝ) × (Fin 1 → ℝ) × ℝ)} (hA : ∀ j, MeasurableSet (A j)) :
    MeasurableSet (rightStateSet a x₀ ρ ts A) := by
  set D : ℝ≥0 → CPath → ℝ := negProc canonBM
  have hDm : ∀ t, Measurable (D t) := fun t => (QuantumZipper.RS.measurable_canonBM t).neg
  set 𝓕 := Bessel.natFilt (B := canonBM) QuantumZipper.RS.measurable_canonBM
  have hDad : ∀ t, Measurable[𝓕 t] (D t) := fun t =>
    (Bessel.natFilt_adapted QuantumZipper.RS.measurable_canonBM t).neg
  have hDc : ∀ f, Continuous (D · f) := fun f => (QuantumZipper.RS.continuous_canonBM f).neg
  set g : ℝ × ℝ × ℝ → ℝ × (Fin 0 → ℝ) × (Fin 1 → ℝ) × ℝ := fun p =>
    (x₀ + 2 / Real.sqrt a * p.2.1 - Real.sqrt a * p.1, fun i : Fin 0 => i.elim0,
      fun _ => x₀ + 2 / Real.sqrt a * p.2.1, -p.2.2) with hgdef
  have hg : Measurable g := by
    refine Measurable.prodMk (by fun_prop) (Measurable.prodMk measurable_const
      (Measurable.prodMk ?_ (by fun_prop)))
    exact Measurable.of_eval fun _ => by fun_prop
  have heq : rightStateSet a x₀ ρ ts A = ⋂ j, {f | (ts j : ℝ≥0∞) <
      oneζ ((ρ + 2) / a) (x₀ / Real.sqrt a) D f ∧
      (oneX ((ρ + 2) / a) (x₀ / Real.sqrt a) D (ts j) f,
        oneJ ((ρ + 2) / a) (x₀ / Real.sqrt a) D (ts j) f, D (ts j) f) ∈ g ⁻¹' A j} := by
    ext f
    simp only [rightStateSet, mem_ofPred_eq, mem_iInter, mem_preimage, hgdef]
    refine forall_congr' fun j => and_congr Iff.rfl ?_
    simp only [D, negProc, neg_neg]
    rfl
  rw [heq]
  exact MeasurableSet.iInter fun j => 𝓕.le (ts j) _
    (measurableSet_one 𝓕 hDad hDc (ts j) (hg (hA j)))


variable {a : ℝ}

/-- The killed-state probabilities of a left evolution are those of the law of a continuous
version `B'` of its Brownian motion on `CPath`, evaluated on `leftStateSet`. -/
theorem measure_killedState_left_eq_map {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (ha : 0 < a) {xL : Fin 1 → ℝ} {xR : Fin 0 → ℝ} {ρL : Fin 1 → ℝ} {ρR : Fin 0 → ℝ}
    (hxL : xL 0 ≤ 0) {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ}
    {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {B' : ℝ≥0 → Ω → ℝ}
    (hB' : IsPreBrownianReal B' P) (hB'm : ∀ t, Measurable (B' t))
    (hB'c : ∀ ω, Continuous (B' · ω)) (hB'0 : ∀ ω, B' 0 ω = 0)
    (hae : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω) {n : ℕ} (ts : Fin n → ℝ≥0)
    (A : Fin n → Set (ℝ × (Fin 1 → ℝ) × (Fin 0 → ℝ) × ℝ)) (hA : ∀ j, MeasurableSet (A j)) :
    P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
        (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ A j} =
      (P.map (toCPath B' hB'c)) (leftStateSet a (xL 0) (ρL 0) ts A) := by
  rw [Measure.map_apply (QuantumZipper.RS.measurable_toCPath hB'm hB'c)
    (measurableSet_leftStateSet _ _ _ ts hA)]
  refine measure_congr ?_
  filter_upwards [ae_eq_construction_left ha hxL h hB' hB'm hB'c hB'0 hae, hae]
    with ω ⟨hζ, hform⟩ hBeq
  refine propext (forall_congr' fun j => ?_)
  change _ ↔ (ts j : ℝ≥0∞) < leftζ a (xL 0) (ρL 0) B' ω ∧
    (leftWProc a (xL 0) (ρL 0) B' (ts j) ω, (fun _ => leftVProc a (xL 0) (ρL 0) B' (ts j) ω),
      (fun i : Fin 0 => i.elim0), B' (ts j) ω) ∈ A j
  rw [← hζ]
  refine and_congr_right fun ht => ?_
  have hVL : (fun i => VL i (ts j) ω) = fun _ => leftVProc a (xL 0) (ρL 0) B' (ts j) ω :=
    funext fun i => by rw [Fin.fin_one_eq_zero i]; exact (hform _ ht).2
  have hVR : (fun i => VR i (ts j) ω) = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
  rw [(hform _ ht).1, hVL, hVR, hBeq]

/-- The killed-state probabilities of a right evolution, as `measure_killedState_left_eq_map`. -/
theorem measure_killedState_right_eq_map {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (ha : 0 < a) {xL : Fin 0 → ℝ} {xR : Fin 1 → ℝ} {ρL : Fin 0 → ℝ} {ρR : Fin 1 → ℝ}
    (hxR : 0 ≤ xR 0) {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ}
    {VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {B' : ℝ≥0 → Ω → ℝ}
    (hB' : IsPreBrownianReal B' P) (hB'm : ∀ t, Measurable (B' t))
    (hB'c : ∀ ω, Continuous (B' · ω)) (hB'0 : ∀ ω, B' 0 ω = 0)
    (hae : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω) {n : ℕ} (ts : Fin n → ℝ≥0)
    (A : Fin n → Set (ℝ × (Fin 0 → ℝ) × (Fin 1 → ℝ) × ℝ)) (hA : ∀ j, MeasurableSet (A j)) :
    P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
        (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ A j} =
      (P.map (toCPath B' hB'c)) (rightStateSet a (xR 0) (ρR 0) ts A) := by
  rw [Measure.map_apply (QuantumZipper.RS.measurable_toCPath hB'm hB'c)
    (measurableSet_rightStateSet _ _ _ ts hA)]
  refine measure_congr ?_
  filter_upwards [ae_eq_construction_right ha hxR h hB' hB'm hB'c hB'0 hae, hae]
    with ω ⟨hζ, hform⟩ hBeq
  refine propext (forall_congr' fun j => ?_)
  change _ ↔ (ts j : ℝ≥0∞) < rightζ a (xR 0) (ρR 0) B' ω ∧
    (rightWProc a (xR 0) (ρR 0) B' (ts j) ω, (fun i : Fin 0 => i.elim0),
      (fun _ => rightVProc a (xR 0) (ρR 0) B' (ts j) ω), B' (ts j) ω) ∈ A j
  rw [← hζ]
  refine and_congr_right fun ht => ?_
  have hVR : (fun i => VR i (ts j) ω) = fun _ => rightVProc a (xR 0) (ρR 0) B' (ts j) ω :=
    funext fun i => by rw [Fin.fin_one_eq_zero i]; exact (hform _ ht).2
  have hVL : (fun i => VL i (ts j) ω) = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
  rw [(hform _ ht).1, hVL, hVR, hBeq]

/-- **Theorem 2.2, uniqueness in law, one force point on the left** (the frozen statement
`IsIntegratedSLEEvolution.measure_killedState_eq` with `nL = 1`, `nR = 0`). -/
theorem measure_killedState_eq_left (ha : 0 < a) {xL : Fin 1 → ℝ} {xR : Fin 0 → ℝ}
    {ρL : Fin 1 → ℝ} {ρR : Fin 0 → ℝ} (hF : IsOrderedForceWord xL xR)
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin 0 → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution a xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin 0 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution a xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (n : ℕ) (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin 1 → ℝ) × (Fin 0 → ℝ) × ℝ))
    (hA : ∀ j, MeasurableSet (A j)) :
    P₁ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₁ ω ∧
        (W₁ (ts j) ω, (fun i => VL₁ i (ts j) ω), (fun i => VR₁ i (ts j) ω), B₁ (ts j) ω) ∈ A j} =
      P₂ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₂ ω ∧
        (W₂ (ts j) ω, (fun i => VL₂ i (ts j) ω), (fun i => VR₂ i (ts j) ω), B₂ (ts j) ω) ∈
          A j} := by
  obtain ⟨B₁', hm₁, hc₁, h0₁, hB₁', hae₁⟩ := QuantumZipper.RS.exists_good_version0 h₁.1.1
  obtain ⟨B₂', hm₂, hc₂, h0₂, hB₂', hae₂⟩ := QuantumZipper.RS.exists_good_version0 h₂.1.1
  rw [measure_killedState_left_eq_map ha (hF.2.1 0) h₁ hB₁'.toIsPreBrownianReal hm₁ hc₁ h0₁
      hae₁ ts A hA,
    measure_killedState_left_eq_map ha (hF.2.1 0) h₂ hB₂'.toIsPreBrownianReal hm₂ hc₂ h0₂
      hae₂ ts A hA,
    QuantumZipper.RS.map_toCPath_eq hB₁'.toIsPreBrownianReal hB₂'.toIsPreBrownianReal hm₁ hm₂
      hc₁ hc₂]

/-- **Theorem 2.2, uniqueness in law, one force point on the right** (the frozen statement
`IsIntegratedSLEEvolution.measure_killedState_eq` with `nL = 0`, `nR = 1`). -/
theorem measure_killedState_eq_right (ha : 0 < a) {xL : Fin 0 → ℝ} {xR : Fin 1 → ℝ}
    {ρL : Fin 0 → ℝ} {ρR : Fin 1 → ℝ} (hF : IsOrderedForceWord xL xR)
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin 0 → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution a xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin 0 → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution a xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (n : ℕ) (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin 0 → ℝ) × (Fin 1 → ℝ) × ℝ))
    (hA : ∀ j, MeasurableSet (A j)) :
    P₁ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₁ ω ∧
        (W₁ (ts j) ω, (fun i => VL₁ i (ts j) ω), (fun i => VR₁ i (ts j) ω), B₁ (ts j) ω) ∈ A j} =
      P₂ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₂ ω ∧
        (W₂ (ts j) ω, (fun i => VL₂ i (ts j) ω), (fun i => VR₂ i (ts j) ω), B₂ (ts j) ω) ∈
          A j} := by
  obtain ⟨B₁', hm₁, hc₁, h0₁, hB₁', hae₁⟩ := QuantumZipper.RS.exists_good_version0 h₁.1.1
  obtain ⟨B₂', hm₂, hc₂, h0₂, hB₂', hae₂⟩ := QuantumZipper.RS.exists_good_version0 h₂.1.1
  rw [measure_killedState_right_eq_map ha (hF.2.2.2 0) h₁ hB₁'.toIsPreBrownianReal hm₁ hc₁ h0₁
      hae₁ ts A hA,
    measure_killedState_right_eq_map ha (hF.2.2.2 0) h₂ hB₂'.toIsPreBrownianReal hm₂ hc₂ h0₂
      hae₂ ts A hA,
    QuantumZipper.RS.map_toCPath_eq hB₁'.toIsPreBrownianReal hB₂'.toIsPreBrownianReal hm₁ hm₂
      hc₁ hc₂]

end Law

end OneForce

end InteractingSLE
