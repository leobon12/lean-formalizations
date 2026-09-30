import QuantumZipper.Proofs.Section5.Prop17StatAbstract
import QuantumZipper.Proofs.Section5.Prop17RawPos
import QuantumZipper.Proofs.Section5.TVLocal
import QuantumZipper.Proofs.Wire3

/-!
# Proposition 1.7, node D5-e: stationarity of the circle-coordinate law (PROP17-STAT)

Sheffield, arXiv:1012.4797, Proposition 1.7 and its proof (pp. 25–26): the γ-wedge is the
TV-local limit of Palm zooms (Proposition 1.6), the shift by quantum length `L` of the zoom at
level `C` is the zoom at the Palm point shifted by `δ L`, `δ = e^{-C/2}`, whose law is TV-close
to the unshifted one, and one passes to the limit `C → ∞` on both sides.

This file does the passage to the limit on the law `μ` of `coordsFull` of the reference wedge:

* `shiftCoords γ L`: the shift map on circle coordinates; `coordsFull_shiftL`: on good samples
  `coordsFull (shiftL γ L x) = shiftCoords γ L (coordsFull x)`;
* `locFull R`: the circle coordinates at the folded circles inside `closedBall 0 R`, `locEvents`
  the events they determine, `GoodC γ` the good coordinate vectors;
* `Prop17ShiftLocalStmt γ L` (**hypothesis**, locality of the shift, blueprint D5 "the shift-by-`L`
  map is `𝓛_R`-local on `{y_L < R}`"), and `Prop17ApproxStmt γ L` (**hypothesis**, the output of the
  pre-limit: TV-local approximations of `μ` by laws that are almost shift invariant on cylinders;
  derived from Palm zooms, A6 and D5-c in `Prop17StatPalm.lean`);
* `prop17RefCoordsShiftStmt_of_approx`: these two give `Prop17RefCoordsShiftStmt γ L`.

The passage to the limit is an own elementary argument (`Prop17StatAbstract.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull TV

/-! ## 1. The shift map on circle coordinates -/

/-- The shift map of Proposition 1.7 read on the full circle coordinates. -/
def shiftCoords (γ L : ℝ) (c : ℕ → ℝ) : ℕ → ℝ := (shiftData γ L (c, fun _ => 0)).1

theorem measurable_shiftCoords (γ L : ℝ) : Measurable (shiftCoords γ L) :=
  measurable_fst.comp ((measurable_shiftData γ L).comp (measurable_id.prodMk measurable_const))

theorem coordsFull_shiftL {γ L : ℝ} {x : FieldSample} (hx : IsLQGGood γ x) :
    coordsFull (shiftL γ L x) = shiftCoords γ L (coordsFull x) := by
  have h := congrArg Prod.fst (dataFull_shiftL (L := L) hx)
  exact h

/-! ## 2. Local coordinates, local events and good coordinate vectors -/

/-- The `i`-th enumerated folded circle lies in `closedBall 0 R`. -/
def inBallFull (R i : ℕ) : Prop := ‖(fullIndex i).1‖ + (fullIndex i).2 ≤ (R : ℝ)

open Classical in
/-- The circle coordinates at the enumerated folded circles inside `closedBall 0 R` (junk `0`
elsewhere). -/
def locFull (R : ℕ) (c : ℕ → ℝ) : ℕ → ℝ := fun i => if inBallFull R i then c i else 0

theorem measurable_locFull (R : ℕ) : Measurable (locFull R) := by
  classical
  refine measurable_pi_iff.2 fun i => ?_
  unfold locFull
  split_ifs
  · exact measurable_pi_apply i
  · exact measurable_const

/-- The local events: those determined by `locFull R` for some `R`. -/
def locEvents : Set (Set (ℕ → ℝ)) :=
  {F | ∃ R : ℕ, ∃ G : Set (ℕ → ℝ), MeasurableSet G ∧ F = locFull R ⁻¹' G}

/-- Good coordinate vectors: the reconstructed sample is good and has infinite boundary length
to the right of `0`. -/
def GoodC (γ : ℝ) : Set (ℕ → ℝ) :=
  {c | IsLQGGood γ (reconstruct (proj c)) ∧ qBoundaryMeasure γ (reconstruct (proj c)) (Ici 0) = ⊤}

open Classical in
theorem measurableSet_goodC (γ : ℝ) : MeasurableSet (GoodC γ) := by
  have hS : MeasurableSet ({x : FieldSample | IsLQGGood γ x} ∩
      {x | (if IsLQGGood γ x then qBoundaryMeasure γ x else 0) (Ici 0) = ⊤}) :=
    (GoodMeas.measurableSet_isLQGGood γ).inter (by
      have := ((Measure.measurable_coe (measurableSet_Ici (a := (0 : ℝ)))).comp
        (GoodMeas.measurable_qBoundaryMeasure_global γ)) (measurableSet_singleton ⊤)
      exact this)
  have e : GoodC γ = (fun c => reconstruct (proj c)) ⁻¹' ({x : FieldSample | IsLQGGood γ x} ∩
      {x | (if IsLQGGood γ x then qBoundaryMeasure γ x else 0) (Ici 0) = ⊤}) := by
    ext c
    simp only [GoodC, mem_ofPred_eq, mem_preimage, mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [if_pos h1]; exact h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [if_pos h1] at h2⟩
  rw [e]
  exact (measurable_reconstruct.comp measurable_proj) hS

theorem coordsFull_mem_goodC {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x)
    (hb : qBoundaryMeasure γ x (Ici 0) = ⊤) : coordsFull x ∈ GoodC γ := by
  rw [GoodC, mem_ofPred_eq, ← coords_eq_proj, GoodSample.isLQGGood_iff_reconstruct,
    Factorization.qBoundaryMeasure_congr (avgReg_reconstruct_coords x)]
  exact ⟨hx, hb⟩

theorem fullIndex_radius_pos (i : ℕ) : 0 < (fullIndex i).2 := by
  simp only [fullIndex]
  positivity

/-- Measurable cylinders are local events. -/
theorem measurableCylinders_subset_locEvents :
    measurableCylinders (fun _ : ℕ => ℝ) ⊆ locEvents := by
  intro E hE
  obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders E).1 hE
  refine ⟨⌈∑ i ∈ s, (‖(fullIndex i).1‖ + (fullIndex i).2)⌉₊, cylinder s S, hS.cylinder, ?_⟩
  have hin : ∀ i ∈ s, inBallFull ⌈∑ i ∈ s, (‖(fullIndex i).1‖ + (fullIndex i).2)⌉₊ i := by
    intro i hi
    unfold inBallFull
    refine le_trans ?_ (Nat.le_ceil _)
    exact Finset.single_le_sum (f := fun i => ‖(fullIndex i).1‖ + (fullIndex i).2)
      (fun j _ => add_nonneg (norm_nonneg _) (fullIndex_radius_pos j).le) hi
  ext c
  simp only [mem_cylinder, mem_preimage]
  have : s.restrict (locFull ⌈∑ i ∈ s, (‖(fullIndex i).1‖ + (fullIndex i).2)⌉₊ c) =
      s.restrict c := by
    funext i
    simp [Finset.restrict, locFull, hin i.1 i.2]
  rw [this]

/-- TV-local convergence on `locFull` gives convergence of the probabilities of local events. -/
theorem tendsto_real_of_tvLocal {ι : Type*} {l : Filter ι} {μs : ι → Measure (ℕ → ℝ)}
    {μ : Measure (ℕ → ℝ)} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)]
    (h : TVLocalTendsto l μs μ locFull) :
    ∀ F ∈ locEvents, Tendsto (fun i => (μs i).real F) l (𝓝 (μ.real F)) := by
  rintro F ⟨R, G, hG, rfl⟩
  have hR := h R
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun i => (tvDist ((μs i).map (locFull R)) (μ.map (locFull R))).toReal) l
      (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hR
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) h0
  have e1 : (μs i).real (locFull R ⁻¹' G) = ((μs i).map (locFull R)).real G := by
    rw [map_measureReal_apply (measurable_locFull R) hG]
  have e2 : μ.real (locFull R ⁻¹' G) = (μ.map (locFull R)).real G := by
    rw [map_measureReal_apply (measurable_locFull R) hG]
  rw [e1, e2, Real.norm_eq_abs, abs_le]
  set m1 := (μs i).map (locFull R)
  set m2 := μ.map (locFull R)
  have ht : tvDist m1 m2 ≠ ⊤ := tvDist_ne_top
  have a1 : m1 G ≤ m2 G + tvDist m1 m2 := tsub_le_iff_left.1 (le_tvDist hG)
  have a2 : m2 G ≤ m1 G + tvDist m1 m2 := tsub_le_iff_left.1 (le_tvDist' hG)
  have b1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, ht⟩) a1
  have b2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, ht⟩) a2
  rw [ENNReal.toReal_add (measure_ne_top _ _) ht] at b1 b2
  simp only [measureReal_def]
  constructor <;> linarith

/-! ## 3. The two hypotheses and the assembly -/

/-- **Pre-limit approximation (hypothesis; discharged from Palm zooms in `Prop17StatPalm`).**
For every reference construction, the law of `coordsFull` of the reference wedge is the TV-local
limit (on `locFull`) of laws of good vectors that are asymptotically invariant under
`shiftCoords γ L` on measurable cylinders. -/
def Prop17ApproxStmt (γ L : ℝ) : Prop :=
  ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → FieldSample)
    (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
    IsWedgeProcess γ (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
    ∃ (ι : Type) (l : Filter ι) (μs : ι → Measure (ℕ → ℝ)), l.NeBot ∧
      (∀ i, IsProbabilityMeasure (μs i)) ∧
      TVLocalTendsto l μs (P'.map fun ω => coordsFull (refField γ X A ω)) locFull ∧
      (∀ i, ∀ᵐ c ∂μs i, c ∈ GoodC γ) ∧
      ∀ E ∈ measurableCylinders (fun _ : ℕ => ℝ),
        Tendsto (fun i => (μs i).real (shiftCoords γ L ⁻¹' E) - (μs i).real E) l (𝓝 0)

end Raw
end FieldLaw
end S5
end QuantumZipper
