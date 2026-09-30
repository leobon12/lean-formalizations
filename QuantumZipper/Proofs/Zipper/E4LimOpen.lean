import QuantumZipper.Proofs.Zipper.E4LimStrict
import QuantumZipper.Proofs.Zipper.E4LimMC

/-!
# E4-MC, first generators: indicators of open finite-dimensional cylinders in `Ψ`

`handoff/E4.md`, item E4 (monotone class), stage 1. `exists_approx_open`: the indicator of an
open set of a metric space is a pointwise limit of continuous `[0,1]`-valued functions
(`min(1, k·d(y, Oᶜ))`, own elementary argument). `goodEq_open_psi`: E4 (`GoodEq`, i.e. identity
plus a.e.-measurability) for `Ψ = 1_O(x, d.1∘u, d.2∘u)` with `O` open and `Φ = cylPhi I f`
continuous, from `e4_cyl` by dominated convergence (`tendsto_iter_lintegral`, bound `1`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E4Grid

open B2 E1 CoordsFull PalmNorm

/-- Indicators of open sets are pointwise limits of continuous `[0,1]`-valued functions. -/
theorem exists_approx_open {E : Type*} [MetricSpace E] {O : Set E} (hO : IsOpen O) :
    ∃ g : ℕ → E → ℝ≥0∞, (∀ k, Continuous (g k)) ∧ (∀ k y, g k y ≤ 1) ∧
      ∀ y, Tendsto (fun k => g k y) atTop (𝓝 (O.indicator 1 y)) := by
  rcases (Oᶜ).eq_empty_or_nonempty with h | h
  · refine ⟨fun _ _ => 1, fun _ => continuous_const, fun _ _ => le_rfl, fun y => ?_⟩
    rw [indicator_of_mem (compl_empty_iff.1 h ▸ mem_univ y), Pi.one_apply]
    exact tendsto_const_nhds
  refine ⟨fun k y => ENNReal.ofReal (min 1 (k * Metric.infDist y Oᶜ)), fun k =>
    ENNReal.continuous_ofReal.comp (continuous_const.min
      (continuous_const.mul (Metric.continuous_infDist_pt Oᶜ))),
    fun k y => ENNReal.ofReal_le_one.2 (min_le_left _ _), fun y => ?_⟩
  by_cases hy : y ∈ O
  · rw [indicator_of_mem hy, Pi.one_apply]
    have hd : 0 < Metric.infDist y Oᶜ := (Metric.infDist_pos_iff_notMem_closure h).1
      (by rw [hO.isClosed_compl.closure_eq]; exact fun h' => h' hy)
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / Metric.infDist y Oᶜ)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with k hk
    have h1 : 1 / Metric.infDist y Oᶜ < k := hN.trans_le (Nat.cast_le.2 hk)
    rw [div_lt_iff₀ hd] at h1
    rw [min_eq_left h1.le, ENNReal.ofReal_one]
  · rw [indicator_of_notMem hy]
    refine tendsto_const_nhds.congr fun k => ?_
    dsimp only
    rw [Metric.infDist_zero_of_mem (mem_compl hy)]
    simp

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- **Stage 1 generators.** E4 with the a.e.-measurability, for `Ψ` the indicator of an open
cylinder and `Φ` continuous cylinder, given the interior form `hL3i` of L3. -/
theorem goodEq_open_psi (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X' : Ω' → FieldSample} (hX' : IsFreeGFFModConstH X' P') {δ : ℝ} (hδ : 0 < δ)
    {m : ℕ} (u : Fin m → ℝ≥0) {O : Set (ℝ × (Fin m → ℝ) × (Fin m → ℝ))} (hO : IsOpen O)
    {m' : ℕ} {I : Fin m' → ℕ} {f : (Fin m' → ℝ) → ℝ≥0∞} (hf : Continuous f) (hf1 : ∀ c, f c ≤ 1)
    (hL3i : ∀ᵐ ω ∂P, ∀ x < 0, ∀ s, 0 ≤ s → s < T → IsLive (Vr κ T B ω) s x →
      ContinuousWithinAt (fun s => ∫⁻ ω', cylPhi I f (coordsFull
          (targetField κ (Vr κ T B ω) s ϖ x (X' ω'))) ∂P') (Ici s) s) :
    GoodEq P (fun ω => nuPalm κ T B X ϖ ω) (Icc (-δ) 0)
      (lhsInt κ T B X ϖ (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T})
        (cylPsi u (O.indicator 1)) (cylPhi I f))
      (rhsInt κ T B ϖ P' X' (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T})
        (cylPsi u (O.indicator 1)) (cylPhi I f)) := by
  obtain ⟨g, hgc, hg1, hgt⟩ := exists_approx_open hO
  have hk := fun k => e4_cyl hκ hκ4 hT hB hX hind hϖ hX' hδ (u := u) (hgc k) (hg1 k) hf hf1
    hL3i
  have hfin : ∀ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) < ⊤ := fun ω =>
    qBoundaryMeasure_Icc_lt_top _ _ _ _
  have hint := (EWire.zfin hκ hκ4 hT hδ hB hX hind hϖ (ϖ := ϖ)).2.2.ne
  have hL := tendsto_iter_lintegral (P := P) hfin hint
    (a := fun k => lhsInt κ T B X ϖ
      (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}) (cylPsi u (g k))
        (cylPhi I f))
    (b := lhsInt κ T B X ϖ (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T})
        (cylPsi u (O.indicator 1)) (cylPhi I f))
    (fun k ω x => indicator_apply_le' (fun _ => mul_le_one' (hg1 _ _) (hf1 _)) fun _ => zero_le)
    (ae_all_iff.2 fun k => (hk k).2.2.1) (fun k => (hk k).2.1)
    (Eventually.of_forall fun ω => Eventually.of_forall fun x => by
      simp only [lhsInt, indicator_apply]
      split_ifs
      · exact ENNReal.Tendsto.mul_const (hgt _) (Or.inr (ne_top_of_le_one' (hf1 _)))
      · exact tendsto_const_nhds)
  have hR := tendsto_iter_lintegral (P := P) hfin hint
    (a := fun k => rhsInt κ T B ϖ P' X'
      (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}) (cylPsi u (g k))
        (cylPhi I f))
    (b := rhsInt κ T B ϖ P' X' (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T})
        (cylPsi u (O.indicator 1)) (cylPhi I f))
    (fun k ω x => indicator_apply_le' (fun _ => mul_le_one' (hg1 _ _)
      (lintegral_le_one_of_le_one fun _ => hf1 _)) fun _ => zero_le)
    (ae_all_iff.2 fun k => (hk k).2.2.2.2) (fun k => (hk k).2.2.2.1)
    (Eventually.of_forall fun ω => Eventually.of_forall fun x => by
      simp only [rhsInt, indicator_apply]
      split_ifs
      · exact ENNReal.Tendsto.mul_const (hgt _)
          (Or.inr (ne_top_of_le_one' (lintegral_le_one_of_le_one fun _ => hf1 _)))
      · exact tendsto_const_nhds)
  exact ⟨tendsto_nhds_unique hL.1 (hR.1.congr fun k => ((hk k).1).symm),
    hL.2.1, hL.2.2, hR.2.1, hR.2.2⟩

omit [IsProbabilityMeasure P] in
theorem tsum_indicator_one_disjoint {E : Type*} {f : ℕ → Set E}
    (hd : Pairwise (Function.onFun Disjoint f)) (p : E) :
    ∑' i, (f i).indicator (1 : E → ℝ≥0∞) p = (⋃ i, f i).indicator 1 p := by
  by_cases hp : p ∈ ⋃ i, f i
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hp
    rw [indicator_of_mem hp, tsum_eq_single i fun j hj =>
      indicator_of_notMem (fun hj' => Set.disjoint_left.1 (hd hj) hj' hi) _, indicator_of_mem hi]
  · rw [indicator_of_notMem hp]
    exact ENNReal.tsum_eq_zero.2 fun i => indicator_of_notMem (fun h => hp (mem_iUnion.2 ⟨i, h⟩)) _

/-- Pointwise algebra of `s.indicator (1_C(q) · φ)` in the set `C`. -/
theorem indMul_facts {E : Type*} (s : Set ℝ) (q : ℝ → E) (φ : ℝ → ℝ≥0∞) (x : ℝ) :
    (s.indicator (fun x => (∅ : Set E).indicator 1 (q x) * φ x) x = 0) ∧
    (∀ C : Set E, s.indicator (fun x => C.indicator 1 (q x) * φ x) x ≤
      s.indicator (fun x => (univ : Set E).indicator 1 (q x) * φ x) x) ∧
    (∀ C : Set E, s.indicator (fun x => Cᶜ.indicator 1 (q x) * φ x) x =
      s.indicator (fun x => (univ : Set E).indicator 1 (q x) * φ x) x -
        s.indicator (fun x => C.indicator 1 (q x) * φ x) x) ∧
    (∀ f : ℕ → Set E, Pairwise (Function.onFun Disjoint f) →
      s.indicator (fun x => (⋃ i, f i).indicator 1 (q x) * φ x) x =
        ∑' i, s.indicator (fun x => (f i).indicator 1 (q x) * φ x) x) ∧
    (φ x ≤ 1 → ∀ C : Set E, s.indicator (fun x => C.indicator 1 (q x) * φ x) x ≤ 1) := by
  refine ⟨by simp, fun C => ?_, fun C => ?_, fun f hd => ?_, fun h1 C => ?_⟩
  · by_cases hx : x ∈ s <;> by_cases hq : q x ∈ C <;> simp [hx, hq]
  · by_cases hx : x ∈ s <;> by_cases hq : q x ∈ C <;> simp [hx, hq]
  · by_cases hx : x ∈ s
    · simp only [indicator_of_mem hx]
      rw [← tsum_indicator_one_disjoint hd, ENNReal.tsum_mul_right]
    · simp [indicator_of_notMem hx]
  · by_cases hx : x ∈ s <;> by_cases hq : q x ∈ C <;> simp [hx, hq, h1]

/-- **Stage 1, finite-dimensional Borel sets.** E4 (with measurability) for `Ψ = 1_S(x, d.1∘u,
d.2∘u)`, `S` Borel, `Φ` continuous cylinder (Dynkin from the open sets, `goodEq_of_pi`). -/
theorem goodEq_borel_psi (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X' : Ω' → FieldSample} (hX' : IsFreeGFFModConstH X' P') {δ : ℝ} (hδ : 0 < δ)
    {m : ℕ} (u : Fin m → ℝ≥0)
    {m' : ℕ} {I : Fin m' → ℕ} {f : (Fin m' → ℝ) → ℝ≥0∞} (hf : Continuous f) (hf1 : ∀ c, f c ≤ 1)
    (hL3i : ∀ᵐ ω ∂P, ∀ x < 0, ∀ s, 0 ≤ s → s < T → IsLive (Vr κ T B ω) s x →
      ContinuousWithinAt (fun s => ∫⁻ ω', cylPhi I f (coordsFull
          (targetField κ (Vr κ T B ω) s ϖ x (X' ω'))) ∂P') (Ici s) s) :
    ∀ S : Set (ℝ × (Fin m → ℝ) × (Fin m → ℝ)), MeasurableSet S →
    GoodEq P (fun ω => nuPalm κ T B X ϖ ω) (Icc (-δ) 0)
      (lhsInt κ T B X ϖ (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T})
        (cylPsi u (S.indicator 1)) (cylPhi I f))
      (rhsInt κ T B ϖ P' X' (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T})
        (cylPsi u (S.indicator 1)) (cylPhi I f)) := by
  have hfin : ∀ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) < ⊤ := fun ω =>
    qBoundaryMeasure_Icc_lt_top _ _ _ _
  have hint := (EWire.zfin hκ hκ4 hT hδ hB hX hind hϖ (ϖ := ϖ)).2.2.ne
  have hFL := fun ω x => indMul_facts (E := ℝ × (Fin m → ℝ) × (Fin m → ℝ))
    {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}
    (fun x => (x, fun j => (Vstop κ T (realHitTime (Vr κ T B ω) x).toReal B ω) (u j),
      fun j => W0p κ T B ω (u j)))
    (fun x => cylPhi I f (coordsFull (addConst (Yf κ T (realHitTime (Vr κ T B ω) x).toReal B X ω)
        (-(mReg κ T B X ϖ ω))))) x
  have hFR := fun ω x => indMul_facts (E := ℝ × (Fin m → ℝ) × (Fin m → ℝ))
    {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}
    (fun x => (x, fun j => (Vstop κ T (realHitTime (Vr κ T B ω) x).toReal B ω) (u j),
      fun j => W0p κ T B ω (u j)))
    (fun x => ∫⁻ ω', cylPhi I f (coordsFull (targetColl κ (Vr κ T B ω)
        (realHitTime (Vr κ T B ω) x).toReal ϖ (X' ω'))) ∂P') x
  exact goodEq_of_pi hfin hint
    (fun C => lhsInt κ T B X ϖ (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T})
      (cylPsi u (C.indicator 1)) (cylPhi I f))
    (fun C => rhsInt κ T B ϖ P' X' (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T})
      (cylPsi u (C.indicator 1)) (cylPhi I f))
    (fun C ω x => (hFL ω x).2.2.2.2 (hf1 _) C)
    (fun C ω x => (hFR ω x).2.2.2.2 (lintegral_le_one_of_le_one fun _ => hf1 _) C)
    (fun ω x => (hFL ω x).1) (fun ω x => (hFR ω x).1)
    (fun C _ ω x => (hFL ω x).2.1 C) (fun C _ ω x => (hFR ω x).2.1 C)
    (fun C _ ω x => (hFL ω x).2.2.1 C) (fun C _ ω x => (hFR ω x).2.2.1 C)
    (fun g hd _ ω x => (hFL ω x).2.2.2.1 g hd) (fun g hd _ ω x => (hFR ω x).2.2.2.1 g hd)
    BorelSpace.measurable_eq isPiSystem_isOpen
    (goodEq_open_psi hκ hκ4 hT hB hX hind hϖ hX' hδ u isOpen_univ hf hf1 hL3i)
    (fun C hC => goodEq_open_psi hκ hκ4 hT hB hX hind hϖ hX' hδ u hC hf hf1 hL3i)

end E4Grid
end QuantumZipper
