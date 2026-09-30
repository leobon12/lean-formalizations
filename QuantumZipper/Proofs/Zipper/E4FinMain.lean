import QuantumZipper.Proofs.Zipper.E4FinBasic
import QuantumZipper.Proofs.Zipper.E5Stmt

/-!
# E4-MC, indicator stages: `Ψ = 1_D`, `Φ = 1_C` for all measurable `D`, `C`

`handoff/E4.md`, item E4 (monotone class). With `hL3i` (`L3iHyp`) for all continuous cylinder
`Φ`:
* `e4good_S1`: `Ψ = 1_D` (`D ⊆ ℝ × paths²` measurable), `Φ = cylPhi I f` continuous `≤ 1`
  (Dynkin over the cylinder generators `genE` from `goodEq_borel_psi`);
* `e4good_S2`: `Φ = 1_O ∘ cylN I`, `O` open (dominated convergence from `S1`,
  `exists_approx_open`);
* `e4good_S3`: `Φ = 1_C`, `C ⊆ ℕ → ℝ` measurable (Dynkin over `genN`; the Φ-dependence is written
  through the laws `δ_{φ}` resp. `P' ∘ r⁻¹` so that `indMeas_facts` applies).

Standard Dynkin / dominated-convergence arguments (Kallenberg, *Foundations*, Thm 1.1, Thm 1.21);
own bookkeeping. Part of the proof of Sheffield, arXiv:1012.4797, Lemma 5.6 (pp. 66–68).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E4Grid

open B2 E1 CoordsFull PalmNorm

/-- The interior form `hL3i` of L3, for every continuous cylinder `Φ ≤ 1`. -/
def L3iHyp {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ϖ : Measure ℂ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (X' : Ω' → FieldSample) :
    Prop :=
  ∀ (m' : ℕ) (I : Fin m' → ℕ) (f : (Fin m' → ℝ) → ℝ≥0∞), Continuous f → (∀ c, f c ≤ 1) →
    ∀ᵐ ω ∂P, ∀ x < 0, ∀ s, 0 ≤ s → s < T → IsLive (Vr κ T B ω) s x →
      ContinuousWithinAt (fun s => ∫⁻ ω', cylPhi I f (coordsFull
          (targetField κ (Vr κ T B ω) s ϖ x (X' ω'))) ∂P') (Ici s) s

/-- E4 with the a.e.-measurability, for `Ψ(x, d) = ψ(x, d)` and `Φ`. -/
def E4Good {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (X : Ω → FieldSample) (ϖ : Measure ℂ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (X' : Ω' → FieldSample) (δ : ℝ) (ψ : CfgE → ℝ≥0∞) (Φ : (ℕ → ℝ) → ℝ≥0∞) : Prop :=
  GoodEq P (fun ω => nuPalm κ T B X ϖ ω) (Icc (-δ) 0)
    (lhsInt κ T B X ϖ (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T})
      (fun x d => ψ (x, d)) Φ)
    (rhsInt κ T B ϖ P' X' (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T})
      (fun x d => ψ (x, d)) Φ)

theorem measurable_coordsFull_targetColl {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {X' : Ω' → FieldSample} (hX' : IsFreeGFFModConstH X' P') (κ : ℝ) (V : ℝ → ℝ) (t : ℝ)
    (ϖ : Measure ℂ) : Measurable fun ω' => coordsFull (targetColl κ V t ϖ (X' ω')) := by
  simp_rw [coordsFull_targetColl]
  exact measurable_pi_iff.2 fun j => measurable_const.add
    ((hX'.measurable_coord _).sub (hX'.measurable_coord _))

theorem indicator_one_le_one {α : Type*} (s : Set α) (p : α) :
    s.indicator (1 : α → ℝ≥0∞) p ≤ 1 :=
  indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X' : Ω' → FieldSample}

/-- **S1.** `Ψ = 1_D`, `Φ` continuous cylinder. -/
theorem e4good_S1 (hS : E5.Setup κ T P B X ϖ) (hX' : IsFreeGFFModConstH X' P')
    (hL : L3iHyp P κ T B ϖ P' X') {δ : ℝ} (hδ : 0 < δ)
    {m' : ℕ} {I : Fin m' → ℕ} {f : (Fin m' → ℝ) → ℝ≥0∞} (hf : Continuous f) (hf1 : ∀ c, f c ≤ 1)
    (D : Set CfgE) (hD : MeasurableSet D) :
    E4Good P κ T B X ϖ P' X' δ (D.indicator 1) (cylPhi I f) := by
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := hS
  have hfin : ∀ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) < ⊤ := fun ω =>
    qBoundaryMeasure_Icc_lt_top _ _ _ _
  have hint := (EWire.zfin hκ hκ4 hT hδ hB hX hind hϖ (ϖ := ϖ)).2.2.ne
  have hFL := fun ω x => indMul_facts (E := CfgE)
    {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}
    (fun x => (x, (Vstop κ T (realHitTime (Vr κ T B ω) x).toReal B ω, W0p κ T B ω)))
    (fun x => cylPhi I f (coordsFull (addConst (Yf κ T (realHitTime (Vr κ T B ω) x).toReal B X ω)
        (-(mReg κ T B X ϖ ω))))) x
  have hFR := fun ω x => indMul_facts (E := CfgE)
    {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}
    (fun x => (x, (Vstop κ T (realHitTime (Vr κ T B ω) x).toReal B ω, W0p κ T B ω)))
    (fun x => ∫⁻ ω', cylPhi I f (coordsFull (targetColl κ (Vr κ T B ω)
        (realHitTime (Vr κ T B ω) x).toReal ϖ (X' ω'))) ∂P') x
  have hbasic : ∀ C ∈ genE, E4Good P κ T B X ϖ P' X' δ (C.indicator 1) (cylPhi I f) := by
    rintro _ ⟨m, u, S, hS, rfl⟩
    exact goodEq_borel_psi hκ hκ4 hT hB hX hind hϖ hX' hδ u hf hf1 (hL m' I f hf hf1) S hS
  exact goodEq_of_pi hfin hint
    (fun C => lhsInt κ T B X ϖ (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T})
      (fun x d => C.indicator 1 (x, d)) (cylPhi I f))
    (fun C => rhsInt κ T B ϖ P' X' (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T})
      (fun x d => C.indicator 1 (x, d)) (cylPhi I f))
    (fun C ω x => (hFL ω x).2.2.2.2 (hf1 _) C)
    (fun C ω x => (hFR ω x).2.2.2.2 (lintegral_le_one_of_le_one fun _ => hf1 _) C)
    (fun ω x => (hFL ω x).1) (fun ω x => (hFR ω x).1)
    (fun C _ ω x => (hFL ω x).2.1 C) (fun C _ ω x => (hFR ω x).2.1 C)
    (fun C _ ω x => (hFL ω x).2.2.1 C) (fun C _ ω x => (hFR ω x).2.2.1 C)
    (fun g hd _ ω x => (hFL ω x).2.2.2.1 g hd) (fun g hd _ ω x => (hFR ω x).2.2.2.1 g hd)
    generate_genE isPiSystem_genE
    (hbasic univ ⟨0, Fin.elim0, univ, MeasurableSet.univ, preimage_univ.symm⟩) hbasic D hD

/-- **S2.** `Ψ = 1_D`, `Φ = 1_O ∘ cylN I` with `O` open. -/
theorem e4good_S2 (hS : E5.Setup κ T P B X ϖ) (hX' : IsFreeGFFModConstH X' P')
    (hL : L3iHyp P κ T B ϖ P' X') {δ : ℝ} (hδ : 0 < δ) (D : Set CfgE) (hD : MeasurableSet D)
    {m' : ℕ} (I : Fin m' → ℕ) {O : Set (Fin m' → ℝ)} (hO : IsOpen O) :
    E4Good P κ T B X ϖ P' X' δ (D.indicator 1) (cylPhi I (O.indicator 1)) := by
  obtain ⟨g, hgc, hg1, hgt⟩ := exists_approx_open hO
  have hk := fun k => e4good_S1 hS hX' hL hδ (I := I) (hgc k) (hg1 k) D hD
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := hS
  have hfin : ∀ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) < ⊤ := fun ω =>
    qBoundaryMeasure_Icc_lt_top _ _ _ _
  have hint := (EWire.zfin hκ hκ4 hT hδ hB hX hind hϖ (ϖ := ϖ)).2.2.ne
  have hI : Measurable fun c : ℕ → ℝ => fun j => c (I j) :=
    measurable_pi_iff.2 fun j => measurable_pi_apply (I j)
  have hL' := tendsto_iter_lintegral (P := P) hfin hint
    (a := fun k => lhsInt κ T B X ϖ
      (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T})
        (fun x d => D.indicator 1 (x, d)) (cylPhi I (g k)))
    (b := lhsInt κ T B X ϖ (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T})
        (fun x d => D.indicator 1 (x, d)) (cylPhi I (O.indicator 1)))
    (fun k ω x => indicator_apply_le' (fun _ => mul_le_one' (indicator_one_le_one _ _)
      (hg1 _ _)) fun _ => zero_le)
    (ae_all_iff.2 fun k => (hk k).2.2.1) (fun k => (hk k).2.1)
    (Eventually.of_forall fun ω => Eventually.of_forall fun x => by
      by_cases hx : x ∈ {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}
      · simp only [lhsInt, indicator_of_mem hx]
        exact ENNReal.Tendsto.const_mul (hgt _)
          (Or.inr (ne_top_of_le_one' (indicator_one_le_one _ _)))
      · simp only [lhsInt, indicator_of_notMem hx]
        exact tendsto_const_nhds)
  have hR' := tendsto_iter_lintegral (P := P) hfin hint
    (a := fun k => rhsInt κ T B ϖ P' X'
      (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T})
        (fun x d => D.indicator 1 (x, d)) (cylPhi I (g k)))
    (b := rhsInt κ T B ϖ P' X' (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T})
        (fun x d => D.indicator 1 (x, d)) (cylPhi I (O.indicator 1)))
    (fun k ω x => indicator_apply_le' (fun _ => mul_le_one' (indicator_one_le_one _ _)
      (lintegral_le_one_of_le_one fun _ => hg1 _ _)) fun _ => zero_le)
    (ae_all_iff.2 fun k => (hk k).2.2.2.2) (fun k => (hk k).2.2.2.1)
    (Eventually.of_forall fun ω => Eventually.of_forall fun x => by
      by_cases hx : x ∈ {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}
      · simp only [rhsInt, indicator_of_mem hx]
        refine ENNReal.Tendsto.const_mul ?_
          (Or.inr (ne_top_of_le_one' (indicator_one_le_one _ _)))
        exact tendsto_lintegral_of_dominated_convergence (fun _ => 1)
          (fun k => (hgc k).measurable.comp (hI.comp
            (measurable_coordsFull_targetColl hX' κ _ _ ϖ)))
          (fun k => Eventually.of_forall fun ω' => hg1 k _) (by simp)
          (Eventually.of_forall fun ω' => hgt _)
      · simp only [rhsInt, indicator_of_notMem hx]
        exact tendsto_const_nhds)
  exact ⟨tendsto_nhds_unique hL'.1 (hR'.1.congr fun k => ((hk k).1).symm),
    hL'.2.1, hL'.2.2, hR'.2.1, hR'.2.2⟩

/-- **S3.** `Ψ = 1_D`, `Φ = 1_C` for measurable `C ⊆ ℕ → ℝ`. -/
theorem e4good_S3 (hS : E5.Setup κ T P B X ϖ) (hX' : IsFreeGFFModConstH X' P')
    (hL : L3iHyp P κ T B ϖ P' X') {δ : ℝ} (hδ : 0 < δ) (D : Set CfgE) (hD : MeasurableSet D)
    (C : Set (ℕ → ℝ)) (hC : MeasurableSet C) :
    E4Good P κ T B X ϖ P' X' δ (D.indicator 1) (C.indicator 1) := by
  have hS' := hS
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := hS'
  have hfin : ∀ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) < ⊤ := fun ω =>
    qBoundaryMeasure_Icc_lt_top _ _ _ _
  have hint := (EWire.zfin hκ hκ4 hT hδ hB hX hind hϖ (ϖ := ϖ)).2.2.ne
  -- the data
  set A : Ω → Set ℝ := fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T} with hA
  set a : Ω → ℝ → ℝ≥0∞ := fun ω x =>
    D.indicator 1 (x, (Vstop κ T (realHitTime (Vr κ T B ω) x).toReal B ω, W0p κ T B ω)) with ha
  set φ : Ω → ℝ → ℕ → ℝ := fun ω x => coordsFull (addConst
    (Yf κ T (realHitTime (Vr κ T B ω) x).toReal B X ω) (-(mReg κ T B X ϖ ω))) with hφ
  set r : Ω → ℝ → Ω' → ℕ → ℝ := fun ω x ω' => coordsFull (targetColl κ (Vr κ T B ω)
    (realHitTime (Vr κ T B ω) x).toReal ϖ (X' ω')) with hr
  have hrm : ∀ ω x, Measurable (r ω x) := fun ω x =>
    measurable_coordsFull_targetColl hX' κ _ _ ϖ
  have hPr : ∀ ω x, IsProbabilityMeasure (P'.map (r ω x)) := fun ω x => inferInstance
  have ha1 : ∀ ω x, a ω x ≤ 1 := fun ω x => indicator_one_le_one _ _
  have hFL := fun ω x => indMeas_facts (A ω) (a ω) (fun x => Measure.dirac (φ ω x)) x (ha1 ω x)
  have hFR := fun ω x =>
    haveI := hPr ω
    indMeas_facts (A ω) (a ω) (fun x => P'.map (r ω x)) x (ha1 ω x)
  have eL : ∀ C : Set (ℕ → ℝ), MeasurableSet C →
      lhsInt κ T B X ϖ A (fun x d => D.indicator 1 (x, d)) (C.indicator 1) =
        fun ω x => (A ω).indicator (fun x => a ω x * Measure.dirac (φ ω x) C) x := by
    intro C hC
    funext ω x
    simp only [lhsInt, Measure.dirac_apply' _ hC]
    rfl
  have eR : ∀ C : Set (ℕ → ℝ), MeasurableSet C →
      rhsInt κ T B ϖ P' X' A (fun x d => D.indicator 1 (x, d)) (C.indicator 1) =
        fun ω x => (A ω).indicator (fun x => a ω x * P'.map (r ω x) C) x := by
    intro C hC
    funext ω x
    simp only [rhsInt]
    congr 1
    funext x
    rw [← lintegral_indicator_one hC, lintegral_map (measurable_one.indicator hC) (hrm ω x)]
  have key := goodEq_of_pi (E := ℕ → ℝ) hfin hint
    (fun C ω x => (A ω).indicator (fun x => a ω x * Measure.dirac (φ ω x) C) x)
    (fun C ω x => (A ω).indicator (fun x => a ω x * P'.map (r ω x) C) x)
    (fun C ω x => (hFL ω x).2.2.2.2 C) (fun C ω x => (hFR ω x).2.2.2.2 C)
    (fun ω x => (hFL ω x).1) (fun ω x => (hFR ω x).1)
    (fun C _ ω x => (hFL ω x).2.1 C) (fun C _ ω x => (hFR ω x).2.1 C)
    (fun C hC ω x => (hFL ω x).2.2.1 C hC) (fun C hC ω x => (hFR ω x).2.2.1 C hC)
    (fun g hd hm ω x => (hFL ω x).2.2.2.1 g hd hm) (fun g hd hm ω x => (hFR ω x).2.2.2.1 g hd hm)
    generate_genN isPiSystem_genN
  have hbasic : ∀ C ∈ genN, E4Good P κ T B X ϖ P' X' δ (D.indicator 1) (C.indicator 1) := by
    rintro _ ⟨m, I, O, hO, rfl⟩
    exact e4good_S2 hS hX' hL hδ D hD I hO
  have hmeasN : ∀ C ∈ genN, MeasurableSet C := by
    rintro _ ⟨m, I, O, hO, rfl⟩
    exact (measurable_pi_iff.2 fun j => measurable_pi_apply (I j)) hO.measurableSet
  have hconv : ∀ C, MeasurableSet C →
      E4Good P κ T B X ϖ P' X' δ (D.indicator 1) (C.indicator 1) →
      GoodEq P (fun ω => nuPalm κ T B X ϖ ω) (Icc (-δ) 0)
        (fun ω x => (A ω).indicator (fun x => a ω x * Measure.dirac (φ ω x) C) x)
        (fun ω x => (A ω).indicator (fun x => a ω x * P'.map (r ω x) C) x) := by
    intro C hC h
    unfold E4Good at h
    rw [eL C hC, eR C hC] at h
    exact h
  have hgood := key
    (hconv univ MeasurableSet.univ (hbasic univ ⟨0, Fin.elim0, univ, isOpen_univ, rfl⟩))
    (fun C hC => hconv C (hmeasN C hC) (hbasic C hC)) C hC
  unfold E4Good
  rw [eL C hC, eR C hC]
  exact hgood

end E4Grid
end QuantumZipper
