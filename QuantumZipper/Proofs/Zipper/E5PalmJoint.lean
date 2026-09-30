import QuantumZipper.Proofs.Zipper.E4L3i

/-!
# E5-PALM, part 1: E4 for joint tests (Dynkin extension of `E4Grid.e4good_all`)

Task E5-PALM (Theorem 1.3, node E5, blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4, step (1)).
Sheffield, arXiv:1012.4797, §5.4 (pp. 66–72), proof of Lemma 5.6: under the Palm measure
`P ⊗ ν_ω|_{[−δ,0] ∩ {τ<T}}`, the normalized collided field is a free field `X'` (moved by the
reverse Loewner map at the collision time) independent of the driver data. E4
(`E4Grid.e4good_all`, `E4Grid.l3iStmt`) states this for **product** tests
`Ψ(x, V^τ, W⁰) · Φ(coordsFull …)`. Here it is extended to **joint** tests
`H(x, V^τ, W⁰, coordsFull …)`, `H` measurable on `CfgE × (ℕ → ℝ)`, keeping the
a.e.-measurability bookkeeping (`E4Grid.GoodEq`):

* `e4good_joint_set`: `H = 1_C`, `C` measurable (Dynkin over rectangles, `E4Grid.goodEq_of_pi`,
  mathlib `generateFrom_prod`, `isPiSystem_prod`);
* `e4good_joint`: all measurable `H` (monotone class, `E4Grid.goodEq_induction`);
* `e4_joint`: the resulting identity of iterated integrals (unconditional).

Standard Dynkin π-λ / monotone-class argument (Kallenberg, *Foundations of Modern Probability*,
2nd ed., Thm 1.1 and Lemma 1.35 style extension from rectangles); own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open B2 E1 CoordsFull E4Grid

/-- The collision event `{τ_x < T}`. -/
def palmA {Ω : Type*} (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : Set ℝ :=
  {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}

/-- The collision time `τ_x`. -/
def palmTau {Ω : Type*} (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (x : ℝ) : ℝ :=
  (realHitTime (Vr κ T B ω) x).toReal

/-- The driver data `(x, V^τ, W⁰)` of E4. -/
def palmQ {Ω : Type*} (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (x : ℝ) : CfgE :=
  (x, (Vstop κ T (palmTau κ T B ω x) B ω, W0p κ T B ω))

/-- The field coordinates of E4's left side: `coordsFull (Y_τ − m)`. -/
def palmPhi {Ω : Type*} (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ)
    (ω : Ω) (x : ℝ) : ℕ → ℝ :=
  coordsFull (addConst (Yf κ T (palmTau κ T B ω x) B X ω) (-(mReg κ T B X ϖ ω)))

/-- The field coordinates of E4's right side: `coordsFull (targetColl … X')`. -/
def palmR {Ω Ω' : Type*} (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (ϖ : Measure ℂ) (X' : Ω' → FieldSample)
    (ω : Ω) (x : ℝ) (ω' : Ω') : ℕ → ℝ :=
  coordsFull (targetColl κ (Vr κ T B ω) (palmTau κ T B ω x) ϖ (X' ω'))

/-- Left integrand of joint E4. -/
def jointL {Ω : Type*} (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ)
    (H : CfgE × (ℕ → ℝ) → ℝ≥0∞) (ω : Ω) (x : ℝ) : ℝ≥0∞ :=
  (palmA κ T B ω).indicator (fun x => H (palmQ κ T B ω x, palmPhi κ T B X ϖ ω x)) x

/-- Right integrand of joint E4. -/
def jointR {Ω Ω' : Type*} [MeasurableSpace Ω'] (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (ϖ : Measure ℂ)
    (P' : Measure Ω') (X' : Ω' → FieldSample) (H : CfgE × (ℕ → ℝ) → ℝ≥0∞) (ω : Ω) (x : ℝ) :
    ℝ≥0∞ :=
  (palmA κ T B ω).indicator (fun x => ∫⁻ ω', H (palmQ κ T B ω x, palmR κ T B ϖ X' ω x ω') ∂P') x

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X' : Ω' → FieldSample}

theorem measurable_palmR (hX' : IsFreeGFFModConstH X' P') (ω : Ω) (x : ℝ) :
    Measurable (palmR κ T B ϖ X' ω x) :=
  measurable_coordsFull_targetColl hX' κ _ _ ϖ

theorem measurable_palmPair (hX' : IsFreeGFFModConstH X' P') (ω : Ω) (x : ℝ) :
    Measurable fun ω' => (palmQ κ T B ω x, palmR κ T B ϖ X' ω x ω') :=
  measurable_const.prodMk (measurable_palmR hX' ω x)

/-- **Joint E4, sets.** -/
theorem e4good_joint_set (hS : E5.Setup κ T P B X ϖ) (hX' : IsFreeGFFModConstH X' P') {δ : ℝ}
    (hδ : 0 < δ) (C : Set (CfgE × (ℕ → ℝ))) (hC : MeasurableSet C) :
    GoodEq P (fun ω => nuPalm κ T B X ϖ ω) (Icc (-δ) 0)
      (jointL κ T B X ϖ (C.indicator 1)) (jointR κ T B ϖ P' X' (C.indicator 1)) := by
  have hS' := hS
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := hS'
  have hfin : ∀ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) < ⊤ := fun ω =>
    qBoundaryMeasure_Icc_lt_top _ _ _ _
  have hint := (EWire.zfin hκ hκ4 hT hδ hB hX hind hϖ (ϖ := ϖ)).2.2.ne
  have hL := l3iStmt κ T P B X ϖ P' X' hS hX'
  set A : Ω → Set ℝ := palmA κ T B with hA
  set μL : Ω → ℝ → Measure (CfgE × (ℕ → ℝ)) := fun ω x =>
    Measure.dirac (palmQ κ T B ω x, palmPhi κ T B X ϖ ω x) with hμL
  set μR : Ω → ℝ → Measure (CfgE × (ℕ → ℝ)) := fun ω x =>
    P'.map (fun ω' => (palmQ κ T B ω x, palmR κ T B ϖ X' ω x ω')) with hμR
  have hPR : ∀ ω x, IsProbabilityMeasure (μR ω x) := fun ω x => inferInstance
  have hFL := fun ω x => indMeas_facts (A ω) (fun _ => 1) (μL ω) x le_rfl
  have hFR := fun ω x =>
    haveI : ∀ y, IsProbabilityMeasure (μR ω y) := hPR ω
    indMeas_facts (A ω) (fun _ => 1) (μR ω) x le_rfl
  have eL : ∀ C : Set (CfgE × (ℕ → ℝ)), MeasurableSet C →
      jointL κ T B X ϖ (C.indicator 1) =
        fun ω x => (A ω).indicator (fun x => (fun _ => (1 : ℝ≥0∞)) x * μL ω x C) x := by
    intro C hC
    funext ω x
    simp only [jointL, hμL, Measure.dirac_apply' _ hC, one_mul]
    rfl
  have eR : ∀ C : Set (CfgE × (ℕ → ℝ)), MeasurableSet C →
      jointR κ T B ϖ P' X' (C.indicator 1) =
        fun ω x => (A ω).indicator (fun x => (fun _ => (1 : ℝ≥0∞)) x * μR ω x C) x := by
    intro C hC
    funext ω x
    simp only [jointR, hμR, one_mul]
    congr 1
    funext x
    rw [← lintegral_indicator_one hC,
      lintegral_map (measurable_one.indicator hC) (measurable_palmPair hX' ω x)]
  have key := goodEq_of_pi (E := CfgE × (ℕ → ℝ)) hfin hint
    (fun C ω x => (A ω).indicator (fun x => (fun _ => (1 : ℝ≥0∞)) x * μL ω x C) x)
    (fun C ω x => (A ω).indicator (fun x => (fun _ => (1 : ℝ≥0∞)) x * μR ω x C) x)
    (fun C ω x => (hFL ω x).2.2.2.2 C) (fun C ω x => (hFR ω x).2.2.2.2 C)
    (fun ω x => (hFL ω x).1) (fun ω x => (hFR ω x).1)
    (fun C _ ω x => (hFL ω x).2.1 C) (fun C _ ω x => (hFR ω x).2.1 C)
    (fun C hC ω x => (hFL ω x).2.2.1 C hC) (fun C hC ω x => (hFR ω x).2.2.1 C hC)
    (fun g hd hm ω x => (hFL ω x).2.2.2.1 g hd hm) (fun g hd hm ω x => (hFR ω x).2.2.2.1 g hd hm)
    generateFrom_prod.symm isPiSystem_prod
  -- rectangles
  have hrect : ∀ D : Set CfgE, MeasurableSet D → ∀ C' : Set (ℕ → ℝ), MeasurableSet C' →
      GoodEq P (fun ω => nuPalm κ T B X ϖ ω) (Icc (-δ) 0)
        (fun ω x => (A ω).indicator (fun x => (fun _ => (1 : ℝ≥0∞)) x * μL ω x (D ×ˢ C')) x)
        (fun ω x => (A ω).indicator (fun x => (fun _ => (1 : ℝ≥0∞)) x * μR ω x (D ×ˢ C')) x) := by
    intro D hD C' hC'
    have h4 := e4good_all hS hX' hL hδ (D.indicator 1) (measurable_one.indicator hD)
      (C'.indicator 1) (measurable_one.indicator hC')
    have e1 : (fun ω x => (A ω).indicator (fun x => (fun _ => (1 : ℝ≥0∞)) x * μL ω x (D ×ˢ C')) x)
        = lhsInt κ T B X ϖ A (fun x d => D.indicator 1 (x, d)) (C'.indicator 1) := by
      rw [← eL _ (hD.prod hC')]
      funext ω x
      simp only [jointL, lhsInt, Set.indicator_prod_one]
      rfl
    have e2 : (fun ω x => (A ω).indicator (fun x => (fun _ => (1 : ℝ≥0∞)) x * μR ω x (D ×ˢ C')) x)
        = rhsInt κ T B ϖ P' X' A (fun x d => D.indicator 1 (x, d)) (C'.indicator 1) := by
      rw [← eR _ (hD.prod hC')]
      funext ω x
      simp only [jointR, rhsInt, Set.indicator_prod_one]
      congr 1
      funext x
      exact lintegral_const_mul _ ((measurable_one.indicator hC').comp (measurable_palmR hX' ω x))
    rw [e1, e2]
    exact h4
  have hbasic : ∀ C ∈ image2 (· ×ˢ ·) {s : Set CfgE | MeasurableSet s}
      {t : Set (ℕ → ℝ) | MeasurableSet t},
      GoodEq P (fun ω => nuPalm κ T B X ϖ ω) (Icc (-δ) 0)
        (fun ω x => (A ω).indicator (fun x => (fun _ => (1 : ℝ≥0∞)) x * μL ω x C) x)
        (fun ω x => (A ω).indicator (fun x => (fun _ => (1 : ℝ≥0∞)) x * μR ω x C) x) := by
    rintro _ ⟨D, hD, C', hC', rfl⟩
    exact hrect D hD C' hC'
  have huniv := hrect univ MeasurableSet.univ univ MeasurableSet.univ
  rw [univ_prod_univ] at huniv
  rw [eL C hC, eR C hC]
  exact key huniv hbasic C hC

/-- **Joint E4, all measurable tests** (with the a.e.-measurability of both sides). -/
theorem e4good_joint (hS : E5.Setup κ T P B X ϖ) (hX' : IsFreeGFFModConstH X' P') {δ : ℝ}
    (hδ : 0 < δ) (H : CfgE × (ℕ → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    GoodEq P (fun ω => nuPalm κ T B X ϖ ω) (Icc (-δ) 0)
      (jointL κ T B X ϖ H) (jointR κ T B ϖ P' X' H) := by
  have hm := measurable_palmPair (κ := κ) (T := T) (B := B) (ϖ := ϖ) hX'
  refine goodEq_induction (β := CfgE × (ℕ → ℝ)) (jointL κ T B X ϖ) (jointR κ T B ϖ P' X')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun s hs => e4good_joint_set hS hX' hδ s hs) H hH
  · intro c s _
    funext ω x
    by_cases hx : x ∈ palmA κ T B ω
    · simp only [jointL, indicator_of_mem hx]
      by_cases hy : (palmQ κ T B ω x, palmPhi κ T B X ϖ ω x) ∈ s <;> simp [hy]
    · simp [jointL, indicator_of_notMem hx]
  · intro c s hs
    funext ω x
    by_cases hx : x ∈ palmA κ T B ω
    · simp only [jointR, indicator_of_mem hx]
      rw [← lintegral_const_mul c (f := fun ω' => s.indicator 1
        (palmQ κ T B ω x, palmR κ T B ϖ X' ω x ω')) ((measurable_one.indicator hs).comp (hm ω x))]
      refine lintegral_congr fun ω' => ?_
      by_cases hy : (palmQ κ T B ω x, palmR κ T B ϖ X' ω x ω') ∈ s <;> simp [hy]
    · simp [jointR, indicator_of_notMem hx]
  · intro f g _ _
    funext ω x
    by_cases hx : x ∈ palmA κ T B ω
    · simp [jointL, indicator_of_mem hx]
    · simp [jointL, indicator_of_notMem hx]
  · intro f g hf _
    funext ω x
    by_cases hx : x ∈ palmA κ T B ω
    · simp only [jointR, indicator_of_mem hx, Pi.add_apply]
      exact lintegral_add_left (hf.comp (hm ω x)) _
    · simp [jointR, indicator_of_notMem hx]
  · intro f _ _
    funext ω x
    by_cases hx : x ∈ palmA κ T B ω
    · simp [jointL, indicator_of_mem hx]
    · simp [jointL, indicator_of_notMem hx]
  · intro f hf hmono
    funext ω x
    by_cases hx : x ∈ palmA κ T B ω
    · simp only [jointR, indicator_of_mem hx]
      exact lintegral_iSup (fun n => (hf n).comp (hm ω x))
        (fun a b hab ω' => hmono hab _)
    · simp [jointR, indicator_of_notMem hx]
  · intro f g _ _ hfg ω x
    by_cases hx : x ∈ palmA κ T B ω
    · simp only [jointL, indicator_of_mem hx]
      exact hfg _
    · simp [jointL, indicator_of_notMem hx]
  · intro f g _ _ hfg ω x
    by_cases hx : x ∈ palmA κ T B ω
    · simp only [jointR, indicator_of_mem hx]
      exact lintegral_mono fun ω' => hfg _
    · simp [jointR, indicator_of_notMem hx]

/-- **Joint E4** (unconditional): for every E5 setup, independent free field `X'`, `δ > 0` and
measurable `H` on `(x, V^τ, W⁰, coordsFull)`, the Palm integral of `H` at the true collided field
equals the Palm integral of the `X'`-average of `H` at the collision target field. -/
theorem e4_joint (hS : E5.Setup κ T P B X ϖ) (hX' : IsFreeGFFModConstH X' P') {δ : ℝ}
    (hδ : 0 < δ) (H : CfgE × (ℕ → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, jointL κ T B X ϖ H ω x ∂nuPalm κ T B X ϖ ω ∂P =
      ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, jointR κ T B ϖ P' X' H ω x ∂nuPalm κ T B X ϖ ω ∂P :=
  (e4good_joint hS hX' hδ H hH).1

end E5
end QuantumZipper
