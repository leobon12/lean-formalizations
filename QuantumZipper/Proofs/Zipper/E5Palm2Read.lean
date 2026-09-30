import QuantumZipper.Proofs.Zipper.E5PalmRepr
import QuantumZipper.Proofs.Zipper.E5Main5
import QuantumZipper.Proofs.LQG.WedgeMeasurable
import QuantumZipper.Proofs.Zipper.E6UpBasic
import QuantumZipper.Proofs.LQG.IndepParams

/-!
# E5-PALM2, part 1: the Palm readability input `PalmReadable` for `locFieldFull`

Task E5-PALM2 (Theorem 1.3, node E5). Sheffield, arXiv:1012.4797, §5.4 (pp. 66–72), proof of
Lemma 5.6. `E5PalmRepr.palm_repr_iter` needs `PalmReadable`: one measurable reader `Rd` of the
E4 data `(x, V^τ, W⁰, coordsFull)` reproducing the local data of E5's zoomed configuration on both
sides of E4. Here `PalmReadable (locG locFieldFull) … (palmRd κ C R Dr)` is **proved**, with the
explicit reader `palmRd`, from two exact named inputs:

* `DrvReadable … Dr`: a jointly measurable driver reader `Dr : CfgE → ℝ → ℝ` reproducing, a.e.
  under the Palm measure on `{τ < T}`, the collided driver `(collided …).2` on `[0, ∞)` (the
  driver is read at the random times `a² min(s, R)`, hence joint measurability in the time);
* `ModelGood`: a.e. under the Palm measure on `{τ < T}`, the collision target field
  `targetColl κ V τ ϖ X'` is `IsLQGGood (√κ)` for `P'`-a.e. `ω'` (the model field is the free
  field plus the `α`-log-singular function `shiftFun`, a quantum-wedge-type field).

The field part needs **no** regularity input: `canonical γ` only reads the regularized circle
averages `avgReg`, which only read the small dyadic circle coordinates (`Factorization.coords`,
Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), §3.1), so
`canonical γ W = resc (Qc γ) (coords W, scaleG γ (coords W))` exactly for good `W`
(`WedgeMeas.canonical_eq_resc`, `WedgeMeas.scaleG_coords`). Goodness of the *true* collided field is
**transferred** from `ModelGood` through E4 itself (`e4good_joint` with the bad-set indicator:
goodness is a measurable function of `coordsFull`), so it is not an extra input.

Own elementary arguments (bookkeeping around E4 and the coordinate factorization of `canonical`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open B2 E1 CoordsFull E4Grid

/-! ## Coordinate algebra -/

/-- Shift of a coordinate vector by the constant `c`. -/
def shv (c : ℝ) (v : ℕ → ℝ) : ℕ → ℝ := fun i => v i + c

theorem measurable_shv (c : ℝ) : Measurable (shv c) :=
  measurable_pi_iff.2 fun i => (measurable_pi_apply i).add measurable_const

theorem coords_addConst_shv (x : FieldSample) (k : ℝ) :
    Factorization.coords (addConst x k) = shv k (Factorization.coords x) := by
  funext j
  simp [Factorization.coords, addConst, shv, measure_univ]

theorem addConst_addConst_e5 (y : FieldSample) (c₁ c₂ : ℝ) :
    addConst (addConst y c₁) c₂ = addConst y (c₁ + c₂) := by
  funext μ; simp only [addConst]; ring

open Classical in
/-- The `locFieldFull` read-off of the full data `dataFull H`. -/
def locOfData (R : ℕ) (d : (ℕ → ℝ) × (TestFun H → ℝ)) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  (fun i => if D3Plus.inBallFull R i then d.1 i else 0,
    fun ρ => if D3Plus.suppIn R ρ then d.2 ρ else 0)

theorem measurable_locOfData (R : ℕ) : Measurable (locOfData R) := by
  classical
  unfold locOfData
  refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_) (measurable_pi_iff.2 fun ρ => ?_)
  · by_cases h : D3Plus.inBallFull R i
    · simp only [h, ite_true]; exact (measurable_pi_apply i).comp measurable_fst
    · simp only [h, ite_false]; exact measurable_const
  · by_cases h : D3Plus.suppIn R ρ
    · simp only [h, ite_true]; exact (measurable_pi_apply ρ).comp measurable_snd
    · simp only [h, ite_false]; exact measurable_const

/-! ## The reader -/

/-- Small-circle coordinates of `W + c`, read from `coordsFull W`. -/
def rdCoords (c : ℝ) (y : ℕ → ℝ) : ℕ → ℝ := shv c (E6.coordsOfFull y)

/-- The canonical scale of `W + c`, read from `coordsFull W` (junk `0` off the good set). -/
def rdScale (γ c : ℝ) (y : ℕ → ℝ) : ℝ := WedgeMeas.scaleG γ (rdCoords c y)

/-- The canonical field of `W + c`, read from `coordsFull W`. -/
def rdField (γ c : ℝ) (y : ℕ → ℝ) : FieldSample :=
  WedgeMeas.resc (Qc γ) (rdCoords c y, rdScale γ c y)

/-- **The Palm reader** at level `C`, radius `R`, driver reader `Dr`. -/
def palmRd (κ C : ℝ) (R : ℕ) (Dr : CfgE → ℝ → ℝ) (p : CfgE × (ℕ → ℝ)) :
    ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) :=
  (D3Plus.locFieldFull R (rdField (Real.sqrt κ) (C / Real.sqrt κ) p.2),
    fun s => Dr p.1 (rdScale (Real.sqrt κ) (C / Real.sqrt κ) p.2 ^ 2 * max (min (s : ℝ) R) 0) /
      rdScale (Real.sqrt κ) (C / Real.sqrt κ) p.2)

theorem measurable_rdCoords (c : ℝ) : Measurable (rdCoords c) :=
  (measurable_shv c).comp E6.measurable_coordsOfFull

theorem measurable_rdScale (γ c : ℝ) : Measurable (rdScale γ c) :=
  (WedgeMeas.measurable_scaleG γ).comp (measurable_rdCoords c)

theorem measurable_palmRd {κ C : ℝ} {R : ℕ} {Dr : CfgE → ℝ → ℝ}
    (hDr : Measurable fun p : CfgE × ℝ => Dr p.1 p.2) : Measurable (palmRd κ C R Dr) := by
  refine Measurable.prodMk ?_ (measurable_pi_iff.2 fun s => ?_)
  · have h := (measurable_locOfData R).comp ((WedgeMeas.measurable_dataFull_resc H
      (Qc (Real.sqrt κ))).comp ((measurable_rdCoords (C / Real.sqrt κ)).prodMk
        (measurable_rdScale (Real.sqrt κ) (C / Real.sqrt κ))))
    exact h.comp measurable_snd
  · have ha : Measurable fun p : CfgE × (ℕ → ℝ) => rdScale (Real.sqrt κ) (C / Real.sqrt κ) p.2 :=
      (measurable_rdScale _ _).comp measurable_snd
    exact (hDr.comp (measurable_fst.prodMk ((ha.pow_const 2).mul measurable_const))).div ha

/-- **Core identity** (deterministic): for `W + c` good and a driver reader agreeing with the
driver on `[0, ∞)`, the local data of the canonicalized configuration are the reader's output. -/
theorem locG_canonConfig_addConst_eq {γ c : ℝ} {Z : FieldSample} (hZ : IsLQGGood γ (addConst Z c))
    (R : ℕ) {d D : ℝ → ℝ} (hD : ∀ u, 0 ≤ u → D u = d u) :
    locG D3Plus.locFieldFull R (canonConfig γ (addConst Z c, d)) =
      (D3Plus.locFieldFull R (rdField γ c (coordsFull Z)),
        fun s : ℝ≥0 => D (rdScale γ c (coordsFull Z) ^ 2 * max (min (s : ℝ) R) 0) /
          rdScale γ c (coordsFull Z)) := by
  have hco : rdCoords c (coordsFull Z) = Factorization.coords (addConst Z c) := by
    rw [rdCoords, E6.coordsOfFull_coordsFull, coords_addConst_shv]
  have hsc : rdScale γ c (coordsFull Z) = scaleParam γ (addConst Z c) := by
    rw [rdScale, hco, WedgeMeas.scaleG_coords hZ]
  have hf : rdField γ c (coordsFull Z) = canonical γ (addConst Z c) := by
    rw [rdField, hsc, hco, WedgeMeas.canonical_eq_resc]
  unfold locG canonConfig
  rw [hf, hsc]
  refine Prod.ext rfl (funext fun s => ?_)
  simp only
  rw [hD _ (mul_nonneg (sq_nonneg _) (le_max_right _ _))]

/-! ## The two named inputs -/

/-- **Driver readability** (named input): a jointly measurable driver reader `Dr` of the E4
driver data `(x, V^τ, W⁰)` reproducing, a.e. under the Palm measure on `{τ < T}`, the collided
driver on `[0, ∞)`. -/
def DrvReadable (κ T : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (X : Ω → FieldSample) (ϖ : Measure ℂ) (δ : ℝ) (Dr : CfgE → ℝ → ℝ) : Prop :=
  (Measurable fun p : CfgE × ℝ => Dr p.1 p.2) ∧
    ∀ᵐ ω ∂P, ∀ᵐ x ∂(nuPalm κ T B X ϖ ω).restrict (Icc (-δ) 0), x ∈ palmA κ T B ω →
      ∀ u : ℝ, 0 ≤ u → Dr (palmQ κ T B ω x) u = (collided κ T B X ω x).2 u

/-- **Goodness of the model field** (named input): a.e. under the Palm measure on `{τ < T}`,
the collision target field of an independent free field is `IsLQGGood (√κ)` a.s. -/
def ModelGood (κ T : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (X : Ω → FieldSample) (ϖ : Measure ℂ) {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    (X' : Ω' → FieldSample) (δ : ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ᵐ x ∂(nuPalm κ T B X ϖ ω).restrict (Icc (-δ) 0), x ∈ palmA κ T B ω →
    ∀ᵐ ω' ∂P', IsLQGGood (Real.sqrt κ)
      (targetColl κ (Vr κ T B ω) (palmTau κ T B ω x) ϖ (X' ω'))

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X' : Ω' → FieldSample}

/-- The non-good set of E4 data (a measurable function of `coordsFull`). -/
def badGood (γ : ℝ) : Set (CfgE × (ℕ → ℝ)) :=
  {p | IsLQGGood γ (Factorization.reconstruct (E6.coordsOfFull p.2))}ᶜ

theorem measurableSet_badGood (γ : ℝ) : MeasurableSet (badGood γ) :=
  (((IndepParams.measurableSet_good_coords γ).preimage E6.measurable_coordsOfFull).preimage
    measurable_snd).compl

theorem notMem_badGood_iff {γ : ℝ} (q : CfgE) (W : FieldSample) :
    (q, coordsFull W) ∉ badGood γ ↔ IsLQGGood γ W := by
  simp only [badGood, mem_compl_iff, not_not, mem_ofPred_eq, E6.coordsOfFull_coordsFull,
    GoodSample.isLQGGood_iff_reconstruct]

/-- **Goodness of the true collided field**, transferred from `ModelGood` through E4. -/
theorem ae_good_true (hS : E5.Setup κ T P B X ϖ) (hX' : IsFreeGFFModConstH X' P') {δ : ℝ}
    (hδ : 0 < δ) (hG : ModelGood κ T P B X ϖ P' X' δ) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂(nuPalm κ T B X ϖ ω).restrict (Icc (-δ) 0), x ∈ palmA κ T B ω →
      IsLQGGood (Real.sqrt κ)
        (addConst (Yf κ T (palmTau κ T B ω x) B X ω) (-(mReg κ T B X ϖ ω))) := by
  set γ := Real.sqrt κ
  have e := e4good_joint hS hX' hδ ((badGood γ).indicator 1)
    (measurable_one.indicator (measurableSet_badGood γ))
  have hR : ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, jointR κ T B ϖ P' X' ((badGood γ).indicator 1) ω x
      ∂nuPalm κ T B X ϖ ω ∂P = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hG] with ω hω
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hω] with x hx
    by_cases hA : x ∈ palmA κ T B ω
    · simp only [jointR, indicator_of_mem hA]
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      filter_upwards [hx hA] with ω' h'
      exact indicator_of_notMem ((notMem_badGood_iff _ _).2 h') _
    · simp [jointR, indicator_of_notMem hA]
  have hL := e.1.trans hR
  rw [lintegral_eq_zero_iff' e.2.1] at hL
  filter_upwards [hL, e.2.2.1] with ω hω hmω
  have h2 := (lintegral_eq_zero_iff' hmω).1 hω
  filter_upwards [h2] with x hx hA
  have h3 : (badGood γ).indicator (1 : CfgE × (ℕ → ℝ) → ℝ≥0∞)
      (palmQ κ T B ω x, palmPhi κ T B X ϖ ω x) = 0 := by
    have := hx
    simp only [jointL, indicator_of_mem hA, Pi.zero_apply] at this
    exact this
  rw [indicator_apply_eq_zero] at h3
  by_contra hng
  exact one_ne_zero (h3 (by
    change (palmQ κ T B ω x, coordsFull _) ∈ badGood γ
    exact fun h => hng ((notMem_badGood_iff (palmQ κ T B ω x) _).1 fun h' => h' h)))

/-- **`PalmReadable` for the rich local data**, from driver readability and model goodness. -/
theorem palmReadable_of (hS : E5.Setup κ T P B X ϖ) (hX' : IsFreeGFFModConstH X' P') {δ : ℝ}
    (hδ : 0 < δ) {Dr : CfgE → ℝ → ℝ} (hDr : DrvReadable κ T P B X ϖ δ Dr)
    (hG : ModelGood κ T P B X ϖ P' X' δ) (R : ℕ) (C : ℝ) :
    PalmReadable (locG D3Plus.locFieldFull) κ T P B X ϖ P' X' δ R C (palmRd κ C R Dr) := by
  refine ⟨measurable_palmRd hDr.1, fun Γ _ => ⟨?_, ?_⟩⟩
  · filter_upwards [hDr.2, ae_good_true hS hX' hδ hG] with ω h1 h2
    filter_upwards [h1, h2] with x hx1 hx2 hA
    congr 1
    have hgood := (hx2 hA).addConst (C / Real.sqrt κ)
    have e : zcfg κ T B X ϖ C ω x = canonConfig (Real.sqrt κ)
        (addConst (addConst (Yf κ T (palmTau κ T B ω x) B X ω) (-(mReg κ T B X ϖ ω)))
          (C / Real.sqrt κ), (collided κ T B X ω x).2) := by
      rw [addConst_addConst_e5]; rfl
    rw [e]
    exact locG_canonConfig_addConst_eq hgood R (hx1 hA)
  · filter_upwards [hDr.2, hG] with ω h1 h2
    filter_upwards [h1, h2] with x hx1 hx2 hA
    filter_upwards [hx2 hA] with ω' h'
    congr 1
    exact locG_canonConfig_addConst_eq (h'.addConst _) R (hx1 hA)

end E5
end QuantumZipper
