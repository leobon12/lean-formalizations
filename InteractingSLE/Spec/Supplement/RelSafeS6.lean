/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RelSafeS5
import InteractingSLE.Spec.Sec6.Prop61BMarked

/-!
# GB6's relative safe law, part 6: the line kernels from the marked union locality

Packet PROVE-GB6-RELSAFE2. The line kernels of K2's lines step (Aux. 77 at the physical lines, `hker` of
`HasGB6LineData`) follow from the history-marked locality of the physical union alone: if `B_t` is a relatively
closed hitting-measurable random set, marked local for the centred counterflow-frame field `h′ − u₀` with marks
`ℋ_t ⊇ 𝓖_t`, then given `𝒢L_t = 𝒜(B_t) ∨ ℋ_t` the field `h′(φ)` has the Gaussian characteristic function with mean
`g_t(φ) + ∫ u₀ φ` (`g_t` a local-set mean of `B_t`: the marks do not change the conditional mean,
`Sec6.IsLocalSetMean.ae_eq_condExp_germSigma`) and the zero-boundary variance of `ℍ ∖ B_t` (Aux. lemma 18's germ
law with marks, `WholeField.exists_condExp_germSigma_history`). So the remaining content of the line data is:

* **`HasGB6LineLocal`**: the marked locality of the physical union `B_t` (with `ℍ ∖ B_t` the inverse relative chart
  image of `ℍ ∖ K̃_{a(t)}` on the live event) and the **union mean identification**: the transport of every local-set
  mean of `B_t` (plus `u₀`) through the relative chart is the canonical relative mean at `a(t)` (Aux. 79);
* **`hasGB6LineData_of_local`**: `HasGB6LineLocal ⇒ HasGB6LineData`;
* **`GB6LineLocalStatement`**, **`gb6RelSafeRStatement_of_lineLocal`**: the named input in this form, and
  `GB6RelSafeRStatement` from it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Supp8.RelSafeS

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.RelSafe Restart Restart.DomainMarkov.K2
  Restart.FCDet Sec7.PocketTraversal Sec7.StripSysField LocalSets

section Local

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **GB6's marked union locality and union mean identification at the physical lines.** -/
def HasGB6LineLocal (κ θ : ℝ) (c : BoundaryWord) (P : Measure Ω) (h' Hc : Ω → DistOn upperHalfPlaneOpens)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (s : ℝ≥0) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    (hrec : Measurable (gb6Rec s Wα ζα)) (hWm : ∀ r, Measurable (W r)) (w : WordType) : Prop :=
  ∃ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
    InnerProductSpace.HarmonicOnNhd u₀ H ∧
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀) P ∧
    (∀ t, physFilt hrec hWm P t ≤ ℋ t) ∧ (∀ t, ℋ t ≤ mΩ) ∧
    (∀ t, Measurable[mΩ, hittingSigma] (B t)) ∧ (∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω)) ∧
    (∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (B t) (WholeField.centredField h' u₀) P) ∧
    (∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ liveEv κ θ c s Wα ζα w → min (physClock s W Wα ζα GT t ω) (V ω) < V ω →
      H \ B t ω = (relChart (gb6Rec s Wα ζα ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal)) ∧
    ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (B t) (WholeField.centredField h' u₀) P g →
      ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ liveEv κ θ c s Wα ζα w →
        min (physClock s W Wα ζα GT t ω) (V ω) < V ω →
        Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal ω)
          (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) →
        Chart.chartTransport (isConformal_relChart (gb6Rec s Wα ζα ω)) 1 (2 * Real.pi * chiC (16 / κ))
            (chiC (16 / κ)) (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
          ∫ z, couplingMean (16 / κ) (fun r : ℝ => R r.toNNReal ω)
            (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal
            (DomainMarkov.bheProc (16 / κ) (typedRhoL w) (typedRhoR w) R
              (fun i t ω => geomLW canonDrv (typedL κ θ c w) i t (gb6Rec s Wα ζα ω, relVar Hc R V ω))
              (fun j t ω => geomRW canonDrv (typedR κ θ c w) j t (gb6Rec s Wα ζα ω, relVar Hc R V ω)) ω
              (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) z * ψ z

end Local

section Kernel

variable {Ω : Type u} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- **The line kernel from the marked locality.** For a zero-boundary GFF `h₀`, a relatively closed hitting-measurable
random set `B` marked local for `h₀` with marks `ℋ`, and a local-set mean `g` of `B`: given `𝒜(B) ∨ ℋ`, every test
pairing of `h₀` has the conditional characteristic function `e^{i g(φ)} e^{−σ²_{ℍ∖B}(φ)/2}`. -/
theorem ae_condExp_cexp_marked {P : Measure Ω} [IsProbabilityMeasure P] {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {B : Ω → Set ℂ}
    (hBm : Measurable[mΩ, hittingSigma] B) (hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hℋ : ℋ ≤ mΩ) (hloc : WholeField.IsHistoryAvoidanceLocal ℋ B h₀ P) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean B h₀ P g) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, P[fun ω' => Complex.exp (Complex.I * (h₀ ω' φ : ℂ)) | germSigma B h₀ ⊔ ℋ] ω =
      Complex.exp (Complex.I * (g ω φ : ℂ)) *
        ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ B ω) φ φ) : ℝ) : ℂ) := by
  have hhm := hh.measurable
  have hBc' : ∀ᵐ ω ∂P, B ω ⊆ H ∧ IsOpen (H \ B ω) := Eventually.of_forall hBc
  have hle := germSigma_le hBm hhm
  have hl : IsLocalSet B h₀ P := ((isLocalSet_tfae hh hBm hBc').out 4 1).2 hloc.isAvoidanceLocal
  obtain ⟨M, hMm, hM1, hM2⟩ := WholeField.exists_condExp_germSigma_history hh hBm hℋ hloc hBc' φ
  have hMi : Integrable M P := integrable_condExp.congr hM1.symm
  have hMg : M =ᵐ[P] fun ω => g ω φ := by
    have e1 : P[P[fun ω => h₀ ω φ | germSigma B h₀ ⊔ ℋ] | germSigma B h₀] =ᵐ[P]
        P[fun ω => h₀ ω φ | germSigma B h₀] := condExp_condExp_of_le le_sup_left (sup_le hle hℋ)
    have e2 : P[P[fun ω => h₀ ω φ | germSigma B h₀ ⊔ ℋ] | germSigma B h₀] =ᵐ[P]
        P[M | germSigma B h₀] := condExp_congr_ae hM1.symm
    rw [condExp_of_stronglyMeasurable hle hMm.stronglyMeasurable hMi] at e2
    exact e2.symm.trans (e1.trans (Sec6.IsLocalSetMean.ae_eq_condExp_germSigma hh hBm hl hg φ).symm)
  filter_upwards [hM2, hMg] with ω hω hωM
  rw [← hω, hωM, relClosureH_eq (hBc ω).1 (hBc ω).2]

end Kernel

section Data

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **`HasGB6LineLocal ⇒ HasGB6LineData`.** -/
theorem hasGB6LineData_of_local {κ θ : ℝ} {c : BoundaryWord} {P : Measure Ω} [IsProbabilityMeasure P]
    {h' Hc : Ω → DistOn upperHalfPlaneOpens} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {GT : Set Ω} {s : ℝ≥0}
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {hrec : Measurable (gb6Rec s Wα ζα)} {hWm : ∀ r, Measurable (W r)}
    {w : WordType} (hL : HasGB6LineLocal κ θ c P h' Hc W Wα ζα GT s R V hrec hWm w) :
    HasGB6LineData κ θ c P h' Hc W Wα ζα GT s R V hrec hWm w := by
  obtain ⟨u₀, ℋ, B, hu₀, hh0, h𝓖ℋ, hℋ, hBm, hBc, hloc, hBK, hmean⟩ := hL
  set h₀ := WholeField.centredField h' u₀ with hh₀def
  have hhm := hh0.measurable
  have hl : ∀ t, IsLocalSet (B t) h₀ P := fun t =>
    ((isLocalSet_tfae hh0 (hBm t) (Eventually.of_forall (hBc t))).out 4 1).2 (hloc t).isAvoidanceLocal
  have hg : ∀ t, ∃ g, IsLocalSetMean (B t) h₀ P g := fun t => IsLocalSet.exists_isLocalSetMean hh0 (hBm t) (hl t)
  choose g hgm using hg
  have hu₀c : ContinuousOn u₀ (upperHalfPlaneOpens : Set ℂ) := fun z hz =>
    (hu₀ z hz).1.continuousAt.continuousWithinAt
  refine ⟨fun t => germSigma (B t) h₀ ⊔ ℋ t,
    fun t ω => g t ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀, u₀, ℋ, B,
    fun t => (h𝓖ℋ t).trans le_sup_right, fun t => sup_le (germSigma_le (hBm t) hhm) (hℋ t), ?_,
    fun t ψ => hmean t (g t) (hgm t) ψ, hu₀, hh0, h𝓖ℋ, hℋ, hBm, hBc, hloc, hBK⟩
  intro t φ
  have h1 := ae_condExp_cexp_marked hh0 (hBm t) (hBc t) (hℋ t) (hloc t) (hgm t) φ
  -- the field is the centred field plus the constant pairing of `u₀`
  have hsplit : (fun ω => Complex.exp (Complex.I * (h' ω φ : ℂ))) =
      fun ω => Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (h₀ ω φ : ℂ)) := by
    funext ω
    rw [← Complex.exp_add, hh₀def, WholeField.centredField_apply h' hu₀ ω φ]
    congr 1
    push_cast
    ring
  have hcs : (fun ω => Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (h₀ ω φ : ℂ))) =
      Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) • fun ω => Complex.exp (Complex.I * (h₀ ω φ : ℂ)) :=
    rfl
  have h2 : P[fun ω => Complex.exp (Complex.I * (h' ω φ : ℂ)) | germSigma (B t) h₀ ⊔ ℋ t] =ᵐ[P]
      Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) •
        P[fun ω => Complex.exp (Complex.I * (h₀ ω φ : ℂ)) | germSigma (B t) h₀ ⊔ ℋ t] := by
    rw [hsplit, hcs]
    exact condExp_smul _ _ _
  filter_upwards [h2, h1, hBK t] with ω hω2 hω hBKω hωF hlt _
  rw [hω2, Pi.smul_apply, hω, ← hBKω hωF hlt, smul_eq_mul, add_apply,
    SupercriticalConformalCovariance.GM24.smoothDist_apply hu₀c φ, Complex.ofReal_exp]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have e : (∫ x, φ x * u₀ x) = ∫ z, u₀ z * φ z := by
    congr 1
    funext z
    ring
  rw [e]
  push_cast
  ring

/-! ### The named input in the local form -/

/-- **Named input: GB6's marked union locality and union mean identification** (binders of `GB6LineDataStatement`):
`HasGB6LineLocal` and `HasGB6SafeMeas`. -/
def GB6LineLocalStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    ∀ (hfl : IsFlowLineDriver κ b J θ P h Wα ζα),
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ (s : ℝ≥0) (Hc : Ω → DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (Hc ω)) →
    ∀ c : BoundaryWord, c.jumps = J → (∀ y ∉ J, c.fn y = b y) →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (hW'm : ∀ r, Measurable (W' r)), (∀ᵐ ω ∂P, ∀ t, W' t ω = W t ω) →
    ∀ GT : Set Ω, (∀ ω ∈ GT, PhysGood s W' Wα ζα γ α ω) → MeasurableSet GT →
      (∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s Wα ζα ω ∈ gb6TS s) →
    ∀ (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞), HullId.IsGB6RelVersionR s P W' Wα ζα γ α R V →
    ∀ w : WordType,
      HasGB6LineLocal κ θ c P h' Hc W' Wα ζα GT s R V (measurable_recOf_cfE hfl s).2 hW'm w ∧
        HasGB6SafeMeas P W' Wα ζα GT s R V (measurable_recOf_cfE hfl s).2 hW'm

theorem gb6LineDataStatement_of_lineLocal (hL : GB6LineLocalStatement.{u}) : GB6LineDataStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s Hc
    hHcm hHc c hcJ hcb W' hW'm hWW GT hGT hGTm hGTae R V hver w
  obtain ⟨hD, hS⟩ := hL κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR
    hcomp hfl hα s Hc hHcm hHc c hcJ hcb W' hW'm hWW GT hGT hGTm hGTae R V hver w
  exact ⟨hasGB6LineData_of_local hD, hS⟩

/-- **`GB6RelSafeRStatement` from GB6's marked union locality and union mean identification.** -/
theorem gb6RelSafeRStatement_of_lineLocal (hL : GB6LineLocalStatement.{u}) : GB6RelSafeRStatement.{u} :=
  gb6RelSafeRStatement_of_lineData (gb6LineDataStatement_of_lineLocal hL)

/-- **Theorem 1.4's `GB6HullDetStatement` from GB6's marked union locality and union mean identification**
(`Q3Stop.gb6HullDetStatement_of_relSafeR`). -/
theorem gb6HullDetStatement_of_lineLocal (hL : GB6LineLocalStatement.{u}) : Supp8.GB6.GB6HullDetStatement.{u} :=
  gb6HullDetStatement_of_relSafeR (gb6RelSafeRStatement_of_lineLocal hL)

end Data

end InteractingSLE.Supp8.RelSafeS
