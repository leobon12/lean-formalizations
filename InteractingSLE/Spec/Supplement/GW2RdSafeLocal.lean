/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdSafeData
import InteractingSLE.Spec.Supplement.RelSafeS6

/-!
# GW2's relative safe law (K2's (S), (L)), part 4: the line kernels from the marked union locality

Packet PROVE-GW2-RELDET. GB6's `Supp8.RelSafeS.hasGB6LineData_of_local` with the curves exchanged: the line kernels of
GW2's line data follow from the history-marked locality of the physical union alone (`RelSafeS.ae_condExp_cexp_marked`,
generic). What remains of GW2's line data is:

* **`HasGW2LineLocal`**: the marked locality of the physical union `B_t` for the centred ORIGINAL field `h − u₀`
  (with `ℍ ∖ B_t` the inverse relative chart image of `ℍ ∖ K̃_{a(t)}` on the live event), the **union mean
  identification** (the transport of every local-set mean of `B_t`, plus `u₀`, through the relative chart of the
  counterflow record is the canonical relative mean at `a(t)`), and the physicality of the safe events;
* `hasGW2LineData_of_local`: `HasGW2LineLocal ⇒ HasGW2LineData`;
* **`GW2RdLineLocalStatement`**, `gw2RdLineDataStatement_of_local`, **`gw2RdSafeStatement_of_lineLocal_thr`**,
  **`gw2JointDetC2Statement_of_thm12_thm13_lineLocal_thr`**.

Conditional helpers with distinct names.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.RelSafe Supp8.RelSafeS Restart
  Restart.DomainMarkov.K2 Restart.FCDet Sec7.PocketTraversal GW2TipSystem GW2JointKernel LocalSets

section Local

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **GW2's marked union locality, union mean identification and safe events at the physical lines.** -/
def HasGW2LineLocal (κ θ : ℝ) (c' : BoundaryWord) (P : Measure Ω) (h Hc : Ω → DistOn upperHalfPlaneOpens)
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (s : ℝ≥0)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (hrec : Measurable (gb6Rec s W ζ))
    (hWm : ∀ r, Measurable (regW s Wα ζα r)) (w : WordType) : Prop :=
  ∃ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
    InnerProductSpace.HarmonicOnNhd u₀ H ∧
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P ∧
    (∀ t, physFilt hrec hWm P t ≤ ℋ t) ∧ (∀ t, ℋ t ≤ mΩ) ∧
    (∀ t, Measurable[mΩ, hittingSigma] (B t)) ∧ (∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω)) ∧
    (∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (B t) (WholeField.centredField h u₀) P) ∧
    (∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ liveEvGW2 κ θ c' s W ζ w → gw2LineClock s Wα ζα W ζ GT V t ω < V ω →
      H \ B t ω = (relChart (gb6Rec s W ζ ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal)) ∧
    (∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (B t) (WholeField.centredField h u₀) P g →
      ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ liveEvGW2 κ θ c' s W ζ w →
        gw2LineClock s Wα ζα W ζ GT V t ω < V ω →
        Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal ω)
          (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal) →
        Chart.chartTransport (isConformal_relChart (gb6Rec s W ζ ω)) 1 (specOffset κ + θ * chiC κ) (chiC κ)
            (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
          ∫ z, couplingMean κ (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal
            (DomainMarkov.bheProc κ (typedRhoL w) (typedRhoR w) R
              (fun i t ω => geomLW canonDrv (typedLGW2 κ θ c' w) i t
                (gb6Rec s W ζ ω, relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω))
              (fun j t ω => geomRW canonDrv (typedRGW2 κ θ c' w) j t
                (gb6Rec s W ζ ω, relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω)) ω
              (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal) z * ψ z) ∧
    (∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[physFilt hrec hWm P t]
      {ω | gw2LineClock s Wα ζα W ζ GT V t ω < V ω ∧ Disjoint (tsupport ψ)
        (fwdHull (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal)}) ∧
    ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[physFilt hrec hWm P t]
      {ω | gw2LineClock s Wα ζα W ζ GT V t ω < V ω ∧ Disjoint (Coupling.ballsK Fb)
        (fwdHull (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal)}

/-- **`HasGW2LineLocal ⇒ HasGW2LineData`** (GB6's `hasGB6LineData_of_local`, verbatim with the curves exchanged). -/
theorem hasGW2LineData_of_local {κ θ : ℝ} {c' : BoundaryWord} {P : Measure Ω} [IsProbabilityMeasure P]
    {h Hc : Ω → DistOn upperHalfPlaneOpens} {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {GT : Set Ω} {s : ℝ≥0}
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {hrec : Measurable (gb6Rec s W ζ)}
    {hWm : ∀ r, Measurable (regW s Wα ζα r)} {w : WordType}
    (hL : HasGW2LineLocal κ θ c' P h Hc W ζ Wα ζα GT s R V hrec hWm w) :
    HasGW2LineData κ θ c' P h Hc W ζ Wα ζα GT s R V hrec hWm w := by
  obtain ⟨u₀, ℋ, B, hu₀, hh0, h𝓖ℋ, hℋ, hBm, hBc, hloc, hBK, hmean, hSψ, hSb⟩ := hL
  set h₀ := WholeField.centredField h u₀ with hh₀def
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
    fun t ψ => hmean t (g t) (hgm t) ψ, hu₀, hh0, h𝓖ℋ, hℋ, hBm, hBc, hloc, hBK, hSψ, hSb⟩
  intro t φ
  have h1 := ae_condExp_cexp_marked hh0 (hBm t) (hBc t) (hℋ t) (hloc t) (hgm t) φ
  have hsplit : (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) =
      fun ω => Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (h₀ ω φ : ℂ)) := by
    funext ω
    rw [← Complex.exp_add, hh₀def, WholeField.centredField_apply h hu₀ ω φ]
    congr 1
    push_cast
    ring
  have hcs : (fun ω => Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (h₀ ω φ : ℂ))) =
      Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) • fun ω => Complex.exp (Complex.I * (h₀ ω φ : ℂ)) :=
    rfl
  have h2 : P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | germSigma (B t) h₀ ⊔ ℋ t] =ᵐ[P]
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

end Local

/-! ### The named input in the local form -/

/-- **Named input: GW2's marked union locality, union mean identification and safe events** (binders of
`GW2RdLineDataStatement`). -/
def GW2RdLineLocalStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω)) →
    ∀ (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ),
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    ∀ (hfl : IsFlowLineDriver κ b J θ P h Wα ζα),
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0 (flowLineXL b J 0)
      (flowLineXR b J 0) →
    ∀ (s : ℝ≥0) (Hc : Ω → DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 (specOffset κ) (chiC κ) (h ω) (Hc ω)) →
    ∀ c' : BoundaryWord, c'.jumps = J' → (∀ y ∉ J', c'.fn y = b' y) →
    ∀ GT : Set Ω, (∀ ω ∈ GT, PhysGood s (regW s Wα ζα) W ζ (extTr s Wα ζα α) γ ω) → MeasurableSet GT →
      (∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s W ζ ω ∈ gb6TS s) →
    ∀ (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞), IsGW2RelVersion s P W Wα ζ ζα γ α R V →
    ∀ w : WordType,
      HasGW2LineLocal κ θ c' P h Hc W ζ Wα ζα GT s R V (measurable_recOf_cfE hcf s).2 (measurable_regW hfl s) w

theorem gw2RdLineDataStatement_of_local (hL : GW2RdLineLocalStatement.{u}) : GW2RdLineDataStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hTr hcf hadmL hadmR hcomp hfl hα hseed
    s Hc hHcm hHc c' hcJ hcb GT hGT hGTm hGTae R V hver w
  exact hasGW2LineData_of_local (hL κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hTr hcf
    hadmL hadmR hcomp hfl hα hseed s Hc hHcm hHc c' hcJ hcb GT hGT hGTm hGTae R V hver w)

/-- **`GW2RdSafeStatement` from GW2's marked union locality and union mean identification and the threshold
clause.** -/
theorem gw2RdSafeStatement_of_lineLocal_thr (hL : GW2RdLineLocalStatement.{u}) (hT : GW2RdThrStatement.{u}) :
    GW2RdSafeStatement.{u} :=
  gw2RdSafeStatement_of_lineData_thr (gw2RdLineDataStatement_of_local hL) hT

/-- **GW2's root determination from Theorems 1.2–1.3, GW2's marked union locality and union mean identification, and
the threshold clause.** -/
theorem gw2JointDetC2Statement_of_thm12_thm13_lineLocal_thr (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (hL : GW2RdLineLocalStatement.{u})
    (hT : GW2RdThrStatement.{u}) : GW2JointKernel.GW2JointDetC2Statement.{u} :=
  gw2JointDetC2Statement_of_thm12_thm13_safe h12p₀ h13₀ h13 (gw2RdSafeStatement_of_lineLocal_thr hL hT)

end InteractingSLE.Theorem14.GW2Rd
