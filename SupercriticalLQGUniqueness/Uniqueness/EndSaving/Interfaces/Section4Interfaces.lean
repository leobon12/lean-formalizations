import SupercriticalLQGUniqueness.Uniqueness.Assembly.Collision.HMain
import LQGMetric.Blueprint.M2Defs
import LQGMetric.Field.CameronMartin
import LQGMetric.Papers.GM.S3.GoodAnnulus
import Mathlib




 





set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces
open LQGMetric (DistC TestC)

 
structure AdmissibleRadii where
  radii : Set ℝ
  subset_unit : radii ⊆ Set.Ioo 0 1
  separated : ∀ ⦃r s : ℝ⦄, r ∈ radii → s ∈ radii → r < s → 8 * r ≤ s

 
structure Parameters (ξ : Set.Ioi (0 : ℝ)) where
  Cmax : ℝ
  Cacross : ℝ
  Caround : ℝ
  Crn : ℝ
  Ctime : ℝ
  Cinc : ℝ
  Ctube : ℝ
  max_pos : 0 < Cmax
  across_pos : 0 < Cacross
  around_pos : 0 < Caround
  rn_pos : 0 < Crn
  time_pos : 0 < Ctime
  inc_pos : 0 < Cinc
  tube_pos : 0 < Ctube
  around_gt_across : Cacross < Caround
  strict_slack : (2 * Caround / Cacross) * Ctime <
    Cacross - 4 * Real.exp (-(ξ : ℝ) * Cmax) * Ctube

 
def dyadicRadius (j : ℕ) : Set.Ioi (0 : ℝ) :=
  ⟨(8 : ℝ) ^ (-(j : ℤ)), zpow_pos (show (0 : ℝ) < 8 by norm_num) _⟩

 
def midpoint (cMinus cPlus : ℝ≥0∞) : ℝ :=
  (cMinus.toReal + cPlus.toReal) / 2

 
def IsOpenAnnularTube (z : ℂ) (r : Set.Ioi (0 : ℝ))
    (U : TopologicalSpace.Opens ℂ) : Prop :=
  (U : Set ℂ) ⊆ {x : ℂ | r < dist x z ∧ dist x z < 3 * (r : ℝ)} ∧
  Nonempty (U ≃ₜ {x : ℂ // 1 < dist x 0 ∧ dist x 0 < 2}) ∧
  LQGMetric.Disconnects (U : Set ℂ) (Metric.sphere z r)
    (Metric.sphere z (3 * (r : ℝ)))

 
def Excursion (P : ℝ → ℂ) (T : ℝ) (O : Set ℂ)
    (V : TopologicalSpace.Opens ℂ) (τ' τ σ σ' : ℝ) : Prop :=
  0 ≤ τ' ∧ τ' ≤ τ ∧ τ ≤ σ ∧ σ ≤ σ' ∧ σ' ≤ T ∧
  P τ' ∈ frontier O ∧ P σ' ∈ frontier O ∧
  (∀ t ∈ Set.Ioo τ' σ', P t ∈ O) ∧
  P τ ∈ closure (V : Set ℂ) ∧ P σ ∈ closure (V : Set ℂ) ∧
  (∀ t ∈ Set.Ioo τ' τ, P t ∉ closure (V : Set ℂ)) ∧
  (∀ t ∈ Set.Ioo σ σ', P t ∉ closure (V : Set ℂ))

 
def BumpedGeodesic (D : LSCMetric) (P : ℝ → ℂ) (T : ℝ) : Prop :=
  D.IsCurve P 0 T ∧ HasUnitSpeedOn (D.pt ∘ P) (Set.Icc 0 T) ∧
  D.len P 0 T = D (P 0, P T) ∧ D (P 0, P T) < ⊤

 
def HasTubeSeparator (D : LSCMetric) (z : ℂ) (r : Set.Ioi (0 : ℝ))
    (U : TopologicalSpace.Opens ℂ) (bound : ℝ≥0∞) : Prop :=
  ∃ (pi : ℝ → ℂ) (a b : ℝ), D.IsCurve pi a b ∧
    (∀ t ∈ Set.Icc a b, pi t ∈ (U : Set ℂ)) ∧
    LQGMetric.Disconnects (pi '' Set.Icc a b) (Metric.sphere z r)
      (Metric.sphere z (3 * (r : ℝ))) ∧ D.len pi a b ≤ bound

 
structure ObjectAt {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (par : Parameters ξ)
    (pbar : Set.Ioo (0 : ℝ) 1) (z : ℂ) (r : Set.Ioi (0 : ℝ)) where
  U : TopologicalSpace.Opens ℂ
  V : TopologicalSpace.Opens ℂ
  f : TestC
  E : Set Ω
  U_annular : IsOpenAnnularTube z r U
  V_annular : IsOpenAnnularTube z r V
  closure_U_V : closure (U : Set ℂ) ⊆ (V : Set ℂ)
  closure_V_annulus : closure (V : Set ℂ) ⊆
    {x : ℂ | r < dist x z ∧ dist x z < 3 * (r : ℝ)}
  f_nonneg : ∀ x : ℂ, 0 ≤ f x
  f_le : ∀ x : ℂ, f x ≤ par.Cmax
  f_on_U : ∀ x ∈ (U : Set ℂ), f x = par.Cmax
  f_off_V : ∀ x ∉ (V : Set ℂ), f x = 0
  E_measurable : MeasurableSet E
  E_local : ∃ E₀ : Set Ω,
    @MeasurableSet Ω (LQGMetric.Blueprint.fieldSigmaClosed0 h
      {x : ℂ | r ≤ dist x z ∧ dist x z ≤ 4 * (r : ℝ)}) E₀ ∧
    E =ᵐ[P] E₀
  E_probability : ENNReal.ofReal (pbar : ℝ) ≤ P E
  E_circle : ∀ ω ∈ E, ∃ c : ℝ, IsCircleAverage (h ω) r z c
  E_bounds : ∀ ω ∈ E, ∀ c : ℝ, IsCircleAverage (h ω) r z c →
    let N : ℝ≥0∞ := ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c))
    OptimalConstants.Ratios.setDist (D (h ω)) (V : Set ℂ)
      (Metric.sphere z r ∪ Metric.sphere z (3 * (r : ℝ))) ≥
        ENNReal.ofReal par.Cacross * N ∧
    (∃ A : EuclideanAnnulus,
      A.center = z ∧ A.innerRadius = 3 * (r : ℝ) ∧
      A.outerRadius = 4 * (r : ℝ) ∧
      aroundDist (D (h ω)) A ≤ ENNReal.ofReal par.Caround * N) ∧
    HasTubeSeparator (D (h ω)) z r U (ENNReal.ofReal par.Ctube * N)
  E_rn : ∀ ω ∈ E,
    par.Crn⁻¹ ≤ LQGMetric.cmDensity f (LQGMetric.pair0 (h ω)) ∧
      LQGMetric.cmDensity f (LQGMetric.pair0 (h ω)) ≤ par.Crn
  E_shortcut : ∀ ω ∈ E, ∀ c : ℝ, IsCircleAverage (h ω) r z c →
    let d := D (LQGMetric.addFun (h ω) (-(LQGMetric.testCont f)))
    let e := D' (LQGMetric.addFun (h ω) (-(LQGMetric.testCont f)))
    let W := Metric.ball z (4 * (r : ℝ))
    let N := ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c))
    ∀ (P' : ℝ → ℂ) (T τ' τ σ σ' : ℝ),
      BumpedGeodesic d P' T → P' 0 ∉ W → P' T ∉ W →
      Excursion P' T W V τ' τ σ σ' →
      ∃ (hτ : P' τ ∈ W) (hσ : P' σ ∈ W),
        ENNReal.ofReal par.Ctime * N ≤
          (D (h ω)).internal W (⟨P' τ, hτ⟩, ⟨P' σ, hσ⟩) →
        ∃ s t : ℝ, τ ≤ s ∧ s < t ∧ t ≤ σ ∧
          ENNReal.ofReal par.Cinc * N ≤ ENNReal.ofReal (t - s) ∧
          ∃ (hs : P' s ∈ W) (ht : P' t ∈ W),
            e.internal W (⟨P' s, hs⟩, ⟨P' t, ht⟩) ≤
              ENNReal.ofReal (cMid * (t - s))

 
structure ObjectsExist {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (cMinus cPlus : ℝ≥0∞) (pbar : Set.Ioo (0 : ℝ) 1) where
  cMid' : ℝ
  cMid'_lower : cMinus.toReal < cMid'
  cMid'_upper : cMid' < midpoint cMinus cPlus
  radii : AdmissibleRadii
  params : Parameters ξ
  family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ radii.radii →
    ObjectAt P h D D' ξ Q (midpoint cMinus cPlus) params pbar z r
  density : ∀ κ : Set.Ioi (0 : ℝ), ∃ ε₀ : Set.Ioo (0 : ℝ) 1,
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ j : ℕ,
      let b : Set.Ioi (0 : ℝ) := dyadicRadius j
      ENNReal.ofReal (κ : ℝ) ≤
        P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) b κ
          ⟨cMid', lt_of_le_of_lt ENNReal.toReal_nonneg cMid'_lower⟩} →
      ∃ F : Finset ℝ,
        (F : Set ℝ) = radii.radii ∩ Set.Icc (ε ^ 2 * (b : ℝ)) (ε * (b : ℝ)) ∧
        (5 / 8 : ℝ) * (Real.log ε⁻¹ / Real.log 8) ≤ F.card

 
def euclidSetDist (A B : Set ℂ) : ℝ≥0∞ :=
  ⨅ x ∈ A, ⨅ y ∈ B, ENNReal.ofReal (dist x y)

 
def Configuration (r b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (Z : Finset (ℤ × ℤ)) : Prop :=
  (∀ i ∈ Z, ∀ j ∈ Z, i ≠ j →
    Disjoint (Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ)))
      (Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) j) (4 * (r : ℝ)))) ∧
  (∀ i ∈ Z, Disjoint
    (Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ)))
    (K₁ ∪ K₂ ∪ Metric.sphere (0 : ℂ) b))

 
def IsDyadicSize (q : ℝ) : Prop := ∃ j : ℤ, q = (2 : ℝ) ^ j

 
def SizeWindow (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (ε b r : Set.Ioi (0 : ℝ))
    (hbr hrz : ℝ) : Prop :=
  ε ^ (2 * (ξ : ℝ) * (Q + 3)) * b ^ ((ξ : ℝ) * Q) *
      Real.exp ((ξ : ℝ) * hbr) ≤
    r ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hrz) ∧
  r ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hrz) ≤
    ε ^ ((ξ : ℝ) * min (Q - 3) (2 * (Q - 3))) *
      b ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr)

 
def CountingBadEvent {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (cPlus : ℝ≥0∞) (R : AdmissibleRadii)
    (event : ∀ _z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii → Set Ω)
    (b ε : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ) : Set Ω :=
  {ω | ∃ hbr : ℝ, IsCircleAverage (h ω) b 0 hbr ∧
    OptimalConstants.Ratios.setDist (D' (h ω)) K₁ K₂ ≥
      cPlus * OptimalConstants.Ratios.setDist (D (h ω)) K₁ K₂ -
        ENNReal.ofReal ((1 / 2 : ℝ) * ε ^ (2 * (ξ : ℝ) * (Q + 3)) *
          (b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr)) ∧
    (∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      ε ^ 2 * (b : ℝ) ≤ (r : ℝ) → (r : ℝ) ≤ ε * (b : ℝ) →
      ∀ z ∈ Metric.ball (0 : ℂ) (3 * (b : ℝ)),
        ∃ hrz : ℝ, IsCircleAverage (h ω) r z hrz ∧
          SizeWindow ξ Q ε b r hbr hrz) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) (3 * (b : ℝ)),
      ∃ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii) (i : ℤ × ℤ),
        ε ^ 2 * (b : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) ≤ ε * (b : ℝ) ∧
        LQGMetric.GM.gridPt ((r : ℝ) / 100) i ∈
          Metric.ball z ((r : ℝ) / 25) ∧
        ω ∈ event (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr)}

 
def ClosedEndSaving {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (cPlus : ℝ≥0∞) (b ν δ κ : Set.Ioi (0 : ℝ)) : Set Ω :=
  {ω | ∃ hbr : ℝ, IsCircleAverage (h ω) b 0 hbr ∧
    ∀ i j : ℤ × ℤ,
      let s := (δ : ℝ) ^ (ν : ℝ) * (b : ℝ)
      let z := LQGMetric.GM.gridPt (s / 100) i
      let w := LQGMetric.GM.gridPt (s / 100) j
      z ∈ Metric.ball (0 : ℂ) b → w ∈ Metric.ball (0 : ℂ) b →
      κ * (b : ℝ) ≤ dist z w →
      κ * (b : ℝ) ≤ Metric.infDist z (Metric.sphere (0 : ℂ) b) →
      OptimalConstants.Ratios.setDist (D' (h ω)) (Metric.closedBall z s) (Metric.closedBall w s) +
        ENNReal.ofReal (δ * (b : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * hbr)) <
        cPlus * OptimalConstants.Ratios.setDist (D (h ω))
          (Metric.closedBall z s) (Metric.closedBall w s)}

 
def upperGood {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (D D' : DistC → LSCMetric) (ξ Q : ℝ)
    (a : Set.Ioo (3 / 4 : ℝ) 1) (θ C : Set.Ioi (0 : ℝ))
    (p : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc n (2 * n)).filter fun j =>
    ENNReal.ofReal p ≤ P {ω | OptimalConstants.Ratios.HEvent D D' ξ Q (dyadicRadius j) a C θ (h ω)}

 
def lowerGood {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (κ C : Set.Ioi (0 : ℝ)) (n : ℕ) : Finset ℕ :=
  (Finset.Icc n (2 * n)).filter fun j =>
    ENNReal.ofReal (κ : ℝ) ≤
      P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) (dyadicRadius j) κ C}

 


section CountingStatement
variable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
  (h : Ω → DistC) (D D' : DistC → LSCMetric)
  (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (cMinus cPlus : ℝ≥0∞)
  (pbar : Set.Ioo (0 : ℝ) 1) (R : AdmissibleRadii)
  (params : Parameters ξ)
  (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
    ObjectAt P h D D' ξ Q (midpoint cMinus cPlus) params pbar z r)

variable (hCounting : cMinus < cPlus →
  ∀ (μ : Set.Ioi (0 : ℝ)) (η : Set.Ioo (0 : ℝ) 1),
  ∃ C : Set.Ioi (0 : ℝ), ∃ ε₀ : Set.Ioo (0 : ℝ) 1,
  ∀ ε : ℝ, (hε : 0 < ε) → ε ≤ ε₀ → ∀ b : Set.Ioi (0 : ℝ),
  ∀ K₁ K₂ : Set ℂ,
    K₁.Nonempty → K₂.Nonempty → IsCompact K₁ → IsCompact K₂ →
    Disjoint K₁ K₂ →
    K₁ ⊆ Metric.ball (0 : ℂ) (2 * (b : ℝ)) →
    K₂ ⊆ Metric.ball (0 : ℂ) (2 * (b : ℝ)) →
    ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤ euclidSetDist K₁ K₂ →
    ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤ euclidSetDist K₁ (Metric.sphere (0 : ℂ) b) →
    P (CountingBadEvent h D D' ξ Q cPlus R
      (fun z r hr => (family z r hr).E) b ⟨ε, hε⟩ K₁ K₂) ≤
        ENNReal.ofReal ((C : ℝ) * ε ^ (μ : ℝ)))
#check hCounting
end CountingStatement

section EndUnionStatement
variable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
  (h : Ω → DistC) (D D' : DistC → LSCMetric)
  (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (cMinus cPlus : ℝ≥0∞)
  (pbar : Set.Ioo (0 : ℝ) 1) (objs : ObjectsExist P h D D' ξ Q cMinus cPlus pbar)

variable (hEndUnion : ∀ (ν κG κEnd : Set.Ioi (0 : ℝ))
  (η : Set.Ioo (0 : ℝ) 1),
  ∃ δ₀ : Set.Ioo (0 : ℝ) 1,
    ∀ δ : ℝ, (hδ : 0 < δ) → δ ≤ δ₀ → ∀ j : ℕ,
      let b := dyadicRadius j
      ENNReal.ofReal (κG : ℝ) ≤
        P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) b κG
          ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩} →
      ENNReal.ofReal (1 - (η : ℝ)) ≤
        P (ClosedEndSaving h D D' ξ Q cPlus b ν ⟨δ, hδ⟩ κEnd))
#check hEndUnion
end EndUnionStatement

 

section R53Statement
variable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
  (h : Ω → DistC) (D D' : DistC → LSCMetric)
  (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (cMinus cPlus : ℝ≥0∞)
  (pbar : Set.Ioo (0 : ℝ) 1) (objs : ObjectsExist P h D D' ξ Q cMinus cPlus pbar)
  (θ : Set.Ioi (0 : ℝ))
variable (hR53 : ∀ (a : Set.Ioo (3 / 4 : ℝ) 1)
  (κ : Set.Ioi (0 : ℝ))
  (p : Set.Ioo (0 : ℝ) 1),
    ∃ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
      ∀ j : ℕ,
        ENNReal.ofReal (κ : ℝ) ≤
          P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω))
            (dyadicRadius j) κ
              ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩} →
        P {ω | OptimalConstants.Ratios.HEvent D D' ξ Q (dyadicRadius j) a
          ⟨Ctop, Ctop.property.1⟩ θ (h ω)} <
            ENNReal.ofReal ((p : ℝ) / 2))
#check hR53
end R53Statement

private theorem ratioPair_of_upperOptimal_pos (d e : LSCMetric)
    (hp : 0 < OptimalConstants.Ratios.upperOptimal d e) :
    ∃ z w : ℂ, OptimalConstants.Ratios.RatioPair d z w := by
  by_contra hn
  have hz : OptimalConstants.Ratios.upperOptimal d e = 0 := by
    apply le_antisymm
    · unfold OptimalConstants.Ratios.upperOptimal
      refine iSup_le fun z => iSup_le fun w => iSup_le fun hpair => ?_
      exact False.elim (hn ⟨z, w, hpair⟩)
    · exact bot_le
  exact hp.ne' hz

 

theorem hMAIN_fixed_of_sections {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (cMinus cPlus : ℝ≥0∞) (hPlusPos : 0 < cPlus)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (θ : Set.Ioi (0 : ℝ))
    (hS36upper : ∃ a : Set.Ioo (3 / 4 : ℝ) 1,
      ∃ p : Set.Ioo (0 : ℝ) 1,
        ∀ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
          ∃ n₁ : ℕ, ∀ n ≥ n₁,
            3 * n ≤ 4 * (upperGood P h D D' ξ Q a θ
              ⟨Ctop, Ctop.property.1⟩ p n).card)
    (hS36lower : ∀ Cmid : {x : ℝ // cMinus.toReal < x},
      ∃ κ : Set.Ioi (0 : ℝ), ∃ n₂ : ℕ, ∀ n ≥ n₂,
        3 * n ≤ 4 * (lowerGood P h D D' κ
          ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩ n).card)
    (hT58 : ∀ pbar : Set.Ioo (0 : ℝ) 1, cMinus < cPlus →
      ObjectsExist P h D D' ξ Q cMinus cPlus pbar)
    (hR53 : ∀ (pbar : Set.Ioo (0 : ℝ) 1)
      (objs : ObjectsExist P h D D' ξ Q cMinus cPlus pbar)
      (a : Set.Ioo (3 / 4 : ℝ) 1) (κ : Set.Ioi (0 : ℝ))
      (p : Set.Ioo (0 : ℝ) 1),
        ∃ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
          ∀ j : ℕ,
            ENNReal.ofReal (κ : ℝ) ≤
              P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω))
                (dyadicRadius j) κ
                  ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩} →
            P {ω | OptimalConstants.Ratios.HEvent D D' ξ Q (dyadicRadius j) a
              ⟨Ctop, Ctop.property.1⟩ θ (h ω)} <
                ENNReal.ofReal ((p : ℝ) / 2)) :
    cMinus = cPlus := by
  have hCommon : ∀ᵐ ω ∂P,
      OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus ∧
      OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus := hMinus.and hPlus
  obtain ⟨ω, hωMinus, hωPlus⟩ := hCommon.exists
  have hUpperPos : 0 < OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) := by
    rw [hωPlus]
    exact hPlusPos
  obtain ⟨z, w, hpair⟩ := ratioPair_of_upperOptimal_pos _ _ hUpperPos
  have hle : cMinus ≤ cPlus := by
    calc
      cMinus = OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) := hωMinus.symm
      _ ≤ OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) :=
        OptimalConstants.Ratios.lowerOptimal_le_upperOptimal ⟨z, w, hpair⟩
      _ = cPlus := hωPlus
  rcases lt_or_eq_of_le hle with hstrict | heq
  · let pbar : Set.Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩
    let objs := hT58 pbar hstrict
    obtain ⟨a, p, hUpper⟩ := hS36upper
    obtain ⟨κ, n₂, hLower⟩ := hS36lower ⟨objs.cMid', objs.cMid'_lower⟩
    obtain ⟨Ctop, hCompare⟩ := hR53 pbar objs a κ p
    obtain ⟨n₁, hUpperN⟩ := hUpper Ctop
    let n := max (max n₁ n₂) 5
    have hn : 4 < n := by dsimp [n]; omega
    have hn₁ : n₁ ≤ n := by dsimp [n]; omega
    have hn₂ : n₂ ≤ n := by dsimp [n]; omega
    have hcollision := Assembly.Collision.dyadic_collision hn
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (hUpperN n hn₁) (hLower n hn₂)
    obtain ⟨j, hj⟩ := hcollision
    have hU : ENNReal.ofReal (p : ℝ) ≤
        P {ω | OptimalConstants.Ratios.HEvent D D' ξ Q (dyadicRadius j) a
          ⟨Ctop, Ctop.property.1⟩ θ (h ω)} :=
      (Finset.mem_filter.mp (Finset.mem_inter.mp hj).1).2
    have hG : ENNReal.ofReal (κ : ℝ) ≤
        P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω))
          (dyadicRadius j) κ
            ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩} :=
      (Finset.mem_filter.mp (Finset.mem_inter.mp hj).2).2
    have hpHalf : ENNReal.ofReal ((p : ℝ) / 2) < ENNReal.ofReal (p : ℝ) := by
      exact (ENNReal.ofReal_lt_ofReal_iff p.property.1).2
        (by have hp := p.property.1; linarith)
    exact False.elim (not_lt_of_ge hU (lt_trans (hCompare j hG) hpHalf))
  · exact heq

 



theorem hMAIN_of_sections
    (hDET : ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∃ cMinus cPlus : ℝ≥0∞,
        0 < cMinus ∧ cMinus < ⊤ ∧ 0 < cPlus ∧ cPlus < ⊤ ∧
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) ∧
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus))
    (θFixed : ∀ (_ξ : Set.Ioi (0 : ℝ)) (_Q : ℝ)
      (_D : DistC → LSCMetric), Set.Ioi (0 : ℝ))
    (hS36upper : ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cPlus : ℝ≥0∞, 0 < cPlus → cPlus < ⊤ →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        ∃ a : Set.Ioo (3 / 4 : ℝ) 1,
          ∃ p : Set.Ioo (0 : ℝ) 1,
            ∀ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
              ∃ n₁ : ℕ, ∀ n ≥ n₁,
                3 * n ≤ 4 * (upperGood P h D D' ξ Q a (θFixed ξ Q D)
                  ⟨Ctop, Ctop.property.1⟩ p n).card)
    (hS36lower : ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cMinus : ℝ≥0∞, 0 < cMinus → cMinus < ⊤ →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        ∀ Cmid : {x : ℝ // cMinus.toReal < x},
          ∃ κ : Set.Ioi (0 : ℝ), ∃ n₂ : ℕ, ∀ n ≥ n₂,
            3 * n ≤ 4 * (lowerGood P h D D' κ
              ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩ n).card)
    (hT58 : ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cMinus cPlus : ℝ≥0∞,
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        cMinus < cPlus → ∀ pbar : Set.Ioo (0 : ℝ) 1,
          ObjectsExist P h D D' ξ Q cMinus cPlus pbar)
    (hR53 : ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ (cMinus cPlus : ℝ≥0∞) (pbar : Set.Ioo (0 : ℝ) 1)
        (objs : ObjectsExist P h D D' ξ Q cMinus cPlus pbar)
        (a : Set.Ioo (3 / 4 : ℝ) 1)
        (κ : Set.Ioi (0 : ℝ)) (p : Set.Ioo (0 : ℝ) 1),
          ∃ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
            ∀ j : ℕ,
              ENNReal.ofReal (κ : ℝ) ≤
                P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω))
                  (dyadicRadius j) κ
                    ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩} →
              P {ω | OptimalConstants.Ratios.HEvent D D' ξ Q (dyadicRadius j) a
                ⟨Ctop, Ctop.property.1⟩ (θFixed ξ Q D) (h ω)} <
                  ENNReal.ofReal ((p : ℝ) / 2)) :
    ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cMinus cPlus : ℝ≥0∞,
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        cMinus = cPlus := by
  intro ξ Q hQ D D' hD hD' Ω _ P _ h hGFF cMinus cPlus hMinus hPlus
  obtain ⟨m, M, hmPos, hmFin, hMPos, hMFin, hm, hM⟩ :=
    hDET ξ Q hQ D D' hD hD' P h hGFF
  let θ := θFixed ξ Q D
  obtain ⟨a, p, hUpper⟩ :=
    hS36upper ξ Q hQ D D' hD hD' P h hGFF M hMPos hMFin hM
  have hLower := hS36lower ξ Q hQ D D' hD hD' P h hGFF m hmPos hmFin hm
  have hObjects : ∀ pbar : Set.Ioo (0 : ℝ) 1, m < M →
      ObjectsExist P h D D' ξ Q m M pbar := by
    intro pbar hstrict
    exact hT58 ξ Q hQ D D' hD hD' P h hGFF m M hm hM hstrict pbar
  have hCompare : ∀ (pbar : Set.Ioo (0 : ℝ) 1)
      (objs : ObjectsExist P h D D' ξ Q m M pbar)
      (a : Set.Ioo (3 / 4 : ℝ) 1) (κ : Set.Ioi (0 : ℝ))
      (p : Set.Ioo (0 : ℝ) 1),
        ∃ Ctop : Set.Ioo (0 : ℝ) M.toReal,
          ∀ j : ℕ,
            ENNReal.ofReal (κ : ℝ) ≤
              P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω))
                (dyadicRadius j) κ
                  ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩} →
            P {ω | OptimalConstants.Ratios.HEvent D D' ξ Q (dyadicRadius j) a
              ⟨Ctop, Ctop.property.1⟩ θ (h ω)} <
                ENNReal.ofReal ((p : ℝ) / 2) := by
    intro pbar objs a κ p
    exact hR53 ξ Q hQ D D' hD hD' P h hGFF m M pbar objs a κ p
  have hmEqM := hMAIN_fixed_of_sections P h D D' ξ Q m M hMPos hm hM θ
    ⟨a, p, hUpper⟩ hLower hObjects hCompare
  have hcMinus : cMinus = m := by
    obtain ⟨ω, hω, hω'⟩ := (hMinus.and hm).exists
    exact hω.symm.trans hω'
  have hcPlus : cPlus = M := by
    obtain ⟨ω, hω, hω'⟩ := (hPlus.and hM).exists
    exact hω.symm.trans hω'
  exact hcMinus.trans (hmEqM.trans hcPlus.symm)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces
