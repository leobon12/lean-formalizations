import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.FiniteLocalTransferV2




 







set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents
open LQGMetric (DistC TestC)

 

def SetGeodesic (d : LSCMetric) (K₁ K₂ : Set ℂ)
    (P : ℝ → ℂ) (T : ℝ) : Prop :=
  EndSaving.Interfaces.BumpedGeodesic d P T ∧ P 0 ∈ K₁ ∧ P T ∈ K₂ ∧
    ENNReal.ofReal T = OptimalConstants.Ratios.setDist d K₁ K₂

 

theorem SetGeodesic.isGeodesic (d : LSCMetric) (K₁ K₂ : Set ℂ)
    (P : ℝ → ℂ) (T : ℝ) (hg : SetGeodesic d K₁ K₂ P T) :
    LQGMetric.MetricGeometry.IsGeodesicCurve (d.pt ∘ P) 0 T := by
  rcases hg.1 with ⟨hcurve, _, hlen, _⟩
  exact ⟨hcurve.1, hcurve.2, hlen⟩

 

def UniqueSetGeodesic (d : LSCMetric) (K₁ K₂ : Set ℂ)
    (P : ℝ → ℂ) (T : ℝ) : Prop :=
  SetGeodesic d K₁ K₂ P T ∧
    ∀ (P' : ℝ → ℂ) (T' : ℝ), SetGeodesic d K₁ K₂ P' T' →
      T' = T ∧ Set.EqOn P' P (Set.Icc 0 T)

 
def bumpSumV2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) : TestC :=
  ∑ i ∈ Z, (obj i).f

 
def subtractBumpsV2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (g : DistC) : DistC :=
  LQGMetric.GM.subTest g (bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z)

 

def LocalSizeBin (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (r b q : Set.Ioi (0 : ℝ)) (hrz hbr : ℝ) : Prop :=
  (q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr) ≤
    (r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hrz) ∧
  (r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hrz) ≤
    2 * (q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr)

 

def FbarV2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (g : DistC) : Prop :=
  Z.Nonempty ∧ EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧
  ∃ hbr : ℝ, IsCircleAverage g b 0 hbr ∧
    OptimalConstants.Ratios.setDist (D' g) K₁ K₂ ≥
      cPlus * OptimalConstants.Ratios.setDist (D g) K₁ K₂ -
        ENNReal.ofReal ((q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * hbr)) ∧
    (∀ i ∈ Z,
      g ∈ (obj i).E ∧
        ∃ hrz : ℝ, IsCircleAverage g r
          (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) hrz ∧
          LocalSizeBin ξ Q r b q hrz hbr) ∧
    ∃ P : ℝ → ℂ, ∃ T : ℝ,
      UniqueSetGeodesic (D g) K₁ K₂ P T ∧
        ∀ i ∈ Z, ∃ t ∈ Set.Icc 0 T,
          P t ∈ Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r

 

def StableAtV2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (g : DistC) (P : ℝ → ℂ) (T : ℝ) (i : ℤ × ℤ) : Prop :=
  let z := LQGMetric.GM.gridPt ((r : ℝ) / 100) i
  let W := Metric.ball z (4 * (r : ℝ))
  ∃ hrz : ℝ, IsCircleAverage g r z hrz ∧
    ∃ τ' τ σ σ' : ℝ,
      EndSaving.Interfaces.Excursion P T W (obj i).V τ' τ σ σ' ∧
      ∃ (hτ : P τ ∈ W) (hσ : P σ ∈ W),
        ENNReal.ofReal par.Ctime *
          ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) *
            Real.exp ((ξ : ℝ) * hrz)) ≤
          (D g).internal W (⟨P τ, hτ⟩, ⟨P σ, hσ⟩)

 

def FV2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (g : DistC) : Prop :=
  FbarV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z g ∧
    ∃ P : ℝ → ℂ, ∃ T : ℝ,
      UniqueSetGeodesic
        (D (subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z g))
        K₁ K₂ P T ∧
      ∀ i ∈ Z, StableAtV2 μ h D D' ξ Q cMid par pbar r obj g P T i

 

def ShiftedFV2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) : Set Ω :=
  {ω | FV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z
    (LQGMetric.addFun (h ω)
      (LQGMetric.testCont (bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z)))}

 

def GoodSiteV2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (i : ℤ × ℤ) (g : DistC) : Prop :=
  let z := LQGMetric.GM.gridPt ((r : ℝ) / 100) i
  let W := Metric.ball z (4 * (r : ℝ))
  let gplus := LQGMetric.addFun g (LQGMetric.testCont (obj i).f)
  gplus ∈ (obj i).E ∧
    ∃ hbr hrz : ℝ, IsCircleAverage g b 0 hbr ∧
      IsCircleAverage g r z hrz ∧
      LocalSizeBin ξ Q r b q hrz hbr ∧
      ∃ P : ℝ → ℂ, ∃ T : ℝ,
        UniqueSetGeodesic (D g) K₁ K₂ P T ∧
        ∃ τ' τ σ σ' : ℝ,
          EndSaving.Interfaces.Excursion P T W (obj i).V τ' τ σ σ' ∧
          ∃ (hτ : P τ ∈ W) (hσ : P σ ∈ W),
            ENNReal.ofReal par.Ctime *
              ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) *
                Real.exp ((ξ : ℝ) * hrz)) ≤
              (D gplus).internal W (⟨P τ, hτ⟩, ⟨P σ, hσ⟩)

 
theorem fV2_implies_fbarV2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (g : DistC)
    (hF : FV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z g) :
    FbarV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z g := hF.1

 

theorem fbarV2_mono {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z Z' : Finset (ℤ × ℤ)) (g : DistC)
    (hsub : Z' ⊆ Z) (hne : Z'.Nonempty)
    (hFbar : FbarV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z g) :
    FbarV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z' g := by
  rcases hFbar with ⟨_, hconfig, hbr, havg, hbad, hlocal, P, T, hgeod, hhit⟩
  refine ⟨hne, ?_, hbr, havg, hbad, ?_, P, T, hgeod, ?_⟩
  · rcases hconfig with ⟨hpair, hobst⟩
    constructor
    · intro i hi j hj hij
      exact hpair i (hsub hi) j (hsub hj) hij
    · intro i hi
      exact hobst i (hsub hi)
  · intro i hi
    exact hlocal i (hsub hi)
  · intro i hi
    exact hhit i (hsub hi)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents
