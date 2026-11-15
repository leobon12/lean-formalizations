/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbFam
import InteractingSLE.Spec.Sec7.Lemma76RIdent
import InteractingSLE.Spec.Restart.FCDet

/-!
# `hline` for the retained continuation with the boundary stop

Packet PROVE-RETAUX79C (ruling R55). The per-line input `hline` of `RetAux79.hasSafeLaw_of_retLines` (K2's (S) for the
second continuation of Lemma 7.6), at every line `t`, almost surely on the live event before the lifetime:

* the later-line word `retWordAt … (r + t)` (the explicit measurable word of the later retained data) is sorted, and
  the chart transport of the line mean `g_t + 𝔥₀` in the later chart is its mean (`isRetMeanIdent_wordM`, for every
  capped versions and local-set mean `g_t` at the line);
* (III-a) and (III-b′) for the driver process `retDrv` at the clock `retClock t` (`exists_retLine_facts_R` through
  `retDriver`), with the force word split by its type (`FCDet.IsFlowType`: fixed counts and weights, positions
  `xL ω`, `xR ω`) and the geometric force coordinates `geomLW`, `geomRW`;
* at the trivial line `t = 0` (`Q = 0`) the identities are those of the stop line.

## Main results

* `forceBoundaryData_eq_of_cast`, `forceBoundaryData_geom_of_isFlowType`: reindexing the force data by a word type;
* **`ae_retLine_pos`**, **`ae_retLine_zero`**, **`ae_retLine`**: `hline`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMapInv logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE

namespace Restart.RetAux79

open Supp7 Sec7 Sec7.Lemma76G MartChar.RealFlow

/-! ### Reindexing the force data by a word type -/

/-- The force data are invariant under reindexing the marks by a cast of their index types. -/
theorem forceBoundaryData_eq_of_cast {κ : ℝ} {n m n' m' : ℕ} (eL : n = n') (eR : m = m') {ρL vL : Fin n' → ℝ}
    {ρR vR : Fin m' → ℝ} {ρL' vL' : Fin n → ℝ} {ρR' vR' : Fin m → ℝ} (hρL : ∀ i, ρL' i = ρL (Fin.cast eL i))
    (hρR : ∀ j, ρR' j = ρR (Fin.cast eR j)) (hvL : ∀ i, vL' i = vL (Fin.cast eL i))
    (hvR : ∀ j, vR' j = vR (Fin.cast eR j)) (x : ℝ) :
    forceBoundaryData κ ρL' ρR' vL' vR' x = forceBoundaryData κ ρL ρR vL vR x := by
  subst eL eR
  have h1 : ρL' = ρL := funext fun i => hρL i
  have h2 : ρR' = ρR := funext fun j => hρR j
  have h3 : vL' = vL := funext fun i => hvL i
  have h4 : vR' = vR := funext fun j => hvR j
  rw [h1, h2, h3, h4]

/-- **The force data of the flow-line word of a typed word, in the fixed type.** -/
theorem forceBoundaryData_geom_of_isFlowType {κ θ : ℝ} {B : BoundaryWord} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (ht : FCDet.IsFlowType κ θ B xL xR ρL ρR)
    (w : ℝ≥0 → ℝ) (Q : ℝ≥0) (y : ℝ) :
    forceBoundaryData κ ρL ρR (fun i => -rightImg (fun s : ℝ => -w s.toNNReal) (-xL i) Q - w Q)
        (fun j => rightImg (fun s : ℝ => w s.toNNReal) (xR j) Q - w Q) y =
      forceBoundaryData κ (flowLineRhoL κ B.fn B.jumps 0 θ) (flowLineRhoR κ B.fn B.jumps 0 θ)
        (fun i => -rightImg (fun s : ℝ => -w s.toNNReal) (-flowLineXL B.fn B.jumps 0 i) Q - w Q)
        (fun j => rightImg (fun s : ℝ => w s.toNNReal) (flowLineXR B.fn B.jumps 0 j) Q - w Q) y := by
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := ht
  refine (forceBoundaryData_eq_of_cast eL eR (fun i => (congrFun hρL i).symm) (fun j => (congrFun hρR j).symm)
    (fun i => ?_) (fun j => ?_) y).symm
  · rw [← congrFun hxL i]
  · rw [← congrFun hxR j]

/-- **The force data of a typed word at time `0`**: the flow-line data of the word. -/
theorem forceBoundaryData_zero_of_isFlowType {κ θ : ℝ} {B : BoundaryWord} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (ht : FCDet.IsFlowType κ θ B xL xR ρL ρR) (y : ℝ) :
    forceBoundaryData κ ρL ρR xL xR y =
      forceBoundaryData κ (flowLineRhoL κ B.fn B.jumps 0 θ) (flowLineRhoR κ B.fn B.jumps 0 θ)
        (flowLineXL B.fn B.jumps 0) (flowLineXR B.fn B.jumps 0) y := by
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := ht
  exact (forceBoundaryData_eq_of_cast eL eR (fun i => (congrFun hρL i).symm) (fun j => (congrFun hρR j).symm)
    (fun i => (congrFun hxL i).symm) (fun j => (congrFun hxR j).symm) y).symm

/-- The marks of a typed word have the flow-line signs: left marks `≤ 0`, right marks `≥ 0`. -/
theorem isFlowType_signs {κ θ : ℝ} {B : BoundaryWord} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (ht : FCDet.IsFlowType κ θ B xL xR ρL ρR) :
    (∀ i, xL i ≤ 0) ∧ ∀ j, 0 ≤ xR j := by
  obtain ⟨eL, eR, hxL, hxR, -, -⟩ := ht
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have h := congrFun hxL (Fin.cast eL.symm i)
    simp only [Fin.cast_cast, Fin.cast_eq_self] at h
    rw [h]
    rcases Supp8.flowLineXL_cases (b := B.fn) (J := B.jumps) 0 (Fin.cast eL.symm i) with h0 | ⟨z, -, hz, he⟩
    · rw [h0]
    · rw [he]; linarith
  · have h := congrFun hxR (Fin.cast eR.symm j)
    simp only [Fin.cast_cast, Fin.cast_eq_self] at h
    rw [h]
    rcases Supp8.flowLineXR_cases (b := B.fn) (J := B.jumps) 0 (Fin.cast eR.symm j) with h0 | ⟨z, -, hz, he⟩
    · rw [h0]
    · rw [he]; linarith

/-! ### The line objects -/

section Objects

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The word of the retained data at the line `(u, r')`** with the heights `∓λ − θ₂χ` on the second prefix and
`∓λ − θ₁χ` on the first. -/
def retWordAt (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (u : ℝ≥0) (κ θ₁ θ₂ : ℝ) (c₀ : BoundaryWord) (r' : ℝ≥0)
    (ω : Ω) : BoundaryWord :=
  wordM (retFam G η₁' η₂' u r') c₀ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ) (sleLambda κ - θ₂ * QuantumZipper.chiC κ)
    (-sleLambda κ - θ₁ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ) ω

/-- **The driver process** of the second continuation for the angles `θ₁`, `θ₂`. -/
def retDrv (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0) (κ θ₁ θ₂ : ℝ)
    (c₀ : BoundaryWord) : ℝ≥0 → Ω → ℝ :=
  retDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ₂ c₀ (-sleLambda κ - θ₁ * QuantumZipper.chiC κ)
    (sleLambda κ - θ₁ * QuantumZipper.chiC κ)

theorem continuous_retDrv (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0) (κ θ₁ θ₂ : ℝ)
    (c₀ : BoundaryWord) (ω : Ω) : Continuous fun t => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ t ω :=
  continuous_retDriver ω

theorem retDrv_zero (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0) (κ θ₁ θ₂ : ℝ)
    (c₀ : BoundaryWord) (ω : Ω) : retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ 0 ω = 0 :=
  retDriver_zero ω

end Objects

/-! ### `hline` -/

section Line

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {η₁' η₂' : Ω → ℝ≥0 → ℂ} {G : ℝ≥0 → Set Ω} {u r : ℝ≥0}
  {c₀ : BoundaryWord} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Ω → Fin nL → ℝ}
  {xR : Ω → Fin nR → ℝ} {F : Set Ω}

/-- **`hline` at a positive line** `t > 0`. -/
theorem ae_retLine_pos (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood)
    (hG : ∀ r' : ℝ≥0, ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r' : ℝ≥0∞) < ζ₂ ω → ω ∈ G r')
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps) (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y)
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r)
    (htype : ∀ ω ∈ F, FCDet.IsFlowType κ θ₂ (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ r ω) (xL ω) (xR ω) ρL ρR)
    {t : ℝ≥0} (ht : 0 < t) (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (g : Ω → DistOn upperHalfPlaneOpens)
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hm₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (hag₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime (Lemma76F.capR u (r + t)) (ζ₁ ω) s))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime (Lemma76F.capR u (r + t)) (ζ₂ ω) s))
    (hg : LocalSets.IsLocalSetMean (Lemma76F.cstUnion ηc₁ ηc₂ u (r + t)) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ F → (retClock G η₁' η₂' ζ₂ u r t ω : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω →
      (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ (r + t) ω).IsSorted ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        Chart.chartTransport ((hd (r + t)).isConformal_chart ω) 1 0 (QuantumZipper.chiC κ)
          (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ w, (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ (r + t) ω).mean w * φ w) ∧
      (∀ w ∈ H, ((retFam G η₁' η₂' u (r + t)).chart ω).2.1 w = ((retFam G η₁' η₂' u r).chart ω).2.1
        (fwdMapInv (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
          (retClock G η₁' η₂' ζ₂ u r t ω) w)) ∧
      (∀ w ∈ H, ((retFam G η₁' η₂' u (r + t)).chart ω).2.2 (((retFam G η₁' η₂' u (r + t)).chart ω).2.1 w) =
        (logDerivFwd (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
          (retClock G η₁' η₂' ζ₂ u r t ω)
          (fwdMapInv (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
            (retClock G η₁' η₂' ζ₂ u r t ω) w)).im +
          ((retFam G η₁' η₂' u r).chart ω).2.2 (((retFam G η₁' η₂' u r).chart ω).2.1
            (fwdMapInv (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
              (retClock G η₁' η₂' ζ₂ u r t ω) w))) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
        forceBoundaryData κ ρL ρR
          (fun i => PocketTraversal.geomLW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xL i
              (retClock G η₁' η₂' ζ₂ u r t ω) ω -
            retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ (retClock G η₁' η₂' ζ₂ u r t ω) ω)
          (fun j => PocketTraversal.geomRW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xR j
              (retClock G η₁' η₂' ζ₂ u r t ω) ω -
            retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ (retClock G η₁' η₂' ζ₂ u r t ω) ω) y =
          (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ (r + t) ω).fn y + θ₂ * QuantumZipper.chiC κ := by
  have hag_t : ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → ((r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω →
      ω ∈ (retFam G η₁' η₂' u (r + t)).G ∧
      (∀ s ≤ (retFam G η₁' η₂' u (r + t)).u, (retFam G η₁' η₂' u (r + t)).η₁ ω s = η₁ ω s) ∧
      ∀ s ≤ (retFam G η₁' η₂' u (r + t)).r, (retFam G η₁' η₂' u (r + t)).η₂ ω s = η₂ ω s := by
    filter_upwards [hG (r + t), ha₁, ha₂] with ω hGω e₁ e₂ hu hr
    exact ⟨hGω hu hr, fun s hs => e₁ s ((ENNReal.coe_le_coe.2 hs).trans hu.le),
      fun s hs => e₂ s ((ENNReal.coe_le_coe.2 hs).trans hr.le)⟩
  obtain ⟨hMI, hsort⟩ := Sec7.Lemma76G.isRetMeanIdent_wordM hL75 hκ hκ4 hb hx hh hη₁ hη₂ (hd (r + t)) hag_t hu₀
    hc₀ hc₀J hc₀b
  have hid := hMI ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
  filter_upwards [hid, hsort, hG (r + t), ha₁, ha₂, ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂] with ω hidω hsω hGt e₁ e₂ hp₁ hp₂ hωF hlt
  obtain ⟨hpair, hGr⟩ := hF ω hωF
  have hp₁' : IsPathGood (η₁' ω) (ζ₁ ω) x₁ := Supp7.IsPathGood.congr hp₁ e₁
  have hp₂' : IsPathGood (η₂' ω) (ζ₂ ω) x₂ := Supp7.IsPathGood.congr hp₂ e₂
  have hdrv := isRetDriver_retDriver (exists_isRetDriver hd hGr hp₁' hp₂' hx hpair hc₀ hκ θ₂
    (-sleLambda κ - θ₁ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ))
  obtain ⟨-, -, -, hfacts⟩ := hdrv
  have htL := lt_retLifeP_of_retClock_lt (hd r) hGr hp₂' hpair hlt
  have hrt : ((r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω := (coe_add_lt_iff.1 htL).trans_le contStop_le
  obtain ⟨hpair', hE', hinv, hlift, S, hS, hdat⟩ := hfacts t ht htL (hGt hpair.1 hrt)
  have hpairη : Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) (r + t) :=
    (Lemma76F.isDisjointPair_congr (fun s hs => e₁ s ((ENNReal.coe_le_coe.2 hs).trans hpair.1.le))
      (fun s hs => e₂ s ((ENNReal.coe_le_coe.2 hs).trans hrt.le)) Iff.rfl Iff.rfl).1 hpair'
  rw [retClock_eq (hd r) hGr hp₂' hpair t]
  refine ⟨hsω hpairη, hidω hpairη, hinv, hlift, S, hS, fun y hy => ?_⟩
  have h1 := forceBoundaryData_geom_of_isFlowType (htype ω hωF)
    (fun s => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s ω) (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω) t).toNNReal y
  exact h1.trans (hdat y hy)

/-- **The geometric force coordinates at time `0`** are the marks of a typed word. -/
theorem geom_zero_of_isFlowType {Ω' : Type*} {W : ℝ≥0 → Ω' → ℝ} (hWc : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {xL' : Ω' → Fin nL → ℝ} {xR' : Ω' → Fin nR → ℝ} {ω : Ω'} {B : BoundaryWord}
    (ht : FCDet.IsFlowType κ θ₂ B (xL' ω) (xR' ω) ρL ρR) :
    (fun i => PocketTraversal.geomLW W xL' i 0 ω - W 0 ω) = xL' ω ∧
      (fun j => PocketTraversal.geomRW W xR' j 0 ω - W 0 ω) = xR' ω := by
  obtain ⟨hsL, hsR⟩ := isFlowType_signs ht
  have hc : Continuous (Bessel.realPath W ω) := Bessel.continuous_realPath hWc ω
  have hcn : Continuous (Bessel.realPath (fun t ω => -W t ω) ω) :=
    Bessel.continuous_realPath (fun ω => (hWc ω).neg) ω
  have h0 : Bessel.realPath W ω 0 = 0 := by
    show W (0 : ℝ).toNNReal ω = 0
    rw [Real.toNNReal_zero, hW0]
  have h0n : Bessel.realPath (fun t ω => -W t ω) ω 0 = 0 := by
    show -W (0 : ℝ).toNNReal ω = 0
    rw [Real.toNNReal_zero, hW0, neg_zero]
  refine ⟨funext fun i => ?_, funext fun j => ?_⟩
  · show -rightImg (Bessel.realPath (fun t ω => -W t ω) ω) (-xL' ω i) ((0 : ℝ≥0) : ℝ) - W 0 ω = xL' ω i
    rw [NNReal.coe_zero, rightImg_zero hcn h0n (neg_nonneg.2 (hsL i)), hW0, neg_neg, sub_zero]
  · show rightImg (Bessel.realPath W ω) (xR' ω j) ((0 : ℝ≥0) : ℝ) - W 0 ω = xR' ω j
    rw [NNReal.coe_zero, rightImg_zero hc h0 (hsR j), hW0, sub_zero]

/-- **`hline` at the trivial line** `t = 0` (the stop line: `Q = 0`). -/
theorem ae_retLine_zero (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood)
    (hG : ∀ r' : ℝ≥0, ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r' : ℝ≥0∞) < ζ₂ ω → ω ∈ G r')
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps) (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y)
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r)
    (htype : ∀ ω ∈ F, FCDet.IsFlowType κ θ₂ (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ r ω) (xL ω) (xR ω) ρL ρR)
    (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (g : Ω → DistOn upperHalfPlaneOpens)
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hm₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (hag₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime (Lemma76F.capR u (r + 0)) (ζ₁ ω) s))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime (Lemma76F.capR u (r + 0)) (ζ₂ ω) s))
    (hg : LocalSets.IsLocalSetMean (Lemma76F.cstUnion ηc₁ ηc₂ u (r + 0)) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ F → (retClock G η₁' η₂' ζ₂ u r 0 ω : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω →
      (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ (r + 0) ω).IsSorted ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        Chart.chartTransport ((hd (r + 0)).isConformal_chart ω) 1 0 (QuantumZipper.chiC κ)
          (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ w, (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ (r + 0) ω).mean w * φ w) ∧
      (∀ w ∈ H, ((retFam G η₁' η₂' u (r + 0)).chart ω).2.1 w = ((retFam G η₁' η₂' u r).chart ω).2.1
        (fwdMapInv (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
          (retClock G η₁' η₂' ζ₂ u r 0 ω) w)) ∧
      (∀ w ∈ H, ((retFam G η₁' η₂' u (r + 0)).chart ω).2.2 (((retFam G η₁' η₂' u (r + 0)).chart ω).2.1 w) =
        (logDerivFwd (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
          (retClock G η₁' η₂' ζ₂ u r 0 ω)
          (fwdMapInv (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
            (retClock G η₁' η₂' ζ₂ u r 0 ω) w)).im +
          ((retFam G η₁' η₂' u r).chart ω).2.2 (((retFam G η₁' η₂' u r).chart ω).2.1
            (fwdMapInv (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
              (retClock G η₁' η₂' ζ₂ u r 0 ω) w))) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
        forceBoundaryData κ ρL ρR
          (fun i => PocketTraversal.geomLW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xL i
              (retClock G η₁' η₂' ζ₂ u r 0 ω) ω -
            retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ (retClock G η₁' η₂' ζ₂ u r 0 ω) ω)
          (fun j => PocketTraversal.geomRW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xR j
              (retClock G η₁' η₂' ζ₂ u r 0 ω) ω -
            retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ (retClock G η₁' η₂' ζ₂ u r 0 ω) ω) y =
          (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ (r + 0) ω).fn y + θ₂ * QuantumZipper.chiC κ := by
  have hag_t : ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → ((r + 0 : ℝ≥0) : ℝ≥0∞) < ζ₂ ω →
      ω ∈ (retFam G η₁' η₂' u (r + 0)).G ∧
      (∀ s ≤ (retFam G η₁' η₂' u (r + 0)).u, (retFam G η₁' η₂' u (r + 0)).η₁ ω s = η₁ ω s) ∧
      ∀ s ≤ (retFam G η₁' η₂' u (r + 0)).r, (retFam G η₁' η₂' u (r + 0)).η₂ ω s = η₂ ω s := by
    filter_upwards [hG (r + 0), ha₁, ha₂] with ω hGω e₁ e₂ hu hr
    exact ⟨hGω hu hr, fun s hs => e₁ s ((ENNReal.coe_le_coe.2 hs).trans hu.le),
      fun s hs => e₂ s ((ENNReal.coe_le_coe.2 hs).trans hr.le)⟩
  obtain ⟨hMI, hsort⟩ := Sec7.Lemma76G.isRetMeanIdent_wordM hL75 hκ hκ4 hb hx hh hη₁ hη₂ (hd (r + 0)) hag_t hu₀
    hc₀ hc₀J hc₀b
  have hid := hMI ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
  filter_upwards [hid, hsort, ha₁, ha₂] with ω hidω hsω e₁ e₂ hωF _
  obtain ⟨hpair, -⟩ := hF ω hωF
  have hpairη : Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) (r + 0) := by
    rw [add_zero]
    exact (Lemma76F.isDisjointPair_congr (fun s hs => e₁ s ((ENNReal.coe_le_coe.2 hs).trans hpair.1.le))
      (fun s hs => e₂ s ((ENNReal.coe_le_coe.2 hs).trans hpair.2.1.le)) Iff.rfl Iff.rfl).1 hpair
  set W := retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ with hWdef
  have hWc : Continuous fun s : ℝ => W s.toNNReal ω :=
    (continuous_retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ ω).comp continuous_real_toNNReal
  have hW0 : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by
    show W (0 : ℝ).toNNReal ω = 0
    rw [Real.toNNReal_zero]; exact retDrv_zero G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ ω
  have hfam : retFam G η₁' η₂' u (r + 0) = retFam G η₁' η₂' u r := by rw [add_zero]
  have hword : retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ (r + 0) ω = retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ r ω := by
    rw [add_zero]
  rw [retClock_zero, NNReal.coe_zero]
  refine ⟨hsω hpairη, hidω hpairη, fun w hw => ?_, fun w hw => ?_, ?_⟩
  · rw [fwdMapInv_zero_time hWc hW0 hw, hfam]
  · rw [fwdMapInv_zero_time hWc hW0 hw, hfam,
      show logDerivFwd (fun s : ℝ => W s.toNNReal ω) 0 w = 0 by simp [QuantumZipper.logDerivFwd],
      Complex.zero_im, zero_add]
  · obtain ⟨hgL, hgR⟩ := geom_zero_of_isFlowType (continuous_retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
      (retDrv_zero G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) (htype ω hωF)
    set B := retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ r ω with hB
    refine ⟨{0} ∪ (B.jumps : Set ℝ), (finite_singleton 0).union B.jumps.finite_toSet, fun y hy => ?_⟩
    have hy0 : y ≠ 0 := fun h => hy (Or.inl h)
    have hyJ : y + 0 ∉ B.jumps := by
      rw [add_zero]; exact fun h => hy (Or.inr h)
    rw [hgL, hgR, hword, forceBoundaryData_zero_of_isFlowType (htype ω hωF) y,
      Exist.forceBoundaryData_flowLine_seed hκ (BoundaryWord.isPiecewiseConstantBoundaryData B) 0 θ₂ hy0 hyJ,
      add_zero]

end Line

end Restart.RetAux79

end InteractingSLE
