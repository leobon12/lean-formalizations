/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JtRule
import InteractingSLE.Spec.Supplement.SB2JtTail
import InteractingSLE.Spec.Supplement.SB2JtT

/-!
# SB2(2): the v3 concrete rule's statement and the corrected target from it (D6 option A, D7; ruling R120)

Packet PROVE-SB2-LIFTSET (round 16).

* `StageRelFinP`, `StageRelInfP`, **`StageRelP`**: the relative facts of a stage for a general point map;
* `cΦ3_of_ne`: away from stage `0` the v3 curve is the unshifted one;
* **`liftRel_of_stage3`**: at an unshifted stage every actual-piece fact is proved (tip set in `D` as the image of the
  good times, tail position, compact/closed tail times, density of the tail's `D`-times, lifted endpoint); left: the
  good-time density (`hgd`, from the tail form of S3 almost surely) and the relative facts;
* `Stage0Facts`, **`liftRel_of_stage0`**: the shifted start piece (decision D6): its tip set in `D` as the image of its
  good times after `t_R`, their density, the lifted endpoint, the tail's `D`-time density, and the relative facts;
* `StagesGeom3`, **`piecesLift2_of_geom3`**; `ClauseT` (the corrected target's clause), `GeomAt3`,
  **`ConcreteSplitV3At`**, **`SB2LowerConcreteSplitV3Statement`** (named input, the v3 concrete rule);
* **`sb2LowerRelDriverStatementT_of_splitV3`** (Theorems 1.2–1.3, the tail form of S3, `exists_EL_concrete3`),
  `sb2LowerLaunchLiftStatement_of_splitV3`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C
open LuM GW1W GW1Bookkeep GW1P
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-! ### The relative facts for a general point map -/

/-- The relative facts at a finite piece (point map `p` on `[0, L]`). -/
def StageRelFinP (c : Chart) (m : ℝ) (p : ℝ≥0 → ℂ) (L : ℝ≥0∞) (s₂ : ExplState) (e₂ : Drv) : Prop :=
  e₂.2 ≠ ⊤ ∧ ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2} ∧
  (∃ (α : ℝ≥0 → ℂ) (f : ℂ → ℂ), (∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurvep c m p L s₂) τ) ∧
    α 0 = 0 ∧ ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2} ∧
    (∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → Tendsto (stChart s₂).2.1 (𝓝[H] (α τ)) (𝓝 (f (α τ)))) ∧
    ContinuousOn (fun τ => f (α τ)) {τ | (τ : ℝ≥0∞) ≤ e₂.2}) ∧
  ContinuousOn (stChart s₂).2.1 H ∧ (∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w) ∧
  ∀ t ∈ goodTp c p L, liftPt c m (p t) ∈ (stChart s₂).2.1 '' H

/-- The relative facts at an infinite piece. -/
def StageRelInfP (c : Chart) (m : ℝ) (p : ℝ≥0 → ℂ) (L : ℝ≥0∞) (s₂ : ExplState) (e₂ : Drv) : Prop :=
  ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2} ∧
  (∃ (α : ℝ≥0 → ℂ) (f : ℂ → ℂ), (∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurvep c m p L s₂) τ) ∧
    α 0 = 0 ∧ ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2} ∧
    (∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → Tendsto (stChart s₂).2.1 (𝓝[H] (α τ)) (𝓝 (f (α τ)))) ∧
    ContinuousOn (fun τ => f (α τ)) {τ | (τ : ℝ≥0∞) ≤ e₂.2} ∧
    IsClosed ((fun τ => f (α τ)) '' {τ : ℝ≥0 | (τ : ℝ≥0∞) ≤ e₂.2})) ∧
  ContinuousOn (stChart s₂).2.1 H ∧ (∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w) ∧
  ∀ t ∈ goodTp c p L, liftPt c m (p t) ∈ (stChart s₂).2.1 '' H

/-- **The relative facts of a stage** (finite or infinite piece). -/
def StageRelP (c : Chart) (m : ℝ) (p : ℝ≥0 → ℂ) (L : ℝ≥0∞) (s₂ : ExplState) (e₂ : Drv) : Prop :=
  (L ≠ ⊤ → StageRelFinP c m p L s₂ e₂) ∧ (L = ⊤ → StageRelInfP c m p L s₂ e₂)

/-- Away from stage `0` the v3 curve is the unshifted one. -/
theorem cΦ3_of_ne {Ω : Type*} (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (R : ℝ) (c : Chart) (m : ℝ)
    (D₁ : Ω → ℕ → Drv) {j : ℕ} (hj : j ≠ 0) (ω : Ω) (s₂ : ExplState) :
    cΦ3 κ θ b₁ J₁ R c m D₁ j ω s₂ = stCurvep c m
      (pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) (D₁ ω) (j + relOff κ θ b₁ J₁ R (D₁ ω)))
        (D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω))))
      (D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω))).2 s₂ := by
  unfold cΦ3
  rw [stageShift_of_ne κ θ b₁ J₁ R D₁ hj ω]
  simp only [zero_add, ENNReal.coe_zero, tsub_zero]

/-! ### The lift relation at a stage -/

section Lift

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv} {n : ℕ} {c : Chart} {R m : ℝ} {A : Set ℂ}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {s₂ : ExplState} {e₂ : Drv}

/-- **The lift relation at an unshifted stage**: every actual-piece fact is proved; the good-time density and the
relative facts are the inputs. -/
theorem liftRel_of_stage3 (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcc : c.IsConformal) (hU : UpperChartOK c)
    (hDom : c.2.1 '' H = H \ fillH A) (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hβ : IsProperCurve β₀)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < (D n).2} ⊆
      closure (goodT c (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)))
    (hF : StageRelP c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) (D n).2 s₂ e₂)
    (hρ : IsDrivenCurve (stCurvep c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
      (D n).2 s₂))
    (he₂ : e₂.2 = capLife (stCurvep c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
      (D n).2 s₂))
    (hgen : ∀ T < capLife (stCurvep c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
        (D n).2 s₂),
      IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m
        (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) (D n).2 s₂)))
    (hW0 : e₂.1 0 = 0) :
    LiftRel β₀ tL γ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
      (newPc s₂ e₂) := by
  obtain ⟨hcH, hc1, hoff⟩ := hU
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  have htipD : (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).1.tipSet
      (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.1
      (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.2 ∩ c.2.1 '' H =
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) ''
        goodTp c (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) (D n).2 := by
    rw [htip]
    ext z
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hD⟩
      exact ⟨t, ⟨ht, hD⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hD⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, hD⟩
  have htail := tail_of_launch hl hβr hK hDom
  have hd₁ := hdense_tail_of_good hP hl hpos hβ htail hgd
  by_cases he₁ : (D n).2 = ⊤
  · obtain ⟨hW, ⟨α, f, hαeq, hα0, hαc, hc, hgc, hcl⟩, hcH₂, hc1₂, hdom⟩ := hF.2 he₁
    exact liftRel_concrete_top2P hγ hcH hc1 hoff (isClosed_tail_times hβ.1 tL (isClosed_tipSet_launch hP hl)) hd₁
      htipD htail he₁ hρ he₂ hgen hW hW0 hαeq hα0 hαc hc hgc hcl hcH₂ hc1₂ hdom hgd
  · obtain ⟨hfin₂, hW, ⟨α, f, hαeq, hα0, hαc, hc, hgc⟩, hcH₂, hc1₂, hdom⟩ := hF.1 he₁
    exact liftRel_concrete_drivenP hγ hcH hc1 hoff (isCompact_tail_times_launch hP hl he₁ hβ tL) hd₁ htipD htail
      he₁ hpos hρ he₂ hgen hfin₂ hW hW0 hαeq hα0 hαc hc hgc hcH₂ hc1₂ hdom hgd (hend_of_launch hcc m hP hl hpos)

/-- **The facts of the shifted start piece** (decision D6): point map `p` on `[0, L]` (`p = pcPt (t_R + ·)`), its
good times' image is the start piece's part in `D`, they are dense before `L`, the lifted endpoint, the density of
the tail's `D`-times, and the relative facts. -/
def Stage0Facts (c : Chart) (m : ℝ) (β₀ : ℝ≥0 → ℂ) (tL : ℝ≥0) (s₁ : ExplState) (e₁ : Drv) (p : ℝ≥0 → ℂ)
    (L : ℝ≥0∞) (s₂ : ExplState) (e₂ : Drv) : Prop :=
  (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H = p '' goodTp c p L ∧
  {t : ℝ≥0 | (t : ℝ≥0∞) < L} ⊆ closure (goodTp c p L) ∧ L ≠ 0 ∧
  (∀ t ∈ goodTp c p L, (t : ℝ≥0∞) = L → liftPt c m (p t) ∈
    closure ((fun t' => liftPt c m (p t')) '' (goodTp c p L ∩ {t' | (t' : ℝ≥0∞) < L}))) ∧
  {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2} ⊆
    closure {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H} ∧
  StageRelP c m p L s₂ e₂

/-- **The lift relation at the shifted start piece.** -/
theorem liftRel_of_stage0 (hγ : IsTailLiftCurve c R m β₀ tL γ) (hU : UpperChartOK c)
    (hDom : c.2.1 '' H = H \ fillH A) (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hβ : IsProperCurve β₀)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} (hLfin : L ≠ ⊤ → (D n).2 ≠ ⊤)
    (hF : Stage0Facts c m β₀ tL (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) p L s₂ e₂)
    (hρ : IsDrivenCurve (stCurvep c m p L s₂)) (he₂ : e₂.2 = capLife (stCurvep c m p L s₂))
    (hgen : ∀ T < capLife (stCurvep c m p L s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m p L s₂)))
    (hW0 : e₂.1 0 = 0) :
    LiftRel β₀ tL γ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
      (newPc s₂ e₂) := by
  obtain ⟨hcH, hc1, hoff⟩ := hU
  obtain ⟨htipD, hgd, hpos, hend, hd₁, hfin, htop⟩ := hF
  have htail := tail_of_launch hl hβr hK hDom
  have hTcl := isClosed_tail_times hβ.1 tL (isClosed_tipSet_launch hP hl)
  by_cases he₁ : L = ⊤
  · obtain ⟨hW, ⟨α, f, hαeq, hα0, hαc, hc, hgc, hcl⟩, hcH₂, hc1₂, hdom⟩ := htop he₁
    exact liftRel_concrete_top2P hγ hcH hc1 hoff hTcl hd₁ htipD htail he₁ hρ he₂ hgen hW hW0 hαeq hα0 hαc hc hgc
      hcl hcH₂ hc1₂ hdom hgd
  · obtain ⟨hfin₂, hW, ⟨α, f, hαeq, hα0, hαc, hc, hgc⟩, hcH₂, hc1₂, hdom⟩ := hfin he₁
    exact liftRel_concrete_drivenP hγ hcH hc1 hoff (isCompact_tail_times_launch hP hl (hLfin he₁) hβ tL) hd₁ htipD
      htail he₁ hpos hρ he₂ hgen hfin₂ hW hW0 hαeq hα0 hαc hc hgc hcH₂ hc1₂ hdom hgd hend

end Lift

/-! ### Along the walks -/

/-- The deterministic stage shift (the start piece's visit time of `R` at stage `0`). -/
def shiftD (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (R : ℝ) (D₁ : ℕ → Drv) (j : ℕ) : ℝ≥0 :=
  if j = 0 then visitTime (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R else 0

/-- The deterministic v3 stage curve. -/
def stCurve3 (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (c : Chart) (m : ℝ)
    (D₁ D₂ : ℕ → Drv) (j : ℕ) : ℝ → ℂ :=
  stCurvep c m (fun t => pcPt (wRun κ θ b₁ J₁ D₁ (j + relOff κ θ b₁ J₁ R D₁)) (D₁ (j + relOff κ θ b₁ J₁ R D₁))
      (shiftD κ θ b₁ J₁ R D₁ j + t))
    ((D₁ (j + relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ j) (wRun κ θ b₂ J₂ D₂ j)

theorem stCurve3_of_ne {κ θ : ℝ} {b₁ : ℝ → ℝ} {J₁ : Finset ℝ} {b₂ : ℝ → ℝ} {J₂ : Finset ℝ} {R : ℝ} {c : Chart}
    {m : ℝ} {D₁ D₂ : ℕ → Drv} {j : ℕ} (hj : j ≠ 0) :
    stCurve3 κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂ j = stCurvep c m
      (pcPt (wRun κ θ b₁ J₁ D₁ (j + relOff κ θ b₁ J₁ R D₁)) (D₁ (j + relOff κ θ b₁ J₁ R D₁)))
      (D₁ (j + relOff κ θ b₁ J₁ R D₁)).2 (wRun κ θ b₂ J₂ D₂ j) := by
  unfold stCurve3 shiftD
  simp only [hj, ↓reduceIte, zero_add, ENNReal.coe_zero, tsub_zero]

/-- **The per-stage facts left, along the walks** (one sample). -/
def StagesGeom3 (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (c : Chart) (m : ℝ)
    (D₁ D₂ : ℕ → Drv) (Gi : ℕ → Prop) (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) : Prop :=
  (¬ ZeroRoot κ θ b₁ J₁ R D₁ →
    (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R D₁) ≠ none →
    ((D₁ (relOff κ θ b₁ J₁ R D₁)).2 ≠ 0 → Gi 0 ∧
      Stage0Facts c m β₀ tL (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁))
        (fun t => pcPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁))
          (shiftD κ θ b₁ J₁ R D₁ 0 + t))
        ((D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0) (wRun κ θ b₂ J₂ D₂ 0) (D₂ 0)) ∧
    ((D₁ (relOff κ θ b₁ J₁ R D₁)).2 = 0 → LiftRel β₀ tL γ
      (newPc (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)))
      (newPc (ExplState.init 0) (D₂ 0)))) ∧
  ∀ i, 2 ≤ i → i % 2 = 0 →
    (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (i + relOff κ θ b₁ J₁ R D₁) ≠ none →
    stStatus (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁)) = GW1W.stArcM true →
    ExplState.IsAdmissibleSeed κ (leftLim b₁ (stPt (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁))))
      (rightLim b₁ (stPt (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁)))) θ →
    Gi i ∧ StageRelP c m (pcPt (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁)) (D₁ (i + relOff κ θ b₁ J₁ R D₁)))
      (D₁ (i + relOff κ θ b₁ J₁ R D₁)).2 (wRun κ θ b₂ J₂ D₂ i) (D₂ i)

/-- **The piece lifts from the per-stage facts left** (deterministic, one sample). -/
theorem piecesLift2_of_geom3 {κ θ : ℝ} {b₁ : ℝ → ℝ} {J₁ : Finset ℝ} {b₂ : ℝ → ℝ} {J₂ : Finset ℝ} {R R' : ℝ}
    {c : Chart} {m : ℝ} {A : Set ℂ} {D₁ D₂ : ℕ → Drv} {Gi : ℕ → Prop} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
    (hγ : IsTailLiftCurve c R' m β₀ tL γ) (hcc : c.IsConformal) (hU : UpperChartOK c)
    (hDom : c.2.1 '' H = H \ fillH A) (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hβ : IsProperCurve β₀)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hP : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hpos : ∀ n, 0 < n → (wRun κ θ b₁ J₁ D₁ (n + 1)).2.2.2.1 n ≠ none → (D₁ n).2 ≠ 0)
    (hgd : ∀ i, 2 ≤ i →
      (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (i + relOff κ θ b₁ J₁ R D₁) ≠ none →
      {t : ℝ≥0 | (t : ℝ≥0∞) < (D₁ (i + relOff κ θ b₁ J₁ R D₁)).2} ⊆
        closure (goodT c (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁)) (D₁ (i + relOff κ θ b₁ J₁ R D₁))))
    (hG : StagesGeom3 κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂ Gi β₀ γ tL) (hreg : ∀ j, IsRegularDriver (D₂ j))
    (hgen : ∀ j, Gi j → ¬ (j % 2 = 1 ∨ (j = 0 ∧ ZeroRoot κ θ b₁ J₁ R D₁) ∨ (D₁ (j + relOff κ θ b₁ J₁ R D₁)).2 = 0) →
      (D₂ j).2 = capLife (stCurve3 κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂ j) ∧
      ∀ T < capLife (stCurve3 κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂ j),
        IsGeneratingTrace (D₂ j).1 T (capTrace (stCurve3 κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂ j)))
    (hdrv : ∀ j, Gi j → IsDrivenCurve (stCurve3 κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂ j)) :
    PiecesLift2 κ θ b₁ J₁ b₂ J₂ R D₁ D₂ β₀ γ tL := by
  obtain ⟨h0, hi⟩ := hG
  refine ⟨?_, fun hZ hl => ?_⟩
  · intro i hi2 hl hflow hstat hseed
    have hev : i % 2 = 0 := of_decide_eq_true hflow
    have hne : i ≠ 0 := by omega
    obtain ⟨hGi, hF⟩ := hi i hi2 hev hl hstat hseed
    have hp := hpos _ (by omega) hl
    have hnZ : ¬ (i % 2 = 1 ∨ (i = 0 ∧ ZeroRoot κ θ b₁ J₁ R D₁) ∨ (D₁ (i + relOff κ θ b₁ J₁ R D₁)).2 = 0) := by
      rintro (h | ⟨h, -⟩ | h)
      · omega
      · omega
      · exact hp h
    obtain ⟨he₂, hg⟩ := hgen i hGi hnZ
    have hd := hdrv i hGi
    rw [stCurve3_of_ne hne] at he₂ hg hd
    exact liftRel_of_stage3 hγ hcc hU hDom hK hβ hβr hP hl hp (hgd i hi2 hl) hF hd he₂ hg (hreg i).2.1
  · by_cases hd0 : (D₁ (relOff κ θ b₁ J₁ R D₁)).2 = 0
    · exact (h0 hZ hl).2 hd0
    · obtain ⟨hG0, hF⟩ := (h0 hZ hl).1 hd0
      have hnZ : ¬ (0 % 2 = 1 ∨ (0 = 0 ∧ ZeroRoot κ θ b₁ J₁ R D₁) ∨
          (D₁ (0 + relOff κ θ b₁ J₁ R D₁)).2 = 0) := by
        rintro (h | ⟨-, h⟩ | h)
        · omega
        · exact hZ h
        · rw [zero_add] at h; exact hd0 h
      obtain ⟨he₂, hg⟩ := hgen 0 hG0 hnZ
      have hd := hdrv 0 hG0
      unfold stCurve3 at he₂ hg hd
      simp only [zero_add] at he₂ hg hd
      exact liftRel_of_stage0 hγ hU hDom hK hβ hβr hP hl
        (fun hL h => hL (by rw [h]; exact ENNReal.top_sub_coe)) hF hd he₂ hg (hreg 0).2.1


open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- **The corrected target's clause** (the almost-sure part of `RelDriverAtT`) for a relative family `EL`. -/
def ClauseT (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ)
    (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
        ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀ tL γ →
          ∃ (ι : ℝ → ℝ) (o : ℕ),
            RayCorr b jumps (affData 1 m b') (affJumps 1 m J') (realMax (upperPrefix κ b jumps E u l k ω₀)) ι ∧
            RayChartLim c (realMax (upperPrefix κ b jumps E u l k ω₀)) m ι ∧
            (∀ s, ∀ x : ℝ, β₀ (tL + s) = x → realMax (upperPrefix κ b jumps E u l k ω₀) ≤ x) ∧
            (∀ s, ∀ x : ℝ, realMax (upperPrefix κ b jumps E u l k ω₀) < x → β₀ (tL + s) = x → γ s = ι x) ∧
            ((∃ N : ℕ, RunInputs'' κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
              (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
              (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o N ∧
            (ArcStart κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
                (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ tL o ∨
              PieceStartV κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
                (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
                (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o)) ∨
            (PieceStartV κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
                (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
                (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o ∧
              (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) o ω).2 = ⊤))

/-- The v3 launch-level curves, zero events. -/
abbrev lρ3 (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ) :
    ℕ → (ℕ → Ω → Drv) → Ω → ℝ → ℂ :=
  cρ3 κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) c m (lD₁ b jumps E)

abbrev lZ3 (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) : ℕ → (ℕ → Ω → Drv) → Set Ω :=
  cZ3 κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E)

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- The per-stage facts left, almost surely (v3). -/
def GeomAt3 (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ)
    (ΦG : ℕ → Ω → ExplState → Prop) (EL : ℕ → Ω → Drv) : Prop :=
  ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
    ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
      ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (lR κ b jumps E u l k ω₀) m β₀ tL γ →
        StagesGeom3 κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) c m
          (lD₁ b jumps E ω) (fun j => EL j ω) (fun j => ω ∈ lG κ b' J' m ΦG j EL) β₀ γ tL

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- **The concrete rule in v3 form** (decision D6, option A). -/
def ConcreteSplitV3At (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ ΦG : ℕ → Ω → ExplState → Prop,
    (∀ j F, (∀ i < j, Measurable (F i)) → (∀ i < j, ∀ ω, IsRegularDriver (F i ω)) →
      (∀ i < j, ∀ ω ∈ lZ3 κ b jumps E u l k ω₀ i F, F i ω = zeroDrv) →
      (∀ i < j, ∀ ω ∈ lG κ b' J' m ΦG i F, ω ∉ lZ3 κ b jumps E u l k ω₀ i F →
        (F i ω).2 = capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m i F ω) ∧
        ∀ T < capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m i F ω),
          IsGeneratingTrace (F i ω).1 T (capTrace (lρ3 κ b jumps E u l k ω₀ c b' J' m i F ω))) →
      StageOK (lρ3 κ b jumps E u l k ω₀ c b' J' m j F) (lG κ b' J' m ΦG j F) (lZ3 κ b jumps E u l k ω₀ j F)) ∧
    ∀ EL : ℕ → Ω → Drv, (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      (∀ j, ∀ ω ∈ lZ3 κ b jumps E u l k ω₀ j EL, EL j ω = zeroDrv) →
      (∀ j, ∀ ω ∈ lG κ b' J' m ΦG j EL, ω ∉ lZ3 κ b jumps E u l k ω₀ j EL →
        (EL j ω).2 = capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω) ∧
        ∀ T < capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω),
          IsGeneratingTrace (EL j ω).1 T (capTrace (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω))) →
      GeomAt3 κ b jumps P E u l k ω₀ c b' J' m ΦG EL ∧
      (PiecesLift2AS κ b jumps P E u l k ω₀ c b' J' m EL → ClauseT κ b jumps P E u l k ω₀ c b' J' m EL)

/-- **Named input: SB2(2)'s concrete stage rule in v3 form.** -/
def SB2LowerConcreteSplitV3Statement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ConcreteSplitV3At κ b jumps P E u l k ω₀ c b' J'

/-- **D7's corrected target from the v3 concrete rule** (Theorems 1.2–1.3; the tail form of S3). -/
theorem sb2LowerRelDriverStatementT_of_splitV3 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hS3 : S3.Canon.SB2LowerWalkTailNoCommonArcStatement.{u})
    (hS : SB2LowerConcreteSplitV3Statement.{u}) : SB2LowerRelDriverStatementT.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hRLQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (GW1W.regLaunches_of_stagedPiecesRegular (hER _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)))
  filter_upwards [hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerUpperChart κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHeadHull κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerWalkInputs h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerStageDensityTail h12 h13 h12₀ h13₀ hS3 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp
      hlθ hL hleft,
    hRLQ] with ω₀ h₀ hC₀ hH₀ hI₀ hD₀ hR₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨hcc, hU, hDom⟩ := hC₀ c θ hlaunch b' J' h' hb' hT' hG'
  obtain ⟨ΦG, hok, hcl⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hmeas, hreg, hZ, hgen⟩ := exists_EL_concrete3 κ (-(Real.pi / 2)) b jumps (affData 1 m b')
    (affJumps 1 m J') (lR κ b jumps E u l k ω₀) c m (lD₁ b jumps E) ΦG hok
  refine ⟨EL, hmeas, hreg, ?_⟩
  obtain ⟨hgeom, hrest⟩ := hcl EL hmeas hreg hZ hgen
  refine hrest ?_
  filter_upwards [hgeom, hH₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG',
    hD₀ c θ hlaunch b' J' h' hb' hT' hG', hR₀] with ω hω hHω hIω hDω hRω
  intro β₀ hβ hβ0 hβr tL γ hγ
  exact piecesLift2_of_geom3 hγ hcc hU hDom (hHω β₀ hβ hβ0 hβr tL hγ.1) hβ hβr hRω
    (fun n hn hl => (hIω n).2.2 hn hl) (hDω β₀ hβ hβ0 hβr tL hγ.1) (hω β₀ hβ hβ0 hβr tL γ hγ)
    (fun j => hreg j ω) (fun j hG hnZ => hgen j ω hG hnZ)
    (fun j hG => (hok j EL (fun i _ => hmeas i) (fun i _ ω => hreg i ω) (fun i _ => hZ i)
      (fun i _ => hgen i)).2.2.2 ω hG)

/-- **SB2(2)'s combined target (R104a) from the v3 concrete rule and the conditional half.** -/
theorem sb2LowerLaunchLiftStatement_of_splitV3 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hS3 : S3.Canon.SB2LowerWalkTailNoCommonArcStatement.{u})
    (hS : SB2LowerConcreteSplitV3Statement.{u}) (hcond : SB2LowerRelStageCondStatement.{u}) :
    Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_relDriverT h12 h13 h12₀ h13₀
    (sb2LowerRelDriverStatementT_of_splitV3 h12 h13 h12₀ h13₀ hS3 hS) hcond

end InteractingSLE.Theorem14.SB.Lk
