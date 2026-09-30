import QuantumZipper.Proofs.Section5.Prop16LocGood
import QuantumZipper.Proofs.LQG.FiniteArea
import QuantumZipper.Proofs.LQG.PositivityArea

/-!
# D4⁺ʷ inputs (part 1): local goodness with a *nice* free-field witness

`IsLocNiceOn γ V x` strengthens `Prop16Area.G.IsLocallyGoodOn`: the good sample `y` with
`x = y + ψ` on the dyadic folded circles near `V` also has finite area on every half-ball
`B(0,a) ∩ ℍ` and charges every nonempty open subset of `ℍ`. These two extra properties hold
almost surely for the free field (`FinArea.ae_qAreaMeasure_ball_lt_top`, M4-A3;
`PositivityArea.ae_forall_pos_qAreaMeasure`, M4-P2), so the proof of
`prop16LocGoodStmt_of_coupling` gives the stronger form verbatim: the coupling witness is
`y := X_free ω₀`, and the almost-sure event on the coupling space is enlarged by the two
properties (`prop16LocNiceStmt_of_coupling`).

They are needed for the local scale of the zoomed field (`hsc0` of `Prop16D4WInputsStmt`):
finiteness of the area near the boundary point and positivity of the area of small half-balls.
Own elementary argument (reuse of the LOCGOOD transfer).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area.G

/-- Local goodness on `V` with a nice witness (finite half-ball areas, positive on open sets). -/
def IsLocNiceOn (γ : ℝ) (V : Set ℂ) (x : FieldSample) : Prop :=
  ∃ W : Set ℂ, IsOpen W ∧ W ∩ Hbar = V ∧ ∃ (y : FieldSample) (ψ : ℂ → ℝ),
    IsLQGGood γ y ∧ (∀ a : ℝ, qAreaMeasure γ y (Metric.ball 0 a ∩ H) < ⊤) ∧
    (∀ U : Set ℂ, IsOpen U → U ⊆ H → U.Nonempty → 0 < qAreaMeasure γ y U) ∧
    ContinuousOn ψ V ∧ CircAgree W x (y + ofFun ψ)

theorem IsLocNiceOn.isLocallyGoodOn {γ : ℝ} {V : Set ℂ} {x : FieldSample}
    (h : IsLocNiceOn γ V x) : IsLocallyGoodOn γ V x := by
  obtain ⟨W, hWo, hWV, y, ψ, hy, -, -, hψ, hag⟩ := h
  exact ⟨W, hWo, hWV, y, ψ, hy, hψ, hag⟩

/-- **Node LOCNICE:** almost surely the mixed field is locally nice on `D ∪ (a,b)`. -/
def Prop16LocNiceStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    ∀ᵐ ω ∂P, IsLocNiceOn γ (D ∪ realSet (Set.Ioo a b)) (X ω)

/-- **LOCNICE from the domain Markov coupling** (the proof of `prop16LocGoodStmt_of_coupling`
with the almost-sure event enlarged by M4-A3 and M4-P2). -/
theorem prop16LocNiceStmt_of_coupling (hA : Prop16MixedFreeLocCouplingStmt) :
    Prop16LocNiceStmt := by
  intro γ D c d a b h0 Ω _ P X hdat
  obtain ⟨hγ, hγ2, hgeo, hab, hca, hbd, -, hP, hX, -, -⟩ := hdat
  obtain ⟨W, hWo, hWV⟩ := locGood_exists_open hgeo hca hbd
  obtain ⟨Ω₀, _, _, P₀, Y, Xf, hP₀, hY, hXf, hag⟩ := hA D c d a b hgeo hab hca hbd
  set V := D ∪ realSet (Ioo a b) with hVdef
  have hVW : ∀ {s : Set ℂ}, s ⊆ Hbar → (s ⊆ V ↔ s ⊆ W) := fun {s} hs =>
    ⟨fun h u hu => by rw [← hWV] at h; exact (h hu).1,
      fun h u hu => by rw [← hWV]; exact ⟨h hu, hs hu⟩⟩
  have hsubH : ∀ (n k : ℕ) (z : ℂ), closedBall (dyadicRoundC n z) (radius k) ∩ Hbar ⊆ Hbar :=
    fun _ _ _ => inter_subset_right
  let I := {m : Measure ℂ // m ∈ locCircSet V}
  have : Countable I := (locCircSet_countable V).to_subtype
  have hadm : ∀ i : I, IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) i.1 := by
    rintro ⟨_, n, k, z, hz, hsub, rfl⟩
    exact locGood_isAdmissible_circle hgeo hca hbd hWo hWV
      (CircleCont.dyadicRoundC_mem_Hbar hz n) (radius_pos k) ((hVW (hsubH n k z)).1 hsub)
  have hlaw := locGood_map_eq_of_isMixedGFF hX hY (fun i : I => i.1) hadm
  have hS : ∀ᵐ ω₀ ∂P₀, ω₀ ∈ {ω₀ | IsLQGGood γ (Xf ω₀) ∧
      (∀ a : ℝ, qAreaMeasure γ (Xf ω₀) (Metric.ball 0 a ∩ H) < ⊤) ∧
      (∀ U : Set ℂ, IsOpen U → U ⊆ H → U.Nonempty → 0 < qAreaMeasure γ (Xf ω₀) U) ∧
      ∃ ψ : ℂ → ℝ, ContinuousOn ψ V ∧
      Prop16Area.G.CircAgree V (Y ω₀) (Xf ω₀ + ofFun ψ)} := by
    filter_upwards [AreaOffsets.ae_isLQGGood hXf hγ hγ2,
      FinArea.ae_qAreaMeasure_ball_lt_top hXf (P := P₀) hγ hγ2,
      PositivityArea.ae_forall_pos_qAreaMeasure hXf (P := P₀) hγ hγ2, hag]
      with ω₀ h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩
  have hmF : Measurable fun ω (i : I) => X ω i.1 :=
    measurable_pi_iff.2 fun i => hX.measurable_coord _
  have hmG : Measurable fun ω (i : I) => Y ω i.1 :=
    measurable_pi_iff.2 fun i => hY.measurable_coord _
  filter_upwards [locGood_ae_exists_of_map_eq hmF.aemeasurable hmG hlaw hS] with ω hω
  obtain ⟨ω₀, ⟨hgood, hfin, hpos, ψ, hψ, hag'⟩, hFG⟩ := hω
  refine ⟨W, hWo, hWV, Xf ω₀, ψ, hgood, hfin, hpos, hψ, fun n k z hz hsub => ?_⟩
  have hsubV := (hVW (hsubH n k z)).2 hsub
  have h1 := congrFun hFG ⟨_, n, k, z, hz, hsubV, rfl⟩
  exact h1.trans (hag' n k z hz hsubV)

end Prop16Asm

end QuantumZipper
