/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkChainRun
import InteractingSLE.Spec.Supplement.GW1PieceSimpleFiber
import InteractingSLE.Spec.Supplement.GB6Past

/-!
# GW1: the adapter from GW1Z's simple pieces

The additional geometric data are stated as physical radial-tip equalities, independently
of the chosen trace or boundary extension. Preservation of the upper half-plane by run
charts is proved here from piece regularity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW1WalkChain

open GW1X GW1Bookkeep Exist Exist.Staged Exist.StagedLaw

theorem maps_H_chart_run {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ, (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ) :
    MapsTo (ExplState.run κ b jumps spec D n).2.2.2.2.1.2.1 H H := by
  induction n with
  | zero =>
    intro z hz
    change 0 < (z + (spec.1 : ℂ)).im
    simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using (show 0 < z.im from hz)
  | succ n ih =>
    cases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with
    | none =>
      obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch spec D hl
      rw [ha]
      intro z hz
      apply ih
      change 0 < (z + (a : ℂ)).im
      simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using (show 0 < z.im from hz)
    | some p =>
      obtain ⟨c, θ⟩ := p
      obtain ⟨_, heq, _⟩ := eq_launch_of_launches spec D hl
      rw [heq]
      by_cases htop : min (instrTime spec n) (D n).2 = ⊤
      · rw [GW1P.chart_launch_of_top _ _ _ _ _ htop]
        exact ih
      · rw [chart_launch _ _ _ _ _ htop]
        obtain ⟨hW, hW0⟩ := (hreg n c θ hl).continuous_stoppedReal
        intro z hz
        apply ih
        exact QuantumZipper.RS.fwdMapInv_mem_H hW hW0 (NNReal.coe_nonneg _) hz

/-- The seed and finite endpoint read through a launch chart agree with the machine's
recorded current points. These are geometric equalities, not a simplicity assumption. -/
def WalkTipCoordinates (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∀ k c θ, (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
    let S := min (instrTime spec k) (D k).2
    let W := fun r : ℝ≥0 => (D k).1 (min (r : ℝ≥0∞) S).toNNReal
    c.tipAt W 0 (stPt (ExplState.run κ b jumps spec D k)) ∧
      (S ≠ ⊤ → c.tipAt W S.toNNReal (stPt (ExplState.run κ b jumps spec D (k + 1))))

/-- GW1Z's interface supplies GW1Y's interface once the physical seed and endpoint are
identified. Seed membership in the old union is supplied by the chronological induction. -/
theorem pieceSimpleAt_of_isSimplePiece {c : Chart} {W : ℝ≥0 → ℝ} {S : ℝ≥0∞}
    {A : Set ℂ} {q₀ q₁ : ℝ} (h : GW1Z.IsSimplePiece c W S A)
    (hmaps : MapsTo c.2.1 H H) (hq₀ : (q₀ : ℂ) ∈ A)
    (hstart : c.tipAt (fun r => W (min (r : ℝ≥0∞) S).toNNReal) 0 q₀)
    (hend : S ≠ ⊤ → c.tipAt (fun r => W (min (r : ℝ≥0∞) S).toNNReal) S.toNNReal q₁) :
    PieceSimpleAt c W S A q₀ q₁ := by
  obtain ⟨f, α, C, hf, hC, hW0, hW, hα, htr, hi, havoid⟩ := h
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα
      (hW.mono fun _ ht => mem_ofPred.2 (le_of_lt ht)) hW0 ht
  have htip (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ S) :
      c.tipAt (fun r => W (min (r : ℝ≥0∞) S).toNNReal) t (f (α t)) :=
    CounterflowRange.tendsto_tip_stopped_of_tendsto hα hW hW0 ht (hf _ (hαH t ht))
  have h0 : f (α 0) = (q₀ : ℂ) := Chart.tipAt_unique (htip 0 (by simp)) hstart
  refine ⟨f, α, C, hf, hC, fun p hp => GW1P.mem_Hbar_of_tendsto hp hmaps (hf p hp),
    hW0, hW, hα, htr, hi, h0, ?_, ?_⟩
  · intro hfin
    exact Chart.tipAt_unique (htip S.toNNReal (by rw [ENNReal.coe_toNNReal hfin])) (hend hfin)
  · rw [CounterflowRange.tipSet_stopped_eq_of_tendsto hα hW hW0
      (fun t ht => hf _ (hαH t ht))]
    ext z
    constructor
    · rintro ⟨⟨_, ⟨t, ht, rfl⟩, rfl⟩, hz⟩
      rcases eq_zero_or_pos t with heq | hpos
      · rw [heq]
        exact mem_singleton _
      · exact False.elim (havoid t hpos ht hz)
    · intro hz
      rw [mem_singleton_iff] at hz
      subst z
      exact ⟨⟨α 0, ⟨0, by simp, rfl⟩, rfl⟩, h0.symm ▸ hq₀⟩

end InteractingSLE.Theorem14.GW1WalkChain
