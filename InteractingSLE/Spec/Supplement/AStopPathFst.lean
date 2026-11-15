/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopPathSnd
import InteractingSLE.Spec.Supplement.OrdFstSlit

/-!
# Item 6 of `AStopSourceInputs` for the A-stopped first continuation at its seed

Packet PROVE-T15-ASTOP-PATH. In the setting of `RLC.RetOrdAStopSourceFstSeedStatement`, on an event `M` of ordinary
pairs (almost surely) with a seed `τ = tipPos` (almost surely on `M`) and one force type of the seeded word
`shiftW τ β.1` (angle `θ₁`), for any continuous driver `W` from `0`, stop set `J ω`, stop `V'` and trace `γ'` with
`V' = V`, `γ' = γ − τ` on `[0, V]` (`V`, `γ` the canonical A-stopped life and path from the seed `tipPos`), the
generation `W ↦ γ'` and `J ω = {z real : ψ(z + τ) ∈ A}` almost surely on `M` (the outputs of
PROVE-T15-ASTOP-PROC's `AStopProc.exists_fstProcInputs`), **`ae_aStopPath_fst`** proves the same four facts as
`ae_aStopPath_snd`. The first tip's side heights come from the sided word `IsRetainedWordFst` (PROVE-T15-ORDDET3's
`ae_isRetainedWordFst_of_meanIdent`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.RLC.AStopPath

open Supp7 Restart PiecewiseConstantBoundaryData MartChar.RealFlow OrdModel Exist.StagedLaw

universe u

/-- The untouched word in the chart translated by `τ`. -/
theorem isUntouchedWord_shift {b : ℝ → ℝ} {jumps : Finset ℝ} {K : Set ℂ} {ψ : ℂ → ℂ} {c : BoundaryWord}
    (hu : IsUntouchedWord b jumps K ψ c) (τ : ℝ) :
    IsUntouchedWord b jumps K (fun w => ψ (w + τ)) (BoundaryWord.shiftW τ c) := by
  intro y him hK hJ
  have e : (y : ℂ) + (τ : ℂ) = ((y + τ : ℝ) : ℂ) := (ofReal_add y τ).symm
  simp only [e] at him hK hJ ⊢
  obtain ⟨h1, h2⟩ := hu (y + τ) him hK hJ
  refine ⟨fun hy => h1 ?_, by rw [BoundaryWord.fn_shiftW, h2]⟩
  rw [BoundaryWord.jumps_shiftW, Finset.mem_image] at hy
  obtain ⟨j, hj, hjy⟩ := hy
  rw [← hjy, sub_add_cancel]
  exact hj

theorem IsAChart.congr_K {ψ : ℂ → ℂ} {K K' : Set ℂ} {x : ℝ} (hA : IsAChart ψ K x) (hK : K = K') :
    IsAChart ψ K' x := hK ▸ hA

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞} {d : RetData Ω}

/-- **Item 6 of `AStopSourceInputs` for the first continuation at its seed, up to the terminal case** (see the module
docstring). -/
theorem ae_aStopPath_fst (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hx : x₂ ≤ x₁) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {c : Ω → BoundaryWord}
    (hfst : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      IsRetainedWordFst κ θ₁ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (tipPos d η₁ ω) (c ω) ∧
      IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (c ω))
    {M : Set Ω} (hMord : ∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r)
    {τ : Ω → ℝ} (hτ : ∀ᵐ ω ∂P, ω ∈ M → τ ω = tipPos d η₁ ω)
    {a : RetAux79.ForceWordType}
    (htype : ∀ᵐ ω ∂P, ω ∈ M → BoundaryWord.shiftW (τ ω) (c ω) ∈ FCDet.typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR)
    {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0)
    {J : Ω → Set ℂ} {V' : Ω → ℝ≥0∞} {γ' : Ω → ℝ≥0 → ℂ}
    (hcan : ∀ᵐ ω ∂P, ω ∈ M →
      V' ω = canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
        (tipPos d η₁ ω) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u
        (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) →
        γ' ω t = canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
          (tipPos d η₁ ω) t - τ ω)
    (hgen : ∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (W · ω) (V' ω) (γ' ω))
    (hE : ∀ᵐ ω ∂P, ω ∈ M →
      J ω = {z : ℂ | z.im = 0 ∧ d.inv ω (z + τ ω) ∈ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r}) :
    (∀ᵐ ω ∂P, ω ∈ M → 0 < V' ω) ∧
    (∀ᵐ ω ∂P, ω ∈ M → V' ω ≤ FCDet.thr a.rhoL a.rhoR W
      (fun ω => FCDet.typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (BoundaryWord.shiftW (τ ω) (c ω)))
      (fun ω => FCDet.typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (BoundaryWord.shiftW (τ ω) (c ω))) ω) ∧
    (∀ᵐ ω ∂P, ω ∈ M → ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < V' ω → γ' ω t ∉ J ω) ∧
    (∀ᵐ ω ∂P, ω ∈ M → V' ω ≠ ⊤ →
      (contStop (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) = ζ₁ ω ∧
        η₁ ω (ζ₁ ω).toNNReal ∉ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) ∨
      γ' ω (V' ω).toNNReal ∈ J ω) := by
  have hp₁ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hp₂ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  have hv := FCPlumb.ae_live_real_incident_bounds hκ hκ4 hb hh hη₁
  have hj := RLC.jumpVisitStatement κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁
  have hF : ∀ᵐ ω ∂P, ω ∈ M → 0 < V' ω ∧
      ¬ ForceWord.ThresholdCondition a.rhoL a.rhoR 0
        (FCDet.typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (BoundaryWord.shiftW (τ ω) (c ω)))
        (FCDet.typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (BoundaryWord.shiftW (τ ω) (c ω))) ∧
      (∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < V' ω →
        ¬ ForceWord.ThresholdCondition a.rhoL a.rhoR (W q ω)
          (fun i => Sec7.PocketTraversal.geomLW W
            (fun ω => FCDet.typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (BoundaryWord.shiftW (τ ω) (c ω))) i q ω)
          (fun j => Sec7.PocketTraversal.geomRW W
            (fun ω => FCDet.typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (BoundaryWord.shiftW (τ ω) (c ω))) j q ω)) ∧
      (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < V' ω → γ' ω t ∉ J ω) ∧
      (V' ω ≠ ⊤ →
        (contStop (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) = ζ₁ ω ∧
          η₁ ω (ζ₁ ω).toNNReal ∉ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) ∨
        γ' ω (V' ω).toNNReal ∈ J ω) := by
    filter_upwards [hp₁, hp₂, hv, hj, hag, hfst, hMord, hτ, htype, hcan, hgen, hE] with ω hp₁ω hp₂ω hvω hjω hagω
      hwω hMω hτω htω hcω hgω hEω hω
    have hord := hMω hω
    obtain ⟨hG, ha₁, ha₂⟩ := hagω hord.1 hord.2.1
    have hS : IsOrdSample d η₁ η₂ ζ₁ ζ₂ x₁ x₂ ω := ⟨hG, hp₁ω, hp₂ω, hx, ha₁, ha₂, hord⟩
    obtain ⟨hret, hunt⟩ := hwω hord
    have hR := hS.isRetCont_fst hd
    have hK : η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r = η₂ ω '' Icc 0 d.r ∪ η₁ ω '' Icc 0 d.u := union_comm _ _
    have hA := (hS.isAChart_fst hd).congr_K hK
    have hτe := hτω hω
    have htyp := htω hω
    rw [hτe] at htyp
    obtain ⟨hV, hγ⟩ := hcω hω
    have hg := hgω hω
    have hEq := hEω hω
    rw [hτe] at hγ hEq
    have hD := hS.D_eq hd
    rw [hD, OrdDet.canonRetLife_shift, hK] at hV hγ
    replace hγ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ canonRetLife (H \ fillH (η₂ ω '' Icc 0 d.r ∪ η₁ ω '' Icc 0 d.u))
        (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u (η₂ ω '' Icc 0 d.r ∪ η₁ ω '' Icc 0 d.u) 0 →
        γ' ω t = canonRetPath (H \ fillH (η₂ ω '' Icc 0 d.r ∪ η₁ ω '' Icc 0 d.u))
          (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u (η₂ ω '' Icc 0 d.r ∪ η₁ ω '' Icc 0 d.u) 0 t :=
      fun t ht => by rw [hγ t ht, OrdDet.canonRetPath_shift, add_sub_cancel_right]
    rw [hV] at hg ⊢
    have hg' := isGeneratingTrace_congr_le hg fun t ht => (hγ t ht).symm
    have hunt' := isUntouchedWord_shift (hK ▸ hunt) (tipPos d η₁ ω)
    have hside : ∀ y : ℝ, y ≠ 0 → d.inv ω (y + tipPos d η₁ ω) ∈ H →
        d.inv ω (y + tipPos d η₁ ω) ∉ η₂ ω '' Icc 0 d.r →
        d.inv ω (y + tipPos d η₁ ω) ∈ η₁ ω '' Icc 0 d.u →
        (y < 0 → (BoundaryWord.shiftW (tipPos d η₁ ω) (c ω)).fn y = -sleLambda κ - θ₁ * chiC κ) ∧
          (0 < y → (BoundaryWord.shiftW (tipPos d η₁ ω) (c ω)).fn y = sleLambda κ - θ₁ * chiC κ) := by
      intro y hy0 hyH hyO hyη
      have e : (y : ℂ) + (tipPos d η₁ ω : ℂ) = ((y + tipPos d η₁ ω : ℝ) : ℂ) := (ofReal_add _ _).symm
      have hne₁ : d.inv ω (y + tipPos d η₁ ω) ≠ η₁ ω d.u := fun he =>
        hy0 (ofReal_eq_zero.1 (hR.tipUniq _ (by show (0 : ℝ) ≤ (y : ℂ).im; rw [ofReal_im]) he))
      rw [e] at hyH hyO hyη hne₁
      obtain ⟨h1, h2⟩ := hret (y + tipPos d η₁ ω) hyH hne₁ hyη hyO
      simp only [BoundaryWord.fn_shiftW]
      exact ⟨fun hy => h1 (by linarith), fun hy => h2 (by linarith)⟩
    obtain ⟨hpos, hseed, hthr, havoid, hterm⟩ :=
      aStop_facts hR hA hκ hb hunt' hvω hjω hside htyp (hWc ω) (hW0 ω) hg'
    rw [← hτe] at hseed
    have hEq' : J ω = aSet (fun w => d.inv ω (w + tipPos d η₁ ω))
        (η₂ ω '' Icc 0 d.r ∪ η₁ ω '' Icc 0 d.u) := by
      rw [hEq, ← hK]; rfl
    refine ⟨hpos, hseed, fun q hq0 hq => ?_, fun t ht0 ht => ?_, fun hfin => ?_⟩
    · have h' := hthr q hq0 hq
      rw [← hτe] at h'
      exact h'
    · rw [hγ t ht.le, hEq']
      exact havoid t ht0 ht
    · rcases hterm hfin with h1 | h2
      · left
        rw [hK]
        exact h1
      · right
        rw [hγ _ (ENNReal.coe_toNNReal_le_self), hEq']
        exact h2
  refine ⟨hF.mono fun ω h hω => (h hω).1, ?_, hF.mono fun ω h hω => (h hω).2.2.2.1,
    hF.mono fun ω h hω => (h hω).2.2.2.2⟩
  apply RetAux79.life_le_thr_of_retPrelifeNonThreshold hWc
  exact FCPlumb.prelifeNonThreshold_of_boundary_checks hWc hW0
    (fun ω => (FCDet.isOrderedForceWord_typeXL (BoundaryWord.shiftW (τ ω) (c ω))).2.1)
    (fun ω => (FCDet.isOrderedForceWord_typeXL (BoundaryWord.shiftW (τ ω) (c ω))).2.2.2) hgen
    (hF.mono fun ω h hω => (h hω).2.1) (hF.mono fun ω h hω q hq0 hq _ => (h hω).2.2.1 q hq0 hq)

end InteractingSLE.RLC.AStopPath
