/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3ChainUnion

/-!
# GB6's union mean, part 1: the relative chain with every earlier hull identity

Packet PROVE-GB6-LINEMEAN. PROVE-Q3-REL3's union mean (`Q3Chain.ae_eqOn_unionMean_gb6`) names a relative driver `Wr`
known only through its hull at the single relative time `u = a(t)`. The candidate mean depends on `Wr` on `[0, u]`, so
the comparison with a version of the relative driver needs the hull identities `Ψ(K'_{t'}) = K̃_{a(t')}` at every
`t' ≤ t`, which `Q3Kernel.exists_relChain_trace` produces and `Q3Kernel.exists_relChain_tip` drops. This file
re-threads them (`HullsUpTo`) through the chain, with the same proofs:

* `exists_relChain_tip_hull`, `exists_isRelConfigOff_gb6_hull`, `ae_exists_isRelConfigOff_gb6_hull`,
  `ae_exists_isRelConfigOff_gb6_words_hull`, `ae_isRelConfigOff_gb6_flow_hull`;
* **`ae_eqOn_unionMean_gb6_hull`**: the union mean with the earlier hull identities, for a retained set given through
  the unbounded components of its lower union (so `A = ℍ` off `{s < ζα}` is allowed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Supp8.GB6LMean

open GB6 (relMap relInv relClock firstContactTime sphereInv gb6WordOfRec gb6Rec)
open Q3Rel (invHull relLog relBad IsRelConfigOff)
open Q3Kernel Q3Chain LocalSets

/-- **The relative hulls up to a counterflow time**: `Ψ(K'_{t'}) = K̃_{a(t')}` for every `t' ≤ t` (`Ψ = relMap U s`,
`a = relClock U s Wc`). -/
def HullsUpTo (U : ℝ → ℝ) (s : ℝ≥0) (Wc Wr : ℝ → ℝ) (t : ℝ≥0) : Prop :=
  ∀ t' : ℝ≥0, t' ≤ t → relMap U s '' fwdHull Wc t' = fwdHull Wr (relClock U s Wc t')

section Sample

variable {wα w : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {α γ : ℝ≥0 → ℂ} {s : ℝ≥0} {U : ℝ → ℝ} {αr : ℝ → ℂ} {t₂ : ℝ}

/-- **`Q3Kernel.exists_relChain_tip` with every earlier hull identity**: the relative chain also generates
`Ψ(K'_{t'})` at `a(t')` for every `t' ≤ t` (`HullsUpTo`). Same proof. -/
theorem exists_relChain_tip_hull (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα})
    (hwα0 : wα 0 = 0) (hs : (s : ℝ≥0∞) < Tα) (hsH : α s ∈ H) (hU : Continuous U) (hU0 : U 0 = 0)
    (hst₂ : (s : ℝ) < t₂) (hUeq : ∀ r ∈ Icc (0 : ℝ) t₂, U r = wα r.toNNReal)
    (hΨ : Q3Rel.IsRetainedChartOff (invHull U s) (relMap U s) (relInv U s) (Q3Rel.relLog U s) (Q3Rel.relBad U s))
    (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0) {t t₁ : ℝ≥0} (ht0 : 0 < t)
    (htt₁ : t < t₁)
    (ht₁ : (t₁ : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
      ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
      0 < relClock U s (fun r : ℝ => w r.toNNReal) t ∧
      relMap U s '' fwdHull (fun r : ℝ => w r.toNNReal) t =
        fwdHull Wr (relClock U s (fun r : ℝ => w r.toNNReal) t) ∧
      HullsUpTo U s (fun r : ℝ => w r.toNNReal) Wr t ∧
      Disjoint (closure (fwdHull U s)) (closure ((fun w : ℂ => -w⁻¹) '' fwdHull (fun r : ℝ => w r.toNNReal) t)) ∧
      Tendsto (fun y => fwdMap (fun r : ℝ => w r.toNNReal) t
        (relInv U s (fwdMapInv Wr (relClock U s (fun r : ℝ => w r.toNNReal) t) y))) (𝓝[H] 0) (𝓝 0) := by
  set Tc := firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)
    with hTcdef
  set Wc : ℝ → ℝ := fun r => w r.toNNReal with hWcdef
  have hWcc : Continuous Wc := hw.comp continuous_real_toNNReal
  have hWc0 : Wc 0 = 0 := by simp [hWcdef, hw0]
  have hs0 : (0 : ℝ) < s := by
    rcases eq_or_lt_of_le (NNReal.coe_nonneg s) with h0 | h0
    · exfalso
      have hs' : s = 0 := by exact_mod_cast h0.symm
      exact GB6.ne_zero_of_mem_H hsH (by rw [hs']; exact hα.1)
    · exact h0
  obtain ⟨Wr, ηr, hWr, hWr0, hηr, hK, ha0, hsm, hac, hd⟩ :=
    exists_relChain_trace hα hwα hwα0 hs hsH hU hU0 hst₂ hUeq hγ hw hw0 ht₁
  set a : ℝ → ℝ := relClock U s Wc with hadef
  have htTc : (t : ℝ≥0∞) < Tc := lt_of_le_of_lt (ENNReal.coe_le_coe.2 htt₁.le) ht₁
  have h0Tc : ((0 : ℝ≥0) : ℝ≥0∞) < Tc := lt_of_le_of_lt bot_le htTc
  have hu : 0 < a t := by
    have := hsm h0Tc htTc ht0
    simpa [ha0] using this
  have hKt := hK t htt₁.le
  have hdt := hd t htTc
  have hdA : ∀ T : ℝ≥0, (T : ℝ≥0∞) < Tc → Disjoint (closure (fwdHull Wc T)) (closure (invHull U s)) :=
    fun T hT => Q3Rel.disjoint_closure_invHull hU hs0.le (hd T hT)
  have hγL := isLoewnerTrace_of_isGeneratingTrace hγ
  have hSbK := Q3Rel.relBad_notMem_closure hU hU0 hs0.le hWcc t.2 hKt (hdA t htTc)
  obtain ⟨hg, hA0⟩ := goodPt_zero_and_notMem hΨ hWcc t.2 hWr hWr0 hηr hu hKt (hdA t htTc) hSbK
  refine ⟨Wr, ηr, hWr, hWr0, hηr, hu, hKt, fun t' ht' => hK t' (ht'.trans htt₁.le), hdt, ?_⟩
  refine tendsto_tip_of_later hΨ hWcc hWc0 hγL t.2 hWr hWr0 hηr hu.le hKt (hdA t htTc) hg hA0 fun δ hδ => ?_
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < Tc} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hcont : ContinuousAt (fun t : ℝ≥0 => a t) t := hac.continuousAt (hopen.mem_nhds htTc)
  obtain ⟨η, hη, hηb⟩ := Metric.continuousAt_iff.1 hcont δ hδ
  set ε : ℝ := min (min δ η) ((t₁ : ℝ) - t) / 2 with hεdef
  have htt₁' : (t : ℝ) < t₁ := by exact_mod_cast htt₁
  have hε0 : 0 < ε := by
    have : 0 < min (min δ η) ((t₁ : ℝ) - t) := lt_min (lt_min hδ hη) (by linarith)
    rw [hεdef]; linarith
  have hεδ : ε < δ := by
    have := min_le_left (min δ η) ((t₁ : ℝ) - t)
    have := min_le_left δ η
    rw [hεdef]; linarith
  have hεη : ε < η := by
    have := min_le_left (min δ η) ((t₁ : ℝ) - t)
    have := min_le_right δ η
    rw [hεdef]; linarith
  have hεt : ε < (t₁ : ℝ) - t := by
    have := min_le_right (min δ η) ((t₁ : ℝ) - t)
    rw [hεdef]; linarith
  set t' : ℝ≥0 := ⟨(t : ℝ) + ε, by positivity⟩ with ht'def
  have ht'v : (t' : ℝ) = t + ε := rfl
  have htt' : t < t' := by rw [← NNReal.coe_lt_coe, ht'v]; linarith
  have ht't₁ : t' ≤ t₁ := by rw [← NNReal.coe_le_coe, ht'v]; linarith
  have ht'Tc : (t' : ℝ≥0∞) < Tc := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht't₁) ht₁
  have hdist : dist t' t < η := by
    rw [NNReal.dist_eq, ht'v, add_sub_cancel_left, abs_of_pos hε0]
    exact hεη
  have hau : a t < a t' := hsm htTc ht'Tc htt'
  have hau' : a t' < a t + δ := by
    have := hηb hdist
    rw [Real.dist_eq] at this
    linarith [le_abs_self (a t' - a t)]
  refine ⟨t', a t', by rw [ht'v]; linarith, by rw [ht'v]; linarith, hau, hau', hK t' ht't₁, ?_⟩
  exact Set.disjoint_of_subset_left subset_closure
    (Set.disjoint_of_subset_right subset_closure (hdA t' ht'Tc))

/-- **`Q3Kernel.exists_isRelConfigOff_gb6` with every earlier hull identity.** Same proof. -/
theorem exists_isRelConfigOff_gb6_hull (hα : IsGeneratingTrace wα Tα α)
    (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα}) (hwα0 : wα 0 = 0) (hs : (s : ℝ≥0∞) < Tα) (hsH : α s ∈ H)
    (hU : Continuous U) (hU0 : U 0 = 0) (hαr : IsLoewnerTrace U αr) (hNR : ∀ v ∈ Ioc (0 : ℝ) s, αr v ≠ 0)
    (hst₂ : (s : ℝ) < t₂) (hUeq : ∀ r ∈ Icc (0 : ℝ) t₂, U r = wα r.toNNReal)
    (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0) {t t₁ : ℝ≥0} (ht0 : 0 < t)
    (htt₁ : t < t₁)
    (ht₁ : (t₁ : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
      ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
      0 < relClock U s (fun r : ℝ => w r.toNNReal) t ∧
      relMap U s '' fwdHull (fun r : ℝ => w r.toNNReal) t =
        fwdHull Wr (relClock U s (fun r : ℝ => w r.toNNReal) t) ∧
      HullsUpTo U s (fun r : ℝ => w r.toNNReal) Wr t ∧
      ∀ (χ lam : ℝ) (β₀ βE βu : ℝ → ℝ) (S₀ SE Su : Finset ℝ) (G₀ GE G v : ℂ → ℝ),
        IsBoundedHarmonicExtension β₀ S₀ G₀ → IsBoundedHarmonicExtension βE SE GE →
        IsBoundedHarmonicExtension βu Su G →
        BHMean.IsSideWord βE SE (fwdMapInv (fun r : ℝ => w r.toNNReal) t)
          (fwdHull (fun r : ℝ => w r.toNNReal) t) lam →
        BHMean.IsSideWord βu Su (fwdMapInv Wr (relClock U s (fun r : ℝ => w r.toNNReal) t))
          (fwdHull Wr (relClock U s (fun r : ℝ => w r.toNNReal) t)) lam →
        BHMean.IsFlowedWord βu β₀ Su S₀ (fwdMapInv Wr (relClock U s (fun r : ℝ => w r.toNNReal) t))
          (fwdHull Wr (relClock U s (fun r : ℝ => w r.toNNReal) t)) →
        (∀ z, v z = G (fwdMap Wr (relClock U s (fun r : ℝ => w r.toNNReal) t) (relMap U s z)) -
          χ * ((logDerivFwd Wr (relClock U s (fun r : ℝ => w r.toNNReal) t) (relMap U s z)).im +
            (relLog U s z).im)) →
        IsRelConfigOff (invHull U s) (relMap U s) (relInv U s) (relLog U s) (relBad U s)
          (fun r : ℝ => w r.toNNReal) Wr (fun r : ℝ => γ r.toNNReal) ηr t
          (relClock U s (fun r : ℝ => w r.toNNReal) t) χ lam β₀ βE βu S₀ SE Su G₀ GE G v := by
  have hs0 : (0 : ℝ) < s := by
    rcases eq_or_lt_of_le (NNReal.coe_nonneg s) with h0 | h0
    · exfalso
      have hs' : s = 0 := by exact_mod_cast h0.symm
      exact GB6.ne_zero_of_mem_H hsH (by rw [hs']; exact hα.1)
    · exact h0
  have hΨ := Q3Rel.isRetainedChartOff_relMap hU hU0 hαr hs0 hNR
  obtain ⟨Wr, ηr, hWr, hWr0, hηr, hu, hK, hKall, hd, htip⟩ :=
    exists_relChain_tip_hull hα hwα hwα0 hs hsH hU hU0 hst₂ hUeq hΨ hγ hw hw0 ht0 htt₁ ht₁
  refine ⟨Wr, ηr, hWr, hWr0, hηr, hu, hK, hKall,
    fun χ lam β₀ βE βu S₀ SE Su G₀ GE G v hG₀ hGE hG hsE hsu hflow hv => ?_⟩
  have hWc : Continuous fun r : ℝ => w r.toNNReal := hw.comp continuous_real_toNNReal
  have hWc0 : (fun r : ℝ => w r.toNNReal) 0 = 0 := by simp [hw0]
  exact Q3Rel.isRelConfigOff_gb6 hU hU0 hαr hs0 hNR hWc hWc0 (isLoewnerTrace_of_isGeneratingTrace hγ) t.2 hWr hWr0
    hηr hu.le hK hd htip hG₀ hGE hG hsE hsu hflow hv

end Sample

/-- **`Q3Kernel.ae_exists_isRelConfigOff_gb6` with every earlier hull identity.** Same proof. -/
theorem ae_exists_isRelConfigOff_gb6_hull {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ} {θ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {Wα W : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α γ : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (s : ℝ≥0) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      ∃ (U : ℝ → ℝ) (t₂ : ℝ), (s : ℝ) < t₂ ∧ (∀ r ∈ Icc (0 : ℝ) t₂, U r = Wα r.toNNReal ω) ∧
        ∀ t t₁ : ℝ≥0, 0 < t → t < t₁ →
          (t₁ : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
            ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) →
          ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
            0 < relClock U s (fun r : ℝ => W r.toNNReal ω) t ∧
            relMap U s '' fwdHull (fun r : ℝ => W r.toNNReal ω) t =
              fwdHull Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t) ∧
            HullsUpTo U s (fun r : ℝ => W r.toNNReal ω) Wr t ∧
            ∀ (χ lam : ℝ) (β₀ βE βu : ℝ → ℝ) (S₀ SE Su : Finset ℝ) (G₀ GE G v : ℂ → ℝ),
              IsBoundedHarmonicExtension β₀ S₀ G₀ → IsBoundedHarmonicExtension βE SE GE →
              IsBoundedHarmonicExtension βu Su G →
              BHMean.IsSideWord βE SE (fwdMapInv (fun r : ℝ => W r.toNNReal ω) t)
                (fwdHull (fun r : ℝ => W r.toNNReal ω) t) lam →
              BHMean.IsSideWord βu Su (fwdMapInv Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t))
                (fwdHull Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t)) lam →
              BHMean.IsFlowedWord βu β₀ Su S₀ (fwdMapInv Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t))
                (fwdHull Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t)) →
              (∀ z, v z = G (fwdMap Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t) (relMap U s z)) -
                χ * ((logDerivFwd Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t) (relMap U s z)).im +
                  (relLog U s z).im)) →
              IsRelConfigOff (invHull U s) (relMap U s) (relInv U s) (relLog U s) (relBad U s)
                (fun r : ℝ => W r.toNNReal ω) Wr (fun r : ℝ => γ ω r.toNNReal) ηr t
                (relClock U s (fun r : ℝ => W r.toNNReal ω) t) χ lam β₀ βE βu S₀ SE Su G₀ GE G v := by
  filter_upwards [GB6.ae_driver_zero_continuousOn hF, hα, ae_trace_ne_zero_of_isFlowLineDriver hκ hκ4 hF, hW]
    with ω hω hαω hNRω hWω hs hsH
  have hs0 : 0 < s := by
    rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ s) with h0 | h0
    · exfalso
      exact GB6.ne_zero_of_mem_H hsH (by rw [← h0]; exact hαω.1)
    · exact h0
  obtain ⟨U, αr, t₂, hst₂, -, hU, hU0, hαr, hUeq, hαeq, -⟩ := exists_frozen_retainedChartOff hαω hω.2 hω.1 hs hs0
    fun v hv hvs => hNRω (α ω) hαω v hv (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hvs) hs)
  have hNR : ∀ v ∈ Ioc (0 : ℝ) s, αr v ≠ 0 := fun v hv => by
    rw [hαeq v ⟨hv.1.le, hv.2.trans hst₂.le⟩]
    refine hNRω (α ω) hαω v.toNNReal (Real.toNNReal_pos.2 hv.1) (lt_of_le_of_lt ?_ hs)
    exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hv.2)
  refine ⟨U, t₂, hst₂, hUeq, fun t t₁ ht0 htt₁ ht₁ => ?_⟩
  exact exists_isRelConfigOff_gb6_hull hαω hω.2 hω.1 hs hsH hU hU0 hαr hNR hst₂ hUeq hWω.2.2 hWω.1 hWω.2.1 ht0 htt₁ ht₁


/-- **`Q3Chain.ae_exists_isRelConfigOff_gb6_words` with every earlier hull identity.** Same proof. -/
theorem ae_exists_isRelConfigOff_gb6_words_hull {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    {θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {Wα W : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α γ : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (b' : ℝ → ℝ) (J' : Finset ℝ) (c : Restart.BoundaryWord) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      ∃ (U : ℝ → ℝ) (t₂ : ℝ), (s : ℝ) < t₂ ∧ (∀ r ∈ Icc (0 : ℝ) t₂, U r = Wα r.toNNReal ω) ∧
        ∀ t t₁ : ℝ≥0, 0 < t → t < t₁ →
          (t₁ : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
            ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) →
          ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
            0 < relClock U s (fun r : ℝ => W r.toNNReal ω) t ∧
            relMap U s '' fwdHull (fun r : ℝ => W r.toNNReal ω) t =
              fwdHull Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t) ∧
            HullsUpTo U s (fun r : ℝ => W r.toNNReal ω) Wr t ∧
            ∀ G₀ GE G v : ℂ → ℝ,
              IsBoundedHarmonicExtension
                (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
                  (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
                (cfJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
                  (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps) G₀ →
              IsBoundedHarmonicExtension (cfFlowedData (16 / κ) b' J' (fun r : ℝ => W r.toNNReal ω) t)
                (cfFlowedJumps b' J' (fun r : ℝ => W r.toNNReal ω) t) GE →
              IsBoundedHarmonicExtension
                (cfFlowedData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
                  (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
                  (relClock U s (fun r : ℝ => W r.toNNReal ω) t))
                (cfFlowedJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
                  (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
                  (relClock U s (fun r : ℝ => W r.toNNReal ω) t)) G →
              (∀ z, v z = G (fwdMap Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t) (relMap U s z)) -
                QuantumZipper.chiC (16 / κ) *
                  ((logDerivFwd Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t) (relMap U s z)).im +
                    (relLog U s z).im)) →
              IsRelConfigOff (invHull U s) (relMap U s) (relInv U s) (relLog U s) (relBad U s)
                (fun r : ℝ => W r.toNNReal ω) Wr (fun r : ℝ => γ ω r.toNNReal) ηr t
                (relClock U s (fun r : ℝ => W r.toNNReal ω) t) (QuantumZipper.chiC (16 / κ))
                (Real.pi / Real.sqrt (16 / κ))
                (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
                  (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
                (cfFlowedData (16 / κ) b' J' (fun r : ℝ => W r.toNNReal ω) t)
                (cfFlowedData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
                  (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
                  (relClock U s (fun r : ℝ => W r.toNNReal ω) t))
                (cfJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
                  (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
                (cfFlowedJumps b' J' (fun r : ℝ => W r.toNNReal ω) t)
                (cfFlowedJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
                  (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
                  (relClock U s (fun r : ℝ => W r.toNNReal ω) t)) G₀ GE G v := by
  filter_upwards [ae_exists_isRelConfigOff_gb6_hull hκ hκ4 hF hα hW s, hW] with ω hω hWω hs hsH
  obtain ⟨U, t₂, hst₂, hUeq, hcfg⟩ := hω hs hsH
  refine ⟨U, t₂, hst₂, hUeq, fun t t₁ ht0 htt₁ ht₁ => ?_⟩
  obtain ⟨Wr, ηr, hWr, hWr0, hηr, hu, hK, hKall, hall⟩ := hcfg t t₁ ht0 htt₁ ht₁
  refine ⟨Wr, ηr, hWr, hWr0, hηr, hu, hK, hKall, fun G₀ GE G v hG₀ hGE hG hv => ?_⟩
  have hWc : Continuous fun r : ℝ => W r.toNNReal ω := hWω.1.comp continuous_real_toNNReal
  have hWc0 : (fun r : ℝ => W r.toNNReal ω) 0 = 0 := by simp [hWω.2.1]
  have hη := isLoewnerTrace_of_isGeneratingTrace hWω.2.2
  exact hall _ _ _ _ _ _ _ _ G₀ GE G v hG₀ hGE hG
    (isSideWord_cfFlowedData hη hWc hWc0 t.2 (16 / κ))
    (isSideWord_cfFlowedData hηr hWr hWr0 hu.le (16 / κ))
    (isFlowedWord_cfFlowedData hηr hWr hWr0 hu (16 / κ)) hv

/-- **`Q3Chain.ae_isRelConfigOff_gb6_flow` with every earlier hull identity.** Same proof. -/
theorem ae_isRelConfigOff_gb6_flow_hull {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    {θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {Wα W : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α γ : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (b' : ℝ → ℝ) (J' : Finset ℝ) (c : Restart.BoundaryWord) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      ∀ t t₁ : ℝ≥0, 0 < t → t < t₁ →
        (t₁ : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
          ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) →
        ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), IsGB6RelChain κ θ c b' J' s t Wα W ζα γ ω Wr ηr ∧
          HullsUpTo (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) Wr t := by
  filter_upwards [ae_exists_isRelConfigOff_gb6_words_hull hκ hκ4 hF hα hW b' J' c s,
    GB6.ae_driver_zero_continuousOn hF] with ω hω hc hs hsH t t₁ ht0 htt₁ ht₁
  obtain ⟨U, t₂, hst₂, hUeq, hcfg⟩ := hω hs hsH
  have hs0 : (0 : ℝ) ≤ s := s.2
  have hUeq' : ∀ r ∈ Icc (0 : ℝ) t₂, U r = Wα r.toNNReal ω := hUeq
  have hUs : ∀ r ∈ Icc (0 : ℝ) s, U r = Wα r.toNNReal ω := fun r hr => hUeq r ⟨hr.1, hr.2.trans hst₂.le⟩
  -- a continuous driver equal to both on `[0, s]`
  have hcs : ContinuousOn (fun r : ℝ => Wα r.toNNReal ω) (Icc 0 (s : ℝ)) := by
    refine hc.2.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
    show ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ζα ω
    refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) hs
  set V : ℝ → ℝ := Ito.clampDrv (fun r : ℝ => Wα r.toNNReal ω) s with hVdef
  have hV : Continuous V := Ito.continuous_clampDrv hs0 hcs
  have hVω : ∀ r ∈ Icc (0 : ℝ) s, Wα r.toNNReal ω = V r := fun r hr =>
    (Ito.clampDrv_eqOn (W := fun r : ℝ => Wα r.toNNReal ω) (T := (s : ℝ)) hr).symm
  have hVU : ∀ r ∈ Icc (0 : ℝ) s, U r = V r := fun r hr => (hUs r hr).trans (hVω r hr)
  have hrB : relBad U s = relBad (fun r : ℝ => Wα r.toNNReal ω) s := by
    rw [relBad_eq_of_eqOn hV hs0 hVU, relBad_eq_of_eqOn hV hs0 hVω]
  have hrM := GB6.relMap_eq_of_eqOn hs0 hUs
  have hrC := GB6.relClock_eq_of_eqOn hs0 hUs (fun r : ℝ => W r.toNNReal ω)
  have hiH := invHull_eq_of_eqOn hs0 hst₂ hUeq'
  have hrI := relInv_eq_of_eqOn hs0 hst₂ hUeq'
  have hrL := relLog_eq_of_eqOn hs0 hUs
  obtain ⟨Wr, ηr, hWr, hWr0, hηr, hu, hK, hKall, hall⟩ := hcfg t t₁ ht0 htt₁ ht₁
  rw [hrM, hrC] at hK
  rw [hrC] at hu
  rw [hrM, hrC, hiH, hrI, hrL, hrB] at hall
  refine ⟨Wr, ηr, ⟨hWr, hWr0, hηr, hu, hK, hall⟩, fun t' ht' => ?_⟩
  have h1 := hKall t' ht'
  rw [hrM, hrC] at h1
  exact h1

/-- **`Q3Chain.ae_eqOn_unionMean_gb6` with every earlier hull identity, for a retained set `A` given through the
unbounded components of `A ∪ {Im ≤ 0}`** (instead of `A` being almost surely an inverted hull, so that `A = ℍ` is
allowed off `{s < ζα}`). Same proof. -/
theorem ae_eqOn_unionMean_gb6_hull {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ} {θ : ℝ}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α γ : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    {b' : ℝ → ℝ} {J' : Finset ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h' : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling (16 / κ) (flowLineXL b' J' 0) (flowLineXR b' J' 0) (flowLineRhoL (16 / κ) b' J' 0 0)
      (flowLineRhoR (16 / κ) b' J' 0 0) P 𝓕 W VL VR B ζ h')
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (cfData (16 / κ) b' J')
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀) P)
    (c : Restart.BoundaryWord) (s t : ℝ≥0) (ht0 : 0 < t)
    (E : Set Ω) {A : Ω → Set ℂ}
    (hAeq : ∀ᵐ ω ∂P, ω ∈ E → (s : ℝ≥0∞) < ζα ω → A ω = invHull (fun r : ℝ => Wα r.toNNReal ω) s)
    (hunbA : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    {K : Ω → Set ℂ} (hKeq : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) t)
    (hAm : Measurable[mΩ, hittingSigma] A) (hKm : Measurable[mΩ, hittingSigma] K)
    (hdA : MeasurableSpace.comap A hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h' u₀) inferInstance) P)
    (hlA : IsLocalSet A (WholeField.centredField h' u₀) P)
    (hlU : IsLocalSet (fun ω => A ω ∪ K ω) (WholeField.centredField h' u₀) P)
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A ω ∪ K ω) (WholeField.centredField h' u₀) P g)
    (hg₁ : IsLocalSetMean A (WholeField.centredField h' u₀) P g₁)
    (hg₂ : IsLocalSetMean K (WholeField.centredField h' u₀) P g₂)
    (hind₁ : ∀ᵐ ω ∂P, ω ∈ E → (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension
          (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
          (cfJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps) G₀ →
        ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
          EqOn (fun z => w₁ z + u₀ z)
            (fun z => G₀ (relMap (fun r : ℝ => Wα r.toNNReal ω) s z) -
              QuantumZipper.chiC (16 / κ) * (relLog (fun r : ℝ => Wα r.toNNReal ω) s z).im)
            (H \ A ω)) :
    ∀ᵐ ω ∂P, ω ∈ E → (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
        ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) →
      ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ) (G : ℂ → ℝ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
        0 < relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t ∧
        relMap (fun r : ℝ => Wα r.toNNReal ω) s '' fwdHull (fun r : ℝ => W r.toNNReal ω) t =
          fwdHull Wr (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t) ∧
        HullsUpTo (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) Wr t ∧
        IsBoundedHarmonicExtension
          (cfFlowedData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
            (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
            (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t))
          (cfFlowedJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
            (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
            (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t)) G ∧
        ∀ wU : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd wU (H \ (A ω ∪ K ω)) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ K ω) →
            g ω φ = ∫ z, wU z * φ z) →
          EqOn (fun z => wU z + u₀ z)
            (fun z => G (fwdMap Wr (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t)
                (relMap (fun r : ℝ => Wα r.toNNReal ω) s z)) -
              QuantumZipper.chiC (16 / κ) *
                ((logDerivFwd Wr (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t)
                  (relMap (fun r : ℝ => Wα r.toNNReal ω) s z)).im +
                  (relLog (fun r : ℝ => Wα r.toNNReal ω) s z).im))
            (H \ (A ω ∪ K ω)) := by
  classical
  -- the per-sample relative chain, chosen
  set Tc : Ω → ℝ≥0∞ := fun ω => firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
    ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) with hTc
  set D : Set Ω := {ω | ω ∈ E ∧ (s : ℝ≥0∞) < ζα ω ∧ α ω s ∈ H ∧ (t : ℝ≥0∞) < Tc ω} with hD
  have hex : ∀ᵐ ω ∂P, ω ∈ D → ∃ p : (ℝ → ℝ) × (ℝ → ℂ), IsGB6RelChain κ θ c b' J' s t Wα W ζα γ ω p.1 p.2 ∧
      HullsUpTo (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) p.1 t := by
    filter_upwards [ae_isRelConfigOff_gb6_flow_hull hκ hκ4 hF hα hW b' J' c s] with ω hω hωD
    obtain ⟨-, hs, hsH, htc⟩ := hωD
    obtain ⟨t₁, htt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 htc
    obtain ⟨Wr, ηr, hR⟩ := hω hs hsH t t₁ ht0 (ENNReal.coe_lt_coe.1 htt₁) ht₁
    exact ⟨(Wr, ηr), hR⟩
  set pr : Ω → (ℝ → ℝ) × (ℝ → ℂ) := fun ω =>
    Classical.epsilon fun p : (ℝ → ℝ) × (ℝ → ℂ) => IsGB6RelChain κ θ c b' J' s t Wα W ζα γ ω p.1 p.2 ∧
      HullsUpTo (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) p.1 t with hpr
  have hprs : ∀ᵐ ω ∂P, ω ∈ D → IsGB6RelChain κ θ c b' J' s t Wα W ζα γ ω (pr ω).1 (pr ω).2 ∧
      HullsUpTo (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) (pr ω).1 t := by
    filter_upwards [hex] with ω hω hωD
    exact Classical.epsilon_spec (p := fun p : (ℝ → ℝ) × (ℝ → ℂ) =>
      IsGB6RelChain κ θ c b' J' s t Wα W ζα γ ω p.1 p.2 ∧
      HullsUpTo (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) p.1 t) (hω hωD)
  -- the three bounded harmonic extensions
  set uc : Ω → ℝ := fun ω => relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t with huc
  set G₀ : Ω → ℂ → ℝ := fun ω => (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
    (flowLineRhoL (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0 0)
    (flowLineRhoR (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0 0)
    (flowLineXL (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0)
    (flowLineXR (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
      (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0)).choose with hG₀
  set GE : Ω → ℂ → ℝ := fun ω => (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
    (flowLineRhoL (16 / κ) b' J' 0 0) (flowLineRhoR (16 / κ) b' J' 0 0)
    (fun i => Exist.StagedLaw.markPosL (fun r : ℝ => W r.toNNReal ω) t (flowLineXL b' J' 0 i))
    (fun j => Exist.StagedLaw.markPos (fun r : ℝ => W r.toNNReal ω) t (flowLineXR b' J' 0 j))).choose with hGE
  set G : Ω → ℂ → ℝ := fun ω => (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
    (flowLineRhoL (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0 0)
    (flowLineRhoR (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0 0)
    (fun i => Exist.StagedLaw.markPosL (pr ω).1 (uc ω)
      (flowLineXL (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0 i))
    (fun j => Exist.StagedLaw.markPos (pr ω).1 (uc ω)
      (flowLineXR (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
        (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0 j))).choose with hG
  have hG₀s : ∀ ω, IsBoundedHarmonicExtension
      (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
      (cfJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps) (G₀ ω) :=
    fun ω => by
      rw [coe_cfJumps]
      exact (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData _ _ _ _ _).choose_spec
  have hGEs : ∀ ω, IsBoundedHarmonicExtension (cfFlowedData (16 / κ) b' J' (fun r : ℝ => W r.toNNReal ω) t)
      (cfFlowedJumps b' J' (fun r : ℝ => W r.toNNReal ω) t) (GE ω) := fun ω => by
    rw [cfFlowedJumps, flowedJumps, coe_initJumps]
    exact (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData _ _ _ _ _).choose_spec
  have hGs : ∀ ω, IsBoundedHarmonicExtension
      (cfFlowedData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps
        (pr ω).1 (uc ω))
      (cfFlowedJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps
        (pr ω).1 (uc ω)) (G ω) := fun ω => by
    rw [cfFlowedJumps, flowedJumps, coe_initJumps]
    exact (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData _ _ _ _ _).choose_spec
  -- the candidate mean
  set v : Ω → ℂ → ℝ := fun ω z => G ω (fwdMap (pr ω).1 (uc ω) (relMap (fun r : ℝ => Wα r.toNNReal ω) s z)) -
    QuantumZipper.chiC (16 / κ) * ((logDerivFwd (pr ω).1 (uc ω) (relMap (fun r : ℝ => Wα r.toNNReal ω) s z)).im +
      (relLog (fun r : ℝ => Wα r.toNNReal ω) s z).im) with hv
  -- the configuration on `D`
  have hcfg : ∀ᵐ ω ∂P, ω ∈ D → IsRelConfigOff (A ω)
      (relMap (fun r : ℝ => Wα r.toNNReal ω) s) (relInv (fun r : ℝ => Wα r.toNNReal ω) s)
      (relLog (fun r : ℝ => Wα r.toNNReal ω) s) (relBad (fun r : ℝ => Wα r.toNNReal ω) s)
      (fun r : ℝ => W r.toNNReal ω) (pr ω).1 (fun r : ℝ => γ ω r.toNNReal) (pr ω).2 ((fun _ : Ω => (t : ℝ)) ω)
      (uc ω) (QuantumZipper.chiC (16 / κ)) (Real.pi / Real.sqrt (16 / κ))
      (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
      (cfFlowedData (16 / κ) b' J' (fun r : ℝ => W r.toNNReal ω) t)
      (cfFlowedData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
        (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps (pr ω).1 (uc ω))
      (cfJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
      (cfFlowedJumps b' J' (fun r : ℝ => W r.toNNReal ω) t)
      (cfFlowedJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
        (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps (pr ω).1 (uc ω))
      (G₀ ω) (GE ω) (G ω) (v ω) := by
    filter_upwards [hprs, hAeq] with ω hω hAω hωD
    have hc := (hω hωD).1.2.2.2.2.2
    rw [← hAω hωD.1 hωD.2.1] at hc
    exact hc (G₀ ω) (GE ω) (G ω) (v ω) (hG₀s ω) (hGEs ω) (hGs ω) fun z => rfl
  -- locality and topology of the counterflow hull
  obtain ⟨hX, hker⟩ := hC.2.2.2
  have hτζ : ∀ᵐ ω ∂P, ((((fun _ : Ω => ((t : ℝ≥0) : WithTop ℝ≥0)) ω) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact ENNReal.coe_lt_top
  have hK' : IsLocalSet (fun ω => fwdHull (fun r : ℝ => W r.toNNReal ω) t) h' P := by
    have h1 := (hker (fun _ => ((t : ℝ≥0) : WithTop ℝ≥0)) (isStoppingTime_const _ t) hτζ).1
    simpa only [WithTop.untopD_coe] using h1
  have hlK : IsLocalSet K (WholeField.centredField h' u₀) P := by
    refine Coupling.IsLocalSet.congr_set
      (WholeField.IsLocalSet.sub_dist hK' (WholeField.isHarmonicDistOn_smoothDist hu₀.1)) ?_
    filter_upwards [hKeq] with ω hω
    simp only [hω]
  have hunbK : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (K ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (K ω)) z) := by
    filter_upwards [hKeq, hW] with ω hω hWω
    rw [hω]
    exact Sec5.GlueCond.not_isBounded_lowerUnion_of_isHPHull
      (isHPHull_fwdHull (hWω.1.comp continuous_real_toNNReal) t.coe_nonneg)
  -- the two partial means
  have hind₂ := ae_eqOn_cfMean (by positivity) hC hζ hu₀ hh0 t hKeq hKm hg₂
  have hmain := ae_eqOn_unionMean_of_relConfigOff_ver hh0 hu₀.1 hu₀.2.1 hAm hKm hdA hlA hlK hlU hunbA hunbK hg hg₁
    hg₂ (D := D) (by filter_upwards [hKeq] with ω hω _ using hω) hcfg
    (by
      filter_upwards [hind₁] with ω hω hωD w₁ hw₁ hr₁
      exact hω hωD.1 hωD.2.1 hωD.2.2.1 (G₀ ω) (hG₀s ω) w₁ hw₁ hr₁)
    (by
      filter_upwards [hind₂, hW] with ω hω hWω hωD w₂ hw₂ hr₂
      exact hω hWω.1 hWω.2.1 (GE ω) (hGEs ω) w₂ hw₂ hr₂)
  filter_upwards [hmain, hprs] with ω hω hpω hE hs hsH htc
  have hωD : ω ∈ D := ⟨hE, hs, hsH, htc⟩
  obtain ⟨⟨h1, h2, h3, h4, h5, -⟩, h6⟩ := hpω hωD
  exact ⟨(pr ω).1, (pr ω).2, G ω, h1, h2, h3, h4, h5, h6, hGs ω, fun wU hwU hrU => hω hωD wU hwU hrU⟩

end InteractingSLE.Supp8.GB6LMean
