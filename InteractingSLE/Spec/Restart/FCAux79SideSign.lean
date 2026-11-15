/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCAux79SideSignLimit
import InteractingSLE.Spec.Restart.FCAux79SideSignCorner

/-!
# The orientation of the new piece, IV: `IsFCSideSign`, and Aux. 79 at the later lines unconditionally

Packet PROVE-FCSIDE (spec p. 290). **`IsFCLine.isFCSideSign`** proves the deterministic orientation statement
`FCAux79.IsFCSideSign` at every reading `IsFCLine` of the first-contact continuation, and the consumers of
PROVE-FCAUX79 lose their hypothesis `hsign`:

* `isFCSideLimit_of_flowLines`: the new-piece heights `IsFCSideLimit` from the named inputs of the glued (R1);
* **`ae_chartTransport_lineMean_flowLines`**: Aux. 79's line mean identity `hmean` at every later line
  `(s₀ + t, t₀)` for Lemma 7.8's word, from the setting of `FirstContactWordKernelStatement` and the named inputs
  of the glued (R1) only.

## Proof of `isFCSideSign`

Let `Φ_Q(y) = γ(σ)`, `ψ(γ(σ)) = η₁(s)`, and the stop `s < q < s₀ + t` with `η₁(q) ∈ ℍ`. The chart path and the new
piece are parametrised in the same order (`IsFCLine.lt_of_inv_eq`), so `η₁(q) = ψ(γ(σ_q))` with `σ < σ_q`, and the
capacity `σ_q` is itself a later line, at the time `q` (`IsFCLine.exists_restrict`).
* **Sign.** The transition `f_{σ_q} ∘ f_Q⁻¹` carries `y` to a real `ξ` of the same sign with `Φ_{σ_q}(ξ) = γ(σ)`
  (`exists_transition`). The composed chart at `Q` is the composed chart at `σ_q` after this transition (the flow
  property of the inverse maps), so the single-path chart value `y'` is the limit at `ξ` of the relative map of the
  line `σ_q` (the composed chart and the single-path chart at the same time `q`), which has the sign of `ξ`
  (`IsFCLine.sign_of_tendsto_rel`; the segment between `0` and `ξ` goes onto the chart path: `mem_γ_of_pos`,
  `mem_γ_of_neg`, `le_rightImg_of_mem_γ`, `neg_rightImg_le_of_mem_γ`).
* **Real points.** If `η₁(s)` is real, so is `γ(σ)` (`ψ` maps `ℍ` into `ℍ`). For `0 < y < R̃` it is left of `0`
  (`IsFCLine.re_neg_of_real`), not in `[L, 0]` (whose image is in `K`, which the new piece misses), so `η₁(s) =
  ψ(γ(σ)) < a ≤ x₂ < x₁`. Mirror for `L̃ < y < 0`: right of `R`, so `η₁(s) > b ≥ x₁`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open QuantumZipper.RS (shiftDrive)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE

namespace Restart.FCAux79

open Sec7 Sec7.SideHeightBox Supp7 LocalSets Sec6

universe u

section Path

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω} {ω : Ω} {x₁ x₂ : ℝ} {t : ℝ≥0}
  {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {ζc : ℝ≥0∞} {Q : ℝ≥0}

/-- **The orientation of approaches to the new piece** (`IsFCSideSign`) at every reading of the first-contact
continuation at a later line. -/
theorem IsFCLine.isFCSideSign (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) (hd : d.IsMeasGood) (hx : x₂ < x₁) :
    IsFCSideSign d ω x₁ t W γ Q := by
  intro W₁ hg₁ hWc₁ hW0₁ y σ hσ hσe s q hse hsq hqt hqH U hU y' hy'
  set w' : ℝ → ℝ := fun r => W r.toNNReal with hw'
  have hE := hl.mem_E
  have hsle : s ≤ d.s₀ ω + t := (hsq.trans hqt).le
  -- the time of the approached point is after the contact
  obtain ⟨u, hu, hue⟩ := hl.exists_inv_γ_eq hσ.2.le
  have hus : u = s := hl.injOn₁ ⟨zero_le, hu.2⟩ ⟨zero_le, hsle⟩ (hue.symm.trans hse)
  have hs₀ : d.s₀ ω < s := by
    refine lt_of_le_of_ne (hus ▸ hu.1) fun h => ?_
    have h1 : d.inv ω (γ σ) = d.inv ω (γ 0) := by rw [hse, ← h, hl.inv_γ_zero hd]
    exact (ne_of_gt hσ.1) (hl.injOn_inv_γ hd ⟨zero_le, hσ.2.le⟩ ⟨zero_le, zero_le⟩ h1)
  -- the capacity of the stop
  have hqI : q ∈ Icc (d.s₀ ω) (d.s₀ ω + t) := ⟨(hs₀.trans hsq).le, hqt.le⟩
  have hqmem : d.η₁ ω q ∈ (fun s => d.inv ω (γ s)) '' Icc 0 Q := by rw [hl.image]; exact ⟨q, hqI, rfl⟩
  obtain ⟨σq, hσq, hσqe⟩ := hqmem
  have hσσq : σ < σq := by
    refine lt_of_not_ge fun hle => ?_
    rcases eq_or_lt_of_le hle with h | h
    · rw [h] at hσqe
      have := hl.injOn₁ ⟨zero_le, hsle⟩ ⟨zero_le, hqt.le⟩ (hse.symm.trans hσqe)
      exact (ne_of_lt hsq) this
    · have := hl.lt_of_inv_eq hd hσ.2.le h hqI ⟨hs₀.le, hsle⟩ hσqe hse
      exact absurd hsq (not_lt.2 this.le)
  have hσq0 : 0 < σq := lt_of_le_of_lt zero_le hσσq
  -- the later line at the stop
  obtain ⟨t', ht't, ht'e, hl'⟩ := hl.exists_restrict hd hσq0 hσq.2
  have hqt' : d.s₀ ω + t' = q :=
    hl.injOn₁ ⟨zero_le, add_le_add_right ht't _⟩ ⟨zero_le, hqt.le⟩ (ht'e.symm.trans hσqe)
  -- the transition from `Q` to `σq`
  obtain ⟨ξ, hχ, hΦξ, hξpos, hξneg⟩ := exists_transition hl.gen hl.cont hl.zero hl.inj hσq0 hσq.2 hl.lt hσσq hσe
  -- the relative map of the line `σq`
  have hqζ : ((d.s₀ ω + t' : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω := by
    rw [hqt']; exact lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hqt) hl.le_life
  have htip : d.η₁ ω (d.s₀ ω + t') ∈ H := by rw [hqt']; exact hqH
  have hξγ : extendFrom H (fwdMapInv w' σq) ξ ∈ γ '' Icc 0 σq := ⟨σ, ⟨zero_le, hσσq.le⟩, hΦξ.symm⟩
  obtain ⟨a, ha, -⟩ := hl'.exists_tendsto_rel hd hg₁ hWc₁ hW0₁ hqζ hξγ
  have hseg : ∀ c ∈ uIcc 0 ξ, extendFrom H (fwdMapInv w' σq) c ∈ γ '' Icc 0 σq := by
    intro c hc
    rcases eq_or_ne c 0 with h0 | h0
    · rw [h0, ofReal_zero, hl'.isChart.tip]; exact ⟨σq, ⟨zero_le, le_rfl⟩, rfl⟩
    rcases eq_or_ne c ξ with hcξ | hcξ
    · rw [hcξ]; exact hξγ
    rcases Set.mem_uIcc.1 hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hl'.mem_γ_of_pos (lt_of_le_of_ne h1 (Ne.symm h0))
        (lt_of_lt_of_le (lt_of_le_of_ne h2 hcξ) (hl'.le_rightImg_of_mem_γ hξγ))
    · exact hl'.mem_γ_of_neg (lt_of_le_of_lt (hl'.neg_rightImg_le_of_mem_γ hξγ) (lt_of_le_of_ne h1 (Ne.symm hcξ)))
        (lt_of_le_of_ne h2 h0)
  have hsgn := hl'.sign_of_tendsto_rel hd hg₁ hWc₁ hW0₁ hqζ htip hseg ha
  -- the given limit is the limit of the relative map
  have hflow : ∀ z ∈ H, fwdMapInv w' Q z = fwdMapInv w' σq (fwdMap w' σq (fwdMapInv w' Q z)) := by
    intro z hz
    have hu0 : (0 : ℝ) ≤ (Q : ℝ) - σq := sub_nonneg.2 (NNReal.coe_le_coe.2 hσq.2)
    have he : (σq : ℝ) + ((Q : ℝ) - σq) = Q := by ring
    have h1 := QuantumZipper.RS.fwdMapInv_add_shift hl.continuous_rdrv hl.rdrv_zero σq.coe_nonneg hu0 hz
    have h2 := QuantumZipper.RS.fwdMapInv_shift_eq hl.continuous_rdrv hl.rdrv_zero σq.coe_nonneg hu0 hz
    rw [he] at h1 h2
    rw [h2] at h1
    exact h1
  have hya : y' = a := by
    have hT : Tendsto (fun z => fwdMap (fun r : ℝ => W₁ r.toNNReal) q
        (d.inv ω (fwdMapInv w' Q z) - x₁)) U (𝓝 (a : ℂ)) := by
      refine (ha.comp (hχ.mono_left hU)).congr' ?_
      filter_upwards [hU self_mem_nhdsWithin] with z hz
      have hqr : ((d.s₀ ω : ℝ) + t') = (q : ℝ) := by rw [← NNReal.coe_add, hqt']
      simp only [Function.comp_apply]
      rw [hqr, ← hflow z hz]
    exact_mod_cast tendsto_nhds_unique hy' hT
  -- the real points
  have hγim : (d.η₁ ω s).im = 0 → (γ σ).im = 0 := by
    intro hsim
    rcases mem_H_or_im_eq_zero (hl.γ_mem_Hbar hσ.2.le) with h | h
    · exfalso
      have h1 := ((hl.isDomChart hd).bijOn_inv.mapsTo h).1
      rw [hse] at h1
      exact absurd hsim (ne_of_gt h1)
    · exact h
  have hK := hl.notMem_K hd hs₀ hsle
  have hψw : d.inv ω (((γ σ).re : ℝ) : ℂ) = d.η₁ ω s ∨ (γ σ).im ≠ 0 := by
    by_cases h : (γ σ).im = 0
    · left; rw [ofReal_re_of_im h]; exact hse
    · right; exact h
  refine ⟨fun hy0 hyR => ⟨?_, ?_⟩, fun hy0 hyL => ⟨?_, ?_⟩⟩
  · rw [hya]; exact hsgn.1 (hξpos hy0)
  · rintro ⟨him, hre⟩
    have hsim : (d.η₁ ω s).im = 0 := by simpa using him
    have hγσ := hγim hsim
    have hneg := hl.re_neg_of_real hd hσ.1 hσ.2.le hy0 hyR hσe hγσ
    have hψ : d.inv ω (((γ σ).re : ℝ) : ℂ) = d.η₁ ω s := hψw.resolve_right fun h => h hγσ
    have hwL : (γ σ).re < d.wordL ω := by
      by_contra hle
      push Not at hle
      exact hK (hψ ▸ hd.inv_mem_K_of_mem_Icc hE hle (hneg.le.trans (hd.wordR_nonneg hE)))
    have h1 := (hd.inv_of_lt_wordL hE hwL).1
    have hx₂K : ((x₂ : ℝ) : ℂ) ∈ d.K ω := by
      rw [hl.K_eq]; exact Or.inr ⟨0, ⟨le_rfl, zero_le⟩, IsPathGood.zero hl.path₂⟩
    have h2 := hd.baseL_le hx₂K
    rw [hψ] at h1
    rw [sub_re, ofReal_re] at hre
    linarith
  · rw [hya]; exact hsgn.2 (hξneg hy0)
  · rintro ⟨him, hre⟩
    have hsim : (d.η₁ ω s).im = 0 := by simpa using him
    have hγσ := hγim hsim
    have hpos := hl.re_pos_of_real hd hσ.1 hσ.2.le hyL hy0 hσe hγσ
    have hψ : d.inv ω (((γ σ).re : ℝ) : ℂ) = d.η₁ ω s := hψw.resolve_right fun h => h hγσ
    have hwR : d.wordR ω < (γ σ).re := by
      by_contra hle
      push Not at hle
      exact hK (hψ ▸ hd.inv_mem_K_of_mem_Icc hE ((hd.wordL_nonpos hE).trans hpos.le) hle)
    have h1 := (hd.inv_of_wordR_lt hE hwR).1
    have hx₁K : ((x₁ : ℝ) : ℂ) ∈ d.K ω := by
      rw [hl.K_eq]; exact Or.inl ⟨0, ⟨le_rfl, zero_le⟩, IsPathGood.zero hl.path₁⟩
    have h2 := hd.le_baseR hx₁K
    rw [hψ] at h1
    rw [sub_re, ofReal_re] at hre
    linarith

end Path

section Main

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The heights on the new piece** (`IsFCSideLimit`, spec p. 290) in the setting of
`FirstContactWordKernelStatement`, from the named inputs of the glued (R1) alone (`isFCSideLimit_of_sign` with
`IsFCLine.isFCSideSign`). -/
theorem isFCSideLimit_of_flowLines (hL75 : Theorem15.Lemma75Statement.{u}) (hL77 : Supp10.Lemma77Statement.{u})
    (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    IsFCSideLimit κ θ₁ x₁ x₂ P h η₁ η₂ ζ₁ ζ₂ u₀ d :=
  isFCSideLimit_of_sign hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀
    fun _ _ _ _ _ _ hl => hl.isFCSideSign hd hx

/-- **Aux. lemma 79 at the later first-contact lines, K2's `hmean`, for Lemma 7.8's word — unconditionally**
(`ae_chartTransport_lineMean_word` with the orientation `IsFCLine.isFCSideSign`): in the setting of
`FirstContactWordKernelStatement`, from the named inputs of the glued (R1) (Lemma 7.5, Lemma 7.7, Aux. 56 at first
entrances) only. -/
theorem ae_chartTransport_lineMean_flowLines (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps) (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y)
    (m : ℕ) (t : ℝ≥0) {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hm₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (hag₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (ζ₁ ω) s))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (ζ₂ ω) s)) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (shUnion ηc₁ ηc₂ t 0) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ meetBox d m → d.s₀ ω + t < m →
      ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0), IsFCLine d ω x₁ x₂ t W γ ζc Q →
      ∀ {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ),
      (∀ i, xL i ≤ 0) → (∀ j, 0 ≤ xR j) →
      (∃ S : Set ℝ, S.Finite ∧ ∀ x ∉ S, forceBoundaryData κ ρL ρR xL xR x =
        (d.word c₀ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ) ω).fn x +
          θ₁ * QuantumZipper.chiC κ) →
      ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ fwdHull (fun s : ℝ => W s.toNNReal) Q →
        Chart.chartTransport (hd.isConformal_chart ω) 1 (θ₁ * QuantumZipper.chiC κ) (QuantumZipper.chiC κ)
            (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
          ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal) Q
            (LocalExt.bheAt κ ρL ρR (flowL W Q xL) (flowR W Q xR)) z * ψ z :=
  ae_chartTransport_lineMean_word hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀ hc₀ hc₀J hc₀b
    (fun _ _ _ _ _ _ hl => hl.isFCSideSign hd hx) m t hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg

end Main

end Restart.FCAux79

end InteractingSLE
