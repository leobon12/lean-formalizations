/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6GlueTrace

/-!
# Proposition GB6: the conditional-law half from its hull-level form

Packet PROVE-GB6C. Supplement §8.6, Proposition GB6 (`source/spec/p481-528.md` L929–L975, pp. 518–520). GB6B
stated GB6's conditional-law half as the restart carrier `GB6RestartStatement` (`GB6Contact.lean`) and proved the
first-contact assertion from it. Its pathwise clause `IsGB6ChartContinuation` asks for a clock `ℓ` from `[0, ∞)` onto
the pre-contact interval `[0, T_c)` and the identification `η(ℓ(u)) = c_U⁻¹(Γ(u))` at interior chart times.

This file proves that clause **deterministically** from hull-level information about the relative exploration:

* the relative driver `W'` generates the chart images `Ψ(K'_t)` of the counterflow hulls in the intrinsic relative
  clock `a(t) = hcap(Ψ(K'_t))/2` (`Ψ = relMap`, GB6's fixed-hull restriction);
* the relative lifetime is infinite (`a` is unbounded before `T_c`);
* `Γ` is a complete continuous generating trace of `W'`.

The ingredients are the disjoint closed hulls before the first contact (`GB6Disjoint.lean`), the glued relative
chain (`GB6Glue.lean`), the chart trace identification (`GB6GlueTrace.lean`), the inverse of the exhausting clock
(`Sec5.CrossRestart.clockInv`), and the transfer from the flow driver (continuous only before the flow's lifetime) to
a driver frozen after a later time (`frozenDrive`).

## Main results

* `firstContactTime_pos`: the first contact of the physical counterflow (started at `∞`) with a compact set is
  positive;
* **`isGB6ChartContinuation_of_relHulls`** (one realization);
* **`GB6RelativeLawStatement`** (named, hull-level form of GB6's conditional-law half) and
  **`gb6RestartStatement_of_relativeLaw`**: `GB6RelativeLawStatement → GB6RestartStatement`; hence GB6's first-contact
  assertion and final assertion from it (`gb6FirstContactStatement_of_relativeLaw`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Supp8

namespace GB6

/-! ### The first contact is positive -/

/-- **The first contact of the physical counterflow with a compact set is positive**: `η = R̂ ∘ γ` starts at `∞`. -/
theorem firstContactTime_pos {γ : ℝ≥0 → ℂ} (hγ : ContinuousAt γ 0) (hγ0 : γ 0 = 0) {A : Set ℂ}
    (hA : Bornology.IsBounded A) :
    0 < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun z : ℂ => (z : OnePoint ℂ)) '' A) := by
  obtain ⟨M, hM⟩ := hA.subset_closedBall 0
  have hM1 : (0 : ℝ) < 1 / (|M| + 1) := by positivity
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ≥0), ‖γ t‖ < 1 / (|M| + 1) := by
    have hlim : Tendsto (fun t => ‖γ t‖) (𝓝 0) (𝓝 0) := by
      have := (continuous_norm.tendsto (γ 0)).comp hγ
      rwa [hγ0, norm_zero] at this
    exact hlim.eventually (gt_mem_nhds hM1)
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hev
  have hε' : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  refine lt_of_lt_of_le hε' (le_iInf₂ fun t ht => ?_)
  by_contra hlt
  push Not at hlt
  have htε : dist t 0 < ε := by
    rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg t)]
    have := (ENNReal.lt_ofReal_iff_toReal_lt (by simp)).1 hlt
    simpa using this
  have hsmall := hεb htε
  obtain ⟨z, hzA, hz⟩ := ht
  simp only at hz
  by_cases h0 : γ t = 0
  · simp only [h0, sphereInv_coe, ↓reduceIte] at hz
    exact OnePoint.coe_ne_infty z hz
  · rw [sphereInv_coe_of_ne h0] at hz
    have hzeq : z = -(γ t)⁻¹ := OnePoint.coe_injective hz
    have hzM := mem_closedBall_zero_iff.1 (hM hzA)
    rw [hzeq, norm_neg, norm_inv] at hzM
    have hpos : 0 < ‖γ t‖ := norm_pos_iff.2 h0
    have h1 : 1 ≤ |M| * ‖γ t‖ := by
      have := mul_le_mul_of_nonneg_right (hzM.trans (le_abs_self M)) hpos.le
      rwa [inv_mul_cancel₀ hpos.ne'] at this
    have h2 : |M| * ‖γ t‖ < |M| * (1 / (|M| + 1)) + 1 / (|M| + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hsmall.le (abs_nonneg M), abs_nonneg M]
    have h3 : |M| * (1 / (|M| + 1)) + 1 / (|M| + 1) = 1 := by
      field_simp
    linarith

/-! ### Transfer to a frozen flow driver -/

section Frozen

variable {U U' : ℝ → ℝ} {σ t₂ : ℝ}

theorem relMap_eq_of_eqOn (hσ : 0 ≤ σ) (h : ∀ r ∈ Icc (0 : ℝ) σ, U r = U' r) : relMap U σ = relMap U' σ := by
  funext w
  rw [relMap, relMap, fwdMap_eq_of_eqOn hσ h]

theorem relClock_eq_of_eqOn (hσ : 0 ≤ σ) (h : ∀ r ∈ Icc (0 : ℝ) σ, U r = U' r) (W : ℝ → ℝ) :
    relClock U σ W = relClock U' σ W := by
  funext t
  rw [relClock, relClock, relMap_eq_of_eqOn hσ h]

theorem ownComponentChart_inv_eq_of_eqOn (hσ : 0 ≤ σ) (hσt₂ : σ < t₂) (h : ∀ r ∈ Icc (0 : ℝ) t₂, U r = U' r) :
    (ownComponentChart U σ).2.1 = (ownComponentChart U' σ).2.1 := by
  funext w
  show QuantumZipper.fwdMapInv U σ (-w⁻¹) = QuantumZipper.fwdMapInv U' σ (-w⁻¹)
  rw [fwdMapInv_eq_of_eqOn hσ hσt₂ h]

end Frozen

/-! ### The pathwise clause from the hull-level relative exploration -/

/-- **GB6's pathwise clause from the relative exploration** (one realization). In the original flow chart, let `α` be
the generating trace of the flow driver `wα` with an interior tip `α(s) ∈ ℍ` before its lifetime, `γ` a complete
continuous generating trace of the counterflow driver `w` (physical counterflow `η = R̂ ∘ γ`), and `W'` a continuous
driver with complete continuous generating trace `Γ`. If `W'` generates the chart images `Ψ(K'_t)` of the counterflow
hulls in the relative clock `a(t) = hcap(Ψ(K'_t))/2` at every `t` before the first contact `T_c` of `η` with
`α([0, s])`, and `a` is unbounded before `T_c` (infinite relative lifetime), then `IsGB6ChartContinuation` holds:
`ℓ = a⁻¹` is a continuous strictly increasing clock from `[0, ∞)` onto `[0, T_c)` and `η(ℓ(u)) = c_U⁻¹(Γ(u))`
whenever `Γ(u) ∈ ℍ`. -/
theorem isGB6ChartContinuation_of_relHulls {κ : ℝ} {h H' : LQGMetric.DistOn upperHalfPlaneOpens}
    {wα w W' : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {α γ Γ : ℝ≥0 → ℂ} {s : ℝ≥0}
    (htr : IsChartTransport (ownComponentChart (fun r : ℝ => wα r.toNNReal) s) (-1)
      (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) h H')
    (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα}) (hwα0 : wα 0 = 0)
    (hs : (s : ℝ≥0∞) < Tα) (hsH : α s ∈ H)
    (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0)
    (hΓ : IsGeneratingTrace W' ⊤ Γ) (hW' : Continuous W') (hW'0 : W' 0 = 0)
    (hunb : ∀ u : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) ∧
      u ≤ relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t)
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) →
      QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal)
          (relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t) =
        relMap (fun r : ℝ => wα r.toNNReal) s '' QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) t) :
    IsGB6ChartContinuation κ h H' (fun t => sphereInv (γ t : OnePoint ℂ)) wα α s Γ := by
  set Tc := firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)
    with hTcdef
  set Ur : ℝ → ℝ := fun r => wα r.toNNReal with hUr
  set Wr : ℝ → ℝ := fun r => w r.toNNReal with hWr
  have hs0 : (0 : ℝ) < s := by
    rcases eq_or_lt_of_le (NNReal.coe_nonneg s) with h0 | h0
    · exfalso
      have hs' : s = 0 := by exact_mod_cast h0.symm
      exact ne_zero_of_mem_H hsH (by rw [hs']; exact hα.1)
    · exact h0
  -- the flow driver frozen after a time `t₂ ∈ (s, Tα)`
  obtain ⟨t₂, hst₂, ht₂⟩ := exists_real_btwn_of_lt hs
  set U' : ℝ → ℝ := frozenDrive wα t₂ with hU'def
  have hU' : Continuous U' := continuous_frozenDrive_of_lt hwα ht₂
  have ht₂0 : (0 : ℝ) ≤ t₂ := le_trans (NNReal.coe_nonneg s) hst₂.le
  have hU'0 : U' 0 = 0 := by rw [hU'def, frozenDrive_zero ht₂0, hwα0]
  have hagree : ∀ r ∈ Icc (0 : ℝ) t₂, Ur r = U' r := fun r hr => (frozenDrive_eq hr).symm
  have hagree_s : ∀ r ∈ Icc (0 : ℝ) s, Ur r = U' r := fun r hr => hagree r ⟨hr.1, hr.2.trans hst₂.le⟩
  have hrel : relMap Ur s = relMap U' s := relMap_eq_of_eqOn (NNReal.coe_nonneg s) hagree_s
  have hclock : relClock Ur s Wr = relClock U' s Wr := relClock_eq_of_eqOn (NNReal.coe_nonneg s) hagree_s Wr
  have hhull : QuantumZipper.fwdHull Ur s = QuantumZipper.fwdHull U' s :=
    fwdHull_eq_of_eqOn (NNReal.coe_nonneg s) hst₂ hagree
  have hinv : (ownComponentChart Ur s).2.1 = (ownComponentChart U' s).2.1 :=
    ownComponentChart_inv_eq_of_eqOn (NNReal.coe_nonneg s) hst₂ hagree
  have htip : Tendsto (QuantumZipper.fwdMapInv U' s) (𝓝[H] 0) (𝓝 (α s)) := by
    have h1 := IsGeneratingTrace.tendsto_fwdMapInv_tip hα hwα hwα0 hs
    have h2 : QuantumZipper.fwdMapInv Ur s = QuantumZipper.fwdMapInv U' s :=
      fwdMapInv_eq_of_eqOn (NNReal.coe_nonneg s) hst₂ hagree
    rw [← h2]
    exact h1
  -- disjoint closed hulls before the contact
  have hd : ∀ T : ℝ≥0, (T : ℝ≥0∞) < Tc → Disjoint (closure (QuantumZipper.fwdHull U' s))
      (closure ((fun w : ℂ => -w⁻¹) '' QuantumZipper.fwdHull Wr T)) := fun T hT => by
    rw [← hhull]
    exact disjoint_closure_fwdHull_of_lt_firstContactTime hα hwα hwα0 hγ hw.continuousOn hw0 hs
      ENNReal.coe_lt_top hT
  -- the first contact is positive
  have hγc : Continuous γ := by
    have := hγ.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have hTc : 0 < Tc := by
    have hk : IsCompact (α '' Icc 0 s) := isCompact_Icc.image_of_continuousOn
      (hα.2.1.mono fun t ht => le_trans (by exact_mod_cast ht.2) hs.le)
    have := firstContactTime_pos hγc.continuousAt hγ.1 hk.isBounded
    rwa [image_image] at this
  have hγK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → IsFilling (QuantumZipper.fwdHull Wr t) (γ '' Icc 0 t) :=
    fun t _ => hγ.2.2 t ENNReal.coe_lt_top
  obtain ⟨-, -, ha0, hsm, hac, -, -⟩ := exists_glued_relChain hw hw0 hU' hU'0 hs0 htip hTc hd hγK
  have hexh : Sec5.CrossRestart.IsExhaustingClock (fun t : ℝ≥0 => relClock U' s Wr t) Tc := by
    refine ⟨hTc, ha0, hsm, hac, fun u => ?_⟩
    obtain ⟨t, ht, hu⟩ := hunb u
    exact ⟨t, ht, by rw [← hclock]; exact hu⟩
  have hnn : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ relClock U' s Wr t := fun t ht => hexh.nonneg ht
  have hK' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
      QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (relClock U' s Wr t) =
        relMap U' s '' QuantumZipper.fwdHull Wr t := fun t ht => by
    rw [← hclock, ← hrel]; exact hK t ht
  have hdom : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
      ∀ x ∈ QuantumZipper.fwdHull Wr t, -x⁻¹ ∉ QuantumZipper.fwdHull U' s := fun t ht x hx hxK =>
    Set.disjoint_left.1 (hd t ht) (subset_closure hxK) (subset_closure ⟨x, hx, rfl⟩)
  have hγdom : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → γ t ∈ H → -(γ t)⁻¹ ∉ QuantumZipper.fwdHull U' s := by
    intro t ht hγt
    obtain ⟨T', htT', hT'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    have hmem : γ t ∈ QuantumZipper.fwdHull Wr T' :=
      Sec5.CrossRestart.inter_H_subset_of_isFilling (hγ.2.2 T' ENNReal.coe_lt_top)
        ⟨⟨t, ⟨zero_le, (ENNReal.coe_lt_coe.1 htT').le⟩, rfl⟩, hγt⟩
    exact hdom T' hT' _ hmem
  refine ⟨htr, Sec5.CrossRestart.clockInv (fun t : ℝ≥0 => relClock U' s Wr t) Tc, hexh.continuous_clockInv,
    hexh.strictMono_clockInv, ?_, fun u hu => ?_⟩
  · rw [← image_univ]; exact hexh.image_clockInv
  · obtain ⟨ht, hat⟩ := hexh.clockInv_spec u
    set t := Sec5.CrossRestart.clockInv (fun t : ℝ≥0 => relClock U' s Wr t) Tc u with htdef
    have hnn' : (relClock U' s Wr t).toNNReal = u := by
      have hat' : relClock U' s Wr t = u := hat
      rw [hat', Real.toNNReal_coe]
    have hΓH : Γ (relClock U' s Wr t).toNNReal ∈ H := by rw [hnn']; exact hu
    obtain ⟨hγH, hΓeq⟩ := relTrace_eq hw hw0 hU' hU'0 (NNReal.coe_nonneg s) hγ hW' hW'0 hΓ hsm hnn hK' hdom hγdom ht hΓH
    have hΓeq' : Γ u = relMap U' s (γ t) :=
      calc Γ u = Γ (relClock U' s Wr t).toNNReal := by rw [hnn']
        _ = relMap U' s (γ t) := hΓeq
    show sphereInv (γ t : OnePoint ℂ) = (((ownComponentChart Ur s).2.1 (Γ u) : ℂ) : OnePoint ℂ)
    rw [hΓeq', hinv, ownComponentChart_inv_relMap hU' hU'0 (NNReal.coe_nonneg s) hγH (hγdom t ht hγH),
      sphereInv_coe_of_ne (ne_zero_of_mem_H hγH)]

/-! ### GB6's conditional-law half in hull form -/

/-- **Proposition GB6, conditional-law half, hull form** (named statement; not proved here). Setting and binders of
`GB6RestartStatement` (verbatim). The kernel part is that of `GB6RestartStatement`; the pathwise part says that,
almost surely on `{s < ζα, α(s) ∈ ℍ}`, `ω ∈ M`, the chart field is the field `h` read in the chart of `U`, and the
chart driver `WC(X ω)` **is the relative exploration**: it is continuous from `0` with complete continuous generating
trace `Γ(X ω)`, it generates the chart images `Ψ(K'_t)` of the counterflow hulls in the relative clock
`a(t) = hcap(Ψ(K'_t))/2` at every time before the first contact `T_c`, and `a` is unbounded before `T_c` ("Its relative
lifetime is infinite").

Source (p. 519–520): "the portion of `η` before its first contact with `α[0, σ]`, in the chart of `U` taking `(y, p)`
to `(0, ∞)`, is the complete canonical counterflow of the conditional component field. Its relative lifetime is
infinite"; "Fixed-hull restriction gives continuous relative Loewner growth before `T`"; "Theorem 2.4 and integrated
uniqueness identify the relative driving law through every such stopped buffer"; "Hence `ζ = ∞`". Compared with
`GB6RestartStatement`, the physical identification `η(ℓ(u)) = c_U⁻¹(Γ(u))` and the clock onto `[0, T_c)` are not
asked: they are proved (`isGB6ChartContinuation_of_relHulls`). What remains is the law of the relative exploration
(its mean identification and Theorem 2.4), its infinite lifetime (GB5's passive-point consequence), its complete trace
(the complete finite-force theorem at `16/κ`), and the measurability of the restart variable
(`planning/handoffs/PROVE-GB6C.md`). -/
def GB6RelativeLawStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ s : ℝ≥0, ∃ (S : Type) (_ : MeasurableSpace S) (H' : S → LQGMetric.DistOn upperHalfPlaneOpens)
      (WC : ℝ≥0 → S → ℝ) (Γ : S → ℝ≥0 → ℂ) (M : Set Ω) (β : Ω → Restart.BoundaryWord) (X : Ω → S)
      (K : Kernel Restart.BoundaryWord S),
      IsGB6RestartCoordinates H' WC Γ ∧ MeasurableSet M ∧ Measurable β ∧ Measurable X ∧ IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ c ∂(P.restrict M).map β, IsGB6ConditionalCounterflow κ c (K c) H' WC Γ) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
        ω ∈ M ∧
        IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
          (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (H' (X ω)) ∧
        Continuous (fun t => WC t (X ω)) ∧ WC 0 (X ω) = 0 ∧
        IsGeneratingTrace (fun t => WC t (X ω)) ⊤ (Γ (X ω)) ∧
        (∀ u : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
            ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) ∧
          u ≤ relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
            ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) →
          QuantumZipper.fwdHull (fun r : ℝ => WC r.toNNReal (X ω))
              (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t) =
            relMap (fun r : ℝ => Wα r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) t

/-- **GB6's conditional-law half from its hull form** (conditional helper with a distinct name):
`GB6RelativeLawStatement → GB6RestartStatement`. The kernel part is the same; the pathwise clause
`IsGB6ChartContinuation` is `isGB6ChartContinuation_of_relHulls`. -/
theorem gb6RestartStatement_of_relativeLaw (hRL : GB6RelativeLawStatement.{u}) : GB6RestartStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' htr hcf hadmL hadmR hcomp hfl hα s
  obtain ⟨S, mS, H', WC, Γ, M, β, X, K, hcoord, hM, hβ, hX, hK, hlaw, hcond, hpath⟩ :=
    hRL κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' htr hcf hadmL hadmR hcomp hfl hα s
  refine ⟨S, mS, H', WC, Γ, M, β, X, K, hcoord, hM, hβ, hX, hK, hlaw, hcond, ?_⟩
  filter_upwards [hcomp, hα, ae_driver_zero_continuousOn hfl, ae_driver_zero_continuousOn hcf, hpath]
    with ω hcω hαω hpα hpc hpω hsζ hsH
  obtain ⟨hMω, htrω, hWCc, hWC0, hΓω, hunb, hKω⟩ := hpω hsζ hsH
  have hWc : Continuous fun t => W t ω := by
    have := hpc.2
    rw [hcω.1] at this
    simp only [ENNReal.coe_lt_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  exact ⟨hMω, isGB6ChartContinuation_of_relHulls htrω hαω hpα.2 hpα.1 hsζ hsH hcω.2.1 hWc hpc.1 hΓω hWCc hWC0
    hunb hKω⟩

/-- **GB6's first-contact assertion from the hull form of its conditional-law half** (conditional helper). -/
theorem gb6FirstContactStatement_of_relativeLaw (hRL : GB6RelativeLawStatement.{u}) :
    GB6FirstContactStatement.{u} :=
  gb6FirstContactStatement_of_restart (gb6RestartStatement_of_relativeLaw hRL)

end GB6

end Supp8

end InteractingSLE
