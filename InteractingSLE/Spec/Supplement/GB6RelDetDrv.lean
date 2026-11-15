/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6RelDet
import InteractingSLE.Spec.Supplement.GB6Restart

/-!
# GB6's (Det) in driver form

Packet PROVE-GB6-RELDET. `GB6HullDetStatement` (the hull identity of GB6's (Det)) is a statement about hulls. The
stopped-determination machinery of the project (`Restart.FCDet.ae_driverCodeMatch_of_hasSafeLaw`, PROVE-STOPPEDK2,
PROVE-DOMAINMARKOV10) concludes with **driver** agreements. This file removes the geometric part of the hull identity:

* **`exists_relDriver_of_traces`** (deterministic, one sample): before the first contact `T_c`, the chart images
  `Ψ(K'_t)` of the counterflow hulls are the hulls of one driver `W'` with `W'(0) = 0`, continuous before the relative
  lifetime, in the intrinsic relative clock `a(t) = hcap(Ψ(K'_t))/2`, which is strictly increasing before `T_c` with
  `a(0) = 0` (GB6C's glued chain, transferred from a frozen flow driver);
* `fwdHull_relClock_eq_of_agree`: a driver agreeing with such a `W'` up to every relative time before the relative
  lifetime generates the same chart images;
* **`GB6RelDrvDetStatement`** (named input, driver form): almost surely on `{s < ζα, α(s) ∈ ℍ}`, the decoded canonical
  driver code of the conditional field agrees with **every** continuous generator `W'` of the relative hull family on
  `[0, a(t)]` for every `t < T_c`;
* **`gb6HullDetStatement_of_relDrvDet`**: `GB6RelDrvDetStatement → GB6HullDetStatement`.

Nothing here uses Theorem 1.2/1.3 or any `*_of_param` result.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Supp8

namespace GB6

open Restart Sec2.Assembly

/-! ### The relative driver of one sample -/

section Sample

variable {wα w : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {α γ : ℝ≥0 → ℂ} {s : ℝ≥0}

/-- **The relative driver of one sample** (GB6C's glued chain, `exists_glued_relChain`, for the actual flow driver).
Let `α` be the generating trace of the flow driver `wα` with an interior tip `α(s) ∈ ℍ` before its lifetime, and `γ` a
complete generating trace of the continuous counterflow driver `w`. Then before the first contact `T_c` of the physical
counterflow with `α([0, s])`, the relative clock `a(t) = hcap(Ψ(K'_t))/2` starts at `0` and is strictly increasing,
and one driver `W'` with `W'(0) = 0`, continuous before the relative lifetime, generates `Ψ(K'_t)` at `a(t)`. -/
theorem exists_relDriver_of_traces (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα})
    (hwα0 : wα 0 = 0) (hs : (s : ℝ≥0∞) < Tα) (hsH : α s ∈ H) (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w)
    (hw0 : w 0 = 0) :
    ∃ W' : ℝ≥0 → ℝ, W' 0 = 0 ∧
      relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) 0 = 0 ∧
      StrictMonoOn (fun t : ℝ≥0 => relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t)
        {t | (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
          ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)} ∧
      ContinuousOn W' {u | ∃ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
          ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) ∧
        (u : ℝ) < relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
          ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) →
        QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal)
            (relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t) =
          relMap (fun r : ℝ => wα r.toNNReal) s '' QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) t := by
  set Tc := firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)
    with hTcdef
  set Ur : ℝ → ℝ := fun r => wα r.toNNReal with hUr
  set Wr : ℝ → ℝ := fun r => w r.toNNReal with hWr
  have hw' : Continuous Wr := hw.comp continuous_real_toNNReal
  have hw'0 : Wr 0 = 0 := by simp only [hWr, Real.toNNReal_zero, hw0]
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
  obtain ⟨W', hW'0, ha0, hsm, -, hW'c, hK⟩ := exists_glued_relChain hw hw0 hU' hU'0 hs0 htip hTc hd hγK
  refine ⟨W', hW'0, by rw [hclock]; exact ha0, ?_, ?_, fun t ht => ?_⟩
  · rw [hclock]; exact hsm
  · rw [hclock]; exact hW'c
  · rw [hclock, hrel]; exact (hK t ht).1

end Sample

/-! ### Agreeing drivers generate the same relative hulls -/

/-- **A driver agreeing with a relative driver generates the same chart images.** If `W'` generates `Ψ(K'_t)` at
`a(t)` for every `t < T` (with `a` strictly increasing there and `a(0) = 0`) and `D` agrees with `W'` on `[0, a(t)]`
for every `t < T`, then `D` generates `Ψ(K'_t)` at `a(t)` for every `t < T`. -/
theorem fwdHull_relClock_eq_of_agree {a : ℝ≥0 → ℝ} {T : ℝ≥0∞} {W' D : ℝ≥0 → ℝ} {K : ℝ≥0 → Set ℂ}
    (ha0 : a 0 = 0) (hsm : StrictMonoOn a {t | (t : ℝ≥0∞) < T})
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (a t) = K t)
    (hD : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → ∀ u : ℝ≥0, (u : ℝ) ≤ a t → D u = W' u) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → QuantumZipper.fwdHull (fun r : ℝ => D r.toNNReal) (a t) = K t := by
  intro t ht
  obtain ⟨t', htt', ht'T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htt'' : t < t' := by exact_mod_cast htt'
  have h0T : ((0 : ℝ≥0) : ℝ≥0∞) < T := lt_of_le_of_lt (by simp) ht
  have hat : a t < a t' := hsm ht ht'T htt''
  have hnn : 0 ≤ a t := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
    · rw [← h, ha0]
    · rw [← ha0]; exact (hsm h0T ht h).le
  rw [← hK t ht]
  refine fwdHull_eq_of_eqOn hnn hat fun r hr => ?_
  exact hD t' ht'T r.toNNReal (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2)

/-! ### The driver form of (Det) -/

/-- **Named input: GB6's (Det) in driver form.** Binders of `GB6RelDetStatement` verbatim. Almost surely on
`{s < ζα, α(s) ∈ ℍ}`: for every driver `W'` continuous before the relative lifetime that generates the chart images
`Ψ(K'_t)` of the counterflow hulls in the relative clock `a(t)` before the first contact `T_c`, the decoded canonical
driver code of the conditional field (word `β = gb6Word κ θ c s Wα`) agrees with `W'` on `[0, a(t)]` for every
`t < T_c`. Such a `W'` exists (`exists_relDriver_of_traces`) and is unique on the relative lifetime (Loewner drivers
are determined by their hulls), so this is the driver-level identification "the relative counterflow is, before its
first contact, the canonical counterflow of the conditional field": Astra's follow-up 3, Q3 §§3.2–3.7 (the relative
stopped coupling) and the stopped determination of the canonical code. -/
def GB6RelDrvDetStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
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
    ∀ (s : ℝ≥0) (Hc : Ω → DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (Hc ω)) →
    ∀ F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞,
      IsCanonicalDriverCode (16 / κ) 0 F →
    ∀ c : BoundaryWord, c.jumps = J → (∀ y ∉ J, c.fn y = b y) →
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
        ∀ W' : ℝ≥0 → ℝ,
          ContinuousOn W' {u | ∃ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
            ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) ∧
            (u : ℝ) < relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t} →
          (∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
            ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) →
            QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal)
                (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t) =
              relMap (fun r : ℝ => Wα r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) t) →
          ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
            ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) →
            ∀ u : ℝ≥0, (u : ℝ) ≤ relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t →
              drvDec (F (gb6Word κ θ c s (fun t => Wα t ω), Hc ω)) u = W' u

/-- **GB6's (Det) from its driver form.** Almost surely the flow and counterflow drivers are continuous from `0` with
generating traces, so the relative driver of the sample exists (`exists_relDriver_of_traces`); the driver form makes
the decoded canonical code agree with it up to every relative time before the relative lifetime, so it generates the
same chart images (`fwdHull_relClock_eq_of_agree`). -/
theorem gb6HullDetStatement_of_relDrvDet (hD : GB6RelDrvDetStatement.{u}) : GB6HullDetStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s Hc
    hHcm hHc F hF c hcJ hcb
  have hDω := hD κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl
    hα s Hc hHcm hHc F hF c hcJ hcb
  filter_upwards [hDω, hcomp, ae_driver_zero_continuousOn hcf, ae_driver_zero_continuousOn hfl, hα]
    with ω hω hcω hWω hWαω hαω hs hsH
  obtain ⟨hζ, hγ, -⟩ := hcω
  have hw : Continuous fun t => W t ω :=
    continuousOn_univ.1 (hWω.2.mono fun t _ => by rw [mem_ofPred_eq, hζ]; exact ENNReal.coe_lt_top)
  obtain ⟨W', -, ha0, hsm, hW'c, hK⟩ := exists_relDriver_of_traces hαω hWαω.2 hWαω.1 hs hsH hγ hw hWω.1
  exact fwdHull_relClock_eq_of_agree ha0 hsm hK (hω hs hsH W' hW'c hK)

end GB6

end Supp8

end InteractingSLE
