/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71LFilt
import InteractingSLE.Spec.Sec7.LocalExtGChart

/-!
# Lemma 7.1: the active component of the three-curve complement at the capacity time (B4, geometry)

Packet PROVE-LEMMA71L, item B4. Specification §7.1 (`source/spec/p193-240.md` L590–L595, pp. 224–225: "The means in all
the remaining components are those of the three-curve result in Remark 6.7. In particular, in the active component
they have the two seed heights (CPF2)").

On the good event, at a capacity time `t` below the terminal capacity of the mapped segment `γ'`, the chart preimage
`inv(ℍ ∖ K_t)` of the complement of the Loewner hull `K_t` of `γ'` (`K_t = fill(γ'[0, capInv t])`) is a connected
component of `ℍ ∖ A(τ_t)`, `A(τ_t) = β ∪ α ∪ γ([0, τ_t])` the explored set of the three curves at the capacity time
`τ_t = capTime … t` (`connectedComponentIn_eq_image`). This is the component in which the three-curve law of
Remark 6.7 is applied to the test functions of the chart coupling clause.

* `IsSegCurve.fwdHull_segDriver_eq`: `K_t = fill(γ'[0, capInv t])`, a half-plane hull;
* `mem_closure_of_mem_fillH_of_mem_closure`: a point of a filling that is a limit of points outside it lies on the
  closure of the filled set;
* **`connectedComponentIn_eq_image`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71L

open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open Lemma71I Lemma71C Lemma71K Sec6 LocalSets

/-- **The hull of the canonical driver of a segment curve** at a capacity time below the terminal one is the filled
prefix of the curve, and it is a half-plane hull. -/
theorem IsSegCurve.fwdHull_segDriver_eq {Γ : ℝ → ℂ} (hΓ : IsSegCurve Γ) {s : ℝ} (hs : 0 ≤ s)
    (hsl : ENNReal.ofReal s < capLife Γ) :
    QuantumZipper.fwdHull (fun r : ℝ => segDriver Γ r.toNNReal) s = fillH (Γ '' Icc 0 (capInv Γ s)) ∧
      IsHPHull (fillH (Γ '' Icc 0 (capInv Γ s))) := by
  obtain ⟨n, hn⟩ := exists_lt_capClock_of_lt_capLife hsl
  have hn0 : (0 : ℝ) < n := by
    by_contra h
    have h0 : (n : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg n)
    rw [h0, hΓ.capClock_zero] at hn
    linarith
  obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hΓ.exists_localDriver hn0
  have hK' : ∀ t ∈ Icc 0 (n : ℝ), QuantumZipper.fwdHull W (capClock Γ t) = fillH (Γ '' Icc 0 t) :=
    fun t ht => (hK t ht).2
  have hA := hΓ.fillH_capInv_eq hn0 hK' hs hn.le
  have hcong : QuantumZipper.fwdHull (fun r : ℝ => segDriver Γ r.toNNReal) s = QuantumZipper.fwdHull W s := by
    refine LocalExt.fwdHull_congr_of_eqOn_of_lt hs hn fun r hr => ?_
    show segDriver Γ r.toNNReal = W r
    have hr0 : 0 ≤ r := hr.1
    rw [segDriver, Real.coe_toNNReal r hr0]
    exact hΓ.segDrv_eq hn0 hW hW0 hK' hr0 hr.2
  refine ⟨hcong.trans hA.symm, ?_⟩
  rw [hA]
  exact isHPHull_fwdHull hW hs

/-- A point of the filling `fill(A)` that is a limit of points of `ℍ ∖ fill(A)` lies in the closure of `A`: a point of a
bounded component of `ℍ ∖ cl A` has that whole open component inside the filling. -/
theorem mem_closure_of_mem_fillH_of_mem_closure {A : Set ℂ} {w : ℂ} (hw : w ∈ fillH A)
    (hcl : w ∈ closure (H \ fillH A)) : w ∈ closure A := by
  by_contra hnot
  have hb : IsBounded (connectedComponentIn (H \ closure A) w) := hw.2.resolve_left hnot
  have hwD : w ∈ connectedComponentIn (H \ closure A) w := mem_connectedComponentIn ⟨hw.1, hnot⟩
  have hDo : IsOpen (connectedComponentIn (H \ closure A) w) :=
    (QuantumZipper.isOpen_H.sdiff isClosed_closure).connectedComponentIn
  have hDsub : connectedComponentIn (H \ closure A) w ⊆ fillH A := fun z hz => by
    have hzH : z ∈ H \ closure A := connectedComponentIn_subset _ _ hz
    refine ⟨hzH.1, Or.inr ?_⟩
    rw [← connectedComponentIn_eq hz]
    exact hb
  obtain ⟨z, hzD, hzF⟩ := (_root_.mem_closure_iff.1 hcl) _ hDo hwD
  exact hzF.2 (hDsub hzD)

section Space

variable {Ω : Type*} {β α γ : Ω → ℝ≥0 → ℂ} {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}
  {G : (Hist × Hist) × ℂ → ℂ} {M : Set ((Hist × Hist) × ℂ)} {Y : Hist × Hist → ℂ}

theorem zero_notMem_H : (0 : ℂ) ∉ H := fun h => by
  have : (0 : ℝ) < (0 : ℂ).im := h
  simp at this

/-- **B4 (geometry): the chart preimage of `ℍ ∖ K_t` is a component of `ℍ ∖ A(τ_t)`.** On the good event, for a
capacity time `t` below the terminal capacity of the mapped segment, every point `z₀` of `inv(ℍ ∖ K_t)` lies off the
explored set `A(τ_t) = β ∪ α ∪ γ([0, τ_t])` of the three curves at the capacity time, and its component in `ℍ ∖ A(τ_t)`
is `inv(ℍ ∖ K_t)`. -/
theorem connectedComponentIn_eq_image {ω : Ω} (hg : PocketGood β α γ C c γ' ω) (hCo : IsOpen (C ω))
    (hCH : C ω ⊆ H) (hc : (c ω).IsConformal) (hdom : ((c ω).dom : Set ℂ) = C ω) (hγH : ∀ t, γ ω t ∈ Hbar)
    (hγc : Continuous (γ ω)) (hγ0 : γ ω 0 = 0) (hΓ : IsSegCurve (γ' ω))
    (hMiff : ∀ z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω) (hGeq : ∀ z ∈ C ω, G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : Y (outerHist β α ω) = closePt α C ω) {t : ℝ≥0} (htl : (t : ℝ≥0∞) < capLife (γ' ω)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ (c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun r : ℝ => segDriver (γ' ω) r.toNNReal) t)) :
    z₀ ∈ H \ explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω ∧
      connectedComponentIn (H \ explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
        z₀ = (c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun r : ℝ => segDriver (γ' ω) r.toNNReal) t) := by
  obtain ⟨hvc, -, hin, hD1, hD2⟩ := hg.visit hCo hCH hc hdom hγH
  rw [← hYeq] at hD1 hD2
  have hFc : ContinuousOn (c ω).1 (C ω) := by rw [← hdom]; exact hc.differentiableOn_fwd.continuousOn
  have hvc' := hvc
  obtain ⟨-, hκm, hκ0, hlim, hcov, -⟩ := hvc'
  have htl' : ENNReal.ofReal (t : ℝ) < capLife (γ' ω) := by rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨hU0, -⟩ := hΓ.capInv_spec (NNReal.coe_nonneg t) htl'
  obtain ⟨hKeq, hKhull⟩ := IsSegCurve.fwdHull_segDriver_eq hΓ (NNReal.coe_nonneg t) htl'
  rw [hKeq] at hz₀ ⊢
  set κ := visitClock (γ ω) (closure (cayley '' C ω)) with hκdef
  set U := capInv (γ' ω) t with hUdef
  set Ar := γ' ω '' Icc 0 U with hArdef
  have hκU : 0 ≤ κ U := hκ0.trans (hκm.monotoneOn self_mem_Ici hU0 hU0)
  have hmemC : ∀ z, z ∈ (c ω).dom ↔ z ∈ C ω := fun z => by rw [← SetLike.mem_coe, hdom]
  -- the capacity time: `0` at `t = 0`, the clock time of `capInv t` otherwise
  have hτ : (t = 0 ∧ capTime G M Y β α γ t ω = 0) ∨
      (0 < (t : ℝ) ∧ capTime G M Y β α γ t ω = ENNReal.ofReal (κ U)) := by
    rcases eq_or_lt_of_le (zero_le (a := t)) with ht0 | ht0
    · refine Or.inl ⟨ht0.symm, ?_⟩
      show capRule G M Y (ENNReal.ofReal (2 * (t : ℝ))) (outerHist β α ω) (pathCoord (γ ω)) = 0
      rw [← ht0, NNReal.coe_zero, mul_zero, ENNReal.ofReal_zero]
      exact capRule_zero_eq ((hD1 0 le_rfl).mono bot_le)
    · exact Or.inr ⟨ht0, capRule_eq_visitClock hMiff hGeq hCo hFc hγc hΓ hvc hD1 ht0 htl'⟩
  -- a visit before the capacity time is mapped into the mapped prefix
  have hvisit : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ capTime G M Y β α γ t ω → γ ω s ∈ C ω → (c ω).1 (γ ω s) ∈ Ar := by
    intro s hs hsC
    obtain ⟨v, hv0, hκv⟩ := hcov s hsC
    have hp : γ ω (κ v).toNNReal = γ ω s := by rw [hκv, Real.toNNReal_coe]
    have hF := Lemma71Pin.eq_of_tendsto_of_mem hFc hsC (hp ▸ hlim v hv0)
    refine ⟨v, ⟨hv0, ?_⟩, hF.symm⟩
    rcases hτ with ⟨-, hτ0⟩ | ⟨-, hτeq⟩
    · rw [hτ0, nonpos_iff_eq_zero, ENNReal.coe_eq_zero] at hs
      rw [hs, hγ0] at hsC
      exact absurd (hCH hsC) zero_notMem_H
    · rw [hτeq, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff hκU, ← hκv] at hs
      by_contra hlt
      exact absurd (hκm hU0 hv0 (not_le.1 hlt)) (not_lt.2 hs)
  -- a point of the mapped prefix in `ℍ` comes from a visit before the capacity time
  have hback : ∀ v ∈ Icc 0 U, 0 < (γ' ω v).im → γ ω (κ v).toNNReal ∈ C ω ∧
      (((κ v).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ capTime G M Y β α γ t ω ∧ (c ω).1 (γ ω (κ v).toNNReal) = γ' ω v := by
    intro v hv hpos
    have hzC := hin v hv.1 hpos
    refine ⟨hzC, ?_, Lemma71Pin.eq_of_tendsto_of_mem hFc hzC (hlim v hv.1)⟩
    rcases hτ with ⟨ht0, -⟩ | ⟨-, hτeq⟩
    · have hU : U = 0 := by rw [hUdef, ht0, NNReal.coe_zero]; exact hΓ.capInv_of_nonpos le_rfl
      have hv0 : v = 0 := le_antisymm (hU ▸ hv.2) hv.1
      rw [hv0, hΓ.2.2.2.1] at hpos
      exact absurd hpos (lt_irrefl _)
    · rw [hτeq]
      exact ENNReal.ofReal_le_ofReal (hκm.monotoneOn hv.1 hU0 hv.2)
  have hA := Three.explored_threeStops β α γ (capTime G M Y β α γ t) ω
  have hCdisj : ∀ z ∈ C ω, z ∉ range (β ω) ∪ range (α ω) := by
    obtain ⟨-, -, -, hb, -⟩ := hg
    obtain ⟨z', -, -, -, hCz⟩ := hb
    intro z hz hzr
    rw [hCz] at hz
    have := (connectedComponentIn_subset _ _ hz).2
    exact this (by rcases hzr with h | h; exact Or.inr h; exact Or.inl h)
  set S := (c ω).2.1 '' (H \ fillH Ar) with hSdef
  have hSC : S ⊆ C ω := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hmemC _).1 (hc.inv_mem_dom hw.1)
  have hSsub : S ⊆ H \ explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω := by
    rintro _ ⟨w, ⟨hwH, hwK⟩, rfl⟩
    have hzC := hSC ⟨w, ⟨hwH, hwK⟩, rfl⟩
    refine ⟨hCH hzC, ?_⟩
    rw [hA]
    rintro ⟨hzA, -⟩
    rcases hzA with hzr | ⟨s, hs, hsz⟩
    · exact hCdisj _ hzC hzr
    · have h1 := hvisit s hs (hsz ▸ hzC)
      rw [hsz, hc.2.2 w hwH] at h1
      exact hwK ⟨hwH, Or.inl (subset_closure h1)⟩
  have hSo : IsOpen S := SmallGammaGeodesics.CC.isOpen_image_conf hKhull.isOpen (hc.1.mono sdiff_subset)
    (hc.injOn.mono sdiff_subset)
  have hSc : IsPreconnected S := hKhull.isConnected.isPreconnected.image _ (hc.1.continuousOn.mono sdiff_subset)
  have hz₀A := hSsub hz₀
  -- `S` is closed in `ℍ ∖ A(τ_t)`
  have hclosed : ∀ z ∈ H \ explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω,
      z ∈ closure S → z ∈ S := by
    rintro z ⟨hzH, hzA⟩ hzcl
    have hzr : z ∉ range (β ω) ∪ range (α ω) := fun h => hzA (by rw [hA]; exact ⟨Or.inl h, hzH⟩)
    have hzC : z ∈ C ω := by
      by_contra hzC
      have hfr : z ∈ frontier (C ω) := by
        rw [hCo.frontier_eq]
        exact ⟨closure_mono hSC hzcl, hzC⟩
      obtain ⟨-, -, -, -, hfrH, -⟩ := hg
      exact hzr (hfrH ⟨hfr, hzH⟩)
    have hzd : z ∈ (c ω).dom := (hmemC z).2 hzC
    have hwH : (c ω).1 z ∈ H := hc.fwd_mem hzd
    have hwcl : (c ω).1 z ∈ closure (H \ fillH Ar) := by
      have hcont : ContinuousAt (c ω).1 z := (hFc z hzC).continuousAt (hCo.mem_nhds hzC)
      refine closure_mono ?_ (mem_closure_image hcont hzcl)
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      rw [hc.2.2 w hw.1]
      exact hw
    have hwK : (c ω).1 z ∉ fillH Ar := by
      intro hwK
      have hArc : IsCompact Ar := isCompact_Icc.image_of_continuousOn (hΓ.1.mono Icc_subset_Ici_self)
      have hmem := mem_closure_of_mem_fillH_of_mem_closure hwK hwcl
      rw [hArc.isClosed.closure_eq] at hmem
      obtain ⟨v, hv, hvw⟩ := hmem
      have hpos : 0 < (γ' ω v).im := by rw [hvw]; exact hwH
      obtain ⟨hz'C, hz'τ, hz'F⟩ := hback v hv hpos
      have hzz : γ ω (κ v).toNNReal = z := by
        rw [← hc.inv_fwd ((hmemC _).2 hz'C), hz'F, hvw, hc.inv_fwd hzd]
      exact hzA (by rw [hA]; exact ⟨Or.inr ⟨(κ v).toNNReal, hz'τ, hzz⟩, hzH⟩)
    exact ⟨(c ω).1 z, ⟨hwH, hwK⟩, hc.inv_fwd hzd⟩
  have hsub : connectedComponentIn (H \ explored (Three.threeCurves β α γ)
      (Three.threeStops (capTime G M Y β α γ t)) ω) z₀ ⊆ S := by
    refine IsPreconnected.subset_left_of_subset_union hSo isClosed_closure.isOpen_compl
      (disjoint_compl_right_iff_subset.2 subset_closure) (fun z hz => ?_)
      ⟨z₀, mem_connectedComponentIn hz₀A, hz₀⟩ isPreconnected_connectedComponentIn
    by_cases hcl : z ∈ closure S
    · exact Or.inl (hclosed z (connectedComponentIn_subset _ _ hz) hcl)
    · exact Or.inr hcl
  exact ⟨hz₀A, hsub.antisymm (hSc.subset_connectedComponentIn hz₀ hSsub)⟩

end Space

end InteractingSLE.Sec7.Lemma71L
