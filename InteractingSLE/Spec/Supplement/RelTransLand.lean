/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RelTransHull

/-!
# The relative transition: the joint landing map and the boundary values of the transition

Packet PROVE-RELTRANS. In the setting of `BHMean.RelTransitionStatement` (retained chart `Ψ` of `ℍ ∖ A`, explored
hull `K_t`, relative hull `K̃_u = Ψ(K_t)`, closed hulls disjoint), write `J = Ψi ∘ f̃_u⁻¹` (`BHMean.jointInv`) and
`τ = f_t ∘ J` (the transition).

* **The joint landing map** `ℓ = extendFrom ℍ J` is continuous on `ℍ̄` (`J` has a limit at every point of `ℍ̄`:
  `f̃_u⁻¹` has boundary limits and `Ψi` lands at every real point); at a real point it is never a point of the joint
  complement `C = ℍ ∖ (A ∪ K_t)`, so off `cl A` it is not a point of `ℍ ∖ K_t`. The set
  `U = {x ∈ ℝ | ℓ(x) ∉ cl A}` is open, and on a ball around each `x ∈ U` every real point lands off `ℍ ∖ K_t`
  (`exists_ball_land`, the hypothesis of `BHMean.exists_int_jointChart`).
* On the relative hull image `ℓ` lands on `cl K_t` (`extendFrom_jointInv_mem_closure`); off it `ℓ` is a real point off
  `cl K_t` when it is off `cl A` (`landing_real_of_notMem`).
* **The transition** has a real limit `v` with `F̄_t(v) = ℓ(z)` at every real `z` with `ℓ(z) ∉ cl A`
  (`exists_tendsto_transition`, the cluster-set lemma `Sec7.Lemma71O.exists_tendsto_fwdMap_comp`), so it is
  real-boundary conformal on a half-disc around each point of `U` (`isRealBoundaryConformal_transition`); its boundary
  values `transBdry` have a positive derivative at every point of `U` (`hasDerivAt_transBdry`: the Schwarz reflection
  has positive derivative on the diameter) and increase strictly on every interval inside `U`
  (**`strictMonoOn_transBdry`**); `transBdry 0 = 0` from the tip identity (`transBdry_zero`).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open QuantumZipper.CA (schwarzReflect)

namespace InteractingSLE.Supp8.RelTrans

open BHMean (IsRetainedChart jointInv jointFwd jointLift jointChart)

/-- `𝓝[ℍ] z` is nontrivial at every point of `ℍ̄`. -/
theorem nhdsWithin_H_neBot_of_mem_Hbar {z : ℂ} (hz : z ∈ Hbar) : (𝓝[H] z).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ hz)

theorem ofReal_mem_Hbar (x : ℝ) : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp

section Landing

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u : ℝ}

/-- The retained inverse `Ψi` has a limit at every point of `ℍ̄`. -/
theorem exists_tendsto_retainedInv (hΨ : IsRetainedChart A Ψ Ψi LΨ) {y : ℂ} (hy : y ∈ Hbar) :
    ∃ p, Tendsto Ψi (𝓝[H] y) (𝓝 p) := by
  by_cases hyH : y ∈ H
  · exact ⟨Ψi y, (hΨ.diff_inv.continuousOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds hyH)).tendsto.mono_left
      nhdsWithin_le_nhds⟩
  · have hyim : y.im = 0 := le_antisymm (not_lt.1 hyH) hy
    have hyr : y = (y.re : ℂ) := Complex.ext (by simp) (by simp [hyim])
    obtain ⟨p, hp⟩ := hΨ.inv_lands y.re
    rw [← hyr] at hp
    exact ⟨p, hp⟩

/-- **The joint parametrization lands at every point of `ℍ̄`**, at `ℓ(z) = Ψ̄i(F̄̃_u(z))`. -/
theorem tendsto_jointInv (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) {z : ℂ} (hz : z ∈ Hbar) :
    Tendsto (jointInv Ψi Wr u) (𝓝[H] z) (𝓝 (extendFrom H (jointInv Ψi Wr u) z)) ∧
      Tendsto Ψi (𝓝[H] (extendFrom H (fwdMapInv Wr u) z)) (𝓝 (extendFrom H (jointInv Ψi Wr u) z)) := by
  set yc : ℂ := extendFrom H (fwdMapInv Wr u) z with hycdef
  have hycb : yc ∈ Hbar := BHMean.extendFrom_mem_Hbar hηr hWr hWr0 hu hz
  have hlimF : Tendsto (fwdMapInv Wr u) (𝓝[H] z) (𝓝[H] yc) :=
    tendsto_nhdsWithin_iff.2 ⟨(hηr.hasBdryLimits hWr hWr0 hu).tendsto hz,
      eventually_nhdsWithin_of_forall fun v hv => QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hv⟩
  obtain ⟨p, hp⟩ := exists_tendsto_retainedInv hΨ hycb
  have hJ : Tendsto (jointInv Ψi Wr u) (𝓝[H] z) (𝓝 p) := hp.comp hlimF
  have he : extendFrom H (jointInv Ψi Wr u) z = p := extendFrom_eq (by rw [closure_H]; exact hz) hJ
  rw [he]
  exact ⟨hJ, hp⟩

/-- **The joint landing map is continuous on `ℍ̄`.** -/
theorem continuousOn_extendFrom_jointInv (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hWr : Continuous Wr)
    (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) :
    ContinuousOn (extendFrom H (jointInv Ψi Wr u)) Hbar :=
  continuousOn_extendFrom (by rw [closure_H]) fun _ hz => ⟨_, (tendsto_jointInv hΨ hWr hWr0 hηr hu hz).1⟩

/-- The joint landing map along `ℝ` is continuous. -/
theorem continuous_landing (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hWr : Continuous Wr)
    (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) :
    Continuous fun s : ℝ => extendFrom H (jointInv Ψi Wr u) (s : ℂ) :=
  (continuousOn_extendFrom_jointInv hΨ hWr hWr0 hηr hu).comp_continuous Complex.continuous_ofReal ofReal_mem_Hbar

/-- **The set `U` of real points landing off the closed retained set is open.** -/
theorem isOpen_landOff (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hWr : Continuous Wr)
    (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) :
    IsOpen {s : ℝ | extendFrom H (jointInv Ψi Wr u) (s : ℂ) ∉ closure A} :=
  isClosed_closure.isOpen_compl.preimage (continuous_landing hΨ hWr hWr0 hηr hu)

/-- **A real landing point of the joint parametrization is not a point of the joint complement.** -/
theorem extendFrom_jointInv_notMem (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {z : ℂ} (hz : z.im = 0) : extendFrom H (jointInv Ψi Wr u) z ∉ H \ (A ∪ fwdHull w t) := by
  intro hp
  have hzb : z ∈ Hbar := show (0 : ℝ) ≤ z.im from hz.ge
  have hJ := (tendsto_jointInv hΨ hWr hWr0 hηr hu hzb).1
  have hc : ContinuousAt (jointFwd Ψ Wr u) (extendFrom H (jointInv Ψi Wr u) z) :=
    (BHMean.differentiableAt_jointFwd hΨ hw ht hWr hWr0 hu hK hd hp).continuousAt
  have h1 : Tendsto (fun y => jointFwd Ψ Wr u (jointInv Ψi Wr u y)) (𝓝[H] z)
      (𝓝 (jointFwd Ψ Wr u (extendFrom H (jointInv Ψi Wr u) z))) := hc.tendsto.comp hJ
  have h2 : Tendsto (fun y => jointFwd Ψ Wr u (jointInv Ψi Wr u y)) (𝓝[H] z) (𝓝 z) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (eventually_nhdsWithin_of_forall fun y hy =>
      (BHMean.jointFwd_jointInv hΨ hw ht hWr hWr0 hu hK hd hy).symm)
  have := nhdsWithin_H_neBot_of_mem_Hbar hzb
  have he := tendsto_nhds_unique h1 h2
  have hpos : (0 : ℝ) < (jointFwd Ψ Wr u (extendFrom H (jointInv Ψi Wr u) z)).im :=
    BHMean.jointFwd_mem hΨ hw ht hWr hWr0 hu hK hd hp
  rw [he, hz] at hpos
  exact lt_irrefl _ hpos

/-- Off the closed retained set, a real landing point is not a point of `ℍ ∖ K_t`. -/
theorem notMem_compl_fwdHull_of_landOff (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {z : ℂ} (hz : z.im = 0) (hzA : extendFrom H (jointInv Ψi Wr u) z ∉ closure A) :
    extendFrom H (jointInv Ψi Wr u) z ∉ H \ fwdHull w t := fun hp =>
  extendFrom_jointInv_notMem hΨ hw ht hWr hWr0 hηr hu hK hd hz
    ⟨hp.1, fun h => h.elim (fun hA => hzA (subset_closure hA)) hp.2⟩

/-- **Around a point of `U`, every real point lands off the closed retained set.** -/
theorem exists_ball_land (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hWr : Continuous Wr)
    (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) {x : ℝ}
    (hx : extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∉ closure A) :
    ∃ r > 0, ∀ z ∈ ball (x : ℂ) r, z.im = 0 → extendFrom H (jointInv Ψi Wr u) z ∉ closure A := by
  have hc := continuousOn_extendFrom_jointInv hΨ hWr hWr0 hηr hu _ (ofReal_mem_Hbar x)
  have ho : (closure A)ᶜ ∈ 𝓝 (extendFrom H (jointInv Ψi Wr u) (x : ℂ)) :=
    isClosed_closure.isOpen_compl.mem_nhds hx
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.1 (hc.preimage_mem_nhdsWithin ho)
  exact ⟨r, hr, fun z hz hz0 => hsub ⟨hz, show (0 : ℝ) ≤ z.im from hz0.ge⟩⟩

/-- The landing hypothesis of `BHMean.exists_int_jointChart` on such a ball. -/
theorem hland_of_ball (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A)) {x r : ℝ}
    (hball : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → extendFrom H (jointInv Ψi Wr u) z ∉ closure A) :
    ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ∃ p, p ∉ H \ fwdHull w t ∧ Tendsto (jointInv Ψi Wr u) (𝓝[H] z) (𝓝 p) :=
  fun z hz hz0 => ⟨_, notMem_compl_fwdHull_of_landOff hΨ hw ht hWr hWr0 hηr hu hK hd hz0 (hball z hz hz0),
    (tendsto_jointInv hΨ hWr hWr0 hηr hu (show (0 : ℝ) ≤ z.im from hz0.ge)).1⟩

/-- **On the relative hull image the joint parametrization lands on the closed explored hull.** -/
theorem extendFrom_jointInv_mem_closure (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {z : ℂ} (hz : z ∈ Hbar) (hzK : extendFrom H (fwdMapInv Wr u) z ∈ closure (fwdHull Wr u)) :
    extendFrom H (jointInv Ψi Wr u) z ∈ closure (fwdHull w t) :=
  BHMean.landing_mem_closure hΨ hw ht hK hd hWr hu hzK (tendsto_jointInv hΨ hWr hWr0 hηr hu hz).2

/-- **Off the relative hull image**, a landing point off the closed retained set is a real point off the closed
explored hull (the argument of `BHMean.retained_side`). -/
theorem landing_real_of_notMem (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A)) {x : ℝ}
    (hy : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u))
    (hpA : extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∉ closure A) :
    (extendFrom H (jointInv Ψi Wr u) (x : ℂ)).im = 0 ∧
      extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∉ closure (fwdHull w t) := by
  set yc : ℂ := extendFrom H (fwdMapInv Wr u) (x : ℂ) with hycdef
  set p : ℂ := extendFrom H (jointInv Ψi Wr u) (x : ℂ) with hpdef
  have hyim : yc.im = 0 := BHMean.im_extendFrom_eq_zero_of_notMem_closure hηr hWr hWr0 hu hy
  have hp : Tendsto Ψi (𝓝[H] yc) (𝓝 p) := (tendsto_jointInv hΨ hWr hWr0 hηr hu (ofReal_mem_Hbar x)).2
  have hycb : yc ∈ Hbar := show (0 : ℝ) ≤ yc.im from hyim.ge
  have := nhdsWithin_H_neBot_of_mem_Hbar hycb
  have hpbar : p ∈ Hbar := by
    rw [← closure_H]
    exact mem_closure_of_tendsto hp (eventually_nhdsWithin_of_forall fun v hv => (hΨ.inv_mem v hv).1)
  have hpC : p ∉ H \ A := BHMean.notMem_compl_of_tendsto_inv hΨ hyim hp
  have hpre : p.im = 0 :=
    le_antisymm (not_lt.1 fun hpos => hpC ⟨hpos, fun h => hpA (subset_closure h)⟩) hpbar
  refine ⟨hpre, fun hpK => ?_⟩
  have hpr : p = (p.re : ℂ) := Complex.ext (by simp) (by simp [hpre])
  obtain ⟨x', hx'⟩ := hΨ.fwd_lands p.re (by rw [← hpr]; exact hpA)
  rw [← hpr] at hx'
  have hpw : Tendsto Ψi (𝓝[H] yc) (𝓝[H \ A] p) :=
    tendsto_nhdsWithin_iff.2 ⟨hp, eventually_nhdsWithin_of_forall fun v hv => hΨ.inv_mem v hv⟩
  have h1 : Tendsto (fun v => Ψ (Ψi v)) (𝓝[H] yc) (𝓝 (x' : ℂ)) := hx'.comp hpw
  have h2 : Tendsto (fun v => Ψ (Ψi v)) (𝓝[H] yc) (𝓝 yc) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (eventually_nhdsWithin_of_forall fun v hv =>
      (hΨ.fwd_inv v hv).symm)
  have hx'y : (x' : ℂ) = yc := tendsto_nhds_unique h1 h2
  apply hy
  have hKsub : fwdHull w t ⊆ H \ A := BHMean.fwdHull_subset_compl hd hw ht
  have hNeK : (𝓝[fwdHull w t] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hpK
  have h3 : Tendsto Ψ (𝓝[fwdHull w t] p) (𝓝 (x' : ℂ)) := hx'.mono_left (nhdsWithin_mono p hKsub)
  rw [← hx'y]
  exact mem_closure_of_tendsto h3 (eventually_nhdsWithin_of_forall fun z hz => hK ▸ mem_image_of_mem Ψ hz)

end Landing

/-! ### The transition and its boundary values -/

/-- **The boundary values of the transition** `τ = f_t ∘ Ψi ∘ f̃_u⁻¹` on `ℝ` (real part of its boundary extension). -/
def transBdry (Ψi : ℂ → ℂ) (w Wr : ℝ → ℝ) (t u : ℝ) (s : ℝ) : ℝ :=
  (extendFrom H (fun y => fwdMap w t (jointInv Ψi Wr u y)) (s : ℂ)).re

section Transition

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u : ℝ}

/-- **The transition has a real limit** at every real point landing off the closed retained set, and the inverse
explored map sends it to the joint landing point. -/
theorem exists_tendsto_transition (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {z : ℂ} (hz : z.im = 0) (hzA : extendFrom H (jointInv Ψi Wr u) z ∉ closure A) :
    ∃ v : ℂ, v.im = 0 ∧ extendFrom H (fwdMapInv w t) v = extendFrom H (jointInv Ψi Wr u) z ∧
      Tendsto (fun y => fwdMap w t (jointInv Ψi Wr u y)) (𝓝[H] z) (𝓝 v) := by
  have hzb : z ∈ Hbar := show (0 : ℝ) ≤ z.im from hz.ge
  have hc := BHMean.isConformal_jointChart hΨ hw ht hWr hWr0 hu hK hd
  have hCt : ((jointChart Ψ Ψi LΨ Wr u).dom : Set ℂ) ⊆ H \ fwdHull w t := by
    rw [BHMean.coe_dom_jointChart hΨ hw ht hWr hWr0 hu hK hd]
    exact fun y hy => ⟨hy.1, fun h => hy.2 (Or.inr h)⟩
  obtain ⟨v, hv, hFv, hT⟩ := Sec7.Lemma71O.exists_tendsto_fwdMap_comp hη hw hw0 ht hc hCt hzb
    (tendsto_jointInv hΨ hWr hWr0 hηr hu hzb).1
  exact ⟨v, Sec7.Lemma71O.im_eq_zero_of_land hw hw0 ht hv hFv
    (notMem_compl_fwdHull_of_landOff hΨ hw ht hWr hWr0 hηr hu hK hd hz hzA), hFv, hT⟩

/-- **The transition is real-boundary conformal** on a half-disc whose real points land off the closed retained set
(Schwarz reflection across the real diameter). -/
theorem isRealBoundaryConformal_transition (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {x r : ℝ} (hball : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → extendFrom H (jointInv Ψi Wr u) z ∉ closure A) :
    R16.IsRealBoundaryConformal (extendFrom H fun y => fwdMap w t (jointInv Ψi Wr u y)) x r :=
  Sec7.Lemma71O.isRealBoundaryConformal_extendFrom (c := jointChart Ψ Ψi LΨ Wr u)
    (D := H \ fwdHull w t)
    (BHMean.isConformal_jointChart hΨ hw ht hWr hWr0 hu hK hd) (BHMean.coe_dom_jointChart hΨ hw ht hWr hWr0 hu hK hd)
    (fun y hy => ⟨hy.1, fun h => hy.2 (Or.inr h)⟩)
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hw ht) (QuantumZipper.FwdHolo.injOn_fwdMap hw ht)
    (fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hw ht hz) fun z hz hz0 => by
      obtain ⟨v, hv, -, hT⟩ := exists_tendsto_transition hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd hz0
        (hball z hz hz0)
      exact ⟨v, hv, hT⟩

/-- **The boundary values of the transition have a positive derivative** at every point of `U`. -/
theorem hasDerivAt_transBdry (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {x : ℝ} (hx : extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∉ closure A) :
    ∃ d > 0, HasDerivAt (transBdry Ψi w Wr t u) d x := by
  obtain ⟨r, hr, hball⟩ := exists_ball_land hΨ hWr hWr0 hηr hu hx
  have hrbc := isRealBoundaryConformal_transition hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd hball
  set φ : ℂ → ℂ := extendFrom H fun y => fwdMap w t (jointInv Ψi Wr u y) with hφdef
  have hxb : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
  have hdiff : HasDerivAt (schwarzReflect φ) (deriv (schwarzReflect φ) x) x :=
    ((hrbc.differentiableOn_schwarzReflect).differentiableAt (isOpen_ball.mem_nhds hxb)).hasDerivAt
  have heq : transBdry Ψi w Wr t u = fun s : ℝ => (schwarzReflect φ s).re := by
    funext s
    simp only [transBdry, schwarzReflect, Complex.ofReal_im, le_refl, ↓reduceIte, hφdef]
  refine ⟨(deriv (schwarzReflect φ) x).re, (hrbc.deriv_schwarzReflect_pos hxb).2, ?_⟩
  rw [heq]
  exact hdiff.real_of_complex

/-- **The boundary values of the transition increase strictly on every interval inside `U`.** -/
theorem strictMonoOn_transBdry (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {a b : ℝ} (hU : ∀ s ∈ Icc a b, extendFrom H (jointInv Ψi Wr u) (s : ℂ) ∉ closure A) :
    StrictMonoOn (transBdry Ψi w Wr t u) (Icc a b) := by
  have hder : ∀ s ∈ Icc a b, ∃ d > 0, HasDerivAt (transBdry Ψi w Wr t u) d s := fun s hs =>
    hasDerivAt_transBdry hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd (hU s hs)
  refine strictMonoOn_of_deriv_pos (convex_Icc a b) (fun s hs => ?_) (fun s hs => ?_)
  · obtain ⟨d, -, hd'⟩ := hder s hs
    exact hd'.continuousAt.continuousWithinAt
  · obtain ⟨d, hd0, hd'⟩ := hder s (interior_subset hs)
    rw [hd'.deriv]
    exact hd0

/-- **The tip identity**: the boundary value of the transition at `0` is `0`. -/
theorem transBdry_zero (htip : Tendsto (fun y => fwdMap w t (Ψi (fwdMapInv Wr u y))) (𝓝[H] 0) (𝓝 0)) :
    transBdry Ψi w Wr t u 0 = 0 := by
  have h0 : (0 : ℂ) ∈ closure H := by rw [closure_H]; exact ofReal_mem_Hbar 0
  have h : extendFrom H (fun y => fwdMap w t (jointInv Ψi Wr u y)) 0 = 0 := extendFrom_eq h0 htip
  simp only [transBdry, Complex.ofReal_zero, h, Complex.zero_re]

end Transition

end InteractingSLE.Supp8.RelTrans
