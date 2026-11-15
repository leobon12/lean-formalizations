/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BHMeanChart
import InteractingSLE.Spec.Sec6.DrivingArgLift
import InteractingSLE.Spec.ZhanGT4.CrosscutInterior
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal
import InteractingSLE.Spec.Supplement.GB6LawChain

/-!
# The boundary-hitting mean identification: retained sides and untouched real points

Packet PROVE-BHMEAN. At a real point `x` of the joint chart off the relative hull image (its landing point
`y = F̄̃_u(x)` lies off `cl K̃_u`; then `y` is real), the joint parametrization `Ψi ∘ f̃_u⁻¹` lands at a point `p`
of the retained set or of the real line with positive distance from the explored hull, and the retained mean minus the
candidate tends to `0`: it equals `G₀(Y) − G(y') + χ Im log f̃_u'(Y)` with `Y = f̃_u⁻¹(y') → y`, the relative word
at `x` is the retained word at `y` (`IsFlowedWord`), and the normalized argument vanishes at the untouched real point
`y` (Aux. lemma 57 / (CA2), `Sec6.tendsto_im_logDerivFwd_of_isForwardSol_real`). Only the relative chain enters; this
is the "untouched original-real interval / incoming flow side" part of Astra's Q3 §3.3.

* `exists_isForwardSol_of_notMem_closure`, `tendsto_im_logDerivFwd_of_notMem_closure`;
* `extendFrom_mem_Hbar`, `im_extendFrom_eq_zero_of_notMem_closure`;
* `eq_fwdMap_of_extendFrom_notMem_closure` (the landing point determines `x`, for the finite exceptional set);
* **`retained_side`** (the A-side alternative of `HasUnionWordBoundary`, along `𝓝[ℍ] x` in the joint chart).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd IsForwardSol)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Supp8.BHMean

/-! ### Real points off a closed Loewner hull -/

section Alive

variable {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {u : ℝ}

/-- **A real point off the closed hull, other than `0`, is alive** on `[0, u]`. -/
theorem exists_isForwardSol_of_notMem_closure (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u) {y : ℝ}
    (hy : (y : ℂ) ∉ closure (fwdHull Wr u)) (hy0 : y ≠ 0) : ∃ v, IsForwardSol Wr (y : ℂ) u v := by
  obtain ⟨r, hr, hball⟩ := GB6.exists_ball_disjoint_of_notMem_closure hy
  exact ZhanGT4.exists_isForwardSol_of_disjoint_ball hWr hWr0 hy0 hu hr hball

/-- **(CA2) at a real point off the closed hull**: `Im log f_u' → 0`. -/
theorem tendsto_im_logDerivFwd_of_notMem_closure (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u) {y : ℝ}
    (hy : (y : ℂ) ∉ closure (fwdHull Wr u)) :
    Tendsto (fun z => (logDerivFwd Wr u z).im) (𝓝[H] (y : ℂ)) (𝓝 0) := by
  rcases eq_or_ne y 0 with rfl | hy0
  · rcases hu.eq_or_lt with rfl | hpos
    · have e : (fun z => (logDerivFwd Wr 0 z).im) = fun _ => 0 := by
        funext z; simp [QuantumZipper.logDerivFwd]
      rw [e]; exact tendsto_const_nhds
    · exact absurd (by simpa using ConformalImageFull.zero_mem_closure_fwdHull hWr hWr0 hpos) hy
  · obtain ⟨v, hv⟩ := exists_isForwardSol_of_notMem_closure hWr hWr0 hu hy hy0
    exact Sec6.tendsto_im_logDerivFwd_of_isForwardSol_real hWr hu hv

/-- The boundary extension of the inverse map takes `ℍ̄` into `ℍ̄`. -/
theorem extendFrom_mem_Hbar (hηr : IsLoewnerTrace Wr ηr) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u)
    {x : ℂ} (hx : x ∈ Hbar) : extendFrom H (fwdMapInv Wr u) x ∈ Hbar := by
  have hlim := (hηr.hasBdryLimits hWr hWr0 hu).tendsto hx
  have : (𝓝[H] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ hx)
  rw [← closure_H]
  exact mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun w hw =>
    QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hw)

/-- **A landing point off the closed hull is real.** -/
theorem im_extendFrom_eq_zero_of_notMem_closure (hηr : IsLoewnerTrace Wr ηr) (hWr : Continuous Wr)
    (hWr0 : Wr 0 = 0) (hu : 0 ≤ u) {x : ℝ}
    (hy : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u)) :
    (extendFrom H (fwdMapInv Wr u) (x : ℂ)).im = 0 := by
  obtain ⟨-, -, -, hFR⟩ := hηr.fiber_hyps hWr hWr0 hu
  have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  refine le_antisymm (not_lt.1 fun hpos => hFR (x : ℂ) (by simp) ?_) (extendFrom_mem_Hbar hηr hWr hWr0 hu hxbar)
  have hmem : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∈ H \ fwdHull Wr u := ⟨hpos, fun h => hy (subset_closure h)⟩
  rw [← QuantumZipper.RS.image_fwdMapInv_H hWr hWr0 hu] at hmem
  obtain ⟨v, hv, hve⟩ := hmem
  exact ⟨v, hv, by rw [WangWu.extendFrom_fwdMapInv_eq hWr hWr0 hu hv, hve]⟩

/-- **The landing point determines the real point**: if `F̄_u(x) = y` lies off the closed hull, then
`x = Re f_u(Re y)` (for `Re y ≠ 0`). -/
theorem eq_fwdMap_of_extendFrom_notMem_closure (hηr : IsLoewnerTrace Wr ηr) (hWr : Continuous Wr)
    (hWr0 : Wr 0 = 0) (hu : 0 ≤ u) {x : ℝ}
    (hy : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u))
    (hy0 : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re ≠ 0) :
    x = (fwdMap Wr u ((extendFrom H (fwdMapInv Wr u) (x : ℂ)).re : ℂ)).re := by
  set y : ℂ := extendFrom H (fwdMapInv Wr u) (x : ℂ) with hydef
  have hyim : y.im = 0 := im_extendFrom_eq_zero_of_notMem_closure hηr hWr hWr0 hu hy
  have hyr : y = (y.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hyim]
  have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hlimF : Tendsto (fwdMapInv Wr u) (𝓝[H] (x : ℂ)) (𝓝[H] y) :=
    tendsto_nhdsWithin_iff.2 ⟨(hηr.hasBdryLimits hWr hWr0 hu).tendsto hxbar,
      eventually_nhdsWithin_of_forall fun w hw => QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hw⟩
  have hy' : ((y.re : ℝ) : ℂ) ∉ closure (fwdHull Wr u) := by rw [← hyr]; exact hy
  -- the limit of `f_u` at `y`
  have hlimf : ∃ c, Tendsto (fwdMap Wr u) (𝓝[H] y) (𝓝 c) ∧ c = fwdMap Wr u (y.re : ℂ) := by
    obtain ⟨v, hv⟩ := exists_isForwardSol_of_notMem_closure hWr hWr0 hu hy' hy0
    refine ⟨v u, ?_, (fwdMap_eq_of_isForwardSol hWr hv ⟨hu, le_rfl⟩).symm⟩
    rw [hyr]; exact tendsto_fwdMap_of_isForwardSol hWr hu hv
  obtain ⟨c, hc, hce⟩ := hlimf
  have hcomp : Tendsto (fun w => fwdMap Wr u (fwdMapInv Wr u w)) (𝓝[H] (x : ℂ)) (𝓝 c) := hc.comp hlimF
  have hid : Tendsto (fun w => fwdMap Wr u (fwdMapInv Wr u w)) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (eventually_nhdsWithin_of_forall fun w hw =>
      (QuantumZipper.RS.fwdMap_fwdMapInv hWr hWr0 hu hw).symm)
  have : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ hxbar)
  have hxc : (x : ℂ) = c := tendsto_nhds_unique hid hcomp
  rw [← hce, ← hxc]; simp

end Alive

/-! ### The retained-side alternative -/

section Retained

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {w Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {t u χ : ℝ}
  {β₀ βu : ℝ → ℝ} {S₀ Su : Finset ℝ} {G₀ G u₀ w₁ : ℂ → ℝ}

/-- A point of `ℍ ∖ A` is never the landing point of `Ψi` at a real point. -/
theorem notMem_compl_of_tendsto_inv (hΨ : IsRetainedChart A Ψ Ψi LΨ) {y p : ℂ} (hy : y.im = 0)
    (hp : Tendsto Ψi (𝓝[H] y) (𝓝 p)) : p ∉ H \ A := by
  intro hpA
  have hyb : y ∈ Hbar := show (0 : ℝ) ≤ y.im from hy.ge
  have : (𝓝[H] y).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ hyb)
  have hc : ContinuousAt Ψ p := (hΨ.conf.1.differentiableAt (hΨ.isOpen.mem_nhds hpA)).continuousAt
  have h1 : Tendsto (fun v => Ψ (Ψi v)) (𝓝[H] y) (𝓝 (Ψ p)) := hc.tendsto.comp hp
  have h2 : Tendsto (fun v => Ψ (Ψi v)) (𝓝[H] y) (𝓝 y) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (eventually_nhdsWithin_of_forall fun v hv =>
      (hΨ.fwd_inv v hv).symm)
  have he : Ψ p = y := tendsto_nhds_unique h1 h2
  have hpos : 0 < (Ψ p).im := hΨ.conf.2.mapsTo hpA
  rw [he, hy] at hpos
  exact lt_irrefl _ hpos

/-- **The retained-side alternative** of `HasUnionWordBoundary` at a real point `x` of the joint chart off the
relative hull image: the joint parametrization lands at a point `p` of `A ∪ ℝ` off the closed explored hull, and the
retained mean minus the candidate tends to `0`. -/
theorem retained_side (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    (hG₀ : IsBoundedHarmonicExtension β₀ S₀ G₀) (hG : IsBoundedHarmonicExtension βu Su G)
    (hflow : IsFlowedWord βu β₀ Su S₀ (fwdMapInv Wr u) (fwdHull Wr u))
    (hw₁ : EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ (Ψ z) - χ * (LΨ z).im) (H \ A))
    {x : ℝ} (hxS : x ∉ Su) (hy : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u))
    (hyS : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re ∉ S₀) :
    ∃ p : ℂ, Tendsto (jointInv Ψi Wr u) (𝓝[H] (x : ℂ)) (𝓝 p) ∧ p ∈ A ∪ {z : ℂ | z.im = 0} ∧
      (∃ r > 0, fwdHull w t ∩ ball p r ⊆ A) ∧
      Tendsto (fun y => (w₁ (jointInv Ψi Wr u y) + u₀ (jointInv Ψi Wr u y)) -
        (G (jointFwd Ψ Wr u (jointInv Ψi Wr u y)) - χ * jointLift Ψ LΨ Wr u (jointInv Ψi Wr u y)))
        (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set yc : ℂ := extendFrom H (fwdMapInv Wr u) (x : ℂ) with hycdef
  have hyim : yc.im = 0 := im_extendFrom_eq_zero_of_notMem_closure hηr hWr hWr0 hu hy
  have hyr : yc = (yc.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hyim]
  have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hlimF : Tendsto (fwdMapInv Wr u) (𝓝[H] (x : ℂ)) (𝓝[H] yc) :=
    tendsto_nhdsWithin_iff.2 ⟨(hηr.hasBdryLimits hWr hWr0 hu).tendsto hxbar,
      eventually_nhdsWithin_of_forall fun v hv => QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hv⟩
  obtain ⟨p, hp⟩ := hΨ.inv_lands yc.re
  rw [← hyr] at hp
  have hjoint : Tendsto (jointInv Ψi Wr u) (𝓝[H] (x : ℂ)) (𝓝 p) := hp.comp hlimF
  have hycb : yc ∈ Hbar := show (0 : ℝ) ≤ yc.im from hyim.ge
  have hNe : (𝓝[H] yc).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ hycb)
  have hpbar : p ∈ Hbar := by
    rw [← closure_H]
    exact mem_closure_of_tendsto hp (eventually_nhdsWithin_of_forall fun v hv => (hΨ.inv_mem v hv).1)
  have hpC : p ∉ H \ A := notMem_compl_of_tendsto_inv hΨ hyim hp
  -- `p ∈ A ∪ ℝ`
  have hpAR : p ∈ A ∪ {z : ℂ | z.im = 0} := by
    by_cases hpA : p ∈ A
    · exact Or.inl hpA
    · refine Or.inr (le_antisymm (not_lt.1 fun hpos => hpC ⟨hpos, hpA⟩) hpbar)
  -- `p` is off the closed explored hull
  have hpK : p ∉ closure (fwdHull w t) := by
    intro hpK
    have hpA' : p ∉ closure A := Set.disjoint_left.1 hd hpK
    have hpre : p.im = 0 := by
      rcases hpAR with h | h
      · exact absurd (subset_closure h) hpA'
      · exact h
    have hpr : p = (p.re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hpre]
    obtain ⟨x', hx'⟩ := hΨ.fwd_lands p.re (by rw [← hpr]; exact hpA')
    rw [← hpr] at hx'
    have hpw : Tendsto Ψi (𝓝[H] yc) (𝓝[H \ A] p) :=
      tendsto_nhdsWithin_iff.2 ⟨hp, eventually_nhdsWithin_of_forall fun v hv => hΨ.inv_mem v hv⟩
    have h1 : Tendsto (fun v => Ψ (Ψi v)) (𝓝[H] yc) (𝓝 (x' : ℂ)) := hx'.comp hpw
    have h2 : Tendsto (fun v => Ψ (Ψi v)) (𝓝[H] yc) (𝓝 yc) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (eventually_nhdsWithin_of_forall fun v hv =>
        (hΨ.fwd_inv v hv).symm)
    have hx'y : (x' : ℂ) = yc := tendsto_nhds_unique h1 h2
    apply hy
    have hKsub : fwdHull w t ⊆ H \ A := fwdHull_subset_compl hd hw ht
    have hNeK : (𝓝[fwdHull w t] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hpK
    have h3 : Tendsto Ψ (𝓝[fwdHull w t] p) (𝓝 (x' : ℂ)) := hx'.mono_left (nhdsWithin_mono p hKsub)
    rw [← hx'y]
    exact mem_closure_of_tendsto h3 (eventually_nhdsWithin_of_forall fun z hz => hK ▸ mem_image_of_mem Ψ hz)
  obtain ⟨r, hr, hball⟩ := GB6.exists_ball_disjoint_of_notMem_closure hpK
  refine ⟨p, hjoint, hpAR, ⟨r, hr, fun z hz => absurd hz.1 (Set.disjoint_left.1 hball hz.2)⟩, ?_⟩
  -- the limit
  have hyK : ((yc.re : ℝ) : ℂ) ∉ closure (fwdHull Wr u) := by rw [← hyr]; exact hy
  have hL0 : Tendsto (fun v => (logDerivFwd Wr u (fwdMapInv Wr u v)).im) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    have := tendsto_im_logDerivFwd_of_notMem_closure hWr hWr0 hu hyK
    rw [← hyr] at this
    exact this.comp hlimF
  have hG₀l : Tendsto (fun v => G₀ (fwdMapInv Wr u v)) (𝓝[H] (x : ℂ)) (𝓝 (β₀ yc.re)) := by
    have := hG₀.2.2 yc.re hyS
    rw [← hyr] at this
    exact this.comp hlimF
  have hGl : Tendsto G (𝓝[H] (x : ℂ)) (𝓝 (βu x)) := hG.2.2 x hxS
  have hsum := (hG₀l.sub hGl).add (hL0.const_mul χ)
  rw [hflow x hxS hy hyS, sub_self, mul_zero, add_zero] at hsum
  refine hsum.congr' (eventually_nhdsWithin_of_forall fun v hv => ?_)
  have hFv := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu hv
  have hJ : jointInv Ψi Wr u v ∈ H \ A := hΨ.inv_mem _ hFv.1
  have hΨJ : Ψ (jointInv Ψi Wr u v) = fwdMapInv Wr u v := hΨ.fwd_inv _ hFv.1
  have e1 := hw₁ hJ
  simp only at e1
  simp only [jointLift, jointFwd_jointInv hΨ hw ht hWr hWr0 hu hK hd hv, e1, hΨJ]
  ring

end Retained

end InteractingSLE.Supp8.BHMean
