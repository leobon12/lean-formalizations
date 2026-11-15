/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BHMean

/-!
# The boundary-hitting mean identification with a retained chart landing off a finite set: the chart layer

Packet PROVE-Q3-REL. PROVE-BHMEAN's `BHMean.IsRetainedChart` asks that the inverse `Ψi` of the retained chart land at
**every** real point. In the two configurations the statement was made for (GB6: retained = the flow prefix read in
the counterflow's frame `w = −1/z`; GW2: retained = the counterflow prefix read in the flow's frame) the retained set is
the inversion of a hull started at `0`, so it is **unbounded**: the prime ends of `ℍ ∖ A` at `∞` (the two sides of the
retained curve's base, when the base is not swallowed) are sent by `Ψ` to finitely many real points, and `Ψi` tends to
`∞` there (for GB6, `relInv U σ v = −1/f_σ⁻¹(−1/v)` and `f̄_σ⁻¹(−1/v) = 0` at the images of the base's two sides).

This file restates the chart with **finitely many exceptional real points** `Sb` (`IsRetainedChartOff`: `Ψi` lands at
every real point off `Sb`) and re-proves, for it, the chart and side lemmas of `BHMeanChart`, `BHMeanReal` and
`BHMeanSide` (same statements and proofs; the two landing uses get the side condition: off `Sb` on the retained side,
and on the closed relative hull, which misses `Sb`, on the explored side).

Deterministic. Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE.Supp8.Q3Rel

open BHMean (jointInv jointFwd jointLift jointChart jointLog IsSideWord IsFlowedWord)

/-- **The chart of the retained component, landing off a finite set**: `BHMean.IsRetainedChart` with the inverse `Ψi`
required to land only at the real points off the finite set `Sb`, and the lift's boundary values required only at real
points other than `0` (the base of the explored chain, which lies in every closed explored hull of positive time). -/
structure IsRetainedChartOff (A : Set ℂ) (Ψ Ψi LΨ : ℂ → ℂ) (Sb : Finset ℝ) : Prop where
  isOpen : IsOpen (H \ A)
  conf : IsConformalBijection Ψ (H \ A) H
  inv_mem : ∀ v ∈ H, Ψi v ∈ H \ A
  fwd_inv : ∀ v ∈ H, Ψ (Ψi v) = v
  diff_inv : DifferentiableOn ℂ Ψi H
  log : IsDerivLog Ψ LΨ (H \ A)
  inv_lands : ∀ x : ℝ, x ∉ Sb → ∃ p, Tendsto Ψi (𝓝[H] (x : ℂ)) (𝓝 p)
  fwd_lands : ∀ y : ℝ, (y : ℂ) ∉ closure A → ∃ x : ℝ, Tendsto Ψ (𝓝[H \ A] (y : ℂ)) (𝓝 (x : ℂ))
  lift_real : ∀ y : ℝ, y ≠ 0 → (y : ℂ) ∉ closure A → Tendsto (fun z => (LΨ z).im) (𝓝[H \ A] (y : ℂ)) (𝓝 0)

/-- A chart landing everywhere is a chart landing off the empty set. -/
theorem _root_.InteractingSLE.Supp8.BHMean.IsRetainedChart.off {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ}
    (hΨ : BHMean.IsRetainedChart A Ψ Ψi LΨ) : IsRetainedChartOff A Ψ Ψi LΨ ∅ :=
  ⟨hΨ.isOpen, hΨ.conf, hΨ.inv_mem, hΨ.fwd_inv, hΨ.diff_inv, hΨ.log, fun x _ => hΨ.inv_lands x, hΨ.fwd_lands,
    fun y _ => hΨ.lift_real y⟩

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u χ lam : ℝ}
  {β₀ βE βu : ℝ → ℝ} {S₀ SE Su : Finset ℝ} {G₀ GE G u₀ w₁ w₂ v : ℂ → ℝ}

theorem IsRetainedChartOff.inv_fwd (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) {z : ℂ} (hz : z ∈ H \ A) : Ψi (Ψ z) = z :=
  hΨ.conf.2.injOn (hΨ.inv_mem _ (hΨ.conf.2.mapsTo hz)) hz (hΨ.fwd_inv _ (hΨ.conf.2.mapsTo hz))

section Chart

variable (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (ht : 0 ≤ t)
  (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u)
  (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))

include hΨ hw ht hWr hWr0 hu hK hd


theorem mem_C_iff {z : ℂ} : z ∈ H \ (A ∪ fwdHull w t) ↔ z ∈ H \ A ∧ Ψ z ∈ H \ fwdHull Wr u := by
  constructor
  · rintro ⟨hzH, hzn⟩
    have hzA : z ∈ H \ A := ⟨hzH, fun h => hzn (Or.inl h)⟩
    refine ⟨hzA, hΨ.conf.2.mapsTo hzA, fun hK' => ?_⟩
    rw [← hK] at hK'
    obtain ⟨z', hz', he⟩ := hK'
    have := hΨ.conf.2.injOn (BHMean.fwdHull_subset_compl hd hw ht hz') hzA he
    exact hzn (Or.inr (this ▸ hz'))
  · rintro ⟨⟨hzH, hzA⟩, -, hzK⟩
    refine ⟨hzH, ?_⟩
    rintro (h | h)
    · exact hzA h
    · exact hzK (hK ▸ mem_image_of_mem Ψ h)

theorem jointInv_mem {y : ℂ} (hy : y ∈ H) : jointInv Ψi Wr u y ∈ H \ (A ∪ fwdHull w t) := by
  have h1 := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu hy
  rw [mem_C_iff hΨ hw ht hWr hWr0 hu hK hd]
  refine ⟨hΨ.inv_mem _ h1.1, ?_⟩
  simp only [jointInv]
  rw [hΨ.fwd_inv _ h1.1]
  exact h1

theorem jointFwd_mem {z : ℂ} (hz : z ∈ H \ (A ∪ fwdHull w t)) : jointFwd Ψ Wr u z ∈ H :=
  QuantumZipper.FwdHolo.mapsTo_fwdMap hWr hu ((mem_C_iff hΨ hw ht hWr hWr0 hu hK hd).1 hz).2

theorem jointFwd_jointInv {y : ℂ} (hy : y ∈ H) : jointFwd Ψ Wr u (jointInv Ψi Wr u y) = y := by
  have h1 := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu hy
  simp only [jointFwd, jointInv]
  rw [hΨ.fwd_inv _ h1.1, QuantumZipper.RS.fwdMap_fwdMapInv hWr hWr0 hu hy]

theorem jointInv_jointFwd {z : ℂ} (hz : z ∈ H \ (A ∪ fwdHull w t)) : jointInv Ψi Wr u (jointFwd Ψ Wr u z) = z := by
  obtain ⟨hzA, hzK⟩ := (mem_C_iff hΨ hw ht hWr hWr0 hu hK hd).1 hz
  simp only [jointFwd, jointInv]
  rw [QuantumZipper.RS.fwdMapInv_fwdMap hWr hWr0 hu hzK, hΨ.inv_fwd hzA]

theorem continuousOn_jointInv : ContinuousOn (jointInv Ψi Wr u) H :=
  hΨ.diff_inv.continuousOn.comp (isConformalBijection_fwdMapInv hWr hWr0 hu).1.continuousOn
    fun _ hy => (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu hy).1

theorem image_jointInv : jointInv Ψi Wr u '' H = H \ (A ∪ fwdHull w t) := by
  refine Subset.antisymm ?_ fun z hz => ⟨jointFwd Ψ Wr u z, jointFwd_mem hΨ hw ht hWr hWr0 hu hK hd hz,
    jointInv_jointFwd hΨ hw ht hWr hWr0 hu hK hd hz⟩
  rintro _ ⟨y, hy, rfl⟩
  exact jointInv_mem hΨ hw ht hWr hWr0 hu hK hd hy

theorem isPreconnected_C : IsPreconnected (H \ (A ∪ fwdHull w t)) := by
  rw [← image_jointInv hΨ hw ht hWr hWr0 hu hK hd]
  exact (convex_halfSpace_im_gt 0).isPreconnected.image _ (continuousOn_jointInv hΨ hw ht hWr hWr0 hu hK hd)

theorem connectedComponentIn_C {z₀ : ℂ} (hz₀ : z₀ ∈ H \ (A ∪ fwdHull w t)) :
    connectedComponentIn (H \ (A ∪ fwdHull w t)) z₀ = H \ (A ∪ fwdHull w t) :=
  (isPreconnected_C hΨ hw ht hWr hWr0 hu hK hd).connectedComponentIn hz₀

theorem differentiableAt_jointFwd {z : ℂ} (hz : z ∈ H \ (A ∪ fwdHull w t)) :
    DifferentiableAt ℂ (jointFwd Ψ Wr u) z := by
  obtain ⟨hzA, hzK⟩ := (mem_C_iff hΨ hw ht hWr hWr0 hu hK hd).1 hz
  have h1 : DifferentiableAt ℂ (fwdMap Wr u) (Ψ z) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWr hu).differentiableAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWr hu).mem_nhds hzK)
  have h2 : DifferentiableAt ℂ Ψ z := hΨ.conf.1.differentiableAt (hΨ.isOpen.mem_nhds hzA)
  exact h1.comp z h2

theorem isConformalBijection_jointFwd :
    IsConformalBijection (jointFwd Ψ Wr u) (H \ (A ∪ fwdHull w t)) H := by
  refine ⟨fun z hz => (differentiableAt_jointFwd hΨ hw ht hWr hWr0 hu hK hd hz).differentiableWithinAt,
    ⟨fun z hz => jointFwd_mem hΨ hw ht hWr hWr0 hu hK hd hz, fun z hz z' hz' he => ?_, fun y hy => ?_⟩⟩
  · rw [← jointInv_jointFwd hΨ hw ht hWr hWr0 hu hK hd hz, he, jointInv_jointFwd hΨ hw ht hWr hWr0 hu hK hd hz']
  · exact ⟨jointInv Ψi Wr u y, jointInv_mem hΨ hw ht hWr hWr0 hu hK hd hy,
      jointFwd_jointInv hΨ hw ht hWr hWr0 hu hK hd hy⟩

/-- **The disk parametrization of the joint complement**: `jointInv ∘ cayleyInv : 𝔻 → C`. -/
theorem isConformalBijection_diskInv :
    IsConformalBijection (fun ζ => jointInv Ψi Wr u (cayleyInv ζ)) (ball 0 1) (H \ (A ∪ fwdHull w t)) := by
  have hc1 : ∀ ζ ∈ ball (0 : ℂ) 1, ζ ≠ 1 := fun ζ hζ h => by
    rw [h, mem_ball, dist_zero_right, norm_one] at hζ; exact lt_irrefl _ hζ
  refine ⟨?_, ⟨fun ζ hζ => jointInv_mem hΨ hw ht hWr hWr0 hu hK hd (QuantumZipper.CA.cayleyInv_mem_H hζ),
    fun ζ hζ ζ' hζ' he => ?_, fun z hz => ?_⟩⟩
  · intro ζ hζ
    have hy := QuantumZipper.CA.cayleyInv_mem_H hζ
    have h1 : DifferentiableAt ℂ (fwdMapInv Wr u) (cayleyInv ζ) :=
      (isConformalBijection_fwdMapInv hWr hWr0 hu).1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hy)
    have h2 : DifferentiableAt ℂ Ψi (fwdMapInv Wr u (cayleyInv ζ)) :=
      hΨ.diff_inv.differentiableAt (QuantumZipper.isOpen_H.mem_nhds
        (QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hy))
    exact (h2.comp ζ (h1.comp ζ (QuantumZipper.CA.differentiableAt_cayleyInv (hc1 ζ hζ)))).differentiableWithinAt
  · have he' := congrArg (jointFwd Ψ Wr u) he
    simp only at he'
    rw [jointFwd_jointInv hΨ hw ht hWr hWr0 hu hK hd (QuantumZipper.CA.cayleyInv_mem_H hζ),
      jointFwd_jointInv hΨ hw ht hWr hWr0 hu hK hd (QuantumZipper.CA.cayleyInv_mem_H hζ')] at he'
    rw [← QuantumZipper.CA.cayley_cayleyInv (hc1 ζ hζ), he', QuantumZipper.CA.cayley_cayleyInv (hc1 ζ' hζ')]
  · have hy := jointFwd_mem hΨ hw ht hWr hWr0 hu hK hd hz
    refine ⟨cayley (jointFwd Ψ Wr u z), QuantumZipper.CA.cayley_mem_ball hy, ?_⟩
    simp only
    rw [QuantumZipper.CA.cayleyInv_cayley (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (le_of_lt hy)),
      jointInv_jointFwd hΨ hw ht hWr hWr0 hu hK hd hz]

theorem continuousOn_jointLift : ContinuousOn (jointLift Ψ LΨ Wr u) (H \ (A ∪ fwdHull w t)) := by
  intro z hz
  obtain ⟨hzA, hzK⟩ := (mem_C_iff hΨ hw ht hWr hWr0 hu hK hd).1 hz
  have hΨc : ContinuousAt Ψ z := (hΨ.conf.1.differentiableAt (hΨ.isOpen.mem_nhds hzA)).continuousAt
  have h1 : ContinuousAt (fun z => (logDerivFwd Wr u (Ψ z)).im) z :=
    continuous_im.continuousAt.comp ((continuousAt_logDerivFwd hWr hu hzK).comp hΨc)
  have h2 : ContinuousAt (fun z => (LΨ z).im) z :=
    continuous_im.continuousAt.comp (hΨ.log.1.differentiableAt (hΨ.isOpen.mem_nhds hzA)).continuousAt
  exact (h1.add h2).continuousWithinAt

/-- **The inherited argument of the joint chart**: `jointFwd' = ‖jointFwd'‖ e^{i L}` with `L = jointLift`. -/
theorem deriv_jointFwd {z : ℂ} (hz : z ∈ H \ (A ∪ fwdHull w t)) :
    deriv (jointFwd Ψ Wr u) z = ‖deriv (jointFwd Ψ Wr u) z‖ * Complex.exp (jointLift Ψ LΨ Wr u z * Complex.I) := by
  obtain ⟨hzA, hzK⟩ := (mem_C_iff hΨ hw ht hWr hWr0 hu hK hd).1 hz
  have h1 : DifferentiableAt ℂ (fwdMap Wr u) (Ψ z) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWr hu).differentiableAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWr hu).mem_nhds hzK)
  have h2 : DifferentiableAt ℂ Ψ z := hΨ.conf.1.differentiableAt (hΨ.isOpen.mem_nhds hzA)
  have hchain : deriv (jointFwd Ψ Wr u) z = deriv (fwdMap Wr u) (Ψ z) * deriv Ψ z :=
    deriv_comp z h1 h2
  have e1 := (isDerivLog_fwdMap hWr hu).2 (Ψ z) hzK
  have e2 := hΨ.log.2 z hzA
  set a : ℂ := logDerivFwd Wr u (Ψ z) + LΨ z with ha
  have hexp : deriv (jointFwd Ψ Wr u) z = Complex.exp a := by
    rw [hchain, ← e1, ← e2, ha, Complex.exp_add]
  have hL : jointLift Ψ LΨ Wr u z = a.im := by simp only [jointLift, ha, Complex.add_im]
  rw [hexp, hL, Complex.norm_exp]
  conv_lhs => rw [← Complex.re_add_im a]
  rw [Complex.exp_add, Complex.ofReal_exp]

end Chart

/-! ### The retained and explored sides; the joint chart and its local integer -/

/-- A point of `ℍ ∖ A` is never the landing point of `Ψi` at a real point. -/
theorem notMem_compl_of_tendsto_inv (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) {y p : ℂ} (hy : y.im = 0)
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
theorem retained_side (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    (hG₀ : IsBoundedHarmonicExtension β₀ S₀ G₀) (hG : IsBoundedHarmonicExtension βu Su G)
    (hflow : IsFlowedWord βu β₀ Su S₀ (fwdMapInv Wr u) (fwdHull Wr u))
    (hw₁ : EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ (Ψ z) - χ * (LΨ z).im) (H \ A))
    {x : ℝ} (hxS : x ∉ Su) (hy : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u))
    (hyS : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re ∉ S₀) (hyb : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re ∉ Sb) :
    ∃ p : ℂ, Tendsto (jointInv Ψi Wr u) (𝓝[H] (x : ℂ)) (𝓝 p) ∧ p ∈ A ∪ {z : ℂ | z.im = 0} ∧
      (∃ r > 0, fwdHull w t ∩ ball p r ⊆ A) ∧
      Tendsto (fun y => (w₁ (jointInv Ψi Wr u y) + u₀ (jointInv Ψi Wr u y)) -
        (G (jointFwd Ψ Wr u (jointInv Ψi Wr u y)) - χ * jointLift Ψ LΨ Wr u (jointInv Ψi Wr u y)))
        (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set yc : ℂ := extendFrom H (fwdMapInv Wr u) (x : ℂ) with hycdef
  have hyim : yc.im = 0 := BHMean.im_extendFrom_eq_zero_of_notMem_closure hηr hWr hWr0 hu hy
  have hyr : yc = (yc.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hyim]
  have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hlimF : Tendsto (fwdMapInv Wr u) (𝓝[H] (x : ℂ)) (𝓝[H] yc) :=
    tendsto_nhdsWithin_iff.2 ⟨(hηr.hasBdryLimits hWr hWr0 hu).tendsto hxbar,
      eventually_nhdsWithin_of_forall fun v hv => QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hv⟩
  obtain ⟨p, hp⟩ := hΨ.inv_lands yc.re hyb
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
    have hKsub : fwdHull w t ⊆ H \ A := BHMean.fwdHull_subset_compl hd hw ht
    have hNeK : (𝓝[fwdHull w t] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hpK
    have h3 : Tendsto Ψ (𝓝[fwdHull w t] p) (𝓝 (x' : ℂ)) := hx'.mono_left (nhdsWithin_mono p hKsub)
    rw [← hx'y]
    exact mem_closure_of_tendsto h3 (eventually_nhdsWithin_of_forall fun z hz => hK ▸ mem_image_of_mem Ψ hz)
  obtain ⟨r, hr, hball⟩ := GB6.exists_ball_disjoint_of_notMem_closure hpK
  refine ⟨p, hjoint, hpAR, ⟨r, hr, fun z hz => absurd hz.1 (Set.disjoint_left.1 hball hz.2)⟩, ?_⟩
  -- the limit
  have hyK : ((yc.re : ℝ) : ℂ) ∉ closure (fwdHull Wr u) := by rw [← hyr]; exact hy
  have hL0 : Tendsto (fun v => (logDerivFwd Wr u (fwdMapInv Wr u v)).im) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    have := BHMean.tendsto_im_logDerivFwd_of_notMem_closure hWr hWr0 hu hyK
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


/-- **The joint parametrization lands on the closed explored hull** at a real point of the relative hull image. -/
theorem landing_mem_closure (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (ht : 0 ≤ t)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    (hWr : Continuous Wr) (hu : 0 ≤ u) {y p : ℂ} (hy : y ∈ closure (fwdHull Wr u))
    (hp : Tendsto Ψi (𝓝[H] y) (𝓝 p)) : p ∈ closure (fwdHull w t) := by
  have hKH : fwdHull Wr u ⊆ H := (isHPHull_fwdHull hWr hu).1
  have hNe : (𝓝[fwdHull Wr u] y).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hy
  have h1 : Tendsto Ψi (𝓝[fwdHull Wr u] y) (𝓝 p) := hp.mono_left (nhdsWithin_mono y hKH)
  refine mem_closure_of_tendsto h1 (eventually_nhdsWithin_of_forall fun v hv => ?_)
  rw [← hK] at hv
  obtain ⟨z, hz, rfl⟩ := hv
  rw [hΨ.inv_fwd (BHMean.fwdHull_subset_compl hd hw ht hz)]
  exact hz

/-- **The explored-side alternative** of `HasUnionWordBoundary` at a real point `x ≠ 0` of the relative hull image
(off the jumps of `βu`, with `T x` off the jumps of `βE`): the joint parametrization lands at a point `p` of `K_t ∪ ℝ`
off the closed retained set, and the explored mean minus the candidate tends to `0`. -/
theorem explored_side (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    (hSbK : ∀ b ∈ Sb, (b : ℂ) ∉ closure (fwdHull Wr u))
    (hGE : IsBoundedHarmonicExtension βE SE GE) (hG : IsBoundedHarmonicExtension βu Su G)
    (hsE : IsSideWord βE SE (fwdMapInv w t) (fwdHull w t) lam)
    (hsu : IsSideWord βu Su (fwdMapInv Wr u) (fwdHull Wr u) lam)
    (hw₂ : EqOn (fun z => w₂ z + u₀ z) (fun z => GE (fwdMap w t z) - χ * (logDerivFwd w t z).im)
      (H \ fwdHull w t))
    {T : ℝ → ℝ} {x : ℝ} (hx0 : x ≠ 0) (hxK : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∈ closure (fwdHull Wr u))
    (hxS : x ∉ Su) (hTS : T x ∉ SE) (hsign : 0 < T x ↔ 0 < x) (hT0 : T x ≠ 0)
    (hTK : extendFrom H (fwdMapInv w t) (T x : ℂ) ∈ closure (fwdHull w t))
    (hTl : Tendsto (fun y => fwdMap w t (jointInv Ψi Wr u y)) (𝓝[H] (x : ℂ)) (𝓝 (T x : ℂ)))
    (hLl : Tendsto (fun y => (logDerivFwd w t (jointInv Ψi Wr u y)).im - jointLift Ψ LΨ Wr u (jointInv Ψi Wr u y))
      (𝓝[H] (x : ℂ)) (𝓝 0)) :
    ∃ p : ℂ, Tendsto (jointInv Ψi Wr u) (𝓝[H] (x : ℂ)) (𝓝 p) ∧ p ∈ fwdHull w t ∪ {z : ℂ | z.im = 0} ∧
      (∃ r > 0, A ∩ ball p r ⊆ fwdHull w t) ∧
      Tendsto (fun y => (w₂ (jointInv Ψi Wr u y) + u₀ (jointInv Ψi Wr u y)) -
        (G (jointFwd Ψ Wr u (jointInv Ψi Wr u y)) - χ * jointLift Ψ LΨ Wr u (jointInv Ψi Wr u y)))
        (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set yc : ℂ := extendFrom H (fwdMapInv Wr u) (x : ℂ) with hycdef
  have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hycb : yc ∈ Hbar := BHMean.extendFrom_mem_Hbar hηr hWr hWr0 hu hxbar
  have hlimF : Tendsto (fwdMapInv Wr u) (𝓝[H] (x : ℂ)) (𝓝[H] yc) :=
    tendsto_nhdsWithin_iff.2 ⟨(hηr.hasBdryLimits hWr hWr0 hu).tendsto hxbar,
      eventually_nhdsWithin_of_forall fun v hv => QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hv⟩
  -- the landing point of `Ψi` at `yc`
  have hland : ∃ p, Tendsto Ψi (𝓝[H] yc) (𝓝 p) := by
    by_cases hyH : yc ∈ H
    · exact ⟨Ψi yc, (hΨ.diff_inv.continuousOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds hyH)).tendsto.mono_left
        nhdsWithin_le_nhds⟩
    · have hyim : yc.im = 0 := le_antisymm (not_lt.1 hyH) hycb
      have hyr : yc = (yc.re : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hyim]
      obtain ⟨p, hp⟩ := hΨ.inv_lands yc.re fun hb => hSbK _ hb (by rw [← hyr]; exact hxK)
      rw [← hyr] at hp
      exact ⟨p, hp⟩
  obtain ⟨p, hp⟩ := hland
  have hjoint : Tendsto (jointInv Ψi Wr u) (𝓝[H] (x : ℂ)) (𝓝 p) := hp.comp hlimF
  have hpK : p ∈ closure (fwdHull w t) := landing_mem_closure hΨ hw ht hK hd hWr hu hxK hp
  have hpA : p ∉ closure A := Set.disjoint_left.1 hd hpK
  have hpbar : p ∈ Hbar := by
    rw [← closure_H]; exact closure_mono (isHPHull_fwdHull hw ht).1 hpK
  have hpKR : p ∈ fwdHull w t ∪ {z : ℂ | z.im = 0} := by
    by_cases hpH : p ∈ H
    · left
      by_contra hpn
      have hopen : IsOpen (H \ fwdHull w t) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw ht
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen p ⟨hpH, hpn⟩
      obtain ⟨z, hzK, hzb⟩ := Metric.mem_closure_iff.1 hpK r hr
      exact (hball (by rw [mem_ball, dist_comm]; exact hzb)).2 hzK
    · exact Or.inr (le_antisymm (not_lt.1 hpH) hpbar)
  obtain ⟨r, hr, hball⟩ := GB6.exists_ball_disjoint_of_notMem_closure hpA
  refine ⟨p, hjoint, hpKR, ⟨r, hr, fun z hz => absurd hz.1 (Set.disjoint_left.1 hball hz.2)⟩, ?_⟩
  -- the limit
  have hJC : ∀ y ∈ H, jointInv Ψi Wr u y ∈ H \ fwdHull w t := fun y hy => by
    have h := jointInv_mem hΨ hw ht hWr hWr0 hu hK hd hy
    exact ⟨h.1, fun hk => h.2 (Or.inr hk)⟩
  have hTH : Tendsto (fun y => fwdMap w t (jointInv Ψi Wr u y)) (𝓝[H] (x : ℂ)) (𝓝[H] (T x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hTl, eventually_nhdsWithin_of_forall fun y hy =>
      QuantumZipper.FwdHolo.mapsTo_fwdMap hw ht (hJC y hy)⟩
  have hGEl := (hGE.2.2 (T x) hTS).comp hTH
  have hGl : Tendsto G (𝓝[H] (x : ℂ)) (𝓝 (βu x)) := hG.2.2 x hxS
  have hsum := (hGEl.sub hGl).sub (hLl.const_mul χ)
  have hβ : βE (T x) = βu x := by
    rw [hsE (T x) hTS hT0 hTK, hsu x hxS hx0 hxK]
    simp only [hsign]
  rw [hβ, sub_self, mul_zero, sub_zero] at hsum
  refine hsum.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  have e2 := hw₂ (hJC y hy)
  simp only at e2
  simp only [Function.comp, jointLift, jointFwd_jointInv hΨ hw ht hWr hWr0 hu hK hd hy, e2]
  ring


theorem isConformal_jointChart (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A)) :
    (jointChart Ψ Ψi LΨ Wr u).IsConformal := by
  refine ⟨?_, fun y hy => (jointInv_mem hΨ hw ht hWr hWr0 hu hK hd hy).1, fun y hy =>
    jointFwd_jointInv hΨ hw ht hWr hWr0 hu hK hd hy⟩
  have h := (isConformalBijection_diskInv hΨ hw ht hWr hWr0 hu hK hd).1
  intro y hy
  have hF : DifferentiableAt ℂ (fwdMapInv Wr u) y :=
    (isConformalBijection_fwdMapInv hWr hWr0 hu).1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hy)
  have hP : DifferentiableAt ℂ Ψi (fwdMapInv Wr u y) :=
    hΨ.diff_inv.differentiableAt (QuantumZipper.isOpen_H.mem_nhds (QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hy))
  exact (hP.comp y hF).differentiableWithinAt

theorem coe_dom_jointChart (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A)) :
    ((jointChart Ψ Ψi LΨ Wr u).dom : Set ℂ) = H \ (A ∪ fwdHull w t) := by
  rw [(isConformal_jointChart hΨ hw ht hWr hWr0 hu hK hd).coe_dom]
  exact image_jointInv hΨ hw ht hWr hWr0 hu hK hd

theorem isDerivLog_jointLog (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A)) :
    IsDerivLog (jointFwd Ψ Wr u) (jointLog Ψ LΨ Wr u) (H \ (A ∪ fwdHull w t)) := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨hzA, hzK⟩ := (mem_C_iff hΨ hw ht hWr hWr0 hu hK hd).1 hz
    have h2 : DifferentiableAt ℂ Ψ z := hΨ.conf.1.differentiableAt (hΨ.isOpen.mem_nhds hzA)
    have h1 : DifferentiableAt ℂ (logDerivFwd Wr u) (Ψ z) :=
      (isDerivLog_fwdMap hWr hu).1.differentiableAt ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWr hu).mem_nhds hzK)
    have h3 : DifferentiableAt ℂ LΨ z := hΨ.log.1.differentiableAt (hΨ.isOpen.mem_nhds hzA)
    exact ((h1.comp z h2).add h3).differentiableWithinAt
  · obtain ⟨hzA, hzK⟩ := (mem_C_iff hΨ hw ht hWr hWr0 hu hK hd).1 hz
    have h1 : DifferentiableAt ℂ (fwdMap Wr u) (Ψ z) :=
      (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWr hu).differentiableAt
        ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWr hu).mem_nhds hzK)
    have h2 : DifferentiableAt ℂ Ψ z := hΨ.conf.1.differentiableAt (hΨ.isOpen.mem_nhds hzA)
    rw [show jointFwd Ψ Wr u = fwdMap Wr u ∘ Ψ from rfl, deriv_comp z h1 h2, ← (isDerivLog_fwdMap hWr hu).2 _ hzK,
      ← hΨ.log.2 z hzA, jointLog, Complex.exp_add]

/-- **The local integer lift of the transition** (the first step of the single-lift argument): if the joint
parametrization lands off `ℍ ∖ K_t` at every real point of `B(x, r)`, then for one integer `n` the inherited argument
difference `Im log f_t' − jointLift` tends to `2πn` at every real point of a smaller ball (`Lemma71O.exists_int_wall`:
Schwarz reflection of `f_t ∘ Ψi ∘ f̃_u⁻¹` with positive derivative). -/
theorem exists_int_jointChart (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {x r : ℝ} (hr : 0 < r)
    (hland : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ∃ p, p ∉ H \ fwdHull w t ∧
      Tendsto (jointInv Ψi Wr u) (𝓝[H] z) (𝓝 p)) :
    ∃ n : ℤ, ∃ ε > 0, ε ≤ r ∧ ∀ z ∈ ball (x : ℂ) ε, z.im = 0 →
      Tendsto (fun y => (logDerivFwd w t (jointInv Ψi Wr u y)).im - jointLift Ψ LΨ Wr u (jointInv Ψi Wr u y))
        (𝓝[H] z) (𝓝 (2 * Real.pi * n)) := by
  have hCt : H \ (A ∪ fwdHull w t) ⊆ H \ fwdHull w t := fun z hz => ⟨hz.1, fun h => hz.2 (Or.inr h)⟩
  obtain ⟨n, ε, hε, hεr, hlim⟩ := Sec7.Lemma71O.exists_int_wall hη hw hw0 ht
    (isConformal_jointChart hΨ hw ht hWr hWr0 hu hK hd) (coe_dom_jointChart hΨ hw ht hWr hWr0 hu hK hd)
    (isDerivLog_jointLog hΨ hw ht hWr hWr0 hu hK hd) hCt hr hland
  refine ⟨n, ε, hε, hεr, fun z hz hz0 => (hlim z hz hz0).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)⟩
  simp only [jointChart, jointLog, jointLift, Complex.sub_im, Complex.add_im]

/-- **The pinning of the integer** (the single-lift argument's normalization): at a real point `x` of the joint chart
off the relative hull image whose joint landing point `p` is a real point off `cl A ∪ cl K_t` (an untouched original
real point next to the explored base), the inherited argument difference tends to `0`: all three arguments vanish
there ((CA2) for both chains and `IsRetainedChart.lift_real`). -/
theorem tendsto_lift_sub_zero_of_untouched (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) {ηr : ℝ → ℂ} (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {x : ℝ} (hy : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u)) {p : ℂ}
    (hp : Tendsto (jointInv Ψi Wr u) (𝓝[H] (x : ℂ)) (𝓝 p)) (hpim : p.im = 0) (hpA : p ∉ closure A)
    (hpK : p ∉ closure (fwdHull w t)) (hp0 : p ≠ 0) :
    Tendsto (fun y => (logDerivFwd w t (jointInv Ψi Wr u y)).im - jointLift Ψ LΨ Wr u (jointInv Ψi Wr u y))
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hpr : p = (p.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hpim]
  set yc : ℂ := extendFrom H (fwdMapInv Wr u) (x : ℂ) with hycdef
  have hyim : yc.im = 0 := BHMean.im_extendFrom_eq_zero_of_notMem_closure hηr hWr hWr0 hu hy
  have hyr : yc = (yc.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hyim]
  have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hlimF : Tendsto (fwdMapInv Wr u) (𝓝[H] (x : ℂ)) (𝓝[H] yc) :=
    tendsto_nhdsWithin_iff.2 ⟨(hηr.hasBdryLimits hWr hWr0 hu).tendsto hxbar,
      eventually_nhdsWithin_of_forall fun v hv => QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hv⟩
  have hJC : ∀ y ∈ H, jointInv Ψi Wr u y ∈ H \ (A ∪ fwdHull w t) := fun y hy =>
    jointInv_mem hΨ hw ht hWr hWr0 hu hK hd hy
  -- the explored argument
  have h1 : Tendsto (fun y => (logDerivFwd w t (jointInv Ψi Wr u y)).im) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    have hl := BHMean.tendsto_im_logDerivFwd_of_notMem_closure hw hw0 ht (y := p.re) (by rw [← hpr]; exact hpK)
    rw [← hpr] at hl
    exact hl.comp (tendsto_nhdsWithin_iff.2 ⟨hp, eventually_nhdsWithin_of_forall fun y hy => (hJC y hy).1⟩)
  -- the relative argument
  have h2 : Tendsto (fun y => (logDerivFwd Wr u (fwdMapInv Wr u y)).im) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    have hl := BHMean.tendsto_im_logDerivFwd_of_notMem_closure hWr hWr0 hu (y := yc.re) (by rw [← hyr]; exact hy)
    rw [← hyr] at hl
    exact hl.comp hlimF
  -- the retained chart's argument
  have h3 : Tendsto (fun y => (LΨ (jointInv Ψi Wr u y)).im) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    have hl := hΨ.lift_real p.re (fun h => hp0 (by rw [hpr, h]; simp)) (by rw [← hpr]; exact hpA)
    rw [← hpr] at hl
    exact hl.comp (tendsto_nhdsWithin_iff.2 ⟨hp, eventually_nhdsWithin_of_forall fun y hy =>
      ⟨(hJC y hy).1, fun h => (hJC y hy).2 (Or.inl h)⟩⟩)
  have hsum := h1.sub (h2.add h3)
  rw [add_zero, sub_zero] at hsum
  refine hsum.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  have hFv := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu hy
  simp only [jointLift, jointInv, hΨ.fwd_inv _ hFv.1]


end InteractingSLE.Supp8.Q3Rel
