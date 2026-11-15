/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3RelBH

/-!
# Lemma SB2 at a junction: the relative component and its joint chart

Packet PROVE-T14-SB2UNION. Lemma SB2 (supplement pp. 630–633, `source/spec/p625-671.md` L113–L150) identifies the
continuation of one history in the conditional field of the domain `D_A` left by a retained history `A`. The moving
curve **enters through a junction on `A`**: SB2(1)'s upper flow runs inside the filled hull of `A` until its first visit
to `L = min (A ∩ ℝ)` and leaves `A` there; afterwards its right side may touch `A` again ("Earlier right-side
contacts of its simple relative trace are filled; only the current record junction can remain exposed", p. 632). The
landed union mean `Supp8.Q3Rel.ae_eqOn_unionMean_of_relConfigOff` assumes that the explored hull and the retained set
have disjoint closures, so it does not apply.

This file starts the junction version. With the retained chart `Ψ : ℍ ∖ A → ℍ` and the relative Loewner chain `Wr` at
time `u`, the **relative component** is `relComp A Ψ Wr u = {z ∈ ℍ ∖ A | Ψ z ∉ K̃_u}`: the points that the relative
chain has not explored. It is always the image of `ℍ` under the joint inverse `Ψi ∘ f̃_u⁻¹`, so it is open and
connected, and the joint chart `f̃_u ∘ Ψ` is a conformal bijection onto `ℍ` there (`isConformalBijection_jointFwd`,
`isConformalBijection_diskInv`, `isConformal_jointChart`), with no hypothesis relating it to the physical hull.

Two **junction hull hypotheses** replace the landed configuration's `Ψ(K_t) = K̃_u` and the disjointness of the closed
hulls:

* `hKin : ∀ z ∈ K_t, z ∉ A → Ψ z ∈ K̃_u` (the physical exploration outside `A` is explored in the chart), so
  `relComp ⊆ ℍ ∖ (A ∪ K_t)`;
* `hKfr : ∀ z ∈ ℍ ∖ A, Ψ z ∈ frontier K̃_u → z ∈ K_t` (the frontier of the relative hull comes from the curve), so
  `relComp` is relatively closed in `ℍ ∖ (A ∪ K_t)`.

Under them `relComp` is the connected component of `ℍ ∖ (A ∪ K_t)` through each of its points
(`connectedComponentIn_eq_relComp`): the **unbounded** component, the one carrying the relative chain. The other
components are the pockets between the curve's right side and `A`; the source identifies their fields separately
("all frozen components", p. 632), and the conditional flow-line law (K2) only tests the field off the relative hull.

The local integer of the single-lift argument (`exists_int_jointChart_rel`) and its normalization at an untouched real
point (`tendsto_lift_sub_zero_of_untouched_rel`) hold on `relComp` with `hKin` alone.

Deterministic. Conditional helpers with distinct names; they replace no source theorem. R48: serves Theorem 1.4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE.Theorem14.SB.Union

open Supp8.BHMean (jointInv jointFwd jointLift jointChart jointLog)
open Supp8.Q3Rel (IsRetainedChartOff)

/-- **The relative component**: the points of `ℍ ∖ A` whose chart image lies off the relative hull `K̃_u`. -/
def relComp (A : Set ℂ) (Ψ : ℂ → ℂ) (Wr : ℝ → ℝ) (u : ℝ) : Set ℂ :=
  {z | z ∈ H \ A ∧ Ψ z ∈ H \ fwdHull Wr u}

/-! ### The joint chart on the relative component -/

section Chart

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {Wr : ℝ → ℝ} {u : ℝ}
  (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u)

include hΨ hWr hWr0 hu

theorem jointInv_mem_relComp {y : ℂ} (hy : y ∈ H) : jointInv Ψi Wr u y ∈ relComp A Ψ Wr u := by
  have h1 := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu hy
  refine ⟨hΨ.inv_mem _ h1.1, ?_⟩
  simp only [jointInv]
  rw [hΨ.fwd_inv _ h1.1]
  exact h1

theorem jointFwd_mem_of_relComp {z : ℂ} (hz : z ∈ relComp A Ψ Wr u) : jointFwd Ψ Wr u z ∈ H :=
  QuantumZipper.FwdHolo.mapsTo_fwdMap hWr hu hz.2

theorem jointFwd_jointInv_rel {y : ℂ} (hy : y ∈ H) : jointFwd Ψ Wr u (jointInv Ψi Wr u y) = y := by
  have h1 := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu hy
  simp only [jointFwd, jointInv]
  rw [hΨ.fwd_inv _ h1.1, QuantumZipper.RS.fwdMap_fwdMapInv hWr hWr0 hu hy]

theorem jointInv_jointFwd_rel {z : ℂ} (hz : z ∈ relComp A Ψ Wr u) :
    jointInv Ψi Wr u (jointFwd Ψ Wr u z) = z := by
  simp only [jointFwd, jointInv]
  rw [QuantumZipper.RS.fwdMapInv_fwdMap hWr hWr0 hu hz.2, hΨ.inv_fwd hz.1]

theorem continuousOn_jointInv_rel : ContinuousOn (jointInv Ψi Wr u) H :=
  hΨ.diff_inv.continuousOn.comp (isConformalBijection_fwdMapInv hWr hWr0 hu).1.continuousOn
    fun _ hy => (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu hy).1

theorem image_jointInv_rel : jointInv Ψi Wr u '' H = relComp A Ψ Wr u := by
  refine Subset.antisymm ?_ fun z hz => ⟨jointFwd Ψ Wr u z, jointFwd_mem_of_relComp hΨ hWr hWr0 hu hz,
    jointInv_jointFwd_rel hΨ hWr hWr0 hu hz⟩
  rintro _ ⟨y, hy, rfl⟩
  exact jointInv_mem_relComp hΨ hWr hWr0 hu hy

theorem isPreconnected_relComp : IsPreconnected (relComp A Ψ Wr u) := by
  rw [← image_jointInv_rel hΨ hWr hWr0 hu]
  exact (convex_halfSpace_im_gt 0).isPreconnected.image _ (continuousOn_jointInv_rel hΨ hWr hWr0 hu)

theorem isOpen_relComp : IsOpen (relComp A Ψ Wr u) :=
  hΨ.conf.1.continuousOn.isOpen_inter_preimage hΨ.isOpen (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWr hu)

theorem differentiableAt_jointFwd_rel {z : ℂ} (hz : z ∈ relComp A Ψ Wr u) :
    DifferentiableAt ℂ (jointFwd Ψ Wr u) z := by
  have h1 : DifferentiableAt ℂ (fwdMap Wr u) (Ψ z) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWr hu).differentiableAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWr hu).mem_nhds hz.2)
  have h2 : DifferentiableAt ℂ Ψ z := hΨ.conf.1.differentiableAt (hΨ.isOpen.mem_nhds hz.1)
  exact h1.comp z h2

/-- **The joint chart is a conformal bijection of the relative component onto `ℍ`.** -/
theorem isConformalBijection_jointFwd_rel : IsConformalBijection (jointFwd Ψ Wr u) (relComp A Ψ Wr u) H := by
  refine ⟨fun z hz => (differentiableAt_jointFwd_rel hΨ hWr hWr0 hu hz).differentiableWithinAt,
    ⟨fun z hz => jointFwd_mem_of_relComp hΨ hWr hWr0 hu hz, fun z hz z' hz' he => ?_, fun y hy => ?_⟩⟩
  · rw [← jointInv_jointFwd_rel hΨ hWr hWr0 hu hz, he, jointInv_jointFwd_rel hΨ hWr hWr0 hu hz']
  · exact ⟨jointInv Ψi Wr u y, jointInv_mem_relComp hΨ hWr hWr0 hu hy, jointFwd_jointInv_rel hΨ hWr hWr0 hu hy⟩

/-- **The disk parametrization of the relative component**: `jointInv ∘ cayleyInv : 𝔻 → relComp`. -/
theorem isConformalBijection_diskInv_rel :
    IsConformalBijection (fun ζ => jointInv Ψi Wr u (cayleyInv ζ)) (ball 0 1) (relComp A Ψ Wr u) := by
  have hc1 : ∀ ζ ∈ ball (0 : ℂ) 1, ζ ≠ 1 := fun ζ hζ h => by
    rw [h, mem_ball, dist_zero_right, norm_one] at hζ; exact lt_irrefl _ hζ
  refine ⟨?_, ⟨fun ζ hζ => jointInv_mem_relComp hΨ hWr hWr0 hu (QuantumZipper.CA.cayleyInv_mem_H hζ),
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
    rw [jointFwd_jointInv_rel hΨ hWr hWr0 hu (QuantumZipper.CA.cayleyInv_mem_H hζ),
      jointFwd_jointInv_rel hΨ hWr hWr0 hu (QuantumZipper.CA.cayleyInv_mem_H hζ')] at he'
    rw [← QuantumZipper.CA.cayley_cayleyInv (hc1 ζ hζ), he', QuantumZipper.CA.cayley_cayleyInv (hc1 ζ' hζ')]
  · have hy := jointFwd_mem_of_relComp hΨ hWr hWr0 hu hz
    refine ⟨cayley (jointFwd Ψ Wr u z), QuantumZipper.CA.cayley_mem_ball hy, ?_⟩
    simp only
    rw [QuantumZipper.CA.cayleyInv_cayley (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (le_of_lt hy)),
      jointInv_jointFwd_rel hΨ hWr hWr0 hu hz]

theorem continuousOn_jointLift_rel : ContinuousOn (jointLift Ψ LΨ Wr u) (relComp A Ψ Wr u) := by
  intro z hz
  have hΨc : ContinuousAt Ψ z := (hΨ.conf.1.differentiableAt (hΨ.isOpen.mem_nhds hz.1)).continuousAt
  have h1 : ContinuousAt (fun z => (logDerivFwd Wr u (Ψ z)).im) z :=
    continuous_im.continuousAt.comp ((continuousAt_logDerivFwd hWr hu hz.2).comp hΨc)
  have h2 : ContinuousAt (fun z => (LΨ z).im) z :=
    continuous_im.continuousAt.comp (hΨ.log.1.differentiableAt (hΨ.isOpen.mem_nhds hz.1)).continuousAt
  exact (h1.add h2).continuousWithinAt

/-- **The inherited argument of the joint chart** on the relative component. -/
theorem deriv_jointFwd_rel {z : ℂ} (hz : z ∈ relComp A Ψ Wr u) :
    deriv (jointFwd Ψ Wr u) z = ‖deriv (jointFwd Ψ Wr u) z‖ * Complex.exp (jointLift Ψ LΨ Wr u z * Complex.I) := by
  have h1 : DifferentiableAt ℂ (fwdMap Wr u) (Ψ z) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWr hu).differentiableAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWr hu).mem_nhds hz.2)
  have h2 : DifferentiableAt ℂ Ψ z := hΨ.conf.1.differentiableAt (hΨ.isOpen.mem_nhds hz.1)
  have hchain : deriv (jointFwd Ψ Wr u) z = deriv (fwdMap Wr u) (Ψ z) * deriv Ψ z :=
    deriv_comp z h1 h2
  have e1 := (isDerivLog_fwdMap hWr hu).2 (Ψ z) hz.2
  have e2 := hΨ.log.2 z hz.1
  set a : ℂ := logDerivFwd Wr u (Ψ z) + LΨ z with ha
  have hexp : deriv (jointFwd Ψ Wr u) z = Complex.exp a := by
    rw [hchain, ← e1, ← e2, ha, Complex.exp_add]
  have hL : jointLift Ψ LΨ Wr u z = a.im := by simp only [jointLift, ha, Complex.add_im]
  rw [hexp, hL, Complex.norm_exp]
  conv_lhs => rw [← Complex.re_add_im a]
  rw [Complex.exp_add, Complex.ofReal_exp]

theorem isConformal_jointChart_rel : (jointChart Ψ Ψi LΨ Wr u).IsConformal := by
  refine ⟨?_, fun y hy => (jointInv_mem_relComp hΨ hWr hWr0 hu hy).1.1, fun y hy =>
    jointFwd_jointInv_rel hΨ hWr hWr0 hu hy⟩
  intro y hy
  have hF : DifferentiableAt ℂ (fwdMapInv Wr u) y :=
    (isConformalBijection_fwdMapInv hWr hWr0 hu).1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hy)
  have hP : DifferentiableAt ℂ Ψi (fwdMapInv Wr u y) :=
    hΨ.diff_inv.differentiableAt (QuantumZipper.isOpen_H.mem_nhds (QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hy))
  exact (hP.comp y hF).differentiableWithinAt

theorem coe_dom_jointChart_rel : ((jointChart Ψ Ψi LΨ Wr u).dom : Set ℂ) = relComp A Ψ Wr u := by
  rw [(isConformal_jointChart_rel hΨ hWr hWr0 hu).coe_dom]
  exact image_jointInv_rel hΨ hWr hWr0 hu

theorem isDerivLog_jointLog_rel : IsDerivLog (jointFwd Ψ Wr u) (jointLog Ψ LΨ Wr u) (relComp A Ψ Wr u) := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · have h2 : DifferentiableAt ℂ Ψ z := hΨ.conf.1.differentiableAt (hΨ.isOpen.mem_nhds hz.1)
    have h1 : DifferentiableAt ℂ (logDerivFwd Wr u) (Ψ z) :=
      (isDerivLog_fwdMap hWr hu).1.differentiableAt
        ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWr hu).mem_nhds hz.2)
    have h3 : DifferentiableAt ℂ LΨ z := hΨ.log.1.differentiableAt (hΨ.isOpen.mem_nhds hz.1)
    exact ((h1.comp z h2).add h3).differentiableWithinAt
  · have h1 : DifferentiableAt ℂ (fwdMap Wr u) (Ψ z) :=
      (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWr hu).differentiableAt
        ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWr hu).mem_nhds hz.2)
    have h2 : DifferentiableAt ℂ Ψ z := hΨ.conf.1.differentiableAt (hΨ.isOpen.mem_nhds hz.1)
    rw [show jointFwd Ψ Wr u = fwdMap Wr u ∘ Ψ from rfl, deriv_comp z h1 h2,
      ← (isDerivLog_fwdMap hWr hu).2 _ hz.2, ← hΨ.log.2 z hz.1, jointLog, Complex.exp_add]

end Chart

/-! ### The relative component is a component of the joint complement -/

section Component

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {t u : ℝ}

/-- Under `hKin`, the relative component misses the physical hull. -/
theorem relComp_subset (hKin : ∀ z ∈ fwdHull w t, z ∉ A → Ψ z ∈ fwdHull Wr u) :
    relComp A Ψ Wr u ⊆ H \ (A ∪ fwdHull w t) := by
  rintro z ⟨⟨hzH, hzA⟩, -, hzK⟩
  refine ⟨hzH, ?_⟩
  rintro (h | h)
  · exact hzA h
  · exact hzK (hKin z h hzA)

/-- Under `hKfr`, the relative component is relatively closed in the joint complement. -/
theorem mem_relComp_of_mem_closure (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb)
    (hKfr : ∀ z ∈ H \ A, Ψ z ∈ frontier (fwdHull Wr u) → z ∈ fwdHull w t)
    {z : ℂ} (hz : z ∈ H \ (A ∪ fwdHull w t)) (hcl : z ∈ closure (relComp A Ψ Wr u)) : z ∈ relComp A Ψ Wr u := by
  have hzA : z ∈ H \ A := ⟨hz.1, fun h => hz.2 (Or.inl h)⟩
  refine ⟨hzA, hΨ.conf.2.mapsTo hzA, fun hK => ?_⟩
  have hc : ContinuousAt Ψ z := (hΨ.conf.1.differentiableAt (hΨ.isOpen.mem_nhds hzA)).continuousAt
  have hcl' : Ψ z ∈ closure (fwdHull Wr u)ᶜ := by
    have h1 : Ψ z ∈ closure (Ψ '' relComp A Ψ Wr u) := mem_closure_image hc hcl
    refine closure_mono ?_ h1
    rintro _ ⟨z', hz', rfl⟩
    exact hz'.2.2
  have hfr : Ψ z ∈ frontier (fwdHull Wr u) := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hK, hcl'⟩
  exact hz.2 (Or.inr (hKfr z hzA hfr))

/-- **The relative component is the component of the joint complement through each of its points** (under the two
junction hull hypotheses). -/
theorem connectedComponentIn_eq_relComp (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hWr : Continuous Wr)
    (hWr0 : Wr 0 = 0) (hu : 0 ≤ u) (hKin : ∀ z ∈ fwdHull w t, z ∉ A → Ψ z ∈ fwdHull Wr u)
    (hKfr : ∀ z ∈ H \ A, Ψ z ∈ frontier (fwdHull Wr u) → z ∈ fwdHull w t)
    {z₀ : ℂ} (hz₀ : z₀ ∈ relComp A Ψ Wr u) :
    connectedComponentIn (H \ (A ∪ fwdHull w t)) z₀ = relComp A Ψ Wr u := by
  set C := connectedComponentIn (H \ (A ∪ fwdHull w t)) z₀ with hCdef
  refine Subset.antisymm ?_ ((isPreconnected_relComp hΨ hWr hWr0 hu).subset_connectedComponentIn hz₀
    (relComp_subset hKin))
  have hCsub : C ⊆ H \ (A ∪ fwdHull w t) := connectedComponentIn_subset _ _
  refine (isPreconnected_connectedComponentIn).subset_left_of_subset_union
    (isOpen_relComp hΨ hWr hWr0 hu) isClosed_closure.isOpen_compl
    (Set.disjoint_left.2 fun z hz hz' => hz' (subset_closure hz)) (fun z hz => ?_)
    ⟨z₀, mem_connectedComponentIn (relComp_subset hKin hz₀), hz₀⟩
  by_cases hcl : z ∈ closure (relComp A Ψ Wr u)
  · exact Or.inl (mem_relComp_of_mem_closure hΨ hKfr (hCsub hz) hcl)
  · exact Or.inr hcl

end Component

/-! ### The local integer and its normalization on the relative component -/

section Integer

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η : ℝ → ℂ} {t u : ℝ}

/-- **The local integer lift of the transition on the relative component** (`Q3Rel.exists_int_jointChart` with the
junction hypothesis `hKin` in place of the hull identity and the disjointness): if the joint parametrization lands off
`ℍ ∖ K_t` at every real point of `B(x, r)`, the inherited argument difference tends to `2πn` at every real point of a
smaller ball, for one integer `n`. -/
theorem exists_int_jointChart_rel (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u)
    (hKin : ∀ z ∈ fwdHull w t, z ∉ A → Ψ z ∈ fwdHull Wr u)
    {x r : ℝ} (hr : 0 < r)
    (hland : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ∃ p, p ∉ H \ fwdHull w t ∧
      Tendsto (jointInv Ψi Wr u) (𝓝[H] z) (𝓝 p)) :
    ∃ n : ℤ, ∃ ε > 0, ε ≤ r ∧ ∀ z ∈ ball (x : ℂ) ε, z.im = 0 →
      Tendsto (fun y => (logDerivFwd w t (jointInv Ψi Wr u y)).im - jointLift Ψ LΨ Wr u (jointInv Ψi Wr u y))
        (𝓝[H] z) (𝓝 (2 * Real.pi * n)) := by
  have hCt : relComp A Ψ Wr u ⊆ H \ fwdHull w t := fun z hz =>
    ⟨(relComp_subset hKin hz).1, fun h => (relComp_subset hKin hz).2 (Or.inr h)⟩
  obtain ⟨n, ε, hε, hεr, hlim⟩ := Sec7.Lemma71O.exists_int_wall hη hw hw0 ht
    (isConformal_jointChart_rel hΨ hWr hWr0 hu) (coe_dom_jointChart_rel hΨ hWr hWr0 hu)
    (isDerivLog_jointLog_rel hΨ hWr hWr0 hu) hCt hr hland
  refine ⟨n, ε, hε, hεr, fun z hz hz0 => (hlim z hz hz0).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)⟩
  simp only [jointChart, jointLog, jointLift, Complex.sub_im, Complex.add_im]

/-- **The pinning of the integer at an untouched real point** (`Q3Rel.tendsto_lift_sub_zero_of_untouched` on the
relative component): at a real point `x` off the relative hull image whose joint landing point is a real point off
`cl A ∪ cl K_t`, other than `0`, the inherited argument difference tends to `0`. -/
theorem tendsto_lift_sub_zero_of_untouched_rel (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w)
    (hw0 : w 0 = 0) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) {ηr : ℝ → ℂ} (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) {x : ℝ} (hy : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u)) {p : ℂ}
    (hp : Tendsto (jointInv Ψi Wr u) (𝓝[H] (x : ℂ)) (𝓝 p)) (hpim : p.im = 0) (hpA : p ∉ closure A)
    (hpK : p ∉ closure (fwdHull w t)) (hp0 : p ≠ 0) :
    Tendsto (fun y => (logDerivFwd w t (jointInv Ψi Wr u y)).im - jointLift Ψ LΨ Wr u (jointInv Ψi Wr u y))
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hpr : p = (p.re : ℂ) := Complex.ext (by simp) (by simp [hpim])
  set yc : ℂ := extendFrom H (fwdMapInv Wr u) (x : ℂ) with hycdef
  have hyim : yc.im = 0 := Supp8.BHMean.im_extendFrom_eq_zero_of_notMem_closure hηr hWr hWr0 hu hy
  have hyr : yc = (yc.re : ℂ) := Complex.ext (by simp) (by simp [hyim])
  have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hlimF : Tendsto (fwdMapInv Wr u) (𝓝[H] (x : ℂ)) (𝓝[H] yc) :=
    tendsto_nhdsWithin_iff.2 ⟨(hηr.hasBdryLimits hWr hWr0 hu).tendsto hxbar,
      eventually_nhdsWithin_of_forall fun v hv => QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hv⟩
  have hJA : ∀ y ∈ H, jointInv Ψi Wr u y ∈ H \ A := fun y hy => (jointInv_mem_relComp hΨ hWr hWr0 hu hy).1
  -- the explored argument: near `p` the joint parametrization stays in `ℍ`
  have h1 : Tendsto (fun y => (logDerivFwd w t (jointInv Ψi Wr u y)).im) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    have hl := Supp8.BHMean.tendsto_im_logDerivFwd_of_notMem_closure hw hw0 ht (y := p.re)
      (by rw [← hpr]; exact hpK)
    rw [← hpr] at hl
    exact hl.comp (tendsto_nhdsWithin_iff.2 ⟨hp, eventually_nhdsWithin_of_forall fun y hy => (hJA y hy).1⟩)
  -- the relative argument
  have h2 : Tendsto (fun y => (logDerivFwd Wr u (fwdMapInv Wr u y)).im) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    have hl := Supp8.BHMean.tendsto_im_logDerivFwd_of_notMem_closure hWr hWr0 hu (y := yc.re)
      (by rw [← hyr]; exact hy)
    rw [← hyr] at hl
    exact hl.comp hlimF
  -- the retained chart's argument
  have h3 : Tendsto (fun y => (LΨ (jointInv Ψi Wr u y)).im) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    have hl := hΨ.lift_real p.re (fun h => hp0 (by rw [hpr, h]; simp)) (by rw [← hpr]; exact hpA)
    rw [← hpr] at hl
    exact hl.comp (tendsto_nhdsWithin_iff.2 ⟨hp, eventually_nhdsWithin_of_forall fun y hy => hJA y hy⟩)
  have hsum := h1.sub (h2.add h3)
  rw [add_zero, sub_zero] at hsum
  refine hsum.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  have hFv := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu hy
  simp only [jointLift, jointInv, hΨ.fwd_inv _ hFv.1]

end Integer

end InteractingSLE.Theorem14.SB.Union
