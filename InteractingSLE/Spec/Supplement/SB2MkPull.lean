/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MkFill
import InteractingSLE.Spec.Supplement.SBS3CanonComp
import InteractingSLE.Spec.Supplement.WalkIntRunChronCarrier
import InteractingSLE.Foundations.Loewner.CapacityEstimates

/-!
# SB2(2)'s stage pull-back from the run-chart package

Packet PROVE-SB2-LCMEAN, round 8. `Ln.IsStagePullback c g A₁ A₂ A₁' K` collects the deterministic properties of B's
stage chart `c` used to pull the union datum back. For a regular run chart that is not finished, the landed
`S3.Canon.runChart_package` gives the chart of `ℍ ∖ fill(prefix)` and a continuous boundary map `g` of the inverse,
within bounded distance of the identity. All clauses but one follow:

* **`isStagePullback_of_domainChart`** (deterministic): a domain chart of `ℍ ∖ fill X` with a continuous boundary map at
  bounded distance from the identity, finite fibres, `ℍ ∖ c.dom ⊆ A₁`, `ℍ ∖ c.dom ⊆ A₂` and `corr₂` give the stage
  pull-back with `A₁' = c.2.1⁻¹ A₁` (`liftc`, `liftd` from the domain chart; `gp` from the bounded distance; `gR`:
  a boundary value of the inverse inside the chart domain would be mapped back to the real boundary point, which is not
  in `ℍ`);
* **`ae_isStagePullback_fill`**: for SB2(2)'s sets (`A₁` almost surely the filled `A ∪ B_{<ℓ}`, `A₂` with `corr₂`,
  `dom₂`), almost surely on the capped launch event at an upper launch: the boundary map `g` of B's stage chart exists,
  and **finite fibres of `g` give the stage pull-back** (`dom₁`: the complement of B's stage chart domain is the fill of
  `B_{<ℓ}`, inside the fill of the bounded set `A ∪ B_{<ℓ}`).

The finite fibres are the one clause left: the landed route (`LuM.pinv_prefix_walk`, `Lk.finite_fibre_of_pinv`) needs
GW1's tip coordinates of the lower walk, available under `Ly.LowerLeftAdmissible` (all of `x < 0`), while SB2(2)'s
setting gives the left bound on `(u, 0)` only.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdMap fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mk

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField

/-! ### The stage pull-back of a domain chart -/

/-- **The stage pull-back of a domain chart with a proper boundary map with finite fibres.** -/
theorem isStagePullback_of_domainChart {c : Chart} {X : Set ℂ} (hD : IsDomainChart (H \ fillH X) c)
    {g : ℂ → ℂ} (hgc : ContinuousOn g Hbar) (hgi : EqOn g c.2.1 H) {C : ℝ} (hgb : ∀ q ∈ Hbar, ‖g q - q‖ ≤ C)
    (hgf : ∀ z, (g ⁻¹' {z} ∩ Hbar).Finite) {A₁ A₂ K : Set ℂ} (hdom₁ : H \ (c.dom : Set ℂ) ⊆ A₁)
    (hdom₂ : H \ (c.dom : Set ℂ) ⊆ A₂) (hcorr₂ : ∀ w ∈ H, c.2.1 w ∈ A₂ ↔ w ∈ K) :
    Ln.IsStagePullback c g A₁ A₂ {w | c.2.1 w ∈ A₁} K := by
  have hdom : (c.dom : Set ℂ) = H \ fillH X := by rw [hD.1.coe_dom]; exact hD.2.1
  have hHHbar : H ⊆ Hbar := fun z hz => show 0 ≤ z.im from le_of_lt hz
  have hHbarc : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
  refine ⟨hD.1, ?_, fun z hz => hD.deriv_eq (hdom ▸ hz), hgc, hgi, hgf, fun M => ⟨M + C, fun z hz hR => ?_⟩,
    fun x => ?_, hdom₁, hdom₂, fun w _ => Iff.rfl, hcorr₂⟩
  · rw [hdom]
    exact hD.continuousOn_lift
  · have h1 := norm_sub_norm_le z (g z)
    rw [norm_sub_rev] at h1
    linarith [hgb z hz]
  · have hx : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
    have := GW1P.neBot_nhdsWithin_H hx
    have ht : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (g x)) :=
      ((hgc (x : ℂ) hx).tendsto.mono_left (nhdsWithin_mono _ hHHbar)).congr'
        (eventually_nhdsWithin_of_forall fun w hw => hgi hw)
    by_cases him : (g x).im = 0
    · exact Or.inr him
    · left
      have hgH : g x ∈ Hbar := hHbarc.mem_of_tendsto ht
        (eventually_nhdsWithin_of_forall fun w hw => hHHbar (hD.subset_H (hD.inv_mem hw)))
      have hgxH : g x ∈ H := lt_of_le_of_ne hgH (Ne.symm him)
      refine ⟨hgxH, fun hgD => ?_⟩
      have hgD' : g x ∈ H \ fillH X := hdom ▸ hgD
      have hc1 : ContinuousAt c.1 (g x) :=
        (hD.differentiableOn_fwd.differentiableAt (hD.isOpen.mem_nhds hgD')).continuousAt
      have h2 : Tendsto (fun w => c.1 (c.2.1 w)) (𝓝[H] (x : ℂ)) (𝓝 (c.1 (g x))) := hc1.tendsto.comp ht
      have h3 : Tendsto (fun w => c.1 (c.2.1 w)) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) :=
        (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr'
          (eventually_nhdsWithin_of_forall fun w hw => (hD.fwd_inv hw).symm)
      have e : (x : ℂ) = c.1 (g x) := tendsto_nhds_unique h3 h2
      have hm : c.1 (g x) ∈ H := hD.fwd_mem hgD'
      rw [← e] at hm
      exact absurd hm (by simp [QuantumZipper.H])

/-! ### SB2(2) -/

section SB2

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

open Mi Mf in
/-- **SB2(2)'s stage pull-back up to the finite fibres**: for SB2(2)'s retained set (almost surely the filled
`A ∪ B_{<ℓ}`) and an explored set with `corr₂`, `dom₂`, almost surely on the capped launch event at an upper launch,
B's stage chart has a continuous boundary map `g` of its inverse, and finite fibres of `g` give
`Ln.IsStagePullback` with `A₁' = c.2.1⁻¹ A₁` and the hull of the stopped piece. -/
theorem ae_isStagePullback_fill (h13 : Theorem13Statement.{u}) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length) (τ : ℝ≥0) {A₁ A₂ : Ω → Set ℂ}
    (hA₁ : ∀ᵐ ω ∂P, A₁ ω = fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω)
    (hA₂ : ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ τ →
      (∀ v ∈ H, (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.1 v ∈ A₂ ω ↔
        v ∈ fwdHull (sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ τ ω)
          (sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ τ ω)) ∧
      H \ ((sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).dom : Set ℂ) ⊆ A₂ ω) :
    ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ τ →
      (ExplState.run κ b jumps (Lu.upperSpec u l)
        (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none →
      ∃ g : ℂ → ℂ, ContinuousOn g Hbar ∧ EqOn g (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.1 H ∧
        ((∀ z, (g ⁻¹' {z} ∩ Hbar).Finite) →
          Ln.IsStagePullback (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω) g (A₁ ω) (A₂ ω)
            {w | (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.1 w ∈ A₁ ω}
            (fwdHull (sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ τ ω)
              (sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ τ ω))) := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hup := hE' (Lu.upperSpec u l) (Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ)
  have hRw := stagedPiecesRegular_of_regular h13 hκ hb (hE' _ hw) (hreg' w)
  have hRu := stagedPiecesRegular_of_regular h13 hκ hb hup (hreg' _)
  filter_upwards [hA₁, hA₂, hRw.ae_pieceRegular, hRu.ae_pieceRegular] with ω h1 h2 hPw hPu hcap hlu
  set c := sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω with hcdef
  obtain ⟨⟨c₀, θ₀⟩, hl⟩ := Option.ne_none_iff_exists'.1 hcap.1
  have hnot := WalkIntRunChron.not_done_of_launch _ _ hl
  obtain ⟨⟨c₁, θ₁⟩, hlu'⟩ := Option.ne_none_iff_exists'.1 hlu
  have hnotU := WalkIntRunChron.not_done_of_launch _ _ hlu'
  obtain ⟨-, gc, C, hD, -, -, -, hgc, hgi, -, -, hgb⟩ := S3.Canon.runChart_package w _ hPw ℓ hnot
  refine ⟨gc, hgc, hgi, fun hgf => isStagePullback_of_domainChart hD hgc hgi hgb hgf ?_ (h2 hcap).2 (h2 hcap).1⟩
  -- `dom₁`: the complement of B's stage chart domain is the fill of `B_{<ℓ}`
  have hdomc : ((c.dom : Set ℂ)) = H \ fillH (SB.prefixPhysSet κ b jumps w
      (fun j => StagedReg.regFam E w j ω) ℓ) := dom_runChart_eq w _ hPw ℓ hnot
  have hsw : WalkLaw.stageSet κ b jumps w (StagedReg.regFam E w) ℓ ω =
      WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) τ) (StagedReg.regFam E w) ℓ ω := by
    simp only [WalkLaw.stageSet, run_capSpec_of_le hℓ.le _ le_rfl]
  have hbW : Bornology.IsBounded
      (WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) τ) (StagedReg.regFam E w) ℓ ω) := by
    rw [← hsw]
    refine (Lx.isCompact_prefixPhysSet_run _ _ hPw ℓ hnot).isBounded.subset ?_
    rw [← prefixPhysSet_inter_H_eq]
    exact inter_subset_left
  have hbU : Bornology.IsBounded
      (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω) := by
    refine (Lx.isCompact_prefixPhysSet_run _ _ hPu k hnotU).isBounded.subset ?_
    rw [← prefixPhysSet_inter_H_eq]
    exact inter_subset_left
  intro z hz₀
  have hz : z ∈ H \ (c.dom : Set ℂ) := hz₀
  have hzf : z ∈ fillH (WalkLaw.stageSet κ b jumps w (StagedReg.regFam E w) ℓ ω) := by
    rw [← fillH_prefixPhysSet_eq]
    rw [hdomc] at hz
    by_contra hzn
    exact hz.2 ⟨hz.1, hzn⟩
  show z ∈ A₁ ω
  rw [h1, fillVer_of_bounded (B := fun ω =>
    WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) τ) (StagedReg.regFam E w) ℓ ω)
    (hbU.union hbW), Sec7.SideHeight.fillH_closure]
  rw [hsw] at hzf
  exact fillH_mono subset_union_right hzf

end SB2

end InteractingSLE.Theorem14.SB.Mk
