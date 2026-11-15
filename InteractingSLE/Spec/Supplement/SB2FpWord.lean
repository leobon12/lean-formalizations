/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FpAdm
import InteractingSLE.Spec.Supplement.SB2MoPhys
import InteractingSLE.Spec.Supplement.SB2CzMix
import InteractingSLE.Spec.Supplement.SB2KZero

/-!
# D55: the root word read with the offset of a chart identity

Worker PROVE-SB2-F3LAW (round 4, decision D55). CONDFIN's root-word identity asks, under the upper kernel, that the
word `shiftW x₀ β₁` of any canonical root objects `(G, K, x₀)` be one constant data word of the relative field.
`Mz.CanonIdentOn` alone does not pin the offset `x₀`; the chart identity
`(Mo.hullChart (fill K) x₀).1 = (Mo.physRelChart c₀ (init chart) m).1` on `ℍ ∖ fill K` (which CONDFIN's consumer
obtains from `Mz.ident_rel_stage` at relative stage `0`) does: both `mapOut (fill K) − x₀ − m` and the upper run
chart plus its hull-model shift `s` are mapping-out functions normalized at `∞`, so `x₀ = s − m`
(**`offset_eq_of_hullModel`**). Then `shiftW x₀ (shiftW (−s) β₀) = shiftW (−m) β₀`, constant under the kernel, and a
data word of `affField m h'` (the witness law, `isGFFWithBoundaryData_shiftW`).

* `offset_eq_of_hullModel`, `shiftW_shiftW_neg`;
* **`RootWordAtX`** (the identity with the chart-identity premise) and **`rootWordAtX_of_hull`** (for the base word
  `β = shiftW (−s) β₀` of `Fp.exists_hullLawW`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fp

open Restart Exist Exist.Staged Exist.StagedLaw Lu Fm FlowDilate

/-- **The offset of a hull chart agreeing with a hull-modelled chart up to a real shift**: if
`(Mo.hullChart A x₀).1 = c.1 + m` on `ℍ ∖ A` and `c` has a hull model with shift `s`, then `x₀ = s − m`
(normalization of both mapping-out functions at `∞`). -/
theorem offset_eq_of_hullModel {c : Chart} (M : WalkIntCanon.HullModel c) {A : Set ℂ} (hA : IsHPHull A)
    {x₀ m : ℝ} (hfwd : EqOn (Mo.hullChart A x₀).1 (fun z => c.1 z + (m : ℂ)) (H \ A)) : x₀ = M.shift - m := by
  set D : Set ℂ := (H \ A) ∩ (H \ M.hull) with hD
  have hne : (Bornology.cobounded ℂ ⊓ 𝓟 D).NeBot := by
    rw [inf_principal_neBot_iff]
    intro S hS
    have hSb : Bornology.IsBounded Sᶜ := Bornology.isBounded_def.2 (by rwa [compl_compl])
    obtain ⟨r, hr⟩ := (hSb.union (hA.2.1.union M.isHull.2.1)).subset_closedBall 0
    set ρ : ℝ := |r| + 1 with hρ
    have hρ0 : 0 < ρ := by positivity
    have hρr : r < ρ := by linarith [le_abs_self r]
    have hnorm : ‖((ρ : ℝ) : ℂ) * Complex.I‖ = ρ := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
    have hout : ((ρ : ℝ) : ℂ) * Complex.I ∉ closedBall (0 : ℂ) r := by
      rw [mem_closedBall, dist_zero_right, hnorm]
      linarith
    have hH : ((ρ : ℝ) : ℂ) * Complex.I ∈ H := by
      show 0 < (((ρ : ℝ) : ℂ) * Complex.I).im
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
        mul_zero, add_zero]
      exact hρ0
    refine ⟨((ρ : ℝ) : ℂ) * Complex.I, ?_, ⟨hH, fun hz => hout (hr (Or.inr (Or.inl hz)))⟩,
      ⟨hH, fun hz => hout (hr (Or.inr (Or.inr hz)))⟩⟩
    by_contra hz
    exact hout (hr (Or.inl hz))
  have h1 : Tendsto (fun z => ConformalImage.mapOut A z - z) (Bornology.cobounded ℂ ⊓ 𝓟 D) (𝓝 0) :=
    (ConformalImage.isMapOut_mapOut hA).2.mono_left (inf_le_inf_left _ (principal_mono.2 inter_subset_left))
  have h2 : Tendsto (fun z => (c.1 z + (M.shift : ℂ)) - z) (Bornology.cobounded ℂ ⊓ 𝓟 D) (𝓝 0) :=
    M.mapOut.2.mono_left (inf_le_inf_left _ (principal_mono.2 inter_subset_right))
  have hconst : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 D,
      (ConformalImage.mapOut A z - z) - ((c.1 z + (M.shift : ℂ)) - z) = ((x₀ + m - M.shift : ℝ) : ℂ) := by
    filter_upwards [mem_inf_of_right (mem_principal_self D)] with z hz
    have e := hfwd hz.1
    simp only [Mo.hullChart_fwd] at e
    push_cast
    linear_combination e
  have h3 := (h1.sub h2).congr' hconst
  rw [sub_zero] at h3
  have h4 := tendsto_nhds_unique h3 tendsto_const_nhds
  have h5 : x₀ + m - M.shift = 0 := by exact_mod_cast h4.symm
  linarith

theorem shiftW_shiftW_neg (s m : ℝ) (β : BoundaryWord) :
    BoundaryWord.shiftW (s - m) (BoundaryWord.shiftW (-s) β) = BoundaryWord.shiftW (-m) β := by
  simp only [BoundaryWord.shiftW]
  refine Prod.ext rfl (Prod.ext (funext fun i => ?_) rfl)
  simp only
  ring

/-- **The root-word identity at the root chart identity** (D55, in the corrected form of this packet's handoff R4):
under the upper kernel at almost every upper launch, for every relative datum `(b', J', h')`, the word `c` is,
almost surely on `G` wherever the root chart identity of `(K, x₀)` holds, one constant word `w`, and `w` is a data word
of the relative field `affField m h'`. -/
def RootWordAtX (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ)
    (G : Set Ω) (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (c : Ω → BoundaryWord) : Prop :=
  ∀ᵐ ω₀ ∂P, ∀ (c₀ : Chart) (θ : ℝ),
    (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1)).2.2.2.1 k = some (c₀, θ) →
    ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens), IsPiecewiseConstantBoundaryData b' J' →
      (∀ ω, IsChartTransport c₀ 1 0 (chiC κ) (h ω) (h' ω)) →
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
        h' b' J' →
      ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ →
      ∃ w : BoundaryWord,
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
          (fun ω => affField m one_pos (h' ω)) w.fn w.jumps ∧
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀), ω ∈ G →
          EqOn (Mo.hullChart (fillH (K ω)) (x₀ ω)).1 (Mo.physRelChart c₀ (ExplState.init 0).2.2.2.2.1 m).1
            (H \ fillH (K ω)) → c ω = w

/-- **The root-word identity for the base word** `β = shiftW (−s) β₀` of `Fp.exists_hullLawW` (the stage witness word
read with the run chart's hull-model shift `s`), for every root object family `(G, K, x₀)`. -/
theorem rootWordAtX_of_hull {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) {k : ℕ}
    {β β₀ : Ω → BoundaryWord} {Y₀ : Ω → DistOn upperHalfPlaneOpens} {s : Ω → ℝ} {G₁ : Set Ω}
    (hW : IsStageWitness κ b jumps P h (upperSpec u l) (StagedReg.regFam E (upperSpec u l)) k β₀ Y₀)
    (hβeq : ∀ ω, β ω = BoundaryWord.shiftW (-(s ω)) (β₀ ω))
    (hG₁ae : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (upperSpec u l)
      (fun j => StagedReg.regFam E (upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none → ω ∈ G₁)
    (hmodel : ∀ ω ∈ G₁, ∃ Mh : WalkIntCanon.HullModel (ExplState.run κ b jumps (upperSpec u l)
      (fun j => StagedReg.regFam E (upperSpec u l) j ω) k).2.2.2.2.1, s ω = Mh.shift)
    (G : Set Ω) (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) :
    RootWordAtX κ b jumps P h E u l k G K x₀ (fun ω => BoundaryWord.shiftW (x₀ ω) (β ω)) := by
  classical
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hsp := isBoundaryContinuedProgram_upperSpec (u := u) hlθ
  have hm' : pastSigma κ b jumps (upperSpec u l) (StagedReg.regFam E (upperSpec u l)) k ≤ mΩ := (hE' _ hsp).2.1 k
  have hpm' : Measurable (pastMap κ b jumps (upperSpec u l) (StagedReg.regFam E (upperSpec u l)) k) :=
    Measurable.of_comap_le hm'
  have hpm : Measurable (pastMap κ b jumps (upperSpec u l) (E (upperSpec u l)) k) :=
    Measurable.of_comap_le ((hE _ hsp).2.1 k)
  have hK : ∀ᵐ ω₀ ∂P, condExpKernel P (pastSigma κ b jumps (upperSpec u l)
      (StagedReg.regFam E (upperSpec u l)) k) ω₀ =
      condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀ :=
    StagedReg.ae_condExpKernel_eq_of_ae_eq hpm' hpm (StagedReg.ae_pastMap_regHist (hER _ hsp) k)
  have hrunQ := Nc.ae_ae_run_eq_of_regular (P := P) (upperSpec u l) (hreg' (upperSpec u l)) hm' le_rfl
  have htrQ := KernelTower.ae_ae_condExpKernel_of_ae (P := P) hm' hW.2.2.1
  have hGQ := KernelTower.ae_ae_condExpKernel_of_ae (P := P) hm' hG₁ae
  have hβQ := Cz.ae_ae_word_eq (P := P) hm' hW.1
  filter_upwards [hW.2.2.2, hK, hrunQ, htrQ, hGQ, hβQ, hrun _ hsp, hW.2.2.1] with ω₀ hlaw hk hrQ htQ hGQω hβQω hr0
    hc0
  intro c₀ θ hcθ b' J' h' hb' hT' hG' m hm
  have hlr : (ExplState.run κ b jumps (upperSpec u l) (fun j => StagedReg.regFam E (upperSpec u l) j ω₀)
      (k + 1)).2.2.2.1 k ≠ none := by
    rw [launches_run_succ_of_run_eq (upperSpec u l) (hr0 k), hcθ]
    exact Option.some_ne_none _
  have hc0e : c₀ = (ExplState.run κ b jumps (upperSpec u l)
      (fun j => StagedReg.regFam E (upperSpec u l) j ω₀) k).2.2.2.2.1 := by
    rw [(eq_launch_of_launches _ _ hcθ).2.2, hr0 k]
  obtain ⟨hconf, -, -⟩ := hc0 hlr
  rw [← hc0e] at hconf
  have hlω : ∀ ω, (∀ n, n ≤ k → ExplState.run κ b jumps (upperSpec u l)
      (fun j => StagedReg.regFam E (upperSpec u l) j ω) n = ExplState.run κ b jumps (upperSpec u l)
      (fun j => StagedReg.regFam E (upperSpec u l) j ω₀) n) →
      (ExplState.run κ b jumps (upperSpec u l) (fun j => StagedReg.regFam E (upperSpec u l) j ω)
        (k + 1)).2.2.2.1 k ≠ none := fun ω hr => by
    rw [launches_run_succ_of_run_eq (upperSpec u l) (hr k le_rfl)]
    exact hlr
  rw [← hk] at hG' ⊢
  have hY : Y₀ =ᵐ[condExpKernel P (pastSigma κ b jumps (upperSpec u l)
      (StagedReg.regFam E (upperSpec u l)) k) ω₀] h' := by
    filter_upwards [hrQ, htQ] with ω hr ht
    obtain ⟨-, -, htω⟩ := ht (hlω ω hr)
    rw [hr k le_rfl, ← hc0e] at htω
    exact htω.unique hconf (hT' ω)
  have hlawh' := isGFFWithBoundaryData_congr_ae (hlaw hlr) hG'.1 hY
  refine ⟨BoundaryWord.shiftW (-m) (β₀ ω₀), ?_, ?_⟩
  · have e : (fun ω => affField m one_pos (h' ω)) = fun ω => Exist.flowField (-m) 0 (h' ω) := by
      funext ω
      rw [Lv.flowField_eq_affField, neg_neg]
    rw [e]
    exact isGFFWithBoundaryData_shiftW (-m) hlawh'
  · filter_upwards [hrQ, hGQω, hβQω] with ω hr hGω hβω _ hid
    obtain ⟨Mh, hsM⟩ := hmodel ω (hGω (hlω ω hr))
    have hfwd : EqOn (Mo.hullChart (fillH (K ω)) (x₀ ω)).1
        (fun z => (ExplState.run κ b jumps (upperSpec u l) (fun j => StagedReg.regFam E (upperSpec u l) j ω)
          k).2.2.2.2.1.1 z + (m : ℂ)) (H \ fillH (K ω)) := by
      intro z hz
      rw [hid hz, hr k le_rfl, ← hc0e]
      simp [Mo.physRelChart_fwd, ExplState.init, Chart.recenter, Chart.id]
    have hx := offset_eq_of_hullModel Mh (Mo.isHPHull_fillH hKc hKp ω) hfwd
    show BoundaryWord.shiftW (x₀ ω) (β ω) = _
    rw [hx, ← hsM, hβeq ω, shiftW_shiftW_neg, hβω]

end InteractingSLE.Theorem14.SB.Fp
