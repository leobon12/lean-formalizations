/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstChartLanding

/-! # Windows that stop at first real contact and preserve the seed collar -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Complex MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)

namespace InteractingSLE.Sec5.Aux61GInst
open Aux61FibData

/-- Allow only the seed interval on the real axis. The surrounding buffer
can still contain the completed slit and its comparison endpoint. -/
def seedExitWindow (U : Set ℂ) (δ : ℝ) : Set ℂ :=
  U \ {z : ℂ | z.im = 0 ∧ δ ≤ |z.re|}

theorem isOpen_seedExitWindow {U : Set ℂ} (hU : IsOpen U) (δ : ℝ) :
    IsOpen (seedExitWindow U δ) :=
  hU.sdiff ((isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re.abs))

theorem zero_mem_seedExitWindow {U : Set ℂ} (hU : (0 : ℂ) ∈ U) {δ : ℝ} (hδ : 0 < δ) :
    (0 : ℂ) ∈ seedExitWindow U δ := by
  exact ⟨hU, by simpa using hδ⟩

/-- Continuity of the inverse extension and clearance of the seed supply a
whole real seed collar avoiding a closed old-boundary set. -/
theorem exists_real_seed_gap {F : ℂ → ℂ} (hF : ContinuousOn F Hbar)
    {C : Set ℂ} (hC : IsClosed C) (h0 : F 0 ∉ C) :
    ∃ δ > 0, ∀ a : ℝ, |a| < δ → F (a : ℂ) ∉ C := by
  have hreal : Continuous (fun a : ℝ => F (a : ℂ)) :=
    hF.comp_continuous continuous_ofReal (fun a => by change 0 ≤ (a : ℂ).im; simp)
  have hn : {a : ℝ | F (a : ℂ) ∉ C} ∈ 𝓝 (0 : ℝ) :=
    hreal.continuousAt.preimage_mem_nhds (hC.isOpen_compl.mem_nhds (by simpa using h0))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hn
  exact ⟨δ, hδ, fun a ha => hball (by simpa [Real.dist_eq] using ha)⟩

/-- The weaker landing condition on a concrete window follows from the
bounded inverse extension, the seed gap, and physical first-contact data.
No forward-chart boundary limit is assumed. -/
theorem hasAccessLanding_on_seedExitWindow {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {U : Set ℂ} (hUb : Bornology.IsBounded U) (δ : ℝ)
    (hF : ∀ x ∈ E,
      EqOn (boundedInverse (c x)) (cayley ∘ (c x).2.1) H ∧
      ContinuousOn (boundedInverse (c x)) Hbar ∧
      DifferentiableOn ℂ (boundedInverse (c x)) H ∧ InjOn (boundedInverse (c x)) H ∧
      ∀ z : ℂ, z.im = 0 → boundedInverse (c x) z ∉ boundedInverse (c x) '' H)
    (C : X → Set ℂ)
    (hseed : ∀ x ∈ E, ∀ a : ℝ, |a| < δ → boundedInverse (c x) (a : ℂ) ∉ C x)
    (hCH : ∀ x ∈ E, Disjoint (boundedInverse (c x) '' H) (C x))
    (hcontact : ∀ x ∈ E, 0 < T x → T x < ⊤ → cayley (ρ x (T x).toNNReal) ∈ C x) :
    HasAccessLanding E c ρ T (seedExitWindow U δ) := by
  apply hasAccessLanding_of_comp_limits hs (hUb.subset sdiff_subset)
    (fun x => boundedInverse (c x)) (fun x => cayley (ρ x (T x).toNNReal))
    (fun x hx => (hF x hx).2.2.1) (fun x hx => (hF x hx).2.1)
    (fun x hx => (hF x hx).2.2.2.1) (fun x hx => (hF x hx).2.2.2.2)
  · intro x hx hT0 hTfin
    have hxev : x ∈ exitEv E c ρ T (seedExitWindow U δ) :=
      ⟨⟨hx, hT0⟩, (IsRestartSpec.exitTime_le x).trans_lt hTfin⟩
    have hcl := hs.mem_closure_at_T hxev hTfin
    have hbar : ρ x (T x).toNNReal ∈ Hbar := closure_H ▸
      closure_mono (hs.conf x hx).dom_subset hcl
    have hlim : Tendsto (fun u => cayley (ρ x u)) (𝓝[<] (T x).toNNReal)
        (𝓝 (cayley (ρ x (T x).toNNReal))) :=
      ((QuantumZipper.CA.differentiableAt_cayley
        (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg hbar)).continuousAt.tendsto.comp
          (hs.contρ x hx).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    refine hlim.congr' ?_
    have heT := ENNReal.coe_toNNReal hTfin.ne
    have he0 : 0 < (T x).toNNReal := by exact_mod_cast (heT ▸ hT0)
    filter_upwards [Ioo_mem_nhdsLT he0] with u hu
    have huT : (u : ℝ≥0∞) < T x := by rw [← heT]; exact ENNReal.coe_lt_coe.2 hu.2
    rw [hs.inPath_eq_fwd hx hu.1 huT, (hF x hx).1 ((hs.conf x hx).fwd_mem (hs.inside x hx u hu.1 huT))]
    dsimp only [Function.comp_apply]
    rw [(hs.conf x hx).inv_fwd (hs.inside x hx u hu.1 huT)]
  · intro x hx hT0 _ hTfin
    rintro ⟨z, ⟨hzV, hzbar⟩, he⟩
    have hpC := hcontact x hx hT0 hTfin
    rcases (show 0 ≤ z.im from hzbar).eq_or_lt with hz0 | hz0
    · have ha : |z.re| < δ := lt_of_not_ge fun ha => hzV.2 ⟨hz0.symm, ha⟩
      have hzre : (z.re : ℂ) = z := Complex.ext rfl (by simp [hz0.symm])
      exact hseed x hx z.re ha (by rwa [hzre, he])
    · exact (hCH x hx).le_bot ⟨⟨z, hz0, he⟩, hpC⟩

end InteractingSLE.Sec5.Aux61GInst
