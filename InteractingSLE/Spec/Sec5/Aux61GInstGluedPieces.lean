/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstSeedPieces

/-! # Countable measurable landing pieces for the glued restart chart -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Complex MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61GInst
open Aux61FibData Aux61Restart
open WangWu (negInv)

/-- Restricting the restart event preserves all physical restart data. -/
theorem isRestartSpec_of_subset {X : Type*} [MeasurableSpace X]
    {E E' : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) (hE' : MeasurableSet E') (hsub : E' ⊆ E) :
    IsRestartSpec E' c ρ T :=
  ⟨hE', hs.measT, hs.measρ, fun x hx => hs.contρ x (hsub hx), hs.chart,
    fun x hx => hs.conf x (hsub hx), fun x hx => hs.start_mem x (hsub hx),
    fun x hx => hs.start_lim x (hsub hx), fun x hx => hs.inside x (hsub hx)⟩

/-- The source's retained chart and physical first hitting time admit
countably many measurable landing pieces. A fixed rational collar on each
piece suffices for the successor code; there is no unrestricted forward
limit at a physical contact point among the inputs. -/
theorem exists_glued_landing_pieces {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {W : X → ℝ → ℝ} {β η : X → ℝ → ℂ}
    {s r : ℝ} (hs0 : 0 ≤ s)
    (hβ : ∀ x ∈ E, IsLoewnerTrace (W x) (β x))
    (hβm : ∀ t, Measurable (fun x => β x t))
    (hη : ∀ x ∈ E, ContinuousOn (η x) (Icc 0 r))
    (hηH : ∀ x ∈ E, MapsTo (η x) (Icc 0 r) Hbar) {b : X → ℂ}
    (hb : ∀ x ∈ E, b x ∈ retainedDomain (negInv '' QuantumZipper.fwdHull (W x) s) (η x) r)
    (hdom : ∀ x ∈ E, ((c x).dom : Set ℂ) =
      restartComponent (negInv '' QuantumZipper.fwdHull (W x) s) (η x) r (b x))
    (hT : T = hitTime ρ (fun x => (H \ negInv '' QuantumZipper.fwdHull (W x) s)ᶜ))
    {U : Set ℂ} (hUb : Bornology.IsBounded U) :
    ∃ S : ℕ × ℕ → Set X, (∀ p, MeasurableSet (S p)) ∧
      E ∩ {x | 0 < T x} = ⋃ p, S p ∧ (∀ p, S p ⊆ E) ∧
      (∀ p, IsRestartSpec (S p) c ρ T) ∧
      ∀ p, HasAccessLanding (S p) c ρ T (seedExitWindow U (collarRadius p.1)) := by
  classical
  let Ep := E ∩ {x | 0 < T x}
  let C : X → Set ℂ := fun x => oldModelBoundary (counterflowRecord (β x) s)
  let F : X → ℝ → ℂ := fun x a => boundedInverse (c x) (a : ℂ)
  have hEp : MeasurableSet Ep := hs.measurableSet.inter (measurableSet_lt measurable_const hs.measT)
  have hF : ∀ x ∈ Ep, EqOn (boundedInverse (c x))
      (QuantumZipper.CA.cayley ∘ (c x).2.1) H ∧ ContinuousOn (boundedInverse (c x)) Hbar := by
    intro x hx
    have hh := boundedInverse_spec_of_traces (hβ x hx.1) hs0 (hη x hx.1) (hηH x hx.1)
      (hb x hx.1) (hs.conf x hx.1) (hdom x hx.1)
    exact ⟨hh.1, hh.2.1⟩
  have hFm : ∀ a, Measurable (Ep.indicator fun x => F x a) :=
    fun a => measurable_boundedInverse_real hEp hs.chart (fun x hx => hs.conf x hx.1) hF a
  have hFc : ∀ x ∈ Ep, Continuous (F x) := fun x hx =>
    (hF x hx).2.comp_continuous continuous_ofReal (fun a => by change 0 ≤ (a : ℂ).im; simp)
  have hCm : ∀ z, Measurable (Ep.indicator fun x => infDist z (C x)) := by
    intro z
    have hd : Measurable (fun x : Ep => infDist z (C x)) :=
      measurable_infDist_oldModelBoundary
        (β := fun x : Ep => β x.1) (s := s)
        (fun x => (hβ x x.2.1).2.1.mono Icc_subset_Ici_self)
        (fun t => (hβm t).comp measurable_subtype_coe) z
    have hzero : Measurable (fun _ : (Epᶜ : Set X) => (0 : ℝ)) := measurable_const
    have hm := Measurable.dite hd hzero hEp
    convert hm using 1
    funext x
    by_cases hx : x ∈ Ep <;> simp [hx]
  have hCc : ∀ x ∈ Ep, IsClosed (C x) := by
    intro x hx
    exact (isCompact_oldModelBoundary
      (isCompact_Icc.image_of_continuousOn (continuous_clipH.comp_continuousOn
        ((hβ x hx.1).2.1.mono Icc_subset_Ici_self)))
      (by rintro _ ⟨t, -, rfl⟩; exact clipH_mem_Hbar _)).isClosed
  have hCne : ∀ x ∈ Ep, (C x).Nonempty := fun x _ => ⟨1, Or.inl (by simp)⟩
  have hgap : ∀ x ∈ Ep, ∃ δ > 0, ∀ a : ℝ, |a| < δ → F x a ∉ C x :=
    fun x hx => exists_glued_seed_gap hs hs0 hβ hη hηH hb hdom hT x hx.1 hx.2
  obtain ⟨S, hSm, hcover, hsub, hfree⟩ :=
    exists_measurable_seedPieces hEp hFm hFc hCm hCc hCne hgap
  have hSE : ∀ p, S p ⊆ E := fun p _ hx => (hsub p hx).1
  have hspec : ∀ p, IsRestartSpec (S p) c ρ T :=
    fun p => isRestartSpec_of_subset hs (hSm p) (hSE p)
  refine ⟨S, hSm, hcover, hSE, hspec, fun p => ?_⟩
  apply hasAccessLanding_glued_restart (hspec p) hs0
    (fun x hx => hβ x (hSE p hx)) (fun x hx => hη x (hSE p hx))
    (fun x hx => hηH x (hSE p hx)) (fun x hx => hb x (hSE p hx))
    (fun x hx => hdom x (hSE p hx)) hT hUb (collarRadius p.1)
  exact fun x hx a ha => hfree p x hx a ha.le

end InteractingSLE.Sec5.Aux61GInst
