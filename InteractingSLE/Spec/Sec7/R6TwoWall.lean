/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76ExitChart
import InteractingSLE.Spec.Sec7.R6SafeIncl

/-!
# R.6: an unvisited shared wall and the two current domains

PROVE-R6-TWO. The shared side in the two-outer-arm comparison is the left
side, with weight `rL` in both pockets. The planar ray lemma is already
available as `HalfPlaneSep.isFreeAt_of_not_isBounded`. We specialize it to
left real rays and pull its unfilled collars back through the two initial
pocket coordinates. This works for finite targets and targets at infinity.

These are deterministic helpers. They do not assert that the actual R.6
configuration supplies the required shared-wall point or contact ordering.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Two

open HalfPlaneSep

/-- A real point to the left of every real contact of a compact trace has
an unfilled upper half-disc. Interior trace points may lie on either side. -/
theorem isFreeAt_of_real_contacts_ge {F : Set ℂ} (hF : IsCompact F) {a x : ℝ}
    (hcontact : ∀ z ∈ F, z.im = 0 → a ≤ z.re) (hx : x < a) :
    IsFreeAt F (x : ℂ) := by
  apply isFreeAt_of_not_isBounded hF.isClosed hF.isBounded
    (isPreconnected_Iio.image Complex.ofReal Complex.continuous_ofReal.continuousOn)
    (Lemma76Exit.not_isBounded_ofReal_Iio a)
    (fun z hz => ?_) (x : ℂ) (show (x : ℂ) ∈ Complex.ofReal '' Iio a from ⟨x, hx, rfl⟩)
  obtain ⟨t, ht, rfl⟩ := hz
  refine ⟨by simp only [mem_ofPred_eq, Complex.ofReal_im, le_refl], ?_⟩
  intro htF
  have h := hcontact (t : ℂ) htF (Complex.ofReal_im t)
  exact (not_le_of_gt ht) h

/-- Pull back the two unfilled chart collars at a shared wall point. The
physical neighbourhood lies in both actual relative hull complements;
no equality with the ambient hull complement is used. -/
theorem exists_ball_subset_pullbacks_of_isFreeAt {C U F G : Set ℂ}
    {ψ φ : ℂ → ℂ} {p : ℂ} (hUC : U ⊆ C) (hψH : MapsTo ψ C H) (hφH : MapsTo φ U H)
    (hψc : ContinuousWithinAt ψ C p) (hφc : ContinuousWithinAt φ U p)
    (hF : IsFreeAt F (ψ p)) (hG : IsFreeAt G (φ p)) :
    ∃ ε > 0, U ∩ ball p ε ⊆
      (C ∩ ψ ⁻¹' (H \ fillH F)) ∩ (U ∩ φ ⁻¹' (H \ fillH G)) := by
  obtain ⟨r, hr, hFr⟩ := hF
  obtain ⟨s, hs, hGs⟩ := hG
  obtain ⟨δ, hδ, hψδ⟩ := Metric.continuousWithinAt_iff.1 hψc r hr
  obtain ⟨δ', hδ', hφδ'⟩ := Metric.continuousWithinAt_iff.1 hφc s hs
  refine ⟨min δ δ', lt_min hδ hδ', ?_⟩
  rintro z ⟨hzU, hzB⟩
  have hzδ : dist z p < δ := (mem_ball.1 hzB).trans_le (min_le_left _ _)
  have hzδ' : dist z p < δ' := (mem_ball.1 hzB).trans_le (min_le_right _ _)
  exact ⟨⟨hUC hzU, hFr ⟨hψδ (hUC hzU) hzδ, hψH (hUC hzU)⟩⟩,
    ⟨hzU, hGs ⟨hφδ' hzU hzδ', hφH hzU⟩⟩⟩

/-- The shared unvisited wall supplies the common point needed by the
current-domain inclusion lemma. Both domains retain their own relative
hulls, as required for outer pockets. -/
theorem current_domains_meet_of_isFreeAt {C U F G : Set ℂ}
    {ψ φ : ℂ → ℂ} {p : ℂ} {outer inner : Chart}
    (hUC : U ⊆ C) (hψH : MapsTo ψ C H) (hφH : MapsTo φ U H)
    (hψc : ContinuousWithinAt ψ C p) (hφc : ContinuousWithinAt φ U p)
    (hF : IsFreeAt F (ψ p)) (hG : IsFreeAt G (φ p)) (hp : p ∈ closure U)
    (hOuter : (outer.dom : Set ℂ) = C ∩ ψ ⁻¹' (H \ fillH F))
    (hInner : (inner.dom : Set ℂ) = U ∩ φ ⁻¹' (H \ fillH G)) :
    ((inner.dom : Set ℂ) ∩ (outer.dom : Set ℂ)).Nonempty := by
  obtain ⟨ε, hε, hboth⟩ := exists_ball_subset_pullbacks_of_isFreeAt hUC hψH hφH hψc hφc hF hG
  obtain ⟨z, hzU, hzp⟩ := Metric.mem_closure_iff.1 hp ε hε
  have hz := hboth ⟨hzU, mem_ball.2 ((dist_comm z p).trans_lt hzp)⟩
  exact ⟨z, hInner.symm ▸ hz.2, hOuter.symm ▸ hz.1⟩

/-- The common-point criterion with the left real-contact bounds of the
shared outer arm. These bounds are on the compact traces before filling. -/
theorem current_domains_meet_of_real_contact_order {C U F G : Set ℂ}
    {ψ φ : ℂ → ℂ} {p : ℂ} {outer inner : Chart} {a b x y : ℝ}
    (hUC : U ⊆ C) (hψH : MapsTo ψ C H) (hφH : MapsTo φ U H)
    (hψc : ContinuousWithinAt ψ C p) (hφc : ContinuousWithinAt φ U p)
    (hF : IsCompact F) (hG : IsCompact G)
    (hcontactF : ∀ z ∈ F, z.im = 0 → a ≤ z.re)
    (hcontactG : ∀ z ∈ G, z.im = 0 → b ≤ z.re)
    (hψp : ψ p = (x : ℂ)) (hφp : φ p = (y : ℂ)) (hx : x < a) (hy : y < b)
    (hp : p ∈ closure U)
    (hOuter : (outer.dom : Set ℂ) = C ∩ ψ ⁻¹' (H \ fillH F))
    (hInner : (inner.dom : Set ℂ) = U ∩ φ ⁻¹' (H \ fillH G)) :
    ((inner.dom : Set ℂ) ∩ (outer.dom : Set ℂ)).Nonempty := by
  apply current_domains_meet_of_isFreeAt hUC hψH hφH hψc hφc
    (hψp.symm ▸ isFreeAt_of_real_contacts_ge hF hcontactF hx)
    (hφp.symm ▸ isFreeAt_of_real_contacts_ge hG hcontactG hy) hp hOuter hInner

/-- Near a genuinely shared piece of the initial walls, an unfilled inner
collar gives R.6's inclusion of active complements at the shared landing.
The exposed counterflow landing requires its own prime-end argument. -/
theorem local_complement_subset_of_isFreeAt {C U G : Set ℂ} {φ : ℂ → ℂ} {p : ℂ}
    {outer inner : Chart} (hOuter : (outer.dom : Set ℂ) ⊆ C)
    (hInner : (inner.dom : Set ℂ) = U ∩ φ ⁻¹' (H \ fillH G))
    (hφH : MapsTo φ U H) (hφc : ContinuousWithinAt φ U p) (hG : IsFreeAt G (φ p))
    (hWall : ∃ r > 0, C ∩ ball p r ⊆ U) :
    ∃ ε > 0, (H \ (inner.dom : Set ℂ)) ∩ ball p ε ⊆ H \ (outer.dom : Set ℂ) := by
  obtain ⟨r, hr, hWallr⟩ := hWall
  obtain ⟨s, hs, hGs⟩ := hG
  obtain ⟨δ, hδ, hφδ⟩ := Metric.continuousWithinAt_iff.1 hφc s hs
  refine ⟨min r δ, lt_min hr hδ, ?_⟩
  rintro z ⟨⟨hzH, hzI⟩, hzB⟩
  refine ⟨hzH, fun hzO => hzI ?_⟩
  have hzU : z ∈ U := hWallr ⟨hOuter hzO,
    mem_ball.2 ((mem_ball.1 hzB).trans_le (min_le_left _ _))⟩
  rw [hInner]
  exact ⟨hzU, hGs ⟨hφδ hzU ((mem_ball.1 hzB).trans_le (min_le_right _ _)), hφH hzU⟩⟩

/-- The common-point criterion for the actual branch-shifted relative
charts used in all three two-outer-arm shapes. The domain identities and
the conversion from the relative Loewner hulls to traced fillings are
discharged by the existing pocket-chart API. -/
theorem relCharts_meet_of_isFreeAt {Ω : Type*} {A B : Set Ω}
    {C U : Ω → Set ℂ} {ψ φ : Ω → ℂ → ℂ} {n m : Ω → ℤ} {γ δ : Ω → ℝ → ℂ}
    {q q' : ℝ≥0} {ω : Ω} {p : ℂ}
    (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H)
    (hUo : ∀ ω ∈ B, IsOpen (U ω)) (hUH : ∀ ω ∈ B, U ω ⊆ H)
    (hφ : ∀ ω ∈ B, IsConformalBijection (φ ω) (U ω) H)
    (hωA : ω ∈ A) (hωB : ω ∈ B) (hγ : PocketTraversal.IsDrivenCurve (γ ω))
    (hδ : PocketTraversal.IsDrivenCurve (δ ω))
    (hq : (q : ℝ≥0∞) < Lemma71C.capLife (γ ω))
    (hq' : (q' : ℝ≥0∞) < Lemma71C.capLife (δ ω))
    (hUC : U ω ⊆ C ω) (hp : p ∈ closure (U ω))
    (hψc : ContinuousWithinAt (ψ ω) (C ω) p) (hφc : ContinuousWithinAt (φ ω) (U ω) p)
    (hF : IsFreeAt (γ ω '' Icc 0 (Lemma71C.capInv (γ ω) q)) (ψ ω p))
    (hG : IsFreeAt (δ ω '' Icc 0 (Lemma71C.capInv (δ ω) q')) (φ ω p)) :
    (((PocketStop.relChart (fun ω => PocketStopField.shiftChart
        (PocketStopField.pChart B U φ ω) (m ω)) δ q' ω).dom : Set ℂ) ∩
      ((PocketStop.relChart (fun ω => PocketStopField.shiftChart
        (PocketStopField.pChart A C ψ ω) (n ω)) γ q ω).dom : Set ℂ)).Nonempty := by
  have hOuter := R6Safe.relChart_dom_eq_inter (n := n) hCo hCH hψ hωA hγ hq
  have hInner := R6Safe.relChart_dom_eq_inter (n := m) hUo hUH hφ hωB hδ hq'
  rw [hγ.fwdHull_segDriver q.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)] at hOuter
  rw [hδ.fwdHull_segDriver q'.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq')] at hInner
  exact current_domains_meet_of_isFreeAt hUC (hψ ω hωA).2.mapsTo (hφ ω hωB).2.mapsTo
    hψc hφc hF hG hp hOuter hInner

end InteractingSLE.Sec7.R6Two
