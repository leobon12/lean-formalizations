/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntFiberFamily
import InteractingSLE.Spec.Supplement.WalkIntBridgePrefix

/-!
# Ordinary matches require only one designated transition coordinate

Regularity supplies normalization, proper extensions and prefix avoidance.
The component's physical collar supplies all neighboring real limits.
Identifying the central incident side remains a geometric obligation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntFiber

open WalkBdry WalkIntCanon WalkMean Exist.StagedLaw

/-- Deterministic facts of all live recorded prefixes. These are proved
for the actual walks below, rather than retained as a global input. -/
def PrefixBoundaryFacts (s : ExplState) : Prop :=
  ∀ (pre post : List Piece) (pc : Piece) (τ : ℝ≥0),
    s.1 = pre ++ pc :: post → (τ : ℝ≥0∞) < pc.2.2 →
      IsNormalized (prefixChart pc τ) ∧ GW1P.HasProperBdryExt (prefixChart pc τ) ∧
        Disjoint ((prefixChart pc τ).dom : Set ℂ) (prefixSet pre pc τ)

theorem prefixBoundaryFacts_run {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
      D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1
        (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2))
    (hD : ∀ k, Exist.Staged.IsRegularDriver (D k)) :
    PrefixBoundaryFacts (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length) := by
  intro pre post pc τ hs hτ
  exact ⟨isNormalized_prefixChart _ D _ (fun j _ c θ' hl => hreg j c θ' hl) hD hs hτ,
    hasProperBdryExt_prefixChart θ right D hreg hD hs hτ,
    WalkIntBridge.prefixChart_disjoint_prefixSet θ right D hreg hD hs hτ⟩

/-- Local physical matching and the selected central incident coordinate.
There are no interval transition limits or boundary lift comparisons. -/
def IsPiecePhysicalMatch (s s' : ExplState) (left : Bool) (c : Chart)
    {d : Chart} (B : HullModel d) (x : ℝ) : Prop :=
  ∃ (pre post : List Piece) (pc : Piece) (τ : ℚ≥0) (y : ℝ) (p : ℂ) (r δ : ℝ)
    (A : HullModel (prefixChart pc τ)),
    s.1 = pre ++ pc :: post ∧ (((τ : ℝ≥0)) : ℝ≥0∞) < pc.2.2 ∧
    (if left then IsLeftSidePt pc τ y else IsRightSidePt pc τ y) ∧
    Tendsto (prefixChart pc τ).2.1 (𝓝[H] (y : ℂ)) (𝓝 p) ∧
    p ∈ wsetOf s ∪ {z : ℂ | z.im = 0} ∧ 0 < r ∧
    wsetOf s ∩ ball p r ⊆ prefixSet pre pc τ ∧
    wsetOf s' ∩ ball p r ⊆ wsetOf s ∧ A.hull ⊆ B.hull ∧ 0 < δ ∧
    (∀ w ∈ H ∩ ball (x : ℂ) δ, c.2.1 w ∈ (prefixChart pc τ).dom) ∧
    Tendsto (fun w => (prefixChart pc τ).1 (c.2.1 w))
      (𝓝[H] (x : ℂ)) (𝓝 (y : ℂ))

/-- All neighboring real transition limits follow from the original
physical collar conditions and the regularity of the recorded prefixes. -/
theorem isPieceIncidentMatch_of_physical {s s' : ExplState} {left : Bool}
    {R L C : Set ℂ} {c d : Chart} {B : HullModel d} {x : ℝ}
    (hchart : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H)
    (hwall : (R ∪ L) ∩ H = wsetOf s ∪ wsetOf s')
    (hprefix : PrefixBoundaryFacts s) (hx : x ≠ 0)
    (h : IsPiecePhysicalMatch s s' left c B x) :
    WalkIntGerm.IsPieceIncidentMatch s s' left c B x := by
  obtain ⟨pre, post, pc, τ, y, p, r, ρ, A, h1, h2, h3, h4, h5, h6, h7, h8,
    hAB, hρ, hdom, hT⟩ := h
  obtain ⟨hnorm, hproper, hdisj⟩ := hprefix pre post pc τ h1 h2
  have hnear : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H ∩ ball (x : ℂ) ρ :=
    inter_mem_nhdsWithin H (ball_mem_nhds (x : ℂ) hρ)
  have hTw : Tendsto (fun z => (prefixChart pc τ).1 (c.2.1 z))
      (𝓝[H] (x : ℂ)) (𝓝[H] (y : ℂ)) := by
    exact tendsto_nhdsWithin_iff.2 ⟨hT, hnear.mono fun z hz =>
      hnorm.conformal.fwd_mem (hdom z hz)⟩
  have hland : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) := by
    refine (h4.comp hTw).congr' ?_
    filter_upwards [hnear] with z hz
    exact hnorm.conformal.inv_fwd (hdom z hz)
  have havoid : Disjoint ((prefixChart pc τ).dom : Set ℂ)
      (((R ∪ L) ∩ H) ∩ ball p r) := by
    rw [hwall]
    refine Set.disjoint_left.2 fun z hz ⟨hw, hb⟩ => ?_
    have hown : z ∈ wsetOf s := hw.elim id (fun ho => h8 ⟨ho, hb⟩)
    exact Set.disjoint_left.1 hdisj hz (h7 ⟨hown, hb⟩)
  obtain ⟨δ, hδ, -, hdom', hlim⟩ := exists_realLimits_of_component_collar
    hchart hCo hCH hnorm.conformal hproper hx h6 hρ hland havoid hdom
  exact ⟨pre, post, pc, τ, y, p, r, δ, A, h1, h2, h3, h4, h5, h6, h7, h8,
    hnorm, hAB, hδ, hdom', hT, hlim⟩

end InteractingSLE.Theorem14.WalkIntFiber
