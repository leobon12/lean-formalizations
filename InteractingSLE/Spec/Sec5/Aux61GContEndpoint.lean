/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstAccessLanding
import InteractingSLE.Spec.Sec5.Aux61GInstAccessVisit

/-! # Finite prime-end endpoints and endpoint visits

The named input `hinverse_target` records continuity of the inverse at the
retained original target. A different physical endpoint then has bounded
chart coordinates, so the existing connected-cluster theorem gives its
finite selected-access limit.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.Aux61GCont
open Aux61GInst Aux61FibData

/-- Inverse continuity at the retained target bounds any approaching chart
path whose physical limit is different from that target. -/
theorem exists_eventual_bound_of_inverse_target {α : Type*} {l : Filter α}
    {γ : α → ℂ} {F : ℂ → ℂ} {p target : ℂ}
    (hH : ∀ᶠ u in l, γ u ∈ H)
    (hlim : Tendsto (F ∘ γ) l (𝓝 p)) (hne : p ≠ target)
    (hinverse_target : ∀ ε > 0, ∃ R : ℝ, ∀ z ∈ H, R ≤ ‖z‖ → dist (F z) target < ε) :
    ∃ R : ℝ, ∀ᶠ u in l, ‖γ u‖ ≤ R := by
  have hd : 0 < dist p target := dist_pos.2 hne
  obtain ⟨R, hR⟩ := hinverse_target (dist p target / 2) (half_pos hd)
  refine ⟨R, ?_⟩
  have hnear := (Metric.tendsto_nhds.1 hlim) _ (half_pos hd)
  filter_upwards [hH, hnear] with u hu hpu
  by_contra hn
  have htu := hR (γ u) hu (le_of_not_ge hn)
  have htri := dist_triangle p (F (γ u)) target
  dsimp only [Function.comp_apply] at hpu
  rw [dist_comm (F (γ u)) p] at hpu
  linarith only [hpu, htu, htri]

/-- A non-target finite physical contact has an actual finite chart limit
along its own access. No full-domain forward landing statement is used. -/
theorem exists_finite_accessEndpoint_of_target {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E)
    {e : ℝ≥0} (he : 0 < e) (heT : (e : ℝ≥0∞) ≤ T x)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F H) (hFc : ContinuousOn F Hbar)
    (hFi : InjOn F H) (hFR : ∀ z : ℂ, z.im = 0 → F z ∉ F '' H)
    {p target : ℂ}
    (hlim : Tendsto (F ∘ inPath E c ρ T x) (𝓝[<] e) (𝓝 p)) (hne : p ≠ target)
    (hinverse_target : ∀ ε > 0, ∃ R : ℝ, ∀ z ∈ H, R ≤ ‖z‖ → dist (F z) target < ε) :
    ∃ L ∈ Hbar, F L = p ∧ Tendsto (inPath E c ρ T x) (𝓝[<] e) (𝓝 L) := by
  have : (𝓝[<] e).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, he⟩
  have hH : ∀ᶠ u in 𝓝[<] e, inPath E c ρ T x u ∈ H := by
    filter_upwards [Ioo_mem_nhdsLT he] with u hu
    have huT := (ENNReal.coe_lt_coe.2 hu.2).trans_le heT
    rw [hs.inPath_eq_fwd hx hu.1 huT]
    exact (hs.conf x hx).fwd_mem (hs.inside x hx u hu.1 huT)
  obtain ⟨R, hR⟩ := exists_eventual_bound_of_inverse_target hH hlim hne hinverse_target
  exact YuanCharacterisation.exists_tendsto_of_tendsto_comp_filter hFd hFc hFi hFR
    (inPath_connected_left_basis hs hx he heT) (hH.mono fun _ hu => QuantumZipper.H_subset_Hbar hu) hR hlim

/-- Capturing every pre-contact point makes the capped window exit equal
the physical contact time. -/
theorem exitTime_eq_of_before_mem {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
    (hs : IsRestartSpec E c ρ T) (hV : IsOpen V) {x : X} (hx : x ∈ E)
    (hbefore : ∀ u : ℝ≥0, (u : ℝ≥0∞) < T x → inPath E c ρ T x u ∈ V) :
    Aux61FibData.exitTime E c ρ T V x = T x := by
  apply le_antisymm (IsRestartSpec.exitTime_le x)
  by_contra hn
  obtain ⟨u, heu, huT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_of_not_ge hn)
  have hu := IsRestartSpec.lt_exitTime_of hx (fun v hv => hbefore v
    ((ENNReal.coe_lt_coe.2 hv).trans huT)) (hs.eventually_mem_of_lt hx hV huT (hbefore u huT))
  exact (not_lt_of_ge heu.le) hu

/-- A finite contact or a witnessed window exit gives the finite exit event.
This also permits infinite physical lifetimes. -/
theorem mem_exitEv_of_contact_or_exit {X : Type*} {E : Set X} {c : X → Chart}
    {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ} {x : X}
    (hx : x ∈ E) (hpos : 0 < T x)
    (hstop : T x < ⊤ ∨ ∃ u : ℝ≥0, (u : ℝ≥0∞) < T x ∧ inPath E c ρ T x u ∉ V) :
    x ∈ exitEv E c ρ T V := by
  rcases hstop with hfin | ⟨u, -, hu⟩
  · exact mem_exitEv_of_finite hx hpos hfin
  · refine ⟨⟨hx, hpos⟩, lt_of_le_of_lt (b := (u : ℝ≥0∞)) ?_ ENNReal.coe_lt_top⟩
    exact le_of_not_gt fun h => hu (IsRestartSpec.lt_exitTime h).2

/-- The source's completed-window geometry supplies the cover's visit
condition, without a code-level visit assumption. -/
theorem accessExitCode_mem_visitSet_of_contact {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
    (hs : IsRestartSpec E c ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
    (hland : HasAccessLanding E c ρ T V)
    (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
    {x : X} (hx : x ∈ E) (hpos : 0 < T x) (hfin : T x < ⊤)
    (hbefore : ∀ u : ℝ≥0, (u : ℝ≥0∞) < T x → inPath E c ρ T x u ∈ V)
    {a k p q y : ℝ} {h : X → DistOn upperHalfPlaneOpens} (hy : y ∈ Ioo p q)
    (hendpoint : Tendsto (inPath E c ρ T x) (𝓝[<] (T x).toNNReal) (𝓝 (y : ℂ))) :
    accessExitCode E c ρ T V a k h x ∈ visitSet p q := by
  have hxev : x ∈ exitEv E c ρ T V := mem_exitEv_of_finite hx hpos hfin
  apply accessExitCode_mem_visitSet hs hV hV0 hland hinj hxev hy
  have hexit := exitTime_eq_of_before_mem hs hV hx hbefore
  have he : exitNN E c ρ T V x = (T x).toNNReal := by
    rw [← hexit, ← IsRestartSpec.coe_exitNN hxev, ENNReal.toNNReal_coe]
  have hpositive : 0 < (T x).toNNReal := ENNReal.toNNReal_pos hpos.ne' hfin.ne
  have : (𝓝[<] (T x).toNNReal).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpositive⟩
  unfold accessExitPoint
  rw [he]
  exact hendpoint.limUnder_eq

end InteractingSLE.Sec5.Aux61GCont
