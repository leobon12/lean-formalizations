/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VhLift

/-!
# SB2(1)'s version half: the relative curve defined from the flow

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). The version's relative curve must be a
function of the flow, not a chosen lift. It is defined deterministically:

* `goodTimes η u t_L A'`: the times `s` after the entrance at which the shifted flow `η(t_L + s) − u` lies in the
  shifted chart domain `ℍ \ fill A'`;
* **`liftOf c' η u t_L A'`**: the continuous extension (`extendFrom`) from the good times of the forward chart image
  `s ↦ c'(η(t_L + s) − u)`;
* `mem_closure_goodTimes`: below a horizon where the bad times have empty interior, every time is a limit of good
  times before the horizon;
* **`liftOf_eq`**: in a chain record (domain chart `c'` with boundary map `g`, S2 lift `γ`, agreement with `η − u`
  before `t_L + S₁`, bad times of empty interior), `liftOf … s = γ s` for every `s < S₁`. So every record has the same
  lift, namely `liftOf`.

Deterministic in the data; nothing here replaces a source statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Vc

open Lv

/-- The good times after the entrance: the shifted flow lies in the shifted chart domain. -/
def goodTimes (η : ℝ≥0 → ℂ) (u : ℝ) (tL : ℝ≥0) (A' : Set ℂ) : Set ℝ≥0 :=
  {s | η (tL + s) - u ∈ H \ fillH A'}

/-- **The lift read from the flow**: the continuous extension of `s ↦ c'(η(t_L + s) − u)` from the good times. -/
def liftOf (c' : Chart) (η : ℝ≥0 → ℂ) (u : ℝ) (tL : ℝ≥0) (A' : Set ℂ) : ℝ≥0 → ℂ :=
  extendFrom (goodTimes η u tL A') fun s => c'.1 (η (tL + s) - u)

/-- **Good times accumulate at every time below the horizon** when the bad times have empty interior. -/
theorem mem_closure_goodTimes {η β' : ℝ≥0 → ℂ} {u : ℝ} {tL : ℝ≥0} {A' : Set ℂ} {S₁ : ℝ}
    (hagree : ∀ t : ℝ≥0, (t : ℝ) < (tL : ℝ) + S₁ → β' t = η t - u)
    (hbad : interior {r ∈ Ioo (0 : ℝ) S₁ | β' (tL + r.toNNReal) ∉ H \ fillH A'} = ∅) {s : ℝ≥0}
    (hs : (s : ℝ) < S₁) : s ∈ closure (goodTimes η u tL A' ∩ Iio S₁.toNNReal) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set a₀ : ℝ := max ((s : ℝ) - ε) 0
  set b₀ : ℝ := min ((s : ℝ) + ε) S₁
  have hs0 : (0 : ℝ) ≤ s := s.2
  have hab : a₀ < b₀ := by
    refine max_lt (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
  have hsub : ¬ Ioo a₀ b₀ ⊆ {r ∈ Ioo (0 : ℝ) S₁ | β' (tL + r.toNNReal) ∉ H \ fillH A'} := by
    intro h
    have hI := interior_maximal h isOpen_Ioo
    rw [hbad] at hI
    obtain ⟨x, hx⟩ := nonempty_Ioo.2 hab
    exact hI hx
  rw [not_subset] at hsub
  obtain ⟨r, hr, hrbad⟩ := hsub
  have hr0 : 0 < r := lt_of_le_of_lt (le_max_right _ _) hr.1
  have hrS : r < S₁ := lt_of_lt_of_le hr.2 (min_le_right _ _)
  have hgood : β' (tL + r.toNNReal) ∈ H \ fillH A' := by
    by_contra hn
    exact hrbad ⟨⟨hr0, hrS⟩, hn⟩
  refine ⟨r.toNNReal, ⟨?_, ?_⟩, ?_⟩
  · show η (tL + r.toNNReal) - u ∈ H \ fillH A'
    rw [← hagree _ (by rw [NNReal.coe_add, Real.coe_toNNReal _ hr0.le]; linarith)]
    exact hgood
  · exact Real.toNNReal_lt_toNNReal_iff_of_nonneg hr0.le |>.2 hrS
  · rw [NNReal.dist_eq, Real.coe_toNNReal _ hr0.le, abs_lt]
    constructor
    · linarith [lt_of_lt_of_le hr.2 (min_le_left ((s : ℝ) + ε) S₁)]
    · linarith [lt_of_le_of_lt (le_max_left ((s : ℝ) - ε) 0) hr.1]

/-- **Every record's lift is `liftOf`** below its horizon. -/
theorem liftOf_eq {A' : Set ℂ} {c' : Chart} (hD : IsDomainChart (H \ fillH A') c') {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c'.2.1 H) {β' γ η : ℝ≥0 → ℂ} {tL : ℝ≥0} {u S₁ : ℝ}
    (hγ : Supp9B.IsProperCurve γ) (hlift : ∀ s, g (γ s) = β' (tL + s))
    (hagree : ∀ t : ℝ≥0, (t : ℝ) < (tL : ℝ) + S₁ → β' t = η t - u)
    (hbad : interior {r ∈ Ioo (0 : ℝ) S₁ | β' (tL + r.toNNReal) ∉ H \ fillH A'} = ∅) {s : ℝ≥0}
    (hs : (s : ℝ) < S₁) : liftOf c' η u tL A' s = γ s := by
  have hmem := mem_closure_goodTimes hagree hbad hs
  have hsS : s < S₁.toNNReal := Real.lt_toNNReal_iff_coe_lt.2 hs
  have hev : (fun s' => c'.1 (η (tL + s') - u)) =ᶠ[𝓝[goodTimes η u tL A'] s] γ := by
    filter_upwards [inter_mem_nhdsWithin (goodTimes η u tL A') (Iio_mem_nhds hsS)] with s' hs'
    exact (Vh.lift_eq_fwd hD hgc hgi hγ hlift hagree (Real.lt_toNNReal_iff_coe_lt.1 hs'.2) hs'.1).symm
  have ht : Tendsto (fun s' => c'.1 (η (tL + s') - u)) (𝓝[goodTimes η u tL A'] s) (𝓝 (γ s)) :=
    ((hγ.1.continuousAt (x := s)).tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
  exact extendFrom_eq (closure_mono inter_subset_left hmem) ht

end InteractingSLE.Theorem14.SB.Vc
