/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YeLine

/-!
# The retained hull as the filling of a boundary arc of its chart

Packet PROVE-T14-SB2LIFT (round 32; `IsStageS2`'s retained path). For a domain chart `Ψ` of `ℍ ∖ D` (`D ⊆ ℍ` bounded)
whose inverse extends continuously to `g` on `ℍ̄` within distance `C` of the identity, with real values on `(0, ∞)`:

* `mem_of_real`: the values of `g` on `ℝ` that lie in `ℍ` lie in `D`;
* `exists_real_of_frontier`: every point of `D` in the closure of `ℍ ∖ D` is `g y` for a real `y ≤ 0`, `|y| ≤ ‖p‖ + C`;
* **`fillH_arc_eq`**: `fill (g([−K, 0])) = D` for `K ≥ sup_D ‖·‖ + C`.
Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Sx

variable {D : Set ℂ} {Ψ : Chart} {g : ℂ → ℂ} {C : ℝ}

/-- `ℍ` is unbounded. -/
theorem not_isBounded_H : ¬ IsBounded H := by
  intro hb
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  have hmem : (((|R| + 1 : ℝ) : ℂ) * Complex.I) ∈ H := by
    show 0 < (((|R| + 1 : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one,
      mul_zero, add_zero]
    positivity
  have h := hR _ hmem
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h
  linarith [le_abs_self R]

section Arc

variable (hΨD : IsDomainChart (H \ D) Ψ) (hg : ∀ p ∈ Hbar, Tendsto Ψ.2.1 (𝓝[H] p) (𝓝 (g p)))
  (hgb : ∀ p ∈ Hbar, ‖g p - p‖ ≤ C) (hgc : ContinuousOn g Hbar) (hgH : EqOn g Ψ.2.1 H) (hDH : D ⊆ H)

include hΨD hg in
/-- The values of `g` on `ℝ` that lie in `ℍ` lie in `D`. -/
theorem mem_of_real {y : ℝ} (hy : g y ∈ H) : g y ∈ D := by
  by_contra hyD
  have hyU : g y ∈ H \ D := ⟨hy, hyD⟩
  have hyH : (y : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (y : ℂ).im by simp
  have : (𝓝[H] (y : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H hyH
  have hcont : ContinuousAt Ψ.1 (g y) :=
    (hΨD.differentiableOn_fwd.differentiableAt (hΨD.isOpen.mem_nhds hyU)).continuousAt
  have h1 := hcont.tendsto.comp (hg y hyH)
  have h2 : Tendsto (fun w => Ψ.1 (Ψ.2.1 w)) (𝓝[H] (y : ℂ)) (𝓝 (y : ℂ)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall fun w hw => (hΨD.fwd_inv hw).symm)
  have heq : Ψ.1 (g y) = y := tendsto_nhds_unique h1 h2
  have hmem := hΨD.fwd_mem hyU
  rw [heq] at hmem
  have : (0 : ℝ) < (y : ℂ).im := hmem
  simp at this

include hΨD hgb hgc hgH hDH in
/-- Every point of `D` in the closure of `ℍ ∖ D` is `g y` for some real `y ≤ 0` with `|y| ≤ ‖p‖ + C`. -/
theorem exists_real_of_frontier (hpos : ∀ y : ℝ, 0 < y → (g y).im = 0) {p : ℂ} (hp : p ∈ D)
    (hpc : p ∈ closure (H \ D)) : ∃ y : ℝ, y ≤ 0 ∧ |y| ≤ ‖p‖ + C ∧ g y = p := by
  obtain ⟨w, hwm, hwt⟩ := mem_closure_iff_seq_limit.1 hpc
  have hsurj : ∀ n, ∃ v, v ∈ H ∧ Ψ.2.1 v = w n := fun n => by
    have h := hwm n
    rw [← hΨD.image_eq] at h
    obtain ⟨v, hv, hve⟩ := h
    exact ⟨v, hv, hve⟩
  choose v hvH hve using hsurj
  obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto w hwt).exists_norm_le
  have hvb : ∀ n, v n ∈ closedBall (0 : ℂ) (R + C) := by
    intro n
    have h1 := hgb (v n) (QuantumZipper.H_subset_Hbar (hvH n))
    rw [hgH (hvH n), hve n] at h1
    have h2 := hR (w n) ⟨n, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    have h3 : ‖v n‖ ≤ ‖w n‖ + ‖w n - v n‖ := by
      calc ‖v n‖ = ‖w n - (w n - v n)‖ := by ring_nf
        _ ≤ ‖w n‖ + ‖w n - v n‖ := norm_sub_le _ _
    linarith
  obtain ⟨y₀, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded isBounded_closedBall hvb
  have hHc : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
  have hy₀ : y₀ ∈ Hbar := hHc.mem_of_tendsto hlim (Eventually.of_forall fun n =>
    QuantumZipper.H_subset_Hbar (hvH (φ n)))
  have hlim' : Tendsto (fun n => v (φ n)) atTop (𝓝[Hbar] y₀) := tendsto_nhdsWithin_iff.2
    ⟨hlim, Eventually.of_forall fun n => QuantumZipper.H_subset_Hbar (hvH (φ n))⟩
  have h1 := ((hgc y₀ hy₀).tendsto).comp hlim'
  have h2 : Tendsto (fun n => g (v (φ n))) atTop (𝓝 p) :=
    (hwt.comp hφ.tendsto_atTop).congr fun n => by
      show w (φ n) = g (v (φ n))
      rw [hgH (hvH (φ n)), hve]
  have hgy : g y₀ = p := tendsto_nhds_unique h1 h2
  have hnH : y₀ ∉ H := fun hH => by
    have := hΨD.inv_mem hH
    rw [← hgH hH, hgy] at this
    exact this.2 hp
  have him : y₀.im = 0 := le_antisymm (not_lt.1 hnH) hy₀
  have hy₀eq : ((y₀.re : ℝ) : ℂ) = y₀ := Complex.ext (by simp) (by simp [him])
  refine ⟨y₀.re, ?_, ?_, by rw [hy₀eq, hgy]⟩
  · by_contra hlt
    push Not at hlt
    have h3 := hpos y₀.re hlt
    rw [hy₀eq, hgy] at h3
    have : (0 : ℝ) < p.im := hDH hp
    linarith
  · have h4 := hgb y₀ hy₀
    rw [hgy] at h4
    have h5 : ‖y₀‖ ≤ ‖p‖ + C := by
      have : ‖y₀‖ ≤ ‖p‖ + ‖p - y₀‖ := by
        calc ‖y₀‖ = ‖p - (p - y₀)‖ := by ring_nf
          _ ≤ ‖p‖ + ‖p - y₀‖ := norm_sub_le _ _
      linarith
    rw [← hy₀eq, Complex.norm_real, Real.norm_eq_abs] at h5
    exact h5


include hΨD hg hgb hgc hgH hDH in
/-- **The retained hull is the filling of the boundary arc `g([−K, 0])`.** -/
theorem fillH_arc_eq (hDb : IsBounded D) (hpos : ∀ y : ℝ, 0 < y → (g y).im = 0) {K : ℝ}
    (hK : ∀ z ∈ D, ‖z‖ + C ≤ K) : fillH ((fun t : ℝ => g t) '' Icc (-K) 0) = D := by
  set X := (fun t : ℝ => g t) '' Icc (-K) 0 with hXdef
  have hmaps : MapsTo (fun t : ℝ => (t : ℂ)) (Icc (-K) 0) Hbar := fun t _ =>
    show (0 : ℝ) ≤ (t : ℂ).im by simp
  have hXc : IsCompact X :=
    isCompact_Icc.image_of_continuousOn (hgc.comp Complex.continuous_ofReal.continuousOn hmaps)
  have hXcl : closure X = X := hXc.isClosed.closure_eq
  have hXD : ∀ w ∈ X, w ∈ H → w ∈ D := by
    rintro _ ⟨t, -, rfl⟩ hH
    exact mem_of_real hΨD hg hH
  have hfr : ∀ p ∈ D, p ∈ closure (H \ D) → p ∈ X := by
    intro p hp hpc
    obtain ⟨y, hy0, hyK, hgy⟩ := exists_real_of_frontier hΨD hgb hgc hgH hDH hpos hp hpc
    have := hK p hp
    exact ⟨y, ⟨by linarith [neg_abs_le y], hy0⟩, hgy⟩
  have hunb : ¬ IsBounded (H \ D) := fun hb => not_isBounded_H ((hb.union hDb).subset fun z hz => by
    by_cases hzD : z ∈ D
    · exact Or.inr hzD
    · exact Or.inl ⟨hz, hzD⟩)
  have hint : ∀ p ∈ H \ closure X, p ∈ D → p ∈ interior D := by
    intro p hp hpD
    by_contra hpI
    have h1 : p ∈ closure Dᶜ := by rw [closure_compl]; exact hpI
    have h2 : p ∈ closure (Dᶜ ∩ H) := QuantumZipper.isOpen_H.closure_inter ⟨h1, hp.1⟩
    have h3 : Dᶜ ∩ H = H \ D := by ext z; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [h3] at h2
    exact hp.2 (subset_closure (hfr p hpD h2))
  ext z
  constructor
  · rintro ⟨hzH, hz | hz⟩
    · rw [hXcl] at hz
      exact hXD z hz hzH
    · by_contra hzD
      have hsub : H \ D ⊆ connectedComponentIn (H \ closure X) z :=
        hΨD.isPreconnected.subset_connectedComponentIn ⟨hzH, hzD⟩ fun w hw =>
          ⟨hw.1, fun hwX => hw.2 (hXD w (by rwa [hXcl] at hwX) hw.1)⟩
      exact hunb (hz.subset hsub)
  · intro hzD
    have hzH := hDH hzD
    refine ⟨hzH, ?_⟩
    by_cases hzX : z ∈ closure X
    · exact Or.inl hzX
    · right
      set Kz := connectedComponentIn (H \ closure X) z with hKzdef
      have hKz : Kz ⊆ interior D ∪ (H \ D) := fun p hp => by
        have hp' := connectedComponentIn_subset _ _ hp
        by_cases hpD : p ∈ D
        · exact Or.inl (hint p hp' hpD)
        · exact Or.inr ⟨hp'.1, hpD⟩
      have hpre : IsPreconnected Kz := isPreconnected_connectedComponentIn
      have hzK : z ∈ Kz := mem_connectedComponentIn ⟨hzH, hzX⟩
      have hzI := hint z ⟨hzH, hzX⟩ hzD
      have hdisj : ∀ p ∈ Kz, p ∉ H \ D := by
        intro p hp hpU
        obtain ⟨q, -, hq1, hq2⟩ := hpre _ _ isOpen_interior hΨD.isOpen hKz ⟨z, hzK, hzI⟩ ⟨p, hp, hpU⟩
        exact hq2.2 (interior_subset hq1)
      refine hDb.subset fun p hp => ?_
      rcases hKz hp with h | h
      · exact interior_subset h
      · exact absurd h (hdisj p hp)

end Arc

end InteractingSLE.Theorem14.SB.Sx
