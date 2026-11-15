/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G7ClockGeom
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane
import InteractingSLE.Foundations.Topology.PathComplement

/-!
# Theorem 1.5's leaf 3: an inactive fixed tip means the other prefix is enclosed

Packet PROVE-T15-ORDDET5. PROVE-T15-ORDDET4 reduced the ordinariness of a later line of a continuation to two
conditions; the second, "the fixed tip stays active", fails when the continuation closes a real pocket around the
other prefix (G7, p. 498: "Any portion of the fixed retained hull it surrounds is swallowed with that same pocket").
This file proves the planar fact behind that sentence, in a chart of the stop line.

**`subset_fillH_of_inactive`** (deterministic). Let `ψ` be a chart (`Supp7.IsDomChart`) of `ℍ \ fill(K)`, `K ⊆ A₁ ∪ A₂`,
`A₁ ⊆ K`, and let `G` be a compact chart set (the chart range of the continuation up to the line) whose hull
`fill(G)` is mapped by `ψ` into the later active domain `ℍ \ fill(A₁ ∪ A₂)` off it, with `ψ(G) ⊆ A₂ \ A₁` (the new piece
makes no contact with `A₁`). Suppose the chart preimage of the exposed part of `A₁` lies in an interval `[L, R]`
containing a chart point `τ` of the fixed tip, with `ψ([L, R]) ⊆ A₁`. If the fixed tip `ψ(τ)` is not adherent to the
later active domain, then `A₁ ∩ ℍ ⊆ fill(A₂)`: the whole fixed prefix is enclosed by the moving path.

Proof. (1) `τ` is adherent to `fill(G)` (otherwise `ψ(τ + is) → ψ(τ)` from the later active domain). (2) A
`δ`-neighbourhood `N` of `[L, R]` in `ℍ` misses `G` (compactness) and is connected, and it meets `fill(G)`, so it lies
in one bounded component `C₀` of `ℍ \ G`. (3) A point `p ∈ A₁ \ A₂` adherent to the later active domain `D'` is the
`ψ`-image of a real chart limit `w₀` of chart points `φ(z)`, `z ∈ D'` (bounded displacement, Bolzano–Weierstrass);
`w₀ ∈ [L, R]`, so some `φ(z) ∈ N ⊆ C₀`; the `φ`-image of the (unbounded) component of `z` in `ℍ \ (A₁ ∪ A₂)` misses `G`,
so it lies in `C₀` and is bounded — a contradiction. (4) Hence `D'` is relatively clopen in the connected set
`ℍ \ fill(A₂)`, so the two are equal, and `A₁ ∩ ℍ` misses `ℍ \ fill(A₂)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE.RLC.OrdGap

open Supp7

/-- **An inactive fixed tip means the fixed prefix is enclosed** (deterministic; see the module docstring). -/
theorem subset_fillH_of_inactive {K A₁ A₂ G : Set ℂ} {φ ψ : ℂ → ℂ} (hD : IsDomChart K φ ψ)
    (hA₁ : IsCompact A₁) (hA₂ : IsCompact A₂) (hG : IsCompact G) (hA₁K : A₁ ⊆ K) (hKA : K ⊆ A₁ ∪ A₂)
    (hGψ : ∀ z ∈ G, ψ z ∈ A₂ ∧ ψ z ∉ A₁)
    (hD' : ψ '' (H \ fillH G) ⊆ H \ fillH (A₁ ∪ A₂)) {L R τ : ℝ} (hLτ : L ≤ τ) (hτR : τ ≤ R)
    (hS : ∀ w ∈ Icc L R, ψ w ∈ A₁) (hZ : ∀ w : ℝ, ψ w ∈ A₁ → ψ w ∉ A₂ → w ∈ Icc L R)
    (hin : ψ τ ∉ closure (H \ fillH (A₁ ∪ A₂))) : A₁ ∩ H ⊆ fillH A₂ := by
  classical
  set X := A₁ ∪ A₂ with hX
  have hXc : IsCompact X := hA₁.union hA₂
  set Sc : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc L R with hSc
  have hScc : IsCompact Sc := isCompact_Icc.image Complex.continuous_ofReal
  have hτS : ((τ : ℝ) : ℂ) ∈ Sc := ⟨τ, ⟨hLτ, hτR⟩, rfl⟩
  -- the chart interval misses `G`
  have hSG : Sc ⊆ Gᶜ := by
    rintro _ ⟨w, hw, rfl⟩ hwG
    exact (hGψ _ hwG).2 (hS w hw)
  obtain ⟨δ, hδ, hδS⟩ := hScc.exists_thickening_subset_open hG.isClosed.isOpen_compl hSG
  set N : Set ℂ := H ∩ thickening δ Sc with hN
  have hNc : IsPreconnected N := by
    have h1 : Convex ℝ H := convex_halfSpace_gt Complex.imLm.isLinear 0
    have h2 : Convex ℝ Sc := (convex_Icc L R).linear_image Complex.ofRealCLM.toLinearMap
    exact (h1.inter (h2.thickening δ)).isPreconnected
  have hNG : N ⊆ H \ closure G := fun z hz => ⟨hz.1, by rw [hG.isClosed.closure_eq]; exact hδS hz.2⟩
  -- (1) the fixed tip's chart point is adherent to the hull of `G`
  have hτK : ((τ : ℝ) : ℂ) ∈ closure (fillH G) := by
    by_contra hτ
    obtain ⟨ε, hε, hεK⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hτ
    apply hin
    have hmem : ∀ s : ℝ, 0 < s → s < ε → ψ ((τ : ℂ) + (s : ℂ) * I) ∈ H \ fillH X := by
      intro s hs hsε
      have hsH : (τ : ℂ) + (s : ℂ) * I ∈ H := by
        show 0 < ((τ : ℂ) + (s : ℂ) * I).im
        simpa using hs
      refine hD' ⟨_, ⟨hsH, fun hK => hεK ?_ (subset_closure hK)⟩, rfl⟩
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hs]
      exact hsε
    have hc : Tendsto (fun s : ℝ => (τ : ℂ) + (s : ℂ) * I) (𝓝[>] 0) (𝓝[Hbar] (τ : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Continuous fun s : ℝ => (τ : ℂ) + (s : ℂ) * I := by fun_prop
        have h0 := this.tendsto 0
        simp only [ofReal_zero, zero_mul, add_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        show (0 : ℝ) ≤ ((τ : ℂ) + (s : ℂ) * I).im
        simpa using (le_of_lt (show (0 : ℝ) < s from hs))
    have hτH : ((τ : ℝ) : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((τ : ℝ) : ℂ).im by simp
    have hlim := (hD.continuousOn_inv _ hτH).tendsto.comp hc
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hε] with s hs
    exact hmem s hs.1 hs.2
  -- (2) the neighbourhood `N` lies in a bounded component of `ℍ \ G`
  obtain ⟨k, hkK, hkτ⟩ := Metric.mem_closure_iff.1 hτK δ hδ
  have hkN : k ∈ N := ⟨fillH_subset_H _ hkK, Metric.mem_thickening_iff.2 ⟨_, hτS, by rw [dist_comm]; exact hkτ⟩⟩
  have hC₀b : Bornology.IsBounded (connectedComponentIn (H \ closure G) k) := by
    rcases hkK.2 with h | h
    · exact absurd h (hNG hkN).2
    · exact h
  have hNC₀ : N ⊆ connectedComponentIn (H \ closure G) k := hNc.subset_connectedComponentIn hkN hNG
  -- (3) a point of `A₁` adherent to the later active domain is on `A₂`
  have hD'D : H \ fillH X ⊆ H \ fillH K := fun y hy => ⟨hy.1, fun h => hy.2 (fillH_mono hKA h)⟩
  obtain ⟨M, hM⟩ := hD.bdd
  have hkey : ∀ p ∈ A₁, p ∈ closure (H \ fillH X) → p ∈ A₂ := by
    intro p hp hpc
    by_contra hpA₂
    obtain ⟨z, hzD', hzlim⟩ := mem_closure_iff_seq_limit.1 hpc
    set w : ℕ → ℂ := fun n => φ (z n) with hw
    have hwH : ∀ n, w n ∈ H := fun n => hD.mapsTo_fwd (hD'D (hzD' n))
    have hψw : ∀ n, ψ (w n) = z n := fun n => hD.inv_fwd (hD'D (hzD' n))
    obtain ⟨Rz, hRz⟩ := (Metric.isBounded_range_of_tendsto z hzlim).subset_closedBall 0
    have hwb : Bornology.IsBounded (range w) := by
      refine (isBounded_closedBall (x := (0 : ℂ)) (r := Rz + |M|)).subset ?_
      rintro _ ⟨n, rfl⟩
      rw [mem_closedBall, dist_zero_right]
      have h1 := hM (w n) (QuantumZipper.H_subset_Hbar (hwH n))
      have h2 := hRz (mem_range_self n)
      rw [mem_closedBall, dist_zero_right] at h2
      rw [hψw n] at h1
      have h3 := norm_sub_norm_le (w n) (z n)
      rw [norm_sub_rev] at h1
      linarith [le_abs_self M]
    obtain ⟨w₀, -, σ, hσ, hσlim⟩ := tendsto_subseq_of_bounded hwb (fun n => mem_range_self n)
    have hw₀H : w₀ ∈ Hbar :=
      QuantumZipper.isClosed_Hbar.mem_of_tendsto hσlim
        (Eventually.of_forall fun n => QuantumZipper.H_subset_Hbar (hwH (σ n)))
    have hψw₀ : ψ w₀ = p := by
      have h1 : Tendsto (fun n => ψ (w (σ n))) atTop (𝓝 (ψ w₀)) :=
        (hD.continuousOn_inv _ hw₀H).tendsto.comp (tendsto_nhdsWithin_iff.2
          ⟨hσlim, Eventually.of_forall fun n => QuantumZipper.H_subset_Hbar (hwH (σ n))⟩)
      have h2 : Tendsto (fun n => ψ (w (σ n))) atTop (𝓝 p) := by
        simp only [hψw]
        exact hzlim.comp hσ.tendsto_atTop
      exact tendsto_nhds_unique h1 h2
    -- the chart limit is a real point of the chart interval
    have hw₀notH : w₀ ∉ H := by
      intro h
      have hD₀ := hD.bijOn_inv.mapsTo h
      rw [hψw₀] at hD₀
      exact hD₀.2 (mem_fillH_of_mem_closure hD₀.1 (subset_closure (hA₁K hp)))
    have hw₀im : w₀.im = 0 := le_antisymm (not_lt.1 hw₀notH) hw₀H
    have hw₀re : w₀ = ((w₀.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hw₀im])
    have hw₀S : w₀.re ∈ Icc L R := hZ _ (by rw [← hw₀re, hψw₀]; exact hp) (by rw [← hw₀re, hψw₀]; exact hpA₂)
    have hev : ∀ᶠ n in atTop, w (σ n) ∈ N := by
      filter_upwards [hσlim.eventually (Metric.ball_mem_nhds w₀ hδ)] with n hn
      exact ⟨hwH (σ n), Metric.mem_thickening_iff.2 ⟨w₀, by rw [hw₀re]; exact ⟨_, hw₀S, rfl⟩, hn⟩⟩
    obtain ⟨n, hn⟩ := hev.exists
    -- the component of `z (σ n)` in `ℍ \ (A₁ ∪ A₂)`
    set y := z (σ n) with hy
    have hyD' : y ∈ H \ fillH X := hzD' (σ n)
    have hyX : y ∉ X := fun h => hyD'.2 (mem_fillH_of_mem_closure hyD'.1 (subset_closure h))
    have hCU : ¬ Bornology.IsBounded (connectedComponentIn (H \ X) y) := by
      intro h
      refine hyD'.2 ⟨hyD'.1, Or.inr ?_⟩
      rw [hXc.isClosed.closure_eq]
      exact h
    have hCD' : connectedComponentIn (H \ X) y ⊆ H \ fillH X := by
      intro c hc
      have hcX : c ∈ H \ X := connectedComponentIn_subset _ _ hc
      refine ⟨hcX.1, ?_⟩
      rintro ⟨-, hcl | hcb⟩
      · rw [hXc.isClosed.closure_eq] at hcl
        exact hcX.2 hcl
      · rw [hXc.isClosed.closure_eq, ← connectedComponentIn_eq hc] at hcb
        exact hCU hcb
    have hφC : φ '' connectedComponentIn (H \ X) y ⊆ H \ closure G := by
      rintro _ ⟨c, hc, rfl⟩
      have hcD := hD'D (hCD' hc)
      refine ⟨hD.mapsTo_fwd hcD, fun hcG => ?_⟩
      rw [hG.isClosed.closure_eq] at hcG
      have h1 := (hGψ _ hcG).1
      rw [hD.inv_fwd hcD] at h1
      exact (connectedComponentIn_subset _ _ hc).2 (Or.inr h1)
    have hpcφ : IsPreconnected (φ '' connectedComponentIn (H \ X) y) :=
      isPreconnected_connectedComponentIn.image φ (hD.continuousOn_fwd.mono fun c hc => hD'D (hCD' hc))
    have hyC : y ∈ connectedComponentIn (H \ X) y := mem_connectedComponentIn ⟨hyD'.1, hyX⟩
    have hwnC : w (σ n) ∈ φ '' connectedComponentIn (H \ X) y := ⟨y, hyC, rfl⟩
    have hsub : φ '' connectedComponentIn (H \ X) y ⊆ connectedComponentIn (H \ closure G) k := by
      have h1 := hpcφ.subset_connectedComponentIn hwnC hφC
      rwa [← connectedComponentIn_eq (hNC₀ hn)] at h1
    apply hCU
    obtain ⟨Rb, hRb⟩ := hC₀b.subset_closedBall 0
    refine (isBounded_closedBall (x := (0 : ℂ)) (r := Rb + |M|)).subset fun c hc => ?_
    have hcD := hD'D (hCD' hc)
    have h1 := hRb (hsub ⟨c, hc, rfl⟩)
    have h2 := hM (φ c) (QuantumZipper.H_subset_Hbar (hD.mapsTo_fwd hcD))
    rw [hD.inv_fwd hcD] at h2
    rw [mem_closedBall, dist_zero_right] at h1 ⊢
    have h3 := norm_sub_norm_le c (φ c)
    linarith [le_abs_self M]
  -- (4) the later active domain is the unbounded component of `ℍ \ A₂`
  rintro z ⟨hzA₁, hzH⟩
  by_contra hzF
  obtain ⟨R₂, hR₂, hA₂R, hU₂eq⟩ := HalfPlaneSep.exists_H_diff_fillH_eq hA₂.isClosed hA₂.isBounded
  obtain ⟨RX, hRX, hXR, hD'eq⟩ := HalfPlaneSep.exists_H_diff_fillH_eq hXc.isClosed hXc.isBounded
  have hU₂pc : IsPreconnected (H \ fillH A₂) := by
    rw [hU₂eq]; exact isPreconnected_connectedComponentIn
  have hD'o : IsOpen (H \ fillH X) := isOpen_H_diff_fillH hXc.isBounded
  have hne : ((H \ fillH A₂) ∩ (H \ fillH X)).Nonempty := by
    set z₀ : ℂ := ((max R₂ RX + 1 : ℝ) : ℂ) * I with hz₀
    have hz₀H : z₀ ∈ H := by
      show 0 < (((max R₂ RX + 1 : ℝ) : ℂ) * I).im
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      have := le_max_left R₂ RX
      linarith
    have hz₀n : ‖z₀‖ = max R₂ RX + 1 := by
      rw [hz₀, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by have := le_max_left R₂ RX; linarith)]
    refine ⟨z₀, ?_, ?_⟩
    · rw [hU₂eq]
      exact mem_connectedComponentIn_of_le_norm hR₂ hA₂R hz₀H (by rw [hz₀n]; linarith [le_max_left R₂ RX])
    · rw [hD'eq]
      exact mem_connectedComponentIn_of_le_norm hRX hXR hz₀H (by rw [hz₀n]; linarith [le_max_right R₂ RX])
  have hcl : closure (H \ fillH X) ∩ (H \ fillH A₂) ⊆ H \ fillH X := by
    rintro y ⟨hyc, hyH, hyF⟩
    have hyA₂ : y ∉ A₂ := fun h => hyF (mem_fillH_of_mem_closure hyH (subset_closure h))
    have hyA₁ : y ∉ A₁ := fun h => hyA₂ (hkey y h hyc)
    have hyX : y ∉ X := by
      rintro (h | h)
      exacts [hyA₁ h, hyA₂ h]
    refine ⟨hyH, ?_⟩
    rintro ⟨-, hyX' | hyb⟩
    · rw [hXc.isClosed.closure_eq] at hyX'
      exact hyX hyX'
    · rw [hXc.isClosed.closure_eq] at hyb
      have hO : IsOpen (connectedComponentIn (H \ X) y) :=
        (QuantumZipper.isOpen_H.sdiff hXc.isClosed).connectedComponentIn
      obtain ⟨y', hy'C, hy'D'⟩ := mem_closure_iff.1 hyc _ hO (mem_connectedComponentIn ⟨hyH, hyX⟩)
      refine hy'D'.2 ⟨hy'D'.1, Or.inr ?_⟩
      rw [hXc.isClosed.closure_eq, ← connectedComponentIn_eq hy'C]
      exact hyb
  have hsub := hU₂pc.subset_of_closure_inter_subset hD'o hne hcl
  exact (hsub ⟨hzH, hzF⟩).2 (mem_fillH_of_mem_closure hzH (subset_closure (Or.inl hzA₁)))

end InteractingSLE.RLC.OrdGap
