/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux39InfArm
import InteractingSLE.Spec.Sec6.Aux36FacePocket

/-!
# The central face at infinity from the physical pocket; Propositions 1.5–1.6 there

Ruling R41's note (`source/external/AstraIG1/ig1_ztip_elimination.txt` §1.1 and Lemma 1.3), the case
in which the pocket junction `x_C` is the original target (`∞` in the physical half-plane). The
pocket `C` is open with `∂C = α₁([c₁, ∞)) ∪ α₂([c₂, ∞))`, two proper simple paths; at the chart time
`r` the parts `α_i([c_i, u_i])` are visited (not in `D_r`) and the prefixes `α_i((u_i, ∞))` lie in
`D_r` and are disjoint. Far real points are outside `C̄` (the flow lines meet `ℝ` only at their
ends).

In the `g_r` chart the prefixes lift to proper arcs from gates `q_i` to `∞`; after the real Möbius
map `ψ_p` (`p` left of everything) they become the arcs `b_i` of `IsArcPairInf` (`Aux39InfArm`).

## Main results

* `exists_norm_trMap_zero_sub_le_Hbar`, `exists_trMap_ofReal_notMem_closure`: `f̄_r` on `ℍ̄` moves
  points by a bounded amount, and far real points go to far real points;
* `trMap_psiMapInv_mem_iff`: **the face identification at infinity** (distinct gates): for
  `ζ ∈ ℍ`, `f̄_r(ψ_p⁻¹(ζ)) ∈ C ↔ ζ ∈ innerSide (B₁ ∪ B₂ ∪ [x₁, x₂])`;
* `ownFuture_gap_eq_of_pocket_inf`: **Propositions 1.5 (old start) and 1.6 at infinity**
  (distinct gates; `q₁ ≠ q₂`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec6

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- `f̄_r` moves points of `ℍ̄` by a bounded amount. -/
theorem exists_norm_trMap_zero_sub_le_Hbar (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {r : ℝ} (hr : 0 ≤ r) : ∃ K, ∀ w ∈ Hbar, ‖trMap W 0 r w - w‖ ≤ K := by
  obtain ⟨K, hK⟩ := exists_norm_trMap_zero_sub_le hW hW0 hr
  refine ⟨K, fun w hw => ?_⟩
  have hc : ContinuousWithinAt (fun z => ‖trMap W 0 r z - z‖) H w :=
    (((YuanSimpleApprox.trMap_continuousOn hη hW hW0 le_rfl hr) w hw).sub
      continuousWithinAt_id).norm.mono QuantumZipper.H_subset_Hbar
  have hcl : w ∈ closure H := by rw [closure_H]; exact hw
  have : (𝓝[H] w).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  exact le_of_tendsto hc (eventually_nhdsWithin_of_forall fun z hz => hK z hz)

/-- Far real points are mapped by `f̄_r` to far real points; in particular outside `C̄` when far
real points are. -/
theorem exists_trMap_ofReal_notMem_closure (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {r : ℝ} (hr : 0 ≤ r) {C : Set ℂ}
    (hCR : ∃ M, ∀ y : ℝ, M ≤ |y| → (y : ℂ) ∉ closure C) :
    ∃ M', ∀ y : ℝ, M' ≤ |y| → trMap W 0 r y ∉ closure C := by
  obtain ⟨M, hM⟩ := hCR
  obtain ⟨K, hK⟩ := exists_norm_trMap_zero_sub_le_Hbar hη hW hW0 hr
  have hRc : IsCompact (η '' Icc 0 r) :=
    isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun t ht => ht.1)
  obtain ⟨ρ, hρ, hρR⟩ := exists_closure_subset_ball hRc.isBounded
  have hKρ : fwdHull W r ⊆ ball 0 ρ := by rw [hη.2.2 r hr]; exact fillH_subset_ball hρ hρR
  obtain ⟨-, -, -, hFR⟩ := YuanSimpleApprox.trMap_fiber_hyps hη hW hW0 le_rfl hr
  refine ⟨|M| + |K| + ρ + 1, fun y hy => ?_⟩
  set w := trMap W 0 r y with hw
  have hwH : w ∈ Hbar := YuanSimpleApprox.trMap_mapsTo_Hbar hη hW hW0 le_rfl hr (ofReal_mem_Hbar y)
  have hwy := hK y (ofReal_mem_Hbar y)
  have hnorm : |y| - K ≤ ‖w‖ := by
    have := norm_sub_norm_le (y : ℂ) w
    rw [norm_real, Real.norm_eq_abs, norm_sub_rev] at this
    linarith
  have hwim : w.im = 0 := by
    by_contra hne
    have hwH' : w ∈ H := lt_of_le_of_ne hwH (Ne.symm hne)
    have hnot := hFR y (by simp)
    rw [trMap_zero_image_H hW hW0 hr] at hnot
    have hwK : w ∈ fwdHull W r := by
      by_contra h'; exact hnot ⟨hwH', h'⟩
    have := mem_ball_zero_iff.1 (hKρ hwK)
    linarith [le_abs_self K, abs_nonneg M]
  have hwr : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hwim])
  rw [hwr]
  refine hM _ ?_
  have h1 : ‖w‖ = |w.re| := by rw [hwr, norm_real, Real.norm_eq_abs]; simp
  linarith [le_abs_self K, le_abs_self M]

/-- **The face identification at infinity**, generic form. `b₁, b₂` are arcs from the real points
`x₁ ≤ x₂ < 0` to `0`, open in `ℍ`, whose open parts are the `ψ_p`-images of the lifted unvisited
prefixes; `Ξᵢ = Bᵢ ∪ [xᵢ, 0]`. Let `Γ ⊆ ℍ̄` be a Jordan curve containing the open arcs such that
every
point off `B₁ ∪ B₂ ∪ [x₁, 0]` is outside `Ξ₁`, inside `Γ` or inside `Ξ₂`, with `B₂°` inside `Ξ₁` and
`B₁°` outside `Ξ₂`. Then `f̄_r(ψ_p⁻¹(ζ)) ∈ C ↔ ζ ∈ innerSide Γ` for `ζ ∈ ℍ`. -/
theorem trMap_psiMapInv_mem_iff_of_faces (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {r : ℝ} (hr : 0 ≤ r) {C : Set ℂ} (hC : IsOpen C)
    (hCR : ∃ M, ∀ y : ℝ, M ≤ |y| → (y : ℂ) ∉ closure C) {α₁ α₂ : ℝ → ℂ} {c₁ u₁ c₂ u₂ : ℝ}
    (hcu₁ : c₁ ≤ u₁) (hcu₂ : c₂ ≤ u₂) (hfrC : frontier C = α₁ '' Ici c₁ ∪ α₂ '' Ici c₂)
    (hα₁D : ∀ v ∈ Ioi u₁, α₁ v ∈ H \ fwdHull W r) (hα₂D : ∀ v ∈ Ioi u₂, α₂ v ∈ H \ fwdHull W r)
    (hα₁K : ∀ v ∈ Icc c₁ u₁, α₁ v ∉ H \ fwdHull W r)
    (hα₂K : ∀ v ∈ Icc c₂ u₂, α₂ v ∉ H \ fwdHull W r) {p q₂ x₁ x₂ : ℝ} {b₁ b₂ : ℝ → ℂ}
    (hx₁0 : x₁ < 0) (hx₂0 : x₂ < 0)
    (hb₁c : ContinuousOn b₁ (Icc 0 1)) (hb₂c : ContinuousOn b₂ (Icc 0 1))
    (hb₁i : InjOn b₁ (Icc 0 1)) (hb₂i : InjOn b₂ (Icc 0 1)) (hb₁0 : b₁ 0 = x₁) (hb₂0 : b₂ 0 = x₂)
    (hb₁1 : b₁ 1 = 0) (hb₂1 : b₂ 1 = 0) (hb₁H : ∀ t ∈ Ioo (0 : ℝ) 1, b₁ t ∈ H)
    (hb₂H : ∀ t ∈ Ioo (0 : ℝ) 1, b₂ t ∈ H) {Γ : Set ℂ}
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    (hAΓ : b₁ '' Ioo 0 1 ∪ b₂ '' Ioo 0 1 ⊆ Γ)
    (hcover : ∀ z, z ∉ b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0 →
      z ∈ outerSide (b₁ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0) ∨ z ∈ innerSide Γ ∨
        z ∈ innerSide (b₂ '' Icc 0 1 ∪ ofReal '' Icc x₂ 0))
    (hside₂ : b₂ '' Ioo 0 1 ⊆ innerSide (b₁ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0))
    (hside₁ : b₁ '' Ioo 0 1 ⊆ outerSide (b₂ '' Icc 0 1 ∪ ofReal '' Icc x₂ 0))
    (hpq₂ : p < q₂) (hx₂ : x₂ = -(q₂ - p)⁻¹)
    (hb₁img : b₁ '' Ioo 0 1 = psiMap p '' (fwdMap W r '' (α₁ '' Ioi u₁)))
    (hb₂img : b₂ '' Ioo 0 1 = psiMap p '' (fwdMap W r '' (α₂ '' Ioi u₂))) {ζ : ℂ} (hζ : ζ ∈ H) :
    trMap W 0 r (psiMapInv p ζ) ∈ C ↔ ζ ∈ innerSide Γ := by
  set G : ℂ → ℂ := fun z => trMap W 0 r (psiMapInv p z) with hG
  obtain ⟨hΞ₁, hΞ₁H⟩ := isJordanCurve_sideInf hx₁0 hb₁c hb₁i hb₁0 hb₁1 hb₁H
  obtain ⟨hΞ₂, hΞ₂H⟩ := isJordanCurve_sideInf hx₂0 hb₂c hb₂i hb₂0 hb₂1 hb₂H
  obtain ⟨-, -, -, -, -, hO₁o, -, -, -⟩ := jordan_sides hΞ₁ hΞ₁H
  obtain ⟨-, -, -, -, -, -, -, hI₂p, -⟩ := jordan_sides hΞ₂ hΞ₂H
  obtain ⟨-, -, -, -, -, -, -, hIp, -⟩ := jordan_sides hΓ hΓH
  have hTc := YuanSimpleApprox.trMap_continuousOn hη hW hW0 le_rfl hr
  have hGc : ContinuousOn G H := by
    refine hTc.comp (continuousOn_psiMapInv.mono fun z hz h0 => ?_) fun z hz =>
      QuantumZipper.H_subset_Hbar (psiMapInv_mem_H hz)
    rw [mem_singleton_iff] at h0; rw [h0] at hz
    have h1 : (0 : ℝ) < (0 : ℂ).im := hz
    simp at h1
  have hGcw : ∀ w ∈ Hbar, w ≠ 0 → ContinuousWithinAt G Hbar w := fun w hw hw0 =>
    (hTc _ (psiMapInv_mem_Hbar hw)).comp
      (continuousOn_psiMapInv.continuousAt (isOpen_compl_singleton.mem_nhds hw0)).continuousWithinAt
      fun z hz => psiMapInv_mem_Hbar hz
  -- the open arcs are exactly the preimage of `∂C` in `ℍ`
  have hfr1 : ∀ z ∈ H, G z ∈ frontier C → z ∈ b₁ '' Ioo 0 1 ∪ b₂ '' Ioo 0 1 := by
    intro z hz hzC
    have hwH := psiMapInv_mem_H (p := p) hz
    have hD := trMap_zero_mem_domain hW hW0 hr hwH
    have hzeq : z = psiMap p (fwdMap W r (G z)) := by
      rw [hG]; simp only
      rw [fwdMap_trMap_zero hW hW0 hr hwH, psiMap_psiMapInv]
    rw [hfrC] at hzC
    rcases hzC with ⟨v, hv, hvz⟩ | ⟨v, hv, hvz⟩
    · have hvu : u₁ < v := by
        by_contra h'; push Not at h'; exact hα₁K v ⟨hv, h'⟩ (hvz ▸ hD)
      left; rw [hb₁img, hzeq, ← hvz]; exact ⟨_, ⟨_, ⟨v, hvu, rfl⟩, rfl⟩, rfl⟩
    · have hvu : u₂ < v := by
        by_contra h'; push Not at h'; exact hα₂K v ⟨hv, h'⟩ (hvz ▸ hD)
      right; rw [hb₂img, hzeq, ← hvz]; exact ⟨_, ⟨_, ⟨v, hvu, rfl⟩, rfl⟩, rfl⟩
  have hfr2 : ∀ z ∈ b₁ '' Ioo 0 1 ∪ b₂ '' Ioo 0 1, G z ∉ C := by
    have hfrC' : frontier C ∩ C = ∅ := by
      rw [hC.frontier_eq]; exact Set.sdiff_inter_self
    rintro z (hz | hz) hzC
    · rw [hb₁img] at hz
      obtain ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩ := hz
      have : G (psiMap p (fwdMap W r (α₁ v))) = α₁ v := by
        simp only [hG, psiMapInv_psiMap, trMap_zero_fwdMap hW hW0 hr (hα₁D v hv)]
      rw [this] at hzC
      have hfr : α₁ v ∈ frontier C := by
        rw [hfrC]; exact Or.inl ⟨v, le_of_lt (lt_of_le_of_lt hcu₁ hv), rfl⟩
      exact (Set.eq_empty_iff_forall_notMem.1 hfrC') _ ⟨hfr, hzC⟩
    · rw [hb₂img] at hz
      obtain ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩ := hz
      have : G (psiMap p (fwdMap W r (α₂ v))) = α₂ v := by
        simp only [hG, psiMapInv_psiMap, trMap_zero_fwdMap hW hW0 hr (hα₂D v hv)]
      rw [this] at hzC
      have hfr : α₂ v ∈ frontier C := by
        rw [hfrC]; exact Or.inr ⟨v, le_of_lt (lt_of_le_of_lt hcu₂ hv), rfl⟩
      exact (Set.eq_empty_iff_forall_notMem.1 hfrC') _ ⟨hfr, hzC⟩
  -- far real points are not mapped near `C̄`
  obtain ⟨M', hM'⟩ := exists_trMap_ofReal_notMem_closure hη hW hW0 hr hCR
  have hnear : ∀ y : ℝ, M' ≤ |y| → y ≠ p →
      ∃ ε > 0, ∀ z ∈ Hbar, dist z (psiMap p y) < ε → G z ∉ closure C := by
    intro y hy hyp
    have h0 : psiMap p y ≠ 0 := fun h0 => hyp (by
      have := psiMap_eq_zero_iff.1 h0; exact_mod_cast this)
    have hGy : G (psiMap p y) = trMap W 0 r y := by simp only [hG, psiMapInv_psiMap]
    have hc := hGcw _ (by rw [psiMap_ofReal]; exact ofReal_mem_Hbar _) h0
    obtain ⟨ε₀, hε₀, hε₀s⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _
      (show G (psiMap p y) ∈ (closure C)ᶜ by rw [hGy]; exact hM' y hy)
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 hc ε₀ hε₀
    exact ⟨δ, hδ, fun z hz hzd => hε₀s (hδc hz hzd)⟩
  -- a point above a real point near which `G` misses `C̄`, in a given open side
  have hpt : ∀ {U : Set ℂ} (y : ℝ), M' ≤ |y| → y ≠ p → (∃ ε > 0, ∀ z : ℂ,
      dist z (psiMap p y) < ε → 0 < z.im → z ∈ U) → ∃ z ∈ U, z ∈ H ∧ G z ∉ closure C := by
    intro U y hy hyp ⟨ε₁, hε₁, hε₁U⟩
    obtain ⟨ε₂, hε₂, hε₂G⟩ := hnear y hy hyp
    set ε := min ε₁ ε₂ with hε
    have hεpos : 0 < ε := lt_min hε₁ hε₂
    set z : ℂ := psiMap p y + ((ε / 2 : ℝ) : ℂ) * I with hz
    have hzd : dist z (psiMap p y) = ε / 2 := by
      rw [hz, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real,
        Real.norm_of_nonneg (by positivity)]
    have hzim : 0 < z.im := by simp [hz, psiMap_ofReal]; positivity
    refine ⟨z, hε₁U z (by rw [hzd]; linarith [min_le_left ε₁ ε₂]) hzim, hzim,
      hε₂G z (QuantumZipper.H_subset_Hbar hzim) (by rw [hzd]; linarith [min_le_right ε₁ ε₂])⟩
  have hJR₁ : ∀ x : ℝ, (x : ℂ) ∈ b₁ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0 ↔ x ∈ Icc x₁ 0 := by
    intro x
    constructor
    · rintro (hx | ⟨y, hy, hyx⟩)
      · rcases arcInf_real hb₁0 hb₁1 hb₁H hx (by simp) with h' | h'
        · rw [ofReal_injective h']; exact ⟨le_rfl, hx₁0.le⟩
        · rw [ofReal_eq_zero.1 h']; exact ⟨hx₁0.le, le_rfl⟩
      · rw [← ofReal_injective hyx]; exact hy
    · intro hx; exact Or.inr ⟨x, hx, rfl⟩
  have fwd : ∀ z ∈ H, G z ∈ C →
      z ∈ innerSide Γ := by
    intro z hz hGz
    have hzΘ : z ∉ b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0 := by
      rintro ((hz1 | hz1) | ⟨y, -, rfl⟩)
      · rcases mem_arc_trichotomy hz1 with h' | h' | h'
        · rw [h', hb₁0] at hz; exact not_mem_H_ofReal _ hz
        · exact hfr2 z (Or.inl h') hGz
        · rw [h', hb₁1] at hz
          have h1 : (0 : ℝ) < (0 : ℂ).im := hz
          simp at h1
      · rcases mem_arc_trichotomy hz1 with h' | h' | h'
        · rw [h', hb₂0] at hz; exact not_mem_H_ofReal _ hz
        · exact hfr2 z (Or.inr h') hGz
        · rw [h', hb₂1] at hz
          have h1 : (0 : ℝ) < (0 : ℂ).im := hz
          simp at h1
      · exact not_mem_H_ofReal y hz
    rcases hcover z hzΘ with hO | hI | hI₂
    · exfalso
      have hall := mapsTo_of_isPreconnected hC (isPreconnected_outerSide_inter_H hΞ₁ hΞ₁H hJR₁)
        (hGc.mono inter_subset_right) (fun s hs hsC => by
          rcases hfr1 s hs.2 hsC with h' | h'
          · exact outerSide_subset_compl hs.1
              (Or.inl (image_mono Ioo_subset_Icc_self h'))
          · exact disjoint_innerSide_outerSide.le_bot ⟨hside₂ h', hs.1⟩)
        ⟨hO, hz⟩ hGz
      set y₀ : ℝ := -(|M'| + |p| + 1) with hy₀
      have hy₀p : y₀ < p := by linarith [neg_abs_le p, abs_nonneg M']
      have hy₀M : M' ≤ |y₀| := by
        rw [hy₀, abs_neg, abs_of_pos (by positivity)]; linarith [le_abs_self M', abs_nonneg p]
      have hw₀ : 0 < -(y₀ - p)⁻¹ := neg_pos.2 (inv_lt_zero.2 (by linarith))
      have hw₀O : psiMap p y₀ ∈ outerSide (b₁ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0) := by
        rw [psiMap_ofReal]
        exact ofReal_mem_outerSide hΞ₁ hΞ₁H fun hm => by
          have := ((hJR₁ _).1 hm).2; linarith
      obtain ⟨ε₁, hε₁, hε₁O⟩ := Metric.isOpen_iff.1 hO₁o _ hw₀O
      obtain ⟨z₁, hz₁O, hz₁H, hz₁C⟩ := hpt y₀ hy₀M hy₀p.ne
        ⟨ε₁, hε₁, fun z hz _ => hε₁O hz⟩
      exact hz₁C (subset_closure (hall z₁ ⟨hz₁O, hz₁H⟩))
    · exact hI
    · exfalso
      have hall := mapsTo_of_isPreconnected hC hI₂p
        (hGc.mono (innerSide_subset_H hΞ₂ hΞ₂H)) (fun s hs hsC => by
          rcases hfr1 s (innerSide_subset_H hΞ₂ hΞ₂H hs) hsC with h' | h'
          · exact disjoint_innerSide_outerSide.le_bot ⟨hs, hside₁ h'⟩
          · exact innerSide_subset_compl hs (Or.inl (image_mono Ioo_subset_Icc_self h')))
        hI₂ hGz
      set y₂ : ℝ := |M'| + |q₂| + 1 with hy₂
      have hy₂q : q₂ < y₂ := by linarith [le_abs_self q₂, abs_nonneg M']
      have hy₂M : M' ≤ |y₂| := by
        rw [abs_of_pos (by positivity)]; linarith [le_abs_self M', abs_nonneg q₂]
      obtain ⟨hlt, hneg⟩ := psiMap_ofReal_lt hpq₂ hy₂q
      obtain ⟨ε₁, hε₁, hε₁I⟩ := halfDisc_side hb₂c hΞ₂ hΞ₂H hb₂0 hb₂1 hb₂H
        (v := -(y₂ - p)⁻¹) ⟨by rw [hx₂]; exact hlt, hneg⟩
      obtain ⟨z₂, hz₂I, -, hz₂C⟩ := hpt y₂ hy₂M (by linarith) ⟨ε₁, hε₁, fun z hz hzim => by
        rw [psiMap_ofReal] at hz
        rcases hε₁I z hz hzim.le with h' | h'
        · exact h'
        · exact absurd (im_eq_zero_of_mem_ofReal_image h') hzim.ne'⟩
      exact hz₂C (subset_closure (hall z₂ hz₂I))
  refine ⟨fwd ζ hζ, fun hζI => ?_⟩
  -- a point of `C ∩ D_r` near an unvisited boundary point
  have hx₀D := hα₁D (u₁ + 1) (by simp)
  have hx₀fr : α₁ (u₁ + 1) ∈ frontier C := by
    rw [hfrC]; exact Or.inl ⟨u₁ + 1, by simp only [mem_Ici]; linarith, rfl⟩
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1
    (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hr) _ hx₀D
  obtain ⟨y, hyb, hyC⟩ := mem_closure_iff.1 (frontier_subset_closure hx₀fr) _ isOpen_ball
    (mem_ball_self hε)
  have hyD := hεD hyb
  have hgH := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr hyD
  have hgp : fwdMap W r y ≠ p := fun h' => by rw [h'] at hgH; exact not_mem_H_ofReal p hgH
  have hz₀H : psiMap p (fwdMap W r y) ∈ H := (psiMap_mem_H_iff hgp).2 hgH
  have hGz₀ : G (psiMap p (fwdMap W r y)) = y := by
    simp only [hG, psiMapInv_psiMap, trMap_zero_fwdMap hW hW0 hr hyD]
  exact mapsTo_of_isPreconnected hC hIp (hGc.mono (innerSide_subset_H hΓ hΓH))
    (fun s hs hsC => by
      rcases hfr1 s (innerSide_subset_H hΓ hΓH hs) hsC with h' | h'
      · exact innerSide_subset_compl hs (hAΓ (Or.inl h'))
      · exact innerSide_subset_compl hs (hAΓ (Or.inr h')))
    (fwd _ hz₀H (by rw [hGz₀]; exact hyC)) (by rw [hGz₀]; exact hyC) ζ hζI


/-- **The face identification at infinity** (distinct gates). In the `ψ_p`-picture of the chart at
`r`, a point `ζ ∈ ℍ` is mapped by `f̄_r ∘ ψ_p⁻¹` into the pocket `C` iff it is on the inner side of
`Γ = B₁ ∪ B₂ ∪ [x₁, x₂]`. -/
theorem trMap_psiMapInv_mem_iff (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {r : ℝ} (hr : 0 ≤ r) {C : Set ℂ} (hC : IsOpen C)
    (hCR : ∃ M, ∀ y : ℝ, M ≤ |y| → (y : ℂ) ∉ closure C) {α₁ α₂ : ℝ → ℂ} {c₁ u₁ c₂ u₂ : ℝ}
    (hcu₁ : c₁ ≤ u₁) (hcu₂ : c₂ ≤ u₂) (hfrC : frontier C = α₁ '' Ici c₁ ∪ α₂ '' Ici c₂)
    (hα₁D : ∀ v ∈ Ioi u₁, α₁ v ∈ H \ fwdHull W r) (hα₂D : ∀ v ∈ Ioi u₂, α₂ v ∈ H \ fwdHull W r)
    (hα₁K : ∀ v ∈ Icc c₁ u₁, α₁ v ∉ H \ fwdHull W r)
    (hα₂K : ∀ v ∈ Icc c₂ u₂, α₂ v ∉ H \ fwdHull W r) {p q₂ x₁ x₂ : ℝ} {b₁ b₂ : ℝ → ℂ}
    (h : IsArcPairInf x₁ x₂ b₁ b₂) (hpq₂ : p < q₂) (hx₂ : x₂ = -(q₂ - p)⁻¹)
    (hb₁img : b₁ '' Ioo 0 1 = psiMap p '' (fwdMap W r '' (α₁ '' Ioi u₁)))
    (hb₂img : b₂ '' Ioo 0 1 = psiMap p '' (fwdMap W r '' (α₂ '' Ioi u₂))) {ζ : ℂ} (hζ : ζ ∈ H) :
    trMap W 0 r (psiMapInv p ζ) ∈ C ↔
      ζ ∈ innerSide (b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ x₂) :=
  trMap_psiMapInv_mem_iff_of_faces hη hW hW0 hr hC hCR hcu₁ hcu₂ hfrC hα₁D hα₂D hα₁K hα₂K
    (h.lt.trans h.neg) h.neg h.cont₁ h.cont₂ h.inj₁ h.inj₂ h.zero₁ h.zero₂ h.one₁ h.one₂ h.mem₁
    h.mem₂ h.isJordanCurve_face.1 h.isJordanCurve_face.2
    (by
      rintro z (hz | hz)
      · exact Or.inl (Or.inl (image_mono Ioo_subset_Icc_self hz))
      · exact Or.inl (Or.inr (image_mono Ioo_subset_Icc_self hz)))
    (fun z hz => h.compl_subset hz) h.arcInt₂_subset_innerSide₁ h.arcInt₁_subset_outerSide₂ hpq₂
    hx₂ hb₁img hb₂img hζ

/-- **The face identification at infinity, equal gates**, when the open arc `B₂` is inside
`Ξ₁ = B₁ ∪ [x, 0]`: the face is the inner side of the Jordan loop `B₁ ∪ B₂`. -/
theorem trMap_psiMapInv_mem_iff_eq_of_inside (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {r : ℝ} (hr : 0 ≤ r) {C : Set ℂ} (hC : IsOpen C)
    (hCR : ∃ M, ∀ y : ℝ, M ≤ |y| → (y : ℂ) ∉ closure C) {α₁ α₂ : ℝ → ℂ} {c₁ u₁ c₂ u₂ : ℝ}
    (hcu₁ : c₁ ≤ u₁) (hcu₂ : c₂ ≤ u₂) (hfrC : frontier C = α₁ '' Ici c₁ ∪ α₂ '' Ici c₂)
    (hα₁D : ∀ v ∈ Ioi u₁, α₁ v ∈ H \ fwdHull W r) (hα₂D : ∀ v ∈ Ioi u₂, α₂ v ∈ H \ fwdHull W r)
    (hα₁K : ∀ v ∈ Icc c₁ u₁, α₁ v ∉ H \ fwdHull W r)
    (hα₂K : ∀ v ∈ Icc c₂ u₂, α₂ v ∉ H \ fwdHull W r) {p q x : ℝ} {b₁ b₂ : ℝ → ℂ}
    (hx0 : x < 0) (hb₁c : ContinuousOn b₁ (Icc 0 1)) (hb₂c : ContinuousOn b₂ (Icc 0 1))
    (hb₁i : InjOn b₁ (Icc 0 1)) (hb₂i : InjOn b₂ (Icc 0 1)) (hb₁0 : b₁ 0 = x) (hb₂0 : b₂ 0 = x)
    (hb₁1 : b₁ 1 = 0) (hb₂1 : b₂ 1 = 0) (hb₁H : ∀ t ∈ Ioo (0 : ℝ) 1, b₁ t ∈ H)
    (hb₂H : ∀ t ∈ Ioo (0 : ℝ) 1, b₂ t ∈ H)
    (hinter : b₁ '' Icc 0 1 ∩ b₂ '' Icc 0 1 ⊆ {(x : ℂ), 0})
    (hin : b₂ '' Ioo 0 1 ⊆ innerSide (b₁ '' Icc 0 1 ∪ ofReal '' Icc x 0))
    (hpq : p < q) (hx : x = -(q - p)⁻¹)
    (hb₁img : b₁ '' Ioo 0 1 = psiMap p '' (fwdMap W r '' (α₁ '' Ioi u₁)))
    (hb₂img : b₂ '' Ioo 0 1 = psiMap p '' (fwdMap W r '' (α₂ '' Ioi u₂))) {ζ : ℂ} (hζ : ζ ∈ H) :
    trMap W 0 r (psiMapInv p ζ) ∈ C ↔ ζ ∈ innerSide (b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1) := by
  have hne : (x : ℂ) ≠ ((0 : ℝ) : ℂ) := fun h' => by have := ofReal_injective h'; linarith
  have hseg : segPath (x : ℂ) ((0 : ℝ) : ℂ) '' Icc 0 1 = ofReal '' Icc x 0 :=
    image_segPath_ofReal hx0.le
  have hu : Foundations.ThetaCurve.IsArcFrom b₁ (x : ℂ) 0 := ⟨hb₁c, hb₁i, hb₁0, hb₁1⟩
  have hv : Foundations.ThetaCurve.IsArcFrom (segPath (x : ℂ) ((0 : ℝ) : ℂ)) (x : ℂ) 0 :=
    ⟨(continuous_segPath _ _).continuousOn, injOn_segPath hne, segPath_zero _ _,
      by rw [segPath_one, ofReal_zero]⟩
  have hw : Foundations.ThetaCurve.IsArcFrom b₂ (x : ℂ) 0 := ⟨hb₂c, hb₂i, hb₂0, hb₂1⟩
  have hav : Foundations.ThetaCurve.arc (segPath (x : ℂ) ((0 : ℝ) : ℂ)) = ofReal '' Icc x 0 :=
    hseg
  have huv : Foundations.ThetaCurve.arc b₁ ∩
      Foundations.ThetaCurve.arc (segPath (x : ℂ) ((0 : ℝ) : ℂ)) ⊆ {(x : ℂ), 0} := by
    rw [hav]; rintro w ⟨hw1, ⟨y, -, rfl⟩⟩; exact arcInf_real hb₁0 hb₁1 hb₁H hw1 (by simp)
  have hvw : Foundations.ThetaCurve.arc (segPath (x : ℂ) ((0 : ℝ) : ℂ)) ∩
      Foundations.ThetaCurve.arc b₂ ⊆ {(x : ℂ), 0} := by
    rw [hav]; rintro w ⟨⟨y, -, rfl⟩, hw2⟩; exact arcInf_real hb₂0 hb₂1 hb₂H hw2 (by simp)
  have huw : Foundations.ThetaCurve.arc b₁ ∩ Foundations.ThetaCurve.arc b₂ ⊆ {(x : ℂ), 0} :=
    hinter
  obtain ⟨hΞ₁, hΞ₁H⟩ := isJordanCurve_sideInf hx0 hb₁c hb₁i hb₁0 hb₁1 hb₁H
  obtain ⟨hΞ₂, hΞ₂H⟩ := isJordanCurve_sideInf hx0 hb₂c hb₂i hb₂0 hb₂1 hb₂H
  have hΓ := Sec7.isJordanCurve_image_union hb₁c hb₂c hb₁i hb₂i (by rw [hb₁0, hb₂0])
    (by rw [hb₁1, hb₂1]) (by rw [hb₁0, hb₁1]; exact hinter)
  have hΓH : b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ⊆ Hbar :=
    union_subset (image_arcInf_subset_Hbar hb₁0 hb₁1 hb₁H)
      (image_arcInf_subset_Hbar hb₂0 hb₂1 hb₂H)
  have E1 : Foundations.ThetaCurve.arc (segPath (x : ℂ) ((0 : ℝ) : ℂ)) ∪
      Foundations.ThetaCurve.arc b₁ = b₁ '' Icc 0 1 ∪ ofReal '' Icc x 0 := by
    rw [hav, union_comm]
  have E2 : Foundations.ThetaCurve.arc (segPath (x : ℂ) ((0 : ℝ) : ℂ)) ∪
      Foundations.ThetaCurve.arc b₂ = b₂ '' Icc 0 1 ∪ ofReal '' Icc x 0 := by
    rw [hav, union_comm]
  -- `B₁°` is outside `Ξ₂`
  have hside₁ : b₁ '' Ioo 0 1 ⊆ outerSide (b₂ '' Icc 0 1 ∪ ofReal '' Icc x 0) := by
    have hin' : Foundations.ThetaCurve.arcInt b₂ ⊆ WangWu.jordanIn
        (Foundations.ThetaCurve.arc (segPath (x : ℂ) ((0 : ℝ) : ℂ)) ∪
          Foundations.ThetaCurve.arc b₁) := by
      rw [E1, jordanIn_eq_innerSide hΞ₁ hΞ₁H]; exact hin
    have h1 := Foundations.ThetaCurve.arcInt_subset_jordanOut hv hu hw
      (by rw [inter_comm]; exact huv) hvw huw hin'
    rw [E2, jordanOut_eq_outerSide hΞ₂ hΞ₂H] at h1
    exact h1
  refine trMap_psiMapInv_mem_iff_of_faces hη hW hW0 hr hC hCR hcu₁ hcu₂ hfrC hα₁D hα₂D hα₁K
    hα₂K hx0 hx0 hb₁c hb₂c hb₁i hb₂i hb₁0 hb₂0 hb₁1 hb₂1 hb₁H hb₂H hΓ hΓH ?_ ?_ hin hside₁ hpq
    hx hb₁img hb₂img hζ
  · rintro z (hz | hz)
    · exact Or.inl (image_mono Ioo_subset_Icc_self hz)
    · exact Or.inr (image_mono Ioo_subset_Icc_self hz)
  · intro z hz
    have hzΘ : z ∉ Foundations.ThetaCurve.arc b₁ ∪
        Foundations.ThetaCurve.arc (segPath (x : ℂ) ((0 : ℝ) : ℂ)) ∪
        Foundations.ThetaCurve.arc b₂ := by
      rw [hav]
      rintro ((h1 | h1) | h1)
      · exact hz (Or.inl (Or.inl h1))
      · exact hz (Or.inr h1)
      · exact hz (Or.inl (Or.inr h1))
    have hmain := Foundations.ThetaCurve.compl_theta_subset hu hv hw huv huw hvw hzΘ
    rw [show Foundations.ThetaCurve.arc b₁ ∪
        Foundations.ThetaCurve.arc (segPath (x : ℂ) ((0 : ℝ) : ℂ)) =
          b₁ '' Icc 0 1 ∪ ofReal '' Icc x 0 by rw [hav], E2,
      jordanOut_eq_outerSide hΞ₁ hΞ₁H, jordanIn_eq_innerSide hΓ hΓH,
      jordanIn_eq_innerSide hΞ₂ hΞ₂H] at hmain
    rcases hmain with (h1 | h1) | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)

/-- **Propositions 1.5–1.6 at infinity, arc level** (distinct gates, `ψ_p`-picture). With the
compactified arcs `b_i` of the unvisited prefixes in the chart at `r ≤ a` (`x_i = ψ_p(q_i)`), if on
the gap `[a, b]` the trace avoids `C` and the prefixes, `δ_r` avoids `p`, the final endpoint is a
limit of `C`-visits after `r`, and the initial endpoint is either such a limit or has `δ_r(a)` a
gate, then `δ_r(a) = δ_r(b)`. -/
theorem ownFuture_eq_of_psiArms (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {r : ℝ} (hr : 0 ≤ r) {C : Set ℂ} (hC : IsOpen C)
    (hCR : ∃ M, ∀ y : ℝ, M ≤ |y| → (y : ℂ) ∉ closure C) {α₁ α₂ : ℝ → ℂ} {c₁ u₁ c₂ u₂ : ℝ}
    (hcu₁ : c₁ ≤ u₁) (hcu₂ : c₂ ≤ u₂) (hfrC : frontier C = α₁ '' Ici c₁ ∪ α₂ '' Ici c₂)
    (hα₁D : ∀ v ∈ Ioi u₁, α₁ v ∈ H \ fwdHull W r) (hα₂D : ∀ v ∈ Ioi u₂, α₂ v ∈ H \ fwdHull W r)
    (hα₁K : ∀ v ∈ Icc c₁ u₁, α₁ v ∉ H \ fwdHull W r)
    (hα₂K : ∀ v ∈ Icc c₂ u₂, α₂ v ∉ H \ fwdHull W r) {p q₁ q₂ x₁ x₂ : ℝ} {b₁ b₂ : ℝ → ℂ}
    (h : IsArcPairInf x₁ x₂ b₁ b₂) (hpq₂ : p < q₂) (hx₁ : x₁ = -(q₁ - p)⁻¹)
    (hx₂ : x₂ = -(q₂ - p)⁻¹)
    (hb₁img : b₁ '' Ioo 0 1 = psiMap p '' (fwdMap W r '' (α₁ '' Ioi u₁)))
    (hb₂img : b₂ '' Ioo 0 1 = psiMap p '' (fwdMap W r '' (α₂ '' Ioi u₂)))
    {a b : ℝ} (hra : r ≤ a) (hab : a < b) (hδp : ∀ t ∈ Icc a b, trMap W r t 0 ≠ p)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C) (hunv₁ : ∀ t ∈ Icc a b, ∀ v ∈ Ioi u₁, η t ≠ α₁ v)
    (hunv₂ : ∀ t ∈ Icc a b, ∀ v ∈ Ioi u₂, η t ≠ α₂ v)
    (ha : (trMap W r a 0 = q₁ ∨ trMap W r a 0 = q₂) ∨ a ∈ closure {t | r < t ∧ η t ∈ C})
    (hb : b ∈ closure {t | r < t ∧ η t ∈ C}) : trMap W r a 0 = trMap W r b 0 := by
  set Γ := b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ x₂ with hΓdef
  have hiff := fun ζ (hζ : ζ ∈ H) => trMap_psiMapInv_mem_iff hη hW hW0 hr hC hCR hcu₁ hcu₂ hfrC
    hα₁D hα₂D hα₁K hα₂K h hpq₂ hx₂ hb₁img hb₂img hζ
  obtain ⟨hΓ, hΓH⟩ := h.isJordanCurve_face
  set δ : ℝ → ℂ := fun t => trMap W r t 0 with hδ
  set δ' : ℝ → ℂ := fun t => psiMap p (δ t) with hδ'
  have hδc : ContinuousOn δ (Icc a b) :=
    (YuanSimpleApprox.continuousOn_trMap_zero hη hW hW0 hr).mono fun t ht => hra.trans ht.1
  have hGδ : ∀ t, r ≤ t → trMap W 0 r (psiMapInv p (δ' t)) = η t := fun t hrt => by
    simp only [hδ', psiMapInv_psiMap, hδ]; exact traceMapOut_trMap_zero hη hW hW0 hr hrt
  -- confinement (1.1) in the `ψ_p`-picture, and (1.2) for the endpoints
  have h11 : ∀ t, r ≤ t → η t ∈ C → δ t ∈ H → δ t ∈ psiMap p ⁻¹' innerSide Γ := by
    intro t hrt htC hδH
    have hδp' : δ t ≠ p := fun h' => by rw [h'] at hδH; exact not_mem_H_ofReal p hδH
    exact (hiff _ ((psiMap_mem_H_iff hδp').2 hδH)).1 (by rw [hGδ t hrt]; exact htC)
  have hcl : ∀ t ∈ Icc a b, t ∈ closure {t | r < t ∧ η t ∈ C} → δ' t ∈ closure (innerSide Γ) := by
    intro t ht htcl
    have h1 := ownFuture_mem_closure_face hη hW hW0 hC hr h11 htcl
    have hcont : ContinuousAt (psiMap p) (δ t) :=
      continuousOn_psiMap.continuousAt (isOpen_compl_singleton.mem_nhds (hδp t ht))
    exact closure_mono (image_preimage_subset _ _) (hcont.continuousWithinAt.mem_closure_image h1)
  have hgate := h.gate_lemma (δ := δ') hab
    (continuousOn_psiMap.comp hδc fun t ht => hδp t ht)
    (fun t ht => psiMap_mem_Hbar (YuanSimpleApprox.trMap_zero_mem_Hbar hη hW hW0 hr
      (hra.trans ht.1)))
    (fun t ht hF => by
      have := (hiff _ (innerSide_subset_H hΓ hΓH hF)).2 hF
      rw [hGδ t (hra.trans ht.1)] at this
      exact hgap t ht this)
    (fun t ht hB => by
      rw [hb₁img] at hB
      obtain ⟨w, hw, hwe⟩ := hB
      rw [psiMap_injective hwe] at hw
      exact ownFuture_notMem_lift hη hW hW0 hr (hra.trans ht.1) hα₁D (hunv₁ t ht) hw)
    (fun t ht hB => by
      rw [hb₂img] at hB
      obtain ⟨w, hw, hwe⟩ := hB
      rw [psiMap_injective hwe] at hw
      exact ownFuture_notMem_lift hη hW hW0 hr (hra.trans ht.1) hα₂D (hunv₂ t ht) hw)
    (fun t ht h0 => hδp t ht (psiMap_eq_zero_iff.1 h0))
    (fun c d hac hcd hdb => by
      obtain ⟨t, ht, htH⟩ := ownFuture_not_forall_real hη hW hW0 hr (hra.trans hac) hcd
      exact ⟨t, ht, (psiMap_mem_H_iff (hδp t ⟨hac.trans ht.1, ht.2.trans hdb⟩)).2 htH⟩)
    (by
      rcases ha with (h1 | h1) | h1
      · left; simp only [hδ', hδ, h1, psiMap_ofReal, hx₁]
      · right; left; simp only [hδ', hδ, h1, psiMap_ofReal, hx₂]
      · right; right; exact hcl a ⟨le_rfl, hab.le⟩ h1)
    (hcl b ⟨hab.le, le_rfl⟩ hb)
  exact psiMap_injective hgate.1

/-- **The face identification at infinity, equal gates**: the face is the inner side of the Jordan
loop `B₁ ∪ B₂` (whichever arm is inner). -/
theorem trMap_psiMapInv_mem_iff_eq (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {r : ℝ} (hr : 0 ≤ r) {C : Set ℂ} (hC : IsOpen C)
    (hCR : ∃ M, ∀ y : ℝ, M ≤ |y| → (y : ℂ) ∉ closure C) {α₁ α₂ : ℝ → ℂ} {c₁ u₁ c₂ u₂ : ℝ}
    (hcu₁ : c₁ ≤ u₁) (hcu₂ : c₂ ≤ u₂) (hfrC : frontier C = α₁ '' Ici c₁ ∪ α₂ '' Ici c₂)
    (hα₁D : ∀ v ∈ Ioi u₁, α₁ v ∈ H \ fwdHull W r) (hα₂D : ∀ v ∈ Ioi u₂, α₂ v ∈ H \ fwdHull W r)
    (hα₁K : ∀ v ∈ Icc c₁ u₁, α₁ v ∉ H \ fwdHull W r)
    (hα₂K : ∀ v ∈ Icc c₂ u₂, α₂ v ∉ H \ fwdHull W r) {p q x : ℝ} {b₁ b₂ : ℝ → ℂ}
    (hx0 : x < 0) (hb₁c : ContinuousOn b₁ (Icc 0 1)) (hb₂c : ContinuousOn b₂ (Icc 0 1))
    (hb₁i : InjOn b₁ (Icc 0 1)) (hb₂i : InjOn b₂ (Icc 0 1)) (hb₁0 : b₁ 0 = x) (hb₂0 : b₂ 0 = x)
    (hb₁1 : b₁ 1 = 0) (hb₂1 : b₂ 1 = 0) (hb₁H : ∀ t ∈ Ioo (0 : ℝ) 1, b₁ t ∈ H)
    (hb₂H : ∀ t ∈ Ioo (0 : ℝ) 1, b₂ t ∈ H)
    (hinter : b₁ '' Icc 0 1 ∩ b₂ '' Icc 0 1 ⊆ {(x : ℂ), 0}) (hpq : p < q) (hx : x = -(q - p)⁻¹)
    (hb₁img : b₁ '' Ioo 0 1 = psiMap p '' (fwdMap W r '' (α₁ '' Ioi u₁)))
    (hb₂img : b₂ '' Ioo 0 1 = psiMap p '' (fwdMap W r '' (α₂ '' Ioi u₂))) {ζ : ℂ} (hζ : ζ ∈ H) :
    trMap W 0 r (psiMapInv p ζ) ∈ C ↔ ζ ∈ innerSide (b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1) := by
  have hne : (x : ℂ) ≠ ((0 : ℝ) : ℂ) := fun h' => by have := ofReal_injective h'; linarith
  have hseg : segPath (x : ℂ) ((0 : ℝ) : ℂ) '' Icc 0 1 = ofReal '' Icc x 0 :=
    image_segPath_ofReal hx0.le
  have hu : Foundations.ThetaCurve.IsArcFrom b₁ (x : ℂ) 0 := ⟨hb₁c, hb₁i, hb₁0, hb₁1⟩
  have hv : Foundations.ThetaCurve.IsArcFrom (segPath (x : ℂ) ((0 : ℝ) : ℂ)) (x : ℂ) 0 :=
    ⟨(continuous_segPath _ _).continuousOn, injOn_segPath hne, segPath_zero _ _,
      by rw [segPath_one, ofReal_zero]⟩
  have hw : Foundations.ThetaCurve.IsArcFrom b₂ (x : ℂ) 0 := ⟨hb₂c, hb₂i, hb₂0, hb₂1⟩
  have hav : Foundations.ThetaCurve.arc (segPath (x : ℂ) ((0 : ℝ) : ℂ)) = ofReal '' Icc x 0 :=
    hseg
  have hvu : Foundations.ThetaCurve.arc (segPath (x : ℂ) ((0 : ℝ) : ℂ)) ∩
      Foundations.ThetaCurve.arc b₁ ⊆ {(x : ℂ), 0} := by
    rw [hav]; rintro w ⟨⟨y, -, rfl⟩, hw1⟩; exact arcInf_real hb₁0 hb₁1 hb₁H hw1 (by simp)
  have hvw : Foundations.ThetaCurve.arc (segPath (x : ℂ) ((0 : ℝ) : ℂ)) ∩
      Foundations.ThetaCurve.arc b₂ ⊆ {(x : ℂ), 0} := by
    rw [hav]; rintro w ⟨⟨y, -, rfl⟩, hw2⟩; exact arcInf_real hb₂0 hb₂1 hb₂H hw2 (by simp)
  obtain ⟨hΞ₁, hΞ₁H⟩ := isJordanCurve_sideInf hx0 hb₁c hb₁i hb₁0 hb₁1 hb₁H
  obtain ⟨hΞ₂, hΞ₂H⟩ := isJordanCurve_sideInf hx0 hb₂c hb₂i hb₂0 hb₂1 hb₂H
  have hΓ := Sec7.isJordanCurve_image_union hb₁c hb₂c hb₁i hb₂i (by rw [hb₁0, hb₂0])
    (by rw [hb₁1, hb₂1]) (by rw [hb₁0, hb₁1]; exact hinter)
  have hΓH : b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ⊆ Hbar :=
    union_subset (image_arcInf_subset_Hbar hb₁0 hb₁1 hb₁H)
      (image_arcInf_subset_Hbar hb₂0 hb₂1 hb₂H)
  rcases Foundations.ThetaCurve.exists_arcInt_subset_jordanIn hv hu hw hvu hvw hinter with
    h1 | h1 | h1
  · rw [hav, union_comm, jordanIn_eq_innerSide hΞ₁ hΞ₁H] at h1
    exact trMap_psiMapInv_mem_iff_eq_of_inside hη hW hW0 hr hC hCR hcu₁ hcu₂ hfrC hα₁D hα₂D
      hα₁K hα₂K hx0 hb₁c hb₂c hb₁i hb₂i hb₁0 hb₂0 hb₁1 hb₂1 hb₁H hb₂H hinter h1 hpq hx hb₁img
      hb₂img hζ
  · exfalso
    rw [jordanIn_eq_innerSide hΓ hΓH] at h1
    have hmid : segPath (x : ℂ) ((0 : ℝ) : ℂ) (1 / 2) ∈
        Foundations.ThetaCurve.arcInt (segPath (x : ℂ) ((0 : ℝ) : ℂ)) :=
      ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
    have := innerSide_subset_H hΓ hΓH (h1 hmid)
    rw [segPath_ofReal] at this
    exact not_mem_H_ofReal _ this
  · rw [hav, union_comm, jordanIn_eq_innerSide hΞ₂ hΞ₂H] at h1
    rw [union_comm (b₁ '' Icc 0 1)]
    exact trMap_psiMapInv_mem_iff_eq_of_inside hη hW hW0 hr hC hCR hcu₂ hcu₁
      (by rw [hfrC, union_comm]) hα₂D hα₁D hα₂K hα₁K hx0 hb₂c hb₁c hb₂i hb₁i hb₂0 hb₁0 hb₂1 hb₁1
      hb₂H hb₁H (by rw [inter_comm]; exact hinter) h1 hpq hx hb₂img hb₁img hζ

/-- **Propositions 1.5–1.6 at infinity, arc level, equal gates** (`ψ_p`-picture): both endpoint
values of `ψ_p ∘ δ_r` are the common gate `x = ψ_p(q)`. -/
theorem ownFuture_eq_of_psiArms_eq (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {r : ℝ} (hr : 0 ≤ r) {C : Set ℂ} (hC : IsOpen C)
    (hCR : ∃ M, ∀ y : ℝ, M ≤ |y| → (y : ℂ) ∉ closure C) {α₁ α₂ : ℝ → ℂ} {c₁ u₁ c₂ u₂ : ℝ}
    (hcu₁ : c₁ ≤ u₁) (hcu₂ : c₂ ≤ u₂) (hfrC : frontier C = α₁ '' Ici c₁ ∪ α₂ '' Ici c₂)
    (hα₁D : ∀ v ∈ Ioi u₁, α₁ v ∈ H \ fwdHull W r) (hα₂D : ∀ v ∈ Ioi u₂, α₂ v ∈ H \ fwdHull W r)
    (hα₁K : ∀ v ∈ Icc c₁ u₁, α₁ v ∉ H \ fwdHull W r)
    (hα₂K : ∀ v ∈ Icc c₂ u₂, α₂ v ∉ H \ fwdHull W r) {p q x : ℝ} {b₁ b₂ : ℝ → ℂ}
    (hx0 : x < 0) (hb₁c : ContinuousOn b₁ (Icc 0 1)) (hb₂c : ContinuousOn b₂ (Icc 0 1))
    (hb₁i : InjOn b₁ (Icc 0 1)) (hb₂i : InjOn b₂ (Icc 0 1)) (hb₁0 : b₁ 0 = x) (hb₂0 : b₂ 0 = x)
    (hb₁1 : b₁ 1 = 0) (hb₂1 : b₂ 1 = 0) (hb₁H : ∀ t ∈ Ioo (0 : ℝ) 1, b₁ t ∈ H)
    (hb₂H : ∀ t ∈ Ioo (0 : ℝ) 1, b₂ t ∈ H)
    (hinter : b₁ '' Icc 0 1 ∩ b₂ '' Icc 0 1 ⊆ {(x : ℂ), 0}) (hpq : p < q) (hx : x = -(q - p)⁻¹)
    (hb₁img : b₁ '' Ioo 0 1 = psiMap p '' (fwdMap W r '' (α₁ '' Ioi u₁)))
    (hb₂img : b₂ '' Ioo 0 1 = psiMap p '' (fwdMap W r '' (α₂ '' Ioi u₂)))
    {a b : ℝ} (hra : r ≤ a) (hab : a ≤ b) (hδp : ∀ t ∈ Icc a b, trMap W r t 0 ≠ p)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C) (hunv₁ : ∀ t ∈ Icc a b, ∀ v ∈ Ioi u₁, η t ≠ α₁ v)
    (hunv₂ : ∀ t ∈ Icc a b, ∀ v ∈ Ioi u₂, η t ≠ α₂ v)
    (ha : trMap W r a 0 = q ∨ a ∈ closure {t | r < t ∧ η t ∈ C})
    (hb : b ∈ closure {t | r < t ∧ η t ∈ C}) : trMap W r a 0 = trMap W r b 0 := by
  set Γ := b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 with hΓdef
  have hiff := fun ζ (hζ : ζ ∈ H) => trMap_psiMapInv_mem_iff_eq hη hW hW0 hr hC hCR hcu₁ hcu₂
    hfrC hα₁D hα₂D hα₁K hα₂K hx0 hb₁c hb₂c hb₁i hb₂i hb₁0 hb₂0 hb₁1 hb₂1 hb₁H hb₂H hinter hpq hx
    hb₁img hb₂img hζ
  have hΓ := Sec7.isJordanCurve_image_union hb₁c hb₂c hb₁i hb₂i (by rw [hb₁0, hb₂0])
    (by rw [hb₁1, hb₂1]) (by rw [hb₁0, hb₁1]; exact hinter)
  have hΓH : Γ ⊆ Hbar := union_subset (image_arcInf_subset_Hbar hb₁0 hb₁1 hb₁H)
    (image_arcInf_subset_Hbar hb₂0 hb₂1 hb₂H)
  set δ : ℝ → ℂ := fun t => trMap W r t 0 with hδ
  have hGδ : ∀ t, r ≤ t → trMap W 0 r (psiMapInv p (psiMap p (δ t))) = η t := fun t hrt => by
    simp only [psiMapInv_psiMap, hδ]; exact traceMapOut_trMap_zero hη hW hW0 hr hrt
  have h11 : ∀ t, r ≤ t → η t ∈ C → δ t ∈ H → δ t ∈ psiMap p ⁻¹' innerSide Γ := by
    intro t hrt htC hδH
    have hδp' : δ t ≠ p := fun h' => by rw [h'] at hδH; exact not_mem_H_ofReal p hδH
    exact (hiff _ ((psiMap_mem_H_iff hδp').2 hδH)).1 (by rw [hGδ t hrt]; exact htC)
  -- each endpoint approached by `C`-visits is mapped to the gate
  have hend : ∀ t ∈ Icc a b, t ∈ closure {t | r < t ∧ η t ∈ C} → psiMap p (δ t) = x := by
    intro t ht htcl
    have h1 := ownFuture_mem_closure_face hη hW hW0 hC hr h11 htcl
    have hcont : ContinuousAt (psiMap p) (δ t) :=
      continuousOn_psiMap.continuousAt (isOpen_compl_singleton.mem_nhds (hδp t ht))
    have hcl := closure_mono (image_preimage_subset _ _)
      (hcont.continuousWithinAt.mem_closure_image h1)
    have hF : psiMap p (δ t) ∉ innerSide Γ := fun hF => by
      have := (hiff _ (innerSide_subset_H hΓ hΓH hF)).2 hF
      rw [hGδ t (hra.trans ht.1)] at this
      exact hgap t ht this
    rcases mem_of_mem_closure_innerSide (isCompact_of_isJordanCurve hΓ).isClosed hcl hF with
      hw | hw
    · rcases mem_arc_trichotomy hw with h' | h' | h'
      · rw [h', hb₁0]
      · rw [hb₁img] at h'
        obtain ⟨w, hw', hwe⟩ := h'
        rw [psiMap_injective hwe] at hw'
        exact absurd hw' (ownFuture_notMem_lift hη hW hW0 hr (hra.trans ht.1) hα₁D (hunv₁ t ht))
      · exact absurd (psiMap_eq_zero_iff.1 (h'.trans hb₁1)) (hδp t ht)
    · rcases mem_arc_trichotomy hw with h' | h' | h'
      · rw [h', hb₂0]
      · rw [hb₂img] at h'
        obtain ⟨w, hw', hwe⟩ := h'
        rw [psiMap_injective hwe] at hw'
        exact absurd hw' (ownFuture_notMem_lift hη hW hW0 hr (hra.trans ht.1) hα₂D (hunv₂ t ht))
      · exact absurd (psiMap_eq_zero_iff.1 (h'.trans hb₂1)) (hδp t ht)
  have hxa : psiMap p (δ a) = x := by
    rcases ha with h1 | h1
    · simp only [hδ, h1, psiMap_ofReal, hx]
    · exact hend a ⟨le_rfl, hab⟩ h1
  exact psiMap_injective (hxa.trans (hend b ⟨hab, le_rfl⟩ hb).symm)

end InteractingSLE.Sec6
