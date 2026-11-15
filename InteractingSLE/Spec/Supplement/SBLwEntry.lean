/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLwChart

/-!
# The walk's launch chart as a left entry chart: boundary limits and S5's coordinates

Packet PROVE-T14-SBLEAVES2, item (b). Complements `SBLwChart`:

* `norm_sub_le_of_tendsto_mapOut`: the real boundary values of a mapping-out function near untouched real points are
  `48`-Lipschitz (from `IsMapOut.norm_sub_le_of_disjoint`), so they converge at the left entry point (clause 2);
* `isDomainChart_shiftChart`: a domain chart read in S5's coordinates (`Lw.shiftChart`) is a domain chart of the
  translated domain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lw

theorem ofReal_mem_Hbar (x : ℝ) : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℂ)).im by simp

/-- **Boundary values of a mapping-out function near untouched real points are `48`-Lipschitz.** -/
theorem norm_sub_le_of_tendsto_mapOut {E : Set ℂ} {g : ℂ → ℂ} (hE : IsHPHull E) (hg : IsMapOut E g) {y ρ : ℝ}
    (hd : Disjoint (ball (y : ℂ) ρ) E) {x₁ x₂ : ℝ} (h₁ : (x₁ : ℂ) ∈ ball (y : ℂ) (ρ / 2))
    (h₂ : (x₂ : ℂ) ∈ ball (y : ℂ) (ρ / 2)) {L₁ L₂ : ℂ} (hL₁ : Tendsto g (𝓝[H] (x₁ : ℂ)) (𝓝 L₁))
    (hL₂ : Tendsto g (𝓝[H] (x₂ : ℂ)) (𝓝 L₂)) : ‖L₂ - L₁‖ ≤ 48 * |x₂ - x₁| := by
  have := GW1P.neBot_nhdsWithin_H (ofReal_mem_Hbar x₁)
  have := GW1P.neBot_nhdsWithin_H (ofReal_mem_Hbar x₂)
  set F := 𝓝[H] (x₁ : ℂ) ×ˢ 𝓝[H] (x₂ : ℂ)
  have hT : Tendsto (fun p : ℂ × ℂ => ‖g p.2 - g p.1‖) F (𝓝 ‖L₂ - L₁‖) :=
    ((hL₂.comp tendsto_snd).sub (hL₁.comp tendsto_fst)).norm
  have hF : F ≤ 𝓝 ((x₁ : ℂ), (x₂ : ℂ)) := by
    rw [nhds_prod_eq]; exact Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds
  have hT' : Tendsto (fun p : ℂ × ℂ => 48 * ‖p.2 - p.1‖) F (𝓝 (48 * ‖(x₂ : ℂ) - x₁‖)) :=
    ((continuous_const.mul (continuous_snd.sub continuous_fst).norm).tendsto _).mono_left hF
  have hmem : ∀ x : ℝ, (x : ℂ) ∈ ball (y : ℂ) (ρ / 2) → ball (y : ℂ) (ρ / 2) ∩ H ∈ 𝓝[H] (x : ℂ) := fun x hx =>
    inter_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hx)) self_mem_nhdsWithin
  have hle := le_of_tendsto_of_tendsto hT hT' (by
    filter_upwards [prod_mem_prod (hmem x₁ h₁) (hmem x₂ h₂)] with p hp
    exact hg.norm_sub_le_of_disjoint hE hd hp.1 hp.2)
  have hn : ‖(x₂ : ℂ) - x₁‖ = |x₂ - x₁| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rwa [hn] at hle

/-- **A domain chart in S5's coordinates.** -/
theorem isDomainChart_shiftChart {D : Set ℂ} {c : Chart} (hc : IsDomainChart D c) (u m : ℝ) :
    IsDomainChart ((fun z => z - (u : ℂ)) '' D) (shiftChart c u m) := by
  have hHm : ∀ w : ℂ, w ∈ H → w + m ∈ H := fun w hw => (add_real_mem_H_iff m).2 hw
  have hHs : ∀ w : ℂ, w ∈ H → w - u ∈ H := fun w hw => by
    simpa [sub_eq_add_neg] using (add_real_mem_H_iff (-u)).2 hw
  obtain ⟨⟨hdiff, hmaps, hinv⟩, himg, L, ⟨hLd, hLe⟩, hlift⟩ := hc
  refine ⟨⟨?_, fun w hw => hHs _ (hmaps (hHm w hw)), fun w hw => ?_⟩, ?_, fun z => L (z + u), ⟨?_, ?_⟩, ?_⟩
  · show DifferentiableOn ℂ (fun w => c.2.1 (w + m) - u) H
    exact (hdiff.comp (differentiableOn_id.add_const _) fun w hw => hHm w hw).sub_const _
  · simp only [shiftChart_inv, shiftChart_fwd, sub_add_cancel]
    rw [hinv _ (hHm w hw), add_sub_cancel_right]
  · ext z
    simp only [shiftChart_inv, mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨c.2.1 (w + m), himg ▸ ⟨w + m, hHm w hw, rfl⟩, rfl⟩
    · rintro ⟨z', hz', rfl⟩
      rw [← himg] at hz'
      obtain ⟨w, hw, rfl⟩ := hz'
      refine ⟨w - m, ?_, by simp⟩
      simpa [sub_eq_add_neg] using (add_real_mem_H_iff (-m)).2 hw
  · exact hLd.comp (differentiableOn_id.add_const _) fun z hz => by
      obtain ⟨z', hz', rfl⟩ := hz
      simpa using hz'
  · rintro _ ⟨z', hz', rfl⟩
    simp only [sub_add_cancel]
    rw [hLe z' hz']
    have h1 : deriv (shiftChart c u m).1 (z' - u) = deriv (fun z => c.1 (z + u)) (z' - u) := by
      show deriv (fun z => c.1 (z + u) - m) (z' - u) = _
      rw [deriv_sub_const]
    rw [h1, deriv_comp_add_const, sub_add_cancel]
  · rintro _ ⟨z', hz', rfl⟩
    simp only [shiftChart, sub_add_cancel]
    exact hlift hz'

theorem image_sub_real_H (u : ℝ) : (fun z : ℂ => z - (u : ℂ)) '' H = H := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [sub_eq_add_neg] using (add_real_mem_H_iff (-u)).2 hw
  · intro hz
    exact ⟨z + u, (add_real_mem_H_iff u).2 hz, by simp⟩

theorem fillH_image_sub_real (A : Set ℂ) (u : ℝ) :
    fillH ((fun z : ℂ => z - (u : ℂ)) '' A) = (fun z : ℂ => z - (u : ℂ)) '' fillH A := by
  have e : (fun z : ℂ => z - (u : ℂ)) = (fun z : ℂ => z + ((-u : ℝ) : ℂ)) := by
    funext z; push_cast; ring
  rw [e]
  exact Restart.fillH_image_add_real A (-u)

theorem tendsto_add_real_nhdsWithin_H (x : ℂ) (u : ℝ) :
    Tendsto (fun z : ℂ => z + u) (𝓝[H] x) (𝓝[H] (x + u)) :=
  tendsto_nhdsWithin_iff.2 ⟨((continuous_id.add continuous_const).tendsto x).mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall fun _z hz => (add_real_mem_H_iff u).2 hz⟩

theorem tendsto_add_cobounded (a : ℂ) {l : Filter ℂ} (h : l ≤ Bornology.cobounded ℂ) :
    Tendsto (fun z => z + a) l (Bornology.cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  have h2 : Tendsto (fun z : ℂ => ‖z‖) l atTop := tendsto_norm_cobounded_atTop.mono_left h
  refine tendsto_atTop_mono (fun z => ?_) (tendsto_atTop_add_const_right _ (-‖a‖) h2)
  have := norm_sub_norm_le z (-a)
  simp only [norm_neg, sub_neg_eq_add] at this
  show ‖z‖ + -‖a‖ ≤ ‖z + a‖
  linarith

/-- **The entry value of SB2(1)'s relative curve is the chart's boundary value at `L`.** If the boundary map `g` of
`c⁻¹` sends a real `y` to `L`, and `c` has the boundary value `m₀` at `L`, then `y = m₀`. -/
theorem eq_of_bdryMap_eq {c : Chart} (hcc : c.IsConformal) {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) {L : ℝ} {m₀ : ℂ} (hm : Tendsto c.1 (𝓝[H] (L : ℂ)) (𝓝 m₀)) {y : ℝ}
    (hy : g y = L) : (y : ℂ) = m₀ := by
  have := GW1P.neBot_nhdsWithin_H (ofReal_mem_Hbar y)
  have hg : Tendsto g (𝓝[H] (y : ℂ)) (𝓝[H] (L : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · rw [← hy]
      exact (hgc (y : ℂ) (ofReal_mem_Hbar y)).tendsto.mono_left
        (nhdsWithin_mono _ fun z hz => le_of_lt (show (0 : ℝ) < z.im from hz))
    · filter_upwards [self_mem_nhdsWithin] with w hw
      rw [hgi hw]; exact hcc.2.1 hw
  have h1 : Tendsto (fun w => c.1 (g w)) (𝓝[H] (y : ℂ)) (𝓝 m₀) := hm.comp hg
  have h2 : Tendsto (fun w => c.1 (g w)) (𝓝[H] (y : ℂ)) (𝓝 (y : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [hgi hw, hcc.2.2 w hw]; rfl
  exact tendsto_nhds_unique h2 h1

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

open WalkIntCanon Exist.Staged Exist.StagedLaw in
/-- **The walk's launch chart is a left entry chart in S5's coordinates.** Let the run be regular and not finished,
`A` compact with the fill of the run's prefix (e.g. `lowerPrefix`, `fillH_union_real`), `L` at most every real point
of `A`, and a ball around `L` missing the fill (`L` is not touched by the run's points in `ℍ`). Then the run chart has
a real boundary value `m` at `L`, and read in S5's coordinates (`shiftChart c u m`) it is a left entry chart of
`A − u` at `L − u`. -/
theorem isLeftEntryChart_shift_of_runChart (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) {A : Set ℂ} (hAc : IsCompact A)
    (hAf : fillH A = fillH (SB.prefixPhysSet κ b jumps spec D n)) {L : ℝ} (hLA : ∀ y : ℝ, (y : ℂ) ∈ A → L ≤ y)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : Disjoint (ball (L : ℂ) ρ) (fillH A)) (u : ℝ) :
    ∃ m : ℝ, Tendsto (stChart (ExplState.run κ b jumps spec D n)).1 (𝓝[H] (L : ℂ)) (𝓝 (m : ℂ)) ∧
      IsLeftEntryChart ((fun z => z - (u : ℂ)) '' A) (L - u)
        (shiftChart (stChart (ExplState.run κ b jumps spec D n)) u m) := by
  set c := stChart (ExplState.run κ b jumps spec D n) with hcdef
  obtain ⟨M, hK⟩ := exists_hullModel_fill spec D hreg n hnot
  have hd : Disjoint (ball (L : ℂ) ρ) M.hull := by rw [hK, ← hAf]; exact hball
  -- boundary values of the map out `g = c.1 + shift`
  have hbv : ∀ x : ℝ, (x : ℂ) ∈ ball (L : ℂ) (ρ / 2) →
      ∃ e : ℝ, Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (e : ℂ)) := by
    intro x hx
    obtain ⟨L₀, hL0, hL⟩ := IsMapOut.exists_tendsto_of_disjoint M.isHull M.mapOut hd hx (by simp)
    have hnhds : 𝓝[ball (L : ℂ) (ρ / 2) ∩ H] (x : ℂ) = 𝓝[H] (x : ℂ) :=
      nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hx))
    rw [hnhds] at hL
    refine ⟨L₀.re - M.shift, ?_⟩
    have hLre : ((L₀.re - M.shift : ℝ) : ℂ) = L₀ - M.shift := by
      apply Complex.ext <;> simp [hL0]
    rw [hLre]
    simpa using hL.sub_const (M.shift : ℂ)
  obtain ⟨m, hm⟩ := hbv L (mem_ball_self (half_pos hρ))
  refine ⟨m, hm, ?_, ?_, ?_, ?_⟩
  · -- clause 1
    have h1 := isDomainChart_shiftChart (hAf ▸ isDomainChart_runChart spec D hreg n hnot) u m
    rw [fillH_image_sub_real, ← image_sub_real_H u, ← image_sdiff (sub_left_injective (b := (u : ℂ)))]
    exact h1
  · -- clause 2: boundary values tending to `0` at the entry point
    set e₀ : ℝ → ℝ := fun x => (limUnder (𝓝[H] (x : ℂ)) c.1).re with he₀
    have he₀x : ∀ x : ℝ, x < L → Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (e₀ x : ℂ)) := by
      intro x hx
      obtain ⟨e, he⟩ := exists_tendsto_runChart_real spec D hreg n hnot hAc hAf
        (fun y hy => lt_of_lt_of_le hx (hLA y hy))
      have := GW1P.neBot_nhdsWithin_H (ofReal_mem_Hbar x)
      have : e₀ x = e := by rw [he₀]; simp only; rw [he.limUnder_eq, Complex.ofReal_re]
      rw [this]; exact he
    refine ⟨fun x => e₀ (x + u) - m, fun x hx => ?_, ?_⟩
    · have h0 := tendsto_add_real_nhdsWithin_H (x : ℂ) u
      have h2 : ((x : ℂ) + u) = ((x + u : ℝ) : ℂ) := by push_cast; ring
      rw [h2] at h0
      have h1 := (he₀x (x + u) (by linarith)).comp h0
      have h3 := h1.sub_const (m : ℂ)
      push_cast
      exact h3
    · have hlim : Tendsto (fun x : ℝ => 48 * |x + u - L|) (𝓝[<] (L - u)) (𝓝 0) := by
        have hc : Continuous (fun x : ℝ => 48 * |x + u - L|) := by fun_prop
        have := (hc.tendsto (L - u)).mono_left (nhdsWithin_le_nhds (s := Iio (L - u)))
        simpa using this
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [Ioo_mem_nhdsLT (show L - u - ρ / 2 < L - u by linarith)] with x hx
      have hxb : ((x + u : ℝ) : ℂ) ∈ ball (L : ℂ) (ρ / 2) := by
        rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
        constructor <;> linarith [hx.1, hx.2]
      have hg₁ : Tendsto (fun z => c.1 z + M.shift) (𝓝[H] (L : ℂ)) (𝓝 ((m : ℂ) + M.shift)) :=
        hm.add_const _
      have hg₂ : Tendsto (fun z => c.1 z + M.shift) (𝓝[H] ((x + u : ℝ) : ℂ))
          (𝓝 ((e₀ (x + u) : ℂ) + M.shift)) := (he₀x (x + u) (by linarith [hx.2])).add_const _
      have hle := norm_sub_le_of_tendsto_mapOut M.isHull M.mapOut hd (mem_ball_self (half_pos hρ)) hxb hg₁ hg₂
      have hn : ‖(e₀ (x + u) : ℂ) + M.shift - ((m : ℂ) + M.shift)‖ = ‖e₀ (x + u) - m‖ := by
        rw [add_sub_add_right_eq_sub, ← Complex.ofReal_sub, Complex.norm_real]
      rw [hn] at hle
      exact hle
  · -- clause 3
    have h1 := tendsto_runChart_cobounded spec D hreg n hnot
    rw [← hAf] at h1
    have hmaps : MapsTo (fun z : ℂ => z + u) (H \ fillH ((fun z => z - (u : ℂ)) '' A)) (H \ fillH A) := by
      intro z hz
      refine ⟨(add_real_mem_H_iff u).2 hz.1, fun hzA => hz.2 ?_⟩
      rw [fillH_image_sub_real]
      exact ⟨z + u, hzA, by simp⟩
    have h2 : Tendsto (fun z : ℂ => z + u) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fillH ((fun z => z - (u : ℂ)) '' A)))
        (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fillH A)) :=
      tendsto_inf.2 ⟨tendsto_add_cobounded _ inf_le_left,
        (tendsto_principal_principal.2 hmaps).mono_left inf_le_right⟩
    have h3 := tendsto_add_cobounded (-(m : ℂ)) le_rfl
    exact (h3.comp (h1.comp h2)).congr fun z => by simp [shiftChart, sub_eq_add_neg, hcdef]
  · -- clause 4
    intro x hx
    have h0 := tendsto_add_real_nhdsWithin_H (x : ℂ) u
    have h2 : ((x : ℂ) + u) = ((x + u : ℝ) : ℂ) := by push_cast; ring
    rw [h2] at h0
    exact (tendsto_runChart_lift_zero spec D hreg n hnot hAc hAf (x := x + u)
      (fun y hy => by linarith [hLA y hy])).comp h0

end Run

end InteractingSLE.Theorem14.SB.Lw
