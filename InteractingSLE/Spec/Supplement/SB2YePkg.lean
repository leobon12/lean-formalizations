/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YeHull
import InteractingSLE.Spec.Supplement.SB2YeFill
import InteractingSLE.Spec.Supplement.SB4RChart
import InteractingSLE.Spec.Supplement.SBS3GeoChart

/-!
# The chart package of `IsStageS2`

Packet PROVE-T14-SB2LIFT (round 32; decisions D38/D39). **`stageChartPkg`**: the retained path, the retained set, the
relative chart and its boundary map in the form of `Om.IsStageS2` (SB2(1)'s reflected orientation), with the
relative chart `cr = reflChart (pullChart c Φ)` (the canonical chart `Φ = Mo.hullChart B x₀` read in the stage chart
`c` and reflected), from:

* the stage chart `c`: a domain chart of `ℍ ∖ Y` whose forward map is, up to the shift `s₀`, a mapping-out function of
  the hull `Y`, with canonical lift (`WalkIntCanon.HullModel` with `IsNormalized`), and boundary limits `gc` of its
  inverse on `ℍ̄` within bounded distance of the identity;
* the canonical chart's boundary limits `gΦ` on `ℍ̄` with finite fibres (CORNER's canonical package);
* the untouched line `(0, ∞)` in stage coordinates and the offset normalization (the real boundary values of `Ψ.1`
  on `(0, ∞)` tend to `0` at `0⁺`).

The retained path is the reflected boundary arc `q(s) = ρ(gΨ(−K s))` from `0` (`SB2YeFill`), the left entry and
`LiftRealOn` come from the hull-chart identification (`SB2YeHull`), the boundary map from clustering (`SB2YeExt`).
Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Sx

open Restart Supp9B

/-- **`LiftRealOn` survives the reflection.** -/
theorem liftRealOn_reflChart {Ψ : Chart} (hΨ : Ψ.IsConformal) (h : FinRel.LiftRealOn Ψ) :
    FinRel.LiftRealOn (Lf.reflChart Ψ) := by
  have hdom : ((Lf.reflChart Ψ).dom : Set ℂ) = Supp9B.refl '' (Ψ.dom : Set ℂ) := by
    rw [(Lf.isConformal_reflChart hΨ).coe_dom, hΨ.coe_dom]
    ext z
    simp only [mem_image, Lf.reflChart_inv]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨Ψ.2.1 (Supp9B.refl w), ⟨Supp9B.refl w, Lf.refl_mem_H hw, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨Supp9B.refl w, Lf.refl_mem_H hw, by rw [refl_refl]⟩
  rintro y ⟨ε, hε, hsub⟩
  rw [hdom] at hsub ⊢
  have hsub' : ball ((-y : ℝ) : ℂ) ε ∩ H ⊆ Ψ.dom := by
    rintro z ⟨hz, hzH⟩
    have hz' : Supp9B.refl z ∈ ball (y : ℂ) ε ∩ H := by
      refine ⟨?_, Lf.refl_mem_H hzH⟩
      rw [mem_ball] at hz ⊢
      have e : Supp9B.refl z - (y : ℂ) = Supp9B.refl (z - ((-y : ℝ) : ℂ)) := by
        simp only [Supp9B.refl, map_sub, Complex.conj_ofReal]; push_cast; ring
      rw [dist_eq_norm, e, Lf.norm_refl, ← dist_eq_norm]
      exact hz
    obtain ⟨w, hw, hwz⟩ := hsub hz'
    rw [← refl_refl z, ← hwz, refl_refl]
    exact hw
  have hlim := h (-y) ⟨ε, hε, hsub'⟩
  have hmap : Tendsto Supp9B.refl (𝓝[Supp9B.refl '' (Ψ.dom : Set ℂ)] (y : ℂ)) (𝓝[(Ψ.dom : Set ℂ)] ((-y : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => ?_⟩
    · have := (continuous_refl.tendsto (y : ℂ)).mono_left (nhdsWithin_le_nhds (s := Supp9B.refl '' (Ψ.dom : Set ℂ)))
      rwa [Lf.refl_ofReal] at this
    · obtain ⟨w, hw, rfl⟩ := hz
      rw [refl_refl]; exact hw
  have h2 : Tendsto (fun x => -Ψ.2.2 (Supp9B.refl x)) (𝓝[Supp9B.refl '' (Ψ.dom : Set ℂ)] (y : ℂ)) (𝓝 0) := by
    simpa using (hlim.comp hmap).neg
  exact h2

variable {c : Chart} {Y B : Set ℂ} {s₀ x₀ : ℝ} {gc gΦ : ℂ → ℂ} {Cc : ℝ}

/-- **The chart package of `IsStageS2`** (deterministic, one sample). -/
theorem stageChartPkg (hcD : IsDomainChart (H \ Y) c) (hY : IsHPHull Y) (hB : IsHPHull B) (hYB : Y ⊆ B)
    (hg₀ : IsMapOut Y (fun z => c.1 z + (s₀ : ℂ))) {LY : ℂ → ℂ}
    (hLY : IsCanonicalDerivLog Y (fun z => c.1 z + (s₀ : ℂ)) LY) (hlift : EqOn c.2.2 (fun z => (LY z).im) (H \ Y))
    (hgc : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (gc q))) (hCc : ∀ q ∈ Hbar, ‖gc q - q‖ ≤ Cc)
    (hgΦ : ∀ p ∈ Hbar, Tendsto (Mo.hullChart B x₀).2.1 (𝓝[H] p) (𝓝 (gΦ p)))
    (hgΦf : ∀ z, (gΦ ⁻¹' {z} ∩ {w : ℂ | 0 ≤ w.im}).Finite)
    (hfree : ∀ x : ℝ, 0 < x → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (pullHull c B))
    (hnorm : ∃ e : ℝ → ℝ, (∀ x : ℝ, 0 < x → Tendsto (Mn.pullChart c (Mo.hullChart B x₀)).1 (𝓝[H] (x : ℂ))
      (𝓝 (e x : ℂ))) ∧ Tendsto e (𝓝[>] 0) (𝓝 0)) :
    ∃ (q : ℝ → ℂ) (R : Set ℂ) (g : ℂ → ℂ),
      ContinuousOn q (Icc 0 1) ∧ q 0 = 0 ∧ (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (q s).im) ∧
      (∀ y : ℝ, (y : ℂ) ∈ q '' Icc 0 1 → 0 ≤ y) ∧ fillH R = fillH (q '' Icc 0 1) ∧
      IsLeftEntryChart R 0 (Lf.reflChart (Mn.pullChart c (Mo.hullChart B x₀))) ∧
      ContinuousOn g {z | 0 ≤ z.im} ∧ EqOn g (Lf.reflChart (Mn.pullChart c (Mo.hullChart B x₀))).2.1 H ∧
      (∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) ∧
      FinRel.LiftRealOn (Lf.reflChart (Mn.pullChart c (Mo.hullChart B x₀))) ∧
      (∀ z ∈ H, z ∈ LP.reflectC '' fillH R ↔ c.2.1 z ∈ B) ∧
      (∀ y ∈ H, (Mo.hullChart B x₀).2.1 y =
        c.2.1 (LP.reflectC ((Lf.reflChart (Mn.pullChart c (Mo.hullChart B x₀))).2.1 (LP.reflectC y)))) ∧
      (∀ y ∈ H, (Mo.hullChart B x₀).2.2 ((Mo.hullChart B x₀).2.1 y) =
        -(Lf.reflChart (Mn.pullChart c (Mo.hullChart B x₀))).2.2
          ((Lf.reflChart (Mn.pullChart c (Mo.hullChart B x₀))).2.1 (LP.reflectC y)) +
          c.2.2 ((Mo.hullChart B x₀).2.1 y)) ∧
      (∀ p ∈ Hbar, Tendsto (Lf.reflChart (Mn.pullChart c (Mo.hullChart B x₀))).2.1 (𝓝[H] p) (𝓝 (g p))) ∧
      (∀ p ∈ Hbar, g p ∈ Hbar) ∧ (∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1, q s = g ((K * s : ℝ) : ℂ)) ∧
      (∀ y : ℝ, g y ∈ H → g y ∈ fillH R) ∧ ∃ C : ℝ, ∀ p ∈ Hbar, ‖g p - p‖ ≤ C := by
  set Φ := Mo.hullChart B x₀ with hΦdef
  set Ψ := Mn.pullChart c Φ with hΨdef
  set D := pullHull c B with hDdef
  obtain ⟨hD, hΨD, gD, LD, hgD, hLD, hfwd, hl⟩ :=
    pullChart_hull (x₀ := x₀) hcD hY hB hYB hg₀ hLY hlift
  -- the inverse of `Ψ` and its boundary extension by clustering
  have hΦD := Mo.isDomainChart_hullChart hB x₀
  obtain ⟨MΦ, hMΦ⟩ := Mo.hullChart_inv_bounded hB x₀
  have hcgH : EqOn gc c.2.1 H := fun y hy => by
    have hyH : y ∈ Hbar := QuantumZipper.H_subset_Hbar hy
    have : (𝓝[H] y).NeBot := GW1P.neBot_nhdsWithin_H hyH
    exact tendsto_nhds_unique (hgc y hyH) (hcD.1.1.continuousOn y hy |>.tendsto.mono_left le_rfl)
  have hfwdb : ∀ z ∈ H \ Y, ‖c.1 z - z‖ ≤ Cc := fun z hz => by
    obtain ⟨w, hw, rfl⟩ := hcD.image_eq.symm ▸ hz
    have h1 := hCc w (QuantumZipper.H_subset_Hbar hw)
    rw [hcgH hw] at h1
    rw [hcD.fwd_inv hw, norm_sub_rev]
    exact h1
  have hsubYB : ∀ y ∈ H, Φ.2.1 y ∈ H \ Y := fun y hy =>
    have h := hΦD.inv_mem hy
    ⟨h.1, fun hYy => h.2 (hYB hYy)⟩
  have hGc : ContinuousOn Ψ.2.1 H :=
    hcD.differentiableOn_fwd.continuousOn.comp hΦD.1.1.continuousOn fun y hy => hsubYB y hy
  have hGH : ∀ y ∈ H, Ψ.2.1 y ∈ H := fun y hy => hcD.fwd_mem (hsubYB y hy)
  have hGb : ∀ y ∈ H, ‖Ψ.2.1 y - y‖ ≤ Cc + MΦ := fun y hy => by
    have h1 := hfwdb _ (hsubYB y hy)
    have h2 := hMΦ y hy
    calc ‖Ψ.2.1 y - y‖ = ‖(c.1 (Φ.2.1 y) - Φ.2.1 y) + (Φ.2.1 y - y)‖ := by
          congr 1; show c.1 (Φ.2.1 y) - y = _; ring
      _ ≤ ‖c.1 (Φ.2.1 y) - Φ.2.1 y‖ + ‖Φ.2.1 y - y‖ := norm_add_le _ _
      _ ≤ Cc + MΦ := add_le_add h1 h2
  have hcomp : ∀ p ∈ Hbar, Tendsto (fun y => c.2.1 (Ψ.2.1 y)) (𝓝[H] p) (𝓝 (gΦ p)) := fun p hp =>
    (hgΦ p hp).congr' (eventually_nhdsWithin_of_forall fun y hy => (hcD.inv_fwd (hsubYB y hy)).symm)
  obtain ⟨gΨ, hgΨt, hgΨcomp, hgΨc, hgΨH, hgΨm, hgΨb⟩ :=
    exists_bdryExt_of_cluster hcD.1 hgc hGc hGH hGb hcomp
  have hgΨf := finite_fibre_of_comp hgΨcomp hgΦf
  -- the right entry chart and the free line
  have hRE := isRightEntryChart_of_hull hD hΨD hgD hLD hfwd hl hfree hnorm
  obtain ⟨-, ⟨e, he, he0⟩, -, -⟩ := hRE
  have hpos : ∀ y : ℝ, 0 < y → (gΨ y).im = 0 := fun y hy => by
    obtain ⟨x, -, hx⟩ := g_pos_of_pos hΨD he hfree hgΨt he0 hgΨc hgΨb hy
    rw [hx]; simp
  have hg0 : gΨ 0 = 0 := g_zero hΨD he hfree hgΨt he0 hgΨc
  -- the boundary arc
  obtain ⟨MD, hMD⟩ := hD.2.1.exists_norm_le
  set K := |MD| + |Cc + MΦ| + 1 with hKdef
  have hK0 : 0 < K := by positivity
  have hK : ∀ z ∈ D, ‖z‖ + (Cc + MΦ) ≤ K := fun z hz => by
    have := hMD z hz; rw [hKdef]; linarith [le_abs_self MD, le_abs_self (Cc + MΦ)]
  have hfill := fillH_arc_eq hΨD hgΨt hgΨb hgΨc hgΨH hD.1 hD.2.1 hpos hK
  have hDc : closure D ∩ H ⊆ D := by
    rintro z ⟨hz, hzH⟩
    by_contra hzD
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hD.2.2.1 z ⟨hzH, hzD⟩
    obtain ⟨w, hwD, hw⟩ := Metric.mem_closure_iff.1 hz ε hε
    exact (hεU (by rw [mem_ball, dist_comm]; exact hw)).2 hwD
  have hfD : fillH D = D := Nq.fillH_eq_self_of_isDomainChart hD.1 hD.2.1 hDc hΨD
  set q : ℝ → ℂ := fun s => Supp9B.refl (gΨ ((-(K * s) : ℝ) : ℂ)) with hqdef
  have hqimg : q '' Icc 0 1 = Supp9B.refl '' ((fun t : ℝ => gΨ t) '' Icc (-K) 0) := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨gΨ ((-(K * s) : ℝ) : ℂ), ⟨-(K * s), ⟨by nlinarith [hs.2], by nlinarith [hs.1]⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨-t / K, ⟨div_nonneg (by linarith [ht.2]) hK0.le, by rw [div_le_one hK0]; linarith [ht.1]⟩, ?_⟩
      show Supp9B.refl (gΨ ((-(K * (-t / K)) : ℝ) : ℂ)) = Supp9B.refl (gΨ t)
      rw [show -(K * (-t / K)) = t by field_simp]
  have hreflfill : ∀ X : Set ℂ, fillH (Supp9B.refl '' X) = Supp9B.refl '' fillH X := fun X => by
    rw [Lf.refl_eq_reflectC]; exact LP.fillH_image_reflectC X
  have hmapsH : ∀ z : ℂ, 0 ≤ z.im → 0 ≤ (Supp9B.refl z).im := fun z hz => by rw [refl_im]; exact hz
  refine ⟨q, Supp9B.refl '' D, fun z => Supp9B.refl (gΨ (Supp9B.refl z)), ?_, ?_, fun s _ => ?_, ?_, ?_, ?_, ?_,
    fun z hz => ?_, ?_, ?_, fun z hz => ?_, fun y hy => ?_, fun y hy => ?_, fun p hp => ?_, fun p hp => ?_,
    ⟨K, hK0.le, fun s _ => ?_⟩, fun y hy => ?_, ⟨Cc + MΦ, fun p hp => ?_⟩⟩
  · -- the retained path is continuous
    refine continuous_refl.comp_continuousOn (hgΨc.comp ?_ fun s _ => ?_)
    · exact (Complex.continuous_ofReal.comp ((continuous_const.mul continuous_id).neg)).continuousOn
    · show (0 : ℝ) ≤ ((-(K * s) : ℝ) : ℂ).im
      simp
  · -- from `0`
    show Supp9B.refl (gΨ ((-(K * 0) : ℝ) : ℂ)) = 0
    rw [mul_zero, neg_zero, Complex.ofReal_zero, hg0]
    simp [Supp9B.refl]
  · -- in the closed upper half-plane
    rw [refl_im]; exact hgΨm _ (show (0 : ℝ) ≤ ((-(K * s) : ℝ) : ℂ).im by simp)
  · -- real points are nonnegative
    rintro y ⟨s, hs, hsy⟩
    by_contra hy
    push Not at hy
    have h1 : gΨ ((-(K * s) : ℝ) : ℂ) = ((-y : ℝ) : ℂ) := by
      have h0 : Supp9B.refl (Supp9B.refl (gΨ ((-(K * s) : ℝ) : ℂ))) = Supp9B.refl (y : ℂ) :=
        congrArg Supp9B.refl hsy
      rw [refl_refl] at h0
      rw [h0, Lf.refl_ofReal]
    exact g_ne_pos_of_nonpos hΨD he hfree hgΨt he0 hgΨc hgΨb (by nlinarith [hs.1]) (by linarith) h1
  · -- the fillings agree
    rw [hqimg, hreflfill, hreflfill, hfill, hfD]
  · -- the left entry chart
    have h := Lf.isLeftEntryChart_reflChart (isRightEntryChart_of_hull hD hΨD hgD hLD hfwd hl hfree hnorm)
    rwa [neg_zero] at h
  · -- the boundary map is continuous
    refine continuous_refl.comp_continuousOn (hgΨc.comp continuous_refl.continuousOn fun z hz => ?_)
    exact hmapsH z hz
  · -- it extends the relative inverse
    show Supp9B.refl (gΨ (Supp9B.refl z)) = Supp9B.refl (Ψ.2.1 (Supp9B.refl z))
    rw [hgΨH (Lf.refl_mem_H hz)]
  · -- finite fibres
    intro z
    refine ((hgΨf (Supp9B.refl z)).image Supp9B.refl).subset fun w hw =>
      ⟨Supp9B.refl w, ⟨?_, hmapsH w hw.2⟩, refl_refl w⟩
    have h1 : Supp9B.refl (gΨ (Supp9B.refl w)) = z := hw.1
    show gΨ (Supp9B.refl w) = Supp9B.refl z
    rw [← h1, refl_refl]
  · -- `LiftRealOn`
    exact liftRealOn_reflChart hΨD.1 (liftRealOn_of_hull hD hgD hLD hΨD.coe_dom hl)
  · -- the retained set in stage coordinates
    rw [hreflfill, hfD, ← Lf.refl_eq_reflectC, image_image]
    simp only [refl_refl, image_id']
    exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩
  · -- the inverse identification
    show Φ.2.1 y = c.2.1 (Supp9B.refl (Supp9B.refl (Ψ.2.1 (Supp9B.refl (Supp9B.refl y)))))
    rw [refl_refl, refl_refl]
    exact (hcD.inv_fwd (hsubYB y hy)).symm
  · -- the lift identification
    show Φ.2.2 (Φ.2.1 y) = -(-Ψ.2.2 (Supp9B.refl (Supp9B.refl (Ψ.2.1 (Supp9B.refl (Supp9B.refl y)))))) + c.2.2 (Φ.2.1 y)
    rw [refl_refl, refl_refl, neg_neg]
    show Φ.2.2 (Φ.2.1 y) = Φ.2.2 (c.2.1 (c.1 (Φ.2.1 y))) - c.2.2 (c.2.1 (c.1 (Φ.2.1 y))) + c.2.2 (Φ.2.1 y)
    rw [hcD.inv_fwd (hsubYB y hy)]
    ring
  · -- boundary limits of the relative inverse
    have hrp : Supp9B.refl p ∈ Hbar := hmapsH p hp
    have h1 := (hgΨt (Supp9B.refl p) hrp).comp (Lf.tendsto_refl_nhdsWithin_H p)
    exact (continuous_refl.tendsto _).comp h1
  · exact hmapsH _ (hgΨm _ (hmapsH p hp))
  · -- the retained path reads `g` on the nonnegative axis
    show Supp9B.refl (gΨ ((-(K * s) : ℝ) : ℂ)) = Supp9B.refl (gΨ (Supp9B.refl ((K * s : ℝ) : ℂ)))
    rw [Lf.refl_ofReal]
  · -- real points of `g` in `ℍ` lie in the retained set
    have hy' : gΨ (Supp9B.refl (y : ℂ)) ∈ H := S3.Geo.refl_mem_H_iff.1 hy
    rw [Lf.refl_ofReal] at hy'
    have hD' := mem_of_real hΨD hgΨt hy'
    rw [hreflfill, hfD]
    show Supp9B.refl (gΨ (Supp9B.refl (y : ℂ))) ∈ Supp9B.refl '' D
    rw [Lf.refl_ofReal]
    exact ⟨_, hD', rfl⟩
  · -- bounded displacement
    have h1 := hgΨb (Supp9B.refl p) (hmapsH p hp)
    have e : Supp9B.refl (gΨ (Supp9B.refl p)) - p = Supp9B.refl (gΨ (Supp9B.refl p) - Supp9B.refl p) := by
      simp only [Supp9B.refl, map_sub, map_neg, Complex.conj_conj]; ring
    show ‖Supp9B.refl (gΨ (Supp9B.refl p)) - p‖ ≤ Cc + MΦ
    rw [e, Lf.norm_refl]
    exact h1

end InteractingSLE.Theorem14.SB.Sx
