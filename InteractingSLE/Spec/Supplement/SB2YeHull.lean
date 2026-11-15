/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntCanonModelRun
import InteractingSLE.Spec.Sec7.ReverseArcLift
import InteractingSLE.Spec.Sec7.Aux57
import InteractingSLE.Spec.Sec5.CrossRestartTrace
import InteractingSLE.Spec.Supplement.SB2XdChart
import InteractingSLE.Spec.Supplement.SB2MoNorm
import InteractingSLE.Spec.Supplement.SB2GLift
import InteractingSLE.Spec.Supplement.SB2NqChain

/-!
# The canonical chart read in a stage chart is a hull chart of the pulled-back retained set

Packet PROVE-T14-SB2LIFT (round 32; decisions D38/D39, `IsStageS2`). Let `c` be a domain chart of `ℍ ∖ Y` whose forward
map is, up to a real shift `s₀`, a mapping-out function of the hull `Y`, with lift the imaginary part of a canonical
logarithm (B's stage chart: `WalkIntCanon.HullModel` with `IsNormalized`), and let `Φ = Mo.hullChart B x₀` be the
canonical chart of a hull `B ⊇ Y` (the retained union). The chart `Ψ = pullChart c Φ` (`Φ` read in `c`'s coordinates):

* **`pullChart_hull`**: `D = pullHull c B = {z ∈ ℍ | c⁻¹ z ∈ B}` is a hull, `Ψ` is a domain chart of `ℍ ∖ D`, and
  `Ψ.1 = g_D + (s₀ − x₀)` with `g_D` a mapping-out function of `D` and `Ψ`'s lift the imaginary part of a canonical
  logarithm of `g_D′` (Aux. lemma 57's composition `IsCanonicalDerivLog.comp`);
* **`liftRealOn_of_hull`**: such a chart has `LiftRealOn` (the lift vanishes at every untouched real point);
* **`isRightEntryChart_of_hull`**: such a chart is a right entry chart of `D` at `0`, given that `(0, ∞)` is untouched
  and the real boundary values of `Ψ.1` on `(0, ∞)` tend to `0` at `0⁺` (the normalization of the offset).
Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Sx

open Restart

/-- **The retained hull read in the chart `c`**: the points of `ℍ` that `c`'s inverse sends into `B`. -/
def pullHull (c : Chart) (B : Set ℂ) : Set ℂ := {z ∈ H | c.2.1 z ∈ B}

section Hull

variable {c : Chart} {Y B : Set ℂ} {s₀ x₀ : ℝ}

/-- The pulled-back hull is the translate of the image hull. -/
theorem pullHull_eq (hcD : IsDomainChart (H \ Y) c) (hBH : B ⊆ H) :
    pullHull c B = (fun w => w + ((-s₀ : ℝ) : ℂ)) '' ((fun z => c.1 z + (s₀ : ℂ)) '' (B \ Y)) := by
  ext z
  constructor
  · rintro ⟨hz, hzB⟩
    have hw := hcD.inv_mem hz
    refine ⟨c.1 (c.2.1 z) + (s₀ : ℂ), ⟨c.2.1 z, ⟨hzB, hw.2⟩, rfl⟩, ?_⟩
    rw [hcD.fwd_inv hz]
    push_cast
    ring
  · rintro ⟨_, ⟨w, ⟨hwB, hwY⟩, rfl⟩, rfl⟩
    have hwD : w ∈ H \ Y := ⟨hBH hwB, hwY⟩
    have e : c.1 w + (s₀ : ℂ) + ((-s₀ : ℝ) : ℂ) = c.1 w := by push_cast; ring
    show c.1 w + (s₀ : ℂ) + ((-s₀ : ℝ) : ℂ) ∈ pullHull c B
    rw [e]
    exact ⟨hcD.fwd_mem hwD, by rw [hcD.inv_fwd hwD]; exact hwB⟩

/-- Off the pulled-back hull, the inverse lands off `B`. -/
theorem inv_mem_diff_of_notMem (hcD : IsDomainChart (H \ Y) c) {w : ℂ} (hw : w ∈ H \ pullHull c B) :
    c.2.1 w ∈ H \ B :=
  ⟨(hcD.inv_mem hw.1).1, fun hB => hw.2 ⟨hw.1, hB⟩⟩

/-- The chart's forward image of `ℍ ∖ B` is the complement of the pulled-back hull. -/
theorem image_fwd_diff (hcD : IsDomainChart (H \ Y) c) (hYB : Y ⊆ B) :
    c.1 '' (H \ B) = H \ pullHull c B := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwD : w ∈ H \ Y := ⟨hw.1, fun h => hw.2 (hYB h)⟩
    refine ⟨hcD.fwd_mem hwD, fun h => hw.2 ?_⟩
    have := h.2
    rwa [hcD.inv_fwd hwD] at this
  · intro hz
    exact ⟨c.2.1 z, inv_mem_diff_of_notMem hcD hz, hcD.fwd_inv hz.1⟩

/-- **The canonical chart of `B` read in `c` is a hull chart of the pulled-back hull** (Aux. lemma 57's
composition). -/
theorem pullChart_hull (hcD : IsDomainChart (H \ Y) c) (hY : IsHPHull Y) (hB : IsHPHull B) (hYB : Y ⊆ B)
    (hg₀ : IsMapOut Y (fun z => c.1 z + (s₀ : ℂ))) {LY : ℂ → ℂ}
    (hLY : IsCanonicalDerivLog Y (fun z => c.1 z + (s₀ : ℂ)) LY) (hlift : EqOn c.2.2 (fun z => (LY z).im) (H \ Y)) :
    IsHPHull (pullHull c B) ∧ IsDomainChart (H \ pullHull c B) (Mn.pullChart c (Mo.hullChart B x₀)) ∧
      ∃ gD LD : ℂ → ℂ, IsMapOut (pullHull c B) gD ∧ IsCanonicalDerivLog (pullHull c B) gD LD ∧
        EqOn (Mn.pullChart c (Mo.hullChart B x₀)).1 (fun w => gD w + ((s₀ - x₀ : ℝ) : ℂ)) (H \ pullHull c B) ∧
        EqOn (Mn.pullChart c (Mo.hullChart B x₀)).2.2 (fun w => (LD w).im) (H \ pullHull c B) := by
  set g₀ : ℂ → ℂ := fun z => c.1 z + (s₀ : ℂ) with hg₀def
  set C := g₀ '' (B \ Y) with hCdef
  have hC : IsHPHull C := hg₀.isHPHull_image hY hB hYB
  set gC := ConformalImage.mapOut C with hgCdef
  have hgC : IsMapOut C gC := ConformalImage.isMapOut_mapOut hC
  obtain ⟨LC, hLC⟩ := exists_isCanonicalDerivLog hC hgC
  have hcomp := IsCanonicalDerivLog.comp hY hB hYB hg₀ hgC hLY hLC
  have hgB' : IsMapOut B (gC ∘ g₀) := hg₀.comp hY hB hYB hgC
  have hgB : IsMapOut B (ConformalImage.mapOut B) := ConformalImage.isMapOut_mapOut hB
  have heqg : EqOn (ConformalImage.mapOut B) (gC ∘ g₀) (H \ B) := IsMapOut.eqOn hB hgB hgB'
  have hLB' : IsCanonicalDerivLog B (gC ∘ g₀) (canonDerivLog B) :=
    (isCanonicalDerivLog_canonDerivLog hB).congr hB heqg
  have heqL : EqOn (canonDerivLog B) (fun z => LC (g₀ z) + LY z) (H \ B) :=
    IsCanonicalDerivLog.eqOn hLB' hcomp hB hgB'
  have hDeq : pullHull c B = (fun w => w + ((-s₀ : ℝ) : ℂ)) '' C := pullHull_eq hcD hB.1
  have hD : IsHPHull (pullHull c B) := by rw [hDeq]; exact Sec5.CrossRestart.isHPHull_image_add hC (-s₀)
  have hgD := Sec7.ReverseArc.isMapOut_translate hgC (-s₀)
  have hLD := Sec7.ReverseArc.isCanonicalDerivLog_translate hLC (-s₀)
  rw [← hDeq] at hgD hLD
  have hsub : H \ B ⊆ H \ Y := fun z hz => ⟨hz.1, fun h => hz.2 (hYB h)⟩
  have hΨ := Mn.isDomainChart_pullback hcD (Mo.isDomainChart_hullChart hB x₀) hsub
  rw [image_fwd_diff hcD hYB] at hΨ
  have hshift : ∀ w : ℂ, w - ((-s₀ : ℝ) : ℂ) = w + (s₀ : ℂ) := fun w => by push_cast; ring
  refine ⟨hD, hΨ, _, _, hgD, hLD, fun w hw => ?_, fun w hw => ?_⟩
  · have hz := inv_mem_diff_of_notMem hcD hw
    have e1 : g₀ (c.2.1 w) = w + (s₀ : ℂ) := by
      simp only [hg₀def]; rw [hcD.fwd_inv hw.1]
    show ConformalImage.mapOut B (c.2.1 w) - (x₀ : ℂ) = gC (w - ((-s₀ : ℝ) : ℂ)) + ((-s₀ : ℝ) : ℂ) +
      ((s₀ - x₀ : ℝ) : ℂ)
    rw [heqg hz, Function.comp_apply, e1, hshift]
    push_cast
    ring
  · have hz := inv_mem_diff_of_notMem hcD hw
    have e1 : g₀ (c.2.1 w) = w + (s₀ : ℂ) := by
      simp only [hg₀def]; rw [hcD.fwd_inv hw.1]
    show (canonDerivLog B (c.2.1 w)).im - c.2.2 (c.2.1 w) = (LC (w - ((-s₀ : ℝ) : ℂ))).im
    rw [heqL hz, hlift (hcD.inv_mem hw.1)]
    beta_reduce
    rw [e1, hshift, Complex.add_im]
    ring

end Hull

section Entry

variable {D : Set ℂ} {Ψ : Chart} {gD LD : ℂ → ℂ} {a : ℝ}

/-- **A chart with a canonical lift has `LiftRealOn`.** -/
theorem liftRealOn_of_hull (hD : IsHPHull D) (hgD : IsMapOut D gD) (hLD : IsCanonicalDerivLog D gD LD)
    (hdom : (Ψ.dom : Set ℂ) = H \ D) (hl : EqOn Ψ.2.2 (fun w => (LD w).im) (H \ D)) : FinRel.LiftRealOn Ψ := by
  rintro y ⟨ε, hε, hsub⟩
  rw [hdom] at hsub ⊢
  have hdisj : Disjoint (ball (y : ℂ) ε) D :=
    disjoint_left.2 fun z hz hzD => (hsub ⟨hz, hD.1 hzD⟩).2 hzD
  have h := IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero hD hLD hgD hε hdisj
  refine (h.mono_left (nhdsWithin_mono _ sdiff_subset)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw using (hl hw).symm

/-- At an untouched real point the forward map has a real limit along `ℍ`. -/
theorem exists_tendsto_fwd_of_hull (hD : IsHPHull D) (hgD : IsMapOut D gD)
    (hfwd : EqOn Ψ.1 (fun w => gD w + (a : ℂ)) (H \ D)) {x : ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hd : Disjoint (ball (x : ℂ) ρ) D) : ∃ L : ℝ, Tendsto Ψ.1 (𝓝[H] (x : ℂ)) (𝓝 (L : ℂ)) := by
  obtain ⟨L, hL0, hL⟩ := IsMapOut.exists_tendsto_of_disjoint hD hgD hd (mem_ball_self (half_pos hρ)) (by simp)
  have hball : 𝓝[ball (x : ℂ) (ρ / 2) ∩ H] (x : ℂ) = 𝓝[H] (x : ℂ) := by
    rw [inter_comm]; exact nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (half_pos hρ)))
  rw [hball] at hL
  refine ⟨L.re + a, ?_⟩
  have hLe : (((L.re + a : ℝ)) : ℂ) = L + (a : ℂ) := by
    apply Complex.ext <;> simp [hL0]
  rw [hLe]
  refine (hL.add tendsto_const_nhds).congr' ?_
  filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds (x : ℂ) hρ)] with w hw
  exact (hfwd ⟨hw.1, fun hwD => disjoint_left.1 hd hw.2 hwD⟩).symm

/-- The forward map of a chart within bounded distance of a mapping-out function tends to `∞` at `∞`. -/
theorem tendsto_cobounded_of_hull (hD : IsHPHull D) (hgD : IsMapOut D gD)
    (hfwd : EqOn Ψ.1 (fun w => gD w + (a : ℂ)) (H \ D)) :
    Tendsto Ψ.1 (cobounded ℂ ⊓ 𝓟 (H \ D)) (cobounded ℂ) := by
  obtain ⟨M, hM⟩ := hgD.exists_norm_sub_le hD
  refine tendsto_norm_atTop_iff_cobounded.1 ?_
  refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-(M + |a|))
    (tendsto_norm_cobounded_atTop.mono_left inf_le_left))
  filter_upwards [mem_inf_of_right (mem_principal_self (H \ D))] with z hz
  have h1 := hM z hz
  rw [hfwd hz]
  have e : z = (gD z + (a : ℂ)) - (gD z - z) - (a : ℂ) := by ring
  have h3 : ‖z‖ ≤ ‖gD z + (a : ℂ)‖ + ‖gD z - z‖ + ‖(a : ℂ)‖ := by
    calc ‖z‖ = ‖(gD z + (a : ℂ)) - (gD z - z) - (a : ℂ)‖ := by rw [← e]
      _ ≤ ‖(gD z + (a : ℂ)) - (gD z - z)‖ + ‖(a : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖gD z + (a : ℂ)‖ + ‖gD z - z‖ + ‖(a : ℂ)‖ := by gcongr; exact norm_sub_le _ _
  rw [Complex.norm_real, Real.norm_eq_abs] at h3
  linarith

/-- **A hull chart of `D` normalized at `0` is a right entry chart of `D` at `0`**: `(0, ∞)` untouched by `D`, and the
forward map's real boundary values on `(0, ∞)` tending to `0` at `0⁺`. -/
theorem isRightEntryChart_of_hull (hD : IsHPHull D) (hΨD : IsDomainChart (H \ D) Ψ) (hgD : IsMapOut D gD)
    (hLD : IsCanonicalDerivLog D gD LD) (hfwd : EqOn Ψ.1 (fun w => gD w + (a : ℂ)) (H \ D))
    (hl : EqOn Ψ.2.2 (fun w => (LD w).im) (H \ D))
    (hfree : ∀ x : ℝ, 0 < x → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) D)
    (hnorm : ∃ e : ℝ → ℝ, (∀ x : ℝ, 0 < x → Tendsto Ψ.1 (𝓝[H] (x : ℂ)) (𝓝 (e x : ℂ))) ∧
      Tendsto e (𝓝[>] 0) (𝓝 0)) :
    IsRightEntryChart D 0 Ψ := by
  have hDc : closure D ∩ H ⊆ D := by
    rintro z ⟨hz, hzH⟩
    by_contra hzD
    have hU : IsOpen (H \ D) := hD.2.2.1
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z ⟨hzH, hzD⟩
    obtain ⟨w, hwD, hw⟩ := Metric.mem_closure_iff.1 hz ε hε
    exact (hεU (by rw [mem_ball, dist_comm]; exact hw)).2 hwD
  have hfD : fillH D = D := Nq.fillH_eq_self_of_isDomainChart hD.1 hD.2.1 hDc hΨD
  obtain ⟨e, he, he0⟩ := hnorm
  refine ⟨by rw [hfD]; exact hΨD, ⟨e, fun x hx => he x hx, he0⟩,
    by rw [hfD]; exact tendsto_cobounded_of_hull hD hgD hfwd, fun x hx => ?_⟩
  · obtain ⟨ρ, hρ, hd⟩ := hfree x hx
    have h := IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero hD hLD hgD hρ hd
    refine h.congr' ?_
    filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds (x : ℂ) hρ)] with w hw
    exact (hl ⟨hw.1, fun hwD => disjoint_left.1 hd hw.2 hwD⟩).symm

end Entry

end InteractingSLE.Theorem14.SB.Sx
