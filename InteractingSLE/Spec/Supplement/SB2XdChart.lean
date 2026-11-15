/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XcIface
import InteractingSLE.Spec.Supplement.SB2LkDom
import InteractingSLE.Spec.Jordan.ChartExists

/-!
# (G1) for the corrected per-stage correspondence: the relative chart in B's stage coordinates is a domain chart

Packet PROVE-T14-SB2LIFT (round 25; item (G1) of §R24.2). `Mn.stageRelChart cℓ c c₁ m` reads the relative run chart
`c₁` in B's stage coordinates: B's inverse stage chart `cℓ.2.1`, then the upper chart `c` shifted by `m`, then `c₁`.

* **`pullChart`**, **`isDomainChart_pullback`**: a domain chart `Ψ` of `D' ⊆ Dℓ`, read through the inverse of a
  domain chart `cℓ` of `Dℓ`, is a domain chart of `cℓ.1 '' D'` (the derivative-log of the inverse by
  `IsDerivLog.invFunOn`);
* **`relShift`**, **`isDomainChart_relShift`**: the upper chart shifted by `m` (relative frame) is a domain chart of
  the same domain;
* **`stageRelChart_eq`**: `stageRelChart cℓ c c₁ m = pullChart cℓ ((relShift c m).trans c₁)`;
* **`isDomainChart_stageRelChart`**: hence a domain chart of `cℓ.1 '' ((fun y => c.2.1 (y − m)) '' D₁)` for any domain
  chart `c₁` of `D₁` whose shifted pull-back lies in `cℓ`'s domain;
* **`image_fwd_diff_fillH`**: for `cℓ` a domain chart of `ℍ \ fill B` and `fill B ⊆ fill X`, `cℓ.1` maps
  `ℍ \ fill X` onto `ℍ \ stageRetained cℓ X`;
* **`image_relShift_diff_fillH`** (the cross fill identity, from round 4's `image_H_diff_fillH_of_chart`): the shifted
  upper-chart inverse maps the complement of the fill of a compact relative set `S` onto the complement of
  `fill (A ∪ ĝ_m '' S)`;
* **`isDomainChart_stageRelChart_of_fill`**: the domain-chart clause of `StageChainAtR`, from the three charts and the
  physical fill identity `fill (A ∪ ĝ_m '' Rel) = fill X`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Mn

open Lk

/-! ### Charts read through the inverse of a domain chart -/

/-- **A chart `Ψ` read through the inverse of the chart `cℓ`.** -/
def pullChart (cℓ Ψ : Chart) : Chart :=
  (fun w => Ψ.1 (cℓ.2.1 w), fun y => cℓ.1 (Ψ.2.1 y), fun w => Ψ.2.2 (cℓ.2.1 w) - cℓ.2.2 (cℓ.2.1 w))

/-- **A domain chart read through the inverse of a domain chart** is a domain chart. -/
theorem isDomainChart_pullback {Dℓ D' : Set ℂ} {cℓ Ψ : Chart} (hℓ : IsDomainChart Dℓ cℓ) (hΨ : IsDomainChart D' Ψ)
    (hsub : D' ⊆ Dℓ) : IsDomainChart (cℓ.1 '' D') (pullChart cℓ Ψ) := by
  have hΨmaps : ∀ y ∈ H, Ψ.2.1 y ∈ D' := fun y hy => hΨ.inv_mem hy
  have hconf : (pullChart cℓ Ψ).IsConformal := by
    refine ⟨?_, fun y hy => hℓ.fwd_mem (hsub (hΨmaps y hy)), fun y hy => ?_⟩
    · exact hℓ.differentiableOn_fwd.comp hΨ.1.1 fun y hy => hsub (hΨmaps y hy)
    · change Ψ.1 (cℓ.2.1 (cℓ.1 (Ψ.2.1 y))) = y
      rw [hℓ.inv_fwd (hsub (hΨmaps y hy)), hΨ.fwd_inv hy]
  have himg : (pullChart cℓ Ψ).2.1 '' H = cℓ.1 '' D' := by
    change (fun y => cℓ.1 (Ψ.2.1 y)) '' H = _
    rw [← image_image, hΨ.image_eq]
  have hEo : IsOpen (cℓ.1 '' D') := himg ▸ hconf.isOpen_image
  have hEH : cℓ.1 '' D' ⊆ H := by
    rintro _ ⟨z, hz, rfl⟩
    exact hℓ.fwd_mem (hsub hz)
  have hmaps : MapsTo cℓ.2.1 (cℓ.1 '' D') D' := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hℓ.inv_fwd (hsub hz)]
    exact hz
  -- the derivative-log of the inverse chart
  obtain ⟨Lℓ, hLℓ, hliftℓ⟩ := hℓ.2.2
  obtain ⟨LΨ, hLΨ, hliftΨ⟩ := hΨ.2.2
  have hinv : IsDerivLog (Function.invFunOn cℓ.1 Dℓ) (fun w => -Lℓ (Function.invFunOn cℓ.1 Dℓ w)) H :=
    IsDerivLog.invFunOn hℓ.isOpen hℓ.isConformalBijection hLℓ
  have heq : EqOn (Function.invFunOn cℓ.1 Dℓ) cℓ.2.1 H := fun w hw => by
    have hmem : cℓ.2.1 w ∈ Dℓ := hℓ.inv_mem hw
    have h := hℓ.isConformalBijection.2.injOn.leftInvOn_invFunOn hmem
    rwa [hℓ.fwd_inv hw] at h
  have hHo : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  have hinv' : IsDerivLog cℓ.2.1 (fun w => -Lℓ (cℓ.2.1 w)) H := by
    have h := IsDerivLog.congr_of_eqOn hHo hinv heq
    refine ⟨h.1.congr fun w hw => ?_, fun w hw => ?_⟩
    · show -Lℓ (cℓ.2.1 w) = -Lℓ (Function.invFunOn cℓ.1 Dℓ w)
      rw [heq hw]
    · have h2 : Complex.exp (-Lℓ (Function.invFunOn cℓ.1 Dℓ w)) = deriv cℓ.2.1 w := h.2 w hw
      rw [heq hw] at h2
      exact h2
  have hdiffinv : DifferentiableOn ℂ cℓ.2.1 (cℓ.1 '' D') := hℓ.1.1.mono hEH
  refine ⟨hconf, himg, fun w => LΨ (cℓ.2.1 w) + -Lℓ (cℓ.2.1 w), ?_, fun w hw => ?_⟩
  · exact IsDerivLog.comp (ψ := Ψ.1) (φ := cℓ.2.1) hEo hΨ.isOpen hΨ.differentiableOn_fwd hdiffinv hmaps hLΨ
      (hinv'.mono hEH)
  · obtain ⟨z, hz, rfl⟩ := hw
    have hzℓ := hsub hz
    show Ψ.2.2 (cℓ.2.1 (cℓ.1 z)) - cℓ.2.2 (cℓ.2.1 (cℓ.1 z)) =
      (LΨ (cℓ.2.1 (cℓ.1 z)) + -Lℓ (cℓ.2.1 (cℓ.1 z))).im
    rw [hℓ.inv_fwd hzℓ, Complex.add_im, Complex.neg_im, hliftΨ hz, hliftℓ hzℓ]
    ring

/-! ### The upper chart in the relative frame -/

/-- The upper chart shifted by `m` (the relative frame). -/
def relShift (c : Chart) (m : ℝ) : Chart := (fun z => c.1 z + (m : ℂ), fun w => c.2.1 (w - (m : ℂ)), fun z => c.2.2 z)

theorem sub_real_mem_H {w : ℂ} (hw : w ∈ H) (m : ℝ) : w - (m : ℂ) ∈ H := by
  show 0 < (w - (m : ℂ)).im
  simpa using (show (0 : ℝ) < w.im from hw)

theorem add_real_mem_H {w : ℂ} (hw : w ∈ H) (m : ℝ) : w + (m : ℂ) ∈ H := by
  show 0 < (w + (m : ℂ)).im
  simpa using (show (0 : ℝ) < w.im from hw)

/-- **The shifted upper chart is a domain chart of the same domain.** -/
theorem isDomainChart_relShift {D : Set ℂ} {c : Chart} (hc : IsDomainChart D c) (m : ℝ) :
    IsDomainChart D (relShift c m) := by
  have hconf : (relShift c m).IsConformal := by
    refine ⟨?_, fun w hw => hc.1.2.1 (sub_real_mem_H hw m), fun w hw => ?_⟩
    · exact hc.1.1.comp ((differentiable_id.sub_const _).differentiableOn) fun w hw => sub_real_mem_H hw m
    · change c.1 (c.2.1 (w - (m : ℂ))) + (m : ℂ) = w
      rw [hc.fwd_inv (sub_real_mem_H hw m), sub_add_cancel]
  have himg : (relShift c m).2.1 '' H = D := by
    rw [← hc.image_eq]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w - (m : ℂ), sub_real_mem_H hw m, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w + (m : ℂ), add_real_mem_H hw m, by change c.2.1 (w + (m : ℂ) - (m : ℂ)) = _; rw [add_sub_cancel_right]⟩
  obtain ⟨L, hL, hlift⟩ := hc.2.2
  refine ⟨hconf, himg, L, ⟨hL.1, fun z hz => ?_⟩, hlift⟩
  have hd : DifferentiableAt ℂ c.1 z := (hc.differentiableOn_fwd z hz).differentiableAt (hc.isOpen.mem_nhds hz)
  rw [hL.2 z hz]
  exact (deriv_add_const (f := c.1) (c := (m : ℂ))).symm

/-- **The relative chart in B's stage coordinates is a pull-back.** -/
theorem stageRelChart_eq (cℓ c c₁ : Chart) (m : ℝ) :
    stageRelChart cℓ c c₁ m = pullChart cℓ ((relShift c m).trans c₁) := rfl

/-- **The relative chart in B's stage coordinates is a domain chart** of the image of the relative domain. -/
theorem isDomainChart_stageRelChart {Dℓ Dc D₁ : Set ℂ} {cℓ c c₁ : Chart} {m : ℝ} (hℓ : IsDomainChart Dℓ cℓ)
    (hc : IsDomainChart Dc c) (h₁ : IsDomainChart D₁ c₁) (hsub : (fun y => c.2.1 (y - (m : ℂ))) '' D₁ ⊆ Dℓ) :
    IsDomainChart (cℓ.1 '' ((fun y => c.2.1 (y - (m : ℂ))) '' D₁)) (stageRelChart cℓ c c₁ m) := by
  rw [stageRelChart_eq]
  exact isDomainChart_pullback hℓ ((isDomainChart_relShift hc m).trans h₁) hsub

/-! ### The domain in stage coordinates -/

/-- **The complement of the retained set in stage coordinates** is the forward image of the physical complement. -/
theorem image_fwd_diff_fillH {B X : Set ℂ} {cℓ : Chart} (hℓ : IsDomainChart (H \ fillH B) cℓ)
    (hBX : fillH B ⊆ fillH X) : cℓ.1 '' (H \ fillH X) = H \ stageRetained cℓ X := by
  ext w
  constructor
  · rintro ⟨z, ⟨hzH, hzX⟩, rfl⟩
    have hzB : z ∈ H \ fillH B := ⟨hzH, fun h => hzX (hBX h)⟩
    refine ⟨hℓ.fwd_mem hzB, fun h => hzX ?_⟩
    have := h.2
    rwa [hℓ.inv_fwd hzB] at this
  · rintro ⟨hwH, hw⟩
    have hmem : cℓ.2.1 w ∈ H \ fillH B := hℓ.inv_mem hwH
    refine ⟨cℓ.2.1 w, ⟨hmem.1, fun h => hw ⟨hwH, h⟩⟩, hℓ.fwd_inv hwH⟩

/-- **The cross fill identity** (round 4's `image_H_diff_fillH_of_chart`, shifted): the upper-chart inverse in the
relative frame maps the complement of the fill of a compact relative set `S ⊆ ℍ̄` onto the complement of the fill of
the upper prefix with the boundary image of `S`. -/
theorem image_relShift_diff_fillH {c : Chart} {A S : Set ℂ} {m : ℝ} {ĝ : ℂ → ℂ} (hc : IsDomainChart (H \ fillH A) c)
    (hA : IsCompact A) (hĝ : ContinuousOn ĝ Hbar) (hgg : EqOn ĝ c.2.1 H) {C : ℝ} (hC : ∀ p ∈ Hbar, ‖ĝ p - p‖ ≤ C)
    (hS : IsCompact S) (hSH : S ⊆ Hbar) :
    (fun y => c.2.1 (y - (m : ℂ))) '' (H \ fillH S) =
      H \ fillH (A ∪ (fun y => ĝ (y - (m : ℂ))) '' S) := by
  have hrel := isDomainChart_relShift hc m
  have hdiff : DifferentiableOn ℂ (fun y => c.2.1 (y - (m : ℂ))) H := hrel.1.1
  have hinj : InjOn (fun y => c.2.1 (y - (m : ℂ))) H := hrel.1.injOn
  have hĝm : ContinuousOn (fun y => ĝ (y - (m : ℂ))) Hbar :=
    hĝ.comp (continuous_id.sub continuous_const).continuousOn fun y (hy : 0 ≤ y.im) =>
      show 0 ≤ (y - (m : ℂ)).im by simpa using hy
  have hgm : EqOn (fun y => ĝ (y - (m : ℂ))) (fun y => c.2.1 (y - (m : ℂ))) H := fun y hy =>
    hgg (sub_real_mem_H hy m)
  have hCm : ∀ p ∈ Hbar, ‖ĝ (p - (m : ℂ)) - p‖ ≤ C + |m| := fun p hp => by
    have hp' : p - (m : ℂ) ∈ Hbar := show 0 ≤ (p - (m : ℂ)).im by simpa using (show (0 : ℝ) ≤ p.im from hp)
    have h1 := hC _ hp'
    calc ‖ĝ (p - (m : ℂ)) - p‖ = ‖(ĝ (p - (m : ℂ)) - (p - (m : ℂ))) - (m : ℂ)‖ := by ring_nf
      _ ≤ ‖ĝ (p - (m : ℂ)) - (p - (m : ℂ))‖ + ‖(m : ℂ)‖ := norm_sub_le _ _
      _ ≤ C + |m| := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have hD : (fun y => c.2.1 (y - (m : ℂ))) '' H = H \ fillH A := hrel.image_eq
  exact image_H_diff_fillH_of_chart hdiff hinj hĝm hgm hCm hA hD hS hSH

/-- **The domain-chart clause of the corrected per-stage correspondence**: for domain charts `cℓ` of
`ℍ \ fill B`, `c` of `ℍ \ fill A` (with a continuous boundary extension `ĝ` near the identity) and `c₁` of
`ℍ \ fill Rel` (`Rel` compact in `ℍ̄`), if the physical fill of `A` with the boundary image of `Rel` is `fill X` and
`fill B ⊆ fill X`, then `stageRelChart cℓ c c₁ m` is a domain chart of `ℍ \ stageRetained cℓ X`. -/
theorem isDomainChart_stageRelChart_of_fill {cℓ c c₁ : Chart} {A B Rel X : Set ℂ} {m : ℝ} {ĝ : ℂ → ℂ}
    (hℓ : IsDomainChart (H \ fillH B) cℓ) (hc : IsDomainChart (H \ fillH A) c) (h₁ : IsDomainChart (H \ fillH Rel) c₁)
    (hA : IsCompact A) (hĝ : ContinuousOn ĝ Hbar) (hgg : EqOn ĝ c.2.1 H) {C : ℝ} (hC : ∀ p ∈ Hbar, ‖ĝ p - p‖ ≤ C)
    (hRel : IsCompact Rel) (hRelH : Rel ⊆ Hbar)
    (hfill : fillH (A ∪ (fun y => ĝ (y - (m : ℂ))) '' Rel) = fillH X) (hBX : fillH B ⊆ fillH X) :
    IsDomainChart (H \ stageRetained cℓ X) (stageRelChart cℓ c c₁ m) := by
  have himg := image_relShift_diff_fillH (m := m) hc hA hĝ hgg hC hRel hRelH
  rw [hfill] at himg
  have hsub : (fun y => c.2.1 (y - (m : ℂ))) '' (H \ fillH Rel) ⊆ H \ fillH B := by
    rw [himg]
    exact fun z hz => ⟨hz.1, fun h => hz.2 (hBX h)⟩
  have h := isDomainChart_stageRelChart hℓ hc h₁ hsub
  rwa [himg, image_fwd_diff_fillH hℓ hBX] at h

end InteractingSLE.Theorem14.SB.Mn
