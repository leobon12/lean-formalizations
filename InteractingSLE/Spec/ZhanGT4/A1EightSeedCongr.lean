/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1SeedFieldCol
import InteractingSLE.Spec.ZhanGT4.DualWidth
import InteractingSLE.Spec.Sec7.LocalExtGChart

/-!
# Zhan's A.1 (R80): the seeded logarithm at own time `u` reads the growing driver on `[0, u]` only

Packet PROVE-A1-EIGHTSEED. Source: Astra, *Follow-up proofs*, §A.1.4 (`ig1_followup_proofs.txt` L401–L406: the
density `M(S₁ᵐ, S₂ᵐ)` "is a function of the two stopped paths alone").

The records of rectangle `m` use the growing driver stopped at the rectangle's exit, so two rectangles use two
different (globally continuous) drivers that agree up to the smaller exit. PROVE-ZHAN-GT4-A18's `DualWidth` proves
that two image chains of the SAME driver agree; here the drivers may differ after a time `U`:

* `fwdMap_eq_of_eqOn_Icc`: forward maps of drivers agreeing on `[0, U]` agree at times `t ≤ U`;
* `OwnData.exists_common_rate_of_eqOn`, **`OwnData.eqOn_clock_of_eqOn`**, `OwnData.imgDrv_clock_eq_of_eqOn`,
  `OwnData.eqOn_imgDriver_of_eqOn`: two image chains of continuous drivers agreeing on `[0, U]` (same frozen hull and
  chart) have the same clock on `[0, min (min T₁ T₂) U]` and the same image driver along it (the capacity rate and the
  boundary value are read from a mapping-out function of `g_t(A)`, which is the same for both drivers);
* **`OwnData.ownExt_congr_of_eqOn`**: hence the same own-time map `ownExt` (the inverse Loewner map at `u` reads the
  driver on `[0, u]`, `LocalExt.fwdMapInv_congr_of_continuousOn`);
* **`SeedData.normEll_congr`**: the seeded logarithm at `u` depends only on `ownExt` on `[0, u]`, the driver on
  `[0, u]`, the frozen-tip factors and the mark coordinates at `u`;
* **`normEll_fromSource_congr`**: for two source records (`SeedData.fromSource`) of continuous drivers agreeing on
  `[0, U]`, with image chains, and marks agreeing at `u ≤ min (min T₁ T₂) U`, the seeded logarithms at `u` agree.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H fwdMap fwdMapInv fwdHull)

/-! ### Two image chains of two drivers agreeing up to `U` -/

namespace OwnData

variable {W₁ W₂ : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T₁ T₂ U : ℝ} {a₁ a₂ I₁ I₂ : ℝ → ℝ}

/-- The common capacity rate at a time `t` where the two drivers and their forward maps agree. -/
theorem exists_common_rate_of_eqOn (h₁ : OwnData W₁ A φ T₁ a₁ I₁) (h₂ : OwnData W₂ A φ T₂ a₂ I₂) {t : ℝ}
    (ht₁ : t ∈ Icc (0 : ℝ) T₁) (ht₂ : t ∈ Icc (0 : ℝ) T₂) (hWt : W₁ t = W₂ t) (hf : fwdMap W₁ t = fwdMap W₂ t) :
    ∃ c : ℝ, HasDerivWithinAt a₁ c (Icc 0 T₁) t ∧ HasDerivWithinAt a₂ c (Icc 0 T₂) t ∧ I₁ (a₁ t) = I₂ (a₂ t) := by
  have hE : (fun z => fwdMap W₂ t z + W₂ t) '' A = (fun z => fwdMap W₁ t z + W₁ t) '' A := by
    rw [hf, hWt]
  have hR := ConformalImage.isMapOut_mapOut (h₁.isHPHull_E ht₁)
  have hR₂ : IsMapOut ((fun z => fwdMap W₂ t z + W₂ t) '' A)
      (ConformalImage.mapOut ((fun z => fwdMap W₁ t z + W₁ t) '' A)) := by
    rw [hE]; exact hR
  obtain ⟨-, hlim, ⟨δ, hδ, Rext, hd, he⟩, hrate⟩ := h₁.rate t ht₁ _ hR
  obtain ⟨-, hlim', -, hrate'⟩ := h₂.rate t ht₂ _ hR₂
  rw [← hWt] at hlim' hrate'
  refine ⟨(deriv Rext (W₁ t)).re ^ 2, (hrate δ hδ Rext hd he).2.2, (hrate' δ hδ Rext hd he).2.2, ?_⟩
  have hne : (𝓝[H] ((W₁ t : ℝ) : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (Complex.ofReal_im _)
  exact Complex.ofReal_injective (tendsto_nhds_unique hlim hlim')

/-- The forward maps of two drivers agreeing on `[0, U]` agree at every `t ≤ U`. -/
theorem _root_.InteractingSLE.ZhanGT4.fwdMap_eq_of_eqOn_Icc (hW : EqOn W₁ W₂ (Icc 0 U)) {t : ℝ} (ht : t ≤ U) :
    fwdMap W₁ t = fwdMap W₂ t :=
  funext fun _ => Ito.fwdMap_congr_of_eqOn fun _ hs => hW ⟨hs.1, hs.2.trans ht⟩

variable (h₁ : OwnData W₁ A φ T₁ a₁ I₁) (h₂ : OwnData W₂ A φ T₂ a₂ I₂) (hW : EqOn W₁ W₂ (Icc 0 U))
include h₁ h₂ hW

omit h₁ h₂ in
theorem eqOn_fwdMap_of_eqOn {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (min (min T₁ T₂) U)) : fwdMap W₁ t = fwdMap W₂ t :=
  fwdMap_eq_of_eqOn_Icc hW (ht.2.trans (min_le_right _ _))

/-- **The clocks agree on `[0, min (min T₁ T₂) U]`.** -/
theorem eqOn_clock_of_eqOn : EqOn a₁ a₂ (Icc 0 (min (min T₁ T₂) U)) := by
  have hsub₁ : Icc (0 : ℝ) (min (min T₁ T₂) U) ⊆ Icc 0 T₁ :=
    Icc_subset_Icc_right ((min_le_left _ _).trans (min_le_left _ _))
  have hsub₂ : Icc (0 : ℝ) (min (min T₁ T₂) U) ⊆ Icc 0 T₂ :=
    Icc_subset_Icc_right ((min_le_left _ _).trans (min_le_right _ _))
  have hcont : ContinuousOn (fun t => a₁ t - a₂ t) (Icc 0 (min (min T₁ T₂) U)) :=
    (h₁.contA.mono hsub₁).sub (h₂.contA.mono hsub₂)
  have hderiv : ∀ x ∈ Ico (0 : ℝ) (min (min T₁ T₂) U), HasDerivWithinAt (fun t => a₁ t - a₂ t) 0 (Ici x) x := by
    intro x hx
    have hxI : x ∈ Icc (0 : ℝ) (min (min T₁ T₂) U) := Ico_subset_Icc_self hx
    have hx₁ : x ∈ Ico (0 : ℝ) T₁ := ⟨hx.1, hx.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))⟩
    have hx₂ : x ∈ Ico (0 : ℝ) T₂ := ⟨hx.1, hx.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))⟩
    obtain ⟨c, hc, hc', -⟩ := exists_common_rate_of_eqOn h₁ h₂ (Ico_subset_Icc_self hx₁)
      (Ico_subset_Icc_self hx₂) (hW ⟨hx.1, hx.2.le.trans (min_le_right _ _)⟩) (eqOn_fwdMap_of_eqOn hW hxI)
    have k₁ := hc.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx₁)
    have k₂ := hc'.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx₂)
    have k₃ := k₁.sub k₂
    rw [sub_self] at k₃
    exact k₃
  intro x hx
  have := constant_of_has_deriv_right_zero hcont hderiv x hx
  rw [h₁.a0, h₂.a0, sub_zero] at this
  exact sub_eq_zero.1 this

/-- **The image drivers agree along the clock.** -/
theorem imgDrv_clock_eq_of_eqOn {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (min (min T₁ T₂) U)) : I₁ (a₁ t) = I₂ (a₂ t) := by
  obtain ⟨-, -, -, he⟩ := exists_common_rate_of_eqOn h₁ h₂
    ⟨ht.1, ht.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
    ⟨ht.1, ht.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩ (hW ⟨ht.1, ht.2.trans (min_le_right _ _)⟩)
    (eqOn_fwdMap_of_eqOn hW ht)
  exact he

/-- **The image drivers agree on `[0, a₁ x]`** for `x ≤ min (min T₁ T₂) U`. -/
theorem eqOn_imgDriver_of_eqOn {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (min (min T₁ T₂) U)) : EqOn I₁ I₂ (Icc 0 (a₁ x)) := by
  intro s hs
  have hxT : x ∈ Icc (0 : ℝ) T₁ := ⟨hx.1, hx.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hc : ContinuousOn a₁ (Icc 0 x) := h₁.contA.mono (Icc_subset_Icc_right hxT.2)
  obtain ⟨u, hu, hus⟩ := intermediate_value_Icc hx.1 hc (by rw [h₁.a0]; exact hs)
  have huT : u ∈ Icc (0 : ℝ) (min (min T₁ T₂) U) := ⟨hu.1, hu.2.trans hx.2⟩
  rw [← hus, imgDrv_clock_eq_of_eqOn h₁ h₂ hW huT, eqOn_clock_of_eqOn h₁ h₂ hW huT]

/-- The image forward maps agree at the clock time. -/
theorem fwdMap_img_eq_of_eqOn {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (min (min T₁ T₂) U)) :
    fwdMap I₁ (a₁ u) = fwdMap I₂ (a₂ u) := by
  funext z
  rw [← eqOn_clock_of_eqOn h₁ h₂ hW hu]
  exact Ito.fwdMap_congr_of_eqOn_of_le (eqOn_imgDriver_of_eqOn h₁ h₂ hW hu) le_rfl

/-- **The own-time maps agree** at every `u ≤ min (min T₁ T₂) U`. -/
theorem ownExt_congr_of_eqOn {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (min (min T₁ T₂) U)) :
    ownExt W₁ I₁ a₁ φ u = ownExt W₂ I₂ a₂ φ u := by
  have hWu : W₁ u = W₂ u := hW ⟨hu.1, hu.2.trans (min_le_right _ _)⟩
  have hinv : ∀ z, invMap W₁ u z = invMap W₂ u z := fun z => by
    unfold invMap
    rw [hWu]
    exact LocalExt.fwdMapInv_congr_of_continuousOn h₁.cont.continuousOn h₂.cont.continuousOn hu.1
      (lt_add_one u) (fun s hs => hW ⟨hs.1, hs.2.trans (hu.2.trans (min_le_right _ _))⟩) _
  have hown : ownMap W₁ I₁ a₁ φ u = ownMap W₂ I₂ a₂ φ u := by
    funext z
    unfold ownMap
    rw [hinv, fwdMap_img_eq_of_eqOn h₁ h₂ hW hu, imgDrv_clock_eq_of_eqOn h₁ h₂ hW hu]
  funext z
  unfold ownExt
  rw [hown]

end OwnData

/-! ### The seeded logarithm reads its data at `u` and the own-time maps on `[0, u]` -/

namespace SeedData

variable {n : ℕ}

/-- **Congruence of the seeded logarithm**: two seeded data with the same `κ`, charges and own-time maps on
`[0, u]`, the same driver on `[0, u]`, and the same frozen-tip factors, other-source coordinate and marks at `u`,
have the same `normEll` at `u`. -/
theorem normEll_congr {s₁ s₂ : SeedData n} {u : ℝ} (hu : 0 ≤ u) (hκ : s₁.κ = s₂.κ) (hr : s₁.r = s₂.r)
    (hext : ∀ v ∈ Icc (0 : ℝ) u, ownExt s₁.W s₁.W' s₁.a s₁.φ v = ownExt s₂.W s₂.W' s₂.a s₂.φ v)
    (hW : ∀ v ∈ Icc (0 : ℝ) u, s₁.W v = s₂.W v) (hA20 : s₁.A20 u = s₂.A20 u) (hA21 : s₁.A21 u = s₂.A21 u)
    (hV₀ : s₁.V₀ u = s₂.V₀ u) (hV : ∀ m, s₁.V m u = s₂.V m u) : s₁.normEll u = s₂.normEll u := by
  have huu : u ∈ Icc (0 : ℝ) u := ⟨hu, le_rfl⟩
  have hF : ∀ k, s₁.F k u = s₂.F k u := fun k => by
    funext x
    unfold F
    rw [hext u huu]
  have hA : ∀ k, s₁.A k u = s₂.A k u := fun k => by
    unfold A frzA
    rw [hext u huu, hW u huu]
  have hL : s₁.L u = s₂.L u := by
    unfold L frzLogF
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hu] at hv
    unfold frzRate frzA
    rw [hext v hv, hW v hv]
  have hB0 : s₁.B0 u = s₂.B0 u := by
    funext m
    unfold B0
    rw [hF, hV]
  have hB1 : s₁.B1 u = s₂.B1 u := by
    funext m
    unfold B1
    rw [hF, hV]
  have hVv : ∀ m, s₁.V m u = s₂.V m u := hV
  unfold normEll
  simp only [hκ, hr, hA21, hL, hB1, hA20, hB0, hV₀, hVv, hF, hA, hW u huu]

end SeedData

/-! ### Source records of two drivers agreeing up to `U` -/

section Source

variable {n : ℕ} {W₁ W₂ : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T₁ T₂ U : ℝ} {a₁ a₂ I₁ I₂ : ℝ → ℝ}

/-- **The seeded logarithm of a source record at own time `u` reads the growing driver on `[0, u]` only**: two source
records (`SeedData.fromSource`, same frozen chart `φ`, charges, frozen tip `ζ₀` and other source `p`) of continuous
drivers agreeing on `[0, U]`, with image chains up to `T₁`, `T₂` against the same frozen hull, and marks agreeing at
`u`, have the same `normEll` at every `u ≤ min (min T₁ T₂) U`. -/
theorem normEll_fromSource_congr (h₁ : OwnData W₁ A φ T₁ a₁ I₁) (h₂ : OwnData W₂ A φ T₂ a₂ I₂)
    (hW : EqOn W₁ W₂ (Icc 0 U)) (κ : ℝ) (rr : Fin n → ℝ) (ζ₀ p : ℝ) {V₁ V₂ : Fin n → ℝ → ℝ} {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (min (min T₁ T₂) U)) (hV : ∀ m, V₁ m u = V₂ m u) :
    (SeedData.fromSource W₁ I₁ a₁ φ κ rr ζ₀ p V₁).normEll u =
      (SeedData.fromSource W₂ I₂ a₂ φ κ rr ζ₀ p V₂).normEll u := by
  have hsub : ∀ v ∈ Icc (0 : ℝ) u, v ∈ Icc (0 : ℝ) (min (min T₁ T₂) U) := fun v hv => ⟨hv.1, hv.2.trans hu.2⟩
  have hWu : W₁ u = W₂ u := hW ⟨hu.1, hu.2.trans (min_le_right _ _)⟩
  have hfu := OwnData.eqOn_fwdMap_of_eqOn hW hu
  have himg := OwnData.fwdMap_img_eq_of_eqOn h₁ h₂ hW hu
  have hI := OwnData.imgDrv_clock_eq_of_eqOn h₁ h₂ hW hu
  refine SeedData.normEll_congr hu.1 rfl rfl (fun v hv => OwnData.ownExt_congr_of_eqOn h₁ h₂ hW (hsub v hv))
    (fun v hv => hW ⟨hv.1, (hsub v hv).2.trans (min_le_right _ _)⟩) ?_ ?_ ?_ hV
  · change frzImg I₁ a₁ ζ₀ u = frzImg I₂ a₂ ζ₀ u
    unfold frzImg
    rw [himg, hI]
  · change frzImgD I₁ a₁ ζ₀ u / (deriv (fwdMap W₁ u) p).re = frzImgD I₂ a₂ ζ₀ u / (deriv (fwdMap W₂ u) p).re
    unfold frzImgD
    rw [himg, hfu]
  · change (fwdMap W₁ u p).re + W₁ u = (fwdMap W₂ u p).re + W₂ u
    rw [hfu, hWu]

end Source

end InteractingSLE.ZhanGT4
