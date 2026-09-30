import QuantumZipper.Proofs.Zipper.FieldLawler4ArcFeet
import QuantumZipper.Proofs.Zipper.FieldLawler3UnifF
import QuantumZipper.Proofs.Zipper.FieldLawlerSubExcGeo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-ARC (A3, part 1): which side of the arc lies in `hullComp`

Task FL4-ARC. For the arc `(α, β)` of `fl4_arc_angles` and the circle charts
`ψ_σ(ζ) = Z_t(ε e^{iσζ})` (`σ = ±1`; `σ = 1`: the upper half-plane goes inside the disc,
`σ = -1`: outside), one of the two half-discs at the mid-angle is mapped into `hullComp η`
(`fl4_side_anchor`), and connected sets off the circle are mapped into `ℍ \ η`
(`fl4_psi_image_sub`).

Own elementary argument (FL, EJP 20 (2015), p. 9 use the arcs as crosscuts without comment):
`η ⊆ ∂ hullComp η` (from `fl3u_FL3Unif_pieces`, using `a ≠ b`, `fl4_feet_ne`); a point of
`hullComp η` near `Z_t(ε e^{ix₀})` pulls back by `Z_t⁻¹` to a point off the circle near
`ε e^{ix₀}`, whose complex logarithm gives the parameter `ζ₀` of the half-disc.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- The circle chart `ζ ↦ ε e^{iσζ}`. -/
def fl4E (ε σ : ℝ) (ζ : ℂ) : ℂ := (ε : ℂ) * exp ((σ : ℂ) * ζ * I)

/-- The image chart `ζ ↦ Z_t(ε e^{iσζ})`. -/
def fl4Psi (W : ℝ → ℝ) (t ε σ : ℝ) (ζ : ℂ) : ℂ := fwdMap W t (fl4E ε σ ζ)

lemma fl4E_real (ε σ x : ℝ) : fl4E ε σ (x : ℂ) = flCirc ε (σ * x) := by
  simp only [fl4E, flCirc]; push_cast; ring_nf

lemma fl4E_norm {ε : ℝ} (hε : 0 < ε) (σ : ℝ) (ζ : ℂ) :
    ‖fl4E ε σ ζ‖ = ε * Real.exp (-(σ * ζ.im)) := by
  simp only [fl4E, norm_mul, Complex.norm_exp, norm_real, Real.norm_eq_abs, abs_of_pos hε]
  congr 2
  simp

lemma fl4E_continuous (ε σ : ℝ) : Continuous (fl4E ε σ) := by
  unfold fl4E; fun_prop

lemma fl4E_neg (ε : ℝ) (ζ : ℂ) : fl4E ε (-1) (-ζ) = fl4E ε 1 ζ := by
  simp only [fl4E]; push_cast; ring_nf

/-- The arc of a crosscut lies in the closure of `hullComp` (feet distinct). -/
theorem fl4_arc_sub_closure {η : ℝ → ℂ} {a b : ℝ} (hη : IsCrosscutH η)
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ))) (hab : a ≠ b) :
    arcH η ⊆ closure (hullComp η) := by
  rcases hab.lt_or_gt with h | h
  · obtain ⟨-, -, -, -, -, hcl, -⟩ := fl3u_FL3Unif_pieces hη ha hb h
    exact subset_closure.trans (hcl.trans frontier_subset_closure)
  · have ha' : Tendsto (fun s => η (1 - s)) (𝓝[>] 0) (𝓝 (b : ℂ)) := hb.comp fl_rev_tendsto0
    have hb' : Tendsto (fun s => η (1 - s)) (𝓝[<] 1) (𝓝 (a : ℂ)) := ha.comp fl_rev_tendsto1
    obtain ⟨-, -, -, -, -, hcl, -⟩ := fl3u_FL3Unif_pieces (fl_rev_crosscut hη) ha' hb' h
    have e1 : hullComp (fun s => η (1 - s)) = hullComp η := by
      unfold hullComp; rw [fl_rev_arcH]
    rw [fl_rev_arcH, e1] at hcl
    exact subset_closure.trans (hcl.trans frontier_subset_closure)

/-- A preconnected subset of `ℍ \ η` meeting `hullComp η` lies in it. -/
theorem fl4_preconn_sub_hullComp {η : ℝ → ℂ} {C : Set ℂ} (hC : IsPreconnected C)
    (hCS : C ⊆ H \ arcH η) {z₀ : ℂ} (hz₀ : z₀ ∈ C) (hz₀U : z₀ ∈ hullComp η) :
    C ⊆ hullComp η := by
  intro z hz
  have hsub : C ⊆ connectedComponentIn (H \ arcH η) z₀ :=
    hC.subset_connectedComponentIn hz₀ hCS
  refine ⟨hCS hz, ?_⟩
  rw [← connectedComponentIn_eq (hsub hz)]
  exact hz₀U.2

variable (hc : SideCtx W t F) {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ}
  (hη : IsCrosscutH η) (hsub : arcH η ⊆ {p | ‖fwdMapInv W t p‖ = ε})
include hc hε hη hsub

/-- Sets off the circle inside `D` are mapped into `ℍ \ η`, preserving preconnectedness. -/
theorem fl4_psi_image_sub {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {T : Set ℂ}
    (hT : ∀ ζ ∈ T, 0 < ζ.im ∧ fl4E ε σ ζ ∈ H \ fwdHull W t) :
    fl4Psi W t ε σ '' T ⊆ H \ arcH η := by
  rintro _ ⟨ζ, hζ, rfl⟩
  obtain ⟨him, hD⟩ := hT ζ hζ
  refine ⟨hc.mapsTo hD, ?_⟩
  rintro ⟨s, hs, hse⟩
  have h1 : F (η s) = fl4E ε σ ζ := by rw [hse]; exact hc.F_fwdMap hD
  have h2 : ‖fwdMapInv W t (η s)‖ = ε := hsub ⟨s, hs, rfl⟩
  rw [← hc.Feq (hη.2.2.1 hs), h1, fl4E_norm hε] at h2
  have h3 : Real.exp (-(σ * ζ.im)) = 1 := by
    have := mul_left_cancel₀ hε.ne' (h2.trans (mul_one ε).symm)
    exact this
  rw [Real.exp_eq_one_iff] at h3
  rcases hσ with rfl | rfl <;> linarith

theorem fl4_psi_preconn {σ : ℝ} {T : Set ℂ} (hTc : IsPreconnected T)
    (hT : ∀ ζ ∈ T, fl4E ε σ ζ ∈ H \ fwdHull W t) : IsPreconnected (fl4Psi W t ε σ '' T) :=
  hTc.image _ ((hc.continuousOn_fwdMap).comp (fl4E_continuous ε σ).continuousOn hT)

omit hsub in
/-- Points of the arc: in `D`, and `Z_t` of them lies on `η`. -/
theorem fl4_arc_pt {α β : ℝ} (himg : fwdMapInv W t '' arcH η = flCircArc ε α β) {y : ℝ}
    (hy : y ∈ Ioo α β) :
    flCirc ε y ∈ H \ fwdHull W t ∧ fwdMap W t (flCirc ε y) ∈ arcH η := by
  have : flCirc ε y ∈ fwdMapInv W t '' arcH η := himg ▸ ⟨y, hy, rfl⟩
  obtain ⟨_, ⟨s, hs, rfl⟩, hse⟩ := this
  have hH := hη.2.2.1 hs
  rw [← hse, ← hc.Feq hH]
  exact ⟨hc.F_mem_dom hH, by rw [hc.fwdMap_F hH]; exact ⟨s, hs, rfl⟩⟩

/-- **(A3, anchor)** One of the two half-discs at the mid-angle `x₀ = (α + β)/2` has a point
mapped into `hullComp η`: `σ = 1` (inside the disc) or `σ = -1` (outside). -/
theorem fl4_side_anchor {a b : ℝ} (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ))) {α β : ℝ} (h0α : 0 ≤ α) (hαβ : α < β)
    (hβπ : β ≤ π) (himg : fwdMapInv W t '' arcH η = flCircArc ε α β) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ r₀ > 0,
      (∀ ζ ∈ ball (((σ * ((α + β) / 2) : ℝ)) : ℂ) r₀, fl4E ε σ ζ ∈ H \ fwdHull W t) ∧
      ∃ ζ₀ ∈ ball (((σ * ((α + β) / 2) : ℝ)) : ℂ) r₀, 0 < ζ₀.im ∧
        fl4Psi W t ε σ ζ₀ ∈ hullComp η := by
  set x₀ : ℝ := (α + β) / 2 with hx₀def
  have hx₀ : x₀ ∈ Ioo α β := ⟨by simp only [hx₀def]; linarith, by simp only [hx₀def]; linarith⟩
  have hx₀π : x₀ ∈ Ioo 0 π := ⟨h0α.trans_lt hx₀.1, hx₀.2.trans_le hβπ⟩
  set D := H \ fwdHull W t with hD
  have hDo : IsOpen D := hc.isOpen_dom
  have hHo : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  have hHb : H ⊆ Hbar := fun z hz => by show (0 : ℝ) ≤ z.im; exact le_of_lt hz
  set q := flCirc ε x₀ with hq
  obtain ⟨hqD, hpA⟩ := fl4_arc_pt hc hε hη himg hx₀
  set p := fwdMap W t q with hp
  have hpcl := fl4_arc_sub_closure hη ha hb (fl4_feet_ne hc hε hη ha hb hsub) hpA
  have hO : IsOpen (fl4E ε 1 ⁻¹' D) := hDo.preimage (fl4E_continuous ε 1)
  have hx₀O : (x₀ : ℂ) ∈ fl4E ε 1 ⁻¹' D := by
    show fl4E ε 1 (x₀ : ℂ) ∈ D; rw [fl4E_real, one_mul]; exact hqD
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.1 hO _ hx₀O
  set L : ℂ → ℂ := fun w => -I * log (w / ε) with hL
  have hqe : q / ε = exp (x₀ * I) := by
    simp only [hq, flCirc]; field_simp [ofReal_ne_zero.2 hε.ne']
  have hsin : 0 < Real.sin x₀ := Real.sin_pos_of_pos_of_lt_pi hx₀π.1 hx₀π.2
  have hLq : L q = x₀ := by
    simp only [hL, hqe]
    rw [log_exp (by simp; linarith [hx₀π.1, Real.pi_pos]) (by simp; exact hx₀π.2.le)]
    ring_nf; rw [I_sq]; ring
  have hslit : q / ε ∈ slitPlane := by
    rw [hqe]; right; rw [exp_ofReal_mul_I_im]; exact hsin.ne'
  have hLc : ContinuousAt L q := by
    have h1 : ContinuousAt (fun w : ℂ => w / (ε : ℂ)) q := continuousAt_id.div_const _
    have h2 : ContinuousAt (fun w : ℂ => log (w / (ε : ℂ))) q :=
      ContinuousAt.comp (g := log) (f := fun w : ℂ => w / (ε : ℂ)) (continuousAt_clog hslit) h1
    exact continuousAt_const.mul h2
  have hqslit : q ∈ slitPlane := by
    right; rw [hq, flCirc_im]; exact (mul_pos hε hsin).ne'
  have hargq : arg q = x₀ := fl4_arg_flCirc hε hx₀π
  have hN : D ∩ L ⁻¹' ball (x₀ : ℂ) r₀ ∩ arg ⁻¹' Ioo α β ∈ 𝓝 q := by
    refine inter_mem (inter_mem (hDo.mem_nhds hqD) (hLc.preimage_mem_nhds ?_))
      ((continuousAt_arg hqslit).preimage_mem_nhds ?_)
    · rw [hLq]; exact ball_mem_nhds _ hr₀
    · rw [hargq]; exact Ioo_mem_nhds hx₀.1 hx₀.2
  have hpH : p ∈ H := hc.mapsTo hqD
  have hFc : ContinuousAt F p :=
    hc.Fcont.continuousAt (Filter.mem_of_superset (hHo.mem_nhds hpH) hHb)
  have hFp : F p = q := hc.F_fwdMap hqD
  obtain ⟨z, hzN, hzU⟩ := mem_closure_iff_nhds.1 hpcl (F ⁻¹' _)
    (hFc.preimage_mem_nhds (hFp ▸ hN))
  have hzH : z ∈ H := hzU.1.1
  have hzA : z ∉ arcH η := hzU.1.2
  set w := F z with hw
  obtain ⟨⟨hwD, hwL⟩, hwarg⟩ := hzN
  have hzw : fwdMap W t w = z := hc.fwdMap_F hzH
  have hw0 : w ≠ 0 := fun h => by
    have h1 : (0 : ℝ) < w.im := hwD.1
    rw [h] at h1; simp at h1
  have hne : ‖w‖ ≠ ε := fun h => by
    have e : flCirc ε (arg w) = w := by
      have := norm_mul_exp_arg_mul_I w; rw [h] at this; exact this
    apply hzA
    rw [← hzw, ← e]
    exact (fl4_arc_pt hc hε hη himg hwarg).2
  have hEw : fl4E ε 1 (L w) = w := by
    have e1 : ((1 : ℝ) : ℂ) * L w * I = log (w / ε) := by
      simp only [hL]; push_cast; ring_nf; rw [I_sq]; ring
    simp only [fl4E]
    rw [e1, exp_log (div_ne_zero hw0 (ofReal_ne_zero.2 hε.ne'))]
    field_simp [ofReal_ne_zero.2 hε.ne']
  have him : (L w).im = -Real.log (‖w‖ / ε) := by
    simp only [hL, neg_mul, neg_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add, log_re,
      norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hε]
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨1, Or.inl rfl, r₀, hr₀, fun ζ hζ => ?_, L w, ?_, ?_, ?_⟩
    · rw [one_mul] at hζ; exact hball hζ
    · rw [one_mul]; exact hwL
    · rw [him]
      have := Real.log_neg (div_pos hwpos hε) ((div_lt_one hε).2 hlt)
      linarith
    · show fwdMap W t _ ∈ _
      rw [hEw, hzw]; exact hzU
  · have hcast : (((-1 : ℝ) * x₀ : ℝ) : ℂ) = -(x₀ : ℂ) := by push_cast; ring
    refine ⟨-1, Or.inr rfl, r₀, hr₀, fun ζ hζ => ?_, -L w, ?_, ?_, ?_⟩
    · rw [hcast] at hζ
      have h1 : -ζ ∈ ball (x₀ : ℂ) r₀ := by
        rw [mem_ball, ← neg_neg (x₀ : ℂ), dist_neg_neg]; exact hζ
      have : fl4E ε 1 (-ζ) ∈ D := hball h1
      rw [← fl4E_neg, neg_neg] at this
      exact this
    · rw [hcast, mem_ball, dist_neg_neg]; exact hwL
    · rw [neg_im, him]
      have := Real.log_pos ((one_lt_div hε).2 hgt)
      linarith
    · show fwdMap W t _ ∈ _
      rw [fl4E_neg, hEw, hzw]; exact hzU

end FieldLawler
end QuantumZipper
