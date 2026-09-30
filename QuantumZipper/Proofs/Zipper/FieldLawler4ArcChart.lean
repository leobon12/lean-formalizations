import QuantumZipper.Proofs.Zipper.FieldLawler4ArcSide
import QuantumZipper.Proofs.Zipper.FieldLawler3Sym

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-ARC (A3): the boundary chart of `hullComp η` along an image crosscut

Task FL4-ARC. For an image crosscut `η ⊆ Z_t(C_ε)` of `FLImageSumBoundStmt`, with arc `(α, β)` of
`fl4_arc_feet`, one of the circle charts `ψ_σ(ζ) = Z_t(ε e^{iσζ})`, `σ = ±1`, is an analytic
boundary chart `FL3Arc (hullComp η) ψ_σ {x | σ x ∈ (α, β)}` whose real trace is `η`
(`fl4_arc_chart`).

Own elementary argument (FL, EJP 20 (2015), p. 9, treat the arcs as crosscuts without comment):
the half-disc at the mid-angle found by `fl4_side_anchor` is joined to the half-disc at any other
point `x` of the arc by the convex set `ℍ ∩ thickening δ [x₀, x]`, whose `ψ_σ`-image is a
connected subset of `ℍ \ η` (`fl4_psi_image_sub`), hence lies in `hullComp η`
(`fl4_preconn_sub_hullComp`).
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- **(A1–A3)** The `D`-arc of an image crosscut, the images of its feet, and a boundary chart of
`hullComp η` along it (`σ = 1`: the chart's upper half-plane goes inside `B(0, ε)`; `σ = -1`:
outside). -/
theorem fl4_arc_chart (hc : SideCtx W t F) {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} {a b : ℝ}
    (hη : IsCrosscutH η) (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hsub : arcH η ⊆ {p | ‖fwdMapInv W t p‖ = ε}) :
    ∃ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ π ∧
      fwdMapInv W t '' arcH η = flCircArc ε α β ∧
      flCirc ε α ∉ H \ fwdHull W t ∧ flCirc ε β ∉ H \ fwdHull W t ∧
      ((F a = flCirc ε α ∧ F b = flCirc ε β) ∨ (F a = flCirc ε β ∧ F b = flCirc ε α)) ∧
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        FL3Arc (hullComp η) (fl4Psi W t ε σ) {x : ℝ | σ * x ∈ Ioo α β} ∧
        fl4Psi W t ε σ '' ((fun x : ℝ => (x : ℂ)) '' {x : ℝ | σ * x ∈ Ioo α β}) = arcH η := by
  obtain ⟨α, β, h0α, hαβ, hβπ, himg, hαD, hβD, hfeet⟩ := fl4_arc_feet hc hε hη ha hb hsub
  refine ⟨α, β, h0α, hαβ, hβπ, himg, hαD, hβD, hfeet, ?_⟩
  obtain ⟨σ, hσ, r₀, hr₀, hball₀, ζ₀, hζ₀b, hζ₀im, hζ₀U⟩ :=
    fl4_side_anchor hc hε hη hsub ha hb h0α hαβ hβπ himg
  refine ⟨σ, hσ, ?_⟩
  set D := H \ fwdHull W t with hD
  have hDo : IsOpen D := hc.isOpen_dom
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set J := {x : ℝ | σ * x ∈ Ioo α β} with hJdef
  obtain ⟨A, B, hJ⟩ : ∃ A B : ℝ, J = Ioo A B := by
    rcases hσ with rfl | rfl
    · exact ⟨α, β, by ext x; simp [hJdef]⟩
    · refine ⟨-β, -α, ?_⟩
      ext x; simp only [hJdef, mem_setOf_eq, mem_Ioo]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  set xa : ℝ := σ * ((α + β) / 2) with hxa
  have hxaJ : xa ∈ J := by
    show σ * xa ∈ Ioo α β
    rw [hxa, ← mul_assoc, hσσ, one_mul]; constructor <;> linarith
  have hrealD : ∀ y ∈ J, fl4E ε σ (y : ℂ) ∈ D ∧ fl4Psi W t ε σ (y : ℂ) ∈ arcH η := fun y hy => by
    rw [fl4Psi, fl4E_real]; exact fl4_arc_pt hc hε hη himg hy
  have hcl : arcH η ⊆ closure (hullComp η) :=
    fl4_arc_sub_closure hη ha hb (fl4_feet_ne hc hε hη ha hb hsub)
  have hUo : IsOpen (hullComp η) := lwExc_hullComp_isOpen hη
  have hHconv : Convex ℝ H := by
    have : H = Complex.imLm ⁻¹' Ioi 0 := rfl
    rw [this]; exact (convex_Ioi 0).linear_preimage _
  have hOσ : IsOpen (fl4E ε σ ⁻¹' D) := hDo.preimage (fl4E_continuous ε σ)
  -- the half-disc at the anchor
  have hHb : fl4Psi W t ε σ '' (H ∩ ball (xa : ℂ) r₀) ⊆ hullComp η := by
    have hT : ∀ ζ ∈ H ∩ ball (xa : ℂ) r₀, 0 < ζ.im ∧ fl4E ε σ ζ ∈ D :=
      fun ζ hζ => ⟨hζ.1, hball₀ ζ hζ.2⟩
    exact fl4_preconn_sub_hullComp
      (fl4_psi_preconn hc hε hη hsub ((hHconv.inter (convex_ball _ _)).isPreconnected)
        fun ζ hζ => (hT ζ hζ).2)
      (fl4_psi_image_sub hc hε hη hsub hσ hT) ⟨ζ₀, ⟨hζ₀im, hζ₀b⟩, rfl⟩ hζ₀U
  refine ⟨⟨by rw [hJ]; exact measurableSet_Ioo, fun x hx => ?_, ?_⟩, ?_⟩
  · -- the chart at `x`
    have hK : IsCompact (uIcc xa x) := isCompact_uIcc
    have hKJ : uIcc xa x ⊆ Ioo A B := by
      rw [← hJ]; rw [hJ] at hxaJ hx ⊢; exact Set.ordConnected_Ioo.uIcc_subset hxaJ hx
    obtain ⟨κ, hκ, hκJ⟩ := hK.exists_thickening_subset_open isOpen_Ioo hKJ
    set S : Set ℂ := segment ℝ (xa : ℂ) (x : ℂ) with hS
    have hSK : IsCompact S := by
      rw [hS, segment_eq_image']; exact isCompact_Icc.image (by fun_prop)
    have hSO : S ⊆ fl4E ε σ ⁻¹' D := by
      rw [hS, segment_eq_image']
      rintro _ ⟨θ, hθ, rfl⟩
      have e : (xa : ℂ) + θ • ((x : ℂ) - xa) = ((xa + θ * (x - xa) : ℝ) : ℂ) := by
        push_cast; rw [Complex.real_smul]
      have hm : xa + θ * (x - xa) ∈ J := by
        rw [hJ]; apply hKJ
        rw [← segment_eq_uIcc, segment_eq_image']
        exact ⟨θ, hθ, by simp [smul_eq_mul]⟩
      show fl4E ε σ ((xa : ℂ) + θ • ((x : ℂ) - xa)) ∈ D
      rw [e]; exact (hrealD _ hm).1
    obtain ⟨δ, hδ, hδO⟩ := hSK.exists_thickening_subset_open hOσ hSO
    set δ' := min δ r₀ with hδ'
    have hδ'0 : 0 < δ' := lt_min hδ hr₀
    set T : Set ℂ := H ∩ thickening δ' S with hT
    have hTO : ∀ ζ ∈ T, 0 < ζ.im ∧ fl4E ε σ ζ ∈ D := fun ζ hζ =>
      ⟨hζ.1, hδO (thickening_mono (min_le_left _ _) _ hζ.2)⟩
    have hTU : fl4Psi W t ε σ '' T ⊆ hullComp η := by
      set ζ₁ : ℂ := (xa : ℂ) + ((δ' / 2 : ℝ) : ℂ) * I with hζ₁
      have hd : dist ζ₁ (xa : ℂ) = δ' / 2 := by
        rw [hζ₁, dist_eq, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real,
          Real.norm_eq_abs, abs_of_pos (half_pos hδ'0)]
      have hζ₁H : ζ₁ ∈ H := by
        show 0 < ζ₁.im; simp [hζ₁]; exact hδ'0
      have hζ₁T : ζ₁ ∈ T := ⟨hζ₁H, Metric.mem_thickening_iff.2
        ⟨xa, left_mem_segment ℝ _ _, by rw [hd]; linarith⟩⟩
      have hζ₁B : ζ₁ ∈ H ∩ ball (xa : ℂ) r₀ := ⟨hζ₁H, by
        rw [mem_ball, hd]; linarith [min_le_right δ r₀]⟩
      exact fl4_preconn_sub_hullComp
        (fl4_psi_preconn hc hε hη hsub
          ((hHconv.inter ((convex_segment _ _).thickening _)).isPreconnected)
          fun ζ hζ => (hTO ζ hζ).2)
        (fl4_psi_image_sub hc hε hη hsub hσ hTO) ⟨ζ₁, hζ₁T, rfl⟩ (hHb ⟨ζ₁, hζ₁B, rfl⟩)
    refine ⟨min κ δ', lt_min hκ hδ'0, ?_, ?_, ?_⟩
    · -- holomorphy
      have hsubO : ball (x : ℂ) (min κ δ') ⊆ fl4E ε σ ⁻¹' D := fun ζ hζ =>
        hδO (Metric.mem_thickening_iff.2 ⟨x, right_mem_segment ℝ _ _,
          (mem_ball.1 hζ).trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩)
      have hdiff : DifferentiableOn ℂ (fl4E ε σ) univ := by
        unfold fl4E; fun_prop
      exact (FwdHolo.differentiableOn_fwdMap hc.cont hc.tpos.le).comp
        (hdiff.mono (subset_univ _)) hsubO
    · rintro ζ ⟨hζH, hζb⟩
      exact hTU ⟨ζ, ⟨hζH, Metric.mem_thickening_iff.2 ⟨x, right_mem_segment ℝ _ _,
        (mem_ball.1 hζb).trans_le (min_le_right _ _)⟩⟩, rfl⟩
    · intro ζ hζ hζim
      have hre : ζ = ((ζ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hζim])
      have hreJ : ζ.re ∈ J := by
        rw [hJ]; apply hκJ
        refine Metric.mem_thickening_iff.2 ⟨x, right_mem_uIcc, ?_⟩
        rw [Real.dist_eq]
        have h1 : |ζ.re - x| ≤ ‖ζ - x‖ := by
          have := abs_re_le_norm (ζ - x); simpa using this
        rw [← dist_eq] at h1
        exact h1.trans_lt ((mem_ball.1 hζ).trans_le (min_le_left _ _))
      have hA := (hrealD _ hreJ).2
      rw [← hre] at hA
      rw [hUo.frontier_eq]
      exact ⟨hcl hA, fun h => h.1.2 hA⟩
  · -- injectivity
    intro x hx y hy hxy
    have e1 := congrArg F hxy
    simp only [fl4Psi] at e1
    rw [hc.F_fwdMap (hrealD x hx).1, hc.F_fwdMap (hrealD y hy).1, fl4E_real, fl4E_real] at e1
    have hIcc : ∀ z ∈ J, σ * z ∈ Icc 0 π := fun z hz =>
      ⟨h0α.trans hz.1.le, hz.2.le.trans hβπ⟩
    have := flCirc_injOn hε (hIcc x hx) (hIcc y hy) e1
    have h2 := congrArg (σ * ·) this
    simp only [← mul_assoc, hσσ, one_mul] at h2
    exact h2
  · -- the real trace is `η`
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact (hrealD x hx).2
    · rintro p ⟨s, hs, rfl⟩
      have hH := hη.2.2.1 hs
      have : fwdMapInv W t (η s) ∈ flCircArc ε α β := himg ▸ ⟨η s, ⟨s, hs, rfl⟩, rfl⟩
      obtain ⟨φ, hφ, hφe⟩ := this
      have hxJ : σ * φ ∈ J := by
        show σ * (σ * φ) ∈ Ioo α β; rw [← mul_assoc, hσσ, one_mul]; exact hφ
      refine ⟨((σ * φ : ℝ) : ℂ), ⟨σ * φ, hxJ, rfl⟩, ?_⟩
      rw [fl4Psi, fl4E_real, ← mul_assoc, hσσ, one_mul]
      show fwdMap W t (flCirc ε φ) = η s
      have e : flCirc ε φ = F (η s) := by rw [hc.Feq hH]; exact hφe
      rw [e, hc.fwdMap_F hH]

end FieldLawler
end QuantumZipper
