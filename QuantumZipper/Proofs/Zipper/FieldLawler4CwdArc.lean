import QuantumZipper.Proofs.Zipper.FieldLawler4Wd
import QuantumZipper.Proofs.Zipper.FieldLawler4ArcChart

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-CWD (C1): the circle chart of `Wd` along `ηD`

Task FL4-CWD. For the sign `σ` of `fl4_arc_chart` (the chart `ψ_σ = Z_t ∘ E_σ`,
`E_σ(ζ) = ε e^{iσζ}`, of `hullComp η'` along `η'`), the plain circle chart `E_σ` is an `FL3Arc`
chart of `Wd = fl4Wd W t R ε α β p₀` over `{x | σ x ∈ (α, β)}`, for a base point `p₀` chosen on
the `σ` side of the arc (`fl4cwd_base`). This `p₀` has the three properties used by
`fl4wd_cmp` (`p₀ ∈ fl4WdDom`, `Z p₀ ∈ hullComp η'`, `ηD ⊆ closure Wd`).

Own elementary argument (FL, EJP 20 (2015), p. 9, leave the domain implicit): as in
`fl4_arc_chart`, `E_σ` maps `ℍ ∩ thickening δ [x₀, x]` (joined with a half-disc at the anchor
`x₀`) into `fl4WdDom`, preconnectedly and through `p₀ = E_σ(x₀ + i y₀)`, hence into `Wd`.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

lemma fl4cwd_J_eq {σ α β : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ A B : ℝ, {x : ℝ | σ * x ∈ Ioo α β} = Ioo A B ∧ {x : ℝ | σ * x ∈ Icc α β} = Icc A B := by
  rcases hσ with rfl | rfl
  · exact ⟨α, β, by ext x; simp, by ext x; simp⟩
  · refine ⟨-β, -α, ?_, ?_⟩ <;> ext x <;> simp only [mem_ofPred_eq, mem_Ioo, mem_Icc] <;>
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

lemma fl4cwd_E_mem_dom {R ε α β σ : ℝ} (hε : 0 < ε) (hσ : σ = 1 ∨ σ = -1) {ζ : ℂ}
    (hζ : 0 < ζ.im) (h : fl4E ε σ ζ ∈ (H \ fwdHull W t) ∩ ball 0 R) :
    fl4E ε σ ζ ∈ fl4WdDom W t R ε α β := by
  refine fl4_mem_dom hε h ?_
  rw [fl4E_norm hε]
  intro e
  have h1 : Real.exp (-(σ * ζ.im)) = 1 := mul_left_cancel₀ hε.ne' (e.trans (mul_one ε).symm)
  rw [Real.exp_eq_one_iff] at h1
  rcases hσ with rfl | rfl <;> linarith

/-- **(C1)** A base point `p₀` on the `σ` side of `ηD` whose component `Wd` has `E_σ` as an
`FL3Arc` chart over `{x | σ x ∈ (α, β)}`. -/
theorem fl4cwd_base (hc : SideCtx W t F) {R ε α β σ : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (h0α : 0 ≤ α) (hαβ : α < β) (hβπ : β ≤ π) (hσ : σ = 1 ∨ σ = -1)
    {η' : ℝ → ℂ} (hη : IsCrosscutH η') (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β)
    (hU : FL3Arc (hullComp η') (fl4Psi W t ε σ) {x : ℝ | σ * x ∈ Ioo α β}) :
    ∃ p₀ ∈ fl4WdDom W t R ε α β, fwdMap W t p₀ ∈ hullComp η' ∧
      flCircArc ε α β ⊆ closure (fl4Wd W t R ε α β p₀) ∧
      FL3Arc (fl4Wd W t R ε α β p₀) (fl4E ε σ) {x : ℝ | σ * x ∈ Ioo α β} := by
  set J := {x : ℝ | σ * x ∈ Ioo α β} with hJdef
  obtain ⟨A, B, hJ, -⟩ := fl4cwd_J_eq (α := α) (β := β) hσ
  rw [← hJdef] at hJ
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set O' := (H \ fwdHull W t) ∩ ball (0 : ℂ) R with hO'
  have hO'o : IsOpen O' := hc.isOpen_dom.inter isOpen_ball
  have hAO' := fl4_arc_subset hc hεR hε hη hηD
  have hrealA : ∀ y ∈ J, fl4E ε σ (y : ℂ) ∈ flCircArc ε α β := fun y hy => by
    rw [fl4E_real]; exact fl4Pol_mem_arc hy
  have hOσ : IsOpen (fl4E ε σ ⁻¹' O') := hO'o.preimage (fl4E_continuous ε σ)
  have hHconv : Convex ℝ H := by
    have : H = Complex.imLm ⁻¹' Ioi 0 := rfl
    rw [this]; exact (convex_Ioi 0).linear_preimage _
  -- the anchor
  set xa : ℝ := σ * ((α + β) / 2) with hxa
  have hxaJ : xa ∈ J := by
    show σ * xa ∈ Ioo α β
    rw [hxa, ← mul_assoc, hσσ, one_mul]; constructor <;> linarith
  obtain ⟨r₀, hr₀, -, hmap₀, -⟩ := hU.chart xa hxaJ
  obtain ⟨r₁, hr₁, hr₁O⟩ := Metric.isOpen_iff.1 hOσ (xa : ℂ) (hAO' (hrealA xa hxaJ))
  set y₀ := min r₀ r₁ / 2 with hy₀
  have hy₀pos : 0 < y₀ := half_pos (lt_min hr₀ hr₁)
  set ζ₀ : ℂ := (xa : ℂ) + (y₀ : ℂ) * I with hζ₀
  have hζ₀d : dist ζ₀ (xa : ℂ) = y₀ := by
    rw [hζ₀, dist_eq, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real,
      Real.norm_eq_abs, abs_of_pos hy₀pos]
  have hζ₀H : ζ₀ ∈ H := by show 0 < ζ₀.im; simp [hζ₀, hy₀pos]
  have hζ₀1 : ζ₀ ∈ ball (xa : ℂ) r₁ := by
    rw [mem_ball, hζ₀d, hy₀]; linarith [min_le_right r₀ r₁]
  have hζ₀0 : ζ₀ ∈ ball (xa : ℂ) r₀ := by
    rw [mem_ball, hζ₀d, hy₀]; linarith [min_le_left r₀ r₁]
  set p₀ := fl4E ε σ ζ₀ with hp₀
  have hdom : ∀ ζ : ℂ, ζ ∈ H → ζ ∈ fl4E ε σ ⁻¹' O' → fl4E ε σ ζ ∈ fl4WdDom W t R ε α β :=
    fun ζ h1 h2 => fl4cwd_E_mem_dom hε hσ h1 h2
  have hp₀D : p₀ ∈ fl4WdDom W t R ε α β := hdom ζ₀ hζ₀H (hr₁O hζ₀1)
  -- sets through `ζ₀` mapped into `fl4WdDom` land in `Wd`
  have hinW : ∀ T : Set ℂ, IsPreconnected T → ζ₀ ∈ T → T ⊆ H ∩ fl4E ε σ ⁻¹' O' →
      fl4E ε σ '' T ⊆ fl4Wd W t R ε α β p₀ := fun T hT hζT hTs =>
    (hT.image _ (fl4E_continuous ε σ).continuousOn).subset_connectedComponentIn
      ⟨ζ₀, hζT, rfl⟩ (by rintro _ ⟨ζ, hζ, rfl⟩; exact hdom ζ (hTs hζ).1 (hTs hζ).2)
  -- local charts
  have hloc : ∀ x ∈ J, ∃ r > 0, (∀ ζ ∈ H ∩ ball (x : ℂ) r, fl4E ε σ ζ ∈ fl4Wd W t R ε α β p₀) ∧
      ∀ ζ ∈ ball (x : ℂ) r, ζ.im = 0 → ζ.re ∈ J := by
    intro x hx
    have hK : IsCompact (uIcc xa x) := isCompact_uIcc
    have hKJ : uIcc xa x ⊆ Ioo A B := by
      rw [← hJ]; rw [hJ] at hxaJ hx ⊢; exact Set.ordConnected_Ioo.uIcc_subset hxaJ hx
    obtain ⟨κ, hκ, hκJ⟩ := hK.exists_thickening_subset_open isOpen_Ioo hKJ
    set S : Set ℂ := segment ℝ (xa : ℂ) (x : ℂ) with hS
    have hSK : IsCompact S := by
      rw [hS, segment_eq_image']; exact isCompact_Icc.image (by fun_prop)
    have hSO : S ⊆ fl4E ε σ ⁻¹' O' := by
      rw [hS, segment_eq_image']
      rintro _ ⟨θ, hθ, rfl⟩
      have e : (xa : ℂ) + θ • ((x : ℂ) - xa) = ((xa + θ * (x - xa) : ℝ) : ℂ) := by
        push_cast; rw [Complex.real_smul]
      have hm : xa + θ * (x - xa) ∈ J := by
        rw [hJ]; apply hKJ
        rw [← segment_eq_uIcc, segment_eq_image']
        exact ⟨θ, hθ, by simp [smul_eq_mul]⟩
      show fl4E ε σ ((xa : ℂ) + θ • ((x : ℂ) - xa)) ∈ O'
      rw [e]; exact hAO' (hrealA _ hm)
    obtain ⟨δ, hδ, hδO⟩ := hSK.exists_thickening_subset_open hOσ hSO
    set T : Set ℂ := (H ∩ thickening δ S) ∪ (H ∩ ball (xa : ℂ) r₁) with hT
    set m := min δ r₁ / 2 with hm
    have hmpos : 0 < m := half_pos (lt_min hδ hr₁)
    set ζ₁ : ℂ := (xa : ℂ) + (m : ℂ) * I with hζ₁
    have hζ₁d : dist ζ₁ (xa : ℂ) = m := by
      rw [hζ₁, dist_eq, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real,
        Real.norm_eq_abs, abs_of_pos hmpos]
    have hζ₁H : ζ₁ ∈ H := by show 0 < ζ₁.im; simp [hζ₁, hmpos]
    have hTc : IsPreconnected T := by
      refine IsPreconnected.union ζ₁ ⟨hζ₁H, Metric.mem_thickening_iff.2
        ⟨xa, left_mem_segment ℝ _ _, by rw [hζ₁d, hm]; linarith [min_le_left δ r₁]⟩⟩
        ⟨hζ₁H, by rw [mem_ball, hζ₁d, hm]; linarith [min_le_right δ r₁]⟩
        (hHconv.inter ((convex_segment _ _).thickening _)).isPreconnected
        (hHconv.inter (convex_ball _ _)).isPreconnected
    have hTs : T ⊆ H ∩ fl4E ε σ ⁻¹' O' := by
      rintro ζ (h | h)
      · exact ⟨h.1, hδO h.2⟩
      · exact ⟨h.1, hr₁O h.2⟩
    have hTW := hinW T hTc (Or.inr ⟨hζ₀H, hζ₀1⟩) hTs
    refine ⟨min κ δ, lt_min hκ hδ, fun ζ hζ => hTW ⟨ζ, Or.inl ⟨hζ.1,
      Metric.mem_thickening_iff.2 ⟨x, right_mem_segment ℝ _ _,
        (mem_ball.1 hζ.2).trans_le (min_le_right _ _)⟩⟩, rfl⟩, fun ζ hζ hζim => ?_⟩
    rw [hJ]; apply hκJ
    refine Metric.mem_thickening_iff.2 ⟨x, right_mem_uIcc, ?_⟩
    rw [Real.dist_eq]
    have h1 : |ζ.re - x| ≤ ‖ζ - x‖ := by
      have := abs_re_le_norm (ζ - x); simpa using this
    rw [← dist_eq] at h1
    exact h1.trans_lt ((mem_ball.1 hζ).trans_le (min_le_left _ _))
  -- the arc lies in the closure of `Wd`
  have hcl : flCircArc ε α β ⊆ closure (fl4Wd W t R ε α β p₀) := by
    rintro _ ⟨θ, hθ, rfl⟩
    have hyJ : σ * θ ∈ J := by
      show σ * (σ * θ) ∈ Ioo α β; rw [← mul_assoc, hσσ, one_mul]; exact hθ
    have e : (ε : ℂ) * exp (θ * I) = fl4E ε σ ((σ * θ : ℝ) : ℂ) := by
      rw [fl4E_real, ← mul_assoc, hσσ, one_mul]; rfl
    show (ε : ℂ) * exp (θ * I) ∈ _
    rw [e, Metric.mem_closure_iff]
    intro e' he'
    obtain ⟨r, hr, hin, -⟩ := hloc _ hyJ
    obtain ⟨r', hr', hr'd⟩ := Metric.continuousAt_iff.1
      ((fl4E_continuous ε σ).continuousAt (x := (((σ * θ : ℝ)) : ℂ))) e' he'
    set s := min r r' / 2 with hs
    have hspos : 0 < s := half_pos (lt_min hr hr')
    set ζ : ℂ := (((σ * θ : ℝ)) : ℂ) + (s : ℂ) * I with hζ
    have hζd : dist ζ (((σ * θ : ℝ)) : ℂ) = s := by
      rw [hζ, dist_eq, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real,
        Real.norm_eq_abs, abs_of_pos hspos]
    have hζH : ζ ∈ H := by show 0 < ζ.im; simp [hζ, hspos]
    refine ⟨fl4E ε σ ζ, hin ζ ⟨hζH, by rw [mem_ball, hζd, hs]; linarith [min_le_left r r']⟩, ?_⟩
    rw [dist_comm]
    exact hr'd (by rw [hζd, hs]; linarith [min_le_right r r'])
  have hfr := fl4wd_arc_frontier hcl
  refine ⟨p₀, hp₀D, hmap₀ ⟨hζ₀H, hζ₀0⟩, hcl, ⟨by rw [hJ]; exact measurableSet_Ioo,
    fun x hx => ?_, ?_⟩⟩
  · obtain ⟨r, hr, hin, hre⟩ := hloc x hx
    refine ⟨r, hr, (by unfold fl4E; fun_prop : Differentiable ℂ (fl4E ε σ)).differentiableOn,
      fun ζ hζ => hin ζ hζ, fun ζ hζ hζim => ?_⟩
    have e : ζ = ((ζ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hζim])
    rw [e]; exact hfr (hrealA _ (hre ζ hζ hζim))
  · intro x hx y hy hxy
    simp only [fl4E_real] at hxy
    have hIcc : ∀ z ∈ J, σ * z ∈ Icc 0 π := fun z hz =>
      ⟨h0α.trans hz.1.le, hz.2.le.trans hβπ⟩
    have := flCirc_injOn hε (hIcc x hx) (hIcc y hy) hxy
    have h2 := congrArg (σ * ·) this
    simp only [← mul_assoc, hσσ, one_mul] at h2
    exact h2

end FieldLawler
end QuantumZipper
