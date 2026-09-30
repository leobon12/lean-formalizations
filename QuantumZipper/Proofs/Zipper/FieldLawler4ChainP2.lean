import QuantumZipper.Proofs.Zipper.FieldLawler4ChainP1
import QuantumZipper.Proofs.Zipper.FieldLawler4CwdArc
import QuantumZipper.Proofs.Zipper.FieldLawler4CwdInt
import QuantumZipper.Proofs.Zipper.FieldLawler3WdSym

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-CHAIN+ (part 2): the second symmetry in `Wd`

Field–Lawler, EJP 20 (2015), p. 9: `ℰ_{Wd}(ηD, C_R) = ℰ_{Wd}(C_R, ηD)` (symmetry of the
excursion measure, FL (2.1)), in the form of `fl3Wd_excR_symm` with arc `A = ηD` in the chart
`fl4E ε σ` and arc `B = ∂Wd ∩ C_R` in the chart `fl3Chart R`, both mapped to real intervals by
the uniformization of `fl4_uwd'` (`fl4cwd_interval`, `fl4cwd_interval_sep`).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology Real ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

lemma fl4chain_circ_mem_closure {ε α β θ : ℝ} (hαβ : α < β) (hθ : θ ∈ Icc α β) :
    flCirc ε θ ∈ closure (flCircArc ε α β) := by
  have h : θ ∈ closure (Ioo α β) := by rw [closure_Ioo hαβ.ne]; exact hθ
  exact (flClArc_cont ε).continuousWithinAt.mem_closure_image h

lemma fl4chain_E_image {ε α β σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    fl4E ε σ '' (((↑) : ℝ → ℂ) '' {x : ℝ | σ * x ∈ Ioo α β}) = flCircArc ε α β := by
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [fl4E_real]; exact ⟨σ * x, hx, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨((σ * θ : ℝ) : ℂ), ⟨σ * θ, ?_, rfl⟩, ?_⟩
    · show σ * (σ * θ) ∈ Ioo α β
      rw [← mul_assoc, hσσ, one_mul]; exact hθ
    · rw [fl4E_real, ← mul_assoc, hσσ, one_mul]; rfl

lemma fl4chain_E_norm {ε σ : ℝ} (hε : 0 < ε) (x : ℝ) : ‖fl4E ε σ (x : ℂ)‖ = ε := by
  rw [fl4E_norm hε]; simp

lemma fl4chain_chart_norm {R : ℝ} (hR : 0 < R) (x : ℝ) : ‖fl3Chart R (x : ℂ)‖ = R := by
  rw [fl4_chart_norm hR.le]; simp

/-- A boundary arc of `D` avoiding `p`, parametrized injectively on `[A, B]`, goes to an
interval under `Re F ∘ T_p`. -/
lemma fl4chain_int {D : Set ℂ} {p : ℂ} {R₀ : ℝ} (hDo : IsOpen D) (hDb : D ⊆ ball 0 R₀)
    (hne : D.Nonempty) (hpD : p ∉ D) {F' : ℂ → ℂ} (hF : FL3Unif (fl3WdT p '' D) F')
    {ψ : ℂ → ℂ} {A B : ℝ} (hAB : A < B) (hψc : Continuous fun x : ℝ => ψ x)
    (hfr : ∀ x ∈ Icc A B, ψ x ∈ frontier D) (hp : ∀ x ∈ Icc A B, ψ x ≠ p)
    (hinj : InjOn (fun x : ℝ => ψ x) (Icc A B)) :
    (∀ x ∈ Icc A B, fl3WdT p (ψ x) ∈ frontier (fl3WdT p '' D)) ∧
    ∃ a b : ℝ, a < b ∧ (fun x : ℝ => (F' (fl3WdT p (ψ x))).re) '' Ioo A B = Ioo a b ∧
      (fun x : ℝ => (F' (fl3WdT p (ψ x))).re) '' Icc A B = Icc a b := by
  have hfrT : ∀ x ∈ Icc A B, fl3WdT p (ψ x) ∈ frontier (fl3WdT p '' D) := fun x hx => by
    rw [fl3Wd_frontierT hDo hDb hne hpD]; exact ⟨ψ x, ⟨hfr x hx, hp x hx⟩, rfl⟩
  refine ⟨hfrT, fl4cwd_interval hF (ψ := fun z => fl3WdT p (ψ z)) hAB ?_ hfrT ?_⟩
  · intro x hx
    exact ((fl3WdT_contAt (hp x hx)).comp (f := fun x : ℝ => ψ x) hψc.continuousAt).continuousWithinAt
  · exact fun x hx y hy h => hinj hx hy (fl3WdT_inj (hp x hx) (hp y hy) h)

/-- **Second symmetry** (FL p. 9) in `Wd`, for the arc chart `fl4E ε σ` and the `C_R` chart. -/
theorem fl4chain_symm (hc : SideCtx W t F) {R ε α β σ : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (h0α : 0 ≤ α) (hαβ : α < β) (hβπ : β ≤ π) (hσ : σ = 1 ∨ σ = -1) {p₀ : ℂ}
    (hp₀ : p₀ ∈ fl4WdDom W t R ε α β)
    (hcl : flCircArc ε α β ⊆ closure (fl4Wd W t R ε α β p₀))
    (hA : FL3Arc (fl4Wd W t R ε α β p₀) (fl4E ε σ) {x : ℝ | σ * x ∈ Ioo α β})
    {p : ℂ} {F' : ℂ → ℂ} (hpfr : p ∈ frontier (fl4Wd W t R ε α β p₀))
    (hpcl : p ∉ closure (flCircArc ε α β)) (hpS : p ∉ sphere 0 R)
    (hF : FL3Unif (fl3WdT p '' fl4Wd W t R ε α β p₀) F')
    {A' B' : ℝ} (hA'B' : A' < B') (hJ' : fl4WdJ W t R ε α β p₀ = Ioo A' B')
    {V g : ℂ → ℝ}
    (hV : IsHarmMeas (fl4Wd W t R ε α β p₀) (fl3Chart R '' (((↑) : ℝ → ℂ) ''
      fl4WdJ W t R ε α β p₀)) V)
    (hg : IsHarmMeas (fl4Wd W t R ε α β p₀) (flCircArc ε α β) g) :
    excR (V ∘ fl4E ε σ) {x : ℝ | σ * x ∈ Ioo α β} =
      excR (g ∘ fl3Chart R) (fl4WdJ W t R ε α β p₀) := by
  have hR : 0 < R := hε.trans hεR
  set Wd := fl4Wd W t R ε α β p₀ with hWd
  have hDo : IsOpen Wd := fl4wd_open hc
  have hDb : Wd ⊆ ball 0 R := fl4wd_subset_ball
  have hne : Wd.Nonempty := ⟨p₀, mem_connectedComponentIn hp₀⟩
  have hpD : p ∉ Wd := fun h => hpfr.2 (by rw [hDo.interior_eq]; exact h)
  have hB := fl4wd_chart (W := W) (t := t) (ε := ε) (α := α) (β := β) hR p₀
  have hclfr : closure (flCircArc ε α β) ⊆ frontier Wd :=
    closure_minimal (fl4wd_arc_frontier hcl) isClosed_frontier
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  -- the arc `A`
  obtain ⟨A, B, hJ, hJc⟩ := fl4cwd_J_eq (α := α) (β := β) hσ
  have hAB : A < B := by
    have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hm : σ * ((α + β) / 2) ∈ {x : ℝ | σ * x ∈ Ioo α β} := by
      show σ * (σ * ((α + β) / 2)) ∈ Ioo α β
      rw [← mul_assoc, hσσ, one_mul]; constructor <;> linarith
    rw [hJ] at hm; exact hm.1.trans hm.2
  have hAmem : ∀ x ∈ Icc A B, σ * x ∈ Icc α β := fun x hx => by
    rw [← hJc] at hx; exact hx
  have hAcl : ∀ x ∈ Icc A B, fl4E ε σ (x : ℂ) ∈ closure (flCircArc ε α β) := fun x hx => by
    rw [fl4E_real]; exact fl4chain_circ_mem_closure hαβ (hAmem x hx)
  have hAp : ∀ x ∈ Icc A B, fl4E ε σ (x : ℂ) ≠ p := fun x hx h => hpcl (h ▸ hAcl x hx)
  have hAinj : InjOn (fun x : ℝ => fl4E ε σ (x : ℂ)) (Icc A B) := by
    intro x hx y hy h
    simp only [fl4E_real] at h
    have h1 := hAmem x hx; have h2 := hAmem y hy
    have := flCirc_injOn hε ⟨h0α.trans h1.1, h1.2.trans hβπ⟩ ⟨h0α.trans h2.1, h2.2.trans hβπ⟩ h
    exact mul_left_cancel₀ hσ0 this
  obtain ⟨hfrA, a, b, hab, hIA, hIAc⟩ := fl4chain_int hDo hDb hne hpD hF hAB
    ((fl4E_continuous ε σ).comp continuous_ofReal)
    (fun x hx => hclfr (hAcl x hx)) hAp hAinj
  -- the arc `B`
  have hJ0 : Icc A' B' ⊆ Icc 0 π := by
    rw [← closure_Ioo hA'B'.ne, ← hJ', ← closure_Ioo (by positivity : (0 : ℝ) ≠ π)]
    exact closure_mono fun θ hθ => hθ.1
  have hBfr0 : fl3Chart R '' (((↑) : ℝ → ℂ) '' fl4WdJ W t R ε α β p₀) ⊆ frontier Wd := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨r, hr, -, -, hreal⟩ := hB.chart x hx
    exact hreal x (mem_ball_self hr) (by simp)
  have hBcl : ∀ x ∈ Icc A' B', fl3Chart R (x : ℂ) ∈
      closure (fl3Chart R '' (((↑) : ℝ → ℂ) '' fl4WdJ W t R ε α β p₀)) := fun x hx => by
    have h : x ∈ closure (fl4WdJ W t R ε α β p₀) := by
      rw [hJ', closure_Ioo hA'B'.ne]; exact hx
    rw [image_image]
    exact ((fl4_chart_continuous R).comp continuous_ofReal).continuousWithinAt.mem_closure_image h
  have hBS : closure (fl3Chart R '' (((↑) : ℝ → ℂ) '' fl4WdJ W t R ε α β p₀)) ⊆ sphere 0 R := by
    refine closure_minimal ?_ isClosed_sphere
    rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    rw [mem_sphere, dist_zero_right, fl4chain_chart_norm hR]
  have hBp : ∀ x ∈ Icc A' B', fl3Chart R (x : ℂ) ≠ p := fun x hx h =>
    hpS (h ▸ hBS (hBcl x hx))
  have hBinj : InjOn (fun x : ℝ => fl3Chart R (x : ℂ)) (Icc A' B') :=
    fun x hx y hy h => flCirc_injOn hR (hJ0 hx) (hJ0 hy) h
  obtain ⟨hfrB, c, d, hcd, hIB, hIBc⟩ := fl4chain_int hDo hDb hne hpD hF hA'B'
    ((fl4_chart_continuous R).comp continuous_ofReal)
    (fun x hx => closure_minimal hBfr0 isClosed_frontier (hBcl x hx)) hBp hBinj
  have hdisj : b < c ∨ d < a := by
    refine fl4cwd_interval_sep hF (ψA := fun z => fl3WdT p (fl4E ε σ z))
      (ψB := fun z => fl3WdT p (fl3Chart R z)) hab hcd hfrA hfrB hIAc hIBc ?_
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have e := fl3WdT_inj (hBp y hy) (hAp x hx) hxy
    have := congrArg norm e
    rw [fl4chain_chart_norm hR, fl4chain_E_norm hε] at this
    linarith
  have hpA : p ∉ closure (fl4E ε σ '' (((↑) : ℝ → ℂ) '' {x : ℝ | σ * x ∈ Ioo α β})) := by
    rw [fl4chain_E_image hσ]; exact hpcl
  have hpB : p ∉ closure (fl3Chart R '' (((↑) : ℝ → ℂ) '' fl4WdJ W t R ε α β p₀)) :=
    fun h => hpS (hBS h)
  have hgA : IsHarmMeas Wd (fl4E ε σ '' (((↑) : ℝ → ℂ) '' {x : ℝ | σ * x ∈ Ioo α β})) g := by
    rw [fl4chain_E_image hσ]; exact hg
  exact fl3Wd_excR_symm hDo hDb hne hpfr hF hA hB hpA hpB hab hcd hdisj
    (by rw [hJ]; exact hIA) (by rw [hJ']; exact hIB) hgA hV

end FieldLawler
end QuantumZipper
