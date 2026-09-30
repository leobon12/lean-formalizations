import QuantumZipper.Proofs.Zipper.FieldLawler4ChainNCmp
import QuantumZipper.Proofs.Zipper.FieldLawler4E0
import QuantumZipper.Proofs.Zipper.FieldLawler4CwdInt
import QuantumZipper.Proofs.Zipper.FieldLawler4WdOuter
import QuantumZipper.Proofs.Zipper.FieldLawler4WdPolar
import QuantumZipper.Proofs.Zipper.FieldLawler3WdSym

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-CHAIN− (2): second symmetry on `Wd` and the flux through `C_R`

Task FL4-CHAIN− (Track A round 4). Steps 4–5 of Field–Lawler's chain (EJP 20 (2015), proof of
Prop. 3.4, p. 9): for the base point `p₀` of `fl4cwd_base`, with `E_σ` an `FL3Arc` chart of
`Wd` along `ηD` and `C_R`-piece index set `fl4WdJ = (A', B')`,
`excR (V ∘ E_σ) J = excR (g ∘ χ_R) (A', B') ≤ fl2FluxR R g`, where `V` is the harmonic measure
of the `C_R` piece in `Wd` and `g` that of `ηD`. The equality is the symmetry of the excursion
measure (`fl3Wd_excR_symm`, via FL4-UWD `fl4_uwd'` and the interval lemmas of FL4-CWD); the
inequality is `fl4hm_excR_le_fluxR`. Sign-agnostic (`σ = ±1`).
-/

noncomputable section

open Set Filter Metric Complex MeasureTheory
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

lemma fl4cn_chart_eq_circ (R x : ℝ) : fl3Chart R (x : ℂ) = flCirc R x := rfl

lemma fl4cn_chart_norm_real {R : ℝ} (hR : 0 < R) (x : ℝ) : ‖fl3Chart R (x : ℂ)‖ = R := by
  rw [fl4cn_chart_eq_circ, flCirc_norm hR]

/-- **Steps 4–5 of FL's chain** (second symmetry on `Wd`, then the flux bound). -/
theorem fl4cn_sym_flux (hc : SideCtx W t F) {R ε α β σ : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (h0α : 0 ≤ α) (hαβ : α < β) (hβπ : β ≤ π) (hσ : σ = 1 ∨ σ = -1)
    (hinj : InjOn (trace W) (Icc 0 t)) (hH : trace W t ∈ H) (hnorm : ‖trace W t‖ = R)
    (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R)
    {η' : ℝ → ℂ} (hη : IsCrosscutH η') {a b : ℝ}
    (ha : Tendsto η' (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η' (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hab : a < b) (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β)
    (hαD : flCirc ε α ∉ H \ fwdHull W t) (hβD : flCirc ε β ∉ H \ fwdHull W t)
    {p₀ : ℂ} (hp : p₀ ∈ fl4WdDom W t R ε α β) (hpU : fwdMap W t p₀ ∈ hullComp η')
    (hcl : flCircArc ε α β ⊆ closure (fl4Wd W t R ε α β p₀))
    (hA : FL3Arc (fl4Wd W t R ε α β p₀) (fl4E ε σ) {x : ℝ | σ * x ∈ Ioo α β})
    (hJint : ∃ A B : ℝ, A < B ∧ fl4WdJ W t R ε α β p₀ = Ioo A B)
    {g : ℂ → ℝ} (hg : IsHarmMeas (fl4Wd W t R ε α β p₀) (flCircArc ε α β) g)
    {V : ℂ → ℝ} (hV : IsHarmMeas (fl4Wd W t R ε α β p₀)
      (fl3Chart R '' (((↑) : ℝ → ℂ) '' fl4WdJ W t R ε α β p₀)) V) :
    excR (V ∘ fl4E ε σ) {x : ℝ | σ * x ∈ Ioo α β} ≤ fl2FluxR R g := by
  have hR : 0 < R := hε.trans hεR
  set Wd := fl4Wd W t R ε α β p₀ with hWddef
  set J := {x : ℝ | σ * x ∈ Ioo α β} with hJdef
  set J' := fl4WdJ W t R ε α β p₀ with hJ'def
  obtain ⟨p, Fu, -, hpfr, hpcl, hpS, -, hpR, hF, -⟩ :=
    fl4_uwd' hc hε hεR h0α hαβ hβπ hinj hH hnorm hlt hη ha hb hab hηD hαD hβD hp hpU
  have hDo : IsOpen Wd := fl4wd_open hc
  have hDb : Wd ⊆ ball 0 R := fl4wd_subset_ball
  have hne : Wd.Nonempty := ⟨p₀, mem_connectedComponentIn hp⟩
  have hpD : p ∉ Wd := fun h => ((hDo.frontier_eq ▸ hpfr) : p ∈ closure Wd \ Wd).2 h
  have hB := fl4wd_chart (W := W) (t := t) (ε := ε) (α := α) (β := β) hR p₀
  have hfrT := fl3Wd_frontierT hDo hDb hne hpD
  have hclarc : closure (flCircArc ε α β) ⊆ frontier Wd :=
    closure_minimal (fl4wd_arc_frontier hcl) isClosed_frontier
  obtain ⟨A, B, hJ, hJc⟩ := fl4cwd_J_eq (α := α) (β := β) hσ
  rw [← hJdef] at hJ
  have hAB : A < B := by
    have : (Ioo A B).Nonempty := by
      rw [← hJ]
      refine ⟨σ * ((α + β) / 2), ?_⟩
      show σ * (σ * ((α + β) / 2)) ∈ Ioo α β
      have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
      rw [← mul_assoc, hσσ, one_mul]; constructor <;> linarith
    exact nonempty_Ioo.1 this
  obtain ⟨A', B', hA'B', hJ'⟩ := hJint
  have hJ'c : Icc A' B' ⊆ Icc 0 π := by
    have h1 : Ioo A' B' ⊆ Ioo 0 π := hJ' ▸ fun θ hθ => hθ.1
    have h2 := closure_mono h1
    rwa [closure_Ioo hA'B'.ne, closure_Ioo Real.pi_pos.ne] at h2
  -- points of the closed arcs
  have hEcl : ∀ x ∈ Icc A B, fl4E ε σ x ∈ closure (flCircArc ε α β) ∧ σ * x ∈ Icc α β := by
    intro x hx
    have hx' : σ * x ∈ Icc α β := by
      have : x ∈ {x : ℝ | σ * x ∈ Icc α β} := hJc ▸ hx
      exact this
    refine ⟨?_, hx'⟩
    rw [fl4E_real]
    have h1 := image_closure_subset_closure_image (f := fun θ : ℝ => (ε : ℂ) * exp (θ * I))
      (s := Ioo α β) (flClArc_cont ε)
    rw [closure_Ioo hαβ.ne] at h1
    exact h1 ⟨σ * x, hx', rfl⟩
  have hChcl : ∀ x ∈ Icc A' B', fl3Chart R x ∈ frontier Wd := by
    intro x hx
    have h1 := image_closure_subset_closure_image (f := fun θ : ℝ => fl3Chart R θ)
      (s := Ioo A' B') ((fl4_chart_continuous R).comp continuous_ofReal)
    rw [closure_Ioo hA'B'.ne] at h1
    have h2 : (fun θ : ℝ => fl3Chart R θ) '' Ioo A' B' ⊆ frontier Wd := by
      rintro _ ⟨θ, hθ, rfl⟩
      exact ((fl4wd_outer_eq hc hε hεR hlt p₀).1 ⟨θ, ⟨θ, (show θ ∈ J' by rw [hJ']; exact hθ), rfl⟩, rfl⟩).1
    exact closure_minimal h2 isClosed_frontier (h1 ⟨x, hx, rfl⟩)
  have hChp : ∀ x : ℝ, fl3Chart R x ≠ p := fun x e => by
    have := fl4cn_chart_norm_real hR x; rw [e] at this; linarith
  have hEp : ∀ x ∈ Icc A B, fl4E ε σ x ≠ p := fun x hx e => hpcl (e ▸ (hEcl x hx).1)
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  -- the two intervals
  have hTfr : ∀ z ∈ frontier Wd, z ≠ p → fl3WdT p z ∈ frontier (fl3WdT p '' Wd) :=
    fun z hz hzp => hfrT ▸ ⟨z, ⟨hz, hzp⟩, rfl⟩
  obtain ⟨a₁, b₁, hab₁, hIA, hIAc⟩ := fl4cwd_interval hF (ψ := fun z => fl3WdT p (fl4E ε σ z))
    hAB (fun x hx => (ContinuousAt.comp (g := fl3WdT p) (f := fun y : ℝ => fl4E ε σ (y : ℂ))
      (fl3WdT_contAt (hEp x hx)) ((fl4E_continuous ε σ).comp continuous_ofReal).continuousAt).continuousWithinAt)
    (fun x hx => hTfr _ (hclarc (hEcl x hx).1) (hEp x hx))
    (fun x hx y hy e => by
      have e1 := fl3WdT_inj (hEp x hx) (hEp y hy) e
      simp only [fl4E_real] at e1
      have h0 : ∀ z ∈ Icc α β, z ∈ Icc 0 π := fun z hz => ⟨h0α.trans hz.1, hz.2.trans hβπ⟩
      exact mul_left_cancel₀ hσ0 (flCirc_injOn hε (h0 _ (hEcl x hx).2) (h0 _ (hEcl y hy).2) e1))
  obtain ⟨c₁, d₁, hcd₁, hIB, hIBc⟩ := fl4cwd_interval hF (ψ := fun z => fl3WdT p (fl3Chart R z))
    hA'B' (fun x _ => (ContinuousAt.comp (g := fl3WdT p) (f := fun y : ℝ => fl3Chart R (y : ℂ))
      (fl3WdT_contAt (hChp x)) ((fl4_chart_continuous R).comp continuous_ofReal).continuousAt).continuousWithinAt)
    (fun x hx => hTfr _ (hChcl x hx) (hChp x))
    (fun x hx y hy e => by
      have e1 := fl3WdT_inj (hChp x) (hChp y) e
      rw [fl4cn_chart_eq_circ, fl4cn_chart_eq_circ] at e1
      exact flCirc_injOn hR (hJ'c hx) (hJ'c hy) e1)
  have hdisj := fl4cwd_interval_sep hF (ψA := fun z => fl3WdT p (fl4E ε σ z))
    (ψB := fun z => fl3WdT p (fl3Chart R z)) hab₁ hcd₁
    (fun x hx => hTfr _ (hclarc (hEcl x hx).1) (hEp x hx)) (fun x hx => hTfr _ (hChcl x hx) (hChp x))
    hIAc hIBc (by
      rw [Set.disjoint_left]
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, e⟩
      have e1 := fl3WdT_inj (hChp y) (hEp x hx) e
      have n1 := fl4cn_chart_norm_real hR y
      rw [e1, fl4E_real, flCirc_norm hε] at n1
      linarith)
  -- the symmetry
  have hEimg := fl4cn_E_image (ε := ε) (α := α) (β := β) hσ
  have hpB : p ∉ closure (fl3Chart R '' (((↑) : ℝ → ℂ) '' J')) := by
    have hsub : fl3Chart R '' (((↑) : ℝ → ℂ) '' J') ⊆ sphere (0 : ℂ) R := by
      rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
      rw [mem_sphere_zero_iff_norm]; exact fl4cn_chart_norm_real hR x
    exact fun h => hpS (closure_minimal hsub isClosed_sphere h)
  have hsym := fl3Wd_excR_symm hDo hDb hne hpfr hF hA hB (by rw [hEimg]; exact hpcl) hpB hab₁
    hcd₁ hdisj (by rw [hJ]; exact hIA) (by rw [← hJ'def, hJ']; exact hIB) (by rw [hEimg]; exact hg) hV
  rw [hsym]
  -- the flux bound
  refine fl4hm_excR_le_fluxR (Wd := Wd) hR hg (fun θ hθ => hθ.1) (fl4WdJ_isOpen R ε α β p₀).measurableSet
    (fun θ hθ => ?_) (fun θ hθ => ?_) (fun _ _ => rfl)
  · obtain ⟨r, hr, -, hmap, hfr⟩ := hB.chart θ hθ
    refine ⟨r, hr, fun z hz hzi => hmap ⟨hzi, hz⟩, fun z hz hzi => ⟨hfr z hz hzi, fun hcl' => ?_⟩⟩
    have h1 := fl4_closure_arc_subset hcl'
    rw [mem_sphere_zero_iff_norm, abs_of_pos hε, fl4_chart_norm hR.le, hzi, neg_zero,
      Real.exp_zero, mul_one] at h1
    linarith
  · obtain ⟨-, ρ, hρ, hsub⟩ := hθ
    filter_upwards [Ioo_mem_nhdsGT (lt_min hρ hR)] with s hs
    refine hsub ⟨?_, ?_⟩
    · rw [mem_ball, fl3Chart_real]
      have e : ∀ u : ℝ, fl2Pt R θ u = fl4Pol (R - u) θ := fun u => rfl
      rw [e, e, fl4Pol_dist, show R - s - (R - 0) = -s by ring, abs_neg, abs_of_pos hs.1]
      exact hs.2.trans_le (min_le_left _ _)
    · have e : fl2Pt R θ s = fl4Pol (R - s) θ := rfl
      rw [mem_ball_zero_iff, e, fl4Pol_norm, abs_of_pos (by linarith [hs.2.trans_le (min_le_right _ _)])]
      linarith [hs.1]

end FieldLawler
end QuantumZipper
