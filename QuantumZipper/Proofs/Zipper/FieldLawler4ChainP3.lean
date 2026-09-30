import QuantumZipper.Proofs.Zipper.FieldLawler4ChainP2
import QuantumZipper.Proofs.Zipper.FieldLawler4E0
import QuantumZipper.Proofs.Zipper.FieldLawler4Gex
import QuantumZipper.Proofs.Zipper.FieldLawler3Asm1
import QuantumZipper.Proofs.Zipper.FieldLawler3Trunc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-CHAIN+ (part 3): Field–Lawler's chain for one crosscut

Field–Lawler, *Escape probability and transience for SLE*, EJP 20 (2015), p. 9:
for a crosscut `η` with positive feet (`0 < a < b`),
`ℰ(η, (−N, 0)) = ℰ(ψ-chart, G_N) ≤ ℰ_{Wd}(ηD, C_R) = ℰ_{Wd}(C_R, ηD) ≤ ℰ_{D₁}(ηD, C_R)`,
then `N → ∞`. Steps: `fl3_first_symm` (first symmetry), `fl4wd_cmp_at` (comparison
`G_N ∘ Z ≤ V`), `fl4chain_symm` (second symmetry), `fl4hm_excR_le_fluxR` (restriction to
`C_R`), `fl3_excR_Iic_eq_iSup` (truncation).
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology Real ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- **FL's chain** (p. 9) for one crosscut `η` with feet `0 < a < b`, given the base point
`p₀` of `fl4cwd_base` and the interval form of the `C_R` piece of `Wd`. -/
theorem fl4chain_bound (hc : SideCtx W t F) (hinj : InjOn (trace W) (Icc 0 t))
    {R ε α β σ : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hH : trace W t ∈ H) (hnorm : ‖trace W t‖ = R)
    (hle : ∀ z ∈ fwdHull W t, ‖z‖ ≤ R) (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R)
    {η : ℝ → ℂ} (hη : IsCrosscutH η) {a b : ℝ} (ha0 : 0 < a)
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hab : a < b) (hηD : fwdMapInv W t '' arcH η = flCircArc ε α β)
    (h0α : 0 ≤ α) (hαβ : α < β) (hβπ : β ≤ π)
    (hαD : flCirc ε α ∉ H \ fwdHull W t) (hβD : flCirc ε β ∉ H \ fwdHull W t)
    (hσ : σ = 1 ∨ σ = -1)
    (hU : FL3Arc (hullComp η) (fl4Psi W t ε σ) {x : ℝ | σ * x ∈ Ioo α β})
    (himg : fl4Psi W t ε σ '' ((fun x : ℝ => (x : ℂ)) '' {x : ℝ | σ * x ∈ Ioo α β}) = arcH η)
    {h : ℂ → ℝ} (hh : IsHarmMeas (hullComp η) (arcH η) h)
    {p₀ : ℂ} (hp : p₀ ∈ fl4WdDom W t R ε α β) (hpU : fwdMap W t p₀ ∈ hullComp η)
    (hcl : flCircArc ε α β ⊆ closure (fl4Wd W t R ε α β p₀))
    (hA : FL3Arc (fl4Wd W t R ε α β p₀) (fl4E ε σ) {x : ℝ | σ * x ∈ Ioo α β})
    (hJint : ∃ A' B' : ℝ, A' < B' ∧ fl4WdJ W t R ε α β p₀ = Ioo A' B')
    {g : ℂ → ℝ} (hg : IsHarmMeas (fl4D₁ W t R \ flCircArc ε α β) (flCircArc ε α β) g) :
    excR h (Iic 0) ≤ fl2FluxR R g := by
  have hR : 0 < R := hε.trans hεR
  set Wd := fl4Wd W t R ε α β p₀ with hWd
  set J := {x : ℝ | σ * x ∈ Ioo α β} with hJdef
  obtain ⟨A', B', hA'B', hJ'⟩ := hJint
  -- the harmonic measures in `Wd`
  obtain ⟨V, hV⟩ := fl4cwd_harm_chart hc hR hαβ.le hαD hβD p₀ (fl4WdJ W t R ε α β p₀)
  have hVo := fl4wd_isHarmMeas_outer hc hε hεR hlt p₀ hV
  have hgW := fl4chain_restrict hc hε hεR hη hηD hαD hβD p₀ hg
  -- the uniformization of `Wd`
  obtain ⟨p, F', -, hpfr, hpcl, hpS, -, -, hF', -⟩ :=
    fl4_uwd' hc hε hεR h0α hαβ hβπ hinj hH hnorm hlt hη ha hb hab hηD hαD hβD hp hpU
  have hsym := fl4chain_symm hc hε hεR h0α hαβ hβπ hσ hp hcl hA hpfr hpcl hpS hF' hA'B' hJ' hV hgW
  have hflux : excR (g ∘ fl3Chart R) (fl4WdJ W t R ε α β p₀) ≤ fl2FluxR R g :=
    fl4hm_excR_le_fluxR hR hg (fun θ hθ => hθ.1)
      (fl4wd_chart (W := W) (t := t) (ε := ε) (α := α) (β := β) hR p₀).meas
      (fun θ hθ => fl4chain_reg hc hε hεR p₀ hθ) (fun θ hθ => fl4chain_pt_mem hR p₀ hθ)
      (fun z _ => rfl)
  -- the vertical approach along `J` and the limits of `V`
  have hev : ∀ x ∈ J, ∀ᶠ y : ℝ in 𝓝[>] 0, fl4E ε σ ((x : ℂ) + (y : ℂ) * I) ∈ Wd := by
    intro x hx
    obtain ⟨r, hr, -, hmap, -⟩ := hA.chart x hx
    have hlt' : ∀ᶠ y : ℝ in 𝓝[>] 0, y < r := nhdsWithin_le_nhds (gt_mem_nhds hr)
    filter_upwards [hlt', self_mem_nhdsWithin] with y hy hy0
    have hy0' : (0 : ℝ) < y := hy0
    refine hmap ⟨show (0 : ℝ) < ((x : ℂ) + (y : ℂ) * I).im by simpa using hy0', ?_⟩
    rw [mem_ball, dist_eq, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real,
      Real.norm_eq_abs, abs_of_pos hy0']
    exact hy
  have hBS : closure (fl3Chart R '' (((↑) : ℝ → ℂ) '' fl4WdJ W t R ε α β p₀)) ⊆ sphere 0 R := by
    refine closure_minimal ?_ isClosed_sphere
    rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    rw [mem_sphere, dist_zero_right, fl4chain_chart_norm hR]
  have hlim : ∀ x ∈ J, ∃ L : ℝ,
      Tendsto (fun y : ℝ => V (fl4E ε σ ((x : ℂ) + (y : ℂ) * I)) / y) (𝓝[>] 0) (𝓝 L) := by
    intro x hx
    obtain ⟨r, hr, hd, hmap, hreal⟩ := hA.chart x hx
    refine fl3reg_harmMeas_zero hV hr (hd.analyticOnNhd isOpen_ball)
      (fun z hz him => hmap ⟨him, hz⟩) (fun z hz him => ⟨hreal z hz him, fun hcl' => ?_⟩)
    have h1 := hBS hcl'
    rw [mem_sphere, dist_zero_right, fl4E_norm hε, him] at h1
    simp at h1
    linarith
  -- the chain for each truncation
  rw [fl3_excR_Iic_eq_iSup]
  refine iSup_le fun N => ?_
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.cast_zero, neg_zero, Ioo_self]
    simp [excR]
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  obtain ⟨G, hG⟩ := fl4_gex hη ha hb (c := -(N : ℝ)) (d := 0) (by linarith)
    (Or.inl (le_min ha0.le (ha0.trans hab).le))
  rw [fl3_first_symm hη ha hb ha0 hab hN' hG hh hU himg]
  have hcmp := fl4wd_cmp_at hc hε hεR hH hnorm hle hlt hη ha0 ha hb hab hηD hp hpU hcl
    (N : ℝ) G V hG hVo (fl4E ε σ) J hA.meas hev hlim
  exact hcmp.trans (hsym.le.trans hflux)

end FieldLawler
end QuantumZipper
