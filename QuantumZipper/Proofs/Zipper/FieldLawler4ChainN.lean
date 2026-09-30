import QuantumZipper.Proofs.Zipper.FieldLawler4ChainNSym
import QuantumZipper.Proofs.Zipper.FieldLawler4CwdHm
import QuantumZipper.Proofs.Zipper.FieldLawler4Sign
import QuantumZipper.Proofs.Zipper.FieldLawler4NegSym
import QuantumZipper.Proofs.Zipper.FieldLawler4Gex
import QuantumZipper.Proofs.Zipper.FieldLawler4Assemble
import QuantumZipper.Proofs.Zipper.FieldLawler4Jint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-CHAIN−: the per-crosscut input `FL4PerArc (-1)` (negative feet)

Task FL4-CHAIN− (Track A round 4). Field–Lawler, *Escape probability and transience for SLE*,
EJP 20 (2015), proof of Prop. 3.4, p. 9 (negative feet "by symmetry"): for an image crosscut
`η` with feet `a, b < 0`,
`excR h [0,∞) = ⨆_N excR h (0,N)` and for each `N`
`excR h (0,N) = excR (G ∘ ψ) J` (first symmetry, `fl4neg_first_symm`)
`≤ excR (V ∘ E_σ) J` (FL (2.1), `fl4wd_cmp_neg_at`)
`= excR (g ∘ χ_R) J' ≤ fl2FluxR R g` (second symmetry and flux, `fl4cn_sym_flux`).
The case `b < a` reduces to `a < b` by reversing `η`.

The `C_R` index set is an interval by `fl4WdJ_eq_Ioo` (task FL4-JINT).
-/

noncomputable section

open Set Filter Metric Complex MeasureTheory
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- **The chain for one negative crosscut with `a < b < 0`.** -/
theorem fl4cn_main (hc : SideCtx W t F) {R ε : ℝ} (hε : 0 < ε)
    (hεR : ε < R) (hinj : InjOn (trace W) (Icc 0 t)) (hH : ∀ u ∈ Ioc 0 t, trace W u ∈ H)
    (hhull : fwdHull W t = trace W '' Ioc 0 t) (hlt : ∀ u ∈ Ico 0 t, ‖trace W u‖ < R)
    (htip : ‖trace W t‖ = R) {η : ℝ → ℂ} {a b : ℝ} {h : ℂ → ℝ} (hη : IsCrosscutH η)
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hab : a < b) (hb0 : b < 0)
    (hsub : arcH η ⊆ {p | ‖fwdMapInv W t p‖ = ε}) (hh : IsHarmMeas (hullComp η) (arcH η) h) :
    ∃ α β : ℝ, (0 < α ∧ α < β ∧ β ≤ π) ∧
      fwdMapInv W t '' arcH η = flCircArc ε α β ∧
      ((ε : ℂ) * exp (α * I) ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ z.re ≤ 0} ∧
        (ε : ℂ) * exp (β * I) ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ z.re ≤ 0}) ∧
      flCircArc ε α β ⊆ H \ trace W '' Ioc 0 t ∧
      ∀ g : ℂ → ℝ, IsHarmMeas (fl4D₁ W t R \ flCircArc ε α β) (flCircArc ε α β) g →
        excR h (Ici 0) ≤ fl2FluxR R g := by
  have hR : 0 < R := hε.trans hεR
  have ha0 : a < 0 := hab.trans hb0
  obtain ⟨α, β, h0α, hαβ, hβπ, himg, hαD, hβD, hfeet, σ, hσ, hU, hψJ⟩ :=
    fl4_arc_chart hc hε hη ha hb hsub
  obtain ⟨hα0, hendα, hendβ⟩ := fl4sign_ends_neg hc hinj hε h0α hαβ hβπ hαD hβD hfeet ha0 hb0
  have harc := fl4sign_arc_subset hc hη himg
  refine ⟨α, β, ⟨hα0, hαβ, hβπ⟩, himg, ⟨hendα, hendβ⟩, harc, fun g hg => ?_⟩
  have hH' : trace W t ∈ H := hH t ⟨hc.tpos, le_rfl⟩
  have hle : ∀ z ∈ fwdHull W t, ‖z‖ ≤ R := by
    rw [hhull]
    rintro _ ⟨s, hs, rfl⟩
    rcases hs.2.lt_or_eq with h' | h'
    · exact (hlt s ⟨hs.1.le, h'⟩).le
    · rw [h', htip]
  obtain ⟨p₀, hp, hpU, hcl, hA⟩ := fl4cwd_base hc hε hεR h0α hαβ hβπ hσ hη himg hU
  set Wd := fl4Wd W t R ε α β p₀ with hWddef
  set J := {x : ℝ | σ * x ∈ Ioo α β} with hJdef
  have hgW := fl4cn_restrict hc hε hεR hαD hβD harc hcl hg
  obtain ⟨V, hV⟩ := fl4cwd_harm_chart hc hR hαβ.le hαD hβD p₀ (fl4WdJ W t R ε α β p₀)
  have hVout := fl4wd_isHarmMeas_outer hc hε hεR hlt p₀ hV
  have hflux := fl4cn_sym_flux hc hε hεR h0α hαβ hβπ hσ hinj hH' htip hlt hη ha hb hab himg
    hαD hβD hp hpU hcl hA
    (fl4WdJ_eq_Ioo hc hε hεR hlt htip hH' hη ha hb hab himg hp hpU) hgW hV
  -- the chart `E_σ` near `J`
  have hEan : ∀ x : ℝ, ∀ r : ℝ, AnalyticOnNhd ℂ (fl4E ε σ) (ball (x : ℂ) r) := fun _ _ z _ =>
    Differentiable.analyticAt (by unfold fl4E; fun_prop) z
  have hψev : ∀ x ∈ J, ∀ᶠ y : ℝ in 𝓝[>] 0, fl4E ε σ ((x : ℂ) + (y : ℂ) * I) ∈ Wd := by
    intro x hx
    obtain ⟨r, hr, -, hmap, -⟩ := hA.chart x hx
    filter_upwards [Ioo_mem_nhdsGT hr] with y hy
    refine hmap ⟨?_, ?_⟩
    · show 0 < ((x : ℂ) + (y : ℂ) * I).im
      simpa using hy.1
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        norm_real, Real.norm_eq_abs, abs_of_pos hy.1]
      exact hy.2
  have hVlim : ∀ x ∈ J, ∃ L : ℝ,
      Tendsto (fun y : ℝ => V (fl4E ε σ ((x : ℂ) + (y : ℂ) * I)) / y) (𝓝[>] 0) (𝓝 L) := by
    intro x hx
    obtain ⟨r, hr, -, hmap, hfr⟩ := hA.chart x hx
    refine fl3reg_harmMeas_zero hVout hr (hEan x r) (fun z hz hzi => hmap ⟨hzi, hz⟩)
      fun z hz hzi => ⟨hfr z hz hzi, fun hcl' => ?_⟩
    have h1 : closure (frontier Wd ∩ sphere 0 R) ⊆ sphere (0 : ℂ) R :=
      closure_minimal inter_subset_right isClosed_sphere
    have h2 := h1 hcl'
    rw [mem_sphere_zero_iff_norm, fl4E_norm hε, hzi, mul_zero, neg_zero, Real.exp_zero,
      mul_one] at h2
    linarith
  rw [fl4_excR_Ici_eq_iSup]
  refine iSup_le fun N => ?_
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [excR]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨G, hG⟩ := fl4_gex hη ha hb (c := 0) (d := N) hNpos
    (Or.inr (max_le ha0.le hb0.le))
  rw [fl4neg_first_symm hη ha hb hb0 hab hNpos hG hh hU hψJ]
  have hcmp := fl4wd_cmp_neg_at hc hε hεR hH' htip hle hlt hη hb0 ha hb hab himg hp hpU hcl
    N G V hG hVout (fl4E ε σ) J hA.meas hψev hVlim
  exact (le_of_eq_of_le rfl hcmp).trans hflux

/-- **`FL4PerArc (-1)`**: Field–Lawler's per-crosscut chain for negative feet. -/
theorem fl4_perArc_neg : FL4PerArc (-1) := by
  intro W hW hW0 t R ε ht hR hε hεR4 htr0 hcont hinj hH hhull hlt htip _ η a b h hη ha hb
    hsa hsb hsub hh
  obtain ⟨F, hc⟩ := flWire_ctx hW hW0 ht hR htr0 hcont hinj hH hhull htip
  have hεR : ε < R := by linarith
  have ha0 : a < 0 := by linarith
  have hb0 : b < 0 := by linarith
  have key : ∀ {η' : ℝ → ℂ} {a' b' : ℝ}, IsCrosscutH η' → Tendsto η' (𝓝[>] 0) (𝓝 (a' : ℂ)) →
      Tendsto η' (𝓝[<] 1) (𝓝 (b' : ℂ)) → a' < b' → b' < 0 → arcH η' = arcH η →
      hullComp η' = hullComp η → _ := fun {η'} {a'} {b'} hη' ha' hb' hab' hb0' e1 e2 =>
    fl4cn_main hc hε hεR hinj hH hhull hlt htip hη' ha' hb' hab' hb0' (e1 ▸ hsub)
      (e1 ▸ e2 ▸ hh)
  have hne := fl4_feet_ne hc hε hη ha hb hsub
  obtain ⟨α, β, ⟨hα0, hαβ, hβπ⟩, himg, ⟨hendα, hendβ⟩, harc, hflux⟩ :
      ∃ α β : ℝ, (0 < α ∧ α < β ∧ β ≤ π) ∧
      fwdMapInv W t '' arcH η = flCircArc ε α β ∧
      ((ε : ℂ) * exp (α * I) ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ z.re ≤ 0} ∧
        (ε : ℂ) * exp (β * I) ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ z.re ≤ 0}) ∧
      flCircArc ε α β ⊆ H \ trace W '' Ioc 0 t ∧
      ∀ g : ℂ → ℝ, IsHarmMeas (fl4D₁ W t R \ flCircArc ε α β) (flCircArc ε α β) g →
        excR h (Ici 0) ≤ fl2FluxR R g := by
    rcases hne.lt_or_gt with hab | hba
    · exact key hη ha hb hab hb0 rfl rfl
    · have e1 : arcH (fun s => η (1 - s)) = arcH η := fl_rev_arcH η
      have e2 : hullComp (fun s => η (1 - s)) = hullComp η := by
        unfold hullComp; rw [fl_rev_arcH]
      have := key (fl_rev_crosscut hη) (hb.comp fl_rev_tendsto0) (ha.comp fl_rev_tendsto1) hba
        ha0 e1 e2
      rwa [e1] at this
  have hend : ∀ z : ℂ, z ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ z.re ≤ 0} →
      z ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ 0 ≤ -1 * z.re} := by
    rintro z (hz | ⟨h1, h2⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨h1, by linarith⟩
  refine ⟨α, β, ?_, himg, ⟨hend _ hendα, hend _ hendβ⟩, harc, fun g hg => ?_⟩
  · simp only [show ¬ (0 : ℝ) < -1 by norm_num, ↓reduceIte]
    exact ⟨hα0, hαβ, hβπ⟩
  · simp only [show ¬ (0 : ℝ) < -1 by norm_num, ↓reduceIte]
    exact hflux g hg

end FieldLawler
end QuantumZipper
