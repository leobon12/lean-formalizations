import QuantumZipper.Proofs.Zipper.FieldLawler4CwdHm
import QuantumZipper.Proofs.Zipper.FieldLawler4Hm
import QuantumZipper.Proofs.Zipper.FieldLawler4L33

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-CHAIN+ (part 1): glue for Field–Lawler's per-crosscut chain

Field–Lawler, *Escape probability and transience for SLE*, EJP 20 (2015), p. 9: the chain
`ℰ(η, (−∞,0]) ≤ ℰ_{Wd}(ηD, C_R) ≤ ℰ_{D₁}(ηD, C_R)`. Here:

* `fl4wd_cmp_at`: `fl4wd_cmp` at a prescribed base point `p₀` (same proof);
* `fl4chain_closure_arc`: `closure C_ε(α,β) ⊆ C_ε(α,β) ∪ {ends}`;
* `fl4chain_restrict`: a harmonic measure `g` of `ηD` in `D₁ \ ηD` is one in `Wd` (FL use this
  implicitly, "the harmonic measure in the smaller domain");
* `fl4chain_reg`, `fl4chain_pt_mem`: the `C_R` regularity and radial approach used by
  `fl4hm_excR_le_fluxR`.

Own elementary bookkeeping (FL leave these domain facts implicit).
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology Real ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- `fl4wd_cmp` at a prescribed base point `p₀`. -/
theorem fl4wd_cmp_at (hc : SideCtx W t F) {R ε α β : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hH : trace W t ∈ H) (hnorm : ‖trace W t‖ = R)
    (hle : ∀ z ∈ fwdHull W t, ‖z‖ ≤ R) (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R)
    {η' : ℝ → ℂ} (hη : IsCrosscutH η') {a b : ℝ} (ha0 : 0 < a)
    (ha : Tendsto η' (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η' (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hab : a < b) (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β) {p₀ : ℂ}
    (hp : p₀ ∈ fl4WdDom W t R ε α β) (hpU : fwdMap W t p₀ ∈ hullComp η')
    (hcl : flCircArc ε α β ⊆ closure (fl4Wd W t R ε α β p₀))
    (N : ℝ) (G V : ℂ → ℝ) (hG : IsHarmMeas (hullComp η') (ofReal '' Ioo (-N) 0) G)
    (hV : IsHarmMeas (fl4Wd W t R ε α β p₀) (frontier (fl4Wd W t R ε α β p₀) ∩ sphere 0 R) V)
    (ψ : ℂ → ℂ) (J : Set ℝ) (hJ : MeasurableSet J)
    (hψ : ∀ x ∈ J, ∀ᶠ y : ℝ in 𝓝[>] 0, ψ ((x : ℂ) + (y : ℂ) * I) ∈ fl4Wd W t R ε α β p₀)
    (hVψ : ∀ x ∈ J, ∃ L : ℝ,
      Tendsto (fun y : ℝ => V (ψ ((x : ℂ) + (y : ℂ) * I)) / y) (𝓝[>] 0) (𝓝 L)) :
    excR ((fun z => G (fwdMap W t z)) ∘ ψ) J ≤ excR (V ∘ ψ) J :=
  fl3cmp_excR_le hc hεR hH hnorm hle hη ha0 ha (fl4wd_level hε hηD) hG (fl4wd_open hc)
    (fl4wd_conn hp) fl4wd_subset_D fl4wd_subset_ball (fl4wd_image_subset hc hηD hp hpU)
    (fl4wd_arc_closure hc hη hηD hcl) (fl4wd_frontier_out hc hη ha hb hab hηD) _
    (fl4wd_E hc hε hεR hlt) hV ψ hJ hψ hVψ

/-- The closed arc: `closure C_ε(α,β) ⊆ C_ε(α,β) ∪ {ε e^{iα}, ε e^{iβ}}`. -/
lemma fl4chain_closure_arc (ε α β : ℝ) :
    closure (flCircArc ε α β) ⊆ flCircArc ε α β ∪ {flCirc ε α, flCirc ε β} := by
  have hcl : closure (flCircArc ε α β) ⊆ flClArc ε α β :=
    closure_minimal (flCircArc_sub_clArc ε α β)
      ((isCompact_Icc.image (flClArc_cont ε)).isClosed)
  intro z hz
  obtain ⟨θ, hθ, rfl⟩ := hcl hz
  rcases hθ.1.eq_or_lt with h | h
  · subst h; exact Or.inr (Or.inl rfl)
  rcases hθ.2.eq_or_lt with h' | h'
  · subst h'; exact Or.inr (Or.inr rfl)
  exact Or.inl ⟨θ, ⟨h, h'⟩, rfl⟩

/-- Points of `closure ηD` in `ℍ \ K` lie on the open arc. -/
lemma fl4chain_closure_arc_D {ε α β : ℝ} (hαD : flCirc ε α ∉ H \ fwdHull W t)
    (hβD : flCirc ε β ∉ H \ fwdHull W t) {z : ℂ} (hz : z ∈ closure (flCircArc ε α β))
    (hzD : z ∈ H \ fwdHull W t) : z ∈ flCircArc ε α β := by
  rcases fl4chain_closure_arc ε α β hz with h | h | h
  · exact h
  · exact absurd (h ▸ hzD) hαD
  · exact absurd ((mem_singleton_iff.1 h) ▸ hzD) hβD

/-- **Restriction.** A harmonic measure `g` of `ηD` in `D₁ \ ηD` is one in `Wd`. -/
theorem fl4chain_restrict (hc : SideCtx W t F) {R ε α β : ℝ} (hε : 0 < ε) (hεR : ε < R)
    {η' : ℝ → ℂ} (hη : IsCrosscutH η') (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β)
    (hαD : flCirc ε α ∉ H \ fwdHull W t) (hβD : flCirc ε β ∉ H \ fwdHull W t) (p₀ : ℂ)
    {g : ℂ → ℝ} (hg : IsHarmMeas (fl4D₁ W t R \ flCircArc ε α β) (flCircArc ε α β) g) :
    IsHarmMeas (fl4Wd W t R ε α β p₀) (flCircArc ε α β) g := by
  set Ω := fl4D₁ W t R \ flCircArc ε α β with hΩ
  set Wd := fl4Wd W t R ε α β p₀ with hWd
  have hmemΩ : ∀ z, z ∈ H \ fwdHull W t → ‖z‖ < R → z ∉ flCircArc ε α β → z ∈ Ω := by
    intro z hz hzR hzA
    refine ⟨⟨⟨hz.1, ?_⟩, mem_ball_zero_iff.2 hzR⟩, hzA⟩
    rw [← hc.hull]; exact hz.2
  have hsub : Wd ⊆ Ω := fun z hz => by
    have hD := fl4wd_subset_D (R := R) (ε := ε) (α := α) (β := β) (p₀ := p₀) hz
    exact hmemΩ z hD (mem_ball_zero_iff.1 (fl4wd_subset_ball hz))
      (fun h => fl4wd_not_arc hz (subset_closure h))
  have hΩ_D : ∀ z ∈ Ω, z ∈ H \ fwdHull W t ∧ ‖z‖ < R := fun z hz => by
    refine ⟨⟨hz.1.1.1, ?_⟩, mem_ball_zero_iff.1 hz.1.2⟩
    rw [hc.hull]; exact hz.1.1.2
  have hAO := fl4_arc_subset hc hεR hε hη hηD
  have hO : IsOpen ((H \ fwdHull W t) ∩ ball (0 : ℂ) R) := hc.isOpen_dom.inter isOpen_ball
  refine ⟨fun z hz => hg.harm z (hsub hz), fun z hz => hg.mem01 z (hsub hz), ?_, ?_, ?_⟩
  · intro x₀ hx₀ _
    refine (hg.one x₀ hx₀ ?_).mono_left (nhdsWithin_mono _ hsub)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO x₀ (hAO hx₀)
    intro hcl
    obtain ⟨z, ⟨hzfr, hzA⟩, hzb'⟩ := Metric.mem_closure_iff.1 hcl r hr
    have hzb : z ∈ ball x₀ r := mem_ball'.2 hzb'
    have hzD := hball hzb
    have hzcl : z ∉ closure (flCircArc ε α β) := fun h =>
      hzA (fl4chain_closure_arc_D hαD hβD h hzD.1)
    -- a neighbourhood of `z` inside `Ω`
    have hnb : ball x₀ r ∩ (closure (flCircArc ε α β))ᶜ ⊆ Ω := fun w hw => by
      have := hball hw.1
      exact hmemΩ w this.1 (mem_ball_zero_iff.1 this.2) (fun h => hw.2 (subset_closure h))
    have hint : z ∈ interior Ω := mem_interior.2 ⟨_, hnb,
      isOpen_ball.inter isClosed_closure.isOpen_compl, ⟨hzb, hzcl⟩⟩
    exact hzfr.2 hint
  · intro x₀ hx₀ hncl
    have hxΩ : x₀ ∈ frontier Ω := by
      refine ⟨closure_mono hsub hx₀.1, fun hint => ?_⟩
      obtain ⟨hD, hR⟩ := hΩ_D x₀ (interior_subset hint)
      have hdom : x₀ ∈ fl4WdDom W t R ε α β :=
        ⟨⟨hD.1, mem_ball_zero_iff.2 hR⟩, by rintro (h | h); exacts [hD.2 h, hncl h]⟩
      exact fl4_frontier_cc_not_mem (fl4WdDom_isOpen hc R ε α β) p₀ hx₀ hdom
    exact (hg.zero x₀ hxΩ hncl).mono_left (nhdsWithin_mono _ hsub)
  · intro hb
    exact (hg.infty hb).mono_left (inf_le_inf_left _ (principal_mono.2 hsub))

/-- `C_R` regularity of `D₁ \ ηD` along the chart piece of `Wd`. -/
theorem fl4chain_reg (hc : SideCtx W t F) {R ε α β : ℝ} (hε : 0 < ε) (hεR : ε < R) (p₀ : ℂ)
    {θ : ℝ} (hθ : θ ∈ fl4WdJ W t R ε α β p₀) :
    Fl3RegAt R (fl4D₁ W t R \ flCircArc ε α β) (flCircArc ε α β) θ := by
  have hR : 0 < R := hε.trans hεR
  set Ω := fl4D₁ W t R \ flCircArc ε α β with hΩ
  have hsub : fl4Wd W t R ε α β p₀ ⊆ Ω := fun z hz => by
    have hD := fl4wd_subset_D (R := R) (ε := ε) (α := α) (β := β) (p₀ := p₀) hz
    refine ⟨⟨⟨hD.1, ?_⟩, fl4wd_subset_ball hz⟩, fun h => fl4wd_not_arc hz (subset_closure h)⟩
    rw [← hc.hull]; exact hD.2
  obtain ⟨r, hr, -, hmap, hreal⟩ := (fl4wd_chart (W := W) (t := t) (ε := ε) (α := α) (β := β)
    hR p₀).chart θ hθ
  refine ⟨r, hr, fun z hz him => hsub (hmap ⟨him, hz⟩), fun z hz him => ⟨?_, ?_⟩⟩
  · have hfr := hreal z hz him
    have hnorm : ‖fl3Chart R z‖ = R := by rw [fl4_chart_norm hR.le, him]; simp
    refine ⟨closure_mono hsub hfr.1, fun hint => ?_⟩
    have := mem_ball_zero_iff.1 (interior_subset hint).1.2
    linarith
  · intro hcl
    have h1 := fl4_closure_arc_subset hcl
    rw [mem_sphere, dist_zero_right, fl4_chart_norm hR.le, him, abs_of_pos hε] at h1
    simp at h1
    linarith

/-- Radial approach to `C_R` along the chart piece stays in `Wd`. -/
theorem fl4chain_pt_mem {R ε α β : ℝ} (hR : 0 < R) (p₀ : ℂ) {θ : ℝ}
    (hθ : θ ∈ fl4WdJ W t R ε α β p₀) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), fl2Pt R θ s ∈ fl4Wd W t R ε α β p₀ := by
  obtain ⟨-, ρ, hρ, hsub⟩ := hθ
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < min ρ R :=
    nhdsWithin_le_nhds (gt_mem_nhds (lt_min hρ hR))
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hs0
  have hs0' : (0 : ℝ) < s := hs0
  have hsR : s < R := hs.trans_le (min_le_right _ _)
  have hsρ : s < ρ := hs.trans_le (min_le_left _ _)
  have he : ‖Complex.exp ((θ : ℂ) * I)‖ = 1 := norm_exp_ofReal_mul_I θ
  refine hsub ⟨?_, ?_⟩
  · rw [mem_ball, dist_eq, fl3Chart, fl2Pt, ← sub_mul, norm_mul, he, mul_one]
    rw [show ((R - s : ℝ) : ℂ) - (R : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_neg, abs_of_pos hs0']
    exact hsρ
  · rw [mem_ball_zero_iff, fl2Pt, norm_mul, he, mul_one, norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith

end FieldLawler
end QuantumZipper
