import QuantumZipper.Proofs.Zipper.FieldLawler4Wd
import QuantumZipper.Proofs.Zipper.FieldLawler4NegCmp
import QuantumZipper.Proofs.Zipper.FieldLawler4CwdArc
import QuantumZipper.Proofs.Zipper.FieldLawler4L33
import QuantumZipper.Proofs.Zipper.FieldLawler4Hm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-CHAIN− (1): truncation, the comparison at a given base point, and `g` on `Wd`

Task FL4-CHAIN− (Track A round 4). Pieces of Field–Lawler's chain (EJP 20 (2015), proof of
Prop. 3.4, p. 9) for a negative image crosscut:

* `fl4_excR_Ici_eq_iSup`: `excR h [0,∞) = ⨆ N, excR h (0, N)` (mirror of
  `fl3_excR_Iic_eq_iSup`; monotone convergence);
* `fl4wd_cmp_neg_at`: `fl4wd_cmp_neg` (FL (2.1)) at a base point `p₀` given from outside
  (the one of `fl4cwd_base`); same proof;
* `fl4cn_E_image`: the circle chart maps `{x | σx ∈ (α,β)}` onto `C_ε(α,β)`;
* `fl4cn_restrict`: a harmonic measure `g` of `ηD` in `D₁ \ ηD` is one in `Wd` (restriction to
  a component; near a point of `ηD` the frontier of `D₁ \ ηD` is `closure ηD ⊆ ∂Wd`).

Own bookkeeping around FL's argument (FL use the domain `Wd` without comment).
-/

noncomputable section

open Set Filter Metric Complex MeasureTheory
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

theorem fl4_excR_Ici_eq_iSup (h : ℂ → ℝ) :
    excR h (Ici 0) = ⨆ N : ℕ, excR h (Ioo 0 (N : ℝ)) := by
  unfold excR
  have hae : (Ioi (0 : ℝ) : Set ℝ) =ᵐ[volume] Ici 0 := Ioi_ae_eq_Ici
  rw [← setLIntegral_congr hae]
  have hU : Ioi (0 : ℝ) = ⋃ N : ℕ, Ioo 0 (N : ℝ) := by
    ext x
    simp only [mem_Ioi, mem_iUnion, mem_Ioo]
    constructor
    · intro hx
      obtain ⟨N, hN⟩ := exists_nat_gt x
      exact ⟨N, hx, hN⟩
    · rintro ⟨N, hx, -⟩; exact hx
  rw [hU]
  refine setLIntegral_iUnion_of_directed _ ?_
  intro i j
  refine ⟨max i j, ?_, ?_⟩
  · exact Ioo_subset_Ioo_right (by exact_mod_cast le_max_left i j)
  · exact Ioo_subset_Ioo_right (by exact_mod_cast le_max_right i j)

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- **FL (2.1), negative feet, at a given base point.** `fl4wd_cmp_neg` with `p₀` supplied. -/
theorem fl4wd_cmp_neg_at (hc : SideCtx W t F) {R ε α β : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hH : trace W t ∈ H) (hnorm : ‖trace W t‖ = R)
    (hle : ∀ z ∈ fwdHull W t, ‖z‖ ≤ R) (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R)
    {η' : ℝ → ℂ} (hη : IsCrosscutH η') {a b : ℝ} (hb0 : b < 0)
    (ha : Tendsto η' (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η' (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hab : a < b) (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β) {p₀ : ℂ}
    (hp : p₀ ∈ fl4WdDom W t R ε α β) (hpU : fwdMap W t p₀ ∈ hullComp η')
    (hcl : flCircArc ε α β ⊆ closure (fl4Wd W t R ε α β p₀))
    (N : ℝ) (G V : ℂ → ℝ) (hG : IsHarmMeas (hullComp η') (ofReal '' Ioo 0 N) G)
    (hV : IsHarmMeas (fl4Wd W t R ε α β p₀) (frontier (fl4Wd W t R ε α β p₀) ∩ sphere 0 R) V)
    (ψ : ℂ → ℂ) (J : Set ℝ) (hJ : MeasurableSet J)
    (hψ : ∀ x ∈ J, ∀ᶠ y : ℝ in 𝓝[>] 0, ψ ((x : ℂ) + (y : ℂ) * I) ∈ fl4Wd W t R ε α β p₀)
    (hVψ : ∀ x ∈ J, ∃ L : ℝ,
      Tendsto (fun y : ℝ => V (ψ ((x : ℂ) + (y : ℂ) * I)) / y) (𝓝[>] 0) (𝓝 L)) :
    excR ((fun z => G (fwdMap W t z)) ∘ ψ) J ≤ excR (V ∘ ψ) J := by
  have ha0 : a < 0 := hab.trans hb0
  exact fl4neg_cmp_excR_le hc hεR hH hnorm hle hη ha0 ha (fl4wd_level hε hηD) hG
    (fl4wd_open hc) (fl4wd_conn hp) fl4wd_subset_D fl4wd_subset_ball
    (fl4wd_image_subset hc hηD hp hpU) (fl4wd_arc_closure hc hη hηD hcl)
    (fl4wd_frontier_out hc hη ha hb hab hηD) _ (fl4wd_E hc hε hεR hlt) hV ψ hJ hψ hVψ

/-- The circle chart `E_σ` maps `{x | σx ∈ (α,β)}` onto `C_ε(α,β)`. -/
lemma fl4cn_E_image {ε σ α β : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    fl4E ε σ '' (((↑) : ℝ → ℂ) '' {x : ℝ | σ * x ∈ Ioo α β}) = flCircArc ε α β := by
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [fl4E_real]
    exact ⟨σ * x, hx, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨((σ * θ : ℝ) : ℂ), ⟨σ * θ, ?_, rfl⟩, ?_⟩
    · show σ * (σ * θ) ∈ Ioo α β
      rw [← mul_assoc, hσσ, one_mul]; exact hθ
    · rw [fl4E_real, ← mul_assoc, hσσ, one_mul]; rfl

/-- `closure C_ε(α,β) ⊆ C_ε[α,β]`. -/
lemma fl4cn_closure_arc (ε α β : ℝ) : closure (flCircArc ε α β) ⊆ flClArc ε α β :=
  closure_minimal (flCircArc_sub_clArc ε α β)
    ((isCompact_Icc.image (flClArc_cont ε)).isClosed)

/-- The domain of `Wd` is `D₁ \ ηD` when the end points of the arc are off `ℍ \ K`. -/
lemma fl4cn_dom_eq (hc : SideCtx W t F) {R ε α β : ℝ}
    (hα : flCirc ε α ∉ H \ fwdHull W t) (hβ : flCirc ε β ∉ H \ fwdHull W t) :
    fl4WdDom W t R ε α β = fl4D₁ W t R \ flCircArc ε α β := by
  ext z
  simp only [fl4WdDom, fl4D₁, Set.mem_sdiff, mem_inter_iff, mem_union, ← hc.hull]
  constructor
  · rintro ⟨⟨hH, hB⟩, hn⟩
    exact ⟨⟨⟨hH, fun h => hn (Or.inl h)⟩, hB⟩, fun h => hn (Or.inr (subset_closure h))⟩
  · rintro ⟨⟨⟨hH, hK⟩, hB⟩, hn⟩
    refine ⟨⟨hH, hB⟩, ?_⟩
    rintro (h | h)
    · exact hK h
    · obtain ⟨θ, hθ, rfl⟩ := fl4cn_closure_arc ε α β h
      rcases eq_or_lt_of_le hθ.1 with e | h1
      · subst e; exact hα ⟨hH, hK⟩
      rcases eq_or_lt_of_le hθ.2 with e | h2
      · subst e; exact hβ ⟨hH, hK⟩
      exact hn ⟨θ, ⟨h1, h2⟩, rfl⟩

/-- **`g` restricted to `Wd`.** A harmonic measure of `ηD` in `D₁ \ ηD` is one in `Wd`. -/
theorem fl4cn_restrict (hc : SideCtx W t F) {R ε α β : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hα : flCirc ε α ∉ H \ fwdHull W t) (hβ : flCirc ε β ∉ H \ fwdHull W t)
    (harc : flCircArc ε α β ⊆ H \ trace W '' Ioc 0 t) {p₀ : ℂ}
    (hcl : flCircArc ε α β ⊆ closure (fl4Wd W t R ε α β p₀)) {g : ℂ → ℝ}
    (hg : IsHarmMeas (fl4D₁ W t R \ flCircArc ε α β) (flCircArc ε α β) g) :
    IsHarmMeas (fl4Wd W t R ε α β p₀) (flCircArc ε α β) g := by
  have hdom := fl4cn_dom_eq (R := R) hc hα hβ
  set U := fl4D₁ W t R \ flCircArc ε α β with hUdef
  have hUo : IsOpen U := by rw [← hdom]; exact fl4WdDom_isOpen hc R ε α β
  have hWd : fl4Wd W t R ε α β p₀ = connectedComponentIn U p₀ := by
    rw [fl4Wd, hdom]
  have hfrW : frontier (fl4Wd W t R ε α β p₀) ⊇ closure (flCircArc ε α β) :=
    closure_minimal (fl4wd_arc_frontier hcl) isClosed_frontier
  have hD₁o : IsOpen (fl4D₁ W t R) := by
    unfold fl4D₁; rw [← hc.hull]; exact hc.isOpen_dom.inter isOpen_ball
  rw [hWd] at hcl hfrW ⊢
  refine fl4hm_restrict_component hg hUo p₀ fun x₀ hx₀ _ hmem => ?_
  -- a neighbourhood of `x₀` inside `D₁`
  have hx₀D : x₀ ∈ fl4D₁ W t R := by
    refine ⟨harc hx₀, ?_⟩
    obtain ⟨θ, -, rfl⟩ := hx₀
    rw [mem_ball_zero_iff]
    have := flCirc_norm hε θ
    simp only [flCirc] at this
    rw [this]; exact hεR
  have hnhds : fl4D₁ W t R ∈ 𝓝 x₀ := hD₁o.mem_nhds hx₀D
  obtain ⟨z, hzN, hz⟩ := mem_closure_iff_nhds.1 hmem _ hnhds
  -- `z ∈ frontier U ∩ D₁` lies in `closure ηD ⊆ ∂Wd`
  refine hz.2 (hfrW ?_)
  by_contra hzc
  have hzU : z ∈ U := ⟨hzN, fun h => hzc (subset_closure h)⟩
  rw [hUo.frontier_eq] at hz
  exact hz.1.2 hzU

end FieldLawler
end QuantumZipper
