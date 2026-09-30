import QuantumZipper.Proofs.Zipper.FieldLawler3UnifD
import QuantumZipper.Proofs.Zipper.FieldLawler3UnifE

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-UNIF (F): `FL3Unif (hullComp η) F` with the boundary correspondence

`fl3u_FL3Unif_pieces`: for a crosscut `η` of `ℍ` with feet `a < b` there are `F` and `α < β`
with `FL3Unif (hullComp η) F` such that
* `closure η ⊆ frontier H_η`;
* `Re F` maps `closure η` onto `[α, β]` and `η` onto `(α, β)`;
* every other frontier point `z` is real with `z < a` or `z > b`, and `Re F z ∉ [α, β]`.
(`F` is real on the frontier, so `Re F = F` there.) The orientation (whether `(-∞, a)` goes
left or right of `[α, β]`) is not determined here.

Inputs: `fl3u_FL3Unif_exists` (Carathéodory, Jordan case) and `fl3u_frontier_pieces` (plane
topology). The inclusion `closure η ⊆ f([α, β])` is an own elementary connectedness argument
(the connected set `f([α, β]) ⊆ η̄` contains both end points, and `η̄` minus an interior point is
disconnected into two closed arcs).
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar QuantumZipper.CA

/-- **FL3-UNIF with the boundary pieces.** -/
theorem fl3u_FL3Unif_pieces {η : ℝ → ℂ} (hη : IsCrosscutH η) {a b : ℝ}
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hab : a < b) :
    ∃ (F : ℂ → ℂ) (α β : ℝ), FL3Unif (hullComp η) F ∧ α < β ∧
      closure (arcH η) ⊆ frontier (hullComp η) ∧
      (fun p => (F p).re) '' closure (arcH η) = Icc α β ∧
      (fun p => (F p).re) '' arcH η = Ioo α β ∧
      ∀ z ∈ frontier (hullComp η), z ∉ closure (arcH η) →
        z.im = 0 ∧ (z.re < a ∨ b < z.re) ∧ ((F z).re < α ∨ β < (F z).re) := by
  obtain ⟨F, Φ, hU, -, -, hΦF, hΦc, hΦi, hΦr, hΦinf⟩ := fl3u_FL3Unif_exists hη ha hb hab.ne
  set f : ℝ → ℂ := fun x => Φ x with hf
  have hRH : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => show (0 : ℝ) ≤ ((x : ℂ)).im by simp
  have hfc : Continuous f := hΦc.comp_continuous continuous_ofReal hRH
  have hFf : ∀ x, F (f x) = x := fun x => hΦF x (hRH x)
  have hlim : ∀ l : Filter ℝ, Tendsto (fun x : ℝ => |x|) l atTop →
      Tendsto f l (Bornology.cobounded ℂ) := fun l hl =>
    hΦinf.comp (tendsto_inf.2 ⟨tendsto_norm_atTop_iff_cobounded.1
      (by simpa [Complex.norm_real] using hl), tendsto_principal.2 (Eventually.of_forall hRH)⟩)
  have hunb : ∀ c : ℝ, ¬ Bornology.IsBounded (f '' Ici c) ∧ ¬ Bornology.IsBounded (f '' Iic c) := by
    intro c
    constructor
    · intro hbd
      obtain ⟨R, hR⟩ := hbd.subset_closedBall 0
      obtain ⟨x, hx1, hx2⟩ := (((hlim atTop tendsto_abs_atTop_atTop).eventually
        (Bornology.isBounded_def.1 (isBounded_closedBall (x := (0 : ℂ)) (r := R)))).and
        (eventually_ge_atTop c)).exists
      exact hx1 (hR ⟨x, hx2, rfl⟩)
    · intro hbd
      obtain ⟨R, hR⟩ := hbd.subset_closedBall 0
      obtain ⟨x, hx1, hx2⟩ := (((hlim atBot tendsto_abs_atBot_atTop).eventually
        (Bornology.isBounded_def.1 (isBounded_closedBall (x := (0 : ℂ)) (r := R)))).and
        (eventually_le_atBot c)).exists
      exact hx1 (hR ⟨x, hx2, rfl⟩)
  obtain ⟨-, α, β, hαβ, hends, harc, hout⟩ := fl3u_frontier_pieces hη ha hb hfc hΦi hΦr hunb
  set g := lwArcExt η a b with hg
  set K := g '' Icc 0 1 with hK
  have hgc : ContinuousOn g (Icc 0 1) := lwArcExt_contOn hη ha hb
  have hgi : InjOn g (Icc 0 1) := fl3u_arcExt_injOn hη hab.ne
  have hg0 : g 0 = a := by simp [hg, lwArcExt]
  have hg1 : g 1 = b := by norm_num [hg, lwArcExt]
  have hAK : arcH η ⊆ K := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨s, Ioo_subset_Icc_self hs, (lwArcExt_mem hη hs).1⟩
  have haK : (a : ℂ) ∈ K := ⟨0, left_mem_Icc.2 zero_le_one, hg0⟩
  have hbK : (b : ℂ) ∈ K := ⟨1, right_mem_Icc.2 zero_le_one, hg1⟩
  have hAim : ∀ z ∈ arcH η, 0 < z.im := by rintro _ ⟨s, hs, rfl⟩; exact hη.2.2.1 hs
  -- `f([α, β]) = K`
  set s := f '' Icc α β with hs
  have hsK : s ⊆ K := by
    rintro _ ⟨x, hx, rfl⟩
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h; rcases hends with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> assumption
    rcases eq_or_lt_of_le hx.2 with h' | h'
    · subst h'; rcases hends with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> assumption
    exact hAK (harc ⟨x, ⟨h, h'⟩, rfl⟩)
  have has : (a : ℂ) ∈ s ∧ (b : ℂ) ∈ s := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⟨α, left_mem_Icc.2 hαβ.le, h1⟩, ⟨β, right_mem_Icc.2 hαβ.le, h2⟩⟩
    · exact ⟨⟨β, right_mem_Icc.2 hαβ.le, h2⟩, ⟨α, left_mem_Icc.2 hαβ.le, h1⟩⟩
  have hKs : K ⊆ s := by
    rintro _ ⟨t₀, ht₀, rfl⟩
    by_contra hns
    have hC : ∀ u v : ℝ, Icc u v ⊆ Icc 0 1 → IsClosed (g '' Icc u v) := fun u v huv =>
      (isCompact_Icc.image_of_continuousOn (hgc.mono huv)).isClosed
    have h1 : Icc 0 t₀ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl ht₀.2
    have h2 : Icc t₀ 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ht₀.1 le_rfl
    have hcov : s ⊆ g '' Icc 0 t₀ ∪ g '' Icc t₀ 1 := by
      intro q hq
      obtain ⟨t, ht, rfl⟩ := hsK hq
      rcases le_total t t₀ with h | h
      · exact Or.inl ⟨t, ⟨ht.1, h⟩, rfl⟩
      · exact Or.inr ⟨t, ⟨h, ht.2⟩, rfl⟩
    have hdisj : s ∩ (g '' Icc 0 t₀ ∩ g '' Icc t₀ 1) = ∅ := by
      ext q
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
      rintro ⟨hq, ⟨t1, ht1, rfl⟩, ⟨t2, ht2, e⟩⟩
      have e' := hgi (h2 ht2) (h1 ht1) e
      have : t1 = t₀ := le_antisymm ht1.2 (e' ▸ ht2.1)
      exact hns (this ▸ hq)
    have hpre : IsPreconnected s := isPreconnected_Icc.image f hfc.continuousOn
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 hpre _ _ (hC 0 t₀ h1) (hC t₀ 1 h2) hcov
      hdisj with h | h
    · obtain ⟨t, ht, e⟩ := h has.2
      rw [← hg1] at e
      have := hgi (h1 ht) (right_mem_Icc.2 zero_le_one) e
      have ht1 : t₀ ≠ 1 := fun h => hns (by rw [h, hg1]; exact has.2)
      exact ht1 (le_antisymm ht₀.2 (this ▸ ht.2))
    · obtain ⟨t, ht, e⟩ := h has.1
      rw [← hg0] at e
      have := hgi (h2 ht) (left_mem_Icc.2 zero_le_one) e
      have ht0 : t₀ ≠ 0 := fun h => hns (by rw [h, hg0]; exact has.1)
      exact ht0 (le_antisymm (this ▸ ht.1) ht₀.1)
  have hclK : closure (arcH η) ⊆ K :=
    closure_minimal hAK (isCompact_Icc.image_of_continuousOn hgc).isClosed
  have hscl : s ⊆ closure (arcH η) := by
    have := image_closure_subset_closure_image (s := Ioo α β) hfc
    rw [closure_Ioo hαβ.ne] at this
    exact this.trans (closure_mono harc)
  have hfr : ∀ x, f x ∈ frontier (hullComp η) := fun x => hΦr ▸ mem_range_self x
  refine ⟨F, α, β, hU, hαβ, fun p hp => ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, -, rfl⟩ := hKs (hclK hp); exact hfr x
  · ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hKs (hclK hp)
      simpa [hFf] using hx
    · intro hy
      exact ⟨f y, hscl ⟨y, hy, rfl⟩, by simp [hFf]⟩
  · ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hKs (hAK hp)
      have him : 0 < (f x).im := hAim _ hp
      have hre : (f α).im = 0 ∧ (f β).im = 0 := by
        rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp [e1, e2]
      simp only [hFf, ofReal_re]
      exact ⟨lt_of_le_of_ne hx.1 fun h => by rw [← h] at him; linarith [hre.1],
        lt_of_le_of_ne hx.2 fun h => by rw [h] at him; linarith [hre.2]⟩
    · intro hy
      exact ⟨f y, harc ⟨y, hy, rfl⟩, by simp [hFf]⟩
  · intro z hz hzA
    obtain ⟨x, rfl⟩ : z ∈ range f := hΦr ▸ hz
    have hx : x < α ∨ β < x := by
      by_contra hcon
      push Not at hcon
      exact hzA (hscl ⟨x, hcon, rfl⟩)
    obtain ⟨h1, h2⟩ := hout x hx
    refine ⟨h1, h2, ?_⟩
    simpa [hFf] using hx

end FieldLawler
end QuantumZipper
