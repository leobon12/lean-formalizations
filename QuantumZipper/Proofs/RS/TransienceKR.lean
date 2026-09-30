import QuantumZipper.Proofs.RS.TransienceKRBasic
import QuantumZipper.Proofs.RS.BasePoint
import QuantumZipper.Proofs.RS.TipB
import QuantumZipper.Proofs.RS.TraceMain

/-!
# EXT-RS node KR: SLE_κ (κ ≤ 4) a.s. stays away from a fixed real point `x ≠ 0`

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §4, node **KR** and its conclusion.

* `ae_hull_avoid`: a.s. there is `r > 0` with `r ≤ ‖z - x‖` for every `z ∈ K_t`, `t ≥ 0`;
* `ae_not_mem_closure_sleTrace`: a.s. `x ∉ closure (η '' [0, ∞))`.

## Source

Rohde–Schramm, *Basic properties of SLE*, Ann. of Math. 161 (2005), Lemma 7.2 and its proof,
p. 32 of `literature/math_0106036.pdf`: the a.s. lower bound on `Υ_t` (`RS.ae_bp1`) combined
with Koebe 1/4 applied to `g_t⁻¹` (`kr_le_norm_sub`). The case `x < 0` is reduced to `x > 0`
by the reflection `z ↦ -z̄` and `B ↦ -B`, as in the paper ("by symmetry"). The closure form
uses `K_t = η (0, t]` (`RS.ae_fwdHull_eq_sleTrace_image_of_le_four`) and `η 0 = 0`.
-/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ComplexConjugate

namespace QuantumZipper
namespace RS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

theorem ae_hull_avoid_of_pos (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    {x : ℝ} (hx : 0 < x) :
    ∀ᵐ ω ∂P, ∃ r > 0, ∀ t : ℝ, 0 ≤ t → ∀ z ∈ fwdHull (drive κ B ω) t, r ≤ ‖z - x‖ := by
  have hy : 0 < x / 2 := by positivity
  have hyx : x / 2 < x := by linarith
  filter_upwards [ae_bp1 hB hκ hκ4 hy hyx, ae_real_alive hB hκ hκ4, hB.cont,
    hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hbp halive hc h0
  obtain ⟨ε, hε, hbp⟩ := hbp
  have hW : Continuous (drive κ B ω) :=
    continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  refine ⟨CA.Koebe.koebeCovConst * ε, mul_pos CA.Koebe.koebeCovConst_pos hε,
    fun t ht z hz => ?_⟩
  obtain ⟨u, hu⟩ := halive x hx.ne' t ht
  obtain ⟨v, hv⟩ := halive (x / 2) hy.ne' t ht
  exact le_trans (mul_le_mul_of_nonneg_left (hbp t ht u v hu hv)
    CA.Koebe.koebeCovConst_pos.le) (kr_le_norm_sub hW hW0 hy hyx ht hu hv hz)

theorem ae_hull_avoid (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    {x : ℝ} (hx : x ≠ 0) :
    ∀ᵐ ω ∂P, ∃ r > 0, ∀ t : ℝ, 0 ≤ t → ∀ z ∈ fwdHull (drive κ B ω) t, r ≤ ‖z - x‖ := by
  rcases hx.lt_or_gt with hneg | hpos
  · filter_upwards [ae_hull_avoid_of_pos hB.neg hκ hκ4 (neg_pos.2 hneg)] with ω h
    obtain ⟨r, hr, h⟩ := h
    refine ⟨r, hr, fun t ht z hz => ?_⟩
    have hdr : drive κ (-B) ω = -drive κ B ω := by
      funext s; simp [drive]
    have hz' : -conj z ∈ fwdHull (drive κ (-B) ω) t := by
      rw [hdr]; exact (LoewnerAlgebra.mem_fwdHull_reflect_iff _ ht z).2 hz
    have e : -conj z - ((-x : ℝ) : ℂ) = -conj (z - x) := by
      simp only [map_sub, Complex.conj_ofReal, Complex.ofReal_neg]; ring
    have := h t ht _ hz'
    rwa [e, norm_neg, Complex.norm_conj] at this
  · exact ae_hull_avoid_of_pos hB hκ hκ4 hpos

theorem ae_not_mem_closure_sleTrace (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ ≤ 4) {x : ℝ} (hx : x ≠ 0) :
    ∀ᵐ ω ∂P, (x : ℂ) ∉ closure (sleTrace κ B ω '' Set.Ici 0) := by
  obtain ⟨δ, -, hgood⟩ := ae_sleTrace_good hB hκ (by linarith : κ < 8)
  filter_upwards [ae_hull_avoid hB hκ hκ4 hx, ae_fwdHull_eq_sleTrace_image_of_le_four hB hκ hκ4,
    hgood] with ω hav hK hg
  obtain ⟨r, hr, hav⟩ := hav
  have hsub : sleTrace κ B ω '' Ici 0 ⊆ {z : ℂ | min r |x| ≤ ‖z - x‖} := by
    rintro _ ⟨s, hs, rfl⟩
    rcases (show (0 : ℝ) ≤ s from hs).eq_or_lt with h0 | hpos
    · rw [← h0]
      show min r |x| ≤ ‖sleTrace κ B ω 0 - x‖
      rw [hg.1, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      exact min_le_right _ _
    · have hmem : sleTrace κ B ω s ∈ fwdHull (drive κ B ω) s := by
        rw [hK s hs]; exact ⟨s, ⟨hpos, le_rfl⟩, rfl⟩
      exact (min_le_left _ _).trans (hav s hs _ hmem)
  have hcl : IsClosed {z : ℂ | min r |x| ≤ ‖z - x‖} :=
    isClosed_le continuous_const (continuous_id.sub continuous_const).norm
  intro hxc
  have : min r |x| ≤ ‖(x : ℂ) - x‖ := closure_minimal hsub hcl hxc
  rw [sub_self, norm_zero] at this
  linarith [lt_min hr (abs_pos.2 hx)]

end RS
end QuantumZipper
