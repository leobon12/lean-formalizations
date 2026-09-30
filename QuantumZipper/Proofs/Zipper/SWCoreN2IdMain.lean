import QuantumZipper.Proofs.Zipper.SWCoreN2IdRound
import QuantumZipper.Proofs.Zipper.SWCoreN2IdCc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-N2-ID (5): pathwise identification for a finite-parameter Lipschitz family of class maps

Task SWC-N2-ID (helper of SWC-N2, step (c)). Setting (finite-parameter restriction of
`BdryDistClassStmt`): `Ψ : ℝⁿ → ℂ → ℂ`, `Ψ q ∈ BdryClass a b ρ M m` for `q ∈ K`,
`‖Ψ q z − Ψ q' z‖ ≤ L ‖q − q'‖` on the `ρ`-thickening of `[a,b]`, and a Lipschitz retraction
`π` of `ℝⁿ` onto `K` (for a box `K`, the coordinatewise clamp). Then there is `k₀` such that:

* a.s., for all `k ≥ k₀`, `q ∈ K`, `t ∈ [a,b]`:
  (i) `avgReg (coordChange x (Ψ q) Q) k t = evalReg x (fc(t,r_k).map (Ψ q)) + Q cc(Ψ q, t, r_k)`;
  (ii) `(q,t) ↦ evalReg x (fc(t,r_k).map (Ψ q))` and
      `(q,t) ↦ evalReg x (fc(Re Ψ_q(t), r_k ‖Ψ_q'(t)‖))` are continuous on `K × [a,b]`;
* (iii) for each `k ≥ k₀`, `q ∈ K`, `t ∈ [a,b]`, both `evalReg` values equal the raw values a.s.

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (Kolmogorov continuity of
circle averages); Sheffield–Wang, arXiv:1605.06171, Lemma 3.5 (p. 16). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace SWCore

variable {n : ℕ} {a b ρ M m L : ℝ} {Ψ : (Fin n → ℝ) → ℂ → ℂ} {K : Set (Fin n → ℝ)}
  {Kπ : ℝ≥0} {π : (Fin n → ℝ) → Fin n → ℝ}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- **SWC-N2-ID: pathwise identification** (items (i)–(iii)). -/
theorem swcN2_id (hab : a < b) (hρ : 0 < ρ) (hm : 0 < m)
    (hΨ : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m) (hL0 : 0 ≤ L)
    (hL : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening ρ (segC a b), ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ π) (hπK : ∀ q, π q ∈ K) (hπid : ∀ q ∈ K, π q = q) (Q : ℝ)
    (hX : IsFreeGFFModConstH X P) :
    ∃ k₀ : ℕ,
      (∀ᵐ ω ∂P, ∀ k ≥ k₀,
        (∀ q ∈ K, ∀ t ∈ Icc a b,
          avgReg (coordChange (X ω) (Ψ q) Q) k (t : ℂ) =
            evalReg (X ω) ((foldedCircle (t : ℂ) (radius k)).map (Ψ q)) +
              Q * CoordChange.cc (Ψ q) t (radius k)) ∧
        ContinuousOn (fun x : (Fin n → ℝ) × ℝ =>
          evalReg (X ω) ((foldedCircle (x.2 : ℂ) (radius k)).map (Ψ x.1))) (K ×ˢ Icc a b) ∧
        ContinuousOn (fun x : (Fin n → ℝ) × ℝ => evalReg (X ω)
          (foldedCircle (((Ψ x.1 (x.2 : ℂ)).re : ℝ) : ℂ) (radius k * ‖deriv (Ψ x.1) (x.2 : ℂ)‖)))
          (K ×ˢ Icc a b)) ∧
      ∀ k ≥ k₀, ∀ q ∈ K, ∀ t ∈ Icc a b,
        (∀ᵐ ω ∂P, evalReg (X ω) ((foldedCircle (t : ℂ) (radius k)).map (Ψ q)) =
          X ω ((foldedCircle (t : ℂ) (radius k)).map (Ψ q))) ∧
        (∀ᵐ ω ∂P, evalReg (X ω)
            (foldedCircle (((Ψ q t).re : ℝ) : ℂ) (radius k * ‖deriv (Ψ q) t‖)) =
          X ω (foldedCircle (((Ψ q t).re : ℝ) : ℂ) (radius k * ‖deriv (Ψ q) t‖))) := by
  obtain ⟨r₂, hr₂, hpush⟩ := swcN2_push_ae hab hρ hm hΨ hL0 hL hπ hπK hπid hX
  set A : ℝ := |M| + 1 with hA
  have hA0 : 0 < A := by positivity
  set r₃ : ℝ := min r₂ (min (ρ / 16) (m * ρ ^ 2 / (128 * A))) with hr₃
  have hr₃0 : 0 < r₃ := lt_min hr₂ (lt_min (by positivity) (by positivity))
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, (2⁻¹ : ℝ) ^ k₀ < r₃ :=
    exists_pow_lt_of_lt_one hr₃0 (by norm_num)
  have hrad : ∀ k ≥ k₀, radius k < r₃ := fun k hk =>
    lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk) hk₀
  -- the smallness conditions at `r = radius k`
  have hcond : ∀ k ≥ k₀, radius k ∈ Ioo 0 r₂ ∧ 2 * radius k ≤ ρ / 8 ∧
      32 * (|M| + 1) / ρ ^ 2 * (2 * radius k) ≤ m / 2 := by
    intro k hk
    have h := hrad k hk
    have h1 : radius k < r₂ := lt_of_lt_of_le h (min_le_left _ _)
    have h2 : radius k < ρ / 16 :=
      lt_of_lt_of_le h ((min_le_right _ _).trans (min_le_left _ _))
    have h3 : radius k < m * ρ ^ 2 / (128 * A) :=
      lt_of_lt_of_le h ((min_le_right _ _).trans (min_le_right _ _))
    rw [lt_div_iff₀ (by positivity)] at h3
    refine ⟨⟨radius_pos k, h1⟩, by linarith, ?_⟩
    rw [show 32 * (|M| + 1) / ρ ^ 2 * (2 * radius k) = 64 * A * radius k / ρ ^ 2 by
      rw [hA]; ring, div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨k₀, ?_, fun k hk q hq t ht => ?_⟩
  · have hall : ∀ k : ℕ, ∀ᵐ ω ∂P, k ≥ k₀ →
        ((∀ q ∈ K, ∀ t ∈ Icc a b,
          avgReg (coordChange (X ω) (Ψ q) Q) k (t : ℂ) =
            evalReg (X ω) ((foldedCircle (t : ℂ) (radius k)).map (Ψ q)) +
              Q * CoordChange.cc (Ψ q) t (radius k)) ∧
        ContinuousOn (fun x : (Fin n → ℝ) × ℝ =>
          evalReg (X ω) ((foldedCircle (x.2 : ℂ) (radius k)).map (Ψ x.1))) (K ×ˢ Icc a b) ∧
        ContinuousOn (fun x : (Fin n → ℝ) × ℝ => evalReg (X ω)
          (foldedCircle (((Ψ x.1 (x.2 : ℂ)).re : ℝ) : ℂ) (radius k * ‖deriv (Ψ x.1) (x.2 : ℂ)‖)))
          (K ×ˢ Icc a b)) := by
      intro k
      by_cases hk : k₀ ≤ k
      · obtain ⟨hr, hr8, hrm⟩ := hcond k hk
        filter_upwards [(hpush (radius k) hr).1,
          swcN2_round_family_ae hρ hm hΨ hL hX (radius_pos k)] with ω hpc hrc _
        refine ⟨fun q hq t ht => ?_, hpc.mono (prod_mono subset_rfl
          (Icc_subset_Icc (by linarith [hr.1]) (by linarith [hr.1]))), hrc⟩
        have htI : t ∈ Icc (a - radius k) (b + radius k) :=
          ⟨by linarith [ht.1, hr.1], by linarith [ht.2, hr.1]⟩
        have h1 : ContinuousWithinAt (fun s : ℝ =>
            evalReg (X ω) ((foldedCircle (s : ℂ) (radius k)).map (Ψ q)))
            (Icc (a - radius k) (b + radius k)) t :=
          ContinuousWithinAt.comp (f := fun s : ℝ => (q, s)) (hpc (q, t) ⟨hq, htI⟩)
            (continuous_const.prodMk continuous_id).continuousWithinAt
            (fun s hs => ⟨hq, hs⟩)
        exact swcN2_avgReg_eq (X ω) (Ψ q) Q k ht h1
          (swcN2_cc_continuousOn (hΨ q hq) hab.le hρ hm hr.1 hr8 hrm t htI)
      · exact Eventually.of_forall fun ω h => absurd h hk
    filter_upwards [ae_all_iff.2 hall] with ω hω k hk
    exact hω k hk
  · obtain ⟨hr, -, -⟩ := hcond k hk
    have htI : t ∈ Icc (a - radius k) (b + radius k) :=
      ⟨by linarith [ht.1, hr.1], by linarith [ht.2, hr.1]⟩
    have hpos : 0 < radius k * ‖deriv (Ψ q) t‖ :=
      mul_pos hr.1 (lt_of_lt_of_le hm ((hΨ q hq).2.2.2.2 t ht))
    exact ⟨(hpush (radius k) hr).2 q hq t htI, (swcN2_round_ae hpos hX).2 _ _ le_rfl⟩

end SWCore
end QuantumZipper
