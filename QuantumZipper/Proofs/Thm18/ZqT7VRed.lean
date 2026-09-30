import QuantumZipper.Proofs.Thm18.ZqT6VPalm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-TYP (7): the `V + logSing` clause from fixed Palm points and the partner map

* `ae_V_side_of_palm`: the Palm transfer `ae_typ_of_palm_V` on countably many windows
  `(−(n+1), −1/(n+1))` (resp. `(1/(n+1), n+1)`) exhausting the side half-line turns the local
  certificate `LocCertC` of the pulled-back PALM field at Lebesgue-a.e. fixed point into the local
  area `LocAreaQ` of the pulled-back `V + logSing` at `ν`-typical side points.
* `G3ZqTVPalmStmt` (fixed Palm points; the analog of ZQ-REG's `G3ZqLPalmCertStmt` for the
  log-singular field) and `G3ZqTVPartnerStmt` (the length-partner map `x ↦ R(x)` does not charge
  `ν`-null sets; measure theory of the boundary length only) give `G3ZqTVSideStmt`
  (`g3ZqTVSideStmt_of`), hence the headline `theorem1_8PaperMO_of_typVPalm`.

Duplantier–Sheffield, arXiv:0808.1560, §3.3 (rooted measure); Sheffield, arXiv:1012.4797, proof
of Prop. 5.5, p. 65. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqT

open R18 PalmNorm Factorization G3Zq G3Z2b2 G3ZqL

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

theorem msSide (side : Bool) : MeasurableSet (g1SideHalf side) := by
  cases side <;> simp [g1SideHalf, measurableSet_Iio, measurableSet_Ioi]

/-- Countably many windows avoiding `0` exhaust each side half-line. -/
theorem side_windows (side : Bool) : ∃ J : ℕ → Set ℝ,
    (∀ n, ∃ a b : ℝ, ∃ N : ℕ, J n = Ioo a b ∧ Icc a b ⊆ Icc (-(N : ℝ)) N ∧ (0 : ℝ) ∉ Icc a b) ∧
    ⋃ n, J n = g1SideHalf side := by
  cases side
  · refine ⟨fun n => Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1),
      fun n => ⟨_, _, n + 1, rfl, fun t ht => ?_, fun ht => ?_⟩, ?_⟩
    · have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      push_cast
      exact ⟨by linarith [ht.1], ht.2⟩
    · have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith [ht.1]
    · ext x
      simp only [mem_iUnion, mem_Ioo, g1SideHalf, Bool.false_eq_true, if_false, mem_Ioi]
      constructor
      · rintro ⟨n, h1, -⟩
        exact lt_trans (by positivity) h1
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_gt (max x (1 / x))
        refine ⟨n, ?_, by linarith [le_max_left x (1 / x)]⟩
        have h2 : 1 / x < n := (le_max_right x (1 / x)).trans_lt hn
        rw [div_lt_iff₀ hx] at h2
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
  · refine ⟨fun n => Ioo (-((n : ℝ) + 1)) (-(1 / ((n : ℝ) + 1))),
      fun n => ⟨_, _, n + 1, rfl, fun t ht => ?_, fun ht => ?_⟩, ?_⟩
    · have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      push_cast
      exact ⟨ht.1, by linarith [ht.2]⟩
    · have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith [ht.2]
    · ext x
      simp only [mem_iUnion, mem_Ioo, g1SideHalf, if_true, mem_Iio]
      constructor
      · rintro ⟨n, -, h2⟩
        have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_gt (max (-x) (1 / (-x)))
        have hx' : 0 < -x := by linarith
        refine ⟨n, by linarith [le_max_left (-x) (1 / (-x))], ?_⟩
        have h2 : 1 / (-x) < n := (le_max_right (-x) (1 / (-x))).trans_lt hn
        rw [div_lt_iff₀ hx'] at h2
        have h3 : 1 / ((n : ℝ) + 1) < -x := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
        linarith

/-- **From fixed Palm points to `ν`-typical side points for `V + logSing`.** -/
theorem ae_V_side_of_palm {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hsel : G1PsiSel γ Ψ)
    {a : ℝ≥0 → ℝ} (side : Bool) {Ω'' : Type} [MeasurableSpace Ω'']
    {P'' : Measure Ω''} [IsProbabilityMeasure P''] {V : Ω'' → FieldSample}
    (hV : IsFreeGFFModConstH V P'') (hV0 : ∀ᵐ ω ∂P'', V ω (foldedCircle 0 1) = 0)
    (hP : ∀ᵐ x ∂(volume.restrict (g1SideHalf side)), ∀ᵐ ω ∂P'',
      LocCertC γ (g3coordsM γ 0 Ψ side
        (normAt g3zS (ofFun (shiftFun γ (LogSingGood.Lf (γ - 2 / γ)) g3zS x) + V ω), a, 1, x))) :
    ∀ᵐ ω ∂P'', ∀ᵐ x ∂(qBoundaryMeasure γ (V ω + F2.logSingField (γ ^ 2))),
      x ∈ g1SideHalf side →
        LocAreaQ γ (g3zqPull γ Ψ side a (V ω + F2.logSingField (γ ^ 2)) x) := by
  obtain ⟨J, hJ, hU⟩ := side_windows side
  have hn : ∀ n, ∀ᵐ ω ∂P'', ∀ᵐ x ∂((qBoundaryMeasure γ
      (V ω + F2.logSingField (γ ^ 2))).restrict (J n)),
      (coords (V ω + F2.logSingField (γ ^ 2)), x) ∉ badSet γ Ψ side a := by
    intro n
    obtain ⟨a', b', N, hJn, hsub, h0⟩ := hJ n
    rw [hJn]
    refine ae_typ_of_palm_V hγ hγ2 hV hV0 (measurableSet_badSet hsel side a) hsub h0 ?_
    have hJs : Ioo a' b' ⊆ g1SideHalf side := by
      rw [← hJn, ← hU]; exact subset_iUnion J n
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hJs hP] with x hx
    filter_upwards [hx] with ω hω
    intro hb
    exact hb.2 (by rw [g3coordsM_reconstruct_coords]; exact hω)
  filter_upwards [ae_all_iff.2 hn] with ω hω
  have hall : ∀ᵐ x ∂((qBoundaryMeasure γ (V ω + F2.logSingField (γ ^ 2))).restrict (⋃ n, J n)),
      (coords (V ω + F2.logSingField (γ ^ 2)), x) ∉ badSet γ Ψ side a :=
    (ae_restrict_iUnion_iff _ _).2 hω
  rw [hU, ae_restrict_iff' (msSide side)] at hall
  filter_upwards [hall] with x hx hxs
  have hc : LocCertC γ (g3coordsM γ 0 Ψ side (V ω + F2.logSingField (γ ^ 2), a, 1, x)) := by
    by_contra hn'
    exact hx hxs ⟨hxs, by rw [g3coordsM_reconstruct_coords]; exact hn'⟩
  exact locAreaQ_of_locCertC hc

/-- **Node: the pulled-back Palm field of `V + logSing` is locally certified at Lebesgue-a.e.
fixed point of each side half-line** (fixed-point analog of ZQ-REG's `G3ZqLPalmCertStmt`). -/
def G3ZqTVPalmStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
  ∀ᵐ a ∂(P.map (pathOf B)), G3ZqGoodPathF γ a → ∀ side : Bool,
    ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
      (V : Ω'' → FieldSample), IsFreeGFFModConstH V P'' →
      (∀ᵐ ω ∂P'', V ω (foldedCircle 0 1) = 0) →
      ∀ᵐ x ∂(volume.restrict (g1SideHalf side)), ∀ᵐ ω ∂P'',
        LocCertC γ (g3coordsM γ 0 Ψ side
          (normAt g3zS (ofFun (shiftFun γ (LogSingGood.Lf (γ - 2 / γ)) g3zS x) + V ω), a, 1, x))

/-- **Node: the length-partner map of `V + logSing` does not charge null subsets of `(0, ∞)` of
the boundary length** (the restriction to `(0, ∞)` is needed: `R(x) = lenRight ν 0` for all
`x ≥ 0`). -/
def G3ZqTVPartnerStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 →
  ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (V : Ω'' → FieldSample), IsFreeGFFModConstH V P'' →
    (∀ᵐ ω ∂P'', V ω (foldedCircle 0 1) = 0) →
    ∀ᵐ ω ∂P'', ∀ S : Set ℝ, S ⊆ Ioi 0 →
      qBoundaryMeasure γ (V ω + F2.logSingField (γ ^ 2)) S = 0 →
      ∀ᵐ x ∂(qBoundaryMeasure γ (V ω + F2.logSingField (γ ^ 2))),
        g3zPartner γ (V ω + F2.logSingField (γ ^ 2)) x ∉ S

theorem g3ZqTVSideStmt_of (hP : G3ZqTVPalmStmt) (hR : G3ZqTVPartnerStmt) : G3ZqTVSideStmt := by
  intro γ hγ hγ2 Ψ hsel Ω _ P _ B hB
  filter_upwards [hP γ hγ hγ2 Ψ hsel P B hB] with a ha hg Ω'' _ P'' _ V hV hV0
  have hT := ae_V_side_of_palm hγ hγ2 hsel true hV hV0 (ha hg true P'' V hV hV0)
  have hF := ae_V_side_of_palm hγ hγ2 hsel false hV hV0 (ha hg false P'' V hV hV0)
  filter_upwards [hT, hF, hR γ hγ hγ2 P'' V hV hV0] with ω hωT hωF hωR
  have hS := ae_iff.1 hωF
  have hSs : {x' | ¬(x' ∈ g1SideHalf false →
      LocAreaQ γ (g3zqPull γ Ψ false a (V ω + F2.logSingField (γ ^ 2)) x'))} ⊆ Ioi 0 :=
    fun x' hx' => by
      by_contra hn
      exact hx' fun h => absurd h (by simpa [g1SideHalf] using hn)
  filter_upwards [hωT, hωR _ hSs hS] with x hx1 hx2
  refine ⟨hx1, fun hmem => ?_⟩
  by_contra hne
  exact hx2 fun h => hne (h hmem)

end ZqT
end Thm18Asm
end QuantumZipper
