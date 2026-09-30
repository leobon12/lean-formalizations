import QuantumZipper.Proofs.Thm18.G1RestRC3Wire
import QuantumZipper.Proofs.Zipper.D3PlusN2OscEquiv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PAIR-QUANT (1): a quantitative PAIR-LIM node and its countable certificate

`G1RestPairStmt` asks for PAIR-LIM (convergence of the circle-regularized pairings of the
pulled-back wedge field with **every** test function) at the representative; turning the
resulting good set into a measurable one needed the descriptive-set-theory input
`PairLimUnivMeasStmt`. Here we replace it by the **quantitative** node `G1RestPairLipStmt`,
the analogue for the pulled-back G1 field of the free-field node `D3Plus.N2ZPairLipStmt`:
a.s., for every compact `K ⊆ H` there are `C, δ` with
`|∫ (h_t(u) - h_s(u)) f(u) du| ≤ C · L · √(max t s)` for `t, s ∈ (0, δ)` and every
`L`-Lipschitz `f` vanishing off `K` (`h_t(u)` = regularized semicircle average at `(u, t)`).

Such a modulus is checked on a **countable** family: the boxes `Kb m` exhaust `H`, and the sets
`LipSet m N` of `N`-Lipschitz continuous functions vanishing off `Kb m` are separable in the
compact-open topology of `C(ℂ, ℝ)` (mathlib: `ContinuousMap.instSecondCountableTopology`), so
each has a dense sequence `dseq m N`. `CountCond x` is the modulus for these sequences and
rational radii only.

Own argument (the uniform boundedness / separability bookkeeping; the modulus itself is the
quantitative form of the circle-average estimates of Duplantier–Sheffield, Invent. Math. 185
(2011), Prop. 3.1, and Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1Rest

/-! ## 1. Boxes exhausting `H` -/

/-- The compact boxes `[-m, m] × [1/(m+1), m]` exhausting `H`. -/
def Kb (m : ℕ) : Set ℂ := {z | |z.re| ≤ m ∧ 1 / ((m : ℝ) + 1) ≤ z.im ∧ z.im ≤ m}

theorem Kb_subset_H (m : ℕ) : Kb m ⊆ H := fun z hz =>
  lt_of_lt_of_le (by positivity) hz.2.1

theorem Kb_subset_Hbar (m : ℕ) : Kb m ⊆ Hbar := fun z hz =>
  show (0 : ℝ) ≤ z.im from le_of_lt (Kb_subset_H m hz)

theorem zero_notMem_Kb (m : ℕ) : (0 : ℂ) ∉ Kb m := fun h => by
  have := Kb_subset_H m h
  simp [H] at this

theorem isCompact_Kb (m : ℕ) : IsCompact (Kb m) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · refine (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2 * m)).subset fun z hz => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := Complex.norm_le_abs_re_add_abs_im z
    have h2 : |z.im| ≤ m := abs_le.2 ⟨by
      have : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
      linarith [hz.2.1, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)], hz.2.2⟩
    linarith [hz.1]

/-- Every compact subset of `H` lies in some box. -/
theorem exists_Kb {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) : ∃ m : ℕ, K ⊆ Kb m := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, empty_subset _⟩
  obtain ⟨z0, hz0, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  have ha : 0 < z0.im := hKH hz0
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  refine ⟨⌈max R (1 / z0.im)⌉₊, fun z hz => ?_⟩
  have hm1 : max R (1 / z0.im) ≤ (⌈max R (1 / z0.im)⌉₊ : ℝ) := Nat.le_ceil _
  have hRm : R ≤ (⌈max R (1 / z0.im)⌉₊ : ℝ) := (le_max_left _ _).trans hm1
  have ham : 1 / z0.im ≤ (⌈max R (1 / z0.im)⌉₊ : ℝ) := (le_max_right _ _).trans hm1
  have hzn := hR z hz
  refine ⟨(Complex.abs_re_le_norm z).trans (hzn.trans hRm), ?_,
    (Complex.im_le_norm z).trans (hzn.trans hRm)⟩
  have hzi : z0.im ≤ z.im := hmin hz
  rw [div_le_iff₀ (by positivity)]
  have : 1 ≤ z0.im * ((⌈max R (1 / z0.im)⌉₊ : ℝ) + 1) := by
    have h1 : z0.im * (1 / z0.im) = 1 := by field_simp
    nlinarith
  nlinarith

/-! ## 2. Countable dense families of Lipschitz functions -/

/-- `N`-Lipschitz continuous functions vanishing off the box `Kb m`. -/
def LipSet (m N : ℕ) : Set C(ℂ, ℝ) := {f | LipschitzWith (N : ℝ≥0) f ∧ ∀ z ∉ Kb m, f z = 0}

theorem exists_dseq (m N : ℕ) : ∃ u : ℕ → C(ℂ, ℝ), (∀ i, u i ∈ LipSet m N) ∧
    ∀ f ∈ LipSet m N, ∃ k : ℕ → ℕ, Tendsto (fun n => u (k n)) atTop (𝓝 f) := by
  have : Nonempty (LipSet m N) :=
    ⟨⟨0, (LipschitzWith.const (0 : ℝ)).weaken (by simp), fun _ _ => rfl⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (LipSet m N)
  refine ⟨fun i => (u i).1, fun i => (u i).2, fun f hf => ?_⟩
  have hmem : (⟨f, hf⟩ : LipSet m N) ∈ closure (range u) := by
    rw [hu.closure_range]; exact mem_univ _
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.1 hmem
  choose k hk using hx
  refine ⟨k, ?_⟩
  have e : (fun n => (u (k n)).1) = fun n => (x n).1 := funext fun n => by rw [hk n]
  rw [e]
  exact (continuous_subtype_val.tendsto _).comp hlim

/-- A dense sequence in `LipSet m N` (compact-open topology). -/
def dseq (m N : ℕ) : ℕ → C(ℂ, ℝ) := Classical.choose (exists_dseq m N)

theorem dseq_mem (m N i : ℕ) : dseq m N i ∈ LipSet m N :=
  (Classical.choose_spec (exists_dseq m N)).1 i

theorem exists_dseq_tendsto {m N : ℕ} {f : C(ℂ, ℝ)} (hf : f ∈ LipSet m N) :
    ∃ k : ℕ → ℕ, Tendsto (fun n => dseq m N (k n)) atTop (𝓝 f) :=
  (Classical.choose_spec (exists_dseq m N)).2 f hf

/-! ## 3. The countable certificate -/

/-- Pairing of the radius increment of the regularized semicircle averages of `x` with `f`. -/
def pairInt (x : FieldSample) (f : ℂ → ℝ) (t s : ℝ) : ℝ :=
  ∫ u, (evalReg x (foldedCircle u t) - evalReg x (foldedCircle u s)) * f u

/-- The Lipschitz modulus of the pairings (all compacts `K ⊆ H`, all Lipschitz `f`). -/
def PairLipMod (x : FieldSample) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ H → ∃ C δ : ℝ, 0 < δ ∧
    ∀ (L : ℝ≥0) (f : ℂ → ℝ), LipschitzWith L f → (∀ z ∉ K, f z = 0) →
      ∀ t ∈ Ioo 0 δ, ∀ s ∈ Ioo 0 δ, |pairInt x f t s| ≤ C * L * Real.sqrt (max t s)

/-- The countable certificate: the modulus on the boxes, for the dense sequences and rational
radii. -/
def CountCond (x : FieldSample) : Prop :=
  ∀ m N : ℕ, ∃ C e : ℕ, ∀ i : ℕ, ∀ t s : ℚ, (0 : ℝ) < t → (t : ℝ) < 1 / ((e : ℝ) + 1) →
    (0 : ℝ) < s → (s : ℝ) < 1 / ((e : ℝ) + 1) →
      |pairInt x (dseq m N i) t s| ≤ (C : ℝ) * N * Real.sqrt (max (t : ℝ) s)

theorem countCond_of_pairLipMod {x : FieldSample} (h : PairLipMod x) : CountCond x := by
  intro m N
  obtain ⟨C, δ, hδ, hb⟩ := h (Kb m) (isCompact_Kb m) (Kb_subset_H m)
  obtain ⟨e, he⟩ := exists_nat_one_div_lt hδ
  refine ⟨⌈C⌉₊, e, fun i t s ht0 ht hs0 hs => ?_⟩
  have hi := dseq_mem m N i
  refine (hb N (dseq m N i) hi.1 hi.2 t ⟨ht0, ht.trans he⟩ s ⟨hs0, hs.trans he⟩).trans ?_
  have : 0 ≤ (N : ℝ) * Real.sqrt (max (t : ℝ) s) := by positivity
  have hC : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
  simp only [NNReal.coe_natCast]
  nlinarith

end G1Rest

/-- **Node G1-REST-PAIR-LIP** (quantitative replacement of `G1RestPairStmt`): for a.e. path
and both sides, almost surely the pulled-back representative `x` has the Lipschitz modulus
`|∫ (h_t(u) - h_s(u)) f(u) du| ≤ C · L · √(max t s)` (`t, s ∈ (0, δ)`, `f` `L`-Lipschitz
vanishing off the compact `K ⊆ H`; `C, δ` depend on the sample and `K`), where
`h_t(u) = evalReg x (foldedCircle u t)`. This is `D3Plus.N2ZPairLipStmt` (scale `c = 1`) for the
pulled-back wedge field. -/
def G1RestPairLipStmt : Prop :=
  G1RepSetting fun γ _ _ P B _ _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
    ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, ∀ᵐ ω' ∂P',
      ∀ K : Set ℂ, IsCompact K → K ⊆ H → ∃ C δ : ℝ, 0 < δ ∧
        ∀ (L : ℝ≥0) (f : ℂ → ℝ), LipschitzWith L f → (∀ z ∉ K, f z = 0) →
          ∀ t ∈ Ioo 0 δ, ∀ s ∈ Ioo 0 δ,
            |∫ u, (evalReg (coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ))
                  (foldedCircle u t) -
                evalReg (coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ))
                  (foldedCircle u s)) * f u| ≤
              C * L * Real.sqrt (max t s)

end Thm18Asm
end QuantumZipper
