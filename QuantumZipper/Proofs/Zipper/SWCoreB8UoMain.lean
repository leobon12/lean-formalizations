import QuantumZipper.Proofs.Zipper.SWCoreB8UoPlus
import QuantumZipper.Proofs.Zipper.F2Step3DensUnif

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B8 (d), part 5: `WedgeUnzip.YMergeOffTipStmt` from the offset anchored input

**Input** (one named hypothesis): `YMergeOffInputStmt` — for every `0 < κ < 4`, Brownian `B` and
independent free field `X`, the offset anchored family input `AnchorUnifFamOffStmt` at every
horizon `T > 0`, for the pair `(B, X)` and for the reflected pair `(−B, X ∘ refl)`
(`AnchorUnifFamOffAllStmt`; offset analogue of `RegUnif.AnchorUnifFamExtAllStmt`, which is proved
as `SWCore.anchorUnifFamExtAllStmt_holds`). It is Sheffield–Wang arXiv:1605.06171 Thm 4.3 with
Thm 1.4 (continuous radius) at the anchors, with the dilation as a family parameter (SWC-B8).

**Main result** `yMergeOffTipStmt_of_offInput : YMergeOffInputStmt → WedgeUnzip.YMergeOffTipStmt`.

Given `t ≥ 0` and `f` with `0 ∉ tsupport f`, pick a horizon `T = n + 1 > t`, split
`f = f₁ + f₂` with `tsupport f₁ ⊂ (−∞, 0)` and `tsupport f₂ ⊂ (0, ∞)` (`exists_split_off_zero`),
and use the minus side (`ae_offTip_minus_off`) and the plus side (`ae_offTip_plus_off`) at the
field `y_t = h⁰_t` (`F2.h0f_eq_unzY`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2

/-- **AC-fam-ext, offset form, at every horizon, for the pair and its reflection.** -/
def AnchorUnifFamOffAllStmt {Ω : Type} [MeasurableSpace Ω] (κ : ℝ) (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  (∀ T : ℝ, 0 < T → AnchorUnifFamOffStmt κ T P B X) ∧
    (∀ T : ℝ, 0 < T → AnchorUnifFamOffStmt κ T P (negB B) (reflX X))

/-- **The input of the offset off-tip node** (SW Thm 4.3/1.4 with offsets, at every horizon,
reflected pair included). -/
def YMergeOffInputStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    AnchorUnifFamOffAllStmt κ P B X

/-- The explicit `ε`–`N` form of Cauchy along `goodFilter` (the form a D70 transfer produces:
`|A_{(k,c)}(s) − A_{(k',c')}(s)| < ε` for all `k, k' ≥ N`, all offsets `c, c' ∈ [1,2]` and all
`s ∈ S`) implies `OffCauchyOn goodFilter`. -/
theorem offCauchyOn_goodFilter_of_explicit {α : Type*} {A : ℕ × ℝ → α → ℝ} {S : Set α}
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∀ k' : ℕ, N ≤ k' →
      ∀ c ∈ Icc (1 : ℝ) 2, ∀ c' ∈ Icc (1 : ℝ) 2, ∀ s ∈ S, |A (k, c) s - A (k', c') s| < ε) :
    OffCauchyOn goodFilter A S := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  have hE : ∀ᶠ j in goodFilter, N ≤ j.1 ∧ j.2 ∈ Icc (1 : ℝ) 2 := by
    have h1 : ∀ᶠ j in goodFilter, N ≤ j.1 :=
      (tendsto_fst (f := (atTop : Filter ℕ)) (g := 𝓟 (Icc (1 : ℝ) 2))).eventually
        (eventually_ge_atTop N)
    have h2 : ∀ᶠ j in goodFilter, j.2 ∈ Icc (1 : ℝ) 2 :=
      (tendsto_snd (f := (atTop : Filter ℕ)) (g := 𝓟 (Icc (1 : ℝ) 2))).eventually
        (eventually_principal.2 fun c hc => hc)
    exact h1.and h2
  filter_upwards [hE.prod_mk hE] with ij hij s hs
  exact hN ij.1.1 hij.1.1 ij.2.1 hij.2.1 ij.1.2 hij.1.2 ij.2.2 hij.2.2 s hs

/-- Splitting a test function whose support avoids `0` into a part supported in `(−∞, 0)` and a
part supported in `(0, ∞)`. -/
theorem exists_split_off_zero {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : (0 : ℝ) ∉ tsupport f) :
    ∃ f₁ f₂ : ℝ → ℝ, Continuous f₁ ∧ HasCompactSupport f₁ ∧ tsupport f₁ ⊆ Iio 0 ∧
      Continuous f₂ ∧ HasCompactSupport f₂ ∧ tsupport f₂ ⊆ Ioi 0 ∧ ∀ t, f t = f₁ t + f₂ t := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (isClosed_tsupport f).isOpen_compl 0 hf0
  have hz : ∀ t : ℝ, -δ < t → t < δ → f t = 0 := fun t h1 h2 =>
    image_eq_zero_of_notMem_tsupport (hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact ⟨h1, h2⟩))
  set χ : ℝ → ℝ := fun t => min 1 (max 0 (-t / δ)) with hχ
  have hχc : Continuous χ :=
    continuous_const.min (continuous_const.max (continuous_neg.div_const _))
  refine ⟨fun t => f t * χ t, fun t => f t * (1 - χ t), hf.mul hχc,
    hfc.mul_right (f' := χ), ?_, hf.mul (continuous_const.sub hχc),
    hfc.mul_right (f' := fun t => 1 - χ t), ?_, fun t => by ring⟩
  · refine (closure_minimal (fun t ht => ?_) isClosed_Iic).trans
      (Iic_subset_Iio.2 (by linarith : -δ < 0))
    have ht' := Function.mem_support.1 ht
    simp only [mem_Iic]
    by_contra h
    rw [not_le] at h
    apply ht'
    rcases le_or_gt 0 t with h0 | h0
    · have h3 : -t / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
      simp only [hχ, max_eq_left h3, min_eq_right zero_le_one, mul_zero]
    · rw [hz t h (by linarith), zero_mul]
  · refine (closure_minimal (fun t ht => ?_) isClosed_Ici).trans (Ici_subset_Ioi.2 hδ)
    have ht' := Function.mem_support.1 ht
    simp only [mem_Ici]
    by_contra h
    rw [not_le] at h
    apply ht'
    rcases le_or_gt t (-δ) with h0 | h0
    · have h1 : 1 ≤ -t / δ := by rw [le_div_iff₀ hδ]; linarith
      simp only [hχ, max_eq_right (by linarith : (0 : ℝ) ≤ -t / δ), min_eq_left h1, sub_self,
        mul_zero]
    · rw [hz t h0 h, zero_mul]

/-- **`YMergeOffTipStmt` from the offset anchored input.** -/
theorem yMergeOffTipStmt_of_offInput (h : YMergeOffInputStmt) : WedgeUnzip.YMergeOffTipStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  obtain ⟨hI1, hI2⟩ := h κ hκ hκ4 P B X hB hX hind
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ,
      (∀ s ∈ Icc (0 : ℝ) ((n : ℝ) + 1), ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
        tsupport g ⊆ Iio 0 →
        Tendsto (WedgeUnzip.bdryMergeDiff (Real.sqrt κ) (h0f κ s B X ω) g) goodFilter (𝓝 0)) ∧
      (∀ s ∈ Icc (0 : ℝ) ((n : ℝ) + 1), ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
        tsupport g ⊆ Ioi 0 →
        Tendsto (WedgeUnzip.bdryMergeDiff (Real.sqrt κ) (h0f κ s B X ω) g) goodFilter (𝓝 0)) :=
    ae_all_iff.2 fun n =>
      (ae_offTip_minus_off hκ hκ4 (by positivity) hB hX hind (hI1 _ (by positivity))).and
        (ae_offTip_plus_off hκ hκ4 (by positivity) hB hX hind (hI2 _ (by positivity)))
  filter_upwards [hall, WedgeUnzip.ae_forall_isRegularSample_unzY (κ := κ) hB hX hind]
    with ω hω hreg t ht f hf hfc hf0
  obtain ⟨n, hn⟩ := exists_nat_gt t
  have hts : t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) := ⟨ht, by linarith⟩
  obtain ⟨f₁, f₂, hc1, hcs1, hs1, hc2, hcs2, hs2, hsum⟩ := exists_split_off_zero hf hfc hf0
  have e : F2.unzY κ (X ω) (drive κ B ω) t = h0f κ t B X ω := (F2.h0f_eq_unzY κ t B X ω).symm
  have h1 := (hω n).1 t hts f₁ hc1 hcs1 hs1
  have h2 := (hω n).2 t hts f₂ hc2 hcs2 hs2
  obtain ⟨F, hF⟩ := hreg t ht
  rw [e] at hF ⊢
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [GoodSample.eventually_goodRad_pos] with i hi
  simp only [WedgeUnzip.bdryMergeDiff]
  have hf_eq : f = fun t => f₁ t + f₂ t := funext hsum
  rw [hf_eq, integral_add (WedgeUnzip.integrable_bdryR_of_reg hF hi hc1 hcs1)
      (WedgeUnzip.integrable_bdryR_of_reg hF hi hc2 hcs2),
    integral_add (WedgeUnzip.integrable_bdryR_of_reg hF (radius_pos _) hc1 hcs1)
      (WedgeUnzip.integrable_bdryR_of_reg hF (radius_pos _) hc2 hcs2)]
  ring

end RegUnif
end QuantumZipper
