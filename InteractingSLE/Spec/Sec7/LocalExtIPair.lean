/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtGStmt

/-!
# The source of Aux. lemma 55 for a random word: measurability in the force positions

Packet PROVE-LOCEXT-I. At a restart (Aux. lemma 53) the force positions are the **current** positions `V_T − W_T`,
random and `𝓓_T`-measurable. The Cameron–Martin density (HL3) of the time-`0` construction pairs the field with the source
`v = −(2π)⁻¹ Δ(χ q)` of the word through a fast subsequence of the approximations `v_n` (`pairSeq`), chosen **per word**
(PROVE-LOCEXT-G's obstruction: `srcPair` is not measurable in the word). This file makes every ingredient a jointly
measurable function of the word:

* `IsAdmWord r x`: `x = (xL, xR)` is an ordered force word with seed radius `r`; a measurable set of words;
* `measurable_qExt_word`, `measurable_fCut_word`: `(x, z) ↦ q_x(z)`, `(x, z) ↦ (χ q_x)(z)` are jointly measurable;
* `measurable_indicator_fderiv_apply`: derivatives of a family `g x` (differentiable on a measurable set of
  parameters) are measurable in the parameter (difference quotients, `HasFDerivAt.lim`);
* **`vDensW`**: the source density `vDens` of an admissible word, `0` for the others; **jointly measurable** in the word
  and the point (`measurable_vDensW`: measurability in the word through the two difference-quotient levels of the
  Laplacian, continuity in the point, Carathéodory);
* `vApproxW`, `vApproxTestW`: the approximations `v_n` of an admissible word (test functions), `0` for the others;
  `measurable_apply_vApproxTestW`: `(x, T) ↦ T(v_n^x)` is jointly measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE

namespace LocalExt

/-! ### Admissible words -/

section Words

variable {nL nR : ℕ}

/-- `x = (xL, xR)` is an ordered force word and `r` is a seed radius for it. -/
def IsAdmWord (r : ℝ) (x : (Fin nL → ℝ) × (Fin nR → ℝ)) : Prop :=
  IsOrderedForceWord x.1 x.2 ∧ IsSeedRadius x.1 x.2 r

theorem measurableSet_isAdmWord (r : ℝ) :
    MeasurableSet {x : (Fin nL → ℝ) × (Fin nR → ℝ) | IsAdmWord r x} := by
  have hL : ∀ i, Measurable fun x : (Fin nL → ℝ) × (Fin nR → ℝ) => x.1 i := fun i =>
    (measurable_pi_apply i).comp measurable_fst
  have hR : ∀ j, Measurable fun x : (Fin nL → ℝ) × (Fin nR → ℝ) => x.2 j := fun j =>
    (measurable_pi_apply j).comp measurable_snd
  refine measurableSet_setOfPred.2 (Measurable.and ?_ ?_)
  · refine Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ ?_))
    · exact Measurable.forall fun a => Measurable.forall fun b => measurable_const.imp
        (measurableSet_setOfPred.1 (measurableSet_le (hL b) (hL a)))
    · exact Measurable.forall fun i => measurableSet_setOfPred.1 (measurableSet_le (hL i) measurable_const)
    · exact Measurable.forall fun a => Measurable.forall fun b => measurable_const.imp
        (measurableSet_setOfPred.1 (measurableSet_le (hR a) (hR b)))
    · exact Measurable.forall fun i => measurableSet_setOfPred.1 (measurableSet_le measurable_const (hR i))
  · refine Measurable.and measurable_const (Measurable.and ?_ ?_)
    · exact Measurable.forall fun i => (measurableSet_setOfPred.1
        (measurableSet_eq_fun (hL i) measurable_const)).not.imp
        (measurableSet_setOfPred.1 (measurableSet_lt measurable_const (hL i).abs))
    · exact Measurable.forall fun j => (measurableSet_setOfPred.1
        (measurableSet_eq_fun (hR j) measurable_const)).not.imp
        (measurableSet_setOfPred.1 (measurableSet_lt measurable_const (hR j).abs))

end Words

/-! ### Derivatives of a measurable family -/

section Deriv

/-- **Directional derivatives of a parametrized family are measurable in the parameter**: if `g x w` is measurable
in `x` for every `w`, and `g x` is differentiable at `z` for every `x` in a measurable set `S`, then
`x ↦ 1_S(x) · Dg_x(z) v` is measurable (a pointwise limit of difference quotients). -/
theorem measurable_indicator_fderiv_apply {X : Type*} [MeasurableSpace X] {S : Set X} (hS : MeasurableSet S)
    {g : X → ℂ → ℝ} (hg : ∀ w, Measurable fun x => g x w) {z : ℂ}
    (hd : ∀ x ∈ S, DifferentiableAt ℝ (g x) z) (v : ℂ) :
    Measurable (S.indicator fun x => fderiv ℝ (g x) z v) := by
  have hc : Tendsto (fun n : ℕ => ‖((n : ℝ) + 1)‖) atTop atTop := by
    refine (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).congr fun n => ?_
    rw [Real.norm_of_nonneg (by positivity)]
  have ht : ∀ x, Tendsto (fun n : ℕ => S.indicator (fun x =>
      ((n : ℝ) + 1) * (g x (z + ((n : ℝ) + 1)⁻¹ • v) - g x z)) x) atTop
      (𝓝 (S.indicator (fun x => fderiv ℝ (g x) z v) x)) := by
    intro x
    by_cases hx : x ∈ S
    · simp only [indicator_of_mem hx]
      exact (hd x hx).hasFDerivAt.lim v hc
    · simp only [indicator_of_notMem hx]
      exact tendsto_const_nhds
  refine measurable_of_tendsto_metrizable (fun n => ?_) (tendsto_pi_nhds.2 ht)
  exact (measurable_const.mul ((hg _).sub (hg z))).indicator hS

end Deriv

/-! ### The source density as a function of the word -/

section Source

variable {nL nR : ℕ} (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ)

/-- `q_x(z)` is jointly measurable in the word and the point. -/
theorem measurable_qExt_word :
    Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ => qExt κ p.1.1 p.1.2 ρL ρR p.2 := by
  simp_rw [qExt_eq_sum_ite]
  refine measurable_const.mul (Measurable.add (Finset.measurable_sum _ fun i _ => ?_)
    (Finset.measurable_sum _ fun j _ => ?_))
  · have hxi : Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ => p.1.1 i :=
      (measurable_pi_apply i).comp measurable_fst.fst
    refine Measurable.ite ?_ (measurable_const.mul (Complex.measurable_arg.comp
      (measurable_snd.sub (Complex.measurable_ofReal.comp hxi)))) measurable_const
    exact (measurableSet_eq_fun hxi measurable_const).compl
  · have hxj : Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ => p.1.2 j :=
      (measurable_pi_apply j).comp measurable_fst.snd
    refine Measurable.ite ?_ (measurable_const.mul (Complex.measurable_arg.comp
      ((Complex.measurable_ofReal.comp hxj).sub measurable_snd))) measurable_const
    exact (measurableSet_eq_fun hxj measurable_const).compl

/-- `(χ q_x)(z)` is jointly measurable in the word and the point. -/
theorem measurable_fCut_word :
    Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ => fCut κ p.1.1 p.1.2 ρL ρR r p.2 :=
  ((contDiff_cutoffFn.continuous (n := 0)).measurable.comp measurable_snd).mul (measurable_qExt_word κ ρL ρR)

/-- **The source density of a word**: `vDens` for an admissible word, `0` otherwise. -/
def vDensW (x : (Fin nL → ℝ) × (Fin nR → ℝ)) (z : ℂ) : ℝ :=
  {x : (Fin nL → ℝ) × (Fin nR → ℝ) | IsAdmWord r x}.indicator (fun x => vDens κ x.1 x.2 ρL ρR r z) x

theorem vDensW_of_adm {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : IsAdmWord r x) (z : ℂ) :
    vDensW κ ρL ρR r x z = vDens κ x.1 x.2 ρL ρR r z := by
  simp only [vDensW, indicator_of_mem (show x ∈ {x | IsAdmWord r x} from hx)]

theorem vDensW_of_not_adm {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : ¬ IsAdmWord r x) (z : ℂ) :
    vDensW κ ρL ρR r x z = 0 := by
  simp only [vDensW, indicator_of_notMem (show x ∉ {x | IsAdmWord r x} from hx)]

theorem vDensW_eq_of_adm {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : IsAdmWord r x) :
    vDensW κ ρL ρR r x = vDens κ x.1 x.2 ρL ρR r :=
  funext (vDensW_of_adm κ ρL ρR r hx)

theorem vDensW_eq_of_not_adm {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : ¬ IsAdmWord r x) :
    vDensW κ ρL ρR r x = 0 :=
  funext (vDensW_of_not_adm κ ρL ρR r hx)

theorem continuous_vDensW (x : (Fin nL → ℝ) × (Fin nR → ℝ)) : Continuous (vDensW κ ρL ρR r x) := by
  by_cases hx : IsAdmWord r x
  · rw [vDensW_eq_of_adm κ ρL ρR r hx]
    exact continuous_vDens hx.1 hx.2
  · rw [vDensW_eq_of_not_adm κ ρL ρR r hx]
    exact continuous_const

theorem contDiff_fCut_of_adm {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : IsAdmWord r x) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fCut κ x.1 x.2 ρL ρR r) :=
  contDiff_fCut hx.1 hx.2

theorem measurable_fCut_word_apply (w : ℂ) :
    Measurable fun x : (Fin nL → ℝ) × (Fin nR → ℝ) => fCut κ x.1 x.2 ρL ρR r w := by
  have h := (measurable_fCut_word κ ρL ρR r).comp
    ((measurable_id (α := (Fin nL → ℝ) × (Fin nR → ℝ))).prodMk (measurable_const (a := w)))
  exact h

/-- First derivatives of `χ q_x`, measurably in the word. -/
theorem measurable_fderiv_fCut_apply (v w : ℂ) :
    Measurable ({x : (Fin nL → ℝ) × (Fin nR → ℝ) | IsAdmWord r x}.indicator
      fun x => fderiv ℝ (fCut κ x.1 x.2 ρL ρR r) w v) :=
  measurable_indicator_fderiv_apply (g := fun x => fCut κ x.1 x.2 ρL ρR r) (measurableSet_isAdmWord r)
    (measurable_fCut_word_apply κ ρL ρR r)
    (fun x hx => ((contDiff_fCut_of_adm κ ρL ρR r hx).differentiable (by simp)).differentiableAt) v

/-- Second derivatives of `χ q_x`, measurably in the word. -/
theorem measurable_fderiv_fderiv_fCut_apply (v z : ℂ) :
    Measurable ({x : (Fin nL → ℝ) × (Fin nR → ℝ) | IsAdmWord r x}.indicator
      fun x => fderiv ℝ (fun y => fderiv ℝ (fCut κ x.1 x.2 ρL ρR r) y v) z v) := by
  have hm := measurable_indicator_fderiv_apply
    (g := fun x y => {x : (Fin nL → ℝ) × (Fin nR → ℝ) | IsAdmWord r x}.indicator
      (fun x => fderiv ℝ (fCut κ x.1 x.2 ρL ρR r) y v) x) (z := z)
    (measurableSet_isAdmWord r) (fun w => measurable_fderiv_fCut_apply κ ρL ρR r v w) ?_ v
  · convert hm using 1
    funext x
    by_cases hx : IsAdmWord r x
    · simp only [indicator_of_mem (show x ∈ {x : (Fin nL → ℝ) × (Fin nR → ℝ) | IsAdmWord r x} from hx)]
    · simp only [indicator_of_notMem (show x ∉ {x : (Fin nL → ℝ) × (Fin nR → ℝ) | IsAdmWord r x} from hx)]
  · intro x hx
    have e : (fun y => {x : (Fin nL → ℝ) × (Fin nR → ℝ) | IsAdmWord r x}.indicator
        (fun x => fderiv ℝ (fCut κ x.1 x.2 ρL ρR r) y v) x) =
          fun y => fderiv ℝ (fCut κ x.1 x.2 ρL ρR r) y v :=
      funext fun y => indicator_of_mem hx _
    rw [e]
    have hc := (contDiff_fCut_of_adm κ ρL ρR r hx).fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
    exact ((hc.clm_apply contDiff_const).differentiable (by simp)).differentiableAt

/-- The source density through the second derivatives (for every word). -/
theorem vDensW_eq_fderiv (x : (Fin nL → ℝ) × (Fin nR → ℝ)) (z : ℂ) :
    vDensW κ ρL ρR r x z = -(2 * Real.pi)⁻¹ *
      ({x : (Fin nL → ℝ) × (Fin nR → ℝ) | IsAdmWord r x}.indicator
          (fun x => fderiv ℝ (fun y => fderiv ℝ (fCut κ x.1 x.2 ρL ρR r) y 1) z 1) x +
        {x : (Fin nL → ℝ) × (Fin nR → ℝ) | IsAdmWord r x}.indicator
          (fun x => fderiv ℝ (fun y => fderiv ℝ (fCut κ x.1 x.2 ρL ρR r) y Complex.I) z Complex.I) x) := by
  by_cases hx : IsAdmWord r x
  · rw [vDensW_of_adm κ ρL ρR r hx, indicator_of_mem (show x ∈ {x | IsAdmWord r x} from hx),
      indicator_of_mem (show x ∈ {x | IsAdmWord r x} from hx)]
    change QuantumZipper.K3.greenDensity (fCut κ x.1 x.2 ρL ρR r) z = _
    rw [QuantumZipper.K3.greenDensity,
      QuantumZipper.K3.laplacian_eq_fderiv_fderiv ((contDiff_fCut_of_adm κ ρL ρR r hx).of_le (by simp))]
  · rw [vDensW_of_not_adm κ ρL ρR r hx, indicator_of_notMem (show x ∉ {x | IsAdmWord r x} from hx),
      indicator_of_notMem (show x ∉ {x | IsAdmWord r x} from hx), add_zero, mul_zero]

/-- For every point, the source density is a measurable function of the word (the Laplacian of `χ q_x` through two
levels of difference quotients). -/
theorem measurable_vDensW_apply (z : ℂ) : Measurable fun x => vDensW κ ρL ρR r x z := by
  simp_rw [vDensW_eq_fderiv κ ρL ρR r _ z]
  exact measurable_const.mul ((measurable_fderiv_fderiv_fCut_apply κ ρL ρR r 1 z).add
    (measurable_fderiv_fderiv_fCut_apply κ ρL ρR r Complex.I z))

/-- **The source density is jointly measurable in the word and the point.** -/
theorem measurable_vDensW :
    Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ => vDensW κ ρL ρR r p.1 p.2 := by
  have h := measurable_uncurry_of_continuous_of_measurable (u := fun (z : ℂ) (x : (Fin nL → ℝ) × (Fin nR → ℝ)) =>
    vDensW κ ρL ρR r x z) (fun x => continuous_vDensW κ ρL ρR r x) (fun z => measurable_vDensW_apply κ ρL ρR r z)
  exact h.comp measurable_swap

/-- The approximation `v_n = cutIm n · v` of the source of a word (`0` for a non-admissible word). -/
def vApproxW (x : (Fin nL → ℝ) × (Fin nR → ℝ)) (n : ℕ) (z : ℂ) : ℝ := cutIm n z * vDensW κ ρL ρR r x z

theorem vApproxW_of_adm {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : IsAdmWord r x) (n : ℕ) (z : ℂ) :
    vApproxW κ ρL ρR r x n z = vApprox κ x.1 x.2 ρL ρR r n z := by
  rw [vApproxW, vDensW_of_adm κ ρL ρR r hx, vApprox]

theorem measurable_vApproxW (n : ℕ) :
    Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ => vApproxW κ ρL ρR r p.1 n p.2 :=
  ((contDiff_cutIm n (k := 0)).continuous.measurable.comp measurable_snd).mul (measurable_vDensW κ ρL ρR r)

open Classical in
/-- The approximation `v_n` of an admissible word as a test function on `ℍ` (`0` for the others). -/
def vApproxTestW (x : (Fin nL → ℝ) × (Fin nR → ℝ)) (n : ℕ) : LQGMetric.TestOn upperHalfPlaneOpens :=
  if hx : IsAdmWord r x then vApproxTest (κ := κ) (ρL := ρL) (ρR := ρR) hx.1 hx.2 n else 0

theorem vApproxTestW_apply (x : (Fin nL → ℝ) × (Fin nR → ℝ)) (n : ℕ) (z : ℂ) :
    vApproxTestW κ ρL ρR r x n z = vApproxW κ ρL ρR r x n z := by
  by_cases hx : IsAdmWord r x
  · rw [vApproxTestW, dite_eq_left_of_eq_true (eq_true hx), vApproxTest_apply, vApproxW_of_adm κ ρL ρR r hx]
  · rw [vApproxTestW, dite_eq_right_of_eq_false (eq_false hx), vApproxW, vDensW_of_not_adm κ ρL ρR r hx, mul_zero]
    rfl

/-- **`(x, T) ↦ T(v_n^x)` is jointly measurable.** -/
theorem measurable_apply_vApproxTestW (n : ℕ) :
    Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × LQGMetric.DistOn upperHalfPlaneOpens =>
      p.2 (vApproxTestW κ ρL ρR r p.1 n) := by
  refine RandomTest.measurable_apply_of_forall_measurable measurable_snd fun z => ?_
  simp_rw [vApproxTestW_apply]
  exact ((measurable_vApproxW κ ρL ρR r n).comp (measurable_id.prodMk measurable_const)).comp measurable_fst

end Source


/-! ### A fast subsequence chosen measurably in the word -/

section FastSeq

variable {nL nR : ℕ} (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ)

/-- The Green energy `G_ℍ(v_n − v_m, v_n − v_m)` of a word. -/
def pairEnergyW (x : (Fin nL → ℝ) × (Fin nR → ℝ)) (n m : ℕ) : ℝ :=
  greenEnergy (fun z => vApproxW κ ρL ρR r x n z - vApproxW κ ρL ρR r x m z)
    (fun z => vApproxW κ ρL ρR r x n z - vApproxW κ ρL ρR r x m z)

theorem measurable_pairEnergyW (n m : ℕ) : Measurable fun x => pairEnergyW κ ρL ρR r x n m := by
  have hv : ∀ k, Measurable fun q : ((Fin nL → ℝ) × (Fin nR → ℝ)) × (ℂ × ℂ) => vApproxW κ ρL ρR r q.1 k q.2.1 :=
    fun k => (measurable_vApproxW κ ρL ρR r k).comp (measurable_fst.prodMk measurable_snd.fst)
  have hv' : ∀ k, Measurable fun q : ((Fin nL → ℝ) × (Fin nR → ℝ)) × (ℂ × ℂ) => vApproxW κ ρL ρR r q.1 k q.2.2 :=
    fun k => (measurable_vApproxW κ ρL ρR r k).comp (measurable_fst.prodMk measurable_snd.snd)
  have hF : Measurable fun q : ((Fin nL → ℝ) × (Fin nR → ℝ)) × (ℂ × ℂ) =>
      (vApproxW κ ρL ρR r q.1 n q.2.1 - vApproxW κ ρL ρR r q.1 m q.2.1) *
        (vApproxW κ ρL ρR r q.1 n q.2.2 - vApproxW κ ρL ρR r q.1 m q.2.2) * QuantumZipper.greenH q.2.1 q.2.2 :=
    (((hv n).sub (hv m)).mul ((hv' n).sub (hv' m))).mul (QuantumZipper.measurable_greenH.comp measurable_snd)
  exact (hF.stronglyMeasurable.integral_prod_right (ν := (volume : Measure ℂ).prod volume)).measurable

/-- For an admissible word, the energies of `v_n − v_m` are eventually below `16^{-k}`. -/
theorem exists_pairIdx {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : IsAdmWord r x) (k : ℕ) :
    ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m → pairEnergyW κ ρL ρR r x n m < (1 / 16 : ℝ) ^ k := by
  obtain ⟨N, hN⟩ := (eventually_greenEnergy_vApprox_sub_lt (κ := κ) (ρL := ρL) (ρR := ρR) hx.1 hx.2
    (show (0 : ℝ) < (1 / 16) ^ k by positivity)).exists
  refine ⟨N, fun n m hn hm => ?_⟩
  have e : ∀ j z, vApproxW κ ρL ρR r x j z = vApprox κ x.1 x.2 ρL ρR r j z := fun j z =>
    vApproxW_of_adm κ ρL ρR r hx j z
  simp only [pairEnergyW, e]
  exact hN n m hn hm

/-- The predicate selecting the fast index: the word is not admissible, or the energies beyond `N` are small. -/
def PairIdxProp (k : ℕ) (x : (Fin nL → ℝ) × (Fin nR → ℝ)) (N : ℕ) : Prop :=
  ¬ IsAdmWord r x ∨ ∀ n m : ℕ, N ≤ n → N ≤ m → pairEnergyW κ ρL ρR r x n m < (1 / 16 : ℝ) ^ k

theorem exists_pairIdxProp (k : ℕ) (x : (Fin nL → ℝ) × (Fin nR → ℝ)) :
    ∃ N, PairIdxProp κ ρL ρR r k x N := by
  by_cases hx : IsAdmWord r x
  · obtain ⟨N, hN⟩ := exists_pairIdx κ ρL ρR r hx k
    exact ⟨N, Or.inr hN⟩
  · exact ⟨0, Or.inl hx⟩

open Classical in
/-- The least admissible index of the `k`-th fast level (`0` for a non-admissible word). -/
def pairIdxW (k : ℕ) (x : (Fin nL → ℝ) × (Fin nR → ℝ)) : ℕ := Nat.find (exists_pairIdxProp κ ρL ρR r k x)

theorem measurable_pairIdxW (k : ℕ) : Measurable (pairIdxW (nL := nL) (nR := nR) κ ρL ρR r k) := by
  classical
  refine measurable_find (exists_pairIdxProp κ ρL ρR r k) fun N => ?_
  refine measurableSet_setOfPred.2 (Measurable.or ?_ ?_)
  · exact (measurableSet_setOfPred.1 (measurableSet_isAdmWord r)).not
  · exact Measurable.forall fun n => Measurable.forall fun m => measurable_const.imp (measurable_const.imp
      (measurableSet_setOfPred.1 (measurableSet_lt (measurable_pairEnergyW κ ρL ρR r n m) measurable_const)))

theorem pairEnergyW_lt_of_pairIdxW_le {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : IsAdmWord r x) {k n m : ℕ}
    (hn : pairIdxW κ ρL ρR r k x ≤ n) (hm : pairIdxW κ ρL ρR r k x ≤ m) :
    pairEnergyW κ ρL ρR r x n m < (1 / 16 : ℝ) ^ k := by
  classical
  have h := Nat.find_spec (exists_pairIdxProp κ ρL ρR r k x)
  rcases h with h | h
  · exact absurd hx h
  · exact h n m hn hm

/-- **The fast subsequence of a word, measurable in the word**: `n_k(x) = ∑_{j ≤ k} N_j(x) + k`. -/
def pairSeqW (x : (Fin nL → ℝ) × (Fin nR → ℝ)) (k : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (k + 1), pairIdxW κ ρL ρR r j x) + k

theorem measurable_pairSeqW (k : ℕ) :
    Measurable fun x : (Fin nL → ℝ) × (Fin nR → ℝ) => pairSeqW κ ρL ρR r x k := by
  have h : Measurable fun x : (Fin nL → ℝ) × (Fin nR → ℝ) =>
      ∑ j ∈ Finset.range (k + 1), pairIdxW κ ρL ρR r j x :=
    Finset.measurable_sum _ fun j _ => measurable_pairIdxW κ ρL ρR r j
  exact h.add_const k

theorem strictMono_pairSeqW (x : (Fin nL → ℝ) × (Fin nR → ℝ)) : StrictMono (pairSeqW κ ρL ρR r x) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  simp only [pairSeqW, Finset.sum_range_succ (n := k + 1)]
  omega

theorem pairIdxW_le_pairSeqW (x : (Fin nL → ℝ) × (Fin nR → ℝ)) (k : ℕ) :
    pairIdxW κ ρL ρR r k x ≤ pairSeqW κ ρL ρR r x k := by
  have h : pairIdxW κ ρL ρR r k x ≤ ∑ j ∈ Finset.range (k + 1), pairIdxW κ ρL ρR r j x :=
    Finset.single_le_sum (f := fun j => pairIdxW κ ρL ρR r j x) (fun _ _ => Nat.zero_le _)
      (Finset.self_mem_range_succ k)
  exact h.trans (Nat.le_add_right _ _)

/-- **The energies along the fast subsequence**: `G_ℍ(v_n − v_m) < 16^{-k}` for `n, m ≥ n_k(x)`. -/
theorem pairEnergyW_lt {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : IsAdmWord r x) {k n m : ℕ}
    (hn : pairSeqW κ ρL ρR r x k ≤ n) (hm : pairSeqW κ ρL ρR r x k ≤ m) :
    pairEnergyW κ ρL ρR r x n m < (1 / 16 : ℝ) ^ k :=
  pairEnergyW_lt_of_pairIdxW_le κ ρL ρR r hx ((pairIdxW_le_pairSeqW κ ρL ρR r x k).trans hn)
    ((pairIdxW_le_pairSeqW κ ρL ρR r x k).trans hm)

/-- The approximating test function `v_{n_k(x)}` of a word. -/
def srcTestW (x : (Fin nL → ℝ) × (Fin nR → ℝ)) (k : ℕ) : LQGMetric.TestOn upperHalfPlaneOpens :=
  vApproxTestW κ ρL ρR r x (pairSeqW κ ρL ρR r x k)

theorem srcTestW_apply (x : (Fin nL → ℝ) × (Fin nR → ℝ)) (k : ℕ) (z : ℂ) :
    srcTestW κ ρL ρR r x k z = vApproxW κ ρL ρR r x (pairSeqW κ ρL ρR r x k) z :=
  vApproxTestW_apply κ ρL ρR r x _ z

theorem measurable_srcTestW_apply (k : ℕ) :
    Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ => srcTestW κ ρL ρR r p.1 k p.2 := by
  have h : Measurable fun q : (((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ) × ℕ => vApproxW κ ρL ρR r q.1.1 q.2 q.1.2 :=
    measurable_from_prod_countable_left fun N => by
      have h := measurable_vApproxW κ ρL ρR r N
      exact h
  have h2 := h.comp ((measurable_id (α := ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ)).prodMk
    ((measurable_pairSeqW κ ρL ρR r k).comp measurable_fst))
  have e : (fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ => srcTestW κ ρL ρR r p.1 k p.2) =
      (fun q : (((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ) × ℕ => vApproxW κ ρL ρR r q.1.1 q.2 q.1.2) ∘
        fun p => (p, pairSeqW κ ρL ρR r p.1 k) :=
    funext fun p => srcTestW_apply κ ρL ρR r p.1 k p.2
  rw [e]
  exact h2

/-- `(x, T) ↦ T(v_{n_k(x)})` is jointly measurable. -/
theorem measurable_apply_srcTestW (k : ℕ) :
    Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × LQGMetric.DistOn upperHalfPlaneOpens =>
      p.2 (srcTestW κ ρL ρR r p.1 k) := by
  refine RandomTest.measurable_apply_of_forall_measurable measurable_snd fun z => ?_
  have h := (measurable_srcTestW_apply κ ρL ρR r k).comp
    ((measurable_id (α := (Fin nL → ℝ) × (Fin nR → ℝ))).prodMk (measurable_const (a := z)))
  exact h.comp measurable_fst

/-- **The GFF pairing with the source of a word**, jointly Borel in the word and the field:
`(T, v_x) := lim_k T(v_{n_k(x)})` (`limUnder`). -/
def srcPairW (x : (Fin nL → ℝ) × (Fin nR → ℝ)) (T : LQGMetric.DistOn upperHalfPlaneOpens) : ℝ :=
  limUnder atTop fun k => T (srcTestW κ ρL ρR r x k)

theorem measurable_srcPairW :
    Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × LQGMetric.DistOn upperHalfPlaneOpens =>
      srcPairW κ ρL ρR r p.1 p.2 :=
  (StronglyMeasurable.limUnder fun k => (measurable_apply_srcTestW κ ρL ρR r k).stronglyMeasurable).measurable

end FastSeq


/-! ### Almost sure convergence for a random word -/

section RandomConv

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {𝒢 mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- `‖g‖_{L²} ≤ √a` from `∫ g² ≤ a`. -/
theorem eLpNorm_two_le_of_lintegral_sq {g : Ω → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h : ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂P ≤ ENNReal.ofReal a) :
    eLpNorm g 2 P ≤ ENNReal.ofReal (Real.sqrt a) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofNat_ne_top]
  have e : ∀ ω, ‖g ω‖ₑ ^ (((2 : ℝ≥0∞)).toReal) = ENNReal.ofReal (g ω ^ 2) := fun ω => by
    rw [Real.enorm_eq_ofReal_abs, show ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp_rw [e]
  rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ha (by norm_num)]
  exact ENNReal.rpow_le_rpow h (by norm_num)

/-- The means `∫ u v_{n_k(x)}` converge to `∫ u v_x` for an admissible word. -/
theorem tendsto_integral_mul_srcTestW {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : IsAdmWord r x) {u : ℂ → ℝ}
    (hu : ContinuousOn u H) {C : ℝ} (hC : ∀ z ∈ H, |u z| ≤ C) :
    Tendsto (fun k => ∫ z, u z * srcTestW κ ρL ρR r x k z) atTop
      (𝓝 (∫ z, u z * vSrc κ x.1 x.2 ρL ρR r z)) := by
  refine tendsto_integral_of_dominated_convergence (fun z => C * |vSrc κ x.1 x.2 ρL ρR r z|)
    (fun k => (integrable_mul_testOn hu (srcTestW κ ρL ρR r x k)).aestronglyMeasurable)
    ((integrable_vSrc hx.1 hx.2).abs.const_mul C) (fun k => ae_of_all _ fun z => ?_) (ae_of_all _ fun z => ?_)
  · rw [Real.norm_eq_abs, abs_mul, srcTestW_apply, vApproxW_of_adm κ ρL ρR r hx]
    by_cases hz : z ∈ H
    · exact mul_le_mul (hC z hz) (abs_vApprox_le _ z) (abs_nonneg _) ((abs_nonneg _).trans (hC z hz))
    · have h0 : vSrc κ x.1 x.2 ρL ρR r z = 0 := by rw [vSrc, Set.indicator_of_notMem hz]
      have h1 := abs_vApprox_le (κ := κ) (ρL := ρL) (ρR := ρR) (xL := x.1) (xR := x.2) (r := r)
        (pairSeqW κ ρL ρR r x k) z
      rw [h0, abs_zero] at h1
      rw [abs_nonpos_iff.1 h1, h0, abs_zero, mul_zero, mul_zero]
  · simp only [srcTestW_apply, vApproxW_of_adm κ ρL ρR r hx]
    exact tendsto_const_nhds.mul ((tendsto_vApprox z).comp (strictMono_pairSeqW κ ρL ρR r x).tendsto_atTop)

omit [MeasurableSpace Ω] in
theorem greenEnergy_srcTestW_sub (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ)
    (x : (Fin nL → ℝ) × (Fin nR → ℝ)) (n m : ℕ) :
    greenEnergy (⇑(srcTestW κ ρL ρR r x n - srcTestW κ ρL ρR r x m))
        (⇑(srcTestW κ ρL ρR r x n - srcTestW κ ρL ρR r x m)) =
      pairEnergyW κ ρL ρR r x (pairSeqW κ ρL ρR r x n) (pairSeqW κ ρL ρR r x m) := by
  have e : (⇑(srcTestW κ ρL ρR r x n - srcTestW κ ρL ρR r x m)) = fun z =>
      vApproxW κ ρL ρR r x (pairSeqW κ ρL ρR r x n) z - vApproxW κ ρL ρR r x (pairSeqW κ ρL ρR r x m) z := by
    funext z
    rw [← srcTestW_apply, ← srcTestW_apply]
    rfl
  rw [e]
  rfl

theorem measurable_pairEnergyW_seq (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ) (n m : ℕ) :
    Measurable fun x : (Fin nL → ℝ) × (Fin nR → ℝ) =>
      pairEnergyW κ ρL ρR r x (pairSeqW κ ρL ρR r x n) (pairSeqW κ ρL ρR r x m) := by
  have h2 : Measurable fun q : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℕ × ℕ =>
      pairEnergyW κ ρL ρR r q.1 q.2.1 q.2.2 :=
    measurable_from_prod_countable_left fun p => by
      have h := measurable_pairEnergyW κ ρL ρR r p.1 p.2
      exact h
  have h3 := h2.comp ((measurable_id (α := (Fin nL → ℝ) × (Fin nR → ℝ))).prodMk
    ((measurable_pairSeqW κ ρL ρR r n).prodMk (measurable_pairSeqW κ ρL ρR r m)))
  exact h3

/-- **The approximate pairings with the source of a random word converge almost surely** to the jointly Borel
pairing `srcPairW`. Hypotheses: the word `c` is `𝒢`-measurable and admissible; conditionally on `𝒢`, the field is
a zero-boundary GFF on `ℍ` around a `𝒢`-measurable mean `u` (bounded by `C`, continuous on `ℍ`), in the form of the
conditional characteristic functions of the centred pairings with every `𝒢`-measurable random test function. -/
theorem ae_tendsto_srcPairW [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ)
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)} (hc : Measurable[𝒢] c) (hadm : ∀ ω, IsAdmWord r (c ω))
    {u : Ω → ℂ → ℝ} (hum : Measurable (Function.uncurry u)) (hu : ∀ ω, ContinuousOn (u ω) H) {C : ℝ}
    (hC : ∀ ω, ∀ z ∈ H, |u ω z| ≤ C)
    (hcf : ∀ φ : Ω → LQGMetric.TestOn upperHalfPlaneOpens, (∀ z, Measurable[𝒢] fun ω => φ ω z) → ∀ t : ℝ,
      P[fun ω => Complex.exp (Complex.I * ((t * (h ω (φ ω) - ∫ z, u ω z * φ ω z) : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
        fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * greenEnergy (φ ω) (φ ω)))) : ℂ)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => h ω (srcTestW κ ρL ρR r (c ω) k)) atTop
      (𝓝 (srcPairW κ ρL ρR r (c ω) (h ω))) := by
  have hcm : Measurable c := hc.mono h𝒢 le_rfl
  set f : ℕ → Ω → ℝ := fun k ω =>
    h ω (srcTestW κ ρL ρR r (c ω) k) - ∫ z, u ω z * srcTestW κ ρL ρR r (c ω) k z with hf
  -- measurability
  have hpair : ∀ k, Measurable fun ω => h ω (srcTestW κ ρL ρR r (c ω) k) := fun k =>
    (measurable_apply_srcTestW κ ρL ρR r k).comp (hcm.prodMk hh)
  have hmean : ∀ k, Measurable fun ω => ∫ z, u ω z * srcTestW κ ρL ρR r (c ω) k z := by
    intro k
    have hj : Measurable fun q : Ω × ℂ => u q.1 q.2 * srcTestW κ ρL ρR r (c q.1) k q.2 :=
      hum.mul ((measurable_srcTestW_apply κ ρL ρR r k).comp ((hcm.comp measurable_fst).prodMk measurable_snd))
    exact (hj.stronglyMeasurable.integral_prod_right (ν := (volume : Measure ℂ))).measurable
  have hfm : ∀ k, Measurable (f k) := fun k => (hpair k).sub (hmean k)
  -- the differences, as centred pairings with a random test function
  have hdiff : ∀ n m : ℕ, ∫⁻ ω, ENNReal.ofReal ((f n ω - f m ω) ^ 2) ∂P ≤
      ENNReal.ofReal (4 * (1 / 16 : ℝ) ^ min n m) := by
    intro n m
    set φ : Ω → LQGMetric.TestOn upperHalfPlaneOpens := fun ω =>
      srcTestW κ ρL ρR r (c ω) n - srcTestW κ ρL ρR r (c ω) m with hφ
    have hφm : ∀ z, Measurable[𝒢] fun ω => φ ω z := fun z => by
      have h1 : Measurable fun x : (Fin nL → ℝ) × (Fin nR → ℝ) =>
          srcTestW κ ρL ρR r x n z - srcTestW κ ρL ρR r x m z := by
        have a1 := (measurable_srcTestW_apply κ ρL ρR r n).comp
          ((measurable_id (α := (Fin nL → ℝ) × (Fin nR → ℝ))).prodMk (measurable_const (a := z)))
        have a2 := (measurable_srcTestW_apply κ ρL ρR r m).comp
          ((measurable_id (α := (Fin nL → ℝ) × (Fin nR → ℝ))).prodMk (measurable_const (a := z)))
        exact a1.sub a2
      exact h1.comp hc
    have e : ∀ ω, f n ω - f m ω = h ω (φ ω) - ∫ z, u ω z * φ ω z := fun ω => by
      have hi : ∫ z, u ω z * φ ω z = (∫ z, u ω z * srcTestW κ ρL ρR r (c ω) n z) -
          ∫ z, u ω z * srcTestW κ ρL ρR r (c ω) m z := by
        rw [← integral_sub (integrable_mul_testOn (hu ω) _) (integrable_mul_testOn (hu ω) _)]
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        change u ω z * (srcTestW κ ρL ρR r (c ω) n z - srcTestW κ ρL ρR r (c ω) m z) = _
        ring
      rw [hi]
      simp only [hf, hφ, map_sub]
      ring
    have hY : Measurable fun ω => h ω (φ ω) - ∫ z, u ω z * φ ω z := by
      have h1 := (hfm n).sub (hfm m)
      have e' : (f n - f m) = fun ω => h ω (φ ω) - ∫ z, u ω z * φ ω z := funext e
      rw [e'] at h1
      exact h1
    have hV : Measurable fun ω => greenEnergy (φ ω) (φ ω) := by
      have h1 : (fun ω => greenEnergy (φ ω) (φ ω)) = fun ω =>
          pairEnergyW κ ρL ρR r (c ω) (pairSeqW κ ρL ρR r (c ω) n) (pairSeqW κ ρL ρR r (c ω) m) :=
        funext fun ω => greenEnergy_srcTestW_sub κ ρL ρR r (c ω) n m
      rw [h1]
      exact (measurable_pairEnergyW_seq κ ρL ρR r n m).comp hcm
    have hVle : ∀ ω, greenEnergy (φ ω) (φ ω) ≤ (1 / 16 : ℝ) ^ min n m := fun ω => by
      have h1 := greenEnergy_srcTestW_sub κ ρL ρR r (c ω) n m
      refine le_of_eq_of_le h1 ?_
      exact (pairEnergyW_lt κ ρL ρR r (hadm ω)
        ((strictMono_pairSeqW κ ρL ρR r (c ω)).monotone (min_le_left n m))
        ((strictMono_pairSeqW κ ρL ρR r (c ω)).monotone (min_le_right n m))).le
    have hV0 : ∀ ω, 0 ≤ greenEnergy (φ ω) (φ ω) := fun ω => by
      have h1 := zeroGFFTestCov_H_eq_greenEnergy (φ ω)
      have h2 : (0 : ℝ) ≤ QuantumZipper.zeroGFFTestCov H (φ ω) (φ ω) :=
        LocalSets.zeroGFFTestCov_self_nonneg QuantumZipper.isOpen_H subset_rfl (φ ω)
      exact h1 ▸ h2
    simp_rw [e]
    exact lintegral_sq_le_of_condCharFun h𝒢 hY hV (ae_of_all _ hV0) (hcf φ hφm) (by positivity)
      (ae_of_all _ fun ω => hVle ω)
  -- `L²`-Cauchy along the fast subsequence, hence almost surely convergent
  have hB : ∑' i : ℕ, ENNReal.ofReal (3 * (1 / 4 : ℝ) ^ i) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 3)]
    exact ENNReal.ofReal_ne_top
  have hcau : ∀ N n m : ℕ, N ≤ n → N ≤ m →
      eLpNorm (f n - f m) 2 P < ENNReal.ofReal (3 * (1 / 4 : ℝ) ^ N) := by
    intro N n m hn hm
    have h1 := eLpNorm_two_le_of_lintegral_sq (g := f n - f m) (by positivity) (hdiff n m)
    have h2 : Real.sqrt (4 * (1 / 16 : ℝ) ^ min n m) = 2 * (1 / 4 : ℝ) ^ min n m := by
      rw [show (4 : ℝ) * (1 / 16 : ℝ) ^ min n m = (2 * (1 / 4 : ℝ) ^ min n m) ^ 2 by
        rw [mul_pow, ← pow_mul, mul_comm (min n m) 2, pow_mul]; norm_num,
        Real.sqrt_sq (by positivity)]
    have h3 : (1 / 4 : ℝ) ^ min n m ≤ (1 / 4 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_min hn hm)
    refine h1.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_)
    rw [h2]
    have h4 : (0 : ℝ) < (1 / 4 : ℝ) ^ N := by positivity
    linarith
  have hae := Lp.ae_tendsto_of_cauchy_eLpNorm (f := f) (p := 2)
    (fun n => (hfm n).aestronglyMeasurable) one_le_two hB hcau
  filter_upwards [hae] with ω ⟨l, hl⟩
  have hconv : Tendsto (fun k => h ω (srcTestW κ ρL ρR r (c ω) k)) atTop
      (𝓝 (l + ∫ z, u ω z * vSrc κ (c ω).1 (c ω).2 ρL ρR r z)) :=
    (hl.add (tendsto_integral_mul_srcTestW (hadm ω) (hu ω) (hC ω))).congr fun k => by simp only [hf]; ring
  rw [srcPairW, hconv.limUnder_eq]
  exact hconv

end RandomConv

end LocalExt

end InteractingSLE
