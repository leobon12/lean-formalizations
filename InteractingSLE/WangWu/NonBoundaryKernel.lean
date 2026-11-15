/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.NonBoundaryReconstruct
import InteractingSLE.WangWu.NonBoundaryGreen

/-!
# The full conditional Gaussian kernel from the kernel off a thin set (Wang–Wu Corollary 4.23)

Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), §4.5, Corollary 4.23 and its proof (text
dump lines 1779–1815): "Given the local-set information, the complementary field restrictions are independent Gaussian
fields with the identified component means and Green covariances. Write `v_A` for the bounded function formed by these
means … The linear reconstruction in Lemma 4.14 also identifies the full Gaussian kernel. Indeed use the approximations
`p_δ` there and omit the squares meeting `A`. Their conditional means tend to `∫ v_A p`, by the uniform bound and
vanishing area of the omitted squares. Their conditional covariances tend to `Q_{D∖A}(p, p)` by dominated convergence,
using `G_{D∖A} ≤ G_D` and the locally integrable logarithmic singularity. The reconstructed pairings converge almost
surely to `(h, p)`. Conditional bounded convergence of their characteristic functions therefore gives
`E[e^{i(h,p)} | A] = exp(i ∫ v_A p − ½ Q_{D∖A}(p, p))`."

This is also step (WF12)–(WF13) of the whole-field identification in `source/external/AstraIG1/ig1_followup_proofs.pdf`
§C.5 (ruling R38).

## Setting

`F = h + m` on `ℍ` (`h` a zero-boundary GFF, `m` bounded), `𝒢` a sub-σ-algebra (the local-set information) for which
every avoidance event `{tsupport ψ ∩ A = ∅}` is measurable, `v : Ω → ℂ → ℝ` a bounded mean, and `G : Ω → ℂ → ℂ → ℝ` a
kernel with `0 ≤ G ≤ G_ℍ` off the diagonal. The hypothesis is the conditional Gaussian kernel **off `A`**: for every
test function `ψ`, on `{tsupport ψ ∩ A = ∅}`, `E[e^{i F ψ} | 𝒢] = exp(i ∫ v ψ − ½ Q_G(ψ))`. The conclusion is the
same identity for **every** test function, under the covering hypothesis (R1.1) for `A`.

## Main results

* `goodSet`, `goodTest`: the pieces avoiding `A` and their sum `f_n`; `offSum_eq_goodTest`;
* `condExp_exp_offSum`: the conditional characteristic function of the reconstruction sum (finitely many cases);
* **`ae_condExp_exp_eq_gaussCF`** (Corollary 4.23, kernel identity).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal Real

namespace InteractingSLE.WangWu

open QuantumZipper (greenH H)

/-- The Gaussian characteristic-function value `exp(i μ − ½ q)`, in the form used by `IsFullLevelLineCoupling`. -/
def gaussCF (μ q : ℝ) : ℂ := Complex.exp (Complex.I * (μ : ℂ) - (((1 / 2 : ℝ) * q : ℝ) : ℂ))

lemma continuous_gaussCF : Continuous fun p : ℝ × ℝ => gaussCF p.1 p.2 := by
  unfold gaussCF
  fun_prop

/-! ### The pieces avoiding `A` -/

open Classical in
/-- The indices of the pieces `φ ψ_{n,k}`, `k ∈ [−M_n, M_n]²`, whose supports avoid `A`. -/
def goodSet (A : Set ℂ) (φ : LQGMetric.TestOn upperHalfPlaneOpens) (R : ℝ) (n : ℕ) :
    Finset (ℤ × ℤ) :=
  (pouIdx (scaleIdx R n)).filter fun k => Disjoint (tsupport (pouTest φ n k)) A

/-- The sum of the pieces with indices in `S`. -/
def goodTest (φ : LQGMetric.TestOn upperHalfPlaneOpens) (n : ℕ) (S : Finset (ℤ × ℤ)) :
    LQGMetric.TestOn upperHalfPlaneOpens :=
  ∑ k ∈ S, pouTest φ n k

lemma goodTest_apply (φ : LQGMetric.TestOn upperHalfPlaneOpens) (n : ℕ) (S : Finset (ℤ × ℤ))
    (z : ℂ) : goodTest φ n S z = ∑ k ∈ S, φ z * pouSq n k z := by
  rw [goodTest, testOn_sum_apply]
  rfl

open Classical in
lemma offSum_eq_goodTest {Ω : Type*} (A : Ω → Set ℂ) (F : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) (R : ℝ) (n : ℕ) (ω : Ω) :
    offSum A F φ R n ω = F ω (goodTest φ n (goodSet (A ω) φ R n)) := by
  rw [offSum, goodTest, map_sum, goodSet, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : Disjoint (tsupport (pouTest φ n k)) (A ω)
  · rw [offEval_of_disjoint hk]; simp [hk]
  · rw [offEval_of_not_disjoint hk]; simp [hk]

lemma tsupport_goodTest_subset (φ : LQGMetric.TestOn upperHalfPlaneOpens) (n : ℕ)
    (S : Finset (ℤ × ℤ)) : tsupport (goodTest φ n S) ⊆ ⋃ k ∈ S, tsupport (pouTest φ n k) := by
  have hsupp : Function.support (goodTest φ n S) ⊆ ⋃ k ∈ S, Function.support (pouTest φ n k) := by
    intro z hz
    rw [Function.mem_support, goodTest, testOn_sum_apply] at hz
    obtain ⟨k, hk, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
    exact mem_biUnion hk hne
  refine (closure_mono hsupp).trans ?_
  rw [Finset.closure_biUnion]
  exact subset_rfl

lemma disjoint_goodTest_goodSet (A : Set ℂ) (φ : LQGMetric.TestOn upperHalfPlaneOpens) (R : ℝ)
    (n : ℕ) : Disjoint (tsupport (goodTest φ n (goodSet A φ R n))) A := by
  classical
  refine Set.disjoint_of_subset_left (tsupport_goodTest_subset φ n _) ?_
  rw [Set.disjoint_iUnion₂_left]
  intro k hk
  exact (Finset.mem_filter.1 hk).2

/-- Partial sums of the square cut-offs are at most `1` where the full sum is `1`. -/
lemma abs_goodTest_le {φ : LQGMetric.TestOn upperHalfPlaneOpens} {R B : ℝ}
    (hRsub : tsupport φ ⊆ closedBall 0 R) (hB : ∀ z, |φ z| ≤ B) (n : ℕ) {S : Finset (ℤ × ℤ)}
    (hS : S ⊆ pouIdx (scaleIdx R n)) (z : ℂ) : |goodTest φ n S z| ≤ B := by
  rw [goodTest_apply, ← Finset.mul_sum]
  by_cases hz : z ∈ tsupport φ
  · have hzR : ‖z‖ ≤ R := by simpa using hRsub hz
    have h2 : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
    have hM := le_scaleIdx R n
    have hre : |z.re * 2 ^ n| ≤ scaleIdx R n := by
      rw [abs_mul, abs_of_pos h2]
      exact (mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm z).trans hzR) h2.le).trans hM
    have him : |z.im * 2 ^ n| ≤ scaleIdx R n := by
      rw [abs_mul, abs_of_pos h2]
      exact (mul_le_mul_of_nonneg_right ((Complex.abs_im_le_norm z).trans hzR) h2.le).trans hM
    have hsum := sum_pouSq hre him
    have h0 : 0 ≤ ∑ k ∈ S, pouSq n k z := Finset.sum_nonneg fun k _ => pouSq_nonneg n k z
    have h1 : ∑ k ∈ S, pouSq n k z ≤ 1 := by
      rw [← hsum]
      exact Finset.sum_le_sum_of_subset_of_nonneg hS fun k _ _ => pouSq_nonneg n k z
    rw [abs_mul, abs_of_nonneg h0]
    calc |φ z| * ∑ k ∈ S, pouSq n k z ≤ B * 1 :=
          mul_le_mul (hB z) h1 h0 ((abs_nonneg _).trans (hB z))
      _ = B := mul_one B
  · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, abs_zero]
    exact (abs_nonneg _).trans (hB z)

lemma goodTest_eq_zero_of_notMem {φ : LQGMetric.TestOn upperHalfPlaneOpens} (n : ℕ)
    (S : Finset (ℤ × ℤ)) {z : ℂ} (hz : z ∉ tsupport φ) : goodTest φ n S z = 0 := by
  rw [goodTest_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]

/-- The union of the balls `B(k 2^{-n}, 2 · 2^{-n})` of the omitted pieces. -/
def badBalls (n : ℕ) (T : Finset (ℤ × ℤ)) : Set ℂ := ⋃ k ∈ T, ball (pouCentre n k) (2 / 2 ^ n)

lemma measurableSet_badBalls (n : ℕ) (T : Finset (ℤ × ℤ)) : MeasurableSet (badBalls n T) :=
  Finset.measurableSet_biUnion _ fun _ _ => measurableSet_ball

lemma volume_badBalls_le (n : ℕ) (T : Finset (ℤ × ℤ)) :
    volume (badBalls n T) ≤ T.card * ENNReal.ofReal (4 * π / 4 ^ n) := by
  refine (measure_biUnion_finset_le _ _).trans (le_of_eq ?_)
  have h4 : (4 : ℝ) ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  simp only [Complex.volume_ball, Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_mul (by positivity), h4]
  congr 1
  field_simp
  ring

/-- Off the balls of the omitted pieces, `f_n = φ`. -/
lemma goodTest_eq_of_notMem_badBalls {φ : LQGMetric.TestOn upperHalfPlaneOpens} {R : ℝ}
    (hRsub : tsupport φ ⊆ closedBall 0 R) (n : ℕ) {S : Finset (ℤ × ℤ)}
    (hS : S ⊆ pouIdx (scaleIdx R n)) {z : ℂ} (hz : z ∉ badBalls n (pouIdx (scaleIdx R n) \ S)) :
    φ z = goodTest φ n S z := by
  have hdec := congrArg (fun ψ : LQGMetric.TestOn upperHalfPlaneOpens => ψ z)
    (sum_pouTest hRsub (le_scaleIdx R n))
  simp only [testOn_sum_apply] at hdec
  rw [← hdec, goodTest_apply, ← Finset.sum_sdiff hS]
  simp only [pouTest_apply]
  rw [add_eq_right]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hzb : z ∉ ball (pouCentre n k) (2 / 2 ^ n) := fun h => hz (mem_biUnion hk h)
  rw [pouSq_eq_zero_of_notMem_ball hzb, mul_zero]

/-! ### The conditional characteristic function of a reconstruction sum -/

section Kernel

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ}

omit mΩ in
open Classical in
/-- The event that exactly the pieces with indices in `S ⊆ [−M_n, M_n]²` avoid `A` is an intersection of avoidance
events and their complements. -/
lemma setOf_goodSet_eq (φ : LQGMetric.TestOn upperHalfPlaneOpens) (R : ℝ) (n : ℕ)
    {S : Finset (ℤ × ℤ)} (hS : S ⊆ pouIdx (scaleIdx R n)) :
    {ω | goodSet (A ω) φ R n = S} = ⋂ k ∈ pouIdx (scaleIdx R n),
      {ω | Disjoint (tsupport (pouTest φ n k)) (A ω) ↔ k ∈ S} := by
  ext ω
  simp only [Set.mem_ofPred_eq, mem_iInter, Finset.ext_iff, goodSet, Finset.mem_filter]
  constructor
  · intro h k hk
    rw [← h k]
    exact ⟨fun hd => ⟨hk, hd⟩, fun h' => h'.2⟩
  · intro h k
    by_cases hk : k ∈ pouIdx (scaleIdx R n)
    · rw [← h k hk]
      exact ⟨fun h' => h'.2, fun hd => ⟨hk, hd⟩⟩
    · exact ⟨fun h' => absurd h'.1 hk, fun h' => absurd (hS h') hk⟩

omit mΩ in
lemma measurableSet_setOf_goodSet
    (hA𝒢 : ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens,
      MeasurableSet[𝒢] {ω | Disjoint (tsupport ψ) (A ω)})
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) (R : ℝ) (n : ℕ) {S : Finset (ℤ × ℤ)}
    (hS : S ⊆ pouIdx (scaleIdx R n)) : MeasurableSet[𝒢] {ω | goodSet (A ω) φ R n = S} := by
  rw [setOf_goodSet_eq φ R n hS]
  refine Finset.measurableSet_biInter _ fun k _ => ?_
  by_cases hk : k ∈ S
  · simpa only [hk, iff_true] using hA𝒢 (pouTest φ n k)
  · simp only [hk, iff_false]
    exact (hA𝒢 (pouTest φ n k)).compl

lemma integrable_exp_pairing (hFm : ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens,
      Measurable fun ω => F ω ψ) (ψ : LQGMetric.TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => Complex.exp (Complex.I * (F ω ψ : ℂ))) P := by
  refine Integrable.of_bound (C := 1) ?_ (Eventually.of_forall fun ω => ?_)
  · exact (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (hFm ψ)))).aestronglyMeasurable
  · rw [Complex.norm_exp_I_mul_ofReal]

open Classical in
/-- **The conditional characteristic function of a reconstruction sum.** If the conditional Gaussian kernel holds off
`A` (hypothesis `hker`), then `E[e^{i Y_n} | 𝒢] = exp(i ∫ v f_n − ½ Q_G(f_n))` a.s., where `Y_n = offSum` and
`f_n = goodTest` is the (random) sum of the pieces avoiding `A`: on each of the finitely many events
`{goodSet = S}` (all in `𝒢`) the sum is a fixed test function avoiding `A`. -/
theorem ae_condExp_exp_offSum (h𝒢 : 𝒢 ≤ mΩ) (hA𝒢 : ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens,
      MeasurableSet[𝒢] {ω | Disjoint (tsupport ψ) (A ω)})
    (hFm : ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, Measurable fun ω => F ω ψ)
    {v : Ω → ℂ → ℝ} {G : Ω → ℂ → ℂ → ℝ}
    (hker : ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (A ω) →
      P[fun ω' => Complex.exp (Complex.I * (F ω' ψ : ℂ)) | 𝒢] ω =
        gaussCF (∫ z, v ω z * ψ z) (greenForm (G ω) ψ))
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) (R : ℝ) (n : ℕ) :
    ∀ᵐ ω ∂P, P[fun ω' => Complex.exp (Complex.I * (offSum A F φ R n ω' : ℂ)) | 𝒢] ω =
      gaussCF (∫ z, v ω z * goodTest φ n (goodSet (A ω) φ R n) z)
        (greenForm (G ω) (goodTest φ n (goodSet (A ω) φ R n))) := by
  set I := pouIdx (scaleIdx R n) with hI
  set X : Finset (ℤ × ℤ) → Ω → ℂ := fun S ω => Complex.exp (Complex.I * (F ω (goodTest φ n S) : ℂ))
    with hX
  set E : Finset (ℤ × ℤ) → Set Ω := fun S => {ω | goodSet (A ω) φ R n = S} with hE
  have hgood : ∀ ω, goodSet (A ω) φ R n ∈ I.powerset := fun ω =>
    Finset.mem_powerset.2 (Finset.filter_subset _ _)
  have hpt : (fun ω => Complex.exp (Complex.I * (offSum A F φ R n ω : ℂ))) =
      ∑ S ∈ I.powerset, (E S).indicator (X S) := by
    funext ω
    rw [Finset.sum_apply, Finset.sum_eq_single (goodSet (A ω) φ R n)]
    · rw [indicator_of_mem (show ω ∈ E (goodSet (A ω) φ R n) from rfl), offSum_eq_goodTest]
    · intro S _ hS
      exact indicator_of_notMem (fun h => hS h.symm) _
    · exact fun h => absurd (hgood ω) h
  have hEm : ∀ S ∈ I.powerset, MeasurableSet[𝒢] (E S) := fun S hS =>
    measurableSet_setOf_goodSet hA𝒢 φ R n (Finset.mem_powerset.1 hS)
  have hint : ∀ S ∈ I.powerset, Integrable ((E S).indicator (X S)) P := fun S hS =>
    (integrable_exp_pairing hFm _).indicator (h𝒢 _ (hEm S hS))
  have hsum := condExp_finsetSum (μ := P) hint 𝒢
  have hind : ∀ᵐ ω ∂P, ∀ S ∈ I.powerset,
      P[(E S).indicator (X S) | 𝒢] ω = (E S).indicator (P[X S | 𝒢]) ω :=
    (eventually_all_finset _).2 fun S hS =>
      condExp_indicator (integrable_exp_pairing hFm _) (hEm S hS)
  have hkerS : ∀ᵐ ω ∂P, ∀ S ∈ I.powerset, Disjoint (tsupport (goodTest φ n S)) (A ω) →
      P[X S | 𝒢] ω = gaussCF (∫ z, v ω z * goodTest φ n S z) (greenForm (G ω) (goodTest φ n S)) :=
    (eventually_all_finset _).2 fun S _ => hker (goodTest φ n S)
  rw [hpt]
  filter_upwards [hsum, hind, hkerS] with ω h1 h2 h3
  rw [h1, Finset.sum_apply, Finset.sum_eq_single (goodSet (A ω) φ R n)]
  · rw [h2 _ (hgood ω), indicator_of_mem (show ω ∈ E (goodSet (A ω) φ R n) from rfl)]
    exact h3 _ (hgood ω) (disjoint_goodTest_goodSet _ φ R n)
  · intro S hS hne
    rw [h2 S hS, indicator_of_notMem (fun h => hne h.symm)]
  · exact fun h => absurd (hgood ω) h

/-! ### The kernel identity -/

/-- A pointwise `limUnder` of complex functions is strongly measurable for any σ-algebra making them strongly
measurable. -/
lemma stronglyMeasurable_limUnder_complex {X : Type*} [m : MeasurableSpace X] {f : ℕ → X → ℂ}
    (hf : ∀ i, StronglyMeasurable (f i)) : StronglyMeasurable fun x => limUnder atTop (f · x) :=
  StronglyMeasurable.limUnder hf

open Classical in
omit mΩ [IsProbabilityMeasure P] in
lemma offEval_eq_indicator (ψ : LQGMetric.TestOn upperHalfPlaneOpens) :
    offEval A F ψ = {ω | Disjoint (tsupport ψ) (A ω)}.indicator fun ω => F ω ψ := by
  funext ω
  by_cases hω : Disjoint (tsupport ψ) (A ω)
  · rw [offEval_of_disjoint hω, indicator_of_mem (show ω ∈ {ω | Disjoint (tsupport ψ) (A ω)} from hω)]
  · rw [offEval_of_not_disjoint hω, indicator_of_notMem (show ω ∉ {ω | Disjoint (tsupport ψ) (A ω)}
      from hω)]

omit [IsProbabilityMeasure P] in
lemma measurable_offSum_ambient (h𝒢 : 𝒢 ≤ mΩ) (hA𝒢 : ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens,
      MeasurableSet[𝒢] {ω | Disjoint (tsupport ψ) (A ω)})
    (hFm : ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, Measurable fun ω => F ω ψ)
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) (R : ℝ) (n : ℕ) :
    Measurable (offSum A F φ R n) := by
  unfold offSum
  refine Finset.measurable_sum _ fun k _ => ?_
  rw [offEval_eq_indicator]
  exact (hFm _).indicator (h𝒢 _ (hA𝒢 _))

open Classical in
/-- **Wang–Wu Corollary 4.23 (the full conditional Gaussian kernel).** Let `h` be a zero-boundary GFF on `ℍ`,
`F = h + m` with `m` bounded on `ℍ`, `𝒢 ≤ mΩ` a σ-algebra containing every avoidance event
`{tsupport ψ ∩ A = ∅}`, `v` a bounded measurable mean and `G` a measurable kernel with `0 ≤ G ≤ G_ℍ` off the
diagonal of `ℍ × ℍ`. Suppose the conditional Gaussian kernel holds off `A`: for every test function `ψ`, a.s. on
`{tsupport ψ ∩ A = ∅}`, `E[e^{i F ψ} | 𝒢] = exp(i ∫ v ψ − ½ Q_G(ψ))`. If `A` has the covering property (R1.1) on
`tsupport φ`, then almost surely `E[e^{i F φ} | 𝒢] = exp(i ∫ v φ − ½ Q_G(φ))`. -/
theorem ae_condExp_exp_eq_gaussCF (h𝒢 : 𝒢 ≤ mΩ) {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {m : ℂ → ℝ} {Mm : ℝ} (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hm : ∀ z ∈ H, |m z| ≤ Mm) (hF : ∀ ω ψ, F ω ψ = h ω ψ + ∫ z, m z * ψ z)
    (hA𝒢 : ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens,
      MeasurableSet[𝒢] {ω | Disjoint (tsupport ψ) (A ω)})
    {v : Ω → ℂ → ℝ} {Mv : ℝ} (hvm : ∀ ω, Measurable (v ω)) (hv : ∀ ω z, |v ω z| ≤ Mv)
    {G : Ω → ℂ → ℂ → ℝ} (hGm : ∀ ω, Measurable (Function.uncurry (G ω)))
    (hG : ∀ ω a b, a ∈ H → b ∈ H → a ≠ b → 0 ≤ G ω a b ∧ G ω a b ≤ greenH a b)
    (hker : ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (A ω) →
      P[fun ω' => Complex.exp (Complex.I * (F ω' ψ : ℂ)) | 𝒢] ω =
        gaussCF (∫ z, v ω z * ψ z) (greenForm (G ω) ψ))
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    (hcov : ∀ᵐ ω ∂P, Tendsto (fun j => (Dimension.dyadicCount (ns j) (A ω ∩ tsupport φ) : ℝ) *
      (ns j + 1) / 4 ^ ns j) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, P[fun ω' => Complex.exp (Complex.I * (F ω' φ : ℂ)) | 𝒢] ω =
      gaussCF (∫ z, v ω z * φ z) (greenForm (G ω) φ) := by
  have hFm : ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, Measurable fun ω => F ω ψ := fun ψ => by
    simp_rw [hF]; exact (hh.process.measurable ψ).add_const _
  -- support radius and sup bound
  obtain ⟨R₀, hR₀⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  set R := max R₀ 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hRsub : tsupport φ ⊆ closedBall 0 R :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨B, hB'⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hB : ∀ z, |φ z| ≤ B := fun z => by simpa [Real.norm_eq_abs] using hB' z
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hφH : ∀ z, z ∉ H ∩ closedBall 0 R → φ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun ht => hz ⟨φ.tsupport_subset ht, hRsub ht⟩
  -- the reconstruction sums and the (random) good test functions
  set fj : ℕ → Ω → LQGMetric.TestOn upperHalfPlaneOpens :=
    fun j ω => goodTest φ (ns j) (goodSet (A ω) φ R (ns j)) with hfj
  set fs : ℕ → Ω → ℂ := fun j ω => Complex.exp (Complex.I * (offSum A F φ R (ns j) ω : ℂ)) with hfs
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (F ω φ : ℂ)) with hf
  set gs : ℕ → Ω → ℂ := fun j => P[fs j | 𝒢] with hgs
  set g : Ω → ℂ := fun ω => gaussCF (∫ z, v ω z * φ z) (greenForm (G ω) φ) with hg
  -- (K1) the conditional characteristic functions of the reconstruction sums
  have hK1 : ∀ᵐ ω ∂P, ∀ j, gs j ω =
      gaussCF (∫ z, v ω z * fj j ω z) (greenForm (G ω) (fj j ω)) :=
    ae_all_iff.2 fun j => ae_condExp_exp_offSum h𝒢 hA𝒢 hFm hker φ R (ns j)
  -- (K3) their means and covariances converge
  have hK3 : ∀ᵐ ω ∂P, Tendsto (fun j => gaussCF (∫ z, v ω z * fj j ω z)
      (greenForm (G ω) (fj j ω))) atTop (𝓝 (g ω)) := by
    filter_upwards [hcov] with ω hω
    set U : ℕ → Set ℂ := fun j =>
      badBalls (ns j) (pouIdx (scaleIdx R (ns j)) \ goodSet (A ω) φ R (ns j)) with hU
    have hUm : ∀ j, MeasurableSet (U j) := fun j => measurableSet_badBalls _ _
    have hUle' : ∀ j, volume (U j) ≤ ((pouIdx (scaleIdx R (ns j)) \ goodSet (A ω) φ R (ns j)).card : ℝ≥0∞) *
        ENNReal.ofReal (4 * π / 4 ^ ns j) := fun j => volume_badBalls_le _ _
    have hUf : ∀ j, volume (U j) ≠ ⊤ := fun j =>
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top) (hUle' j)
    have hUle : ∀ j, (volume (U j)).toReal ≤ 36 * π *
        ((Dimension.dyadicCount (ns j) (A ω ∩ tsupport φ) : ℝ) * (ns j + 1) / 4 ^ ns j) := by
      intro j
      have hcard : ((pouIdx (scaleIdx R (ns j)) \ goodSet (A ω) φ R (ns j)).card : ℝ) ≤
          9 * Dimension.dyadicCount (ns j) (A ω ∩ tsupport φ) := by
        have h1 := card_bad_le φ (A ω) (ns j) (scaleIdx R (ns j))
        rw [Finset.filter_not] at h1
        exact_mod_cast h1
      have h4 : (0 : ℝ) < 4 ^ ns j := by positivity
      refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
        (hUle' j)).trans ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)]
      have hn1 : (1 : ℝ) ≤ ns j + 1 := by linarith [(Nat.cast_nonneg (ns j) : (0 : ℝ) ≤ ns j)]
      have hN0 : (0 : ℝ) ≤ Dimension.dyadicCount (ns j) (A ω ∩ tsupport φ) := Nat.cast_nonneg _
      calc ((pouIdx (scaleIdx R (ns j)) \ goodSet (A ω) φ R (ns j)).card : ℝ) * (4 * π / 4 ^ ns j)
          ≤ 9 * Dimension.dyadicCount (ns j) (A ω ∩ tsupport φ) * (4 * π / 4 ^ ns j) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 36 * π * ((Dimension.dyadicCount (ns j) (A ω ∩ tsupport φ) : ℝ) * 1 / 4 ^ ns j) := by ring
        _ ≤ 36 * π * ((Dimension.dyadicCount (ns j) (A ω ∩ tsupport φ) : ℝ) * (ns j + 1) / 4 ^ ns j) := by
            gcongr
    have hU0 : Tendsto (fun j => (volume (U j)).toReal) atTop (𝓝 0) :=
      squeeze_zero (fun j => ENNReal.toReal_nonneg) hUle (by simpa using hω.const_mul (36 * π))
    have hfjb : ∀ j z, |fj j ω z| ≤ B := fun j z =>
      abs_goodTest_le hRsub hB _ (Finset.filter_subset _ _) z
    have hfjH : ∀ j z, z ∉ H ∩ closedBall 0 R → fj j ω z = 0 := fun j z hz =>
      goodTest_eq_zero_of_notMem _ _ fun ht => hz ⟨φ.tsupport_subset ht, hRsub ht⟩
    have hfjU : ∀ j z, z ∉ U j → φ z = fj j ω z := fun j z hz =>
      goodTest_eq_of_notMem_badBalls hRsub _ (Finset.filter_subset _ _) hz
    -- covariances
    have hq : Tendsto (fun j => greenForm (G ω) (fj j ω)) atTop (𝓝 (greenForm (G ω) φ)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_)
        (by simpa using hU0.const_mul (256 * π * R ^ 2 * B ^ 2))
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact abs_greenForm_sub_le (hGm ω) (hG ω) hR φ.continuous.measurable
        (fj j ω).continuous.measurable hB (hfjb j) hφH (hfjH j) (hUm j) (hUf j) (hfjU j)
    -- means
    have hvφ : Integrable (fun z => v ω z * φ z) :=
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).bdd_mul
        (hvm ω).aestronglyMeasurable (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]; exact (hv ω z).trans (le_abs_self Mv))
    have hvf : ∀ j, Integrable (fun z => v ω z * fj j ω z) := fun j =>
      ((fj j ω).continuous.integrable_of_hasCompactSupport (fj j ω).hasCompactSupport).bdd_mul
        (hvm ω).aestronglyMeasurable (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]; exact (hv ω z).trans (le_abs_self Mv))
    have hμ : Tendsto (fun j => ∫ z, v ω z * fj j ω z) atTop (𝓝 (∫ z, v ω z * φ z)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_)
        (by simpa using hU0.const_mul (2 * |Mv| * B))
      rw [← integral_sub (hvf j) hvφ]
      have hgi : Integrable ((U j).indicator fun _ => 2 * |Mv| * B) :=
        (integrableOn_const (s := U j) (μ := volume) (C := 2 * |Mv| * B) (hUf j)).integrable_indicator
          (hUm j)
      refine (norm_integral_le_of_norm_le hgi (Eventually.of_forall fun z => ?_)).trans (le_of_eq ?_)
      · by_cases hz : z ∈ U j
        · rw [indicator_of_mem hz, Real.norm_eq_abs, ← mul_sub, abs_mul]
          have h1 : |v ω z| ≤ |Mv| := (hv ω z).trans (le_abs_self Mv)
          have h2 : |fj j ω z - φ z| ≤ 2 * B := (abs_sub _ _).trans (by linarith [hfjb j z, hB z])
          calc |v ω z| * |fj j ω z - φ z| ≤ |Mv| * (2 * B) :=
                mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)
            _ = 2 * |Mv| * B := by ring
        · rw [indicator_of_notMem hz, ← hfjU j z hz, sub_self, norm_zero]
      · rw [integral_indicator_const _ (hUm j), smul_eq_mul, measureReal_def]
        ring
    exact (continuous_gaussCF.tendsto _).comp (hμ.prodMk_nhds hq)
  -- (K2) conditional dominated convergence
  have hfs_int : ∀ j, Integrable (fs j) P := fun j => by
    refine Integrable.of_bound (C := 1) ?_ (Eventually.of_forall fun ω => ?_)
    · exact (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
        (measurable_offSum_ambient h𝒢 hA𝒢 hFm φ R (ns j))))).aestronglyMeasurable
    · simp only [hfs]; rw [Complex.norm_exp_I_mul_ofReal]
  have hfs_lim : ∀ᵐ ω ∂P, Tendsto (fun j => fs j ω) atTop (𝓝 (f ω)) := by
    filter_upwards [ae_tendsto_offSum hh hm hF φ hR.le hRsub hns hcov] with ω hω
    exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).tendsto
      _).comp hω
  have hgs_lim : ∀ᵐ ω ∂P, Tendsto (fun j => gs j ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hK1, hK3] with ω h1 h3
    simpa only [h1] using h3
  have hfs_b : ∀ j, ∀ᵐ ω ∂P, ‖fs j ω‖ ≤ 1 := fun j => Eventually.of_forall fun ω => by
    simp only [hfs]; rw [Complex.norm_exp_I_mul_ofReal]
  have hgs_b : ∀ j, ∀ᵐ ω ∂P, ‖gs j ω‖ ≤ 1 := fun j => ae_bdd_norm_condExp_of_ae_bdd_norm (hfs_b j)
  have hfg : ∀ j, P[fs j | 𝒢] =ᵐ[P] P[gs j | 𝒢] := fun j =>
    (condExp_condExp_of_le le_rfl h𝒢).symm
  have hmain := tendsto_condExp_unique fs gs f g hfs_int (fun j => integrable_condExp) hfs_lim
    hgs_lim (fun _ => (1 : ℝ)) (integrable_const 1) (fun _ => (1 : ℝ)) (integrable_const 1) hfs_b
    hgs_b hfg
  -- the limit `g` is (a.e.) `𝒢`-measurable
  set g' : Ω → ℂ := fun ω => limUnder atTop (fun j => gs j ω) with hg'
  have hg'm : StronglyMeasurable[𝒢] g' :=
    stronglyMeasurable_limUnder_complex (m := 𝒢) fun j => stronglyMeasurable_condExp
  have hgg' : g =ᵐ[P] g' := by
    filter_upwards [hgs_lim] with ω hω
    exact hω.limUnder_eq.symm
  have hg'int : Integrable g' P := by
    refine Integrable.of_bound (C := 1) (hg'm.mono h𝒢).aestronglyMeasurable ?_
    filter_upwards [hgs_lim, ae_all_iff.2 hgs_b] with ω hω hb
    show ‖limUnder atTop (fun j => gs j ω)‖ ≤ 1
    rw [hω.limUnder_eq]
    exact le_of_tendsto hω.norm (Eventually.of_forall hb)
  have hcg : P[g | 𝒢] =ᵐ[P] g := by
    refine (condExp_congr_ae hgg').trans ?_
    rw [condExp_of_stronglyMeasurable h𝒢 hg'm hg'int]
    exact hgg'.symm
  filter_upwards [hmain, hcg] with ω h1 h2
  rw [h1, h2]

end Kernel

end InteractingSLE.WangWu
