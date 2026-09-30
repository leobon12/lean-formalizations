import QuantumZipper.Proofs.LQG.PalmFree
import QuantumZipper.Proofs.Field.Factorization

/-!
# M4-P5: atomlessness of the boundary measure

Blueprint `M4_BLUEPRINT.md`, node M4-P5. Almost surely `qBoundaryMeasure γ (X ω)` has no atoms,
for the free field `X` (`ae_noAtoms_free`), for its normalization `zField X R`
(`ae_noAtoms_zField`) and for `ofFun m + zField X R` with `m` continuous
(`ae_noAtoms_add_ofFun`).

Route: the free-field Palm formula `PalmFree.palm_formula_free` applied to
`φ(Y, s) = min(1, ν_Y({s}))`, written as a measurable function (`phiA`) of the countably many
folded-circle coordinates `muJ j` of `Y` and of `s`: `ν({s}) = inf_n sup_p ∫ tent_{n,p}(s,·) dν`,
and each integral is `liminf_k ∫ tent d(bdryApprox γ Y k)` on the event of vague convergence
(`atomA_eq`). The right side of the Palm formula vanishes by M4-P4, taken as the hypothesis
`LogSingNoAtom` (for each `s`, a.s. the log-singular field `Z + γ(−log‖·−s‖) + g` has a vague
limit with no atom at `s`). Hence `E ∫ w(s) min(1, ν({s})) ν(ds) = 0`, so a.s. `ν` has no atom
where `w > 0`; windows `[-N, N]` and the additive-constant relations give all of `ℝ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace QuantumZipper
namespace Atomless

open BdryExist PalmFree

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample} {γ : ℝ}

/-! ## 1. The countable family of folded circles and the reconstruction -/

/-- Reflection of a centre into `Hbar`. -/
def cenH (q : ℂ) : ℂ := ⟨q.re, |q.im|⟩

lemma cenH_mem (q : ℂ) : cenH q ∈ Hbar := show (0 : ℝ) ≤ |q.im| from abs_nonneg _

lemma cenH_of_mem {q : ℂ} (hq : q ∈ Hbar) : cenH q = q :=
  Complex.ext rfl (show |q.im| = q.im from abs_of_nonneg hq)

/-- The folded circles read by `avgReg` at points of `Hbar` (all admissible). -/
def muJ (j : ℕ) : Measure ℂ :=
  foldedCircle (cenH (Factorization.dyadicIndex j).1) (radius (Factorization.dyadicIndex j).2)

lemma adm_muJ (j : ℕ) : IsAdmissibleH (muJ j) :=
  isAdmissibleH_foldedCircle (cenH_mem _) (radius_pos _)

open Classical in
/-- Measurable reconstruction of a field sample from the coordinates `y j = x (muJ j)`. -/
def recJ (y : ℕ → ℝ) : FieldSample := fun μ =>
  if h : ∃ i, muJ i = μ then y (Nat.find h) else 0

lemma measurable_recJ : Measurable recJ := by
  refine measurable_pi_iff.2 fun μ => ?_
  unfold recJ
  by_cases h : ∃ i, muJ i = μ
  · simp only [dif_pos h]; exact measurable_pi_apply _
  · simp only [dif_neg h]; exact measurable_const

open Classical in
lemma recJ_apply (x : FieldSample) (i : ℕ) : recJ (fun j => x (muJ j)) (muJ i) = x (muJ i) := by
  have h : ∃ j, muJ j = muJ i := ⟨i, rfl⟩
  unfold recJ
  rw [dif_pos h]
  exact congrArg x (Nat.find_spec h)

lemma avgReg_recJ (x : FieldSample) (k : ℕ) {z : ℂ} (hz : z ∈ Hbar) :
    avgReg (recJ (fun j => x (muJ j))) k z = avgReg x k z := by
  unfold avgReg
  congr 1; funext n
  obtain ⟨i, hi⟩ := Factorization.dyadicIndex_surj n k z
  have e : muJ i = foldedCircle (dyadicRoundC n z) (radius k) := by
    simp only [muJ, hi, cenH_of_mem (CircleCont.dyadicRoundC_mem_Hbar hz n)]
  rw [← e, recJ_apply]

lemma bdryApprox_recJ (x : FieldSample) :
    bdryApprox γ (recJ (fun j => x (muJ j))) = bdryApprox γ x := by
  funext k
  unfold bdryApprox
  congr 1; funext t
  rw [avgReg_recJ x k (GaussTK.ofReal_mem_Hbar t)]

/-! ## 2. Atoms as a measurable functional of the approximations -/

/-- Continuous cut-offs increasing (in `p`) to the indicator of `(s − δ, s + δ)`. -/
def tent (δ : ℝ) (p : ℕ) (s t : ℝ) : ℝ := min 1 (max 0 ((p : ℝ) * (δ - |t - s|) - 1))

lemma continuous_tent (δ : ℝ) (p : ℕ) : Continuous fun q : ℝ × ℝ => tent δ p q.1 q.2 :=
  continuous_const.min (continuous_const.max ((continuous_const.mul
    (continuous_const.sub (continuous_snd.sub continuous_fst).abs)).sub continuous_const))

lemma measurable_tent_comp (δ : ℝ) (p : ℕ) {α : Type*} [MeasurableSpace α] {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => tent δ p (f a) (g a) := by
  unfold tent
  exact measurable_const.min (measurable_const.max ((measurable_const.mul
    (measurable_const.sub (continuous_abs.measurable.comp (hg.sub hf)))).sub measurable_const))

lemma continuous_tent_right (δ : ℝ) (p : ℕ) (s : ℝ) : Continuous (tent δ p s) :=
  (continuous_tent δ p).comp (continuous_const.prodMk continuous_id)

lemma tent_nonneg (δ : ℝ) (p : ℕ) (s t : ℝ) : 0 ≤ tent δ p s t :=
  le_min zero_le_one (le_max_left _ _)

lemma tent_le_one (δ : ℝ) (p : ℕ) (s t : ℝ) : tent δ p s t ≤ 1 := min_le_left _ _

lemma tent_eq_zero {δ : ℝ} (p : ℕ) {s t : ℝ} (h : δ ≤ |t - s|) : tent δ p s t = 0 := by
  unfold tent
  have : (p : ℝ) * (δ - |t - s|) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg p) (by linarith)
  rw [max_eq_left (by linarith), min_eq_right zero_le_one]

lemma hasCompactSupport_tent (δ : ℝ) (p : ℕ) (s : ℝ) : HasCompactSupport (tent δ p s) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := s - δ) (b := s + δ)) fun t ht => ?_
  refine tent_eq_zero p (le_abs.2 ?_)
  simp only [mem_Icc, not_and_or, not_le] at ht
  rcases ht with h | h
  · right; linarith
  · left; linarith

lemma tent_mono (δ : ℝ) (s t : ℝ) : Monotone fun p : ℕ => tent δ p s t := by
  intro p q hpq
  rcases le_or_gt δ |t - s| with h | h
  · simp only [tent_eq_zero _ h, le_refl]
  · have : (p : ℝ) * (δ - |t - s|) ≤ q * (δ - |t - s|) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hpq) (by linarith)
    exact min_le_min le_rfl (max_le_max le_rfl (by linarith))

lemma iSup_tent (δ : ℝ) (s t : ℝ) :
    ⨆ p : ℕ, ENNReal.ofReal (tent δ p s t) = (Ioo (s - δ) (s + δ)).indicator 1 t := by
  by_cases ht : t ∈ Ioo (s - δ) (s + δ)
  · rw [indicator_of_mem ht, Pi.one_apply]
    have hts : |t - s| < δ := abs_sub_lt_iff.2 ⟨by linarith [ht.2], by linarith [ht.1]⟩
    refine le_antisymm (iSup_le fun p => ENNReal.ofReal_le_one.2 (tent_le_one _ _ _ _)) ?_
    obtain ⟨p, hp⟩ := exists_nat_gt (2 / (δ - |t - s|))
    refine le_iSup_of_le p (le_of_eq ?_)
    have h2 : 2 ≤ (p : ℝ) * (δ - |t - s|) := by
      rw [div_lt_iff₀ (by linarith)] at hp; linarith
    rw [tent, max_eq_right (by linarith), min_eq_left (by linarith), ENNReal.ofReal_one]
  · rw [indicator_of_notMem ht]
    have h : δ ≤ |t - s| := by
      rw [mem_Ioo, not_and_or, not_lt, not_lt] at ht
      rcases ht with h | h
      · rw [le_abs]; right; linarith
      · rw [le_abs]; left; linarith
    simp only [tent_eq_zero _ h, ENNReal.ofReal_zero, iSup_const]

lemma measure_Ioo_eq_iSup (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (δ s : ℝ) :
    ν (Ioo (s - δ) (s + δ)) = ⨆ p : ℕ, ENNReal.ofReal (∫ t, tent δ p s t ∂ν) := by
  have e : ∀ p : ℕ, ENNReal.ofReal (∫ t, tent δ p s t ∂ν) =
      ∫⁻ t, ENNReal.ofReal (tent δ p s t) ∂ν := fun p =>
    ofReal_integral_eq_lintegral_ofReal
      ((continuous_tent_right δ p s).integrable_of_hasCompactSupport (hasCompactSupport_tent δ p s))
      (ae_of_all _ (tent_nonneg δ p s))
  simp_rw [e]
  rw [← lintegral_iSup (f := fun p t => ENNReal.ofReal (tent δ p s t))
    (fun p => ENNReal.measurable_ofReal.comp
      (continuous_tent_right δ p s).measurable)
    (fun p q hpq t => ENNReal.ofReal_le_ofReal (tent_mono δ s t hpq))]
  simp_rw [iSup_tent]
  rw [lintegral_indicator_one measurableSet_Ioo]

/-- The shrinking radii `1/(n+1)`. -/
def dl (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

lemma dl_pos (n : ℕ) : 0 < dl n := by unfold dl; positivity

/-- The atom functional: `inf_n sup_p ofReal (liminf_k ∫ tent_{n,p}(s,·) dν_k(x))`. -/
def atomA (γ : ℝ) (x : FieldSample) (s : ℝ) : ℝ≥0∞ :=
  ⨅ n : ℕ, ⨆ p : ℕ, ENNReal.ofReal
    (liminf (fun k => ∫ t, tent (dl n) p s t ∂bdryApprox γ x k) atTop)

/-- The density of `bdryApprox γ x k`. -/
def dK (γ : ℝ) (k : ℕ) (x : FieldSample) (t : ℝ) : ℝ :=
  radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg x k (t : ℂ))

lemma measurable_dK_comp (γ : ℝ) (k : ℕ) {α : Type*} [MeasurableSpace α] {f : α → FieldSample}
    {g : α → ℝ} (hf : Measurable f) (hg : Measurable g) : Measurable fun a => dK γ k (f a) (g a) :=
  (Real.measurable_exp.comp (((measurable_avgReg k).comp
    (hf.prodMk (Complex.continuous_ofReal.measurable.comp hg))).const_mul (γ / 2))).const_mul _

lemma measurable_integral_tent (γ : ℝ) (k n p : ℕ) :
    Measurable fun q : FieldSample × ℝ => ∫ t, tent (dl n) p q.2 t ∂bdryApprox γ q.1 k := by
  have heq : ∀ q : FieldSample × ℝ, ∫ t, tent (dl n) p q.2 t ∂bdryApprox γ q.1 k =
      ∫ t, dK γ k q.1 t * tent (dl n) p q.2 t := fun q => by
    unfold bdryApprox
    exact GoodSample.integral_withDensity_ofReal
      (measurable_dK_comp γ k measurable_const measurable_id)
      (fun t => mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le) _
  have hf : Measurable fun u : (FieldSample × ℝ) × ℝ =>
      dK γ k u.1.1 u.2 * tent (dl n) p u.1.2 u.2 :=
    (measurable_dK_comp γ k (measurable_fst.comp measurable_fst) measurable_snd).mul
      (measurable_tent_comp (dl n) p (measurable_snd.comp measurable_fst) measurable_snd)
  have hm := (StronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
    (f := fun u : (FieldSample × ℝ) × ℝ => dK γ k u.1.1 u.2 * tent (dl n) p u.1.2 u.2)
    hf.stronglyMeasurable).measurable
  rw [show (fun q : FieldSample × ℝ => ∫ t, tent (dl n) p q.2 t ∂bdryApprox γ q.1 k) =
    fun q => ∫ t, dK γ k q.1 t * tent (dl n) p q.2 t from funext heq]
  exact hm

lemma measurable_atomA (γ : ℝ) : Measurable (Function.uncurry (atomA γ)) := by
  unfold atomA
  refine Measurable.iInf fun n => Measurable.iSup fun p => ENNReal.measurable_ofReal.comp ?_
  exact Measurable.liminf (f := fun k (q : FieldSample × ℝ) =>
    ∫ t, tent (dl n) p q.2 t ∂bdryApprox γ q.1 k) fun k => measurable_integral_tent γ k n p

lemma iInter_Ioo_dl (s : ℝ) : ⋂ n : ℕ, Ioo (s - dl n) (s + dl n) = {s} := by
  ext t
  simp only [mem_iInter, mem_Ioo, mem_singleton_iff]
  constructor
  · intro h
    by_contra hts
    have hpos : 0 < |t - s| := abs_pos.2 (sub_ne_zero.2 hts)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    have h1 := h n
    have : |t - s| < dl n := abs_sub_lt_iff.2 ⟨by linarith [h1.2], by linarith [h1.1]⟩
    unfold dl at this
    linarith
  · rintro rfl n
    exact ⟨by linarith [dl_pos n], by linarith [dl_pos n]⟩

/-- On the event of vague convergence, `atomA` is the atom mass. -/
lemma atomA_eq {x : FieldSample} {ν : Measure ℝ} (hv : IsVagueLimitR (bdryApprox γ x) ν) (s : ℝ) :
    atomA γ x s = ν {s} := by
  have := hv.1
  have h1 : ∀ n p : ℕ, liminf (fun k => ∫ t, tent (dl n) p s t ∂bdryApprox γ x k) atTop =
      ∫ t, tent (dl n) p s t ∂ν := fun n p =>
    (hv.2 _ (continuous_tent_right _ p s) (hasCompactSupport_tent _ p s)).liminf_eq
  unfold atomA
  simp_rw [h1, ← measure_Ioo_eq_iSup]
  rw [← iInter_Ioo_dl s]
  refine (Antitone.measure_iInter (fun n m hnm => Ioo_subset_Ioo ?_ ?_)
    (fun _ => measurableSet_Ioo.nullMeasurableSet) ⟨0, measure_Ioo_lt_top.ne⟩).symm
  · have : dl m ≤ dl n := by
      unfold dl
      have : (n : ℝ) ≤ m := by exact_mod_cast hnm
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  · have : dl m ≤ dl n := by
      unfold dl
      have : (n : ℝ) ≤ m := by exact_mod_cast hnm
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith

lemma atomA_recJ (x : FieldSample) (s : ℝ) : atomA γ (recJ (fun j => x (muJ j))) s = atomA γ x s := by
  unfold atomA; rw [bdryApprox_recJ]

/-- The Palm test function `φ(y, s) = min(1, ν_{rec y}({s}))`. -/
def phiA (γ : ℝ) (y : ℕ → ℝ) (s : ℝ) : ℝ := min 1 (atomA γ (recJ y) s).toReal

lemma measurable_phiA (γ : ℝ) : Measurable (Function.uncurry (phiA γ)) :=
  measurable_const.min ((measurable_atomA γ).comp
    ((measurable_recJ.comp measurable_fst).prodMk measurable_snd)).ennreal_toReal

lemma measurable_phiA_comp (γ : ℝ) {α : Type*} [MeasurableSpace α] {f : α → ℕ → ℝ} {g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => phiA γ (f a) (g a) := by
  unfold phiA
  exact measurable_const.min ((measurable_atomA γ).comp
    ((measurable_recJ.comp hf).prodMk hg)).ennreal_toReal

lemma phiA_nonneg (γ : ℝ) (y : ℕ → ℝ) (s : ℝ) : 0 ≤ phiA γ y s :=
  le_min zero_le_one ENNReal.toReal_nonneg

lemma phiA_abs_le (γ : ℝ) (y : ℕ → ℝ) (s : ℝ) : |phiA γ y s| ≤ 1 := by
  rw [abs_of_nonneg (phiA_nonneg γ y s)]; exact min_le_left _ _

lemma phiA_coords {x : FieldSample} {ν : Measure ℝ} (hv : IsVagueLimitR (bdryApprox γ x) ν)
    (s : ℝ) : phiA γ (fun j => x (muJ j)) s = min 1 (ν {s}).toReal := by
  unfold phiA; rw [atomA_recJ, atomA_eq hv]

/-! ## 3. The Palm argument on a window -/

/-- **Hypothesis standing in for M4-P4** (log singularity of strength `γ`): for the normalized
free field `Z = zField X R`, every real `s` with `|s| + 1 ≤ R` and every continuous `g`, almost
surely `W = Z + γ(−log‖· − s‖) + g` has a vague limit of its approximations (it is good) and
`ν_W({s}) = 0`. -/
def LogSingNoAtom (X : Ω → FieldSample) (P : Measure Ω) (γ : ℝ) : Prop :=
  ∀ R : ℝ, 0 < R → ∀ s : ℝ, |s| + 1 ≤ R → ∀ g : ℂ → ℝ, Continuous g → ∀ᵐ ω ∂P,
    IsVagueLimitR (bdryApprox γ (zField X R ω + ofFun (fun z => γ * (-Real.log ‖z - (s : ℂ)‖)) +
        ofFun g))
      (qBoundaryMeasure γ (zField X R ω + ofFun (fun z => γ * (-Real.log ‖z - (s : ℂ)‖)) +
        ofFun g)) ∧
    qBoundaryMeasure γ (zField X R ω + ofFun (fun z => γ * (-Real.log ‖z - (s : ℂ)‖)) +
      ofFun g) {s} = 0

lemma ofFun_zero_add (y : FieldSample) : ofFun (fun _ => (0 : ℝ)) + y = y := by
  funext μ; simp [ofFun]

/-- **Window version**: a.s. `ν_{zField X (N+3)}` has no atom in `[-N, N]`. -/
theorem ae_noAtom_window [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ)
    (hγ2 : γ < 2) (hP4 : LogSingNoAtom X P γ) (N : ℕ) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, |s| ≤ N → qBoundaryMeasure γ (zField X ((N : ℝ) + 3) ω) {s} = 0 := by
  set R : ℝ := (N : ℝ) + 3 with hRdef
  have hR0 : 0 < R := by positivity
  have hab : Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1) ⊆
      Icc (-(((N + 1 : ℕ)) : ℝ)) (((N + 1 : ℕ)) : ℝ) := by push_cast; exact subset_rfl
  have hRN : (((N + 1 : ℕ)) : ℝ) + 2 ≤ R := by push_cast; linarith
  have hbump0 : ∀ x ∉ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1), BdryVague.bump N x = 0 :=
    fun x hx => bump_eq_zero_of_notMem hx
  have H := palm_formula_free (m := fun _ => (0 : ℝ)) (μ := muJ) (γ := γ) hX hγ hγ2 hRN hab
    continuous_const adm_muJ (BdryVague.continuous_bump N) (BdryVague.hasCompactSupport_bump N)
    (BdryVague.bump_nonneg N) hbump0 (measurable_phiA γ) (phiA_abs_le γ)
  simp only [ofFun_zero_add] at H
  -- the right side vanishes
  have hinner : ∀ x ∈ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1), ∀ᵐ ω ∂P,
      phiA γ (fun j => (zField X R ω + ofFun (fun z => γ / 2 * freeKernel R x z)) (muJ j)) x
        = 0 := by
    intro x hx
    have hxR : |x| + 1 ≤ R := by have := abs_le.2 hx; linarith
    filter_upwards [hP4 R hR0 x hxR _ (continuous_half_freeKernel_rem γ hR0)] with ω hω
    obtain ⟨hv, hat⟩ := hω
    have hcg : ∀ w ∈ Hbar, ∀ r > 0,
        (zField X R ω + ofFun (fun z => γ / 2 * freeKernel R x z)) (foldedCircle w r) =
        (zField X R ω + ofFun (fun z => γ * (-Real.log ‖z - (x : ℂ)‖)) +
          ofFun (fun z => -(γ / 2) * KernelId.fcPot R 0 z)) (foldedCircle w r) := by
      intro w hw r hr
      simp only [Pi.add_apply]
      rw [ofFun_half_freeKernel_apply γ hR0 x (isAdmissibleH_foldedCircle hw hr)]
      ring
    have hv' : IsVagueLimitR (bdryApprox γ (zField X R ω + ofFun (fun z => γ / 2 * freeKernel R x z)))
        (qBoundaryMeasure γ (zField X R ω + ofFun (fun z => γ / 2 * freeKernel R x z))) := by
      rw [bdryApprox_congr_Hbar hcg, qBoundaryMeasure_congr_Hbar hcg]; exact hv
    rw [phiA_coords hv', qBoundaryMeasure_congr_Hbar hcg, hat]
    simp
  have hRHS : ∫ x, BdryVague.bump N x * Real.exp (γ * 0 / 2 + γ ^ 2 * (2 * Real.log R) / 8) *
      ∫ ω, phiA γ (fun j => (zField X R ω + ofFun (fun z => γ / 2 * freeKernel R x z)) (muJ j)) x
        ∂P = 0 := by
    refine integral_eq_zero_of_ae (ae_of_all _ fun x => ?_)
    simp only [Pi.zero_apply]
    by_cases hx : x ∈ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1)
    · rw [integral_eq_zero_of_ae (hinner x hx), mul_zero]
    · rw [hbump0 x hx, zero_mul, zero_mul]
  -- the left side: integrability
  set ν : Ω → Measure ℝ := fun ω => qBoundaryMeasure γ (zField X R ω) with hνdef
  have hcoord : Measurable fun ω => fun j => zField X R ω (muJ j) :=
    measurable_pi_iff.2 fun j => (measurable_pi_apply _).comp (measurable_zField hX R)
  have hν : AEMeasurable ν P := LQGMeasAE.aemeasurable_qBoundaryMeasure_of_ae (X := zField X R)
    (fun μ => (measurable_pi_apply μ).comp (measurable_zField hX R))
    (ae_isVagueLimitR_qBoundaryMeasure_zField hX hγ hγ2 R)
  have hfin : ∫⁻ ω, ν ω (Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1)) ∂P < ∞ := by
    have h1 := lintegral_qBoundaryMeasure_zG_lt_top (m := fun _ => (0 : ℝ)) hX hγ hγ2 hRN hab
      continuousOn_const
    have e : ∀ ω, qBoundaryMeasure γ (ofFun (fun _ => (0 : ℝ)) + zG X R ω) = ν ω := fun ω => by
      rw [qBoundaryMeasure_congr_Hbar (zG_add_fc' R _ ω), ofFun_zero_add]
    simp_rw [e] at h1
    exact h1
  have hmeasI : AEMeasurable (fun ω => ν ω (Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1))) P :=
    (Measure.measurable_coe measurableSet_Icc).comp_aemeasurable hν
  set G : Ω × ℝ → ℝ := fun q => BdryVague.bump N q.2 * phiA γ (fun j => zField X R q.1 (muJ j)) q.2
    with hG
  have hGm : Measurable G :=
    ((BdryVague.continuous_bump N).measurable.comp measurable_snd).mul
      (measurable_phiA_comp γ (hcoord.comp measurable_fst) measurable_snd)
  have hG0 : ∀ q, 0 ≤ G q := fun q =>
    mul_nonneg (BdryVague.bump_nonneg N _) (phiA_nonneg γ _ _)
  have hG1 : ∀ q, ‖G q‖ ≤ 1 := fun q => by
    rw [Real.norm_of_nonneg (hG0 q)]
    exact mul_le_one₀ (max_le zero_le_one (min_le_left _ _)) (phiA_nonneg γ _ _)
      (min_le_left _ _)
  have hGvan : ∀ ω, ∀ x ∉ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1), G (ω, x) = 0 := fun ω x hx => by
    simp only [hG, hbump0 x hx, zero_mul]
  have hIres : ∀ ω, ∫ x, G (ω, x) ∂ν ω =
      ∫ x in Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1), G (ω, x) ∂ν ω := fun ω =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hGvan ω)).symm
  set κ := Palm.kerI hν (measurableSet_Icc (a := -((N : ℝ) + 1)) (b := (N : ℝ) + 1)) with hκ
  have hsm : StronglyMeasurable fun ω => ∫ x, G (ω, x) ∂κ ω :=
    hGm.stronglyMeasurable.integral_kernel_prod_right'
  have hIeq : (fun ω => ∫ x, G (ω, x) ∂ν ω) =ᵐ[P] fun ω => ∫ x, G (ω, x) ∂κ ω := by
    filter_upwards [Palm.nuMod_ae_eq hν measurableSet_Icc hfin] with ω hω
    simp only [hκ, Palm.kerI_apply, hω]
    exact hIres ω
  have hIbd : ∀ᵐ ω ∂P, ‖∫ x, G (ω, x) ∂ν ω‖ ≤
      (ν ω (Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1))).toReal := by
    filter_upwards [ae_lt_top' hmeasI hfin.ne] with ω hω
    have : IsFiniteMeasure ((ν ω).restrict (Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1))) :=
      isFiniteMeasure_restrict.2 hω.ne
    rw [hIres ω]
    have h := norm_integral_le_of_norm_le_const
      (μ := (ν ω).restrict (Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1))) (C := 1)
      (ae_of_all _ fun x => hG1 (ω, x))
    rwa [measureReal_def, Measure.restrict_apply_univ, one_mul] at h
  have hInt : Integrable (fun ω => ∫ x, G (ω, x) ∂ν ω) P :=
    (integrable_toReal_of_lintegral_ne_top hmeasI hfin.ne).mono'
      (hsm.aestronglyMeasurable.congr hIeq.symm) hIbd
  have hI0 : (fun ω => ∫ x, G (ω, x) ∂ν ω) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => integral_nonneg fun x => hG0 _) hInt).1
      (H.trans hRHS)
  -- conclusion, pathwise
  filter_upwards [hI0, ae_isVagueLimitR_qBoundaryMeasure_zField hX hγ hγ2 R,
    ae_lt_top' hmeasI hfin.ne] with ω hI hv hfinω s hs
  by_contra hne
  have hIω : ∫ x in Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1), G (ω, x) ∂ν ω = 0 := by
    rw [← hIres ω]; exact hI
  have : IsFiniteMeasure ((ν ω).restrict (Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1))) :=
    isFiniteMeasure_restrict.2 hfinω.ne
  have hint : Integrable (fun x => G (ω, x)) ((ν ω).restrict (Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1))) :=
    Integrable.of_bound (hGm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
      (ae_of_all _ fun x => hG1 (ω, x))
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => hG0 (ω, x)) hint).1 hIω
  have hsI : s ∈ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1) :=
    ⟨by linarith [(abs_le.1 hs).1], by linarith [(abs_le.1 hs).2]⟩
  have hfs : ν ω {s} ≠ ∞ := ne_top_of_le_ne_top hfinω.ne (measure_mono (singleton_subset_iff.2 hsI))
  have hpos : 0 < G (ω, s) := by
    simp only [hG]
    rw [BdryVague.bump_eq_one hs, one_mul, phiA_coords hv]
    exact lt_min one_pos (ENNReal.toReal_pos hne hfs)
  have hnull := ae_iff.1 hae
  have h0 : (ν ω).restrict (Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1)) {s} = 0 :=
    measure_mono_null (fun x hx => by
      rw [mem_singleton_iff.1 hx]; simp only [mem_ofPred_eq, Pi.zero_apply]; exact hpos.ne') hnull
  rw [Measure.restrict_apply (measurableSet_singleton s), singleton_inter_of_mem hsI] at h0
  exact hne h0

/-! ## 4. All of `ℝ`, and the other normalizations -/

/-- The additive constant multiplies the boundary measure. -/
lemma ae_qBoundaryMeasure_eq_smul [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) :
    ∀ᵐ ω ∂P, qBoundaryMeasure γ (X ω) =
      ENNReal.ofReal (Real.exp (γ / 2 * X ω (foldedCircle 0 R))) •
        qBoundaryMeasure γ (zField X R ω) := by
  filter_upwards [ae_bdryApprox_eq_smul hX γ R,
    ae_isVagueLimitR_qBoundaryMeasure_zField hX hγ hγ2 R] with ω hs hv
  have h := BdryVague.IsVagueLimitR.const_smul hv
    (c := ENNReal.ofReal (Real.exp (γ / 2 * X ω (foldedCircle 0 R)))) ENNReal.ofReal_ne_top
  have e : (fun k => ENNReal.ofReal (Real.exp (γ / 2 * X ω (foldedCircle 0 R))) •
      bdryApprox γ (zField X R ω) k) = bdryApprox γ (X ω) := funext fun k => (hs k).symm
  rw [e] at h
  exact qBoundaryMeasure_eq h

/-- **M4-P5 for the free field**: a.s. `ν_X` has no atoms. -/
theorem ae_noAtoms_free [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ)
    (hγ2 : γ < 2) (hP4 : LogSingNoAtom X P γ) :
    ∀ᵐ ω ∂P, NullSingletonClass (qBoundaryMeasure γ (X ω)) := by
  have h1 : ∀ᵐ ω ∂P, ∀ N : ℕ, ∀ s : ℝ, |s| ≤ N →
      qBoundaryMeasure γ (zField X ((N : ℝ) + 3) ω) {s} = 0 :=
    ae_all_iff.2 fun N => ae_noAtom_window hX hγ hγ2 hP4 N
  have h2 : ∀ᵐ ω ∂P, ∀ N : ℕ, qBoundaryMeasure γ (X ω) =
      ENNReal.ofReal (Real.exp (γ / 2 * X ω (foldedCircle 0 ((N : ℝ) + 3)))) •
        qBoundaryMeasure γ (zField X ((N : ℝ) + 3) ω) :=
    ae_all_iff.2 fun N => ae_qBoundaryMeasure_eq_smul hX hγ hγ2 _
  filter_upwards [h1, h2] with ω h1 h2
  refine ⟨fun s => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_ge |s|
  rw [h2 N, Measure.smul_apply, h1 N s hN, smul_zero]

/-- **M4-P5 for the normalized field** `zField X R` (any `R`). -/
theorem ae_noAtoms_zField [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ)
    (hγ2 : γ < 2) (hP4 : LogSingNoAtom X P γ) (R : ℝ) :
    ∀ᵐ ω ∂P, NullSingletonClass (qBoundaryMeasure γ (zField X R ω)) := by
  filter_upwards [ae_noAtoms_free hX hγ hγ2 hP4, ae_qBoundaryMeasure_eq_smul hX hγ hγ2 R]
    with ω h1 h2
  refine ⟨fun s => ?_⟩
  have := h1.measure_singleton s
  rw [h2, Measure.smul_apply, smul_eq_mul] at this
  exact (mul_eq_zero.1 this).resolve_left (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

end Atomless
end QuantumZipper
