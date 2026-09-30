import QuantumZipper.Proofs.Thm18.G2RootRPalm
import QuantumZipper.Proofs.Thm18.G2PalmIdCount
import QuantumZipper.Proofs.Zipper.E1Window2
import QuantumZipper.Proofs.Loewner.TwoPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2-PALMID, part 1: the countable coordinates of the rooted events

For the Palm nodes `G2RootXPalmIdStmt`, `G2RootRPalmIdStmt` (Duplantier–Sheffield,
arXiv:0808.1560, §3.3, in the normalized form `E1.palm_formula_Ioo`) every event must be written
as a measurable function of countably many coordinates `Y(μ_n)` of the unit-normalized field
`Y = N_S V` (`V = X₀ ω` or the Palm-shifted `X₀ ω + ψ_x`). The coordinate sequence `pidMu A B`
interleaves the dyadic folded circles `fcC k` (which carry the zoom law and the boundary measure,
through `reconstruct`) with two families `A n, B n` of balanced measures (which carry the outside
increments `V(p₁) − V(p₂)` for the countably many pairs `p` an outside event depends on,
`exists_countable_dep`).

* `coords_pidNf`: the raw dyadic coordinates of `h = 𝔥₀ + V − V(S)` are a deterministic shift
  of those of `N_S V`;
* `outMap_eq_pidR`: the outside increments on the countable set `J` are read from the
  coordinates;
* `cutL_eq`, `cutR_eq`: measurable (rational-infimum) versions of `ν[a, 0]`, `ν[0, b]`, exact for
  measures finite on compact intervals;
* `rhoX_eq`: `ρ_h(x) = |x| ρ_0(x)` (`∫ 𝔥₀ dS = 0`, since `S` lives on the unit circle).

Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Real

namespace QuantumZipper
namespace Thm18Asm

open Factorization (coords reconstruct)

/-! ## 1. The interleaved coordinate sequence -/

/-- `μ_{3k} = fcC k`, `μ_{3k+1} = A k`, `μ_{3k+2} = B k`. -/
def pidMu (A B : ℕ → Measure ℂ) (n : ℕ) : Measure ℂ :=
  if n % 3 = 0 then WedgeGood.fcC (n / 3) else if n % 3 = 1 then A (n / 3) else B (n / 3)

theorem pidMu_fc (A B : ℕ → Measure ℂ) (k : ℕ) : pidMu A B (3 * k) = WedgeGood.fcC k := by
  have h1 : 3 * k % 3 = 0 := by omega
  have h2 : 3 * k / 3 = k := by omega
  simp [pidMu, h1, h2]

theorem pidMu_A (A B : ℕ → Measure ℂ) (k : ℕ) : pidMu A B (3 * k + 1) = A k := by
  have h1 : (3 * k + 1) % 3 = 1 := by omega
  have h2 : (3 * k + 1) / 3 = k := by omega
  simp [pidMu, h1, h2]

theorem pidMu_B (A B : ℕ → Measure ℂ) (k : ℕ) : pidMu A B (3 * k + 2) = B k := by
  have h1 : (3 * k + 2) % 3 = 2 := by omega
  have h2 : (3 * k + 2) / 3 = k := by omega
  simp [pidMu, h1, h2]

theorem pidMu_adm {A B : ℕ → Measure ℂ} (hA : ∀ n, IsAdmissibleH (A n))
    (hB : ∀ n, IsAdmissibleH (B n)) (n : ℕ) : IsAdmissibleH (pidMu A B n) := by
  unfold pidMu
  split_ifs
  exacts [WedgeGood.fcC_admissible _, hA _, hB _]

section Pairs

variable {ι : Type*}

open Classical in
/-- First measures of the pairs indexed through an injection `e : J → ℕ` (junk `fcC 0`). -/
def pidA (J : Set ι) (e : J → ℕ) (pr : ι → Measure ℂ × Measure ℂ) (n : ℕ) : Measure ℂ :=
  if h : ∃ p : J, e p = n then (pr h.choose).1 else WedgeGood.fcC 0

open Classical in
/-- Second measures of the pairs. -/
def pidB (J : Set ι) (e : J → ℕ) (pr : ι → Measure ℂ × Measure ℂ) (n : ℕ) : Measure ℂ :=
  if h : ∃ p : J, e p = n then (pr h.choose).2 else WedgeGood.fcC 0

theorem pidA_e {J : Set ι} {e : J → ℕ} (he : Function.Injective e)
    (pr : ι → Measure ℂ × Measure ℂ) (p : J) : pidA J e pr (e p) = (pr p).1 := by
  have h : ∃ q : J, e q = e p := ⟨p, rfl⟩
  rw [pidA, dif_pos h, he h.choose_spec]

theorem pidB_e {J : Set ι} {e : J → ℕ} (he : Function.Injective e)
    (pr : ι → Measure ℂ × Measure ℂ) (p : J) : pidB J e pr (e p) = (pr p).2 := by
  have h : ∃ q : J, e q = e p := ⟨p, rfl⟩
  rw [pidB, dif_pos h, he h.choose_spec]

theorem pidA_adm {J : Set ι} {e : J → ℕ} {pr : ι → Measure ℂ × Measure ℂ}
    (hpr : ∀ p, IsAdmissibleH (pr p).1) (n : ℕ) : IsAdmissibleH (pidA J e pr n) := by
  unfold pidA
  split_ifs
  exacts [hpr _, WedgeGood.fcC_admissible _]

theorem pidB_adm {J : Set ι} {e : J → ℕ} {pr : ι → Measure ℂ × Measure ℂ}
    (hpr : ∀ p, IsAdmissibleH (pr p).2) (n : ℕ) : IsAdmissibleH (pidB J e pr n) := by
  unfold pidB
  split_ifs
  exacts [hpr _, WedgeGood.fcC_admissible _]

open Classical in
/-- Rebuild a function on `ι` from the coordinates on `J` (junk `0` off `J`). -/
def pidR (J : Set ι) (e : J → ℕ) (d : ℕ → ℝ) : ι → ℝ :=
  fun p => if hp : p ∈ J then d (e ⟨p, hp⟩) else 0

theorem measurable_pidR (J : Set ι) (e : J → ℕ) : Measurable (pidR J e) := by
  refine measurable_pi_iff.2 fun p => ?_
  by_cases hp : p ∈ J
  · simp only [pidR, dif_pos hp]; exact measurable_pi_apply _
  · simp only [pidR, dif_neg hp]; exact measurable_const

end Pairs

/-- The pair differences `c_{3n+1} − c_{3n+2}`. -/
def pidD (c : ℕ → ℝ) : ℕ → ℝ := fun n => c (3 * n + 1) - c (3 * n + 2)

theorem measurable_pidD : Measurable pidD :=
  measurable_pi_iff.2 fun _ => (measurable_pi_apply _).sub (measurable_pi_apply _)

/-! ## 2. Fields and their coordinates -/

/-- Theorem 1.2's field built from a sample `V`: `𝔥₀ + V − V(S)` (so `normField γ X ω =
pidNf γ (X ω)`). -/
def pidNf (γ : ℝ) (V : FieldSample) : FieldSample :=
  fun μ => ofFun (h0rev (γ ^ 2)) μ + (V μ - V refS)

/-- The coordinates `Y(μ_n)` of the unit-normalized field `Y = N_S V`. -/
def pidC (A B : ℕ → Measure ℂ) (V : FieldSample) : ℕ → ℝ :=
  fun n => PalmNorm.normAt refS V (pidMu A B n)

/-- The dyadic coordinates of `𝔥₀ + ·` read from the coordinate vector. -/
def pidDN (γ : ℝ) (c : ℕ → ℝ) : ℕ → ℝ :=
  fun k => ofFun (h0rev (γ ^ 2)) (WedgeGood.fcC k) + c (3 * k)

theorem measurable_pidDN (γ : ℝ) : Measurable (pidDN γ) :=
  measurable_pi_iff.2 fun _ => measurable_const.add (measurable_pi_apply _)

theorem coords_pidNf (γ : ℝ) (A B : ℕ → Measure ℂ) (V : FieldSample) :
    coords (pidNf γ V) = pidDN γ (pidC A B V) := by
  funext k
  simp only [pidDN, pidC, pidMu_fc, PalmNorm.normAt, addConst, measure_univ,
    ENNReal.toReal_one, mul_one]
  show ofFun (h0rev (γ ^ 2)) (WedgeGood.fcC k) + (V (WedgeGood.fcC k) - V refS) = _
  ring

theorem pidC_pair {A B : ℕ → Measure ℂ} (V : FieldSample) {n : ℕ}
    (h : A n univ = B n univ) :
    pidD (pidC A B V) n = V (A n) - V (B n) := by
  simp only [pidD, pidC, pidMu_A, pidMu_B, PalmNorm.normAt, addConst, h]
  ring

/-- The pair map of the outside index. -/
def outPr (i : G3Idx) (p : OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂) : Measure ℂ × Measure ℂ := p.1

theorem outMap_eq_pidR (i : G3Idx) {J : Set (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂)} {e : J → ℕ}
    (he : Function.Injective e) (V : FieldSample) :
    ∀ p ∈ J, outMap i V p =
      pidR J e (pidD (pidC (pidA J e (outPr i)) (pidB J e (outPr i)) V)) p := by
  intro p hp
  simp only [pidR, dif_pos hp]
  rw [pidC_pair V (by rw [pidA_e he, pidB_e he]; exact p.2.2.2.1), pidA_e he, pidB_e he]
  rfl

theorem zoomLaw_reconstruct_coords (γ C : ℝ) (y : FieldSample) (x : ℝ) :
    zoomLaw γ C (reconstruct (coords y)) x = zoomLaw γ C y x := by
  simp only [zoomLaw, S5.FieldLaw.Raw.zoomField_reconstruct_coords]

theorem bdryM_eq_bdryMc (γ : ℝ) (y : FieldSample) : bdryM γ y = bdryMc γ (coords y) := by
  rw [bdryMc_coords_eq]; rfl

/-! ## 3. Measurable interval masses -/

/-- `ν[a, 0]` through rational left endpoints. -/
def cutL (m : Measure ℝ) (a : ℝ) : ℝ≥0∞ := ⨅ q : ℚ, if (q : ℝ) < a then m (Icc (q : ℝ) 0) else ⊤

/-- `ν[0, b]` through rational right endpoints. -/
def cutR (m : Measure ℝ) (b : ℝ) : ℝ≥0∞ := ⨅ q : ℚ, if b < (q : ℝ) then m (Icc 0 (q : ℝ)) else ⊤

theorem cutL_eq {m : Measure ℝ} (hm : ∀ u : ℝ, m (Icc u 0) ≠ ⊤) (a : ℝ) :
    cutL m a = m (Icc a 0) := by
  refine le_antisymm ?_ (le_iInf fun q => ?_)
  · set S : ℕ → Set ℝ := fun n => Icc (a - 1 / ((n : ℝ) + 1)) 0 with hS
    have hanti : Antitone S := fun n n' hnn' => Icc_subset_Icc_left (by
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2 : (n : ℝ) + 1 ≤ (n' : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnn' 1
      have := one_div_le_one_div_of_le h1 h2
      linarith)
    have hI : (⋂ n, S n) = Icc a 0 := by
      ext t
      simp only [hS, mem_iInter, mem_Icc]
      refine ⟨fun h => ⟨?_, (h 0).2⟩, fun h n => ⟨?_, h.2⟩⟩
      · by_contra hlt
        push_neg at hlt
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
        linarith [(h n).1]
      · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith [h.1]
    have hT := tendsto_measure_iInter_atTop (μ := m) (fun n => measurableSet_Icc.nullMeasurableSet)
      hanti ⟨0, hm _⟩
    rw [hI] at hT
    refine ge_of_tendsto hT (Eventually.of_forall fun n => ?_)
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show a - 1 / ((n : ℝ) + 1) < a by linarith)
    refine (iInf_le _ q).trans ?_
    rw [if_pos hq2]
    exact measure_mono (Icc_subset_Icc_left hq1.le)
  · split_ifs with hq
    · exact measure_mono (Icc_subset_Icc_left hq.le)
    · exact le_top

theorem cutR_eq {m : Measure ℝ} (hm : ∀ u : ℝ, m (Icc 0 u) ≠ ⊤) (b : ℝ) :
    cutR m b = m (Icc 0 b) := by
  refine le_antisymm ?_ (le_iInf fun q => ?_)
  · set S : ℕ → Set ℝ := fun n => Icc 0 (b + 1 / ((n : ℝ) + 1)) with hS
    have hanti : Antitone S := fun n n' hnn' => Icc_subset_Icc_right (by
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2 : (n : ℝ) + 1 ≤ (n' : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnn' 1
      have := one_div_le_one_div_of_le h1 h2
      linarith)
    have hI : (⋂ n, S n) = Icc 0 b := by
      ext t
      simp only [hS, mem_iInter, mem_Icc]
      refine ⟨fun h => ⟨(h 0).1, ?_⟩, fun h n => ⟨h.1, ?_⟩⟩
      · by_contra hlt
        push_neg at hlt
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
        linarith [(h n).2]
      · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith [h.2]
    have hT := tendsto_measure_iInter_atTop (μ := m) (fun n => measurableSet_Icc.nullMeasurableSet)
      hanti ⟨0, hm _⟩
    rw [hI] at hT
    refine ge_of_tendsto hT (Eventually.of_forall fun n => ?_)
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show b < b + 1 / ((n : ℝ) + 1) by linarith)
    refine (iInf_le _ q).trans ?_
    rw [if_pos hq1]
    exact measure_mono (Icc_subset_Icc_right hq2.le)
  · split_ifs with hq
    · exact measure_mono (Icc_subset_Icc_right hq.le)
    · exact le_top

theorem measurable_cutL {α : Type*} [MeasurableSpace α] {M : α → Measure ℝ} (hM : Measurable M)
    {a : α → ℝ} (ha : Measurable a) : Measurable fun p => cutL (M p) (a p) := by
  refine Measurable.iInf fun q => Measurable.ite (measurableSet_lt measurable_const ha)
    ((Measure.measurable_coe measurableSet_Icc).comp hM) measurable_const

theorem measurable_cutR {α : Type*} [MeasurableSpace α] {M : α → Measure ℝ} (hM : Measurable M)
    {b : α → ℝ} (hb : Measurable b) : Measurable fun p => cutR (M p) (b p) := by
  refine Measurable.iInf fun q => Measurable.ite (measurableSet_lt hb measurable_const)
    ((Measure.measurable_coe measurableSet_Icc).comp hM) measurable_const

/-! ## 4. The Palm density -/

theorem ae_norm_refS : ∀ᵐ u ∂refS, ‖u‖ = 1 := by
  rw [ae_iff]
  have hB : MeasurableSet {x : ℂ | ¬ ‖x‖ = 1} :=
    (measurableSet_eq_fun continuous_norm.measurable measurable_const).compl
  rw [show refS = foldedCircle 0 1 from rfl, TwoPoint.foldedCircle_apply' 0 1 hB]
  have : {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ foldH (circleMap 0 1 θ) ∈ {x : ℂ | ¬ ‖x‖ = 1}} = ∅ := by
    ext θ
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_not]
    intro _
    rw [TwoPoint.norm_foldH, norm_circleMap_zero]
    simp
  rw [this, measure_empty, mul_zero]

theorem integral_h0rev_refS (κ : ℝ) : ∫ u, h0rev κ u ∂refS = 0 := by
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_norm_refS] with u hu
  simp [h0rev, hu]

/-- **`ρ_h(x) = |x| ρ_0(x)`** off `0`. -/
theorem rhoX_eq {γ : ℝ} (hγ : 0 < γ) {x : ℝ} (hx : x ≠ 0) :
    rhoX γ x = |x| * PalmNorm.rhoNorm γ 0 refS x := by
  unfold rhoX PalmNorm.rhoNorm
  rw [integral_h0rev_refS]
  have hh : h0rev (γ ^ 2) (x : ℂ) = 2 / γ * Real.log |x| := by
    simp only [h0rev, Real.sqrt_sq hγ.le, Complex.norm_real, Real.norm_eq_abs]
  simp only [hh, Pi.zero_apply, integral_zero]
  set k := PalmNorm.kPot refS (x : ℂ)
  set kk := PalmNorm.kkPot refS
  have e : γ * (2 / γ * Real.log |x|) / 2 - γ / 2 * 0 - γ ^ 2 / 4 * k + γ ^ 2 / 8 * kk =
      Real.log |x| + (γ * 0 / 2 - γ / 2 * 0 - γ ^ 2 / 4 * k + γ ^ 2 / 8 * kk) := by
    field_simp
    ring
  rw [e, Real.exp_add, Real.exp_log (abs_pos.2 hx)]

end Thm18Asm
end QuantumZipper
