import QuantumZipper.Proofs.Thm18.A1RS3Tr2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS3 (11): joint measurability of the Loewner maps in (path, point)

On the path space `ℝ≥0 → ℝ` (product σ-algebra), with the regularized driver
`regDrv κ x = √κ · (x̃ − x̃(0))` (`x̃ = pathReg x`, continuous for every `x`; `DrvGood.pB`):

* `measurable_finvM`: `(x, u) ↦ f_t⁻¹(u)` is jointly measurable (`finvM`, equal to
  `fwdMapInv (regDrv κ x) t u` for `u ∈ ℍ`; Carathéodory: holomorphic in `u ∈ ℍ`
  (`RS.differentiableOn_fwdMapInv`), measurable in the path for fixed `u`
  (`RS.measurable_fwdMapInv_drive`); mathlib `measurable_uncurry_of_continuous_of_measurable`);
* `measurable_fM`, `fM_eq`: `(x, z) ↦ f_t(z)` has a jointly measurable version `fM`, equal to
  `fwdMap (regDrv κ x) t z` on `ℍ \ K_t`: `f_t(z)` is the limit of the first points `u_j` of a
  dense sequence of `ℍ` with `|f_t⁻¹(u_j) − z| < 1/(n+1)` (`f_t⁻¹` is a homeomorphism of `ℍ` onto
  `ℍ \ K_t` with inverse `f_t`, `RS.fwdMap_fwdMapInv`, `FwdHolo.differentiableOn_fwdMap`).

Own elementary bookkeeping (measurability the paper leaves implicit).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

/-- The regularized driver of a path. -/
def regDrv (κ : ℝ) (x : ℝ≥0 → ℝ) : ℝ → ℝ := drive κ DrvGood.pB x

theorem continuous_regDrv (κ : ℝ) (x : ℝ≥0 → ℝ) : Continuous (regDrv κ x) :=
  continuous_const.mul ((DrvGood.continuous_pB x).comp continuous_real_toNNReal)

theorem regDrv_zero (κ : ℝ) (x : ℝ≥0 → ℝ) : regDrv κ x 0 = 0 := by
  simp [regDrv, drive, DrvGood.pB_zero]

theorem regDrv_eq {κ : ℝ} {a : ℝ≥0 → ℝ} (hc : Continuous a) (h0 : a 0 = 0) :
    regDrv κ a = pathDrive κ a := by
  funext r
  simp only [regDrv, drive, DrvGood.pB, pathDrive, G1Pkg.pathReg_spec.2.2 a hc, h0, sub_zero]

/-- `f_t⁻¹` vanishes off `ℍ` (the image of `f_t` lies in `ℍ`). -/
theorem fwdMapInv_of_not_mem {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {u : ℂ}
    (hu : u ∉ H) : fwdMapInv W t u = 0 := by
  unfold fwdMapInv
  rw [dif_neg]
  rintro ⟨z', ⟨hz', hfz⟩, -⟩
  exact hu (hfz ▸ FwdHolo.mapsTo_fwdMap hW ht hz')

/-- The jointly measurable inverse Loewner map. -/
def finvM (κ t : ℝ) (q : (ℝ≥0 → ℝ) × ℂ) : ℂ :=
  if 0 < q.2.im then fwdMapInv (regDrv κ q.1) t q.2 else 0

theorem finvM_eq (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ≥0 → ℝ) (u : ℂ) :
    finvM κ t (x, u) = fwdMapInv (regDrv κ x) t u := by
  unfold finvM
  split_ifs with h
  · rfl
  · exact (fwdMapInv_of_not_mem (continuous_regDrv κ x) ht h).symm

theorem measurable_finvM (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) : Measurable (finvM κ t) := by
  set U : H → (ℝ≥0 → ℝ) → ℂ := fun i x => fwdMapInv (regDrv κ x) t i with hU
  have hUc : ∀ x, Continuous fun i : H => U i x := fun x =>
    (RS.differentiableOn_fwdMapInv (continuous_regDrv κ x) (regDrv_zero κ x) ht).continuousOn
      |>.comp_continuous continuous_subtype_val fun i => i.2
  have hUm : ∀ i : H, Measurable (U i) := fun i =>
    RS.measurable_fwdMapInv_drive DrvGood.measurable_pB DrvGood.continuous_pB DrvGood.pB_zero κ
      ht i.2
  have hj : Measurable (Function.uncurry U) := measurable_uncurry_of_continuous_of_measurable hUc hUm
  set S : Set ((ℝ≥0 → ℝ) × ℂ) := {q | 0 < q.2.im} with hSdef
  have hHm : MeasurableSet S :=
    measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_snd)
  have e : finvM κ t = fun q => if h : q ∈ S then Function.uncurry U (⟨q.2, h⟩, q.1) else 0 := by
    funext q
    unfold finvM
    by_cases h : 0 < q.2.im
    · have h' : q ∈ S := h
      rw [dif_pos h', if_pos h]; rfl
    · have h' : q ∉ S := h
      rw [dif_neg h', if_neg h]
  rw [e]
  refine Measurable.dite (f := fun q : S => Function.uncurry U (⟨(q : (ℝ≥0 → ℝ) × ℂ).2, q.2⟩,
    (q : (ℝ≥0 → ℝ) × ℂ).1)) ?_ measurable_const hHm
  exact hj.comp ((measurable_snd.comp measurable_subtype_coe).subtype_mk.prodMk
    (measurable_fst.comp measurable_subtype_coe))

/-- A dense sequence of `ℍ`. -/
def hSeq : ℕ → H :=
  haveI : Nonempty H := ⟨⟨Complex.I, (by norm_num : (0 : ℝ) < Complex.I.im)⟩⟩
  (TopologicalSpace.exists_dense_seq H).choose

theorem denseRange_hSeq : DenseRange hSeq :=
  haveI : Nonempty H := ⟨⟨Complex.I, (by norm_num : (0 : ℝ) < Complex.I.im)⟩⟩
  (TopologicalSpace.exists_dense_seq H).choose_spec

/-- The selection condition. -/
def selP (κ t : ℝ) (n : ℕ) (q : (ℝ≥0 → ℝ) × ℂ) (j : ℕ) : Prop :=
  ‖finvM κ t (q.1, (hSeq j : ℂ)) - q.2‖ < 1 / ((n : ℝ) + 1) ∨
    ¬ ∃ j' : ℕ, ‖finvM κ t (q.1, (hSeq j' : ℂ)) - q.2‖ < 1 / ((n : ℝ) + 1)

theorem selP_exists (κ t : ℝ) (n : ℕ) (q : (ℝ≥0 → ℝ) × ℂ) : ∃ j, selP κ t n q j := by
  by_cases h : ∃ j' : ℕ, ‖finvM κ t (q.1, (hSeq j' : ℂ)) - q.2‖ < 1 / ((n : ℝ) + 1)
  · obtain ⟨j, hj⟩ := h; exact ⟨j, Or.inl hj⟩
  · exact ⟨0, Or.inr h⟩

open Classical in
/-- The jointly measurable forward Loewner map. -/
def fM (κ t : ℝ) (q : (ℝ≥0 → ℝ) × ℂ) : ℂ :=
  limUnder atTop fun n : ℕ => (hSeq (Nat.find (selP_exists κ t n q)) : ℂ)

theorem measurable_fM (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) : Measurable (fM κ t) := by
  classical
  have hfm := measurable_finvM κ ht
  have hc : ∀ j : ℕ, Measurable fun q : (ℝ≥0 → ℝ) × ℂ =>
      ‖finvM κ t (q.1, (hSeq j : ℂ)) - q.2‖ := fun j =>
    ((hfm.comp (measurable_fst.prodMk measurable_const)).sub measurable_snd).norm
  have hS : ∀ n j, MeasurableSet {q | selP κ t n q j} := by
    intro n j
    refine measurableSet_setOfPred.2 ((measurable_prop_lt (hc j) _).or ?_)
    exact (Measurable.exists fun j' => measurable_prop_lt (hc j') _).not
  have hn : ∀ n : ℕ, Measurable fun q => (hSeq (Nat.find (selP_exists κ t n q)) : ℂ) := fun n =>
    Measurable.find (f := fun j (_ : (ℝ≥0 → ℝ) × ℂ) => (hSeq j : ℂ)) (fun j => measurable_const)
      (hS n) (selP_exists κ t n)
  exact (StronglyMeasurable.limUnder (l := atTop) (f := fun n q =>
    (hSeq (Nat.find (selP_exists κ t n q)) : ℂ)) fun n => (hn n).stronglyMeasurable).measurable

theorem fM_eq (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ≥0 → ℝ) {z : ℂ}
    (hz : z ∈ H \ fwdHull (regDrv κ x) t) : fM κ t (x, z) = fwdMap (regDrv κ x) t z := by
  classical
  set W := regDrv κ x with hW
  have hWc : Continuous W := continuous_regDrv κ x
  have hW0 : W 0 = 0 := regDrv_zero κ x
  set fz := fwdMap W t z with hfz
  have hfzH : fz ∈ H := FwdHolo.mapsTo_fwdMap hWc ht hz
  have hinv : fwdMapInv W t fz = z := RS.fwdMapInv_fwdMap hWc hW0 ht hz
  have hcont : ContinuousAt (fwdMapInv W t) fz :=
    (RS.differentiableOn_fwdMapInv hWc hW0 ht).continuousOn.continuousAt
      (isOpen_H.mem_nhds hfzH)
  have hfin : ∀ u ∈ H, finvM κ t (x, u) = fwdMapInv W t u := fun u _ => finvM_eq κ ht x u
  -- existence of good grid points
  have hex : ∀ n : ℕ, ∃ j : ℕ, ‖finvM κ t (x, (hSeq j : ℂ)) - z‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.1 hcont _ hpos
    obtain ⟨δ', hδ', hδ'H⟩ := Metric.isOpen_iff.1 isOpen_H fz hfzH
    set O : Set H := {v : H | dist (v : ℂ) fz < min δ δ'} with hO
    have hOo : IsOpen O := isOpen_lt (continuous_subtype_val.dist continuous_const)
      continuous_const
    have hOne : O.Nonempty := ⟨⟨fz, hfzH⟩, by simp [hO, hδ, hδ']⟩
    obtain ⟨j, hj⟩ := denseRange_hSeq.exists_mem_open hOo hOne
    refine ⟨j, ?_⟩
    have hjd : dist (hSeq j : ℂ) fz < δ := hj.trans_le (min_le_left _ _)
    rw [hfin _ (hSeq j).2, ← dist_eq_norm, ← hinv]
    exact hδb hjd
  have hsel : ∀ n : ℕ, ‖finvM κ t (x, (hSeq (Nat.find (selP_exists κ t n (x, z))) : ℂ)) - z‖ <
      1 / ((n : ℝ) + 1) := by
    intro n
    rcases Nat.find_spec (selP_exists κ t n (x, z)) with h | h
    · exact h
    · exact absurd (hex n) h
  -- convergence to `f_t(z)`
  have hopen := FwdHolo.isOpen_compl_fwdHull hWc ht (W := W)
  have hfc : ContinuousAt (fwdMap W t) z :=
    (FwdHolo.differentiableOn_fwdMap hWc ht).continuousOn.continuousAt (hopen.mem_nhds hz)
  have hT : Tendsto (fun n : ℕ => (hSeq (Nat.find (selP_exists κ t n (x, z))) : ℂ)) atTop
      (𝓝 fz) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.1 hfc ε hε
    obtain ⟨δ', hδ', hδ'U⟩ := Metric.isOpen_iff.1 hopen z hz
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (lt_min hδ hδ')
    refine ⟨N, fun n hn => ?_⟩
    set v : H := hSeq (Nat.find (selP_exists κ t n (x, z))) with hv
    have h1 := hsel n
    rw [hfin _ v.2] at h1
    have hnN : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hd : dist (fwdMapInv W t v) z < min δ δ' := by
      rw [dist_eq_norm]; exact h1.trans_le (hnN.trans hN.le)
    have h2 := hδb (hd.trans_le (min_le_left _ _))
    rw [RS.fwdMap_fwdMapInv hWc hW0 ht v.2] at h2
    exact h2
  exact hT.limUnder_eq

end A1RS
end R18
end QuantumZipper
