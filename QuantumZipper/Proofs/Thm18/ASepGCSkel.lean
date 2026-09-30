import QuantumZipper.Proofs.Thm18.ASepTr1
import QuantumZipper.Proofs.Thm18.G4CMeasCoan
import QuantumZipper.Proofs.Zipper.F1ReadMeasPath
import QuantumZipper.Proofs.Zipper.F1ReadMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP-GC, part 1: the descriptive-set skeleton of `GoodCMeasStmt`

`ASep.GoodC γ` quantifies over all continuous paths with a given code and all fields with given
circle coordinates. Here:

* the codes of continuous paths form a Borel set `C1` (the dyadic certificate `F1.DyUC` of the
  path read from the code, and the code read back; `mem_C1_of_continuous`,
  `exists_of_mem_C1`);
* the realizable circle-coordinate vectors form a closed set `C2` (`mem_C2`, `exists_of_mem_C2`);
* `BackSepI → BackSupportI` (`backSupportI_of_backSepI`), so the support hypothesis of
  `G4SepConcl0` is redundant;
* **`goodCMeasStmt_of`**: `GoodCMeasStmt` follows from two Borel inputs,
  `GCSepStmt` (a Borel set sandwiched between the `1/(n+1)`-separation and `BackSepI`) and
  `GCExStmt` (a Borel set equal to the exactness identities on separated parameters): `GoodC γ`
  is then a universal quantifier over the Polish parameter `(τ, a, i, n)` of a Borel set, hence
  coanalytic and null-measurable (`G4Core.nullMeasurableSet_forall`; Lusin, Kechris,
  *Classical Descriptive Set Theory*, Thm 21.10).

The sandwich is needed because `BackSepI` (an `∃ δ`, `∀`-points-of-a-thickening condition on a
Loewner hull) is only coanalytic on its face; it enters `GoodC` as a hypothesis, so a Borel
replacement between two separation levels is what keeps `GoodC` coanalytic.

Own bookkeeping (measurability the paper leaves implicit; Sheffield arXiv:1012.4797 §1.6 works
with the product law of the independent pair (driver, wedge) throughout).
-/

noncomputable section

open MeasureTheory Set Function
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ASep
namespace GC

open Thm18Asm Thm18Asm.G4Core

/-! ## Codes of continuous paths -/

theorem exists_qs_eq_dy (n j : ℕ) : ∃ m, qs m = (F1.dy n j).toNNReal := by
  obtain ⟨m, hm⟩ := (exists_surjective_nat ℚ).choose_spec ((j : ℚ) / 2 ^ n)
  refine ⟨m, ?_⟩
  simp only [qs, enumRat, hm, F1.dy]
  push_cast
  rfl

open Classical in
/-- The path on `ℝ≥0` read from a code (junk `0` off the code times). -/
def pq (k : ℕ → ℝ) : ℝ≥0 → ℝ := fun r => if h : ∃ n, qs n = r then k (Nat.find h) else 0

theorem measurable_pq : Measurable pq := by
  classical
  refine measurable_pi_iff.2 fun r => ?_
  by_cases h : ∃ n, qs n = r
  · simp only [pq, dif_pos h]; exact measurable_pi_apply _
  · simp only [pq, dif_neg h]; exact measurable_const

theorem pq_codeP {x : ℝ≥0 → ℝ} {r : ℝ≥0} (h : ∃ n, qs n = r) : pq (codeP x) r = x r := by
  classical
  simp only [pq, dif_pos h, codeP]
  rw [Nat.find_spec h]

theorem dyv_pq_codeP (x : ℝ≥0 → ℝ) (n j : ℕ) : F1.dyv (pq (codeP x)) n j = F1.dyv x n j :=
  pq_codeP (exists_qs_eq_dy n j)

/-- The path rebuilt from a code. -/
def xr (k : ℕ → ℝ) : ℝ≥0 → ℝ := fun r => F1.readDrv (pq k) r

/-- The Borel set of codes of continuous paths. -/
def C1 : Set (ℕ → ℝ) :=
  {k | F1.DyUC (pq k)} ∩ ⋂ n, {k | F1.readDrv (pq k) (qs n) = k n}

theorem measurableSet_C1 : MeasurableSet C1 :=
  (F1.measurableSet_dyUC.preimage measurable_pq).inter (MeasurableSet.iInter fun n =>
    measurableSet_eq_fun ((F1.measurable_readDrv_apply _).comp measurable_pq)
      (measurable_pi_apply n))

theorem readDrv_pq_codeP (x : ℝ≥0 → ℝ) : F1.readDrv (pq (codeP x)) = F1.readDrv x := by
  funext t
  rw [F1.readDrv_eq_limUnder, F1.readDrv_eq_limUnder]
  simp only [dyv_pq_codeP]

theorem readDrv_of_continuous {x : ℝ≥0 → ℝ} (hx : Continuous x) (r : ℝ≥0) :
    F1.readDrv x r = x r := by
  have hW : Continuous fun s : ℝ => x s.toNNReal := hx.comp continuous_real_toNNReal
  have e := F1.readDrv_eq hW (fun s => by simp only [Real.toNNReal_coe])
  have e2 : (fun t : ℝ≥0 => x (t : ℝ).toNNReal) = x := funext fun t => by simp
  rw [e2] at e
  rw [e]; simp

theorem mem_C1_of_continuous {x : ℝ≥0 → ℝ} (hx : Continuous x) : codeP x ∈ C1 := by
  refine ⟨?_, mem_iInter.2 fun n => ?_⟩
  · have h := F1.dyUC_of_continuous hx
    show F1.DyUC (pq (codeP x))
    unfold F1.DyUC at h ⊢
    simpa only [dyv_pq_codeP] using h
  · show F1.readDrv (pq (codeP x)) (qs n) = codeP x n
    rw [readDrv_pq_codeP, readDrv_of_continuous hx]
    rfl

theorem exists_of_mem_C1 {k : ℕ → ℝ} (hk : k ∈ C1) : ∃ x, Continuous x ∧ codeP x = k :=
  ⟨xr k, (F1.continuous_readDrv_of_dyUC hk.1).comp NNReal.continuous_coe,
    funext fun n => (mem_iInter.1 hk.2 n)⟩

/-! ## Realizable circle coordinates -/

/-- The enumerated folded circles. -/
def fcF (i : ℕ) : Measure ℂ := foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2

/-- The closed set of realizable circle-coordinate vectors. -/
def C2 : Set (ℕ → ℝ) := ⋂ i, ⋂ j, {v | fcF i = fcF j → v i = v j}

theorem measurableSet_C2 : MeasurableSet C2 := by
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  by_cases h : fcF i = fcF j
  · simp only [h, true_implies]
    exact measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
  · simp [h]

theorem mem_C2 (y : FieldSample) : CoordsFull.coordsFull y ∈ C2 := by
  refine mem_iInter.2 fun i => mem_iInter.2 fun j => fun h => ?_
  show y (fcF i) = y (fcF j)
  rw [h]

open Classical in
theorem exists_of_mem_C2 {v : ℕ → ℝ} (hv : v ∈ C2) :
    ∃ y : FieldSample, CoordsFull.coordsFull y = v := by
  refine ⟨fun μ => if h : ∃ i, fcF i = μ then v (Nat.find h) else 0, funext fun i => ?_⟩
  have h : ∃ j, fcF j = fcF i := ⟨i, rfl⟩
  show (if h : ∃ j, fcF j = fcF i then v (Nat.find h) else 0) = v i
  rw [dif_pos h]
  exact mem_iInter.1 (mem_iInter.1 hv _) i (Nat.find_spec h)

/-! ## The support hypothesis is redundant -/

theorem backSupportI_of_backSepI {c : FieldSample × (ℝ → ℝ)} {τ τ' a : ℝ} {i : ℕ}
    (h : BackSepI c τ τ' a i) : BackSupportI c τ τ' a i := by
  obtain ⟨δ, hδ, hnull⟩ := h
  have hK : fcI i (revHull (backDrv c.2 τ τ' a).2 (backDrv c.2 τ τ' a).1) = 0 :=
    measure_mono_null (Metric.self_subset_thickening hδ _) hnull
  have hHc : fcI i Hᶜ = 0 :=
    ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H _ (UnzipFull.fullIndex_radius_pos i))
  refine measure_mono_null (fun z hz => ?_) (measure_union_null hHc hK)
  by_cases hzH : z ∈ H
  · exact Or.inr ⟨hzH, hz⟩
  · exact Or.inl hzH

/-! ## The two Borel inputs -/

/-- Separation at level `δ` of the `i`-th circle from the hull of `backDrv W τ 0 a`. -/
def SepD (W : ℝ → ℝ) (τ a : ℝ) (i : ℕ) (δ : ℝ) : Prop :=
  fcI i (Metric.thickening δ (revHull (backDrv W τ 0 a).2 (backDrv W τ 0 a).1)) = 0

/-- The two exactness identities of `G4SepConcl0` at one parameter. -/
def ExactC (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) (τ a : ℝ) (i : ℕ) : Prop :=
  (evalReg (rescale (unzippedField γ c τ) (Qc γ) a)
      ((fcI i).map (revMapInv (backDrv c.2 τ 0 a).2 (backDrv c.2 τ 0 a).1)) =
    rescale (unzippedField γ c τ) (Qc γ) a
      ((fcI i).map (revMapInv (backDrv c.2 τ 0 a).2 (backDrv c.2 τ 0 a).1))) ∧
  evalReg (unzippedField γ c τ)
      ((fcI i).map fun w => (a : ℂ) * revMapInv (backDrv c.2 τ 0 a).2
        (backDrv c.2 τ 0 a).1 w) =
    unzippedField γ c τ
      ((fcI i).map fun w => (a : ℂ) * revMapInv (backDrv c.2 τ 0 a).2
        (backDrv c.2 τ 0 a).1 w)

/-- **Borel separation sandwich**: a Borel set of (path code, `τ, a, i, n`) containing the
`1/(n+1)`-separated parameters and contained in the `BackSepI`-separated ones. -/
def GCSepStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ S : Set ((ℕ → ℝ) × (ℝ × ℝ × ℕ × ℕ)), MeasurableSet S ∧
    ∀ x : ℝ≥0 → ℝ, Continuous x → ∀ τ a : ℝ, 0 < τ → 0 < a → ∀ i n : ℕ,
      (SepD (pathDrive (γ ^ 2) x) τ a i (1 / ((n : ℝ) + 1)) →
        (codeP x, (τ, a, i, n)) ∈ S) ∧
      ((codeP x, (τ, a, i, n)) ∈ S → ∃ δ : ℝ, 0 < δ ∧ SepD (pathDrive (γ ^ 2) x) τ a i δ)

/-- **Borel exactness**: a Borel set of (path code, circle coordinates, `τ, a, i`) equal to the
exactness identities on separated parameters. -/
def GCExStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ X : Set (((ℕ → ℝ) × (ℕ → ℝ)) × (ℝ × ℝ × ℕ)), MeasurableSet X ∧
    ∀ x : ℝ≥0 → ℝ, Continuous x → ∀ y : FieldSample, ∀ τ a : ℝ, 0 < τ → 0 < a → ∀ i : ℕ,
      BackSepI (y, pathDrive (γ ^ 2) x) τ 0 a i →
      (((codeP x, CoordsFull.coordsFull y), (τ, a, i)) ∈ X ↔
        ExactC γ (y, pathDrive (γ ^ 2) x) τ a i)

/-- **`GoodCMeasStmt` from the two Borel inputs.** -/
theorem goodCMeasStmt_of (hS : GCSepStmt) (hX : GCExStmt) : GoodCMeasStmt := by
  intro γ hγ hγ2 ρ _
  obtain ⟨S, hSm, hSs⟩ := hS γ hγ hγ2
  obtain ⟨X, hXm, hXs⟩ := hX γ hγ hγ2
  set R : Set (((ℕ → ℝ) × (ℕ → ℝ)) × (ℝ × ℝ × ℕ × ℕ)) :=
    {p | p.1.1 ∈ C1 → p.1.2 ∈ C2 → 0 < p.2.1 → 0 < p.2.2.1 → (p.1.1, p.2) ∈ S →
      (p.1, (p.2.1, p.2.2.1, p.2.2.2.1)) ∈ X} with hRdef
  have hRm : MeasurableSet R := by
    have h1 : Measurable fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℝ × ℝ × ℕ × ℕ) => p.1.1 ∈ C1 :=
      measurableSet_setOfPred.1 (measurableSet_C1.preimage measurable_fst.fst)
    have h2 : Measurable fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℝ × ℝ × ℕ × ℕ) => p.1.2 ∈ C2 :=
      measurableSet_setOfPred.1 (measurableSet_C2.preimage measurable_fst.snd)
    have h3 : Measurable fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℝ × ℝ × ℕ × ℕ) => 0 < p.2.1 :=
      measurableSet_setOfPred.1 (measurableSet_lt measurable_const measurable_snd.fst)
    have h4 : Measurable fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℝ × ℝ × ℕ × ℕ) => 0 < p.2.2.1 :=
      measurableSet_setOfPred.1 (measurableSet_lt measurable_const measurable_snd.snd.fst)
    have h5 : Measurable fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℝ × ℝ × ℕ × ℕ) =>
        (p.1.1, p.2) ∈ S :=
      measurableSet_setOfPred.1 (hSm.preimage (measurable_fst.fst.prodMk measurable_snd))
    have h6 : Measurable fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℝ × ℝ × ℕ × ℕ) =>
        (p.1, (p.2.1, p.2.2.1, p.2.2.2.1)) ∈ X :=
      measurableSet_setOfPred.1 (hXm.preimage (measurable_fst.prodMk
        (measurable_snd.fst.prodMk (measurable_snd.snd.fst.prodMk measurable_snd.snd.snd.fst))))
    exact measurableSet_setOfPred.2 (h1.imp (h2.imp (h3.imp (h4.imp (h5.imp h6)))))
  have e : GoodC γ = {q | ∀ θ, (q, θ) ∈ R} := by
    ext q
    simp only [mem_ofPred_eq, hRdef]
    constructor
    · rintro hq ⟨τ, a, i, n⟩ hC1 hC2 hτ ha hSq
      obtain ⟨x, hx, hxq⟩ := exists_of_mem_C1 hC1
      obtain ⟨y, hyq⟩ := exists_of_mem_C2 hC2
      have hsep : BackSepI (y, pathDrive (γ ^ 2) x) τ 0 a i := by
        rw [← hxq] at hSq
        exact ((hSs x hx τ a hτ ha i n).2 hSq)
      have hE : ExactC γ (y, pathDrive (γ ^ 2) x) τ a i :=
        hq x hx hxq y hyq τ a hτ ha i (backSupportI_of_backSepI hsep) hsep
      have := (hXs x hx y τ a hτ ha i hsep).2 hE
      rw [hxq, hyq] at this
      exact this
    · intro hq x hx hxq y hyq τ a hτ ha i _ hsep
      obtain ⟨δ, hδ, h0⟩ := hsep
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
      have hSD : SepD (pathDrive (γ ^ 2) x) τ a i (1 / ((n : ℝ) + 1)) :=
        measure_mono_null (Metric.thickening_mono hn.le _) h0
      have hmem := (hSs x hx τ a hτ ha i n).1 hSD
      rw [hxq] at hmem
      have hC1 : q.1 ∈ C1 := hxq ▸ mem_C1_of_continuous hx
      have hC2 : q.2 ∈ C2 := hyq ▸ mem_C2 y
      have hXq := hq (τ, a, i, n) hC1 hC2 hτ ha hmem
      have hq' : q = (codeP x, CoordsFull.coordsFull y) := Prod.ext hxq.symm hyq.symm
      rw [hq'] at hXq
      exact (hXs x hx y τ a hτ ha i ⟨δ, hδ, h0⟩).1 hXq
  rw [e]
  exact nullMeasurableSet_forall hRm ρ

end GC
end ASep
end QuantumZipper
