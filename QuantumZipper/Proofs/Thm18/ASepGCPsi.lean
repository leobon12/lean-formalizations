import QuantumZipper.Proofs.Thm18.ASepGCSkel
import QuantumZipper.Proofs.Thm18.G4CMeas4Fld
import QuantumZipper.Proofs.Thm18.G4WeldRem
import QuantumZipper.Proofs.Thm18.G4CMeasProj
import QuantumZipper.Proofs.Loewner.ReverseHolo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP-GC, part 2: the re-zipping map `ψ = revMapInv (backDrv W τ 0 a)` is Borel in the code

* `invOn F w`: the unique `z ∈ ℍ` with `F z = w`, junk `0` otherwise (`revMapInv W t` is
  `invOn (revMap W t)` by definition).
* `measurable_invOn`: for a jointly measurable family `F p` injective on `ℍ` over a standard Borel
  parameter space, `(p, w) ↦ invOn (F p) w` is measurable (Lusin–Souslin: the graph is a
  measurable partial graph, its projection is Borel and it has a measurable selector; Kechris,
  *Classical Descriptive Set Theory*, Thm 15.1, Cor 15.2, as in `Thm14Determination`).
* `kcode κ c`: the dyadic code of `√κ (x − x 0)` read from the path code `c = codeP x`;
  `wg_kcode`: for continuous `x`, the gated driver of this code is `pathDrive κ x − pathDrive κ x 0`.
* **`psiInv`** and **`measurable_psiInv`**, **`revMapInv_backDrv_eq_psiInv`**: for continuous
  `x`, `τ ≥ 0`, `a > 0`,
  `revMapInv (backDrv W τ 0 a) w = psiInv (kcode κ (codeP x), τ, a) w` (`W = pathDrive κ x`), and
  `(c, τ, a, w) ↦ psiInv (kcode κ c, τ, a) w` is Borel.

Loewner scaling (`Thm18Asm.revMap_revDrv`), injectivity of the reverse flow
(`injOn_revMap`), the code reverse flow `G4Core.Psi` (Carathéodory measurability,
`G4Core.measurable_Psi`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Function
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ASep
namespace GC

open Thm18Asm Thm18Asm.G4Core

open Classical in
/-- The inverse on `ℍ` of a map (junk `0`). -/
def invOn (F : ℂ → ℂ) (w : ℂ) : ℂ := if h : ∃! z, z ∈ H ∧ F z = w then h.choose else 0

theorem revMapInv_eq_invOn (W : ℝ → ℝ) (t : ℝ) : revMapInv W t = invOn (revMap W t) := by
  funext w; unfold revMapInv invOn; congr

theorem invOn_eq_of_mem {F : ℂ → ℂ} (hF : InjOn F H) {z w : ℂ} (hz : z ∈ H) (hw : F z = w) :
    invOn F w = z := by
  have h : ∃! z, z ∈ H ∧ F z = w :=
    ⟨z, ⟨hz, hw⟩, fun z' hz' => hF hz'.1 hz (hz'.2.trans hw.symm)⟩
  unfold invOn
  rw [dif_pos h]
  exact h.unique h.choose_spec.1 ⟨hz, hw⟩

theorem invOn_eq_zero {F : ℂ → ℂ} {w : ℂ} (h : ∀ z ∈ H, F z ≠ w) : invOn F w = 0 := by
  unfold invOn
  rw [dif_neg]
  rintro ⟨z, hz, -⟩
  exact h z hz.1 hz.2

theorem invOn_congr {F G : ℂ → ℂ} (hF : InjOn F H) (hFG : ∀ z ∈ H, F z = G z) :
    invOn F = invOn G := by
  have hG : InjOn G H := fun z hz z' hz' h => hF hz hz' (by rw [hFG z hz, hFG z' hz', h])
  funext w
  by_cases h : ∃ z ∈ H, F z = w
  · obtain ⟨z, hz, hw⟩ := h
    rw [invOn_eq_of_mem hF hz hw, invOn_eq_of_mem hG hz (by rw [← hFG z hz, hw])]
  · push_neg at h
    rw [invOn_eq_zero h, invOn_eq_zero fun z hz => by rw [← hFG z hz]; exact h z hz]

/-- **Measurability of the inverse of an injective measurable family.** -/
theorem measurable_invOn {P : Type*} [MeasurableSpace P] [StandardBorelSpace P]
    (F : P → ℂ → ℂ) (hF : Measurable fun q : P × ℂ => F q.1 q.2) (hinj : ∀ p, InjOn (F p) H) :
    Measurable fun q : P × ℂ => invOn (F q.1) q.2 := by
  classical
  set G : Set ((P × ℂ) × ℂ) := {s | s.2 ∈ H ∧ F s.1.1 s.2 = s.1.2} with hGdef
  have hHm : MeasurableSet H := (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hGm : MeasurableSet G :=
    (hHm.preimage measurable_snd).inter (measurableSet_eq_fun
      (hF.comp (measurable_fst.fst.prodMk measurable_snd)) measurable_fst.snd)
  have hGp : Thm14Determination.IsPartialGraph G := by
    rintro ⟨p, w⟩ z z' hz hz'
    exact hinj p hz.1 hz'.1 (hz.2.trans hz'.2.symm)
  obtain ⟨Fs, hFs, hFsG⟩ := Thm14Determination.exists_measurable_of_partialGraph hGm hGp
  have hD : MeasurableSet (Prod.fst '' G) := measurableSet_image_fst_of_partialGraph hGm hGp
  have e : (fun q : P × ℂ => invOn (F q.1) q.2) = (Prod.fst '' G).piecewise Fs 0 := by
    funext q
    by_cases hq : q ∈ Prod.fst '' G
    · rw [piecewise_eq_of_mem _ _ _ hq]
      obtain ⟨⟨q', z⟩, hz, rfl⟩ := hq
      rw [invOn_eq_of_mem (hinj _) hz.1 hz.2]
      exact (hFsG _ hz).symm
    · rw [piecewise_eq_of_notMem _ _ _ hq, invOn_eq_zero]
      · rfl
      intro z hz hzq
      exact hq ⟨(q, z), ⟨hz, hzq⟩, rfl⟩
  rw [e]
  exact hFs.piecewise hD measurable_const

/-! ## The dyadic driver code of `√κ (x − x 0)` -/

theorem exists_qs_eq_dyNN (n : ℕ) : ∃ m, qs m = dyNN n := by
  obtain ⟨m, hm⟩ := exists_qs_eq_dy n.unpair.1 n.unpair.2
  refine ⟨m, hm.trans ?_⟩
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (F1.dy_nonneg _ _)]
  simp [dyNN, F1.dy]

/-- The code index of the dyadic time `dyNN n`. -/
def mIdx (n : ℕ) : ℕ := (exists_qs_eq_dyNN n).choose

/-- The code index of the time `0`. -/
def m0 : ℕ := (exists_qs_eq_dy 0 0).choose

theorem qs_m0 : qs m0 = 0 := by
  rw [m0, (exists_qs_eq_dy 0 0).choose_spec]; simp [F1.dy]

/-- The dyadic code of `√κ (x − x 0)` read from the path code of `x`. -/
def kcode (κ : ℝ) (c : ℕ → ℝ) : ℕ → ℝ := fun n => Real.sqrt κ * (c (mIdx n) - c m0)

theorem measurable_kcode (κ : ℝ) : Measurable (kcode κ) :=
  measurable_pi_iff.2 fun n => measurable_const.mul
    ((measurable_pi_apply _).sub (measurable_pi_apply _))

theorem kcode_codeP (κ : ℝ) (x : ℝ≥0 → ℝ) :
    kcode κ (codeP x) = fun n => Real.sqrt κ * (x (dyNN n) - x 0) := by
  funext n
  simp only [kcode, codeP, (exists_qs_eq_dyNN n).choose_spec, mIdx, qs_m0]

theorem wread_dy (p : ℝ≥0 → ℝ) : wread (fun n => p (dyNN n)) = F1.readDrv p := by
  funext t
  rw [F1.readDrv_eq_limUnder]
  unfold wread
  congr 1
  funext n
  simp only [F1.dyv, F1.dy, dyNN, Nat.unpair_pair]
  refine congrArg p (NNReal.eq ?_)
  rw [NNReal.coe_div, Real.coe_toNNReal _ (by positivity)]
  simp

/-- For a continuous path `p` with `p 0 = 0`, the gated driver of its dyadic code is `p ∘ (·)⁺`. -/
theorem wg_dy {p : ℝ≥0 → ℝ} (hp : Continuous p) (h0 : p 0 = 0) :
    wg (fun n => p (dyNN n)) = fun s => p s.toNNReal := by
  have hW : Continuous fun s : ℝ => p s.toNNReal := hp.comp continuous_real_toNNReal
  have hrdp : F1.readDrv p = fun s => p s.toNNReal := by
    have e := F1.readDrv_eq hW (fun s => by simp only [Real.toNNReal_coe])
    have e2 : (fun t : ℝ≥0 => p (t : ℝ).toNNReal) = p := funext fun t => by simp
    rwa [e2] at e
  have hpa : pa (fun n => p (dyNN n)) = p := by
    funext r; simp only [pa, wread_dy, hrdp, Real.toNNReal_coe]
  have hg : GoodDrv (fun n => p (dyNN n)) := by
    refine ⟨?_, ?_⟩
    · rw [hpa]; exact F1.dyUC_of_continuous hp
    · rw [hpa, hrdp]; simpa using h0
  unfold wg
  rw [if_pos hg, hpa, hrdp]

theorem wg_kcode {κ : ℝ} {x : ℝ≥0 → ℝ} (hx : Continuous x) :
    wg (kcode κ (codeP x)) = fun s => pathDrive κ x s - pathDrive κ x 0 := by
  rw [kcode_codeP, wg_dy (p := fun r => Real.sqrt κ * (x r - x 0)) (by fun_prop) (by simp)]
  funext s
  simp only [pathDrive, Real.toNNReal_zero]
  ring

theorem revDrv_sub_const (W : ℝ → ℝ) (c τ a : ℝ) :
    revDrv (fun s => W s - c) τ a = revDrv W τ a := by
  simp only [revDrv, sub_sub_sub_cancel_right]

/-! ## The code re-zipping map -/

/-- The code reverse flow of `revDrv (wg k) τ a` on `ℍ` (the identity for bad parameters). -/
def psiF (q : (ℕ → ℝ) × ℝ × ℝ) (y : ℂ) : ℂ :=
  if 0 ≤ q.2.1 ∧ 0 < q.2.2 then Psi q.1 q.2.1 ((q.2.2 : ℂ) * y) / (q.2.2 : ℂ) else y

theorem measurable_psiF : Measurable fun s : ((ℕ → ℝ) × ℝ × ℝ) × ℂ => psiF s.1 s.2 := by
  refine Measurable.ite ?_ ?_ measurable_snd
  · exact (measurableSet_le measurable_const measurable_fst.snd.fst).inter
      (measurableSet_lt measurable_const measurable_fst.snd.snd)
  · have h1 : Measurable fun s : ((ℕ → ℝ) × ℝ × ℝ) × ℂ =>
        ((s.1.1, s.1.2.1), (s.1.2.2 : ℂ) * s.2) :=
      (measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk
        ((Complex.measurable_ofReal.comp measurable_fst.snd.snd).mul measurable_snd)
    exact (measurable_Psi.comp h1).div (Complex.measurable_ofReal.comp measurable_fst.snd.snd)

theorem psiF_eq_revMap {k : ℕ → ℝ} {τ a : ℝ} (hτ : 0 ≤ τ) (ha : 0 < a) {y : ℂ} (hy : y ∈ H) :
    psiF (k, τ, a) y = revMap (revDrv (wg k) τ a).2 (revDrv (wg k) τ a).1 y := by
  have hay : (a : ℂ) * y ∈ H := by
    show 0 < ((a : ℂ) * y).im
    have : 0 < y.im := hy
    simpa using mul_pos ha this
  simp only [psiF, if_pos (And.intro hτ ha)]
  rw [revMap_revDrv (continuous_wg k) hτ ha hy, Psi, selC_of_mem hay, psiR, max_eq_left hτ]

theorem injOn_psiF (q : (ℕ → ℝ) × ℝ × ℝ) : InjOn (psiF q) H := by
  by_cases hq : 0 ≤ q.2.1 ∧ 0 < q.2.2
  · intro y hy y' hy' h
    obtain ⟨k, τ, a⟩ := q
    rw [psiF_eq_revMap hq.1 hq.2 hy, psiF_eq_revMap hq.1 hq.2 hy'] at h
    have hVc : Continuous (revDrv (wg k) τ a).2 := by
      simp only [revDrv]; have := continuous_wg k; fun_prop
    have hT : 0 ≤ (revDrv (wg k) τ a).1 := by simp only [revDrv]; exact div_nonneg hq.1 (sq_nonneg a)
    exact injOn_revMap _ hVc hT hy hy' h
  · intro y _ y' _ h
    simpa only [psiF, if_neg hq] using h

/-- The code re-zipping map. -/
@[irreducible] def psiInv (q : (ℕ → ℝ) × ℝ × ℝ) (w : ℂ) : ℂ := invOn (psiF q) w

theorem psiInv_def (q : (ℕ → ℝ) × ℝ × ℝ) : psiInv q = invOn (psiF q) := by
  funext w; unfold psiInv; rfl

theorem measurable_psiInv : Measurable fun s : ((ℕ → ℝ) × ℝ × ℝ) × ℂ => psiInv s.1 s.2 := by
  simp only [psiInv_def]
  exact measurable_invOn psiF measurable_psiF injOn_psiF

/-- **The re-zipping map `ψ` read from the path code.** -/
theorem revMapInv_backDrv_eq_psiInv (κ : ℝ) {x : ℝ≥0 → ℝ} (hx : Continuous x) {τ a : ℝ}
    (hτ : 0 ≤ τ) (ha : 0 < a) :
    revMapInv (backDrv (pathDrive κ x) τ 0 a).2 (backDrv (pathDrive κ x) τ 0 a).1 =
      psiInv (kcode κ (codeP x), τ, a) := by
  rw [backDrv_zero, ← revDrv_sub_const (pathDrive κ x) (pathDrive κ x 0), ← wg_kcode hx,
    revMapInv_eq_invOn]
  rw [psiInv_def]
  exact (invOn_congr (injOn_psiF _) fun y hy => psiF_eq_revMap hτ ha hy).symm

/-- `(c, τ, a, w) ↦ ψ` is Borel. -/
theorem measurable_psiInv_code (κ : ℝ) :
    Measurable fun s : ((ℕ → ℝ) × ℝ × ℝ) × ℂ => psiInv (kcode κ s.1.1, s.1.2) s.2 :=
  by
  have h1 : Measurable fun s : ((ℕ → ℝ) × ℝ × ℝ) × ℂ => ((kcode κ s.1.1, s.1.2), s.2) :=
    (((measurable_kcode κ).comp measurable_fst.fst).prodMk measurable_fst.snd).prodMk
      measurable_snd
  exact Measurable.comp (g := fun s : ((ℕ → ℝ) × ℝ × ℝ) × ℂ => psiInv s.1 s.2)
    (f := fun s : ((ℕ → ℝ) × ℝ × ℝ) × ℂ => ((kcode κ s.1.1, s.1.2), s.2)) measurable_psiInv h1

end GC
end ASep
end QuantumZipper
