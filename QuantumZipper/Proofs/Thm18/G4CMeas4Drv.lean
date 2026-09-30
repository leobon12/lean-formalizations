import QuantumZipper.Proofs.Thm18.G4CMeas3Gate
import QuantumZipper.Proofs.Zipper.E5Asm2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# JOINT-LEN-READER, part D1: the driver read from the code, and the inverse map jointly in time

* `wread a`: the driver read from the dyadic code `a` (`wread (lcode d).2 = F1.readDrv d.2`).
* `wg a`: the gated driver (continuous, starting at `0`, for every code), equal to
  `F1.readDrv d.2` for data with a good driver (`wg_lcode`).
* `measurable_psiR_uncurry`: `(t, z, a) ↦ revMap (vrev (wg a) t⁺) t⁺ z` is jointly measurable on
  `ℝ × ℍ × code` (Carathéodory: continuous in `(t, z)` by `RegUnif.continuousOn_revMap_family`,
  measurable in the code by the Lipschitz dependence on the path, `E5.continuous_revMap_vrPath`).
* `fwdMapInv_eq_psiR`: for `t ≥ 0`, `z ∈ ℍ`, this is `fwdMapInv (wg a) t z`.

Own elementary argument (Carathéodory's joint measurability, mathlib
`measurable_uncurry_of_continuous_of_measurable`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

/-! ## The driver read from the code -/

/-- The driver read from the dyadic code (same limit as `F1.readDrv`). -/
def wread (a : ℕ → ℝ) (t : ℝ) : ℝ := limUnder atTop fun n => a (Nat.pair n (F1.rdx n t))

theorem wread_lcode (d : E6.FullData) : wread (lcode d).2 = F1.readDrv d.2 := by
  funext t
  rw [F1.readDrv_eq_limUnder]
  unfold wread lcode
  congr 1
  funext n
  simp only [F1.dyv, F1.dy, dyNN, Nat.unpair_pair]
  refine congrArg d.2 (NNReal.eq ?_)
  rw [NNReal.coe_div, Real.coe_toNNReal _ (by positivity)]
  simp

theorem measurable_wread_apply (t : ℝ) : Measurable fun a : ℕ → ℝ => wread a t :=
  (StronglyMeasurable.limUnder fun n =>
    (measurable_pi_apply (Nat.pair n (F1.rdx n t))).stronglyMeasurable).measurable

/-- The code driver as a path on `ℝ≥0`. -/
def pa (a : ℕ → ℝ) : ℝ≥0 → ℝ := fun r => wread a r

theorem measurable_pa : Measurable pa :=
  measurable_pi_iff.2 fun r => measurable_wread_apply r

/-- Good code drivers: the continuity certificate and start at `0`. -/
def GoodDrv (a : ℕ → ℝ) : Prop := F1.DyUC (pa a) ∧ F1.readDrv (pa a) 0 = 0

theorem measurableSet_goodDrv : MeasurableSet {a : ℕ → ℝ | GoodDrv a} := by
  show MeasurableSet ({a | F1.DyUC (pa a)} ∩ {a | F1.readDrv (pa a) 0 = 0})
  exact (F1.measurableSet_dyUC.preimage measurable_pa).inter
    (measurableSet_eq_fun ((F1.measurable_readDrv_apply 0).comp measurable_pa) measurable_const)

open Classical in
/-- **The gated driver**: continuous and started at `0` for every code. -/
def wg (a : ℕ → ℝ) : ℝ → ℝ := if GoodDrv a then F1.readDrv (pa a) else fun _ => 0

theorem continuous_wg (a : ℕ → ℝ) : Continuous (wg a) := by
  unfold wg
  split_ifs with h
  · exact F1.continuous_readDrv_of_dyUC h.1
  · exact continuous_const

theorem wg_zero (a : ℕ → ℝ) : wg a 0 = 0 := by
  unfold wg
  split_ifs with h
  · exact h.2
  · rfl

theorem measurable_wg_uncurry : Measurable fun q : (ℕ → ℝ) × ℝ => wg q.1 q.2 := by
  classical
  have e : (fun q : (ℕ → ℝ) × ℝ => wg q.1 q.2) =
      fun q => if GoodDrv q.1 then F1.readDrv (pa q.1) q.2 else 0 := by
    funext q
    unfold wg
    split_ifs <;> rfl
  rw [e]
  refine Measurable.ite (measurableSet_goodDrv.preimage measurable_fst) ?_ measurable_const
  have h1 : Measurable fun q : (ℕ → ℝ) × ℝ => ((fun r : ℝ => pa q.1 r.toNNReal), q.2) :=
    (measurable_pi_iff.2 fun r => (measurable_pi_apply _).comp (measurable_pa.comp measurable_fst)).prodMk
      measurable_snd
  exact F1.B4d.measurable_pathExt.comp h1

theorem measurable_wg_apply (t : ℝ) : Measurable fun a : ℕ → ℝ => wg a t :=
  measurable_wg_uncurry.comp (f := fun a : ℕ → ℝ => (a, t)) (measurable_id.prodMk measurable_const)

theorem rdx_toNNReal (n : ℕ) (s : ℝ) : F1.rdx n s = F1.rdx n (s.toNNReal : ℝ) := by
  rcases le_or_gt 0 s with h | h
  · rw [Real.coe_toNNReal _ h]
  · rw [Real.toNNReal_of_nonpos h.le]
    simp only [F1.rdx, NNReal.coe_zero, mul_zero, Int.floor_zero, Int.toNat_zero]
    exact Int.toNat_eq_zero.2 (Int.floor_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) h.le))

theorem wg_lcode {d : E6.FullData} (hp : F1.PathGoodAll d.2) : wg (lcode d).2 = F1.readDrv d.2 := by
  have hc := F1.continuous_readDrv_of_dyUC hp.1
  have hpa : pa (lcode d).2 = fun r : ℝ≥0 => F1.readDrv d.2 r := by
    funext r; simp only [pa, wread_lcode]
  have hW0 : ∀ s : ℝ, F1.readDrv d.2 s = F1.readDrv d.2 (s.toNNReal : ℝ) := by
    intro s
    rw [F1.readDrv_eq_limUnder, F1.readDrv_eq_limUnder]
    simp only [← rdx_toNNReal]
  have hrd : F1.readDrv (pa (lcode d).2) = F1.readDrv d.2 := by
    rw [hpa]; exact F1.readDrv_eq hc hW0
  have hg : GoodDrv (lcode d).2 := by
    refine ⟨?_, by rw [hrd]; exact hp.2.1⟩
    rw [hpa]; exact F1.dyUC_of_continuous (hc.comp NNReal.continuous_coe)
  unfold wg
  rw [if_pos hg, hrd]

/-! ## The inverse map, jointly in time -/

/-- The inverse forward map of the gated driver at time `t⁺`, through the reverse flow. -/
def psiR (a : ℕ → ℝ) (t : ℝ) (z : ℂ) : ℂ := revMap (B2.vrev (wg a) (max t 0)) (max t 0) z

/-- The code driver on `[0,T]` as a continuous path. -/
def fPath (T : ℝ) (a : ℕ → ℝ) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun u => wg a u, (continuous_wg a).comp continuous_subtype_val⟩

theorem measurable_fPath (T : ℝ) : Measurable (fPath T) :=
  ContinuousMap.measurable_iff_eval.2 fun u => measurable_wg_apply u

theorem vrPath_fPath {T : ℝ} (hT : 0 ≤ T) (a : ℕ → ℝ) :
    E5.vrPath 1 T hT (fPath T a) = B2.vrev (wg a) T := by
  funext s
  have hm : T - min (max s 0) T ∈ Icc (0 : ℝ) T :=
    ⟨sub_nonneg.2 (min_le_right _ _), sub_le_self _ (le_min (le_max_right _ _) hT)⟩
  simp only [E5.vrPath, fPath, ContinuousMap.coe_mk, projIcc_of_mem hT hm,
    projIcc_of_mem hT ⟨hT, le_rfl⟩, Real.sqrt_one, one_mul, B2.vrev]

theorem measurable_psiR_apply {t : ℝ} {z : ℂ} (hz : 0 < z.im) :
    Measurable fun a : ℕ → ℝ => psiR a t z := by
  have hT : (0 : ℝ) ≤ max t 0 := le_max_right _ _
  have e : (fun a : ℕ → ℝ => psiR a t z) =
      (fun f => revMap (E5.vrPath 1 (max t 0) hT f) (max t 0) z) ∘ fPath (max t 0) := by
    funext a
    simp only [Function.comp, psiR, vrPath_fPath hT]
  rw [e]
  exact (E5.continuous_revMap_vrPath 1 (max t 0) hT hT hz).measurable.comp (measurable_fPath _)

theorem measurable_psiR_uncurry :
    Measurable fun p : (ℝ × {z : ℂ // 0 < z.im}) × (ℕ → ℝ) => psiR p.2 p.1.1 p.1.2.1 := by
  refine measurable_uncurry_of_continuous_of_measurable
    (u := fun (i : ℝ × {z : ℂ // 0 < z.im}) (a : ℕ → ℝ) => psiR a i.1 i.2.1)
    (fun a => ?_) (fun i => measurable_psiR_apply i.2.2)
  have hV : Continuous fun p : ℝ × ℝ => B2.vrev (wg a) p.1 p.2 :=
    RegUnif.continuous_vrev_joint (continuous_wg a)
  have hc := RegUnif.continuousOn_revMap_family (V := fun τ s => B2.vrev (wg a) τ s) hV
  exact hc.comp_continuous
    (f := fun i : ℝ × {z : ℂ // 0 < z.im} => (max i.1 0, max i.1 0, i.2.1))
    (by fun_prop) fun i => ⟨le_max_right _ _, i.2.2⟩

/-- **The inverse forward map is the reverse flow of the reversed driver.** -/
theorem fwdMapInv_eq_psiR (a : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H) :
    fwdMapInv (wg a) t z = psiR a t z := by
  rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev _ (continuous_wg a) (wg_zero a) ht hz, psiR,
    max_eq_left ht]
  refine ReverseFlow.revMap_congr_drive z fun r hr => ?_
  simp only [B2.vrev, max_eq_left hr.1, min_eq_left hr.2]

end G4Core
end Thm18Asm
end QuantumZipper
