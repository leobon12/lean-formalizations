import QuantumZipper.Proofs.Zipper.B5VAssemble
import QuantumZipper.Proofs.Zipper.F1Side
import QuantumZipper.Proofs.Loewner.CaraR1

/-!
# UNIF-CLUSTER (D26): the left side image after two unzippings (deterministic)

For a continuous driver `W` with `W 0 = 0`, a horizon `T > 0` with `V = vrev W T` generating a
simple reverse hull, and times `u, s > 0` with `u + s ≤ T`, let `W_u r = W (u + max r 0) − W u`
be the driver of the configuration unzipped by `u` (`zipCapDown`), `t = T − u − s`,
`c = 0₋^V(T − u)`, `F = realRevMap V (T − u)` and `G = realRevMap V t`.

* `isForwardSol_of_isRealRevSol_rev`: a real reverse solution for a driver `V₁` with
  `V₁ r = W'(s − r) − W' s` on `[0,s]`, read backwards in time, is a forward solution for `W'`
  (converse of `B5.isRealRevSol_vrev_of_isForwardSol`);
* `re_fwdMap_shift_realRevMap`: for `y ∈ (0₋^V(T), c)`, `f^{W_u}_s (F y) = G y`: unzipping the
  picture at time `u` by `s` more is the real reverse flow read from the fully unzipped picture;
* **`sideImages_fst_shift_eq`**: `O⁻_s(W_u) = G c`, i.e. the left end of the segment unzipped from
  the configuration `C_u` in capacity time `s`, seen in the picture at time `u + s`, is the image
  of `0₋^V(T − u)`.

Own elementary proof (flow property and time reversal of the real Loewner ODE; Lawler,
*Conformally invariant processes in the plane*, §4.1, uses these facts without proof).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5 RealLine CaraR

/-- **Time reversal, converse direction.** -/
theorem isForwardSol_of_isRealRevSol_rev {W' V₁ : ℝ → ℝ} {s x : ℝ} {g : ℝ → ℝ} (hs : 0 ≤ s)
    (hW'0 : W' 0 = 0) (hV : ∀ r ∈ Icc 0 s, V₁ r = W' (s - r) - W' s)
    (hg : IsRealRevSol V₁ x s g) :
    IsForwardSol W' ((g s : ℝ) : ℂ) s (fun q => ((g (s - q) : ℝ) : ℂ)) := by
  have hmaps : MapsTo (fun q => s - q) (Icc 0 s) (Icc 0 s) := fun q hq =>
    ⟨by linarith [hq.2], by linarith [hq.1]⟩
  have hc : ContinuousOn (fun p => 2 / g p) (Icc 0 s) :=
    continuousOn_const.div hg.1 fun p hp => (hg.2 p hp).1
  refine ⟨Complex.continuous_ofReal.comp_continuousOn
    (hg.1.comp (continuous_const.sub continuous_id).continuousOn hmaps), fun q hq => ?_⟩
  have hsq := hmaps hq
  refine ⟨by show ((g (s - q) : ℝ) : ℂ) ≠ 0; exact_mod_cast (hg.2 _ hsq).1, ?_⟩
  have hI : ∫ p in (0 : ℝ)..q, (2 : ℂ) / ((g (s - p) : ℝ) : ℂ) =
      ((∫ p in (0 : ℝ)..q, 2 / g (s - p) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun p _ => ?_
    push_cast; rfl
  have hsub : ∫ p in (0 : ℝ)..q, 2 / g (s - p) = ∫ p in s - q..s, 2 / g p := by
    rw [intervalIntegral.integral_comp_sub_left (fun p => 2 / g p) s, sub_zero]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((hc.mono (uIcc_subset_Icc ⟨le_rfl, hs⟩ hsq)).intervalIntegrable (μ := volume))
    ((hc.mono (uIcc_subset_Icc hsq ⟨hs, le_rfl⟩)).intervalIntegrable (μ := volume))
  have e1 := (hg.2 _ hsq).2
  have e2 := (hg.2 s ⟨hs, le_rfl⟩).2
  have h1 := hV _ hsq
  have h2 := hV s ⟨hs, le_rfl⟩
  rw [show s - (s - q) = q by ring] at h1
  rw [sub_self, hW'0] at h2
  rw [hI, hsub]
  have key : g (s - q) = g s - W' q + ∫ p in s - q..s, 2 / g p := by
    rw [h1] at e1; rw [h2] at e2; linarith
  beta_reduce
  rw [key]; push_cast; ring

variable {W : ℝ → ℝ} {T u s : ℝ}

/-- The driver of `V = vrev W T` restarted at `t = T − u − s` is the reversal of `W_u` on `[0,s]`. -/
theorem vrev_restart_eq (hu : 0 ≤ u) (hs : 0 ≤ s) (hus : u + s ≤ T) {r : ℝ} (hr : r ∈ Icc 0 s) :
    vrev W T (T - u - s + r) - vrev W T (T - u - s) =
      (W (u + max (s - r) 0) - W u) - (W (u + max s 0) - W u) := by
  rw [vrev_of_mem ⟨by linarith [hr.1], by linarith [hr.2]⟩,
    vrev_of_mem ⟨by linarith, by linarith⟩, max_eq_left (by linarith [hr.2]), max_eq_left hs]
  ring_nf

section Main

variable (hW : Continuous W) (hT : 0 < T) (hK : IsSimpleCurveHull (revHull (vrev W T) T))
  (hKu : IsSimpleCurveHull (revHull (vrev W u) u)) (hu : 0 < u) (hs : 0 < s) (hus : u + s ≤ T)
include hW hT hK hu hs hus

/-- A point of `(0₋^V(T), 0₋^V(T − u))` has a real reverse solution on `[0, T − u]`. -/
theorem exists_isRealRevSol_of_mem {y : ℝ}
    (hy : y ∈ Ioo (zeroMinus (vrev W T) T) (zeroMinus (vrev W T) (T - u))) :
    ∃ g, IsRealRevSol (vrev W T) y (T - u) g := by
  obtain ⟨τ, hτ1, -, he, -⟩ := hitTime_of_mem_Ioo (continuous_vrev hW T) (vrev_zero hT.le) hT hK hu
    (by linarith : (0 : ℝ) ≤ T - u) (by ring) hy
  refine exists_isRealRevSol_of_lt_realHitTime ?_
  rw [he]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hτ1

/-- **Unzipping the picture at time `u` by `s` more**: for `y ∈ (0₋^V(T), 0₋^V(T − u))`,
`f^{W_u}_s (F y) = G y`. -/
theorem re_fwdMap_shift_realRevMap {y : ℝ}
    (hy : y ∈ Ioo (zeroMinus (vrev W T) T) (zeroMinus (vrev W T) (T - u))) :
    (fwdMap (fun r => W (u + max r 0) - W u) s (realRevMap (vrev W T) (T - u) y)).re =
      realRevMap (vrev W T) (T - u - s) y := by
  have hVc := continuous_vrev hW T
  obtain ⟨g, hg⟩ := exists_isRealRevSol_of_mem hW hT hK hu hs hus hy
  have ht : (0 : ℝ) ≤ T - u - s := by linarith
  rw [realRevMap_eq hVc hg (by linarith) le_rfl, realRevMap_eq hVc hg ht (by linarith)]
  have hg' : IsRealRevSol (vrev W T) y (T - u - s + s) g := by
    rwa [show T - u - s + s = T - u by ring]
  have hsh := isRealRevSol_shift (V' := fun r => vrev W T (T - u - s + r) - vrev W T (T - u - s))
    ht (fun r _ => rfl) hs.le hg'
  have hf := isForwardSol_of_isRealRevSol_rev (W' := fun r => W (u + max r 0) - W u) hs.le
    (by simp) (fun r hr => vrev_restart_eq hu.le hs.le hus hr) hsh
  rw [show T - u - s + s = T - u by ring] at hf
  rw [F1.fwdMap_eq_of_isForwardSol hf ⟨hs.le, le_rfl⟩]
  simp

include hKu in
/-- **The left side image of `C_u` unzipped by `s`**: `O⁻_s(W_u) = G (0₋^V(T − u))`. -/
theorem sideImages_fst_shift_eq :
    (sideImages (fun r => W (u + max r 0) - W u) s).1 =
      realRevMap (vrev W T) (T - u - s) (zeroMinus (vrev W T) (T - u)) := by
  set V := vrev W T with hVdef
  have hVc : Continuous V := continuous_vrev hW T
  have hV0 : V 0 = 0 := vrev_zero hT.le
  set F := realRevMap V (T - u) with hF
  set G := realRevMap V (T - u - s) with hG
  set a := zeroMinus V T
  set c := zeroMinus V (T - u) with hc
  have hVuc : Continuous (vrev W u) := continuous_vrev hW u
  have hshift : ∀ r, 0 ≤ r → vrev W u r = V (T - u + r) - V (T - u) :=
    fun r hr => (vrev_shift hu.le (by linarith) hr).symm
  obtain ⟨hac, hmono, -, hC⟩ := realRevMap_endpoints hVc hV0 hT hK hVuc (vrev_zero hu.le) hu hKu
    (by linarith) (by ring) hshift
  have hanti := strictAntiOn_zeroMinus hVc hV0 hT hK
  -- `F` is continuous and negative on `(a,c)`
  have hFc : ∀ y ∈ Ioo a c, ContinuousAt F y := fun y hy => by
    obtain ⟨g, hg⟩ := exists_isRealRevSol_of_mem hW hT hK hu hs hus hy
    exact continuousAt_realRevMap hVc (by linarith) (not_mem_swallowedSet_iff.2 ⟨g, hg⟩)
  have hc0 : c ≤ 0 := by
    rw [hc, ← zeroMinus_zero_time hVc hV0]
    exact hanti.antitoneOn ⟨le_rfl, hT.le⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have hFneg : ∀ y ∈ Ioo a c, F y < 0 := fun y hy => by
    obtain ⟨g, hg⟩ := exists_isRealRevSol_of_mem hW hT hK hu hs hus hy
    have hl : E1.IsLive V (T - u) y := by
      obtain ⟨τ, hτ1, -, he, -⟩ := hitTime_of_mem_Ioo hVc hV0 hT hK hu
        (by linarith : (0 : ℝ) ≤ T - u) (by ring) hy
      show ENNReal.ofReal (T - u) < realHitTime V y
      rw [he]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hτ1
    exact E1.realRevMap_neg hVc hV0 (by linarith) (hy.2.trans_le hc0) hl
  -- `G` is continuous at `c`
  have hGc : ContinuousAt G c := by
    obtain ⟨he, hτ, hz⟩ := hitTime_spec hVc hV0 hT hK
      ⟨hanti ⟨by linarith, by linarith⟩ ⟨hT.le, le_rfl⟩ (by linarith), hc0⟩
    have hτc : (realHitTime V c).toReal = T - u :=
      hanti.injOn hτ ⟨by linarith, by linarith⟩ hz
    have hlt : ENNReal.ofReal (T - u - s) < realHitTime V c := by
      rw [he, hτc]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    obtain ⟨g, hg⟩ := exists_isRealRevSol_of_lt_realHitTime hlt
    exact continuousAt_realRevMap hVc (by linarith) (not_mem_swallowedSet_iff.2 ⟨g, hg⟩)
  refine Tendsto.limUnder_eq ?_
  rw [(Metric.nhds_basis_ball).tendsto_right_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.1 hGc ε hε
  set m := max (c - δ / 2) ((a + c) / 2) with hm
  have hmI : m ∈ Ioo a c := ⟨lt_max_of_lt_right (by linarith),
    max_lt (by linarith) (by linarith)⟩
  filter_upwards [Ioo_mem_nhdsLT (hFneg m hmI)] with x hx
  -- find `y ∈ (m, c)` with `F y = x`
  have hev : ∀ᶠ y in 𝓝[<] c, x < F y ∧ y ∈ Ioo m c :=
    (hC.eventually (lt_mem_nhds hx.2)).and (Ioo_mem_nhdsLT hmI.2)
  obtain ⟨y₁, hy₁, hy₁m⟩ := hev.exists
  have hsub : Icc m y₁ ⊆ Ioo a c := fun z hz => ⟨hmI.1.trans_le hz.1, hz.2.trans_lt hy₁m.2⟩
  have hcont : ContinuousOn F (Icc m y₁) := fun z hz => (hFc z (hsub hz)).continuousWithinAt
  obtain ⟨y, hyI, hyx⟩ := intermediate_value_Icc hy₁m.1.le hcont ⟨hx.1.le, hy₁.le⟩
  have hym : m < y := by
    rcases hyI.1.eq_or_lt with h | h
    · rw [← h] at hyx; exact absurd hyx (ne_of_lt hx.1)
    · exact h
  have hyI' : y ∈ Ioo a c := ⟨hmI.1.trans hym, hyI.2.trans_lt hy₁m.2⟩
  show (fwdMap (fun r => W (u + max r 0) - W u) s x).re ∈ Metric.ball (G c) ε
  rw [← hyx, re_fwdMap_shift_realRevMap hW hT hK hu hs hus hyI']
  refine hδG ?_
  rw [Real.dist_eq, abs_lt]
  constructor
  · have : c - δ / 2 ≤ m := le_max_left _ _
    linarith
  · linarith [hyI'.2]

end Main

end RegUnif
end QuantumZipper
