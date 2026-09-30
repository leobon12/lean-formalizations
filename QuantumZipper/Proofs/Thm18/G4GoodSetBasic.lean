import QuantumZipper.Proofs.Thm18.G4Read2Main
import QuantumZipper.Proofs.Thm18.G4WeldHull

/-!
# Theorem 1.8, node G4: tools for a Borel good set at the random unzipping time

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1). Task
G4-GOODSET.

* `exists_compacts_ae`: a random element of a Polish space lying a.s. in a Borel set `G` lies
  a.s. in a countable union of compact subsets of `G` (tightness of finite measures on Polish
  spaces, mathlib `instInnerRegularOfIsCompletelyPseudoMetrizableSpace`; Kechris, *Classical
  Descriptive Set Theory*, Thm 17.11).
* `aemeasurable_pathC_drive`: the restriction of a Brownian driver to `[0,T]` is a.e.-measurable
  (continuous modification, `CharFun.exists_good_version`).
* `gsPath`, `continuous_gsPath`: the continuous map `(V, t, r) ↦ (u ↦ r (V(n−t+tu) − V(n−t)))`
  from `C([0,n], ℝ) × ℝ²` to `C([0,1], ℝ)`; for `V` the time reversal of `W` at `n` and
  `r = t^{-1/2}` it is the rescaled time reversal `u ↦ (W(t(1−u)) − W t)/√t` of `W` at `t`.
* `goodP_gsMap`: if `V` is a good driver on `[0,n]` (`Thm14GoodDriverSet.GoodDriver`, the
  fixed-time good set of Theorem 1.4), then for **every** `t ∈ (0,n]`, `r √t = 1` and `T > 0`
  the pair `(gsPath (V,t,r), T)` is good (`GoodP`): the hull is an initial arc of the simple
  chord of `V` (Loewner scaling, `isSimpleCurveHull_revDrv`) and its doubling is a closed subset
  of a dilate of the removable doubled hull at time `n` (`isConformallyRemovable_mono`, `_mul`).

**Own elementary argument** (the deterministic steps follow the proof of `ae_remHull_revDrv`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex TopologicalSpace
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm

open Thm14WeldingData Thm14GoodDriverSet

/-! ## Tightness: a.s. membership in a countable union of compacts -/

/-- A random element of a Polish space lying a.s. in a Borel set `G` lies a.s. in a countable
union of compact subsets of `G`. -/
theorem exists_compacts_ae {α : Type*} [TopologicalSpace α] [T2Space α]
    [SecondCountableTopology α] [IsCompletelyPseudoMetrizableSpace α] [MeasurableSpace α]
    [BorelSpace α] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → α} (hX : AEMeasurable X P) {G : Set α} (hG : MeasurableSet G)
    (hae : ∀ᵐ ω ∂P, X ω ∈ G) :
    ∃ K : ℕ → Set α, (∀ m, IsCompact (K m)) ∧ (∀ m, K m ⊆ G) ∧
      ∀ᵐ ω ∂P, ∃ m, X ω ∈ K m := by
  set μ := P.map X
  have hK : ∀ m : ℕ, ∃ K, K ⊆ G ∧ IsCompact K ∧ μ (G \ K) < ((m : ℝ≥0∞))⁻¹ := fun m =>
    hG.exists_isCompact_sdiff_lt (measure_ne_top μ G)
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top m))
  choose K hKG hKc hKμ using hK
  have hKm : MeasurableSet (⋃ m, K m) :=
    MeasurableSet.iUnion fun m => (hKc m).isClosed.measurableSet
  have h0 : μ (G \ ⋃ m, K m) = 0 := by
    by_contra hne
    obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt hne
    exact absurd ((measure_mono (sdiff_subset_sdiff_right (subset_iUnion K m))).trans_lt (hKμ m))
      (not_lt.2 hm.le)
  refine ⟨K, hKc, hKG, ?_⟩
  have h1 : P (X ⁻¹' (G \ ⋃ m, K m)) = 0 := by
    rw [← Measure.map_apply_of_aemeasurable hX (hG.diff hKm)]
    exact h0
  have h2 : ∀ᵐ ω ∂P, X ω ∉ G \ ⋃ m, K m :=
    ae_iff.2 (measure_mono_null (fun ω hω => not_not.1 hω) h1)
  filter_upwards [hae, h2] with ω hω hω'
  by_contra hc
  exact hω' ⟨hω, fun h => hc (mem_iUnion.1 h)⟩

/-- The restriction of a Brownian driver to `[0,T]` is a.e.-measurable. -/
theorem aemeasurable_pathC_drive {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (κ T : ℝ) :
    AEMeasurable (fun ω => pathC T (drive κ B ω)) P := by
  obtain ⟨B', hm, hc, heq⟩ := CharFun.exists_good_version hB
  have hval : ∀ ω (x : Icc (0 : ℝ) T),
      pathC T (drive κ B' ω) x = Real.sqrt κ * B' (x : ℝ).toNNReal ω := by
    intro ω x
    simp [pathC, Thm14FromThm13.continuous_drive (hc ω), drive]
  refine ⟨fun ω => pathC T (drive κ B' ω), ContinuousMap.measurable_iff_eval.2 fun x => ?_, ?_⟩
  · simp_rw [hval]
    exact (hm _).const_mul _
  · filter_upwards [heq] with ω hω
    have : drive κ B ω = drive κ B' ω := funext fun t => by simp [drive, hω]
    rw [this]

/-! ## The rescaled time reversal as a continuous map -/

/-- `(V, t, r) ↦ (u ↦ r (V(n − t + t u) − V(n − t)))` (with `V` extended constantly). -/
def gsPath (n : ℕ) (x : C(Icc (0 : ℝ) n, ℝ) × (ℝ × ℝ)) : C(Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun u => x.2.2 * (extIccPath (Nat.cast_nonneg n) x.1 (n - x.2.1 + x.2.1 * u) -
      extIccPath (Nat.cast_nonneg n) x.1 (n - x.2.1)),
    continuous_const.mul (((continuous_extIccPath _ _).comp
      (continuous_const.add (continuous_const.mul continuous_subtype_val))).sub continuous_const)⟩

theorem continuous_gsPath (n : ℕ) : Continuous (gsPath n) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have hev : Continuous (fun q : C(Icc (0 : ℝ) n, ℝ) × Icc (0 : ℝ) n => q.1 q.2) :=
    continuous_eval
  show Continuous fun q : (C(Icc (0 : ℝ) n, ℝ) × (ℝ × ℝ)) × Icc (0 : ℝ) 1 =>
    q.1.2.2 * (q.1.1 (projIcc (0 : ℝ) (n : ℝ) (Nat.cast_nonneg n) (n - q.1.2.1 + q.1.2.1 * q.2)) -
      q.1.1 (projIcc (0 : ℝ) (n : ℝ) (Nat.cast_nonneg n) (n - q.1.2.1)))
  refine (continuous_snd.comp (continuous_snd.comp continuous_fst)).mul ?_
  refine (hev.comp ((continuous_fst.comp continuous_fst).prodMk ?_)).sub
    (hev.comp ((continuous_fst.comp continuous_fst).prodMk ?_))
  · exact (continuous_projIcc (a := (0 : ℝ)) (b := (n : ℝ)) (h := Nat.cast_nonneg n)).comp
      (continuous_const.sub
      (continuous_fst.comp (continuous_snd.comp continuous_fst)) |>.add
      ((continuous_fst.comp (continuous_snd.comp continuous_fst)).mul
        (continuous_subtype_val.comp continuous_snd)))
  · exact (continuous_projIcc (a := (0 : ℝ)) (b := (n : ℝ)) (h := Nat.cast_nonneg n)).comp
      (continuous_const.sub
      (continuous_fst.comp (continuous_snd.comp continuous_fst)))

/-- The pair `(gsPath (V, t, r), T)`. -/
def gsMap (n : ℕ) (x : C(Icc (0 : ℝ) n, ℝ) × ((ℝ × ℝ) × ℝ)) : PathT :=
  (gsPath n (x.1, x.2.1), x.2.2)

theorem continuous_gsMap (n : ℕ) : Continuous (gsMap n) :=
  ((continuous_gsPath n).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
    (continuous_snd.comp continuous_snd)

/-! ## Goodness at every time from goodness at time `n` -/

/-- **Good pairs from a good driver on `[0,n]`, at every time `t ∈ (0,n]`.** -/
theorem goodP_gsMap {n : ℕ} {V : C(Icc (0 : ℝ) n, ℝ)}
    (hV : GoodDriver n (extIccPath (Nat.cast_nonneg n) V)) {t r T : ℝ} (ht : 0 < t)
    (htn : t ≤ n) (hr : r * Real.sqrt t = 1) (hT : 0 < T) :
    GoodP (gsPath n (V, (t, r)), T) := by
  set e := extIccPath (Nat.cast_nonneg n) V with he
  obtain ⟨he0, -, hrem, η, hη, hhull⟩ := hV
  have hn : (0 : ℝ) < n := ht.trans_le htn
  set Wf : ℝ → ℝ := fun s => e (n - s) - e n with hWf
  have hec : Continuous e := continuous_extIccPath _ _
  have hWc : Continuous Wf := (hec.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hW0 : Wf 0 = 0 := by simp [hWf]
  set a := Real.sqrt t / Real.sqrt T with ha_def
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have ha : 0 < a := div_pos hst hsT
  have ha2 : a ^ 2 = t / T := by rw [ha_def, div_pow, Real.sq_sqrt ht.le, Real.sq_sqrt hT.le]
  have h1 : (revDrv Wf t a).1 = T := by
    show t / a ^ 2 = T
    rw [ha2]
    field_simp
  have heq : EqOn (sclDrv (gsPath n (V, (t, r)), T)) (revDrv Wf t a).2 (Icc 0 T) := by
    intro s hs
    have hu : s / T ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hs.1 hT.le, (div_le_one hT).2 hs.2⟩
    show Real.sqrt T * extIccPath zero_le_one (gsPath n (V, (t, r))) (s / T) =
      (Wf (t - a ^ 2 * s) - Wf t) / a
    rw [extIccPath_of_mem zero_le_one _ hu]
    show Real.sqrt T * (r * (e (n - t + t * (s / T)) - e (n - t))) =
      (e (n - (t - a ^ 2 * s)) - e n - (e (n - t) - e n)) / a
    rw [ha2, show (n : ℝ) - (t - t / T * s) = n - t + t * (s / T) by field_simp; ring]
    have hr' : r = 1 / Real.sqrt t := eq_div_of_mul_eq hst.ne' hr
    rw [hr', ha_def]
    field_simp
    ring
  have hrev : revHull (sclDrv (gsPath n (V, (t, r)), T)) T =
      revHull (revDrv Wf t a).2 (revDrv Wf t a).1 := by
    have hm : revMap (sclDrv (gsPath n (V, (t, r)), T)) T = revMap (revDrv Wf t a).2 T :=
      funext fun z => ReverseFlow.revMap_congr_drive z heq
    rw [h1]
    unfold revHull
    rw [hm]
  refine ⟨hT, ?_, ?_, ?_⟩
  · simp [sclDrv, extIccPath, gsPath]
  · show IsSimpleCurveHull (revHull (sclDrv (gsPath n (V, (t, r)), T)) T)
    rw [hrev]
    exact isSimpleCurveHull_revDrv hWc hW0 ht ha hη (hhull t ⟨ht.le, htn⟩)
  · have hVe : EqOn (B2.vrev Wf n) e (Icc 0 n) := by
      intro s hs
      simp only [B2.vrev, hWf, max_eq_left hs.1, min_eq_left hs.2]
      simp [sub_sub_cancel, he0]
    have hKn : revHull e n = fwdHull Wf n := by
      have hm : revMap (B2.vrev Wf n) n = revMap e n :=
        funext fun z => ReverseFlow.revMap_congr_drive z hVe
      rw [← Cor15Group.revHull_vrev_eq_fwdHull hWc hW0 hn]
      unfold revHull
      rw [hm]
    rw [hKn] at hrem
    show IsConformallyRemovable (closure (revHull (sclDrv (gsPath n (V, (t, r)), T)) T) ∪
      conj '' closure (revHull (sclDrv (gsPath n (V, (t, r)), T)) T))
    rw [hrev]
    have hsub : revHull (revDrv Wf t a).2 (revDrv Wf t a).1 ⊆
        (fun z => ((a⁻¹ : ℝ) : ℂ) * z) '' fwdHull Wf n := by
      refine (revHull_revDrv_subset hWc hW0 ht ha).trans ?_
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, (fwdHull_mono (W := Wf)).1 htn hz, by simp⟩
    have hainv : (a⁻¹ : ℝ) ≠ 0 := inv_ne_zero ha.ne'
    have hK := isConformallyRemovable_mul hrem (c := ((a⁻¹ : ℝ) : ℂ)) (by exact_mod_cast hainv)
    exact isConformallyRemovable_mono hK (doubled_subset_mul hainv hsub)
      (isClosed_closure.union (isClosed_conj_image isClosed_closure))

end Thm18Asm
end QuantumZipper
