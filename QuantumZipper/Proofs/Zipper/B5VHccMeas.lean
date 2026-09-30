import QuantumZipper.Proofs.Zipper.E1TransferM4Main

/-!
# B5V-HCC, measurability: the window identity as a measurable event of (coordinates, driver)

Task B5V-HCC (`handoff/B5.md`, B5V-FIX, "Remaining (R1-TR)"). Data space
`DP t = (ℕ → ℝ) × C([0,t], ℝ)` (circle coordinates, continuous driver path). For rational
`u < v` we build the measurable set `eqP κ ht u v` of data for which, on the good set
`goodP` (driver starts at `0`, `v` is live, and both rebuilt fields carry the boundary certificate
`M4.BCert`), the local boundary measure of the zipped field `coordChange (fromC c) (revMap W t) Q`
on `(u,v)` equals the boundary measure of `fromC c` on `(F u, F v)`, `F = realRevMap W t`.

* `Fm`, `measurable_Fm`, `Fm_eq_realRevMap`: the real flow map as a measurable function of the
  driver path (limit of the tamed flows `revZ`, which are continuous in the path by Grönwall,
  `M4.continuous_revZ_Wof`; on live points the tamed flow equals the real solution for small
  taming parameter, `Collision.revZ_eq_of_isRealRevSol`);
* `rawConverges_congr_full`, `bCert_addConst`, `qBoundaryMeasureOn_congr_full`,
  `qBoundaryMeasure_congr_full`: invariance lemmas;
* `measurableSet_eqP`.

The normalization of `M4.zR` is switched off by taking `ϖ = 0` (then `mC = 0`).
Source of the statement: Sheffield, arXiv:1012.4797, proof of Lemma 5.6 (pp. 66–68). The
measurability plumbing is **own bookkeeping** (as in `E1TransferM4Main`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B5

open E1 E1.M4 CoordsFull Collision

/-! ### The real flow map as a measurable function of the driver path -/

/-- The real flow map read through the tamed flows (a measurable function of the path). -/
def Fm (t : ℝ) (ht : 0 ≤ t) (x : ℝ) (w : C(Icc (0 : ℝ) t, ℝ)) : ℝ :=
  limUnder atTop fun n : ℕ => (revZ (CharFun.Wof 1 t ht w) (1 / ((n : ℝ) + 1)) x t).re

theorem measurable_Fm (t : ℝ) (ht : 0 ≤ t) (x : ℝ) : Measurable (Fm t ht x) := by
  unfold Fm
  exact (StronglyMeasurable.limUnder fun n => (Complex.continuous_re.comp
    (continuous_revZ_Wof ht (by positivity) (x : ℂ) ⟨ht, le_rfl⟩)).measurable.stronglyMeasurable).measurable

theorem Fm_eq_realRevMap {t : ℝ} (ht : 0 ≤ t) {x : ℝ} {w : C(Icc (0 : ℝ) t, ℝ)}
    (hx : IsLive (CharFun.Wof 1 t ht w) t x) (hx0 : x < CharFun.Wof 1 t ht w 0) :
    Fm t ht x w = realRevMap (CharFun.Wof 1 t ht w) t x := by
  set W := CharFun.Wof 1 t ht w with hWdef
  have hW : Continuous W := CharFun.continuous_Wof 1 t ht w
  obtain ⟨u, hu⟩ := (isLive_iff_exists hW ht).1 hx
  obtain ⟨c, hc, K, hcK⟩ := exists_bounds_isRealRevSol hu ht hx0
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hc
  have hev : ∀ n ≥ N, (revZ W (1 / ((n : ℝ) + 1)) x t).re = u t := by
    intro n hn
    have hle : 1 / ((n : ℝ) + 1) ≤ c := (Nat.one_div_le_one_div hn).trans hN.le
    rw [revZ_eq_of_isRealRevSol hW (by positivity) hu (fun r hr => hle.trans (hcK r hr).1) t
      ⟨ht, le_rfl⟩, Complex.ofReal_re]
  unfold Fm
  rw [← hWdef, RealLine.realRevMap_eq hW hu ht le_rfl]
  exact (tendsto_atTop_of_eventually_const hev).limUnder_eq

/-! ### Invariance lemmas -/

theorem rawConverges_congr_full {x x' : FieldSample} (h : coordsFull x = coordsFull x')
    {S : Set ℂ} (hx : LocalRule.RawConverges x S) : LocalRule.RawConverges x' S := by
  intro k z hz
  obtain ⟨l, hl⟩ := hx k z hz
  refine ⟨l, hl.congr fun n => ?_⟩
  rw [radius_eq_div]
  exact coordsFull_apply_eq h n z 1 one_pos k

theorem qBoundaryMeasureOn_congr_full {γ : ℝ} {x x' : FieldSample}
    (h : coordsFull x = coordsFull x') (U : Set ℝ) :
    qBoundaryMeasureOn γ x U = qBoundaryMeasureOn γ x' U := by
  unfold qBoundaryMeasureOn
  rw [Factorization.bdryApprox_congr (avgReg_congr_full h) γ]

theorem qBoundaryMeasure_congr_full {γ : ℝ} {x x' : FieldSample}
    (h : coordsFull x = coordsFull x') : qBoundaryMeasure γ x = qBoundaryMeasure γ x' := by
  unfold qBoundaryMeasure
  rw [Factorization.bdryApprox_congr (avgReg_congr_full h) γ]

theorem bCert_congr_full {γ : ℝ} {x x' : FieldSample} (h : coordsFull x = coordsFull x')
    (hx : BCert γ x) : BCert γ x' := by
  unfold BCert at hx ⊢
  rw [← Factorization.bdryApprox_congr (avgReg_congr_full h) γ]
  exact hx

theorem bCert_addConst {γ : ℝ} {x : FieldSample} (hx : LocalRule.RawConverges x Hbar)
    (h : BCert γ x) (c : ℝ) : BCert γ (addConst x c) := by
  obtain ⟨ν, hν⟩ := exists_isVagueLimitR_of_bCert h
  have he := funext (LocalRule.bdryApprox_addConst hx γ c)
  refine bCert_of_isVagueLimitR (ν := ENNReal.ofReal (Real.exp (γ * c / 2)) • ν)
    (fun k N => ?_) ?_
  · simp only [he, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h.1 k N)
  · rw [he]; exact BdryVague.IsVagueLimitR.const_smul hν ENNReal.ofReal_ne_top

/-! ### The measurable event -/

/-- The data space. -/
abbrev DP (t : ℝ) := (ℕ → ℝ) × C(Icc (0 : ℝ) t, ℝ)

variable (κ : ℝ) {t : ℝ} (ht : 0 ≤ t)

/-- The zipped field rebuilt from coordinates, without normalization (`ϖ = 0`). -/
def Zr (p : DP t) : FieldSample := zR κ ht 0 p

theorem measurable_Zr : Measurable (Zr κ ht) := measurable_zR κ ht 0 (by simp)

open Classical in
/-- The boundary measure, guarded by the certificate (junk `0` off it). -/
def gM (x : FieldSample) : Measure ℝ :=
  if BCert (Real.sqrt κ) x then qBoundaryMeasure (Real.sqrt κ) x else 0

theorem measurable_gM : Measurable (gM κ) := measurable_qBoundaryMeasure_bCert _

theorem gM_Icc_lt_top (x : FieldSample) (a b : ℝ) : gM κ x (Icc a b) < ⊤ := by
  unfold gM
  split_ifs with h
  · have := (isVagueLimitR_qBoundaryMeasure (exists_isVagueLimitR_of_bCert h)).1
    exact measure_Icc_lt_top
  · simp

/-- The good set of the data for the window `(u,v)`. -/
def goodP (v : ℝ) : Set (DP t) :=
  Prod.snd ⁻¹' {w : C(Icc (0 : ℝ) t, ℝ) |
      w ⟨0, ⟨le_rfl, ht⟩⟩ = 0 ∧ v ∈ liveNeg (CharFun.Wof 1 t ht w) t} ∩
    {p | BCert (Real.sqrt κ) (Zr κ ht p)} ∩ {p | BCert (Real.sqrt κ) (fromC p.1)}

/-- Left side of the window identity. -/
def LP (u v : ℝ) (p : DP t) : ℝ≥0∞ := gM κ (Zr κ ht p) (Ioo u v)

/-- Right side of the window identity. -/
def RP (u v : ℝ) (p : DP t) : ℝ≥0∞ := gM κ (fromC p.1) (Ioo (Fm t ht u p.2) (Fm t ht v p.2))

/-- The event of the window identity (on the good set). -/
def eqP (u v : ℝ) : Set (DP t) := (goodP κ ht v)ᶜ ∪ {p | LP κ ht u v p = RP κ ht u v p}

theorem measurableSet_goodP (v : ℝ) : MeasurableSet (goodP κ ht v) :=
  ((measurableSet_liveNeg_pt t ht v).preimage measurable_snd |>.inter
    ((measurableSet_bCert _).preimage (measurable_Zr κ ht))).inter
    ((measurableSet_bCert _).preimage (measurable_fromC.comp measurable_fst))

theorem measurable_LP (u v : ℝ) : Measurable (LP κ ht u v) :=
  (Measure.measurable_coe measurableSet_Ioo).comp ((measurable_gM κ).comp (measurable_Zr κ ht))

theorem measurable_RP (u v : ℝ) : Measurable (RP κ ht u v) := by
  set M : DP t → Measure ℝ := fun p => gM κ (fromC p.1) with hM
  have hMm : Measurable M := (measurable_gM κ).comp (measurable_fromC.comp measurable_fst)
  set S : Set (DP t × ℝ) := {a | Fm t ht u a.1.2 < a.2 ∧ a.2 < Fm t ht v a.1.2} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_lt ((measurable_Fm t ht u).comp (measurable_snd.comp measurable_fst))
      measurable_snd).inter
    (measurableSet_lt measurable_snd ((measurable_Fm t ht v).comp
      (measurable_snd.comp measurable_fst)))
  have e : ∀ p, RP κ ht u v p = ⨆ N : ℕ,
      ∫⁻ y in Icc (-(N : ℝ)) N, S.indicator 1 (p, y) ∂M p := by
    intro p
    have hsec : ∀ y, S.indicator (1 : DP t × ℝ → ℝ≥0∞) (p, y) =
        (Ioo (Fm t ht u p.2) (Fm t ht v p.2)).indicator 1 y := fun y => by
      by_cases hy : y ∈ Ioo (Fm t ht u p.2) (Fm t ht v p.2)
      · rw [indicator_of_mem hy, indicator_of_mem (show (p, y) ∈ S from hy)]; rfl
      · rw [indicator_of_notMem hy, indicator_of_notMem (show (p, y) ∉ S from hy)]
    simp_rw [hsec, lintegral_indicator_one measurableSet_Ioo,
      Measure.restrict_apply measurableSet_Ioo]
    have hU : Ioo (Fm t ht u p.2) (Fm t ht v p.2) =
        ⋃ N : ℕ, Ioo (Fm t ht u p.2) (Fm t ht v p.2) ∩ Icc (-(N : ℝ)) N := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioo]
      constructor
      · intro hy
        obtain ⟨N, hN⟩ := exists_nat_ge |y|
        exact ⟨N, hy, neg_le_of_abs_le hN, le_of_abs_le hN⟩
      · rintro ⟨N, hy, -⟩; exact hy
    rw [RP, ← Monotone.measure_iUnion, ← hU]
    · intro N N' h
      refine inter_subset_inter_right _ (Icc_subset_Icc ?_ ?_)
      · exact neg_le_neg (by exact_mod_cast h)
      · exact_mod_cast h
  rw [show RP κ ht u v = _ from funext e]
  exact Measurable.iSup fun N => measurable_setLIntegral_of_measurable_measure hMm
    measurableSet_Icc (fun p => gM_Icc_lt_top κ _ _ _) (measurable_one.indicator hSm)

theorem measurableSet_eqP (u v : ℝ) : MeasurableSet (eqP κ ht u v) :=
  (measurableSet_goodP κ ht v).compl.union
    (measurableSet_eq_fun (measurable_LP κ ht u v) (measurable_RP κ ht u v))

end B5
end QuantumZipper
