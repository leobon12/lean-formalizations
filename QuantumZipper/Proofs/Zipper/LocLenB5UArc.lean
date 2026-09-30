import QuantumZipper.Proofs.Zipper.LocLenB5ULocal
import QuantumZipper.Proofs.Zipper.UnifClAnchor
import QuantumZipper.Proofs.Zipper.UnifSWRat
import QuantumZipper.Proofs.Zipper.F2S3B5Plus

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R3b: `B5UniformArcStmt` (open-arc B5, uniform in time, both sides)

Sheffield arXiv:1012.4797 p. 56 (the boundary length of the two sides of `η[0,s]` is read in the
unzipped picture); Berestycki–Powell arXiv:2404.16642 Def 8.12 p. 281 and footnote 22 p. 287
(lengths of open boundary arcs, the tip excluded).

Minus side (`ae_b5MinusArc_of_extAll`): the old proof of `RegUnif.ae_b5v_uniform_of_windows`
(UnifClB5.lean) with its two uniform inputs replaced by off-tip ones:
* the window identities `ν_{h⁰_T}(u,v) = ν^{loc}_{h⁰_s}(F_s u, F_s v)` are read from the proved
  anchor windows AW (`anchorWindowAllStmt_of_extAll`) and the fixed-time identities at rational
  anchors (`ae_windows_rat`), exactly as in `unifWindowStmt_of_anchor` but stopping before its
  global-limit (UG) step: the chart-`s` side stays a local measure on an image window;
* the image windows avoid the tip, so the local measures there are restrictions of the off-tip
  limit `ν_s` of `UnifLocalStmt` (`unifLocalStmt_of_extAll`);
* the exhaustion of the open arc `(0₋(T), 0₋(T−s))` by rational windows
  (`B5.measure_Ioo_eq_of_windows`) and `realRevMap_endpoints` give `ν_{h⁰_T}(0₋(T), 0₋(T−s)) =
  ν_s(O⁻_s, 0)`, which is the open-arc length (`arcLen_eq_of_isVagueLimitOnR`).
Plus side (`b5UniformArcStmt_holds`): the minus side for the reflected pair `(−B, X ∘ refl)`
(Sheffield p. 72, "by symmetry"; as `F2.b5PlusUniform_of_refl`), with the reflection of local
limits (`isVagueLimitOnR_neg`) at time `s` and of the global fixed-time limit at time `T`.
No tip input (`TipCore`, UT, UG, UA) and no flow regularity (`CfgFlowRegStmt`) is used.
Own bookkeeping otherwise.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open B2 B5 RegUnif

/-- A strictly increasing function on `(a,c)` with limit `e` at `c⁻` stays below `e`
(own elementary; the `hup` step of `B5.measure_Ioo_eq_of_windows`). -/
theorem lt_of_strictMonoOn_tendsto_left {F : ℝ → ℝ} {a c e : ℝ}
    (hmono : StrictMonoOn F (Ioo a c)) (hC : Tendsto F (𝓝[<] c) (𝓝 e)) {x : ℝ}
    (hx : x ∈ Ioo a c) : F x < e := by
  set m := (x + c) / 2
  have hm : m ∈ Ioo a c := ⟨by simp only [m]; linarith [hx.1, hx.2], by simp only [m]; linarith [hx.2]⟩
  have hxm : x < m := by simp only [m]; linarith [hx.2]
  have hle : F m ≤ e := by
    refine ge_of_tendsto hC ?_
    filter_upwards [Ioo_mem_nhdsLT hm.2] with y hy
    exact hmono.monotoneOn hm ⟨hm.1.trans hy.1, hy.2⟩ hy.1.le
  exact (hmono hx hm hxm).trans_le hle

/-- The open-arc length of an empty arc is `0`. -/
theorem arcLen_self (γ : ℝ) (x : FieldSample) (a : ℝ) : arcLen γ x a a = 0 := by
  unfold arcLen; rw [Ioo_self, measure_empty]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Local window identities (UW without UG)**: a.s., for all `s ∈ (0,T]` and rational windows
`0₋(T) < u < v < 0₋(T−s)`, `ν_{h⁰_T}(u,v)` is the local measure of `h⁰_s` on the image window.
Copy of `RegUnif.unifWindowStmt_of_anchor` without its last (global-limit) step. -/
theorem ae_windows_local_of_anchor (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hAW : AnchorWindowStmt κ T P B X) :
    ∀ᵐ ω ∂P, ∀ s ∈ Ioc 0 T, ∀ u v : ℚ, zeroMinus (Vr κ T B ω) T < u → (u : ℝ) < v →
      (v : ℝ) < zeroMinus (Vr κ T B ω) (T - s) →
      qBoundaryMeasure (Real.sqrt κ) (h0f κ T B X ω) (Ioo u v) =
        arcLen (Real.sqrt κ) (h0f κ s B X ω)
          (realRevMap (Vr κ T B ω) (T - s) u) (realRevMap (Vr κ T B ω) (T - s) v) := by
  filter_upwards [ae_windows_rat hκ hκ4 hT hB hX hind, ae_anchor_all hAW,
    ae_zeroMinus_Vr_facts RS.rohdeSchrammSimple hκ hκ4.le hT P B hB] with ω hq hA hzm
  intro s hs u v hu huv hv
  obtain ⟨-, -, -, hzc, -, -⟩ := hzm
  set zm := zeroMinus (Vr κ T B ω)
  have hTs : T - s ∈ Icc 0 T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  obtain ⟨δ, hδ, hδv⟩ := Metric.continuousWithinAt_iff.1 (hzc (T - s) hTs) (zm (T - s) - v)
    (by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt (sub_lt_self s hδ) hs.1)
  have hq0 : (0 : ℝ) < q := (le_max_right _ _).trans_lt hq1
  have hqs : (q : ℝ) < s := hq2
  have hqT : (q : ℝ) ≤ T := hqs.le.trans hs.2
  have hvq : (v : ℝ) < zm (T - q) := by
    have hmem : T - q ∈ Icc 0 T := ⟨by linarith [hs.2], by linarith⟩
    have hd : dist (T - q) (T - s) < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [(le_max_left _ _).trans_lt hq1]
    have := hδv hmem hd
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  rw [hq q hq0 hqT u v hu huv hvq, ← hA q u v hq0 hqT hu huv hvq s ⟨hqs.le, hs.2⟩]
  rfl

/-- **Minus side of `B5UniformArcStmt`** from AC-fam-ext (no tip input). -/
theorem ae_b5MinusArc_of_extAll (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hF : AnchorUnifFamExtAllStmt κ P B X) :
    ∀ᵐ ω ∂P, ∀ s ∈ Icc (0 : ℝ) T,
      (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) s).1 =
        qBoundaryMeasure (Real.sqrt κ) (h0f κ T B X ω)
          (Ioo (zeroMinus (Vr κ T B ω) T) (zeroMinus (Vr κ T B ω) (T - s))) := by
  have hRSS := RS.rohdeSchrammSimple
  filter_upwards [ae_windows_local_of_anchor hκ hκ4 hT hB hX hind
      (anchorWindowAllStmt_of_extAll hκ hκ4 hB hX hind hF T hT),
    unifLocalStmt_of_extAll hκ hκ4 hT hB hX hind hF, hB.cont, hB.eval_zero_ae_eq_zero,
    ae_isSimpleCurveHull_revHull_Vr hRSS hκ hκ4.le hT P B hB,
    ae_forall_isSimpleCurveHull_revHull_Vr hRSS hκ hκ4.le P B hB,
    RS.ae_real_alive hB hκ hκ4.le] with ω hw hloc hc h0 hK hK's halive
  intro s hs
  set W := drive κ B ω with hWdef
  have hWc : Continuous W := Thm14FromThm13.continuous_drive hc
  have hW0 : W 0 = 0 := by simp [hWdef, drive, h0]
  have hL : (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) s).1 =
      arcLen (Real.sqrt κ) (h0f κ s B X ω) (sideImages W s).1 0 := by
    rw [h0f_eq_unzippedField]; rfl
  rw [hL]
  rcases hs.1.eq_or_lt with hs0 | hs0
  · subst hs0
    rw [sideImages_fst_zero_time hW0, arcLen_self, sub_zero, Ioo_self, measure_empty]
  · have hsT := hs.2
    have hK' := hK's s hs0
    have hVc : Continuous (Vr κ T B ω) := continuous_vrev hWc T
    have hV0 : Vr κ T B ω 0 = 0 := vrev_zero hT.le
    have hV'c : Continuous (Vr κ s B ω) := continuous_vrev hWc s
    have hV'0 : Vr κ s B ω 0 = 0 := vrev_zero hs0.le
    have hshift : ∀ r, 0 ≤ r → Vr κ s B ω r = Vr κ T B ω (T - s + r) - Vr κ T B ω (T - s) :=
      fun r hr => (vrev_shift hs0.le hsT hr).symm
    obtain ⟨hac, hmono, hA, hC⟩ := realRevMap_endpoints hVc hV0 hT hK hV'c hV'0 hs0 hK'
      (sub_nonneg.2 hsT) (by ring) hshift
    have hside : (sideImages W s).1 = zeroMinus (Vr κ s B ω) s :=
      sideImages_fst_eq_zeroMinus_vrev hWc hW0 hs0 hK' fun x hx => halive x hx s hs0.le
    obtain ⟨ν, hν, -⟩ := hloc s ⟨hs0.le, hsT⟩
    have hsub : ∀ {p r : ℝ}, r ≤ 0 → Ioo p r ⊆ ({0} : Set ℝ)ᶜ := fun hr z hz hz0 => by
      rw [mem_singleton_iff] at hz0; linarith [hz.2]
    rw [hside, arcLen_eq_of_isVagueLimitOnR hν (hsub le_rfl)]
    refine (measure_Ioo_eq_of_windows hac hmono hA hC fun u v hu huv hv => ?_).symm
    rw [hw s ⟨hs0, hsT⟩ u v hu huv hv, arcLen_eq_of_isVagueLimitOnR hν (hsub
      (lt_of_strictMonoOn_tendsto_left hmono hC ⟨hu.trans huv, hv⟩).le)]

end LocLen
end QuantumZipper
