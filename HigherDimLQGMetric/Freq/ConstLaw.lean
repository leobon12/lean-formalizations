import HigherDimLQGMetric.Freq.ScaleCount
import HigherDimLQGMetric.Events.EventInvariant
import HigherDimLQGMetric.Events.TightLaw

/-! Constant-shift invariance of the sharp-normalized shell data. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set MeasureTheory
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- A constant field shift cancels between the metric and its sharp normalizer. -/
theorem s4c_normInt_addConst (D : DistRd d → ContMetric d)
    (ξ Q : ℝ) (g : DistRd d) (c r : ℝ) (z : Rd d) (V : Set (Rd d))
    (u v : Rd d) (hr : 0 < r)
    (havg : sphereAvg (addConst g c) r z = sphereAvg g r z + c)
    (hInt : (D (addConst g c)).internal V u v =
      ENNReal.ofReal (Real.exp (ξ * c)) * (D g).internal V u v) :
    normInt ξ Q D g r z V u v =
      normInt ξ Q D (addConst g c) r z V u v := by
  have hs : 0 < sNorm ξ Q g r z := sNorm_pos ξ Q g hr z
  have hs2 : 0 < sNorm ξ Q (addConst g c) r z :=
    sNorm_pos ξ Q (addConst g c) hr z
  have he : Real.exp (ξ * c) ≠ 0 := (Real.exp_pos _).ne'
  have hnorm : sNorm ξ Q (addConst g c) r z =
      sNorm ξ Q g r z * Real.exp (ξ * c) := by
    simp only [sNorm, havg, mul_add, Real.exp_add]
    ring
  have hfactor : (sNorm ξ Q (addConst g c) r z)⁻¹ * Real.exp (ξ * c) =
      (sNorm ξ Q g r z)⁻¹ := by
    rw [hnorm]
    field_simp
  unfold normInt
  rw [hInt, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hs2.le), hfactor]

/-- Simultaneous cancellation on every open region, for a normalized LGF. -/
theorem IsSharpWeakExpMetric.ae_normInt_normalize
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hd : 2 ≤ d)
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    ∀ᵐ ω ∂P, ∀ (V : Set (Rd d)), IsOpen V → ∀ u v : Rd d,
      normInt ξ Q D (h ω) r z V u v =
        normInt ξ Q D
          (addConst (h ω) (-sphereAvg (h ω) 1 0)) r z V u v := by
  have hd1 : 1 ≤ d := by omega
  filter_upwards [hD.ae_internal_eq_weylScaleOn hh.isLGFPlusCont,
    hh.ae_exists_tendsto_sphereAvgSeq hd hr z] with ω hw hc
  obtain ⟨_, hconv⟩ := hc
  intro V hV u v
  let c : ℝ := -sphereAvg (h ω) 1 0
  apply s4c_normInt_addConst D ξ Q (h ω) c r z V u v hr
  · exact sphereAvg_addConst_of_tendsto hd1 hconv c
  · have he := hw (ContinuousMap.const (Rd d) c) V hV u v
    simp only [addFun_const] at he
    rw [he]
    exact weylScaleOn_of_eq_const (D := D (h ω)) (ξ := ξ)
      (f := ContinuousMap.const (Rd d) c) (U := V) (z := u) (w := v)
      (by intro x hx; rfl)

/-- The path-witness event is unchanged by recentering the field by its unit
sphere average. This is the event-level input to law transfer. -/
theorem s4c_ae_witEvent_normalize
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B) (hd : 2 ≤ d)
    (U a A₀ ℓ β₀ t : ℝ) {r : ℝ} (hr : 0 < r) (z : Rd d) :
    ∀ᵐ ω ∂P, h ω ∈ WitEvent A B ξ Q U a A₀ ℓ β₀ t r z ↔
      addConst (h ω) (-sphereAvg (h ω) 1 0) ∈
        WitEvent A B ξ Q U a A₀ ℓ β₀ t r z := by
  let N : Ω → DistRd d :=
    fun ω => addConst (h ω) (-sphereAvg (h ω) 1 0)
  have hc : Measurable (fun ω => -sphereAvg (h ω) 1 0) :=
    ((measurable_sphereAvg_left (d := d) 1 0).comp hh.measurable).neg
  have hhN : IsWholeSpaceLGF N P := hh.addConst hc
  filter_upwards [hA.ae_normInt_normalize P h hh hd hr z,
    hB.ae_normInt_normalize P h hh hd hr z,
    hA.length P h hh.isLGFPlusCont,
    hA.length P N hhN.isLGFPlusCont] with ω hAJ hBJ hlA hlN
  have eAJ : ∀ u ∈ ann z (r / 2) (5 * r), ∀ v ∈ ann z (r / 2) (5 * r),
      normInt ξ Q A (h ω) r z (ann z (r / 2) (5 * r)) u v =
        normInt ξ Q A (N ω) r z (ann z (r / 2) (5 * r)) u v :=
    fun u _ v _ => hAJ _ (isOpen_ann _ _ _) u v
  have eBJ : ∀ u ∈ ann z (r / 2) (5 * r), ∀ v ∈ ann z (r / 2) (5 * r),
      normInt ξ Q B (h ω) r z (ann z (r / 2) (5 * r)) u v =
        normInt ξ Q B (N ω) r z (ann z (r / 2) (5 * r)) u v :=
    fun u _ v _ => hBJ _ (isOpen_ann _ _ _) u v
  have eAO : ∀ u ∈ ann z (3 * r / 4) (3 * r), ∀ v ∈ ann z (3 * r / 4) (3 * r),
      normInt ξ Q A (h ω) r z (ann z (3 * r / 4) (3 * r)) u v =
        normInt ξ Q A (N ω) r z (ann z (3 * r / 4) (3 * r)) u v :=
    fun u _ v _ => hAJ _ (isOpen_ann _ _ _) u v
  have eBO : ∀ u ∈ ann z (3 * r / 4) (3 * r), ∀ v ∈ ann z (3 * r / 4) (3 * r),
      normInt ξ Q B (h ω) r z (ann z (3 * r / 4) (3 * r)) u v =
        normInt ξ Q B (N ω) r z (ann z (3 * r / 4) (3 * r)) u v :=
    fun u _ v _ => hBJ _ (isOpen_ann _ _ _) u v
  constructor
  · exact witEvent_of_normInternal_eq A B ξ Q U a A₀ ℓ β₀ t hr z
      (h ω) (N ω) hlA hlN eAJ eBJ eAO eBO
  · exact witEvent_of_normInternal_eq A B ξ Q U a A₀ ℓ β₀ t hr z
      (N ω) (h ω) hlN hlA
      (fun u hu v hv => (eAJ u hu v hv).symm)
      (fun u hu v hv => (eBJ u hu v hv).symm)
      (fun u hu v hv => (eAO u hu v hv).symm)
      (fun u hu v hv => (eBO u hu v hv).symm)

/-- D-LT for a fixed-center witness event: its probability is independent of
the probability space and of the whole-space LGF representative. -/
theorem s4c_witEvent_law_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (h : Ω → DistRd d) (h' : Ω' → DistRd d)
    (hh : IsWholeSpaceLGF h P) (hh' : IsWholeSpaceLGF h' P')
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B) (hd : 2 ≤ d)
    (U a A₀ ℓ β₀ t : ℝ) {r : ℝ} (hr : 0 < r) (z : Rd d) :
    P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r z) =
      P' (h' ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r z) := by
  let N : Ω → DistRd d :=
    fun ω => addConst (h ω) (-sphereAvg (h ω) 1 0)
  let N' : Ω' → DistRd d :=
    fun ω => addConst (h' ω) (-sphereAvg (h' ω) 1 0)
  have hm : Measurable N :=
    (hh.addConst (((measurable_sphereAvg_left (d := d) 1 0).comp
      hh.measurable).neg)).measurable
  have hm' : Measurable N' :=
    (hh'.addConst (((measurable_sphereAvg_left (d := d) 1 0).comp
      hh'.measurable).neg)).measurable
  have hn : IsWholeSpaceLGF N P := hh.addConst
    (((measurable_sphereAvg_left (d := d) 1 0).comp hh.measurable).neg)
  have hn' : IsWholeSpaceLGF N' P' := hh'.addConst
    (((measurable_sphereAvg_left (d := d) 1 0).comp hh'.measurable).neg)
  let E := WitEvent A B ξ Q U a A₀ ℓ β₀ t r z
  have hE : NullMeasurableSet E (P.map N) := by
    simpa [E] using
      hA.nullMeasurableSet_witEvent (P.map N) id hn.map_id hB
        U a A₀ ℓ β₀ t hr z
  have hE' : NullMeasurableSet E (P'.map N') := by
    simpa [E] using
      hA.nullMeasurableSet_witEvent (P'.map N') id hn'.map_id hB
        U a A₀ ℓ β₀ t hr z
  have heq : P.map N = P'.map N' := map_normalizedLGF_eq hd hh hh'
  have hsets : h ⁻¹' E =ᵐ[P] N ⁻¹' E := by
    filter_upwards [s4c_ae_witEvent_normalize P h hh hA hB hd U a A₀ ℓ β₀ t hr z]
      with ω hw
    exact propext hw
  have hsets' : h' ⁻¹' E =ᵐ[P'] N' ⁻¹' E := by
    filter_upwards [s4c_ae_witEvent_normalize P' h' hh' hA hB hd U a A₀ ℓ β₀ t hr z]
      with ω hw
    exact propext hw
  calc
    P (h ⁻¹' E) = P (N ⁻¹' E) := measure_congr hsets
    _ = (P.map N) E := (Measure.map_apply₀ hm.aemeasurable hE).symm
    _ = (P'.map N') E := by rw [heq]
    _ = P' (N' ⁻¹' E) := Measure.map_apply₀ hm'.aemeasurable hE'
    _ = P' (h' ⁻¹' E) := measure_congr hsets'.symm

private theorem s4c_scale_le_iff {e a b : ℝ} (he : 0 < e) :
    a ≤ b ↔ a * e ≤ e * b := by
  rw [mul_comm e b, mul_le_mul_iff_of_pos_right he]

private theorem s4c_scale_lt_iff {e a b : ℝ} (he : 0 < e) :
    a < b ↔ a * e < e * b := by
  rw [mul_comm e b, mul_lt_mul_iff_of_pos_right he]

/-- The ratio event is homogeneous under a constant Weyl shift. -/
theorem s4c_gEvent_addConst (A B : DistRd d → ContMetric d)
    (ξ Q u β R : ℝ) (g : DistRd d) (c : ℝ)
    (havg : sphereAvg (addConst g c) R 0 = sphereAvg g R 0 + c)
    (hAe : ∀ x y : Rd d, (A (addConst g c)).1 (x, y) =
      Real.exp (ξ * c) * (A g).1 (x, y))
    (hBe : ∀ x y : Rd d, (B (addConst g c)).1 (x, y) =
      Real.exp (ξ * c) * (B g).1 (x, y)) :
    g ∈ GEvent A B ξ Q u β R ↔
      addConst g c ∈ GEvent A B ξ Q u β R := by
  let e := Real.exp (ξ * c)
  have he : 0 < e := Real.exp_pos _
  have hee : Real.exp (ξ * c) = e := rfl
  have hs : sNorm ξ Q (addConst g c) R 0 = sNorm ξ Q g R 0 * e := by
    simp only [sNorm, havg, mul_add, Real.exp_add, e]
    ring
  have hlow (x y : Rd d) :
      β * sNorm ξ Q g R 0 ≤ (A g).1 (x, y) ↔
      β * sNorm ξ Q (addConst g c) R 0 ≤
        (A (addConst g c)).1 (x, y) := by
    rw [hs, hAe, hee]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      (s4c_scale_le_iff (e := e) (a := β * sNorm ξ Q g R 0)
        (b := (A g).1 (x, y)) he)
  have hhigh (x y : Rd d) :
      (A g).1 (x, y) ≤ β⁻¹ * sNorm ξ Q g R 0 ↔
      (A (addConst g c)).1 (x, y) ≤
        β⁻¹ * sNorm ξ Q (addConst g c) R 0 := by
    rw [hs, hAe, hee]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      (s4c_scale_le_iff (e := e) (a := (A g).1 (x, y))
        (b := β⁻¹ * sNorm ξ Q g R 0) he)
  have hratio (x y : Rd d) :
      u * (A g).1 (x, y) < (B g).1 (x, y) ↔
      u * (A (addConst g c)).1 (x, y) <
        (B (addConst g c)).1 (x, y) := by
    rw [hAe, hBe, hee]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      (s4c_scale_lt_iff (e := e) (a := u * (A g).1 (x, y))
        (b := (B g).1 (x, y)) he)
  simp only [GEvent, mem_ofPred_eq, hlow, hhigh, hratio]

theorem s4c_ae_gEvent_normalize
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B) (hd : 2 ≤ d)
    (u β : ℝ) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ ω ∂P, h ω ∈ GEvent A B ξ Q u β R ↔
      addConst (h ω) (-sphereAvg (h ω) 1 0) ∈ GEvent A B ξ Q u β R := by
  have hd1 : 1 ≤ d := by omega
  filter_upwards [hA.ae_apply_addFun_const hh.isLGFPlusCont,
    hB.ae_apply_addFun_const hh.isLGFPlusCont,
    hh.ae_exists_tendsto_sphereAvgSeq hd hR 0] with ω hwA hwB hc
  obtain ⟨_, hconv⟩ := hc
  let c := -sphereAvg (h ω) 1 0
  apply s4c_gEvent_addConst A B ξ Q u β R (h ω) c
  · exact sphereAvg_addConst_of_tendsto hd1 hconv c
  · intro x y
    simpa only [addFun_const] using hwA c x y
  · intro x y
    simpa only [addFun_const] using hwB c x y

/-- D-LT for the Borel ratio event at a fixed radius. -/
theorem s4c_gEvent_law_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (h : Ω → DistRd d) (h' : Ω' → DistRd d)
    (hh : IsWholeSpaceLGF h P) (hh' : IsWholeSpaceLGF h' P')
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B) (hd : 2 ≤ d)
    (u β : ℝ) {R : ℝ} (hR : 0 < R) :
    P (h ⁻¹' GEvent A B ξ Q u β R) =
      P' (h' ⁻¹' GEvent A B ξ Q u β R) := by
  let N : Ω → DistRd d :=
    fun ω => addConst (h ω) (-sphereAvg (h ω) 1 0)
  let N' : Ω' → DistRd d :=
    fun ω => addConst (h' ω) (-sphereAvg (h' ω) 1 0)
  have hm : Measurable N :=
    (hh.addConst (((measurable_sphereAvg_left (d := d) 1 0).comp
      hh.measurable).neg)).measurable
  have hm' : Measurable N' :=
    (hh'.addConst (((measurable_sphereAvg_left (d := d) 1 0).comp
      hh'.measurable).neg)).measurable
  let E := GEvent A B ξ Q u β R
  have hE : MeasurableSet E := measurableSet_GEvent hA.measurable hB.measurable
  have heq : P.map N = P'.map N' := map_normalizedLGF_eq hd hh hh'
  have hsets : h ⁻¹' E =ᵐ[P] N ⁻¹' E := by
    filter_upwards [s4c_ae_gEvent_normalize P h hh hA hB hd u β hR] with ω hw
    exact propext hw
  have hsets' : h' ⁻¹' E =ᵐ[P'] N' ⁻¹' E := by
    filter_upwards [s4c_ae_gEvent_normalize P' h' hh' hA hB hd u β hR] with ω hw
    exact propext hw
  calc
    P (h ⁻¹' E) = P (N ⁻¹' E) := measure_congr hsets
    _ = (P.map N) E := (Measure.map_apply hm hE).symm
    _ = (P'.map N') E := by rw [heq]
    _ = P' (N' ⁻¹' E) := Measure.map_apply hm' hE
    _ = P' (h' ⁻¹' E) := measure_congr hsets'.symm

end HigherDimLQGMetric
