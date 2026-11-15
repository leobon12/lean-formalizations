import InteractingSLE.Spec.Dimension.Finite
import InteractingSLE.Spec.Sec4.RepulsionNoncollision
import InteractingSLE.Spec.Sec4.SpecialHeights
import QuantumZipper.Proofs.RS.TipB

/-!
# Aux. lemma 24: a real trace contact has a force collision (§4.2)

Packet PROVE-SEC4-B3. Specification, Aux. lemma 24 and its proof (`source/spec/p097-144.md`, L640–L644,
p. 124): "Let `0 < κ < 4`, and consider an integrated finite-force `SLE_κ(ρ)` evolution with its geometric
force coordinates. Assume that its available trace is continuous on the stopped interval in question. At every
strictly positive time at which this trace lies on the original real boundary, at least one force coordinate
equals the driver. With no force coordinates, there is no such contact. The assertion includes a continuous
finite terminal endpoint at which the force coordinates have limits."

Proof as in the source: localize after a deterministic rational time `a` while all force gaps stay at least
`1/(n+1)` and for elapsed time at most `n`. Stopped Girsanov makes the future driver equal to `√κ X` with the law
of `X` absolutely continuous with respect to a Brownian law (`Dimension.exists_brownian_localization`, PROVE-T11-DU2).
The ordinary `SLE_κ` trace (`κ ≤ 4`) is in the open half-plane at every positive time
(`QuantumZipper.RS.ae_sleTrace_simple_of_le_four`, [RS05, Theorem 6.1]); transferred through `≪`, the future trace
`γ^a` of the localized driver is in `ℍ` at positive times. Its pullback by the inverse mapping-out function
`F_a = f_a⁻¹` of the own prefix (`QuantumZipper.RS.trace_add_of_tendsto_shift`) is the original trace and stays in
`ℍ`. A positive real-contact time with all gaps nonzero lies in one of the countably many localizations
(continuity of the gaps). At the end of a stopped interval the trace is the limit of these pullbacks.

At a finite terminal endpoint `ζ` of the evolution itself, the continuation threshold holds for every left limit
of the state (maximality of the lifetime), and the threshold forces a collision (`ThresholdCondition` with an empty
collision group is `0 ≤ −2`, false).

## Main results

* `eq_fwdMapInv_trace_of_shift_eq`, `mem_H_of_shift_eq`: the pathwise core (pullback of the future trace);
* `IsIntegratedSLEEvolution.ae_mem_H_of_forall_ne`: nonzero force gaps at a positive time `t ≤ T` (`t < ζ`) put
  every continuous generating trace on `[0, T]` in `ℍ` at `t`;
* `IsIntegratedSLEEvolution.ae_exists_eq_of_im_eq_zero`: **Aux. lemma 24** (`κ ≤ 4`, contains the source's
  `0 < κ < 4`), every stopped interval `[0, T]`, `T ≤ ζ`;
* `IsIntegratedSLEPath.exists_eq_of_tendsto_lifetime`: the terminal endpoint `t = ζ < ∞`;
* `IsIntegratedSLEEvolution.ae_mem_H_of_hasAdmissiblePartialSums`, `…_of_cond44`: with Aux. lemma 6
  (noncollision), the non-boundary-intersecting weights keep every continuous trace in `ℍ` at all positive times
  (the hypothesis `η((0, S]) ⊂ ℍ` of Aux. lemma 23, and the exclusion of `∂_L𝒮` after the start in Remark 4.8 (a)).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Sec4

open QuantumZipper QuantumZipper.RS InteractingSLE.Dimension

/-! ### Pathwise core: pullback of the localized future trace -/

section Pathwise

variable {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- The inverse map at time `a` of the driver read on `ℝ` is that of any frozen driver `frozenDrive w t₂`,
`a < t₂`. -/
theorem fwdMapInv_eq_frozenDrive {a : ℝ≥0} {t₂ : ℝ} (hat₂ : (a : ℝ) < t₂) :
    fwdMapInv (fun s : ℝ => w s.toNNReal) a = fwdMapInv (frozenDrive w t₂) a :=
  fwdMapInv_eq_of_eqOn (NNReal.coe_nonneg a) hat₂ fun _ hr => (frozenDrive_eq hr).symm

/-- **Pullback of the localized future trace** (proof of Aux. lemma 24: "Its pullback by the own inverse
mapping-out function stays in the open original active component"). Let `η` be a generating trace of `w`
before `T`. If the future driver after `a` agrees on `[a, t]` (`t < T`) with a continuous driver `f`
(`w(a + s) − w(a) = f(s)`), whose trace at `t − a` is a radial limit lying in `ℍ`, then
`η(t) = F_a(γ^f(t − a))`, where `F_a` is the inverse mapping-out function of the prefix. -/
theorem eq_fwdMapInv_trace_of_shift_eq (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : f 0 = 0) {a t : ℝ≥0} (hat : a ≤ t) (htT : (t : ℝ≥0∞) < T)
    (hid : ∀ s : ℝ≥0, a + s ≤ t → w (a + s) - w a = f s)
    (hlim : Tendsto (fun y : ℝ => fwdMapInv f ((t : ℝ) - a) (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (trace f ((t : ℝ) - a))))
    (hH : trace f ((t : ℝ) - a) ∈ H) :
    η t = fwdMapInv (fun s : ℝ => w s.toNNReal) a (trace f ((t : ℝ) - a)) := by
  obtain ⟨t₂, htt₂, ht₂T⟩ := exists_real_btwn_of_lt htT
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg _).trans htt₂.le
  set W' := frozenDrive w t₂ with hW'def
  have hW' : Continuous W' := continuous_frozenDrive_of_lt hw ht₂T
  have hW'0 : W' 0 = 0 := by rw [hW'def, frozenDrive_zero ht₂, hw0]
  have hL := hη.isLoewnerTraceLT ht₂T
  set A : ℝ := (a : ℝ) with hA
  set u : ℝ := (t : ℝ) - A with hu
  have hA0 : 0 ≤ A := NNReal.coe_nonneg _
  have hat' : A ≤ t := by exact_mod_cast hat
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  have hAu : A + u = t := by rw [hu]; ring
  have hAt₂ : A < t₂ := lt_of_le_of_lt hat' htt₂
  have hEq : EqOn (shiftDrive W' A) f (Icc 0 u) := by
    intro r hr
    have hr0 : 0 ≤ r := hr.1
    have h1 : A + r ∈ Icc (0 : ℝ) t₂ := ⟨add_nonneg hA0 hr0, by linarith [hr.2]⟩
    have h2 : A ∈ Icc (0 : ℝ) t₂ := ⟨hA0, hAt₂.le⟩
    have hle : a + r.toNNReal ≤ t := by
      rw [← NNReal.coe_le_coe, NNReal.coe_add, Real.coe_toNNReal _ hr0]
      linarith [hr.2]
    simp only [shiftDrive]
    rw [hW'def, frozenDrive_eq h1, frozenDrive_eq h2, hA, toNNReal_coe_add hr0, Real.toNNReal_coe,
      hid _ hle, Real.coe_toNNReal _ hr0]
  have hS' : Continuous (shiftDrive W' A) := continuous_shiftDrive hW' A
  have htr : trace (shiftDrive W' A) u = trace f u :=
    trace_congr_drive hS' (shiftDrive_zero _ _) hf hf0 hu0 hEq
  have hInv : EqOn (fwdMapInv (shiftDrive W' A) u) (fwdMapInv f u) H :=
    RegCont.fwdMapInv_congr hS' (shiftDrive_zero _ _) hf hf0 hEq ⟨hu0, le_rfl⟩
  have hlimS : Tendsto (fun y : ℝ => fwdMapInv (shiftDrive W' A) u (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (trace (shiftDrive W' A) u)) := by
    rw [htr]
    refine hlim.congr' (eventually_mem_nhdsWithin.mono fun y hy => ?_)
    exact (hInv (mul_I_mem_H hy)).symm
  have hpH : trace (shiftDrive W' A) u ∈ H := htr ▸ hH
  have key := (trace_add_of_tendsto_shift hW' hW'0 hA0 hu0 hpH hlimS).2.2
  have htrη := hL.trace_eq hW' hW'0 (add_nonneg hA0 hu0) (by rw [hAu]; exact htt₂)
  rw [hAu, Real.toNNReal_coe] at htrη
  rw [hAu] at key
  rw [← htrη]
  change trace W' (t : ℝ) = _
  rw [key, htr]
  exact (congrFun (fwdMapInv_eq_frozenDrive (w := w) hAt₂) _).symm

/-- **The localized trace point is interior, up to and including the end of the stopped interval** (proof
of Aux. lemma 24). Let `η` be a generating trace of `w` on `[0, T]`, `a < t₁ ≤ T`, and let the future driver
after `a` agree on `[a, t₁]` with a continuous driver `f` whose trace has radial limits, is continuous and lies
in `ℍ` at all positive times. Then `η(t₁) ∈ ℍ`. For `t₁ < T` this is the pullback identity; for `t₁ = T` the
pullback `F_a(γ^f(t − a))` is continuous in `t` and `η` is continuous at `T`. -/
theorem mem_H_of_shift_eq (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : f 0 = 0)
    (hlim : ∀ u : ℝ, 0 ≤ u → Tendsto (fun y : ℝ => fwdMapInv f u (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (trace f u)))
    (hcont : ContinuousOn (trace f) (Ici 0)) (hH : ∀ u : ℝ, 0 < u → trace f u ∈ H)
    {a t₁ : ℝ≥0} (hat₁ : a < t₁) (ht₁T : (t₁ : ℝ≥0∞) ≤ T)
    (hid : ∀ s : ℝ≥0, a + s ≤ t₁ → w (a + s) - w a = f s) : η t₁ ∈ H := by
  have hat₁' : (a : ℝ) < t₁ := by exact_mod_cast hat₁
  have hpull : ∀ t : ℝ≥0, a < t → t ≤ t₁ → (t : ℝ≥0∞) < T →
      η t = fwdMapInv (fun s : ℝ => w s.toNNReal) a (trace f ((t : ℝ) - a)) :=
    fun t hat htt₁ htT => eq_fwdMapInv_trace_of_shift_eq hη hw hw0 hf hf0 hat.le htT
      (fun s hs => hid s (hs.trans htt₁)) (hlim _ (sub_nonneg.2 (by exact_mod_cast hat.le)))
      (hH _ (sub_pos.2 (by exact_mod_cast hat)))
  -- the inverse map at `a`, through a frozen continuous driver
  set t₂ : ℝ := ((a : ℝ) + t₁) / 2 with ht₂
  have hat₂ : (a : ℝ) < t₂ := by rw [ht₂]; linarith
  have ht₂t₁ : t₂ < t₁ := by rw [ht₂]; linarith
  have ht₂0 : 0 ≤ t₂ := (NNReal.coe_nonneg a).trans hat₂.le
  have ht₂T : ENNReal.ofReal t₂ < T := by
    refine lt_of_lt_of_le ?_ ht₁T
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast (lt_of_le_of_lt ht₂0 ht₂t₁))).2 ht₂t₁
  have hW' : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hw ht₂T
  have hW'0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂0, hw0]
  have hF : fwdMapInv (fun s : ℝ => w s.toNNReal) a = fwdMapInv (frozenDrive w t₂) a :=
    fwdMapInv_eq_frozenDrive hat₂
  set p := trace f ((t₁ : ℝ) - a) with hpdef
  have hp : p ∈ H := hH _ (sub_pos.2 hat₁')
  have hFH : fwdMapInv (fun s : ℝ => w s.toNNReal) a p ∈ H := by
    rw [hF]; exact fwdMapInv_mem_H hW' hW'0 (NNReal.coe_nonneg a) hp
  rcases lt_or_eq_of_le ht₁T with hlt | heq
  · rw [hpull t₁ hat₁ le_rfl hlt]; exact hFH
  suffices hη₁ : η t₁ = fwdMapInv (fun s : ℝ => w s.toNNReal) a p by rw [hη₁]; exact hFH
  have : NeBot (𝓝[<] t₁) := nhdsLT_neBot_of_exists_lt ⟨a, hat₁⟩
  have h1 : Tendsto η (𝓝[<] t₁) (𝓝 (η t₁)) := by
    refine (hη.2.1 t₁ ht₁T).tendsto.mono_left (nhdsWithin_mono _ fun t (ht : t < t₁) => ?_)
    show (t : ℝ≥0∞) ≤ T
    rw [← heq]; exact ENNReal.coe_le_coe.2 ht.le
  have hg : Tendsto (fun t : ℝ≥0 => (t : ℝ) - a) (𝓝[<] t₁) (𝓝[Ici 0] ((t₁ : ℝ) - a)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((NNReal.continuous_coe.sub continuous_const).tendsto t₁).mono_left nhdsWithin_le_nhds
    · filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds hat₁)] with t ht
      have ht' : (a : ℝ) ≤ t := by exact_mod_cast ht.le
      exact mem_Ici.2 (sub_nonneg.2 ht')
  have hc : Tendsto (fun t : ℝ≥0 => fwdMapInv (fun s : ℝ => w s.toNNReal) a
      (trace f ((t : ℝ) - a))) (𝓝[<] t₁) (𝓝 (fwdMapInv (fun s : ℝ => w s.toNNReal) a p)) := by
    rw [hF]
    exact (continuousAt_fwdMapInv hW' hW'0 (NNReal.coe_nonneg a) hp).tendsto.comp
      ((hcont _ (sub_nonneg.2 hat₁'.le)).tendsto.comp hg)
  have h2 : Tendsto η (𝓝[<] t₁) (𝓝 (fwdMapInv (fun s : ℝ => w s.toNNReal) a p)) := by
    refine hc.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds hat₁), self_mem_nhdsWithin] with t hat htt₁
    refine (hpull t hat (le_of_lt htt₁) ?_).symm
    rw [← heq]; exact ENNReal.coe_lt_coe.2 htt₁
  exact tendsto_nhds_unique h1 h2

/-- **No return to the old trace after a localized time** (proof of Aux. lemma 25: "Its future cannot enter the
interior of that old filled hull … so it never returns to the old trace at all", in the case of a localized future
in `ℍ`). If the future driver after `a` agrees on `[a, t]` (`a < t < T`) with a continuous driver whose trace is a
radial limit lying in `ℍ` at positive times, then `η(t) = F_a(γ^f(t − a)) ∉ K_a`, while every interior point
`η(s)`, `s ≤ a`, lies in `K_a`; so `η(s) ≠ η(t)`. -/
theorem ne_of_le_of_shift_eq (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : f 0 = 0)
    (hlim : ∀ u : ℝ, 0 ≤ u → Tendsto (fun y : ℝ => fwdMapInv f u (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (trace f u)))
    (hfH : ∀ u : ℝ, 0 < u → trace f u ∈ H) {a s t : ℝ≥0} (hsa : s ≤ a) (hat : a < t)
    (htT : (t : ℝ≥0∞) < T) (hid : ∀ r : ℝ≥0, a + r ≤ t → w (a + r) - w a = f r)
    (hsH : η s ∈ H) : η s ≠ η t := by
  have hat' : (a : ℝ) < t := by exact_mod_cast hat
  have hp : trace f ((t : ℝ) - a) ∈ H := hfH _ (sub_pos.2 hat')
  have hrep := eq_fwdMapInv_trace_of_shift_eq hη hw hw0 hf hf0 hat.le htT hid
    (hlim _ (sub_nonneg.2 hat'.le)) hp
  have haT : (a : ℝ≥0∞) < T := lt_trans (ENNReal.coe_lt_coe.2 hat) htT
  obtain ⟨t₂, hat₂, ht₂T⟩ := exists_real_btwn_of_lt haT
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg a).trans hat₂.le
  have hW' : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hw ht₂T
  have hW'0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
  have hK : QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) a =
      QuantumZipper.fwdHull (frozenDrive w t₂) a :=
    fwdHull_eq_of_eqOn (NNReal.coe_nonneg a) hat₂ fun _ hr => (frozenDrive_eq hr).symm
  -- the new point is outside the old hull
  have hnot : η t ∉ QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) a := by
    rw [hrep, fwdMapInv_eq_frozenDrive hat₂, hK]
    have hmem : fwdMapInv (frozenDrive w t₂) a (trace f ((t : ℝ) - a)) ∈
        fwdMapInv (frozenDrive w t₂) a '' H := mem_image_of_mem _ hp
    rw [image_fwdMapInv_H hW' hW'0 (NNReal.coe_nonneg a)] at hmem
    exact hmem.2
  -- the old interior point is in the old hull
  have hsK : η s ∈ QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) a := by
    obtain ⟨⟨z, -, hcc⟩, -⟩ := hη.2.2 a haT
    by_contra hns
    have hmem : η s ∈ H \ QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) a := ⟨hsH, hns⟩
    rw [← hcc] at hmem
    exact (connectedComponentIn_subset _ _ hmem).2 ⟨s, ⟨zero_le, hsa⟩, rfl⟩
  intro heq
  exact hnot (heq ▸ hsK)

end Pathwise

/-! ### Aux. lemma 24 -/

section Evolution

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The localizations of Aux. lemma 24, on one almost sure event.** Let `0 < κ ≤ 4`. Almost surely, for every
time `t₁ < ζ` at which all force gaps are nonzero and every `b < t₁`, there are a start `a ∈ (b, t₁)` and a
continuous driver `f` (`f 0 = 0`), whose trace has radial limits, is continuous and lies in `ℍ` at all positive
times, such that the future driver after `a` agrees with `f` on `[a, t₁]`. (Countably many localizations
`exists_brownian_localization` with rational start and `n ∈ ℕ`; the ordinary trace property is transferred
through `≪`.) -/
theorem _root_.InteractingSLE.IsIntegratedSLEEvolution.ae_exists_localization
    [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ t₁ : ℝ≥0, (t₁ : ℝ≥0∞) < ζ ω → (∀ i, W t₁ ω ≠ VL i t₁ ω) →
      (∀ i, W t₁ ω ≠ VR i t₁ ω) → ∀ b : ℝ≥0, b < t₁ → ∃ a : ℝ≥0, b < a ∧ a < t₁ ∧
        ∃ f : ℝ → ℝ, Continuous f ∧ f 0 = 0 ∧
          (∀ u : ℝ, 0 ≤ u → Tendsto (fun y : ℝ => fwdMapInv f u (y * Complex.I)) (𝓝[>] 0)
            (𝓝 (trace f u))) ∧
          ContinuousOn (trace f) (Ici 0) ∧ (∀ u : ℝ, 0 < u → trace f u ∈ H) ∧
          ∀ s : ℝ≥0, a + s ≤ t₁ → W (a + s) ω - W a ω = f s := by
  have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hloc := fun p : ℚ × ℕ =>
    exists_brownian_localization hκ hE ((p.1 : ℝ).toNNReal) (p.2 : ℝ≥0) (hδ p.2)
  choose X hXm μ hμprob hμBM hac hXeq using hloc
  have hgood : ∀ p : ℚ × ℕ, ∀ᵐ ω ∂P, (∀ u : ℝ, 0 ≤ u → Tendsto
        (fun y : ℝ => fwdMapInv (drive κ canonBM (X p ω)) u (y * Complex.I)) (𝓝[>] 0)
        (𝓝 (trace (drive κ canonBM (X p ω)) u))) ∧
      ContinuousOn (trace (drive κ canonBM (X p ω))) (Ici 0) ∧
      HasInteriorDimBound (interiorDimBound κ) (drive κ canonBM (X p ω)) := fun p => by
    have := hμprob p
    exact ae_trace_good_of_absolutelyContinuous hκ (by linarith) (hXm p).aemeasurable (hμBM p)
      (hac p)
  have hsimple : ∀ p : ℚ × ℕ, ∀ᵐ ω ∂P, ∀ u : ℝ, 0 < u →
      trace (drive κ canonBM (X p ω)) u ∈ H := fun p => by
    have := hμprob p
    have h := ae_sleTrace_simple_of_le_four (hμBM p) hκ hκ4
    exact ae_of_ae_map (hXm p).aemeasurable ((hac p).ae_le (h.mono fun f hf u hu => hf.2 u hu))
  filter_upwards [ae_all_iff.2 hgood, ae_all_iff.2 hsimple, ae_all_iff.2 hXeq, hE.2.2.2.2] with
    ω hg hs hx hp t₁ ht₁ζ hgL hgR b hbt₁
  have hw : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := hp.2.2.2.1
  obtain ⟨ε, hε, hεgap⟩ := exists_gap_half_lt hw hp.2.2.2.2.1 hp.2.2.2.2.2.1 ht₁ζ
  -- a rational start `a ∈ (max (t₁ − ε) b, t₁)`
  have hbt₁' : (b : ℝ) < t₁ := by exact_mod_cast hbt₁
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max ((t₁ : ℝ) - ε) b < t₁ from
    max_lt (by linarith) hbt₁')
  have hbq : (b : ℝ) < q := lt_of_le_of_lt (le_max_right _ _) hq1
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (NNReal.coe_nonneg b) hbq
  set a : ℝ≥0 := (q : ℝ).toNNReal with ha
  have haq : (a : ℝ) = q := Real.coe_toNNReal _ hq0.le
  have hat₁ : a < t₁ := by rw [← NNReal.coe_lt_coe, haq]; exact hq2
  have hba : b < a := by rw [← NNReal.coe_lt_coe, haq]; exact hbq
  -- `n` large: small gap threshold and long elapsed time
  have hevn : ∀ᶠ n : ℕ in atTop, ((∀ i, 1 / ((n : ℝ) + 1) < |W t₁ ω - VL i t₁ ω| / 2) ∧
      ∀ i, 1 / ((n : ℝ) + 1) < |W t₁ ω - VR i t₁ ω| / 2) ∧ t₁ - a ≤ (n : ℝ≥0) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine ((Filter.eventually_all.2 fun i => h0.eventually (gt_mem_nhds ?_)).and
      (Filter.eventually_all.2 fun i => h0.eventually (gt_mem_nhds ?_))).and
      ((tendsto_natCast_atTop_atTop (R := ℝ≥0)).eventually_ge_atTop (t₁ - a))
    · exact half_pos (abs_pos.2 (sub_ne_zero.2 (hgL i)))
    · exact half_pos (abs_pos.2 (sub_ne_zero.2 (hgR i)))
  obtain ⟨n, ⟨hnL, hnR⟩, hnT⟩ := hevn.exists
  have hid : ∀ t : ℝ≥0, a + t ≤ t₁ →
      W (a + t) ω - W a ω = drive κ canonBM (X (q, n) ω) (t : ℝ) := by
    intro t ht
    have htn : t ≤ (n : ℝ≥0) := by
      refine le_trans ?_ hnT
      rw [le_tsub_iff_left hat₁.le]
      exact ht
    have htζ : ((a + t : ℝ≥0) : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) ht₁ζ
    rw [show drive κ canonBM (X (q, n) ω) (t : ℝ) = Real.sqrt κ * (X (q, n) ω).1 t by
      simp only [drive, canonBM, Real.toNNReal_coe]]
    refine hx (q, n) t htn htζ fun s hs1 hs2 => ?_
    have hsd : dist s t₁ < ε := by
      rw [NNReal.dist_eq, abs_lt]
      have h1 : (a : ℝ) ≤ s := by exact_mod_cast hs1
      have h2 : (s : ℝ) ≤ t₁ := by exact_mod_cast hs2.trans ht
      constructor <;> [linarith [le_max_left ((t₁ : ℝ) - ε) b]; linarith]
    obtain ⟨hL, hR⟩ := hεgap s hsd
    constructor
    · intro i
      rcases hL i with h | h
      · exact (hnL i).le.trans h.le
      · exact absurd h (hgL i)
    · intro i
      rcases hR i with h | h
      · exact (hnR i).le.trans h.le
      · exact absurd h (hgR i)
  have hf0 : drive κ canonBM (X (q, n) ω) 0 = 0 := by
    have h := hid 0 (by rw [add_zero]; exact hat₁.le)
    rw [add_zero, sub_self, NNReal.coe_zero] at h
    exact h.symm
  exact ⟨a, hba, hat₁, drive κ canonBM (X (q, n) ω), continuous_drive_path (X (q, n) ω).2, hf0,
    (hg (q, n)).1, (hg (q, n)).2.1, hs (q, n), hid⟩

/-- **Nonzero force gaps keep the trace in `ℍ`** (Aux. lemma 24, contrapositive form). Let `0 < κ ≤ 4` and let
`(W, V, B)` be an integrated finite-force `SLE_κ(ρ)` evolution with lifetime `ζ`. Almost surely, for every
stopped interval `[0, T]`, `T ≤ ζ`, on which a continuous generating trace `η` is available, and every time
`0 < t ≤ T` with `t < ζ` at which all force gaps are nonzero, `η(t) ∈ ℍ`. -/
theorem _root_.InteractingSLE.IsIntegratedSLEEvolution.ae_mem_H_of_forall_ne
    [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0∞, T ≤ ζ ω → ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η →
      ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ T → (t : ℝ≥0∞) < ζ ω →
        (∀ i, W t ω ≠ VL i t ω) → (∀ i, W t ω ≠ VR i t ω) → η t ∈ H := by
  filter_upwards [hE.ae_exists_localization hκ hκ4, hE.2.2.2.2] with ω hloc hp T hTζ η hη t₁ ht₁
    ht₁T ht₁ζ hgL hgR
  have hwT : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < T} :=
    hp.2.2.2.1.mono fun t ht => lt_of_lt_of_le ht hTζ
  obtain ⟨a, -, hat₁, f, hf, hf0, hlim, hcont, hH, hid⟩ := hloc t₁ ht₁ζ hgL hgR 0 ht₁
  exact mem_H_of_shift_eq hη hwT hp.1 hf hf0 hlim hcont hH hat₁ ht₁T hid

/-- **Aux. lemma 24** (a real trace contact has a force collision; `source/spec/p097-144.md` L640–L644,
p. 124). Let `0 < κ ≤ 4` (the source states `0 < κ < 4`) and let `(W, V, B)` be an integrated finite-force
`SLE_κ(ρ)` evolution with lifetime `ζ`. Almost surely, for every stopped interval `[0, T]`, `T ≤ ζ`, on which a
continuous generating trace `η` is available, at every time `0 < t ≤ T` with `t < ζ` at which `η(t)` lies on the
real line, at least one force coordinate equals the driver. The terminal endpoint `t = ζ < ∞` is
`IsIntegratedSLEPath.exists_eq_of_tendsto_lifetime`. -/
theorem _root_.InteractingSLE.IsIntegratedSLEEvolution.ae_exists_eq_of_im_eq_zero
    [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0∞, T ≤ ζ ω → ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η →
      ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ T → (t : ℝ≥0∞) < ζ ω → (η t).im = 0 →
        (∃ i, VL i t ω = W t ω) ∨ ∃ i, VR i t ω = W t ω := by
  filter_upwards [hE.ae_mem_H_of_forall_ne hκ hκ4] with ω h T hTζ η hη t ht htT htζ him
  by_contra hne
  rw [not_or, not_exists, not_exists] at hne
  have hH := h T hTζ η hη t ht htT htζ (fun i e => hne.1 i e.symm) fun i e => hne.2 i e.symm
  have hpos : (0 : ℝ) < (η t).im := hH
  rw [him] at hpos
  exact lt_irrefl _ hpos

/-- **Aux. lemma 24 with no force coordinates**: "With no force coordinates, there is no such contact." -/
theorem _root_.InteractingSLE.IsIntegratedSLEEvolution.ae_mem_H_of_fin_zero
    {xL ρL : Fin 0 → ℝ} {xR ρR : Fin 0 → ℝ} {VL VR : Fin 0 → ℝ≥0 → Ω → ℝ}
    [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0∞, T ≤ ζ ω → ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η →
      ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ T → (t : ℝ≥0∞) < ζ ω → η t ∈ H := by
  filter_upwards [hE.ae_mem_H_of_forall_ne hκ hκ4] with ω h T hTζ η hη t ht htT htζ
  exact h T hTζ η hη t ht htT htζ (fun i => i.elim0) fun i => i.elim0

end Evolution

/-! ### The terminal endpoint -/

/-- **A threshold state has a collision**: the continuation threshold at `(w, vL, vR)` puts some force
coordinate at `w` (an empty collision group has total weight `0 > −2`). -/
theorem exists_eq_of_thresholdCondition {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ}
    {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} (h : ForceWord.ThresholdCondition ρL ρR w vL vR) :
    (∃ i, vL i = w) ∨ ∃ i, vR i = w := by
  by_contra hne
  rw [not_or, not_exists, not_exists] at hne
  rcases h with h | h
  · rw [Finset.filter_false_of_mem fun i _ => hne.1 i, Finset.sum_empty] at h
    linarith
  · rw [Finset.filter_false_of_mem fun i _ => hne.2 i, Finset.sum_empty] at h
    linarith

/-- **Aux. lemma 24 at the terminal endpoint** ("The assertion includes a continuous finite terminal endpoint at
which the force coordinates have limits"): if the lifetime `ζ = T` is finite and positive and the state
`(w, vL, vR)` has a limit at `T⁻`, some limiting force coordinate equals the limiting driver (maximality of the
lifetime: the limit satisfies the continuation threshold). -/
theorem _root_.InteractingSLE.IsIntegratedSLEPath.exists_eq_of_tendsto_lifetime {a : ℝ} {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {T : ℝ≥0} (hT : 0 < T)
    (hTζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T)
      (𝓝 (w₀, vL₀, vR₀))) :
    (∃ i, vL₀ i = w₀) ∨ ∃ i, vR₀ i = w₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hthr⟩ := hp
  exact exists_eq_of_thresholdCondition (hthr T hT hTζ w₀ vL₀ vR₀ hlim)

/-! ### Non-boundary-intersecting weights -/

section NonBoundary

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Non-boundary-intersecting traces** (Aux. lemma 24 with Aux. lemma 6). Let `0 < κ ≤ 4` and let the ordered
force word have admissible partial sums (all amalgamated side partial sums at least `κ/2 − 2`). Almost surely the
lifetime is infinite and every continuous generating trace `η` on any interval `[0, T]` is in `ℍ` at every time
`0 < t ≤ T`. -/
theorem _root_.InteractingSLE.IsIntegratedSLEEvolution.ae_mem_H_of_hasAdmissiblePartialSums
    [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hword : IsOrderedForceWord xL xR)
    (hadm : HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ T : ℝ≥0∞, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η →
      ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ T → η t ∈ H := by
  filter_upwards [aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hword hadm hE,
    hE.ae_mem_H_of_forall_ne hκ hκ4] with ω h6 h24
  refine ⟨h6.1, fun T η hη t ht htT => ?_⟩
  have hTζ : T ≤ ζ ω := by rw [h6.1]; exact le_top
  have htζ : (t : ℝ≥0∞) < ζ ω := by rw [h6.1]; exact ENNReal.coe_lt_top
  exact h24 T hTζ η hη t ht htT htζ (fun i => ((h6.2 t ht).1 i).ne') fun i => ((h6.2 t ht).2 i).ne

/-- **Under (4.4) the trace never touches the boundary after the start** (§4.2: "the flow lines thus considered
(almost surely non-boundary intersecting)"): for `0 < κ < 4` and weights satisfying (4.4), almost surely the
lifetime is infinite and every continuous generating trace is in `ℍ` at all positive times. -/
theorem _root_.InteractingSLE.IsIntegratedSLEEvolution.ae_mem_H_of_cond44
    [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4) (hword : IsOrderedForceWord xL xR)
    (h44 : Cond44 κ ρL ρR) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ T : ℝ≥0∞, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η →
      ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ T → η t ∈ H :=
  hE.ae_mem_H_of_hasAdmissiblePartialSums hκ hκ4.le hword
    (hasAdmissiblePartialSums_of_cond44 hκ4 hword h44)

/-- (O2) on a stopped interval: nonzero force gaps at interior tips of a continuous generating trace on `[0, T]`,
`T ≤ ζ`, at times `t < T` (`Dimension.ne_of_mem_H_of_mark` with horizon `T`). -/
theorem _root_.InteractingSLE.IsIntegratedSLEPath.forall_ne_of_mem_H_of_le {a : ℝ} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞}
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ') {T : ℝ≥0∞} (hTζ : T ≤ ζ')
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w T η) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T)
    (hηt : η t ∈ H) : (∀ i, w t ≠ vL i t) ∧ ∀ i, w t ≠ vR i t := by
  obtain ⟨hw0, -, -, hwc, hvLc, hvRc, -, hvLw, hwvR, -, hgapL, hgapR, -, hvLeq, hvReq, hcolL,
    hcolR, -⟩ := hp
  have hlt : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → (s : ℝ≥0∞) < ζ' := fun s hs => lt_of_lt_of_le hs hTζ
  have hsub : {s : ℝ≥0 | (s : ℝ≥0∞) < T} ⊆ {s | (s : ℝ≥0∞) < ζ'} := fun s hs => hlt s hs
  have hnull : ∀ v : ℝ≥0 → ℝ,
      volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ' ∧ w s.toNNReal = v s.toNNReal} = 0 →
      volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < T ∧ w s.toNNReal = v s.toNNReal} = 0 :=
    fun v hv => measure_mono_null (fun r (hr : 0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < T ∧
      w r.toNNReal = v r.toNNReal) => (⟨hr.1, hlt _ hr.2.1, hr.2.2⟩ : 0 ≤ r ∧
        (r.toNNReal : ℝ≥0∞) < ζ' ∧ w r.toNNReal = v r.toNNReal)) hv
  exact ⟨fun i => ne_of_mem_H_of_mark hη (hwc.mono hsub) hw0 ((hvLc i).mono hsub)
      (Or.inr fun s hs => hvLw s (hlt s hs) i) (fun s hs => hgapL s (hlt s hs) i)
      (fun s hs => hvLeq s (hlt s hs) i) (hnull _ (hcolL i)) ht hηt,
    fun i => ne_of_mem_H_of_mark hη (hwc.mono hsub) hw0 ((hvRc i).mono hsub)
      (Or.inl fun s hs => hwvR s (hlt s hs) i) (fun s hs => hgapR s (hlt s hs) i)
      (fun s hs => hvReq s (hlt s hs) i) (hnull _ (hcolR i)) ht hηt⟩

/-- **Aux. lemma 25 for prefixes in the open half-plane** (simplicity of a continuous available prefix, in the
case without a real contact after the start). Let `0 < κ ≤ 4`. Almost surely, every continuous generating trace
`η` on a stopped interval `[0, T]`, `T ≤ ζ`, that lies in `ℍ` at every time `0 < t < T` is injective on `[0, T)`.
The general case (real contacts at force collisions, the endpoints `L_q, R_q` of the source's proof) needs the
boundary correspondence of the hull and Aux. lemma 99 (B1) (handoff PROVE-SEC4-B3). -/
theorem _root_.InteractingSLE.IsIntegratedSLEEvolution.ae_injOn_of_mem_H
    [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0∞, T ≤ ζ ω → ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η →
      (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < T → η t ∈ H) → InjOn η {t | (t : ℝ≥0∞) < T} := by
  filter_upwards [hE.ae_exists_localization hκ hκ4, hE.2.2.2.2] with ω hloc hp T hTζ η hη hH
  have hwT : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < T} :=
    hp.2.2.2.1.mono fun t ht => lt_of_lt_of_le ht hTζ
  have key : ∀ s t : ℝ≥0, s < t → (t : ℝ≥0∞) < T → η s ≠ η t := by
    intro s t hst htT heq
    have ht0 : 0 < t := lt_of_le_of_lt zero_le hst
    have htH : η t ∈ H := hH t ht0 htT
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs0 | hs0
    · rw [← hs0, hη.1] at heq
      rw [← heq] at htH
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from htH)
    · have htζ : (t : ℝ≥0∞) < ζ ω := lt_of_lt_of_le htT hTζ
      obtain ⟨hgL, hgR⟩ := hp.forall_ne_of_mem_H_of_le hTζ hη htT htH
      obtain ⟨a, hsa, hat, f, hf, hf0, hlim, -, hfH, hid⟩ := hloc t htζ hgL hgR s hst
      exact ne_of_le_of_shift_eq hη hwT hp.1 hf hf0 hlim hfH hsa.le hat htT hid
        (hH s hs0 (lt_trans (ENNReal.coe_lt_coe.2 hst) htT)) heq
  intro s hs t ht heq
  rcases lt_trichotomy s t with h | h | h
  · exact absurd heq (key s t h ht)
  · exact h
  · exact absurd heq.symm (key t s h hs)

/-- **Simplicity under (4.4)** (Aux. lemma 25 in the non-boundary-intersecting regime of §4.2): for `0 < κ < 4`
and weights satisfying (4.4), almost surely every continuous generating trace on any interval `[0, T]` is
injective on `[0, T)` and in `ℍ` at all positive times. -/
theorem _root_.InteractingSLE.IsIntegratedSLEEvolution.ae_injOn_of_cond44
    [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4) (hword : IsOrderedForceWord xL xR)
    (h44 : Cond44 κ ρL ρR) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ T : ℝ≥0∞, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η →
      InjOn η {t | (t : ℝ≥0∞) < T} ∧ ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ T → η t ∈ H := by
  filter_upwards [hE.ae_mem_H_of_cond44 hκ hκ4 hword h44, hE.ae_injOn_of_mem_H hκ hκ4.le] with
    ω h1 h2
  refine ⟨h1.1, fun T η hη => ⟨h2 T (by rw [h1.1]; exact le_top) η hη fun t ht htT =>
    h1.2 T η hη t ht htT.le, h1.2 T η hη⟩⟩

end NonBoundary

end InteractingSLE.Sec4
