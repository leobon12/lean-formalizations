/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AssemblyMeasurable
import InteractingSLE.Spec.Sec2.AssemblyPathwise
import InteractingSLE.Spec.Sec2.CriticalLifetime
import QuantumZipper.Proofs.RS.TransienceCanon

/-!
# Theorem 2.2 assembly: uniqueness in law for separated force words

Packet PROVE-SEC2-PATCH. **Theorem 2.2, uniqueness in law** (the frozen
`IsIntegratedSLEEvolution.measure_killedState_eq`) for every force word whose sides are strictly
separated (`∀ i j, xL i < xR j`; every word except those with a left and a right mark both at
`0`), for all weights: `measure_killedState_eq_of_separated`.

Proof (added here; it replaces the source's iterated reverse-Girsanov argument for these words):

* every evolution, coded by `codeOf` (driving path = a continuous version of `B`, state killed at
  `ζ`), lies almost surely in the measurable relation `CRel` of canonical solution codes
  (`ae_codeOf_mem`; the clause `LimThr` is Aux. lemma 3, `ae_tendsto_threshold`);
* the projection `x ↦ x.1` to the driving-path code is injective on `CRel`
  (`injOn_fst_cRel`, from pathwise uniqueness `IsIntegratedSLEPath.eq_of_separated`), so by the
  Lusin–Souslin theorem the image `M` of `CRel ∩ {killed state ∈ A}` is a Borel set of
  driving-path codes, and the killed-state event is almost surely `{code of B ∈ M}`;
* the law of the code of a Brownian motion does not depend on the space
  (`QuantumZipper.RS.map_toCPath_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly

variable {nL nR : ℕ}

/-! ### Canonical codes -/

/-- A code is canonical when its state code is the initial value at time `0` and `0` at the
dyadic times `≥ ζ`. -/
def Canon (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (x : XCode nL nR) : Prop :=
  ∀ n k, (dyad n k = 0 → x.2.2.1 n k = 0 ∧ (∀ i, x.2.2.2.1 i n k = xL i) ∧
      ∀ j, x.2.2.2.2 j n k = xR j) ∧
    (dyad n k ≠ 0 → ¬ (dyad n k : ℝ≥0∞) < cζ x → x.2.2.1 n k = 0 ∧
      (∀ i, x.2.2.2.1 i n k = 0) ∧ ∀ j, x.2.2.2.2 j n k = 0)

theorem measurable_canon (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :
    Measurable fun x : XCode nL nR => Canon xL xR x := by
  have hw : ∀ n k, Measurable fun x : XCode nL nR => x.2.2.1 n k := fun n k =>
    (measurable_code n k).comp measurable_code_w
  have hL : ∀ i n k, Measurable fun x : XCode nL nR => x.2.2.2.1 i n k := fun i n k =>
    (measurable_code n k).comp (measurable_code_vL i)
  have hR : ∀ j n k, Measurable fun x : XCode nL nR => x.2.2.2.2 j n k := fun j n k =>
    (measurable_code n k).comp (measurable_code_vR j)
  unfold Canon
  refine Measurable.forall fun n => Measurable.forall fun k => Measurable.and ?_ ?_
  · exact measurable_const_imp _ ((measurable_eq_real (hw n k) measurable_const).and
      ((Measurable.forall fun i => measurable_eq_real (hL i n k) measurable_const).and
        (Measurable.forall fun j => measurable_eq_real (hR j n k) measurable_const)))
  · exact measurable_const_imp _ ((measurable_coe_lt _ measurable_cζ).not.imp
      ((measurable_eq_real (hw n k) measurable_const).and
      ((Measurable.forall fun i => measurable_eq_real (hL i n k) measurable_const).and
        (Measurable.forall fun j => measurable_eq_real (hR j n k) measurable_const))))

/-- Canonical solution codes. -/
def CRel (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    Set (XCode nL nR) :=
  Rel a xL xR ρL ρR ∩ {x | Canon xL xR x}

theorem measurableSet_cRel (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) : MeasurableSet (CRel a xL xR ρL ρR) :=
  (measurableSet_rel a xL xR ρL ρR).inter (measurableSet_setOfPred.2 (measurable_canon xL xR))

/-- A good canonical code is determined by its driving code, lifetime and decoded state. -/
theorem code_eq {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {x x' : XCode nL nR} (hx : Good x)
    (hx' : Good x') (hc : Canon xL xR x) (hc' : Canon xL xR x') (hb : x.1 = x'.1)
    (hζ : cζ x = cζ x') (hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → cw x t = cw x' t)
    (hL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → ∀ i, cvL x i t = cvL x' i t)
    (hR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → ∀ j, cvR x j t = cvR x' j t) : x = x' := by
  obtain ⟨b, ζ, cw₀, cL, cR⟩ := x
  obtain ⟨b', ζ', cw₀', cL', cR'⟩ := x'
  simp only at hb
  have hζ' : ζ = ζ' := hζ
  subst hb hζ'
  have key : ∀ n k, cw₀ n k = cw₀' n k ∧ (∀ i, cL i n k = cL' i n k) ∧ ∀ j, cR j n k = cR' j n k := by
    intro n k
    by_cases h0 : dyad n k = 0
    · obtain ⟨a1, a2, a3⟩ := (hc n k).1 h0
      obtain ⟨b1, b2, b3⟩ := (hc' n k).1 h0
      exact ⟨a1.trans b1.symm, fun i => (a2 i).trans (b2 i).symm,
        fun j => (a3 j).trans (b3 j).symm⟩
    · by_cases hlt : (dyad n k : ℝ≥0∞) < ζ
      · have u1 : UC cw₀ (dyad n k) := (hx.2 n k hlt).1
        have u2 : ∀ i, UC (cL i) (dyad n k) := (hx.2 n k hlt).2.1
        have u3 : ∀ j, UC (cR j) (dyad n k) := (hx.2 n k hlt).2.2
        have u1' : UC cw₀' (dyad n k) := (hx'.2 n k hlt).1
        have u2' : ∀ i, UC (cL' i) (dyad n k) := (hx'.2 n k hlt).2.1
        have u3' : ∀ j, UC (cR' j) (dyad n k) := (hx'.2 n k hlt).2.2
        refine ⟨?_, fun i => ?_, fun j => ?_⟩
        · rw [← u1.dec_dyad le_rfl, ← u1'.dec_dyad le_rfl]; exact hw _ hlt
        · rw [← (u2 i).dec_dyad le_rfl, ← (u2' i).dec_dyad le_rfl]; exact hL _ hlt i
        · rw [← (u3 j).dec_dyad le_rfl, ← (u3' j).dec_dyad le_rfl]; exact hR _ hlt j
      · obtain ⟨a1, a2, a3⟩ := (hc n k).2 h0 hlt
        obtain ⟨b1, b2, b3⟩ := (hc' n k).2 h0 hlt
        exact ⟨a1.trans b1.symm, fun i => (a2 i).trans (b2 i).symm,
          fun j => (a3 j).trans (b3 j).symm⟩
  have e1 : cw₀ = cw₀' := funext fun n => funext fun k => (key n k).1
  have e2 : cL = cL' := funext fun i => funext fun n => funext fun k => (key n k).2.1 i
  have e3 : cR = cR' := funext fun j => funext fun n => funext fun k => (key n k).2.2 j
  rw [e1, e2, e3]

/-- **Injectivity of the driving-path projection on canonical solution codes** (pathwise
uniqueness). -/
theorem injOn_fst_cRel {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hsep : ∀ i j, xL i < xR j) :
    InjOn Prod.fst (CRel a xL xR ρL ρR) := by
  rintro x ⟨⟨hg, -, hp⟩, hc⟩ x' ⟨⟨hg', -, hp'⟩, hc'⟩ hb
  have hbd : cb x' = cb x := by unfold cb; rw [hb]
  rw [hbd] at hp'
  obtain ⟨hζ, hag⟩ := IsIntegratedSLEPath.eq_of_separated hsep hp hp'
  exact code_eq hg hg' hc hc' hb hζ (fun t ht => (hag t ht).1) (fun t ht => (hag t ht).2.1)
    fun t ht => (hag t ht).2.2

/-! ### Codes of evolutions -/

/-- The killed code of a process: initial value `x₀` at time `0`, the process before `ζ`, `0`
afterwards. -/
def killedCode {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (x₀ : ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : PCode :=
  fun n k => if dyad n k = 0 then x₀ else if (dyad n k : ℝ≥0∞) < ζ ω then X (dyad n k) ω else 0

/-- The killed path behind `killedCode`. -/
def killedPath {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (x₀ : ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) (t : ℝ≥0) : ℝ :=
  if t = 0 then x₀ else if (t : ℝ≥0∞) < ζ ω then X t ω else 0

theorem killedCode_eq_enc {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (x₀ : ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) :
    killedCode X x₀ ζ ω = enc (killedPath X x₀ ζ ω) := rfl

/-- The code of an evolution, with a version `B'` of its Brownian motion. -/
def codeOf {Ω : Type*} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (B' : ℝ≥0 → Ω → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (ω : Ω) : XCode nL nR :=
  (enc (B' · ω), ζ ω, killedCode W 0 ζ ω, fun i => killedCode (VL i) (xL i) ζ ω,
    fun j => killedCode (VR j) (xR j) ζ ω)

section Evolution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}

theorem measurable_killedAt {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X) (t : ℝ≥0) :
    Measurable fun ω => if (t : ℝ≥0∞) < ζ ω then X t ω else 0 := by
  intro A hA
  have h1 : MeasurableSet {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} := 𝓕.le t _ (hX t A hA)
  have h2 : MeasurableSet {ω | (t : ℝ≥0∞) < ζ ω} := by
    simpa using 𝓕.le t _ (hX t univ MeasurableSet.univ)
  by_cases h0 : (0 : ℝ) ∈ A
  · convert h1.union h2.compl using 1
    ext ω; by_cases hω : (t : ℝ≥0∞) < ζ ω <;> simp [hω, h0]
  · convert h1 using 1
    ext ω; by_cases hω : (t : ℝ≥0∞) < ζ ω <;> simp [hω, h0]

theorem measurable_killedCode {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X) (x₀ : ℝ) :
    Measurable (killedCode X x₀ ζ) := by
  refine measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => ?_
  unfold killedCode
  by_cases h0 : dyad n k = 0
  · simp only [h0, ↓reduceIte]; exact measurable_const
  · simp only [h0, ↓reduceIte]; exact measurable_killedAt hX _

theorem measurable_lifetime {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X) : Measurable ζ := by
  refine measurable_of_Ioi fun x => ?_
  induction x using ENNReal.recTopCoe with
  | top => simp
  | coe t =>
    have := 𝓕.le t _ (hX t univ MeasurableSet.univ)
    simpa [preimage, Ioi] using this

theorem measurable_codeOf {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {B' : ℝ≥0 → Ω → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hB' : ∀ t, Measurable (B' t)) (hW : AdaptedBefore 𝓕 ζ W) (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i))
    (hVR : ∀ j, AdaptedBefore 𝓕 ζ (VR j)) :
    Measurable (codeOf xL xR B' W VL VR ζ) := by
  refine (measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => hB' _).prodMk
    ((measurable_lifetime hW).prodMk ((measurable_killedCode hW 0).prodMk
      ((measurable_pi_iff.2 fun i => measurable_killedCode (hVL i) (xL i)).prodMk
        (measurable_pi_iff.2 fun j => measurable_killedCode (hVR j) (xR j)))))

end Evolution

/-! ### The frozen predicate only sees the paths before `ζ` (and at `0`) -/

/-- Changing the paths only at times `≥ ζ` (and keeping the values at `0`) preserves the frozen
predicate. -/
theorem isIntegratedSLEPath_congr {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ}
    {vR vR' : Fin nR → ℝ≥0 → ℝ} {b b' : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (h0w : w' 0 = w 0)
    (h0L : ∀ i, vL' i 0 = vL i 0) (h0R : ∀ j, vR' j 0 = vR j 0)
    (hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w' t = w t)
    (hL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ i, vL' i t = vL i t)
    (hR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ j, vR' j t = vR j t)
    (hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → b' t = b t) :
    IsIntegratedSLEPath a xL xR ρL ρR w' vL' vR' b' ζ := by
  have hp := h.isForcePath
  have hd := h.driverEq
  have hs : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ s ∈ uIcc (0 : ℝ) t, (s.toNNReal : ℝ≥0∞) < ζ :=
    fun {t} ht s hs => by
      rw [uIcc_of_le t.coe_nonneg] at hs; exact toNNReal_lt_of_mem_Icc ht hs
  have eqL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ (c : ℝ) (i : Fin nL),
      EqOn (fun s : ℝ => c / (w' s.toNNReal - vL' i s.toNNReal))
        (fun s : ℝ => c / (w s.toNNReal - vL i s.toNNReal)) (uIcc 0 t) :=
    fun ht c i s hs' => by
      simp only; rw [hw _ (hs ht s hs'), hL _ (hs ht s hs') i]
  have eqR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ (c : ℝ) (j : Fin nR),
      EqOn (fun s : ℝ => c / (w' s.toNNReal - vR' j s.toNNReal))
        (fun s : ℝ => c / (w s.toNNReal - vR j s.toNNReal)) (uIcc 0 t) :=
    fun ht c j s hs' => by
      simp only; rw [hw _ (hs ht s hs'), hR _ (hs ht s hs') j]
  have fL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ i : Fin nL,
      EqOn (fun s : ℝ => 2 / (vL' i s.toNNReal - w' s.toNNReal))
        (fun s : ℝ => 2 / (vL i s.toNNReal - w s.toNNReal)) (uIcc 0 t) :=
    fun ht i s hs' => by
      simp only; rw [hw _ (hs ht s hs'), hL _ (hs ht s hs') i]
  have fR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ j : Fin nR,
      EqOn (fun s : ℝ => 2 / (vR' j s.toNNReal - w' s.toNNReal))
        (fun s : ℝ => 2 / (vR j s.toNNReal - w s.toNNReal)) (uIcc 0 t) :=
    fun ht j s hs' => by
      simp only; rw [hw _ (hs ht s hs'), hR _ (hs ht s hs') j]
  have gL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ i : Fin nL,
      EqOn (fun s : ℝ => (w s.toNNReal - vL i s.toNNReal)⁻¹)
        (fun s : ℝ => (w' s.toNNReal - vL' i s.toNNReal)⁻¹) (uIoc 0 t) :=
    fun {t} ht i s hs' => by
      have hs'' : s ∈ uIcc (0 : ℝ) t := uIoc_subset_uIcc hs'
      simp only; rw [hw _ (hs ht s hs''), hL _ (hs ht s hs'') i]
  have gR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ j : Fin nR,
      EqOn (fun s : ℝ => (w s.toNNReal - vR j s.toNNReal)⁻¹)
        (fun s : ℝ => (w' s.toNNReal - vR' j s.toNNReal)⁻¹) (uIoc 0 t) :=
    fun {t} ht j s hs' => by
      have hs'' : s ∈ uIcc (0 : ℝ) t := uIoc_subset_uIcc hs'
      simp only; rw [hw _ (hs ht s hs''), hR _ (hs ht s hs'') j]
  have hstate : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ →
      (w' t, (fun i => vL' i t), fun j => vR' j t) = (w t, (fun i => vL i t), fun j => vR j t) :=
    fun ht => by rw [hw _ ht, funext (hL _ ht), funext (hR _ ht)]
  have hp' : IsForcePath xL xR ρL ρR w' vL' vR' ζ :=
    { w_zero := h0w.trans hp.w_zero
      vL_zero := fun i => (h0L i).trans (hp.vL_zero i)
      vR_zero := fun j => (h0R j).trans (hp.vR_zero j)
      continuousOn_w := hp.continuousOn_w.congr fun t ht => hw t ht
      continuousOn_vL := fun i => (hp.continuousOn_vL i).congr fun t ht => hL t ht i
      continuousOn_vR := fun j => (hp.continuousOn_vR j).congr fun t ht => hR t ht j
      antitone_vL := fun {t} ht i j hij => by
        show vL' j t ≤ vL' i t
        rw [hL _ ht, hL _ ht]; exact hp.antitone_vL ht hij
      vL_le_w := fun {t} ht i => by rw [hL _ ht, hw _ ht]; exact hp.vL_le_w ht i
      w_le_vR := fun {t} ht j => by rw [hR _ ht, hw _ ht]; exact hp.w_le_vR ht j
      monotone_vR := fun {t} ht i j hij => by
        show vR' i t ≤ vR' j t
        rw [hR _ ht, hR _ ht]; exact hp.monotone_vR ht hij
      integrable_gapL := fun {t} ht i => (hp.integrable_gapL ht i).congr (gL ht i)
      integrable_gapR := fun {t} ht j => (hp.integrable_gapR ht j).congr (gR ht j)
      vL_eq := fun {t} ht i => by
        rw [hL _ ht, intervalIntegral.integral_congr (fL ht i)]; exact hp.vL_eq ht i
      vR_eq := fun {t} ht j => by
        rw [hR _ ht, intervalIntegral.integral_congr (fR ht j)]; exact hp.vR_eq ht j
      volume_collisionL := fun i => by
        convert hp.volume_collisionL i using 2
        ext s
        refine ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, ?_⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, ?_⟩⟩
        · rw [← hw _ h2, ← hL _ h2 i]; exact h3
        · rw [hw _ h2, hL _ h2 i]; exact h3
      volume_collisionR := fun j => by
        convert hp.volume_collisionR j using 2
        ext s
        refine ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, ?_⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, ?_⟩⟩
        · rw [← hw _ h2, ← hR _ h2 j]; exact h3
        · rw [hw _ h2, hR _ h2 j]; exact h3
      not_threshold := fun {t} ht => by
        have e := hstate ht
        simp only [Prod.mk.injEq] at e
        rw [e.1, e.2.1, e.2.2]; exact hp.not_threshold ht
      threshold_of_eq_zero := hp.threshold_of_eq_zero
      threshold_of_tendsto := fun {T} hT hζ {w₀ vL₀ vR₀} hlim => by
        refine hp.threshold_of_tendsto hT hζ (hlim.congr' ?_)
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact hstate (by rw [← hζ]; exact_mod_cast ht) }
  refine IsIntegratedSLEPath.iff_isForcePath_and_driverEq.2 ⟨hp', fun t ht => ?_⟩
  rw [hw _ ht, hb _ ht]
  have e1 : ∀ i, (∫ s in (0 : ℝ)..t, ρL i / (w' s.toNNReal - vL' i s.toNNReal)) =
      ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal) := fun i =>
    intervalIntegral.integral_congr (eqL ht _ i)
  have e2 : ∀ j, (∫ s in (0 : ℝ)..t, ρR j / (w' s.toNNReal - vR' j s.toNNReal)) =
      ∫ s in (0 : ℝ)..t, ρR j / (w s.toNNReal - vR j s.toNNReal) := fun j =>
    intervalIntegral.integral_congr (eqR ht _ j)
  simp only [e1, e2]
  exact hd t ht

/-! ### Codes of evolutions are canonical solution codes -/

theorem dec_zero_of_const {c : PCode} {x₀ : ℝ} (h : ∀ n, c n 0 = x₀) : dec c 0 = x₀ := by
  unfold dec
  have : (fun n => c n (flr n 0)) = fun _ => x₀ := funext fun n => by
    simp [flr, h n]
  rw [this, limsup_const]

theorem killedPath_eq {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {x₀ : ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (h0 : X 0 ω = x₀) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) : killedPath X x₀ ζ ω s = X s ω := by
  unfold killedPath
  by_cases hs0 : s = 0
  · simp [hs0, h0]
  · simp [hs0, hs]

/-- Decoding the killed code recovers the process before `ζ`. -/
theorem dec_killedCode {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {x₀ : ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (h0 : X 0 ω = x₀) (hc : ContinuousOn (X · ω) {t | (t : ℝ≥0∞) < ζ ω}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ ω) : dec (killedCode X x₀ ζ ω) t = X t ω := by
  rw [killedCode_eq_enc, dec_enc, killedPath_eq h0 ht]
  have hsub : Iic t ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := fun s hs =>
    lt_of_le_of_lt (by exact_mod_cast hs) ht
  refine ((hc t ht).mono hsub).congr (fun s hs => killedPath_eq h0 (hsub hs)) ?_
  exact killedPath_eq h0 ht

theorem uc_killedCode {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {x₀ : ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (h0 : X 0 ω = x₀) (hc : ContinuousOn (X · ω) {t | (t : ℝ≥0∞) < ζ ω}) {d : ℝ≥0}
    (hd : (d : ℝ≥0∞) < ζ ω) : UC (killedCode X x₀ ζ ω) d := by
  rw [killedCode_eq_enc]
  have hsub : Iic d ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := fun s hs =>
    lt_of_le_of_lt (by exact_mod_cast hs) hd
  exact uc_enc ((hc.mono hsub).congr fun s hs => killedPath_eq h0 (hsub hs))

theorem killedCode_zero {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (x₀ : ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) (n : ℕ) :
    killedCode X x₀ ζ ω n 0 = x₀ := by
  simp [killedCode, dyad]

section Evolution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Almost surely, the code of an evolution is a canonical solution code**, and it decodes to
the evolution before `ζ`. -/
theorem ae_codeOf_mem (ha : 0 < a)
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {B' : ℝ≥0 → Ω → ℝ}
    (hB'c : ∀ ω, Continuous (B' · ω)) (hae : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω) :
    ∀ᵐ ω ∂P, codeOf xL xR B' W VL VR ζ ω ∈ CRel a xL xR ρL ρR ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
        cw (codeOf xL xR B' W VL VR ζ ω) t = W t ω ∧
        (∀ i, cvL (codeOf xL xR B' W VL VR ζ ω) i t = VL i t ω) ∧
        (∀ j, cvR (codeOf xL xR B' W VL VR ζ ω) j t = VR j t ω) ∧
        cb (codeOf xL xR B' W VL VR ζ ω) t = B t ω := by
  filter_upwards [h.2.2.2.2, hae, h.ae_tendsto_threshold ha] with ω hpath hB hlim
  set x := codeOf xL xR B' W VL VR ζ ω with hxdef
  have hp := hpath.isForcePath
  have hbdec : ∀ t, cb x t = B t ω := fun t => by
    show dec (enc (B' · ω)) t = B t ω
    rw [dec_enc (hB'c ω).continuousWithinAt, hB t]
  have hwdec : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → cw x t = W t ω := fun t ht =>
    dec_killedCode hp.w_zero hp.continuousOn_w ht
  have hLdec : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ i, cvL x i t = VL i t ω := fun t ht i =>
    dec_killedCode (hp.vL_zero i) (hp.continuousOn_vL i) ht
  have hRdec : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ j, cvR x j t = VR j t ω := fun t ht j =>
    dec_killedCode (hp.vR_zero j) (hp.continuousOn_vR j) ht
  have hgood : Good x := by
    refine ⟨fun T => uc_enc (hB'c ω).continuousOn, fun n k hd => ⟨?_, fun i => ?_, fun j => ?_⟩⟩
    · exact uc_killedCode hp.w_zero hp.continuousOn_w hd
    · exact uc_killedCode (hp.vL_zero i) (hp.continuousOn_vL i) hd
    · exact uc_killedCode (hp.vR_zero j) (hp.continuousOn_vR j) hd
  have hpred : IsIntegratedSLEPath a xL xR ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) := by
    refine isIntegratedSLEPath_congr hpath ?_ (fun i => ?_) (fun j => ?_) hwdec hLdec hRdec
      fun t _ => hbdec t
    · show dec (killedCode W 0 ζ ω) 0 = W 0 ω
      rw [dec_zero_of_const (killedCode_zero W 0 ζ ω), hp.w_zero]
    · show dec (killedCode (VL i) (xL i) ζ ω) 0 = VL i 0 ω
      rw [dec_zero_of_const (killedCode_zero (VL i) (xL i) ζ ω), hp.vL_zero i]
    · show dec (killedCode (VR j) (xR j) ζ ω) 0 = VR j 0 ω
      rw [dec_zero_of_const (killedCode_zero (VR j) (xR j) ζ ω), hp.vR_zero j]
  have hlimthr : LimThr ρL ρR x := by
    intro h0 hfin
    set T := (ζ ω).toNNReal
    have hTζ : (T : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hfin.ne
    have hT : 0 < T := by
      have : (0 : ℝ≥0∞) < T := by rw [hTζ]; exact h0
      exact_mod_cast this
    obtain ⟨w₀, vL₀, vR₀, htend, hthr⟩ := hlim T hT hTζ
    have htend' : Tendsto (fun t => (cw x t, fun i => cvL x i t, fun j => cvR x j t)) (𝓝[<] T)
        (𝓝 (w₀, vL₀, vR₀)) := by
      refine htend.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (t : ℝ≥0∞) < ζ ω := by rw [← hTζ]; exact_mod_cast ht
      rw [hwdec t ht', funext (hLdec t ht'), funext (hRdec t ht')]
    have hq := lim_eq_of_tendsto (x := x) hT (show (T : ℝ≥0∞) = cζ x from hTζ) htend'
    simp only [Prod.mk.injEq] at hq
    obtain ⟨h1, h2, h3⟩ := hq
    rw [h1, h2, h3]
    exact hthr
  have hcanon : Canon xL xR x := by
    intro n k
    constructor
    · intro h0
      simp only [x, codeOf, killedCode, h0, ↓reduceIte]
      exact ⟨trivial, fun i => trivial, fun j => trivial⟩
    · intro h0 hlt
      have hlt' : ¬ (dyad n k : ℝ≥0∞) < ζ ω := hlt
      simp only [x, codeOf, killedCode, h0, hlt', ↓reduceIte]
      exact ⟨trivial, fun i => trivial, fun j => trivial⟩
  exact ⟨⟨⟨hgood, hlimthr, hpred⟩, hcanon⟩, fun t ht =>
    ⟨hwdec t ht, hLdec t ht, hRdec t ht, hbdec t⟩⟩

end Evolution

/-! ### The law of the killed state -/

/-- Codes whose decoded killed state at the times `ts` lies in the sets `A`. -/
def KSet {n : ℕ} (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)) :
    Set (XCode nL nR) :=
  {x | ∀ j, (ts j : ℝ≥0∞) < cζ x ∧
    (cw x (ts j), (fun i => cvL x i (ts j)), (fun i => cvR x i (ts j)), cb x (ts j)) ∈ A j}

theorem measurableSet_kSet {n : ℕ} (ts : Fin n → ℝ≥0)
    {A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)} (hA : ∀ j, MeasurableSet (A j)) :
    MeasurableSet (KSet (nL := nL) (nR := nR) ts A) := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun j => (measurable_coe_lt _ measurable_cζ).and ?_)
  have hm : Measurable fun x : XCode nL nR =>
      (cw x (ts j), (fun i => cvL x i (ts j)), (fun i => cvR x i (ts j)), cb x (ts j)) :=
    (measurable_cw_at _).prodMk ((measurable_pi_iff.2 fun i => measurable_cvL_at i _).prodMk
      ((measurable_pi_iff.2 fun i => measurable_cvR_at i _).prodMk (measurable_cb_at _)))
  exact measurableSet_setOfPred.1 (hm (hA j))

/-- The Borel set of driving-path codes whose solution has its killed state in `A`. -/
def lawSet (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {n : ℕ} (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)) :
    Set PCode :=
  Prod.fst '' (CRel a xL xR ρL ρR ∩ KSet ts A)

/-- **Lusin–Souslin**: the law set is Borel. -/
theorem measurableSet_lawSet {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hsep : ∀ i j, xL i < xR j) {n : ℕ} (ts : Fin n → ℝ≥0)
    {A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)} (hA : ∀ j, MeasurableSet (A j)) :
    MeasurableSet (lawSet a xL xR ρL ρR ts A) :=
  ((measurableSet_cRel a xL xR ρL ρR).inter (measurableSet_kSet ts hA)).image_of_measurable_injOn
    measurable_fst ((injOn_fst_cRel hsep).mono inter_subset_left)

/-- The code of a continuous path. -/
def encC (f : QuantumZipper.RS.CPath) : PCode := enc f.1

theorem measurable_encC : Measurable encC :=
  measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k =>
    QuantumZipper.RS.measurable_canonBM (dyad n k)

/-- **The killed-state probabilities of an evolution of a separated word** are those of the law
of (a continuous version of) its Brownian motion on `CPath`, evaluated on the fixed Borel set
`encC ⁻¹' lawSet`. -/
theorem measure_killedState_eq_map {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {a : ℝ} (ha : 0 < a) {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hsep : ∀ i j, xL i < xR j)
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {B' : ℝ≥0 → Ω → ℝ}
    (hB'm : ∀ t, Measurable (B' t)) (hB'c : ∀ ω, Continuous (B' · ω))
    (hae : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω) {n : ℕ} (ts : Fin n → ℝ≥0)
    (A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)) (hA : ∀ j, MeasurableSet (A j)) :
    P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
        (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ A j} =
      (P.map (QuantumZipper.RS.toCPath B' hB'c)) (encC ⁻¹' lawSet a xL xR ρL ρR ts A) := by
  rw [Measure.map_apply (QuantumZipper.RS.measurable_toCPath hB'm hB'c)
    ((measurableSet_lawSet hsep ts hA).preimage measurable_encC)]
  refine measure_congr ?_
  filter_upwards [ae_codeOf_mem ha h hB'c hae] with ω ⟨hmem, hdec⟩
  set x := codeOf xL xR B' W VL VR ζ ω with hx
  have hK : (∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
      (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ A j) ↔
      x ∈ KSet ts A := by
    refine forall_congr' fun j => ?_
    refine ⟨fun ⟨hlt, hmemA⟩ => ⟨hlt, ?_⟩, fun ⟨hlt, hmemA⟩ => ⟨hlt, ?_⟩⟩
    · obtain ⟨e1, e2, e3, e4⟩ := hdec (ts j) hlt
      rw [e1, funext e2, funext e3, e4]; exact hmemA
    · obtain ⟨e1, e2, e3, e4⟩ := hdec (ts j) hlt
      rw [e1, funext e2, funext e3, e4] at hmemA; exact hmemA
  have hfst : encC (QuantumZipper.RS.toCPath B' hB'c ω) = x.1 := rfl
  refine propext ?_
  show (∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
      (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ A j) ↔
    encC (QuantumZipper.RS.toCPath B' hB'c ω) ∈ lawSet a xL xR ρL ρR ts A
  rw [hK, hfst]
  constructor
  · intro hk
    exact ⟨x, ⟨hmem, hk⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hyK⟩, hy1⟩
    have : y = x := injOn_fst_cRel hsep hy hmem hy1
    rw [← this]; exact hyK

end Assembly

end Sec2

open Sec2.Assembly

/-- **Theorem 2.2, uniqueness in law, for separated force words** (every force word in which no
left mark and no right mark both start at `0`): exactly the frozen statement
`IsIntegratedSLEEvolution.measure_killedState_eq` with `IsOrderedForceWord` replaced by the
separation hypothesis `∀ i j, xL i < xR j` (for ordered words this says `¬ (xL 0 = 0 ∧ xR 0 = 0)`),
for all weights. -/
theorem IsIntegratedSLEEvolution.measure_killedState_eq_of_separated {a : ℝ} (ha : 0 < a)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hsep : ∀ i j, xL i < xR j)
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution a xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution a xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (n : ℕ) (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ))
    (hA : ∀ j, MeasurableSet (A j)) :
    P₁ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₁ ω ∧
        (W₁ (ts j) ω, (fun i => VL₁ i (ts j) ω), (fun i => VR₁ i (ts j) ω), B₁ (ts j) ω) ∈ A j} =
      P₂ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₂ ω ∧
        (W₂ (ts j) ω, (fun i => VL₂ i (ts j) ω), (fun i => VR₂ i (ts j) ω), B₂ (ts j) ω) ∈ A j} := by
  obtain ⟨B₁', hm₁, hc₁, -, hbm₁, hae₁⟩ := QuantumZipper.RS.exists_good_version0 h₁.1.1
  obtain ⟨B₂', hm₂, hc₂, -, hbm₂, hae₂⟩ := QuantumZipper.RS.exists_good_version0 h₂.1.1
  rw [measure_killedState_eq_map ha hsep h₁ hm₁ hc₁ hae₁ ts A hA,
    measure_killedState_eq_map ha hsep h₂ hm₂ hc₂ hae₂ ts A hA,
    QuantumZipper.RS.map_toCPath_eq hbm₁.toIsPreBrownianReal hbm₂.toIsPreBrownianReal hm₁ hm₂
      hc₁ hc₂]

end InteractingSLE
