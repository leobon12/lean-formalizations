/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR3Prefix
import InteractingSLE.Spec.Restart.ClockInv

/-!
# Identification of the actual killed-path physical-capacity rule

The attained-level rule agrees with the intrinsic relative clock at every
available physical cutoff. The proof extends the compact inverse clock by
freezing and uses Galmarino locality to discard all later capacity values.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2JDetR3

open Exist.StagedLaw Supp8.GB6 GW2TipSystem Sec7.Lemma71I

private theorem levelRule_read_values {X E : Type*}
    (f : ℚ≥0 → X → (ℚ≥0 → E) → ℝ≥0∞) (Δ : ℝ≥0∞) (x : X) (c : ℚ≥0 → E) :
    levelRule f Δ x c =
      levelRule (fun q (_ : Unit) (d : ℚ≥0 → ℝ≥0∞) => d q) Δ () (fun q => f q x c) := rfl

/-- The attained-level rule is identified by capacity values only through the
claimed stop, even when the input family is irregular after that stop. -/
theorem levelRule_eq_of_continuous_prefix {X E : Type*}
    {f : ℚ≥0 → X → (ℚ≥0 → E) → ℝ≥0∞} {Δ : ℝ≥0∞} {x : X} {c : ℚ≥0 → E}
    {g : ℝ≥0 → ℝ≥0∞} (hg : Continuous g) (hm : Monotone g) {v : ℝ≥0}
    (hreach : Δ ≤ g v) (hlt : ∀ u < v, g u < Δ)
    (hf : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ v → f q x c = g q) :
    levelRule f Δ x c = (v : ℝ≥0∞) := by
  let F := fun q (_ : Unit) (d : ℚ≥0 → ℝ≥0∞) => d q
  have hG : levelRule F Δ () (fun q => g q) = (v : ℝ≥0∞) :=
    levelRule_eq_of_continuous (f := F) hg hm (fun _ => rfl) hreach hlt
  have hloc : ∀ q (x : Unit) (d d' : ℚ≥0 → ℝ≥0∞),
      (∀ r ≤ q, d r = d' r) → F q x d' = F q x d :=
    fun q _ _ _ h => (h q le_rfl).symm
  have hval := levelRule_galmarino (f := F) (a := Δ) hloc ()
    (fun q => g q) (fun q => f q x c) (fun q hq => by
      rw [hG] at hq
      exact (hf q (ENNReal.coe_le_coe.mp hq)).symm)
  exact (levelRule_read_values f Δ x c).trans (hval.trans hG)

/-- The concrete killed-path capacity stopping functional is the actual
relative clock at every physical time before contact and the original life.
All clock, inverse and capacity hypotheses are discharged from source traces. -/
theorem exists_actual_physicalCapacityStop {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ H)
    {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w T γ)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T}) (hw0 : w 0 = 0) (hT : 0 < T) :
    let r := cfRec s W ζ ω
    let S := min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T
    let a : ℝ≥0 → ℝ := fun t => relClock (rdrv r) s (Ito.rpath w) t
    let L := ⨆ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < S), ((a t).toNNReal : ℝ≥0∞)
    ∃ V : ℝ≥0 → ℝ, V 0 = 0 ∧ ContinuousOn V {q | (q : ℝ≥0∞) < L} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < S →
        physicalCapacityStop s (t : ℝ≥0∞) r (V, L) = ((a t).toNNReal : ℝ≥0∞) := by
  dsimp only
  obtain ⟨V, hV0, ha0, hm, hc, hVc, hread⟩ :=
    exists_inverse_capacity_chain W ζ ω hα hW hW0 hs hsH hγ hw hw0 hT
  let r := cfRec s W ζ ω
  let S := min
    (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
      ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T
  let a : ℝ≥0 → ℝ := fun t => relClock (rdrv r) s (Ito.rpath w) t
  let L := ⨆ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < S), ((a t).toNNReal : ℝ≥0∞)
  change a 0 = 0 at ha0
  change StrictMonoOn a {t | (t : ℝ≥0∞) < S} at hm
  change ContinuousOn a {t | (t : ℝ≥0∞) < S} at hc
  change ContinuousOn V {q | (q : ℝ≥0∞) < L} at hVc
  change ∀ t : ℝ≥0, (t : ℝ≥0∞) < S →
    0 ≤ a t ∧ ((a t).toNNReal : ℝ≥0∞) < L ∧
    ∀ b : ℝ≥0, (a t).toNNReal < b → (b : ℝ≥0∞) < L →
      let p := (r, cfRec b (fun u (_ : Unit) => V u) (fun _ => L) ())
      inverseHull s (a t).toNNReal p = QuantumZipper.fwdHull (Ito.rpath w) t ∧
        physicalCapacity s (a t).toNNReal p = t at hread
  refine ⟨V, hV0, hVc, ?_⟩
  intro t ht
  let v := (a t).toNNReal
  have hn := (hread t ht).1
  have ha : Restart.IsClockOn a (t : ℝ≥0∞) :=
    ⟨ha0, hm.mono (fun u hu => hu.trans_lt ht), hc.mono (fun u hu => hu.trans_lt ht),
      fun h => (ENNReal.coe_ne_top h).elim⟩
  have hLife : Restart.capLife a (t : ℝ≥0∞) = (v : ℝ≥0∞) := by
    simp only [Restart.capLife, ENNReal.coe_ne_top, ↓reduceIte, ENNReal.toNNReal_coe]
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hn]
  let I := Restart.invClock a (t : ℝ≥0∞)
  let g : ℝ≥0 → ℝ≥0∞ := fun u => (I (min u v) : ℝ≥0∞)
  have hmemb : ∀ u : ℝ≥0, ((min u v : ℝ≥0) : ℝ≥0∞) ≤ Restart.capLife a t := by
    intro u
    rw [hLife]
    exact ENNReal.coe_le_coe.mpr (min_le_right _ _)
  have hgc : Continuous g := ENNReal.continuous_coe.comp
    (ha.continuousOn_invClock.comp_continuous (continuous_id.min continuous_const) hmemb)
  have hgm : Monotone g := by
    intro u u' huu'
    exact ENNReal.coe_le_coe.mpr
      (ha.strictMonoOn_invClock.monotoneOn (hmemb u) (hmemb u') (min_le_min huu' le_rfl))
  have hIv : I v = t := ha.invClock_apply le_rfl
  have hgv : g v = (t : ℝ≥0∞) := by simp only [g, min_self, hIv]
  have hglt : ∀ u < v, g u < (t : ℝ≥0∞) := by
    intro u huv
    have huCap : (u : ℝ≥0∞) ≤ Restart.capLife a t := by
      rw [hLife]
      exact ENNReal.coe_le_coe.mpr huv.le
    have hvCap := hmemb v
    rw [min_self] at hvCap
    have h := ha.strictMonoOn_invClock huCap hvCap huv
    change I u < I v at h
    simpa only [g, min_eq_left huv.le, hIv] using ENNReal.coe_lt_coe.mpr h
  change levelRule (prefixCapacity s) (t : ℝ≥0∞) r (killedCode (V, L)) = (v : ℝ≥0∞)
  apply levelRule_eq_of_continuous_prefix hgc hgm hgv.ge hglt
  intro q hqv
  have hqCap : ((q : ℝ≥0) : ℝ≥0∞) ≤ Restart.capLife a t := by
    rw [hLife]
    exact ENNReal.coe_le_coe.mpr hqv
  obtain ⟨hu, hau⟩ := ha.invClock_spec hqCap
  let u := I (q : ℝ≥0)
  change (u : ℝ≥0∞) ≤ (t : ℝ≥0∞) at hu
  change a u = (q : ℝ≥0) at hau
  have huS : (u : ℝ≥0∞) < S := hu.trans_lt ht
  obtain ⟨b, hvb, hb⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (hread t ht).2.1
  have hqb : (q : ℝ≥0) < b := hqv.trans_lt (ENNReal.coe_lt_coe.mp hvb)
  rw [prefixCapacity_eq_buffer s r hVc hV0 hqb hb]
  have hval := (hread u huS).2.2 b
    (by simpa only [hau, Real.toNNReal_coe] using hqb) hb
  have hcap : physicalCapacity s (q : ℝ≥0)
      (r, cfRec b (fun u (_ : Unit) => V u) (fun _ => L) ()) = u := by
    simpa only [hau, Real.toNNReal_coe] using hval.2
  rw [hcap, ENNReal.ofReal_coe_nnreal]
  simp only [g, min_eq_left hqv, u, I]

end InteractingSLE.Theorem14.GW2JDetR3
