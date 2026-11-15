/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR4Select

/-!
# The concrete GW2 inverse reconstructs the actual live physical record

All inverse, capacity, buffer existence and strict-prefix invariance premises
are discharged. The input is the retained counterflow record and the killed
relative driver. No preselected relative record or inverse identity is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2JDetR4

open Supp8.GB6 Exist.StagedLaw GW2TipSystem GW2JDetR3

/-- The total Borel inverse reconstructs every strictly live pre-contact
physical stopped record from the actual killed relative chain. The rational
buffer it uses exists and is strictly later than the required relative time. -/
theorem exists_actual_inverseRecord {Ω : Type*}
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
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < S ↔
        ∃ q : ℚ≥0, IsBuffer s t (r, killedCode (V, L), L) q) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < S →
        ∀ B : ℝ≥0∞, ((a t).toNNReal : ℝ≥0∞) < B → B ≤ L →
        let x : BufferInput := (r, killedCode (V, B), B)
        ((a t).toNNReal < (bufferTime s t x : ℝ≥0) ∧
          ((bufferTime s t x : ℝ≥0) : ℝ≥0∞) < B) ∧
        inverseRecord s t (r, (V, B)) =
          cfRec t (fun u (_ : Unit) => w u) (fun _ => T) () := by
  dsimp only
  obtain ⟨V, hV0, ha0, hm, hc, hVc, hread, hdriver⟩ :=
    exists_actual_physicalDriverRead W ζ ω hα hW hW0 hs hsH hγ hw hw0 hT
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
      inverseHull s (a t).toNNReal p = fwdHull (Ito.rpath w) t ∧
        physicalCapacity s (a t).toNNReal p = t at hread
  have hprefix : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < L →
      ∃ u : ℝ≥0, (u : ℝ≥0∞) < S ∧ a u = (q : ℝ≥0) ∧
        prefixCapacity s q r (killedCode (V, L)) = (u : ℝ≥0∞) := by
    intro q hq
    obtain ⟨u, ⟨hu, hau⟩, _⟩ := existsUnique_time_of_lt_clockSup ha0 hm hc hq
    obtain ⟨b, hqb, hb⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hq
    have hqb' : (q : ℝ≥0) < b := ENNReal.coe_lt_coe.mp hqb
    refine ⟨u, hu, hau, ?_⟩
    rw [prefixCapacity_eq_buffer s r hVc hV0 hqb' hb]
    have hcap := ((hread u hu).2.2 b
      (by simpa only [hau, Real.toNNReal_coe] using hqb') hb).2
    change physicalCapacity s (a u).toNNReal _ = u at hcap
    rw [hau, Real.toNNReal_coe] at hcap
    rw [hcap, ENNReal.ofReal_coe_nnreal]
  have hcross : ∀ t : ℝ≥0, (t : ℝ≥0∞) < S →
      ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < L →
      ((t : ℝ≥0∞) < prefixCapacity s q r (killedCode (V, L)) ↔
        (a t).toNNReal < (q : ℝ≥0)) := by
    intro t ht q hq
    obtain ⟨u, hu, hau, hcap⟩ := hprefix q hq
    rw [hcap, ENNReal.coe_lt_coe]
    have hn := (hread t ht).1
    constructor
    · intro htu
      have h := hm ht hu htu
      rw [hau] at h
      apply NNReal.coe_lt_coe.mp
      rwa [Real.coe_toNNReal _ hn]
    · intro hq'
      have h := NNReal.coe_lt_coe.mpr hq'
      rw [Real.coe_toNNReal _ hn, ← hau] at h
      exact (hm.lt_iff_lt ht hu).mp h
  have hex : ∀ t : ℝ≥0, (t : ℝ≥0∞) < S →
      ∃ q : ℚ≥0, IsBuffer s t (r, killedCode (V, L), L) q := by
    intro t ht
    obtain ⟨b, htb, hb⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (hread t ht).2.1
    obtain ⟨q, htq, hqb⟩ := exists_rat_btwn
      (NNReal.coe_lt_coe.mpr (ENNReal.coe_lt_coe.mp htb))
    have hq0 : (0 : ℚ) ≤ q := by
      exact_mod_cast (NNReal.coe_nonneg (a t).toNNReal).trans htq.le
    let q' : ℚ≥0 := ⟨q, hq0⟩
    have hqL : ((q' : ℝ≥0) : ℝ≥0∞) < L :=
      (ENNReal.coe_le_coe.mpr (show (q' : ℝ≥0) ≤ b by exact_mod_cast hqb.le)).trans_lt hb
    exact ⟨q', hqL, (hcross t ht q' hqL).mpr (by exact_mod_cast htq)⟩
  refine ⟨V, hV0, hVc, ?_, ?_⟩
  · intro t
    refine ⟨hex t, ?_⟩
    rintro ⟨q, hq, hcap⟩
    obtain ⟨u, hu, _, he⟩ := hprefix q hq
    rw [he] at hcap
    exact hcap.trans hu
  intro t ht B htB hBL
  let x : BufferInput := (r, killedCode (V, B), B)
  have hcode : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < B →
      prefixRecord q (killedCode (V, B)) = prefixRecord q (killedCode (V, L)) := by
    intro q hq
    apply prefixRecord_congr
    intro u hu
    have huB : ((u : ℝ≥0) : ℝ≥0∞) < B :=
      (ENNReal.coe_le_coe.mpr (by exact_mod_cast hu)).trans_lt hq
    have huL : ((u : ℝ≥0) : ℝ≥0∞) < L := huB.trans_le hBL
    change (if ((u : ℝ≥0) : ℝ≥0∞) < B then V u else 0) =
      (if ((u : ℝ≥0) : ℝ≥0∞) < L then V u else 0)
    rw [ite_eq_left huB, ite_eq_left huL]
  have hcap : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < B →
      prefixCapacity s q r (killedCode (V, B)) =
        prefixCapacity s q r (killedCode (V, L)) := by
    intro q hq
    unfold prefixCapacity
    rw [hcode q hq]
  have hexB : ∃ q : ℚ≥0, IsBuffer s t x q := by
    obtain ⟨b, htb, hb⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp htB
    obtain ⟨q, htq, hqb⟩ := exists_rat_btwn
      (NNReal.coe_lt_coe.mpr (ENNReal.coe_lt_coe.mp htb))
    have hq0 : (0 : ℚ) ≤ q := by
      exact_mod_cast (NNReal.coe_nonneg (a t).toNNReal).trans htq.le
    let q' : ℚ≥0 := ⟨q, hq0⟩
    have hqB : ((q' : ℝ≥0) : ℝ≥0∞) < B :=
      (ENNReal.coe_le_coe.mpr (show (q' : ℝ≥0) ≤ b by exact_mod_cast hqb.le)).trans_lt hb
    refine ⟨q', hqB, ?_⟩
    change (t : ℝ≥0∞) < prefixCapacity s q' r (killedCode (V, B))
    rw [hcap q' hqB]
    exact (hcross t ht q' (hqB.trans_le hBL)).mpr (by exact_mod_cast htq)
  have hbuf := isBuffer_bufferTime s t x hexB
  have hqB : ((bufferTime s t x : ℝ≥0) : ℝ≥0∞) < B := hbuf.1
  have hqL : ((bufferTime s t x : ℝ≥0) : ℝ≥0∞) < L := hqB.trans_le hBL
  have htq : (a t).toNNReal < (bufferTime s t x : ℝ≥0) :=
    (hcross t ht _ hqL).mp ((hcap _ hqB) ▸ hbuf.2)
  refine ⟨⟨htq, hqB⟩, ?_⟩
  change physicalRecordRead s t (r, prefixRecord (bufferTime s t x) (killedCode (V, B))) = _
  rw [hcode _ hqB, prefixRecord_eq_cfRec hVc hV0 hqL]
  exact physicalRecordRead_eq_cfRec s t _ hw hw0 (lt_min_iff.mp ht).2
    (hdriver t ht (bufferTime s t x : ℝ≥0) htq hqL).2

end InteractingSLE.Theorem14.GW2JDetR4
