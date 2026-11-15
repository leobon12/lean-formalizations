/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ClockGeom
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# The two Loewner facts of the original traces used by the relative clocks

Packet PROVE-RESTART-CPL5. The deterministic clock theorem (`IsContinuationGood.exists_driver_chartClock`) uses two
properties of the original trace `η₁` (Aux. lemma 76's proof, p. 286: "original Loewner strict growth gives interior
points arbitrarily close to the beginning of a nonempty continuation"; "the interior times are dense on every
nonempty future parameter interval. Otherwise an original Loewner trace would traverse only the real line on an
interval, contradicting strict growth of its filled hulls"):

* **the tip property** (`IsGeneratingTrace.mem_closure_of_lt`): `η(s)` is adherent to the unbounded domain of
  every earlier prefix `η([0, u])`, `u < s ≤ T` (including a finite terminal point);
* **dense interior times** (`IsGeneratingTrace.exists_mem_H`): every nonempty parameter interval `(a, b)`,
  `b ≤ T`, contains a time with `η(s) ∈ ℍ`.

Both are proved for the frozen `IsGeneratingTrace` with a driver continuous before `T` and vanishing at `0`, and are
transported to traces seeded at a real point `x` (`…_add`), the form in which flow lines carry them.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

/-- Adding points off `ℍ` (for instance real points) does not change a filling. -/
theorem fillH_union_of_forall_notMem_H {A B : Set ℂ} (hB : ∀ z ∈ B, z ∉ H) :
    fillH (A ∪ B) = fillH A := by
  have hBc : closure B ⊆ Hᶜ :=
    closure_minimal (fun z hz => hB z hz) QuantumZipper.isOpen_H.isClosed_compl
  have hcl : ∀ z ∈ H, z ∈ closure (A ∪ B) ↔ z ∈ closure A := by
    intro z hz
    rw [closure_union]
    exact ⟨fun h => h.resolve_right fun h' => hBc h' hz, Or.inl⟩
  have hHc : H \ closure (A ∪ B) = H \ closure A := by
    ext z
    exact ⟨fun h => ⟨h.1, fun h' => h.2 ((hcl z h.1).2 h')⟩,
      fun h => ⟨h.1, fun h' => h.2 ((hcl z h.1).1 h')⟩⟩
  ext z
  simp only [fillH, mem_ofPred_eq, hHc]
  exact ⟨fun h => ⟨h.1, h.2.imp_left ((hcl z h.1).1)⟩, fun h => ⟨h.1, h.2.imp_left ((hcl z h.1).2)⟩⟩

variable {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

theorem neBot_nhdsWithin_H_zero : (𝓝[H] (0 : ℂ)).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; show (0 : ℂ).im ≥ 0; simp)

/-- **The tip property** before `T`: `η(t)` is adherent to the unbounded domain of `η([0, t])`. -/
theorem IsGeneratingTrace.mem_closure_self (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    η t ∈ closure (H \ fillH (η '' Icc 0 t)) := by
  obtain ⟨t₂, htt₂, ht₂T⟩ := exists_real_btwn_of_lt ht
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg t).trans htt₂.le
  have hL := hη.isLoewnerTraceLT ht₂T
  have hWc := continuous_frozenDrive_of_lt hw ht₂T
  have hW0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
  have htip := hL.tendsto_fwdMapInv_tip hWc hW0 (NNReal.coe_nonneg t) htt₂
  simp only [Real.toNNReal_coe] at htip
  have hK := hL.2.2 t (NNReal.coe_nonneg t) htt₂
  rw [image_toNNReal_Icc η (NNReal.coe_nonneg t), Real.toNNReal_coe] at hK
  have := neBot_nhdsWithin_H_zero
  refine mem_closure_of_tendsto htip (eventually_nhdsWithin_of_forall fun z hz => ?_)
  rw [← hK]
  exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWc hW0 (NNReal.coe_nonneg t) hz

/-- **The tip property**: for `u < s ≤ T`, `η(s)` is adherent to the unbounded domain of `η([0, u])`. -/
theorem IsGeneratingTrace.mem_closure_of_lt (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {u s : ℝ≥0} (hus : u < s)
    (hsT : (s : ℝ≥0∞) ≤ T) : η s ∈ closure (H \ fillH (η '' Icc 0 u)) := by
  have hmono : ∀ r : ℝ≥0, u ≤ r → (r : ℝ≥0∞) < T → η r ∈ closure (H \ fillH (η '' Icc 0 u)) :=
    fun r hur hrT => closure_mono (sdiff_subset_sdiff_right (fillH_mono (image_mono
      (Icc_subset_Icc_right hur)))) (IsGeneratingTrace.mem_closure_self hη hw hw0 hrT)
  rcases hsT.lt_or_eq with hsT | hsT
  · exact hmono s hus.le hsT
  -- the terminal point: a limit from the left
  have hc : ContinuousWithinAt η (Ioo u s) s :=
    (hη.2.1 s hsT.le).mono fun r hr => (ENNReal.coe_le_coe.2 hr.2.le).trans hsT.le
  have hcl : s ∈ closure (Ioo u s) := by
    rw [closure_Ioo hus.ne]
    exact ⟨hus.le, le_rfl⟩
  refine closure_minimal ?_ isClosed_closure (hc.mem_closure_image hcl)
  rintro _ ⟨r, hr, rfl⟩
  exact hmono r hr.1.le (lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hr.2) hsT.le)

/-- **Dense interior times**: a generating trace spends no nonempty time interval `(a, b)`, `b ≤ T`, on `ℝ`. -/
theorem IsGeneratingTrace.exists_mem_H (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {a b : ℝ≥0} (hab : a < b)
    (hbT : (b : ℝ≥0∞) ≤ T) : ∃ s ∈ Ioo a b, η s ∈ H := by
  by_contra hcon
  push Not at hcon
  -- two times `a < a' < b' < b`
  obtain ⟨a', haa', ha'b⟩ := exists_between hab
  obtain ⟨b', ha'b', hb'b⟩ := exists_between ha'b
  have hb'T : (b' : ℝ≥0∞) < T := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hb'b) hbT
  obtain ⟨t₂, hb't₂, ht₂T⟩ := exists_real_btwn_of_lt hb'T
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg b').trans hb't₂.le
  have hL := hη.isLoewnerTraceLT ht₂T
  have hWc := continuous_frozenDrive_of_lt hw ht₂T
  have hW0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
  have ha't₂ : (a' : ℝ) < t₂ := lt_trans (NNReal.coe_lt_coe.2 ha'b') hb't₂
  have hKa := hL.2.2 a' (NNReal.coe_nonneg a') ha't₂
  have hKb := hL.2.2 b' (NNReal.coe_nonneg b') hb't₂
  rw [image_toNNReal_Icc η (NNReal.coe_nonneg _), Real.toNNReal_coe] at hKa hKb
  -- the prefixes differ by real points only
  have hunion : η '' Icc 0 b' = η '' Icc 0 a' ∪ η '' Ioc a' b' := by
    rw [← image_union, Icc_union_Ioc_eq_Icc zero_le ha'b'.le]
  have hreal : ∀ z ∈ η '' Ioc a' b', z ∉ H := by
    rintro _ ⟨r, hr, rfl⟩
    exact hcon r ⟨haa'.trans hr.1, lt_of_le_of_lt hr.2 hb'b⟩
  have heq : QuantumZipper.fwdHull (frozenDrive w t₂) a' = QuantumZipper.fwdHull (frozenDrive w t₂) b' := by
    rw [hKa, hKb, hunion, fillH_union_of_forall_notMem_H hreal]
  have h1 := hcap_fwdHull hWc hW0 (NNReal.coe_nonneg a')
  have h2 := hcap_fwdHull hWc hW0 (NNReal.coe_nonneg b')
  have h3 : HPHull.hcap ⟨_, isHPHull_fwdHull hWc (NNReal.coe_nonneg a')⟩ =
      HPHull.hcap ⟨_, isHPHull_fwdHull hWc (NNReal.coe_nonneg b')⟩ := HPHull.hcap_congr heq
  have : (a' : ℝ) = b' := by linarith
  exact absurd (NNReal.coe_injective this) ha'b'.ne

/-! ### Traces seeded at a real point -/

variable {x : ℝ}

theorem image_add_real_eq (η : ℝ≥0 → ℂ) (x : ℝ) (A : Set ℝ≥0) :
    (fun z : ℂ => z + x) '' ((fun t => η t - x) '' A) = η '' A := by
  rw [image_image]
  simp only [sub_add_cancel]

theorem fillH_image_add_real (A : Set ℂ) (x : ℝ) :
    fillH ((fun z : ℂ => z + x) '' A) = (fun z : ℂ => z + x) '' fillH A := by
  have h := fillH_image_affHomeo (r := 1) (x := x) one_pos A
  simpa only [coe_affHomeo, ofReal_one, one_mul] using h

/-- The tip property for a trace seeded at `x` (`η − x` a generating trace). -/
theorem IsGeneratingTrace.mem_closure_of_lt_add (hη : IsGeneratingTrace w T fun t => η t - x)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {u s : ℝ≥0} (hus : u < s)
    (hsT : (s : ℝ≥0∞) ≤ T) : η s ∈ closure (H \ fillH (η '' Icc 0 u)) := by
  have h := IsGeneratingTrace.mem_closure_of_lt hη hw hw0 hus hsT
  have he : Continuous fun z : ℂ => z + x := by fun_prop
  have h1 := image_closure_subset_closure_image he ⟨_, h, rfl⟩
  simp only [sub_add_cancel] at h1
  refine closure_mono ?_ h1
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨show (0 : ℝ) < (z + x).im by simpa using (show (0 : ℝ) < z.im from hz.1), ?_⟩
  rw [← image_add_real_eq η x, fillH_image_add_real]
  rintro ⟨z', hz', hzz'⟩
  exact hz.2 (by rwa [add_left_inj] at hzz' ▸ hz')

/-- Dense interior times for a trace seeded at a real point. -/
theorem IsGeneratingTrace.exists_mem_H_add (hη : IsGeneratingTrace w T fun t => η t - x)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {a b : ℝ≥0} (hab : a < b)
    (hbT : (b : ℝ≥0∞) ≤ T) : ∃ s ∈ Ioo a b, η s ∈ H := by
  obtain ⟨s, hs, hsH⟩ := IsGeneratingTrace.exists_mem_H hη hw hw0 hab hbT
  refine ⟨s, hs, ?_⟩
  have : (η s - x).im = (η s).im := by simp
  exact show (0 : ℝ) < (η s).im from this ▸ hsH

end Restart

end InteractingSLE
