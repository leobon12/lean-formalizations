/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RelSafeGB6Local

/-!
# GB6's relative driver read in the physical history, part 2: the physical clock and the readable driver

Packet PROVE-GB6-RELSAFE. From the local curves of part 1 with the deterministic horizons
`T_k(t) = min(q_k, t)` (an enumeration `q_k` of the rationals):

* `physClock t = sup_k 1_{E_k} capLife(Γ_{T_k})` — GB6's relative clock at physical time `t` (stopped at the first
  contact), and `physDrv t u` — the local relative driver of the first horizon whose curve lives past `u`;
  both read only the record and the physical driver before `t` (**`measurable_physClock`**,
  **`measurable_physDrv`**);
* **`eq_localDrv_of_version`**: a version of GB6's relative exploration (`IsGB6RelVersion`) agrees with the local
  driver at every relative time below the local lifetime and the version stop (Loewner uniqueness through
  `IsDrivenCurve.segDrv_eq`: the version's hulls are the mapped physical hulls, i.e. the filled local curve);
* **`ae_eq_physDrv_of_version`**: almost surely, `R u = physDrv t u` whenever `u < physClock t` and `u ≤ V`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Supp8.RelSafe

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Sec7.Lemma71C Sec7.PocketTraversal

/-! ### A measurable first index -/

section Sel

variable {Ω : Type*}

open Classical in
/-- The first index of a countable family of events containing `ω` (`0` if there is none). -/
def selIdx (valid : ℕ → Set Ω) (ω : Ω) : ℕ :=
  Nat.find (show ∃ k, ω ∈ valid k ∨ ω ∉ ⋃ j, valid j from by
    by_cases h : ω ∈ ⋃ j, valid j
    · obtain ⟨k, hk⟩ := mem_iUnion.1 h
      exact ⟨k, Or.inl hk⟩
    · exact ⟨0, Or.inr h⟩)

theorem selIdx_mem {valid : ℕ → Set Ω} {ω : Ω} {k : ℕ} (hk : ω ∈ valid k) : ω ∈ valid (selIdx valid ω) := by
  classical
  have h := Nat.find_spec (show ∃ k, ω ∈ valid k ∨ ω ∉ ⋃ j, valid j from ⟨k, Or.inl hk⟩)
  unfold selIdx
  rcases h with h | h
  · convert h using 3
  · exact absurd (mem_iUnion.2 ⟨k, hk⟩) (by convert h using 3)

theorem measurable_selIdx {m : MeasurableSpace Ω} {valid : ℕ → Set Ω} (hv : ∀ k, MeasurableSet[m] (valid k)) :
    Measurable[m] (selIdx valid) := by
  classical
  unfold selIdx
  exact @measurable_find Ω m (fun ω k => ω ∈ valid k ∨ ω ∉ ⋃ j, valid j) _ _
    fun k => (hv k).union (MeasurableSet.iUnion hv).compl

end Sel

/-! ### The horizons, the physical clock and the readable driver -/

section Defs

variable {Ω : Type*}

/-- The deterministic horizons below `t`: the nonnegative rationals, capped at `t` (`T_k(t) = min(q_k, t)`, `q_k`
an enumeration of `ℚ`). They are dense below `t`, and each reads the physical driver only before `t`. -/
def hz (t : ℝ≥0) (k : ℕ) : ℝ≥0 := min ((Denumerable.ofNat ℚ k : ℝ).toNNReal) t

theorem hz_le (t : ℝ≥0) (k : ℕ) : hz t k ≤ t := min_le_right _ _

/-- Every rational below `t` is a horizon. -/
theorem exists_hz_eq {t : ℝ≥0} {q : ℚ} (hq : (q : ℝ) < t) : ∃ k, hz t k = (q : ℝ).toNNReal := by
  obtain ⟨k, hk⟩ : ∃ k, Denumerable.ofNat ℚ k = q := ⟨_, Denumerable.ofNat_encode q⟩
  refine ⟨k, ?_⟩
  unfold hz
  rw [hk]
  exact min_eq_left ((Real.toNNReal_le_iff_le_coe.2 hq.le))

/-- The local lifetime with horizon `T` on its event (`0` off it). -/
def locLife (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (T : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  (locEv s W Wα ζα GT T).indicator (fun ω => capLife (gb6Curve s W Wα ζα T ω)) ω

/-- The local relative driver with horizon `T` on its event (`0` off it). -/
def locDrv (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (T u : ℝ≥0) (ω : Ω) : ℝ :=
  (locEv s W Wα ζα GT T).indicator (CoordB.drivenDriver (gb6Curve s W Wα ζα T) u) ω

/-- **GB6's relative clock read in the physical history**: the supremum of the local lifetimes of the horizons
before `t`. -/
def physClock (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨆ k, locLife s W Wα ζα GT (hz t k) ω

/-- The horizons whose local curve lives past `u`. -/
def validEv (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (t u : ℝ≥0) (k : ℕ) : Set Ω :=
  {ω | (u : ℝ≥0∞) < locLife s W Wα ζα GT (hz t k) ω}

/-- **GB6's relative driver read in the physical history**: the local driver of the first horizon before `t` whose
curve lives past `u`. -/
def physDrv (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (t u : ℝ≥0) (ω : Ω) : ℝ :=
  locDrv s W Wα ζα GT (hz t (selIdx (validEv s W Wα ζα GT t u) ω)) u ω

end Defs

section Meas

variable {Ω : Type*} {m : MeasurableSpace Ω} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
  {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {t : ℝ≥0}
  (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω) (hrec : Measurable[m] (gb6Rec s Wα ζα))
  (hW : ∀ r ≤ t, Measurable[m] (W r)) (hGTm : MeasurableSet[m] GT)

include hGT hrec hW hGTm

/-- **The physical clock at `t` reads only the record and the physical driver before `t`.** -/
theorem measurable_physClock : Measurable[m] (physClock s W Wα ζα GT t) := by
  let _ : MeasurableSpace Ω := m
  exact Measurable.iSup fun k => measurable_indicator_localLife hGT hrec hW hGTm (hz_le t k)

/-- **The physical relative driver at `t` reads only the record and the physical driver before `t`.** -/
theorem measurable_physDrv (u : ℝ≥0) : Measurable[m] (physDrv s W Wα ζα GT t u) := by
  have hidx : Measurable[m] (selIdx (validEv s W Wα ζα GT t u)) :=
    measurable_selIdx fun k => measurableSet_lt measurable_const
      (measurable_indicator_localLife hGT hrec hW hGTm (hz_le t k))
  exact @Ito.measurable_comp_index Ω ℝ m _ (fun ω k => locDrv s W Wα ζα GT (hz t k) u ω)
    (fun k => measurable_indicator_localDrv hGT hrec hW hGTm (hz_le t k) u) _ hidx

end Meas

/-! ### Identification with a version -/

section Ident

variable {Ω : Type*} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω}
  (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω)

/-- **The pathwise content of a version at one sample** (the clauses of `IsGB6RelVersion` used here): a continuous
relative driver from `0` whose hulls, at every relative clock value before the first contact and not after the
stop, are the mapped physical hulls. -/
def VersionAt (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (γ α : Ω → ℝ≥0 → ℂ) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    (ω : Ω) : Prop :=
  Continuous (fun t => R t ω) ∧ R 0 ω = 0 ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω → ENNReal.ofReal (gb6Clock s W Wα ω t) ≤ V ω →
      fwdHull (fun r : ℝ => R r.toNNReal ω) (gb6Clock s W Wα ω t) =
        relMap (fun r : ℝ => Wα r.toNNReal ω) s '' fwdHull (fun r : ℝ => W r.toNNReal ω) t

omit hGT in
theorem pos_of_physGood {ω : Ω} (hω : PhysGood s W Wα ζα γ α ω) : (0 : ℝ) < s := by
  obtain ⟨-, ⟨-, -, hα⟩, -, hαs, -⟩ := hω
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h | h
  · exfalso
    rw [← h, hα.1] at hαs
    simp [QuantumZipper.H] at hαs
  · exact_mod_cast h

include hGT in
/-- **A version is the local driver** at every relative time below the local lifetime and the stop (uniqueness of
the Loewner driver of the filled local curve, `IsDrivenCurve.segDrv_eq`). -/
theorem eq_localDrv_of_version {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {T : ℝ≥0} {ω : Ω}
    (hω : ω ∈ locEv s W Wα ζα GT T) (hR : VersionAt s W Wα γ α R V ω) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < capLife (gb6Curve s W Wα ζα T ω)) (huV : (u : ℝ≥0∞) ≤ V ω) :
    R u ω = CoordB.drivenDriver (gb6Curve s W Wα ζα T) u ω := by
  have hωG := hω.1.2
  have hT : 0 < T := hω.1.1
  have hs0 := pos_of_physGood (hGT ω hωG)
  obtain ⟨⟨hWc, hW0, hγt⟩, ⟨h0, hc, hα⟩, hs, -, -, htip⟩ := hGT ω hωG
  have hTc := lt_gb6Tc_of_mem_locEv hGT hω
  have hγ : IsGeneratingTrace (fun t => W t ω) ⊤ (phTr W ω) := by
    rw [phTr_eq (hGT ω hωG)]; exact hγt
  have hd : Disjoint (closure (fwdHull (rdrv (gb6Rec s Wα ζα ω)) s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath (fun t => W t ω)) T)) := by
    rw [GaugeE.record_hull_eq s h0 hc hs]
    exact GB6.disjoint_closure_fwdHull_of_lt_firstContactTime hα hc h0 hγt hWc.continuousOn hW0 hs
      ENNReal.coe_lt_top hTc
  have hcv := isDrivenCurve_of_mem_locEv hGT hω
  have hdd : CoordB.drivenDriver (gb6Curve s W Wα ζα T) u ω = segDrv (gb6Curve s W Wα ζα T ω) u := by
    simp only [CoordB.drivenDriver, hu, ↓reduceIte, segDriver]
  rw [hdd]
  obtain ⟨hRc, hR0, hhull⟩ := hR
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h0u | hu0
  · subst h0u
    rw [hR0]
    have h := hcv.segDriver_spec.1
    simp only [segDriver] at h
    exact_mod_cast h.symm
  have hu' : ENNReal.ofReal (u : ℝ) < capLife (gb6Curve s W Wα ζα T ω) := by
    rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨hS0, hSu⟩ := hcv.capInv_spec u.coe_nonneg hu'
  have hSpos : 0 < capInv (gb6Curve s W Wα ζα T ω) u := by
    rcases eq_or_lt_of_le hS0 with h | h
    · exfalso
      rw [← h, hcv.capClock_zero] at hSu
      exact (ne_of_lt hu0) (by exact_mod_cast hSu)
    · exact h
  have hK : ∀ τ ∈ Icc 0 (capInv (gb6Curve s W Wα ζα T ω) u),
      fwdHull (fun r : ℝ => R r.toNNReal ω) (capClock (gb6Curve s W Wα ζα T ω) τ) =
        fillH (gb6Curve s W Wα ζα T ω '' Icc 0 τ) := by
    intro τ hτ
    have hτT : clockOf T τ < T := clockOf_lt (by exact_mod_cast hT) hτ.1
    have hτ0 : 0 ≤ clockOf T τ := clockOf_nonneg (by exact_mod_cast hT) hτ.1
    have hcap := CoordB.capClock_localCurve (continuous_rdrv _) (rdrv_zero _) hs0 htip hWc hW0 hγ hd hT hτ.1
    have ht''c : (((clockOf T τ).toNNReal : ℝ≥0) : ℝ) = clockOf T τ := Real.coe_toNNReal _ hτ0
    have hclk : gb6Clock s W Wα ω (clockOf T τ).toNNReal = capClock (gb6Curve s W Wα ζα T ω) τ := by
      rw [gb6Curve, hcap, gb6Clock, ht''c, GaugeE.record_relClock_eq s h0 hc hs]
      rfl
    have hle : capClock (gb6Curve s W Wα ζα T ω) τ ≤ u := by
      rw [← hSu]
      exact hcv.strictMonoOn_capClock.monotoneOn hτ.1 hS0 hτ.2
    have hlt : (((clockOf T τ).toNNReal : ℝ≥0) : ℝ≥0∞) < gb6Tc s γ α ω := by
      refine lt_trans (ENNReal.coe_lt_coe.2 ?_) hTc
      exact (Real.toNNReal_lt_iff_lt_coe hτ0).2 hτT
    have hV : ENNReal.ofReal (gb6Clock s W Wα ω (clockOf T τ).toNNReal) ≤ V ω := by
      rw [hclk]
      exact (ENNReal.ofReal_le_ofReal hle).trans (by rwa [ENNReal.ofReal_coe_nnreal])
    have h1 := hhull _ hlt hV
    rw [hclk] at h1
    have hmap : relMap (fun r : ℝ => Wα r.toNNReal ω) s = relMap (rdrv (gb6Rec s Wα ζα ω)) s :=
      (GaugeE.record_relMap_eq s h0 hc hs).symm
    rw [h1, hmap, ht''c]
    obtain ⟨V', -, -, hK'⟩ := CoordB.exists_relBdry_prefix_driver (continuous_rdrv _) (rdrv_zero _) hs0 htip
      hWc hW0 hγ hd
    have hq : clockOf T τ ∈ Icc (0 : ℝ) T := ⟨hτ0, hτT.le⟩
    have himg : gb6Curve s W Wα ζα T ω '' Icc 0 τ =
        (fun r : ℝ => CoordB.relBdry (rdrv (gb6Rec s Wα ζα ω)) s (phTr W ω r.toNNReal)) '' Icc 0 (clockOf T τ) :=
      image_relCurve_Icc (L := (T : ℝ)) (fun r : ℝ => CoordB.relBdry (rdrv (gb6Rec s Wα ζα ω)) s
        (phTr W ω r.toNNReal)) (by exact_mod_cast hT) hτ.1
    rw [himg]
    exact ((hK' _ hq).2.1.symm.trans (hK' _ hq).2.2).symm
  have hRc' : Continuous (fun r : ℝ => R r.toNNReal ω) := hRc.comp continuous_real_toNNReal
  have hR0' : (fun r : ℝ => R r.toNNReal ω) 0 = 0 := by simp only [Real.toNNReal_zero, hR0]
  have h := hcv.segDrv_eq hSpos hRc' hR0' hK u.coe_nonneg hSu.ge
  rw [h]
  simp only [Real.toNNReal_coe]

omit hGT in
/-- Off the good event the physical clock vanishes. -/
theorem physClock_eq_zero_of_notMem {t : ℝ≥0} {ω : Ω} (hω : ω ∉ GT) : physClock s W Wα ζα GT t ω = 0 := by
  unfold physClock locLife
  refine ENNReal.iSup_eq_zero.2 fun k => indicator_of_notMem (fun h => hω h.1.2) _

include hGT in
/-- **A version is the physical relative driver** at every relative time below the physical clock and the stop
(pathwise, on the good event). -/
theorem eq_physDrv_of_version {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ω : Ω}
    (hR : ω ∈ GT → VersionAt s W Wα γ α R V ω) (t u : ℝ≥0)
    (hu : (u : ℝ≥0∞) < physClock s W Wα ζα GT t ω) (huV : (u : ℝ≥0∞) ≤ V ω) :
    R u ω = physDrv s W Wα ζα GT t u ω := by
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 hu
  have hv := selIdx_mem (valid := validEv s W Wα ζα GT t u) (show ω ∈ validEv s W Wα ζα GT t u k from hk)
  set k' := selIdx (validEv s W Wα ζα GT t u) ω
  have hmem : ω ∈ locEv s W Wα ζα GT (hz t k') := by
    by_contra hn
    have h0 : locLife s W Wα ζα GT (hz t k') ω = 0 := indicator_of_notMem hn _
    have hv' : (u : ℝ≥0∞) < locLife s W Wα ζα GT (hz t k') ω := hv
    rw [h0] at hv'
    exact not_lt_zero hv'
  have hlife : (u : ℝ≥0∞) < capLife (gb6Curve s W Wα ζα (hz t k') ω) := by
    have hv' : (u : ℝ≥0∞) < locLife s W Wα ζα GT (hz t k') ω := hv
    rwa [locLife, indicator_of_mem hmem] at hv'
  show R u ω = locDrv s W Wα ζα GT (hz t k') u ω
  rw [locDrv, indicator_of_mem hmem]
  exact eq_localDrv_of_version hGT hmem (hR hmem.1.2) hlife huV

end Ident

end InteractingSLE.Supp8.RelSafe
