/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NvRel

/-!
# SB2(2)'s v6 measurability: measurable surrogates of the stage readings

Packet PROVE-GW2-GEOM2, round 10 (D28, item (A)). For a measurable actual family `Ê`, regular with regular launches
at every sample, read as `Dh ω = fun j => Ê j ω`, the v6 rule's stage readings have measurable surrogates:
* `vAt`, `shm`: the stage shift (the masked visit time at `relOff`);
* `Lhm`: the shifted lifetime;
* `τm`: the stage time of the `i`-th rational curve time;
* `ptm`: the actual point there;
* `Ym`: its lift;
* `Gv`: the good reading, in the version chart's domain;
* `Vm`: the version chart at the lift.

They agree with the rule where it matters (`shm_eq`, `Lhm_eq`, `ptm_eq`, `goodRead_iff_Gv`, `cρ3_ratPt_eq_Vm`), off the
v4 zero events, at a launched stage, on the record-good event. Measurability:
* `measurable_vAt`, `measurable_shm`, `measurable_Lhm`, `measurable_τm`, `measurable_ptm`, `measurable_Ym`,
  `measurableSet_Gv`, `measurable_Vm`;
* `visitTime'_le_life`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Nv

open Lk Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal LuM GW1W GW1Bookkeep

/-- The first visit is at most the lifetime. -/
theorem visitTime'_le_life (s : ExplState) (e : Drv) (z : ℂ) : (visitTime' s e z : ℝ≥0∞) ≤ e.2 := by
  unfold visitTime'
  rcases (({t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2 ∧ pcPt s e t = z}).eq_empty_or_nonempty) with hE | ⟨t, ht⟩
  · rw [hE, NNReal.sInf_empty]; exact zero_le
  · exact le_trans (ENNReal.coe_le_coe.2 (csInf_le ⟨0, fun _ _ => zero_le⟩ ht)) ht.1

/-! ### The surrogates -/

section Surr

variable {Ω : Type*} (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (R : ℝ) (Ê : ℕ → Ω → Drv)

/-- The actual family as a sample-indexed family. -/
abbrev Dh : Ω → ℕ → Drv := fun ω j => Ê j ω

/-- The relative offset of the regular family. -/
abbrev rO (ω : Ω) : ℕ := relOff κ θ b₁ J₁ R (fun j => Ê j ω)

/-- The launch events of the regular family. -/
abbrev LEv (n : ℕ) : Set Ω := {ω | (wRun κ θ b₁ J₁ (fun j => Ê j ω) (n + 1)).2.2.2.1 n ≠ none}

/-- The masked first visit of `R` at instruction `n`. -/
def vAt (n : ℕ) (ω : Ω) : ℝ≥0 :=
  if ω ∈ LEv κ θ b₁ J₁ Ê n then visitTime' (wRun κ θ b₁ J₁ (fun j => Ê j ω) n) (Ê n ω) (R : ℂ) else 0

/-- **The surrogate stage shift.** -/
def shm (j : ℕ) (ω : Ω) : ℝ≥0 := if j = 0 then vAt κ θ b₁ J₁ R Ê (rO κ θ b₁ J₁ R Ê ω) ω else 0

/-- **The surrogate shifted lifetime.** -/
def Lhm (j : ℕ) (ω : Ω) : ℝ≥0∞ := (Ê (j + rO κ θ b₁ J₁ R Ê ω) ω).2 - shm κ θ b₁ J₁ R Ê j ω

/-- The stage time of the `i`-th rational curve time. -/
def τm (j i : ℕ) (ω : Ω) : ℝ≥0 := stTime (Lhm κ θ b₁ J₁ R Ê j ω) (ratPt i)

/-- The actual time of the `i`-th reading. -/
def σm (j i : ℕ) (ω : Ω) : ℝ≥0 := shm κ θ b₁ J₁ R Ê j ω + τm κ θ b₁ J₁ R Ê j i ω

/-- The actual time of the `i`-th reading, truncated at the lifetime of instruction `n`. -/
def σAt (j i n : ℕ) (ω : Ω) : ℝ≥0 :=
  if (σm κ θ b₁ J₁ R Ê j i ω : ℝ≥0∞) ≤ (Ê n ω).2 then σm κ θ b₁ J₁ R Ê j i ω else 0

/-- The masked actual point of the `i`-th reading at instruction `n`. -/
def pAt (j i n : ℕ) (ω : Ω) : ℂ :=
  if ω ∈ LEv κ θ b₁ J₁ Ê n then pcPt (wRun κ θ b₁ J₁ (fun j => Ê j ω) n) (Ê n ω) (σAt κ θ b₁ J₁ R Ê j i n ω)
  else 0

/-- **The surrogate actual point of the `i`-th reading.** -/
def ptm (j i : ℕ) (ω : Ω) : ℂ := pAt κ θ b₁ J₁ R Ê j i (j + rO κ θ b₁ J₁ R Ê ω) ω

open Classical in
/-- **The surrogate lift of the `i`-th reading.** -/
def Ym (c : Chart) (m : ℝ) (j i : ℕ) (ω : Ω) : ℂ :=
  if ptm κ θ b₁ J₁ R Ê j i ω ∈ c.2.1 '' H then c.1 (ptm κ θ b₁ J₁ R Ê j i ω) + m else 0

/-- **The surrogate good reading**, in the version chart's domain. -/
def Gv (c : Chart) (m : ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (j i : ℕ) (F : ℕ → Ω → Drv) (ω : Ω) : Prop :=
  ((τm κ θ b₁ J₁ R Ê j i ω : ℝ≥0∞) ≤ Lhm κ θ b₁ J₁ R Ê j ω ∧ ptm κ θ b₁ J₁ R Ê j i ω ∈ c.2.1 '' H) ∧
    Ym κ θ b₁ J₁ R Ê c m j i ω ∈ (relVer κ θ b₂ J₂ j F ω).dom

/-- **The surrogate reading**: the version chart at the lift (masked by its domain). -/
def Vm (c : Chart) (m : ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (j i : ℕ) (F : ℕ → Ω → Drv) : Ω → ℂ :=
  {ω | Ym κ θ b₁ J₁ R Ê c m j i ω ∈ (relVer κ θ b₂ J₂ j F ω).dom}.indicator
    fun ω => (relVer κ θ b₂ J₂ j F ω).1 (Ym κ θ b₁ J₁ R Ê c m j i ω)

end Surr

/-! ### Agreement with the rule -/

section Eq

variable {Ω : Type*} {κ θ : ℝ} {b₁ : ℝ → ℝ} {J₁ : Finset ℝ} {b₂ : ℝ → ℝ} {J₂ : Finset ℝ} {R : ℝ} {c : Chart}
  {m : ℝ} {Ê : ℕ → Ω → Drv} {ω : Ω} {j : ℕ}

/-- The launch event of a stage is the launch event at its actual instruction (in two steps, to keep the kernel's
conversion cheap). -/
theorem launchEv_mem_LEv (hL : ω ∈ launchEv κ θ b₁ J₁ R (Dh Ê) j) :
    ω ∈ LEv κ θ b₁ J₁ Ê (j + rO κ θ b₁ J₁ R Ê ω) := by
  have h1 : (wRun κ θ b₁ J₁ (fun i => Ê i ω) (j + relOff κ θ b₁ J₁ R (fun i => Ê i ω) + 1)).2.2.2.1
      (j + relOff κ θ b₁ J₁ R (fun i => Ê i ω)) ≠ none := hL
  exact h1

/-- **The stage shift is the surrogate** (at stage `0` off a zero root, given the launch at `relOff`). -/
theorem stageShift_eq_shm
    (hl : j = 0 → (wRun κ θ b₁ J₁ (fun i => Ê i ω) (rO κ θ b₁ J₁ R Ê ω + 1)).2.2.2.1 (rO κ θ b₁ J₁ R Ê ω) ≠ none) :
    stageShift κ θ b₁ J₁ R (Dh Ê) j ω = shm κ θ b₁ J₁ R Ê j ω := by
  unfold stageShift shm
  by_cases hj : j = 0
  · have hL : ω ∈ LEv κ θ b₁ J₁ Ê (rO κ θ b₁ J₁ R Ê ω) := hl hj
    simp only [hj, ↓reduceIte, vAt, hL]
    rfl
  · simp only [hj, ↓reduceIte]

theorem stL_eq_Lhm
    (hl : j = 0 → (wRun κ θ b₁ J₁ (fun i => Ê i ω) (rO κ θ b₁ J₁ R Ê ω + 1)).2.2.2.1 (rO κ θ b₁ J₁ R Ê ω) ≠ none) :
    stL κ θ b₁ J₁ R (Dh Ê) j ω = Lhm κ θ b₁ J₁ R Ê j ω := by
  unfold stL Lhm
  rw [stageShift_eq_shm hl]

/-- The surrogate shift is at most the lifetime (given the launch at `relOff` at stage `0`). -/
theorem shm_le_life (j : ℕ) : (shm κ θ b₁ J₁ R Ê j ω : ℝ≥0∞) ≤ (Ê (j + rO κ θ b₁ J₁ R Ê ω) ω).2 := by
  unfold shm
  by_cases hj : j = 0
  · simp only [hj, ↓reduceIte, zero_add]
    unfold vAt
    split_ifs
    · exact visitTime'_le_life _ _ _
    · simp
  · simp [hj]

/-- **At a good stage time the surrogate point is the actual stage point.** -/
theorem ptm_eq (i : ℕ)
    (hl : j = 0 → (wRun κ θ b₁ J₁ (fun i => Ê i ω) (rO κ θ b₁ J₁ R Ê ω + 1)).2.2.2.1 (rO κ θ b₁ J₁ R Ê ω) ≠ none)
    (hL : ω ∈ launchEv κ θ b₁ J₁ R (Dh Ê) j)
    (hτ : (τm κ θ b₁ J₁ R Ê j i ω : ℝ≥0∞) ≤ Lhm κ θ b₁ J₁ R Ê j ω) :
    ptm κ θ b₁ J₁ R Ê j i ω = stP κ θ b₁ J₁ R (Dh Ê) j ω (τm κ θ b₁ J₁ R Ê j i ω) := by
  have hσ : (σm κ θ b₁ J₁ R Ê j i ω : ℝ≥0∞) ≤ (Ê (j + rO κ θ b₁ J₁ R Ê ω) ω).2 := by
    unfold σm
    rw [ENNReal.coe_add]
    calc (shm κ θ b₁ J₁ R Ê j ω : ℝ≥0∞) + τm κ θ b₁ J₁ R Ê j i ω
        ≤ shm κ θ b₁ J₁ R Ê j ω + Lhm κ θ b₁ J₁ R Ê j ω := add_le_add_right hτ _
      _ = (Ê (j + rO κ θ b₁ J₁ R Ê ω) ω).2 := by unfold Lhm; exact add_tsub_cancel_of_le (shm_le_life j)
  have hLe : ω ∈ LEv κ θ b₁ J₁ Ê (j + rO κ θ b₁ J₁ R Ê ω) := launchEv_mem_LEv hL
  have h2 : ptm κ θ b₁ J₁ R Ê j i ω = pcPt (wRun κ θ b₁ J₁ (fun j => Ê j ω) (j + rO κ θ b₁ J₁ R Ê ω))
      (Ê (j + rO κ θ b₁ J₁ R Ê ω) ω) (σm κ θ b₁ J₁ R Ê j i ω) := by
    unfold ptm pAt σAt
    split_ifs
    rfl
  rw [h2]
  have h3 : stageShift κ θ b₁ J₁ R (Dh Ê) j ω = shm κ θ b₁ J₁ R Ê j ω := stageShift_eq_shm hl
  show _ = pcPt _ _ (stageShift κ θ b₁ J₁ R (Dh Ê) j ω + τm κ θ b₁ J₁ R Ê j i ω)
  rw [h3]
  rfl

/-- **The good readings are the surrogate good readings** (on the record-good event). -/
theorem goodRead_iff_Gv (i : ℕ) {F : ℕ → Ω → Drv} (hFr : ∀ i < j, ∀ ω, IsRegularDriver (F i ω))
    (hl : j = 0 → (wRun κ θ b₁ J₁ (fun i => Ê i ω) (rO κ θ b₁ J₁ R Ê ω + 1)).2.2.2.1 (rO κ θ b₁ J₁ R Ê ω) ≠ none)
    (hL : ω ∈ launchEv κ θ b₁ J₁ R (Dh Ê) j) (hR : ω ∈ recGoodEv κ θ b₂ J₂ j F) :
    GoodRead c m (stP κ θ b₁ J₁ R (Dh Ê) j ω) (stL κ θ b₁ J₁ R (Dh Ê) j ω)
        (wRun κ θ b₂ J₂ (fun i => F i ω) j) i ↔ Gv κ θ b₁ J₁ R Ê c m b₂ J₂ j i F ω := by
  classical
  have hst : stTime (stL κ θ b₁ J₁ R (Dh Ê) j ω) (ratPt i) = τm κ θ b₁ J₁ R Ê j i ω := by
    unfold τm; rw [stL_eq_Lhm hl]
  unfold GoodRead Gv goodTp
  rw [hst, stChart_eq_relVer hFr hR, stL_eq_Lhm hl]
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hτ, hp⟩, hd⟩
    rw [← ptm_eq i hl hL hτ] at hp hd
    refine ⟨⟨hτ, hp⟩, ?_⟩
    unfold Ym
    simp only [hp, ↓reduceIte]
    exact hd
  · rintro ⟨⟨hτ, hp⟩, hd⟩
    rw [← ptm_eq i hl hL hτ]
    refine ⟨⟨hτ, hp⟩, ?_⟩
    unfold Ym at hd
    simp only [hp, ↓reduceIte] at hd
    exact hd

/-- **At a surrogate good reading the stage curve is the surrogate reading** (on the record-good event). -/
theorem cρ3_ratPt_eq_Vm (i : ℕ) {F : ℕ → Ω → Drv} (hFr : ∀ i < j, ∀ ω, IsRegularDriver (F i ω))
    (hl : j = 0 → (wRun κ θ b₁ J₁ (fun i => Ê i ω) (rO κ θ b₁ J₁ R Ê ω + 1)).2.2.2.1 (rO κ θ b₁ J₁ R Ê ω) ≠ none)
    (hL : ω ∈ launchEv κ θ b₁ J₁ R (Dh Ê) j) (hR : ω ∈ recGoodEv κ θ b₂ J₂ j F)
    (hG : Gv κ θ b₁ J₁ R Ê c m b₂ J₂ j i F ω) :
    cρ3 κ θ b₁ J₁ b₂ J₂ R c m (Dh Ê) j F ω (ratPt i) = Vm κ θ b₁ J₁ R Ê c m b₂ J₂ j i F ω := by
  classical
  have hgr := (goodRead_iff_Gv i hFr hl hL hR).2 hG
  have h := stCurvep_ratPt_of_goodRead hgr
  have hst : stTime (stL κ θ b₁ J₁ R (Dh Ê) j ω) (ratPt i) = τm κ θ b₁ J₁ R Ê j i ω := by
    unfold τm; rw [stL_eq_Lhm hl]
  rw [hst, ← ptm_eq i hl hL hG.1.1, stChart_eq_relVer hFr hR] at h
  unfold cρ3 cΦ3
  refine h.trans ?_
  unfold Vm
  rw [indicator_of_mem (show ω ∈ {ω | Ym κ θ b₁ J₁ R Ê c m j i ω ∈ (relVer κ θ b₂ J₂ j F ω).dom} from hG.2)]
  unfold Ym
  simp only [hG.1.2, ↓reduceIte]
  rfl

end Eq

/-! ### Measurability of the surrogates -/

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {κ θ : ℝ} {b₁ : ℝ → ℝ} {J₁ : Finset ℝ} {R : ℝ}
  (hb₁ : IsPiecewiseConstantBoundaryData b₁ J₁) {Ê : ℕ → Ω → Drv} (hÊm : ∀ j, Measurable (Ê j))
  (hÊreg : ∀ j ω, IsRegularDriver (Ê j ω))
  (hÊP : ∀ ω, RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) fun j => Ê j ω)

include hb₁ hÊm hÊreg hÊP

theorem measurable_vAt (n : ℕ) : Measurable (vAt κ θ b₁ J₁ R Ê n) :=
  measurable_visitTime hb₁ hÊm hÊreg hÊP n (R : ℂ)

theorem measurable_shm (j : ℕ) : Measurable (shm κ θ b₁ J₁ R Ê j) := by
  unfold shm
  by_cases hj : j = 0
  · simp only [hj, ↓reduceIte]
    exact measurable_natIdx (x := rO κ θ b₁ J₁ R Ê) (measurableSet_relOff_eq hb₁ hÊm hÊreg hÊP R)
      (g := vAt κ θ b₁ J₁ R Ê) (measurable_vAt hb₁ hÊm hÊreg hÊP)
  · simp only [hj, ↓reduceIte]
    exact measurable_const

theorem measurable_Lhm (j : ℕ) : Measurable (Lhm κ θ b₁ J₁ R Ê j) :=
  (measurable_life_relOff hb₁ hÊm hÊreg hÊP R j).sub
    (measurable_coe_nnreal_ennreal.comp (measurable_shm hb₁ hÊm hÊreg hÊP j))

theorem measurable_τm (j i : ℕ) : Measurable (τm κ θ b₁ J₁ R Ê j i) :=
  measurable_stTime (measurable_Lhm hb₁ hÊm hÊreg hÊP j) _

theorem measurable_σm (j i : ℕ) : Measurable (σm κ θ b₁ J₁ R Ê j i) :=
  (measurable_shm hb₁ hÊm hÊreg hÊP j).add (measurable_τm hb₁ hÊm hÊreg hÊP j i)

theorem measurable_ptm (j i : ℕ) : Measurable (ptm κ θ b₁ J₁ R Ê j i) := by
  classical
  have hσ := measurable_σm hb₁ hÊm hÊreg hÊP (R := R) j i
  have hpA : ∀ n, Measurable (pAt κ θ b₁ J₁ R Ê j i n) := fun n => by
    have hσA : Measurable (σAt κ θ b₁ J₁ R Ê j i n) :=
      Measurable.ite (measurableSet_le (measurable_coe_nnreal_ennreal.comp hσ) (measurable_snd.comp (hÊm n))) hσ
        measurable_const
    refine measurable_pcPt_at hb₁ hÊm hÊreg hÊP n hσA fun ω _ => ?_
    unfold σAt
    split_ifs with h
    · exact h
    · simp
  exact measurable_at_relOff hb₁ hÊm hÊreg hÊP R j (g := fun n => pAt κ θ b₁ J₁ R Ê j i n) hpA

omit hb₁ hÊm hÊreg hÊP in
/-- The chart's domain is a Borel set and its forward map is continuous there. -/
theorem measurable_lift {c : Chart} (hcc : c.IsConformal) (m : ℝ) :
    MeasurableSet (c.2.1 '' H) ∧ ContinuousOn (fun z => c.1 z + m) (c.2.1 '' H) := by
  refine ⟨hcc.isOpen_image.measurableSet, ?_⟩
  have h := hcc.differentiableOn_fwd.continuousOn
  rw [hcc.coe_dom] at h
  exact h.add continuousOn_const

theorem measurable_Ym {c : Chart} (hcc : c.IsConformal) (m : ℝ) (j i : ℕ) :
    Measurable (Ym κ θ b₁ J₁ R Ê c m j i) := by
  classical
  obtain ⟨hU, hcont⟩ := measurable_lift hcc m
  have hpw : Measurable ((c.2.1 '' H).piecewise (fun z => c.1 z + m) (fun _ => (0 : ℂ))) :=
    hcont.measurable_piecewise continuousOn_const hU
  have e : Ym κ θ b₁ J₁ R Ê c m j i =
      (c.2.1 '' H).piecewise (fun z => c.1 z + m) (fun _ => (0 : ℂ)) ∘ ptm κ θ b₁ J₁ R Ê j i := by
    funext ω
    simp only [Ym, Function.comp_apply, Set.piecewise]
  rw [e]
  exact hpw.comp (measurable_ptm hb₁ hÊm hÊreg hÊP j i)

theorem measurableSet_Gv [StandardBorelSpace Ω] {b₂ : ℝ → ℝ} {J₂ : Finset ℝ}
    (hb₂ : IsPiecewiseConstantBoundaryData b₂ J₂) {c : Chart} (hcc : c.IsConformal) (m : ℝ) {j : ℕ} (i : ℕ)
    {F : ℕ → Ω → Drv} (hFm : ∀ i < j, Measurable (F i)) (hFr : ∀ i < j, ∀ ω, IsRegularDriver (F i ω)) :
    MeasurableSet {ω | Gv κ θ b₁ J₁ R Ê c m b₂ J₂ j i F ω} := by
  have hU := (measurable_lift hcc m).1
  refine ((measurableSet_le (measurable_coe_nnreal_ennreal.comp (measurable_τm hb₁ hÊm hÊreg hÊP j i))
    (measurable_Lhm hb₁ hÊm hÊreg hÊP j)).inter ((measurable_ptm hb₁ hÊm hÊreg hÊP j i) hU)).inter ?_
  exact (isMeasChart_relVer (θ := θ) (κ := κ) hb₂ hFm hFr).measurableSet_mem_dom_of_measurable
    (measurable_Ym hb₁ hÊm hÊreg hÊP hcc m j i)

theorem measurable_Vm [StandardBorelSpace Ω] {b₂ : ℝ → ℝ} {J₂ : Finset ℝ}
    (hb₂ : IsPiecewiseConstantBoundaryData b₂ J₂) {c : Chart} (hcc : c.IsConformal) (m : ℝ) {j : ℕ} (i : ℕ)
    {F : ℕ → Ω → Drv} (hFm : ∀ i < j, Measurable (F i)) (hFr : ∀ i < j, ∀ ω, IsRegularDriver (F i ω)) :
    Measurable (Vm κ θ b₁ J₁ R Ê c m b₂ J₂ j i F) :=
  (isMeasChart_relVer (θ := θ) (κ := κ) hb₂ hFm hFr).measurable_fwd_of_measurable
    (measurable_Ym hb₁ hÊm hÊreg hÊP hcc m j i)

end Meas

end InteractingSLE.Theorem14.SB.Nv
