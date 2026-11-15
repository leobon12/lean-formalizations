/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS5Stop

/-!
# On the windows, the restarted word is read from the stopped data

Packet PROVE-STAGED-S5 ((M3) of `planning/handoffs/PROVE-STAGED-S3.md` §5.2). For a good glued sample `p` (in `E`, with
a good flow path) whose last switch `τ` and own time `q` precede the first contact, and with `S₀ + t < σ(q)`, the
restarted word of PROVE-STAGED-S3 up to the restarted time `t` agrees with its stopped-data version at
`y = stopD … q s p` (`StagedS5Stop`):

* `mem_s5Win_iff`: the window in stopped data;
* `kW_eq_s5` (the template's `img_eq_stopD`): the killed image drivers agree below `σ(q)`;
* `s5S₀_stopX`, `s3W_eq_s5W`, `lt_s3ζ_and_lt_s5ζ`, `s3XL_eq_s5XL`, `s3VL_eq_s5VL` (and the right marks), and
  `s3Chart_eq_s5Chart`.

Conditional helpers with distinct names; R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Sec5.CrossCond.StagedS5

open WangWu WangWu.ImgWord Coupling StagedS3 StagedFinal Word49 LawUnique
open Prop59Pieces (arcW arcVL arcVR arcζ IsKilledFamily)
open Sec7.Lemma71C (capClock)

section Rep

variable {Ω : Type*} {s : ℝ≥0} {Wj : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)} {q τ : ℚ}
  {p : Ω × HistorySpace 0 0} {nL nR : ℕ}

/-- The good stopped data of a good glued sample. -/
def stopX (hq : 0 < q) (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hp : p ∈ E)
    (hg : Aux50Hit.IsGoodPath Wj (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
      (fun _ => ⊤) p.1) : XD s q :=
  ⟨stopD Wj (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q s p,
    isGoodD_stopD hq hEg hp hg⟩

variable (hq : 0 < q) (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hp : p ∈ E)
  (hg : Aux50Hit.IsGoodPath Wj (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
    (fun _ => ⊤) p.1)
include hq hEg hp hg

theorem capClock_stopX {u : ℝ} (hu : u ≤ q) :
    capClock (s5γ s q (stopX hq hEg hp hg)) u = capClock (gCurve s (fun _ => ⊤) Wj E p) u :=
  WangWu.capClock_congr fun _ hv => gammaD_stopD hp hg (hv.2.trans hu)

theorem mem_PcD_stopX_iff {u : ℝ} (hu : u ≤ q) :
    u ∈ PcD s (stopX hq hEg hp hg).1 ↔ u ∈ gPre s (fun _ => ⊤) Wj E p :=
  mem_PcD_stopD_iff hp hg hu

theorem mem_s5Alive_stopX_iff (hτq : τ < q) :
    stopX hq hEg hp hg ∈ s5Alive s q τ ↔ (τ : ℝ) ∈ gPre s (fun _ => ⊤) Wj E p := by
  have hτq' : (τ : ℝ) < q := by exact_mod_cast hτq
  change (τ : ℝ) ∈ PD q s (stopX hq hEg hp hg).1 ↔ _
  rw [PD, mem_inter_iff, mem_Iio, mem_PcD_stopX_iff hq hEg hp hg hτq'.le]
  exact ⟨fun h => h.1, fun h => ⟨h, hτq'⟩⟩

theorem s5S₀_stopX (hτq : τ < q) (hal : p ∈ s3Alive s Wj E τ) :
    s5S₀ s q τ (stopX hq hEg hp hg) = s3Start s Wj E τ p := by
  have hτq' : (τ : ℝ) ≤ q := by exact_mod_cast hτq.le
  rw [s5S₀_of_alive ((mem_s5Alive_stopX_iff hq hEg hp hg hτq).2 hal.2), capClock_stopX hq hEg hp hg hτq',
    s3Start_of_mem hal]

/-- **The window in stopped data.** -/
theorem mem_s5Win_iff (hτq : τ ≤ q) (r : ℝ≥0) :
    stopX hq hEg hp hg ∈ s5Win s q τ r ↔ p ∈ s3Alive s Wj E τ ∧ (q : ℝ) ∈ gPre s (fun _ => ⊤) Wj E p ∧
      ((s3Start s Wj E τ p + r : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) Wj E p) q := by
  have hτq' : (τ : ℝ) ≤ q := by exact_mod_cast hτq
  have hcap : ∀ u : ℚ, (u : ℝ) ≤ q → (u : ℝ) ∈ gPre s (fun _ => ⊤) Wj E p →
      capD s q u (stopX hq hEg hp hg) = capClock (gCurve s (fun _ => ⊤) Wj E p) u := fun u huq hu => by
    rw [capD, indicator_of_mem (show stopX hq hEg hp hg ∈ {x : XD s q | (u : ℝ) ∈ PcD s x.1} from
      (mem_PcD_stopX_iff hq hEg hp hg huq).2 hu)]
    exact capClock_stopX hq hEg hp hg huq
  simp only [s5Win, mem_ofPred_eq, mem_PcD_stopX_iff hq hEg hp hg hτq', mem_PcD_stopX_iff hq hEg hp hg le_rfl]
  constructor
  · rintro ⟨hτP, hqP, hlt⟩
    have hal : p ∈ s3Alive s Wj E τ := ⟨hp, hτP⟩
    rw [hcap τ hτq' hτP, hcap q le_rfl hqP, ← s3Start_of_mem hal] at hlt
    exact ⟨hal, hqP, hlt⟩
  · rintro ⟨hal, hqP, hlt⟩
    refine ⟨hal.2, hqP, ?_⟩
    rw [hcap τ hτq' hal.2, hcap q le_rfl hqP, ← s3Start_of_mem hal]
    exact hlt

/-- **The killed image drivers agree below `σ(q)`** (the template's `img_eq_stopD`). -/
theorem kW_eq_s5 (hqP : (q : ℝ) ∈ gPre s (fun _ => ⊤) Wj E p) {v : ℝ≥0}
    (hv : (v : ℝ) < capClock (gCurve s (fun _ => ⊤) Wj E p) q) :
    kW (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p) v =
        kW (s5γ s q (stopX hq hEg hp hg)) (s5P s q (stopX hq hEg hp hg)) v ∧
      (v : WithTop ℝ≥0) < kLife (s5γ s q (stopX hq hEg hp hg)) (s5P s q (stopX hq hEg hp hg)) ∧
      (v : WithTop ℝ≥0) < kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p) := by
  obtain ⟨h1, h2, h3, -, -⟩ := img_eq_stopD (VL := (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ))
    (VR := (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)) (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) hq hEg hp hg
    (le_refl q) hqP hv (le_refl v)
  exact ⟨h3, h1, h2⟩

/-- The killed paths agree on `[0, S]` for `S < σ(q)`. -/
theorem kPath_eqOn_s5 (hqP : (q : ℝ) ∈ gPre s (fun _ => ⊤) Wj E p) {S : ℝ≥0}
    (hS : (S : ℝ) < capClock (gCurve s (fun _ => ⊤) Wj E p) q) :
    EqOn (kPath (s5γ s q (stopX hq hEg hp hg)) (s5P s q (stopX hq hEg hp hg)))
      (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) (Icc 0 (S : ℝ)) := by
  intro r hr
  have hrS : r.toNNReal ≤ S := (Real.toNNReal_le_iff_le_coe).2 hr.2
  have hlt : ((r.toNNReal : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) Wj E p) q :=
    lt_of_le_of_lt (NNReal.coe_le_coe.2 hrS) hS
  exact (kW_eq_s5 hq hEg hp hg hqP hlt).1.symm

variable (hτq : τ < q) (hal : p ∈ s3Alive s Wj E τ) (hqP : (q : ℝ) ∈ gPre s (fun _ => ⊤) Wj E p)
  {t : ℝ≥0} (hwin : ((s3Start s Wj E τ p + t : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) Wj E p) q)
include hτq hal hqP hwin

theorem s3W_eq_s5W {u : ℝ≥0} (hut : u ≤ t) :
    s3W s Wj E τ u p = s5W s q τ u (stopX hq hEg hp hg) := by
  have hS₀ := s5S₀_stopX hq hEg hp hg hτq hal
  have hv1 : ((s3Start s Wj E τ p + u : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) Wj E p) q :=
    lt_of_le_of_lt (NNReal.coe_le_coe.2 (add_le_add_right hut _)) hwin
  have hv0 : ((s3Start s Wj E τ p : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) Wj E p) q :=
    lt_of_le_of_lt (NNReal.coe_le_coe.2 le_self_add) hwin
  obtain ⟨e1, l1, l1'⟩ := kW_eq_s5 hq hEg hp hg hqP hv1
  obtain ⟨e0, -, -⟩ := kW_eq_s5 hq hEg hp hg hqP hv0
  have hz1 : (u : ℝ≥0∞) < s3ζ s Wj E τ p := Prop59Pieces.lt_arcζ_iff.2 ⟨mem_univ _, l1'⟩
  have hz2 : (u : ℝ≥0∞) < s5ζ s q τ (stopX hq hEg hp hg) :=
    Prop59Pieces.lt_arcζ_iff.2 ⟨mem_univ _, by rw [hS₀]; exact l1⟩
  rw [s3W, Prop59Pieces.arcW_of_lt hz1, s5W, Prop59Pieces.arcW_of_lt hz2, hS₀, e1, e0]

theorem lt_s3ζ_and_lt_s5ζ {u : ℝ≥0} (hut : u ≤ t) :
    (u : ℝ≥0∞) < s3ζ s Wj E τ p ∧ (u : ℝ≥0∞) < s5ζ s q τ (stopX hq hEg hp hg) := by
  have hS₀ := s5S₀_stopX hq hEg hp hg hτq hal
  have hv1 : ((s3Start s Wj E τ p + u : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) Wj E p) q :=
    lt_of_le_of_lt (NNReal.coe_le_coe.2 (add_le_add_right hut _)) hwin
  obtain ⟨-, l1, l1'⟩ := kW_eq_s5 hq hEg hp hg hqP hv1
  exact ⟨Prop59Pieces.lt_arcζ_iff.2 ⟨mem_univ _, l1'⟩,
    Prop59Pieces.lt_arcζ_iff.2 ⟨mem_univ _, by rw [hS₀]; exact l1⟩⟩

theorem s3XL_eq_s5XL (xL : Fin nL → ℝ) {τs : ℕ → ℝ} {ℓ : ℕ}
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) :
    s3XL xL τs ℓ s Wj E τ p = s5XL xL τs ℓ s q τ (stopX hq hEg hp hg) := by
  classical
  have hτq' : (τ : ℝ) ≤ q := by exact_mod_cast hτq.le
  have hS₀ := s5S₀_stopX hq hEg hp hg hτq hal
  have hγ := isKilledArc_gCurve hEg p
  have hT := StagedS4.s3Start_lt_kLife hEg hal
  have hwc := continuous_clampDrv_kPath hγ hT
  have hal' : stopX hq hEg hp hg ∈ s5Alive s q τ := (mem_s5Alive_stopX_iff hq hEg hp hg hτq).2 hal.2
  have hA := s3_switch hEg hal hτs
  simp only [s3XL, hal, s5XL, hal', ↓reduceIte, hS₀]
  have hcf : cfDrv0 s (stopX hq hEg hp hg).1.2 = cfDrv0 s p.2 := cfDrv0_cfStop s p.2
  rw [hcf, imgStageVL_congr_A (A := fun m => capClock (s5γ s q (stopX hq hEg hp hg)) (τs m))
    (A' := fun m => capClock (gCurve s (fun _ => ⊤) Wj E p) (τs m)) xL _ _
    (fun j => capClock_stopX hq hEg hp hg ((hτs j).2.trans hτq'))]
  have hEq1 : EqOn (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p))
      (Ito.clampDrv (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) (s3Start s Wj E τ p))
      (Icc 0 (s3Start s Wj E τ p : ℝ)) := fun r hr => (Ito.clampDrv_eqOn hr).symm
  have hEq2 : EqOn (kPath (s5γ s q (stopX hq hEg hp hg)) (s5P s q (stopX hq hEg hp hg)))
      (Ito.clampDrv (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) (s3Start s Wj E τ p))
      (Icc 0 (s3Start s Wj E τ p : ℝ)) := fun r hr => by
    rw [kPath_eqOn_s5 hq hEg hp hg hqP (lt_of_le_of_lt (NNReal.coe_le_coe.2 le_self_add) hwin) hr]
    exact hEq1 hr
  rw [imgStageVL_congr hwc hEq1 xL _ _ (fun j => hA j) (NNReal.coe_nonneg _),
    imgStageVL_congr hwc hEq2 xL _ _ (fun j => hA j) (NNReal.coe_nonneg _)]

theorem s3XR_eq_s5XR (xR : Fin nR → ℝ) {τs : ℕ → ℝ} {ℓ : ℕ}
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) :
    s3XR xR τs ℓ s Wj E τ p = s5XR xR τs ℓ s q τ (stopX hq hEg hp hg) := by
  classical
  have hτq' : (τ : ℝ) ≤ q := by exact_mod_cast hτq.le
  have hS₀ := s5S₀_stopX hq hEg hp hg hτq hal
  have hγ := isKilledArc_gCurve hEg p
  have hT := StagedS4.s3Start_lt_kLife hEg hal
  have hwc := continuous_clampDrv_kPath hγ hT
  have hal' : stopX hq hEg hp hg ∈ s5Alive s q τ := (mem_s5Alive_stopX_iff hq hEg hp hg hτq).2 hal.2
  have hA := s3_switch hEg hal hτs
  simp only [s3XR, hal, s5XR, hal', ↓reduceIte, hS₀]
  have hcf : cfDrv0 s (stopX hq hEg hp hg).1.2 = cfDrv0 s p.2 := cfDrv0_cfStop s p.2
  rw [hcf, imgStageVR_congr_A (A := fun m => capClock (s5γ s q (stopX hq hEg hp hg)) (τs m))
    (A' := fun m => capClock (gCurve s (fun _ => ⊤) Wj E p) (τs m)) xR _ _
    (fun j => capClock_stopX hq hEg hp hg ((hτs j).2.trans hτq'))]
  have hEq1 : EqOn (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p))
      (Ito.clampDrv (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) (s3Start s Wj E τ p))
      (Icc 0 (s3Start s Wj E τ p : ℝ)) := fun r hr => (Ito.clampDrv_eqOn hr).symm
  have hEq2 : EqOn (kPath (s5γ s q (stopX hq hEg hp hg)) (s5P s q (stopX hq hEg hp hg)))
      (Ito.clampDrv (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) (s3Start s Wj E τ p))
      (Icc 0 (s3Start s Wj E τ p : ℝ)) := fun r hr => by
    rw [kPath_eqOn_s5 hq hEg hp hg hqP (lt_of_le_of_lt (NNReal.coe_le_coe.2 le_self_add) hwin) hr]
    exact hEq1 hr
  rw [imgStageVR_congr hwc hEq1 xR _ _ (fun j => hA j) (NNReal.coe_nonneg _),
    imgStageVR_congr hwc hEq2 xR _ _ (fun j => hA j) (NNReal.coe_nonneg _)]

theorem s3VL_eq_s5VL (xL : Fin nL → ℝ) {τs : ℕ → ℝ} {ℓ : ℕ}
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (i : Fin (ℓ + (nL + 1))) {u : ℝ≥0} (hut : u ≤ t) :
    s3VL xL τs ℓ s Wj E τ i u p = s5VL xL τs ℓ s q τ i u (stopX hq hEg hp hg) := by
  have hS₀ := s5S₀_stopX hq hEg hp hg hτq hal
  have hγ := isKilledArc_gCurve hEg p
  have hv1 : ((s3Start s Wj E τ p + t : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) Wj E p) q := hwin
  obtain ⟨-, -, lt1⟩ := kW_eq_s5 hq hEg hp hg hqP hv1
  set w := Ito.clampDrv (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p))
    ((s3Start s Wj E τ p + t : ℝ≥0) : ℝ) with hw
  have hwc : Continuous w := continuous_clampDrv_kPath hγ lt1
  have hsub : Icc (0 : ℝ) ((s3Start s Wj E τ p + u : ℝ≥0) : ℝ) ⊆ Icc 0 ((s3Start s Wj E τ p + t : ℝ≥0) : ℝ) :=
    Icc_subset_Icc le_rfl (NNReal.coe_le_coe.2 (add_le_add_right hut _))
  have hE1 : EqOn (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) w
      (Icc 0 ((s3Start s Wj E τ p + u : ℝ≥0) : ℝ)) := fun r hr => (Ito.clampDrv_eqOn (hsub hr)).symm
  have hE2 : EqOn (kPath (s5γ s q (stopX hq hEg hp hg)) (s5P s q (stopX hq hEg hp hg))) w
      (Icc 0 ((s5S₀ s q τ (stopX hq hEg hp hg) + u : ℝ≥0) : ℝ)) := fun r hr => by
    rw [hS₀] at hr
    rw [kPath_eqOn_s5 hq hEg hp hg hqP hwin (hsub hr)]
    exact hE1 hr
  obtain ⟨hz1, hz2⟩ := lt_s3ζ_and_lt_s5ζ hq hEg hp hg hτq hal hqP hwin hut
  have hr1 := (Prop59Pieces.lt_arcζ_iff.1 hz1).2
  have hr2 := (Prop59Pieces.lt_arcζ_iff.1 hz2).2
  have h1 := arcVL_sub_arcW (γ := gCurve s (fun _ => ⊤) Wj E) (P := gPre s (fun _ => ⊤) Wj E)
    (S₀ := s3Start s Wj E τ) (Al := univ) (xL := s3XL xL τs ℓ s Wj E τ) (ω := p) (mem_univ _) hr1 hwc hE1 i
  have h2 := arcVL_sub_arcW (γ := s5γ s q) (P := s5P s q) (S₀ := s5S₀ s q τ) (Al := univ)
    (xL := s5XL xL τs ℓ s q τ) (ω := stopX hq hEg hp hg) (mem_univ _) hr2 hwc hE2 i
  rw [hS₀, ← s3XL_eq_s5XL hq hEg hp hg hτq hal hqP hwin xL hτs] at h2
  have hW := s3W_eq_s5W hq hEg hp hg hτq hal hqP hwin hut
  change arcVL _ _ _ _ _ i u p = arcVL _ _ _ _ _ i u _
  have e1 : arcVL (gCurve s (fun _ => ⊤) Wj E) (gPre s (fun _ => ⊤) Wj E) (s3Start s Wj E τ) univ
      (s3XL xL τs ℓ s Wj E τ) i u p = _ := eq_add_of_sub_eq h1
  have e2 : arcVL (s5γ s q) (s5P s q) (s5S₀ s q τ) univ (s5XL xL τs ℓ s q τ) i u (stopX hq hEg hp hg) = _ :=
    eq_add_of_sub_eq h2
  have hW' : arcW (gCurve s (fun _ => ⊤) Wj E) (gPre s (fun _ => ⊤) Wj E) (s3Start s Wj E τ) univ u p =
      arcW (s5γ s q) (s5P s q) (s5S₀ s q τ) univ u (stopX hq hEg hp hg) := hW
  rw [e1, e2, hW']

theorem s3VR_eq_s5VR (xR : Fin nR → ℝ) {τs : ℕ → ℝ} {ℓ : ℕ}
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (i : Fin (ℓ + (nR + 1))) {u : ℝ≥0} (hut : u ≤ t) :
    s3VR xR τs ℓ s Wj E τ i u p = s5VR xR τs ℓ s q τ i u (stopX hq hEg hp hg) := by
  have hS₀ := s5S₀_stopX hq hEg hp hg hτq hal
  have hγ := isKilledArc_gCurve hEg p
  have hv1 : ((s3Start s Wj E τ p + t : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) Wj E p) q := hwin
  obtain ⟨-, -, lt1⟩ := kW_eq_s5 hq hEg hp hg hqP hv1
  set w := Ito.clampDrv (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p))
    ((s3Start s Wj E τ p + t : ℝ≥0) : ℝ) with hw
  have hwc : Continuous w := continuous_clampDrv_kPath hγ lt1
  have hsub : Icc (0 : ℝ) ((s3Start s Wj E τ p + u : ℝ≥0) : ℝ) ⊆ Icc 0 ((s3Start s Wj E τ p + t : ℝ≥0) : ℝ) :=
    Icc_subset_Icc le_rfl (NNReal.coe_le_coe.2 (add_le_add_right hut _))
  have hE1 : EqOn (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) w
      (Icc 0 ((s3Start s Wj E τ p + u : ℝ≥0) : ℝ)) := fun r hr => (Ito.clampDrv_eqOn (hsub hr)).symm
  have hE2 : EqOn (kPath (s5γ s q (stopX hq hEg hp hg)) (s5P s q (stopX hq hEg hp hg))) w
      (Icc 0 ((s5S₀ s q τ (stopX hq hEg hp hg) + u : ℝ≥0) : ℝ)) := fun r hr => by
    rw [hS₀] at hr
    rw [kPath_eqOn_s5 hq hEg hp hg hqP hwin (hsub hr)]
    exact hE1 hr
  obtain ⟨hz1, hz2⟩ := lt_s3ζ_and_lt_s5ζ hq hEg hp hg hτq hal hqP hwin hut
  have hr1 := (Prop59Pieces.lt_arcζ_iff.1 hz1).2
  have hr2 := (Prop59Pieces.lt_arcζ_iff.1 hz2).2
  have h1 := arcVR_sub_arcW (γ := gCurve s (fun _ => ⊤) Wj E) (P := gPre s (fun _ => ⊤) Wj E)
    (S₀ := s3Start s Wj E τ) (Al := univ) (xR := s3XR xR τs ℓ s Wj E τ) (ω := p) (mem_univ _) hr1 hwc hE1 i
  have h2 := arcVR_sub_arcW (γ := s5γ s q) (P := s5P s q) (S₀ := s5S₀ s q τ) (Al := univ)
    (xR := s5XR xR τs ℓ s q τ) (ω := stopX hq hEg hp hg) (mem_univ _) hr2 hwc hE2 i
  rw [hS₀, ← s3XR_eq_s5XR hq hEg hp hg hτq hal hqP hwin xR hτs] at h2
  have hW := s3W_eq_s5W hq hEg hp hg hτq hal hqP hwin hut
  change arcVR _ _ _ _ _ i u p = arcVR _ _ _ _ _ i u _
  have e1 : arcVR (gCurve s (fun _ => ⊤) Wj E) (gPre s (fun _ => ⊤) Wj E) (s3Start s Wj E τ) univ
      (s3XR xR τs ℓ s Wj E τ) i u p = _ := eq_add_of_sub_eq h1
  have e2 : arcVR (s5γ s q) (s5P s q) (s5S₀ s q τ) univ (s5XR xR τs ℓ s q τ) i u (stopX hq hEg hp hg) = _ :=
    eq_add_of_sub_eq h2
  have hW' : arcW (gCurve s (fun _ => ⊤) Wj E) (gPre s (fun _ => ⊤) Wj E) (s3Start s Wj E τ) univ u p =
      arcW (s5γ s q) (s5P s q) (s5S₀ s q τ) univ u (stopX hq hEg hp hg) := hW
  rw [e1, e2, hW']

/-- **The restarted chart is read from the stopped data.** -/
theorem s3Chart_eq_s5Chart : s3Chart s Wj E τ p = s5Chart s q τ (stopX hq hEg hp hg) := by
  have hS₀ := s5S₀_stopX hq hEg hp hg hτq hal
  have hS : ((s3Start s Wj E τ p : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) Wj E p) q :=
    lt_of_le_of_lt (NNReal.coe_le_coe.2 le_self_add) hwin
  have hcf : cfChart s (stopX hq hEg hp hg).1.2 = cfChart s p.2 := by
    simp only [cfChart]
    rw [show (stopX hq hEg hp hg).1.2 = GlueCond.cfStop s p.2 from rfl, cfDrv0_cfStop]
  have hcl : Ito.clampDrv (kPath (s5γ s q (stopX hq hEg hp hg)) (s5P s q (stopX hq hEg hp hg)))
      (s3Start s Wj E τ p) =
      Ito.clampDrv (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) (s3Start s Wj E τ p) := by
    funext r
    simp only [Ito.clampDrv]
    exact kPath_eqOn_s5 hq hEg hp hg hqP hS ⟨le_min (le_max_right _ _) (NNReal.coe_nonneg _), min_le_right _ _⟩
  simp only [s3Chart, s5Chart, rChart, hS₀, hcf, hcl]

end Rep

end InteractingSLE.Sec5.CrossCond.StagedS5
