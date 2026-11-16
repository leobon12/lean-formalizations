/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermLineSets

/-!
# The hull identity at a line

Packet PROVE-RC-TERM, second run (ruling R124). At a line `(t, N)` before the stop, the physical chart of the
completed second path maps the complement of the line set onto the complement of the relative hull at the clock:

* `IsPathSample.image_inv_diff` (builder frame, from the hull identity and the chain of
  `Term.exists_relChain_config`): `inv '' (ℍ ∖ fill Γ([0, t])) = ℍ ∖ (fill(completed path) ∪ fill β([0, t]))`;
* `rT`, `rT_image_H_diff`, `rT_image_fillH`: the reflection–translation `z ↦ reflectC z + x`;
* `IsKSample.image_kInv_diff`: the same identity in the original orientation, for `v ↦ kInv v + x₁`;
* `IsKSample.fwdMapInv_eq_kInv`: on `ℍ` the Loewner inverse at `v + τ` is `kInv v + d`;
* `fwdHull_aClock`: at a good sample a generating driver has the filled chart path as hull at the clock;
* **`ae_lineSet_eq`**: almost surely on a good event, before the capacity lifetime,
  `ℍ ∖ lineSet = physChart⁻¹ '' (ℍ ∖ K̃_{clock})` (the input `hBK` of K2's (L) and the domain identity of (S)).

R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.RealContact

namespace Term

open LP (reflectC)
open Restart Restart.RetAux79 Supp7 Exist.Staged Exist.StagedLaw Sec2.Assembly Sec7.Lemma76F RLC.AStopProc
open Theorem14.SB.FinRel (IsSB2RelChain)

/-! ### The builder frame -/

section Builder

variable {V : ℝ → ℝ} {T : ℝ≥0} {ξ : ℝ → ℂ} {p d : ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {β : ℝ≥0 → ℂ}

/-- **The hull identity in the builder frame**: before the physical stop the inverse entry chart maps the complement
of the filled chart path onto the complement of the two filled paths. -/
theorem IsPathSample.image_inv_diff (h : IsPathSample V T ξ p d w ζ β) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < physStop ξ T d β ζ) :
    (entryChart V (T : ℝ) d).2.1 '' (H \ fillH (chartPath V ξ T d β ζ '' Icc 0 t)) =
      H \ (fillH (entryPath ξ (T : ℝ) d '' Icc 0 1) ∪ fillH (β '' Icc 0 t)) := by
  obtain ⟨a, hta, haL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have hta' : t < a := ENNReal.coe_lt_coe.1 hta
  have haζ : (a : ℝ≥0∞) < ζ := lt_life_of_lt haL
  have hP := h.isExpPrefix haL
  obtain ⟨β', γ, Wr, ηr, -, hγ, hγ0, hγeq, hch, hhull, -⟩ := exists_relChain_config (V := V) (ξ := ξ) (p := p)
    (d := d) (nL := 0) (nR := 0) (nL' := 0) (nR' := 0) (ρL := fun i => i.elim0) (ρR := fun i => i.elim0)
    (xL := fun i => i.elim0) (xR := fun i => i.elim0) (ρL' := fun i => i.elim0) (ρR' := fun i => i.elim0)
    (xL' := fun i => i.elim0) (xR' := fun i => i.elim0) 1 0 (fun i => i.elim0) (fun i => i.elim0)
    (fun i => i.elim0) (fun i => i.elim0) h.entry h.tipPos h.ne h.gen h.drvCont h.drvZero haζ
    (h.inj.mono fun s hs => show (s : ℝ≥0∞) ≤ ζ from (ENNReal.coe_le_coe.2 hs.2).trans haζ.le)
    hP.hbar hP.off (h.order a haζ) (S₀ := (t : ℝ)) t.coe_nonneg (NNReal.coe_lt_coe.2 hta')
  have heq : ∀ s ≤ a, chartPath V ξ T d β ζ s = γ s := by
    intro s hs
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs0 | hs0
    · rw [← hs0, h.chartPath_zero, hγ0]
    · rw [hγeq s hs0 hs, h.chartPath_eq_fwd hs0 (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) haL)]
  have hst : (t : ℝ) ∈ Icc (0 : ℝ) t := ⟨t.coe_nonneg, le_rfl⟩
  have h1 := hhull (t : ℝ) hst
  have h2 := (hch.2.2.2.2.2.2 (t : ℝ) hst).2.2.1
  rw [h2, Real.toNNReal_coe] at h1
  have himg : chartPath V ξ T d β ζ '' Icc 0 t = γ '' Icc 0 t :=
    image_congr fun s hs => heq s (hs.2.trans hta'.le)
  rw [himg]
  exact h1

end Builder

/-! ### The reflection–translation -/

/-- The reflection–translation `z ↦ reflectC z + x`. -/
def rT (x : ℝ) (z : ℂ) : ℂ := reflectC z + (x : ℂ)

theorem rT_image_H_diff (x : ℝ) (S : Set ℂ) : rT x '' (H \ S) = H \ rT x '' S := by
  have e : rT x = (fun z : ℂ => z + (x : ℂ)) ∘ reflectC := rfl
  rw [e, image_comp, image_comp, ← LP.H_diff_reflectC_image, image_add_real_H_diff]

theorem rT_image_fillH (x : ℝ) (S : Set ℂ) : rT x '' fillH S = fillH (rT x '' S) := by
  have e : rT x = (fun z : ℂ => z + (x : ℂ)) ∘ reflectC := rfl
  rw [e, image_comp, image_comp, ← LP.fillH_image_reflectC, ← fillH_image_add_real]

/-! ### The original orientation -/

section K

variable {U : ℝ → ℝ} {T : ℝ≥0} {ρ₂ : ℝ → ℂ} {q d : ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {ρ₁ : ℝ≥0 → ℂ}

/-- **The hull identity in the original orientation.** -/
theorem IsKSample.image_kInv_diff (h : IsKSample U T ρ₂ q d w ζ ρ₁) (x₁ : ℝ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < kStop ρ₂ T d ρ₁ ζ) :
    (fun v => kInv U (T : ℝ) d v + (x₁ : ℂ)) '' (H \ fillH (kPath U ρ₂ T d ρ₁ ζ '' Icc 0 t)) =
      H \ (fillH ((fun s : ℝ≥0 => ρ₂ (s : ℝ) + ((x₁ - d : ℝ) : ℂ)) '' Icc 0 T) ∪
        fillH ((fun s : ℝ≥0 => ρ₁ s + (x₁ : ℂ)) '' Icc 0 t)) := by
  have hP : IsPathSample (-U) T (fun s => reflectC (ρ₂ s)) (-q) d (-w) ζ (fun s => reflectC (ρ₁ s)) := h
  have h1 := hP.image_inv_diff ht
  have hV := hP.entry.tip.cont
  have hV0 := hP.entry.tip.zero
  have hT : (0 : ℝ) ≤ T := T.coe_nonneg
  set Γ := chartPath (-U) (fun s => reflectC (ρ₂ s)) T d (fun s => reflectC (ρ₁ s)) ζ with hΓ
  -- the left side through the entry chart
  have hk : kPath U ρ₂ T d ρ₁ ζ '' Icc 0 t = reflectC '' (Γ '' Icc 0 t) := by
    rw [image_image]
    rfl
  have hL : (fun v => kInv U (T : ℝ) d v + (x₁ : ℂ)) '' (H \ fillH (kPath U ρ₂ T d ρ₁ ζ '' Icc 0 t)) =
      rT x₁ '' ((entryChart (-U) (T : ℝ) d).2.1 '' (H \ fillH (Γ '' Icc 0 t))) := by
    rw [hk, LP.H_diff_fillH_image_reflectC, image_image, image_image]
    refine image_congr fun y hy => ?_
    show reflectC (entryInv (-U) (T : ℝ) d (reflectC (reflectC y))) + (x₁ : ℂ) = _
    rw [LP.reflectC_reflectC, entryInv_eqOn hV hV0 hT d hy.1]
    rfl
  rw [hL, h1, rT_image_H_diff, image_union, rT_image_fillH, rT_image_fillH]
  -- the two images
  have e1 : rT x₁ '' (entryPath (fun s => reflectC (ρ₂ s)) (T : ℝ) d '' Icc 0 1) =
      (fun s : ℝ≥0 => ρ₂ (s : ℝ) + ((x₁ - d : ℝ) : ℂ)) '' Icc 0 T := by
    rw [image_entryPath_eq hP.tpos, image_image]
    refine image_congr fun s _ => ?_
    show reflectC (reflectC (ρ₂ (s : ℝ)) + (d : ℂ)) + (x₁ : ℂ) = _
    rw [reflectC_add_ofReal, LP.reflectC_reflectC]
    push_cast
    ring
  have e2 : rT x₁ '' ((fun s : ℝ≥0 => reflectC (ρ₁ s)) '' Icc 0 t) =
      (fun s : ℝ≥0 => ρ₁ s + (x₁ : ℂ)) '' Icc 0 t := by
    rw [image_image]
    refine image_congr fun s _ => ?_
    show reflectC (reflectC (ρ₁ s)) + (x₁ : ℂ) = _
    rw [LP.reflectC_reflectC]
  rw [e1, e2]

/-- On `ℍ` the Loewner inverse of the second path at `v + τ` is `kInv v + d`. -/
theorem IsKSample.fwdMapInv_eq_kInv (h : IsKSample U T ρ₂ q d w ζ ρ₁) {v : ℂ} (hv : v ∈ H) :
    fwdMapInv U (T : ℝ) (v + (markPos U (T : ℝ) d : ℂ)) = kInv U (T : ℝ) d v + (d : ℂ) := by
  have hP : IsPathSample (-U) T (fun s => reflectC (ρ₂ s)) (-q) d (-w) ζ (fun s => reflectC (ρ₁ s)) := h
  have hU : Continuous U := by
    have := hP.entry.tip.cont.neg
    simpa using this
  have hU0 : U 0 = 0 := by
    have := hP.entry.tip.zero
    simpa using this
  have hvH : v + (markPos U (T : ℝ) d : ℂ) ∈ H := by
    show 0 < (v + (markPos U (T : ℝ) d : ℂ)).im
    have : 0 < v.im := hv
    simpa using this
  rw [← h.extendFrom_eq (le_of_lt hv), extendFrom_fwdMapInv_of_mem hU hU0 T.coe_nonneg hvH]

end K

/-! ### The hull at the clock -/

/-- **At a good sample a generating driver has the filled chart path as hull at the clock.** -/
theorem fwdHull_aClock {Ω : Type*} {Γ : Ω → ℝ≥0 → ℂ} {L : Ω → ℝ≥0∞} {ω : Ω} (hg : IsAGood Γ L ω)
    {W : ℝ≥0 → ℝ} (hgen : IsGeneratingTrace W (aLife Γ L ω) (aPath Γ L ω)) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < L ω) :
    fwdHull (fun s : ℝ => W s.toNNReal) (aClock Γ t ω) = fillH (Γ ω '' Icc 0 t) := by
  have hq : (aClock Γ t ω : ℝ≥0∞) < aLife Γ L ω := hg.aClock_lt_aLife_iff.2 ht
  have hfill := hgen.2.2 _ hq
  have himg : aPath Γ L ω '' Icc 0 (aClock Γ t ω) = Γ ω '' Icc 0 t := by
    apply Subset.antisymm
    · rintro _ ⟨u, hu, rfl⟩
      have hu' : (u : ℝ≥0∞) ≤ capLife (chartClock (Γ ω)) (L ω) :=
        ((ENNReal.coe_le_coe.2 hu.2).trans hq.le)
      obtain ⟨hrL, hru⟩ := hg.clock.invClock_spec hu'
      refine ⟨invClock (chartClock (Γ ω)) (L ω) u, ⟨zero_le, ?_⟩, rfl⟩
      by_contra hlt
      have hlt' : t < invClock (chartClock (Γ ω)) (L ω) u := not_le.1 hlt
      have h1 := hg.clock.strictMonoOn (show (t : ℝ≥0∞) ≤ L ω from ht.le) hrL hlt'
      rw [hru, ← hg.coe_aClock t] at h1
      exact absurd (NNReal.coe_le_coe.2 hu.2) (not_le.2 h1)
    · rintro _ ⟨r, hr, rfl⟩
      have hrL : (r : ℝ≥0∞) ≤ L ω := (ENNReal.coe_le_coe.2 hr.2).trans ht.le
      refine ⟨aClock Γ r ω, ⟨zero_le, ?_⟩, ?_⟩
      · rw [hg.aClock_eq, hg.aClock_eq]
        exact Real.toNNReal_le_toNNReal (hg.mono hr.2)
      · show Γ ω (invClock (chartClock (Γ ω)) (L ω) (aClock Γ r ω)) = Γ ω r
        rw [hg.aClock_eq, hg.clock.invClock_apply hrL]
  rw [himg] at hfill
  have hcpt : IsCompact (Γ ω '' Icc 0 t) := isCompact_Icc.image hg.cont
  exact (fillH_eq_iff_isFilling_of_isClosed hcpt.isBounded hcpt.isClosed fun _ hz => hz.1).1 hfill

/-! ### The line set -/

section Line

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {u₀ : ℂ → ℝ} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {x₁ x₂ : ℝ}

/-- **The hull identity at a line**: almost surely on a good event, before the capacity lifetime, the complement of
the line set is the physical chart's inverse image of the complement of the relative hull at the clock. -/
theorem ae_lineSet_eq {N : ℝ≥0} {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE2 : ∀ ω, (E ω).2 = ζ₂ ω)
    {η₁' : Ω → ℝ≥0 → ℂ} (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    {ηb₂ : Ω → ℝ≥0 → ℂ} (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηb₂ ω s = η₂ ω (capTime (capR 0 N) (ζ₂ ω) s))
    {M : Set Ω} (hMg : ∀ ω ∈ M, IsTermGood N E ηb₂ η₁' ζ₁ x₁ x₂ ω)
    {W : ℝ≥0 → Ω → ℝ}
    (hgen : ∀ ω ∈ M, IsGeneratingTrace (W · ω)
      (aLife (pPath N E ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E ηb₂ η₁' ζ₁ x₁ x₂) ω)
      (aPath (pPath N E ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E ηb₂ η₁' ζ₁ x₁ x₂) ω))
    {t : ℝ≥0} {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (d : IsLineData P h u₀ η₁ η₂ ζ₁ ζ₂ x₁ x₂ t N ηc₁ ηc₂) :
    ∀ᵐ ω ∂P, ω ∈ M → (aClock (pPath N E ηb₂ η₁' ζ₁ x₁ x₂) t ω : ℝ≥0∞) <
        aLife (pPath N E ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E ηb₂ η₁' ζ₁ x₁ x₂) ω →
      H \ lineSet ηc₁ ηc₂ t N ω = (physChart x₂ (pRec N E ω) (pSeed N E x₁ x₂ ω)).2.1 ''
        (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (aClock (pPath N E ηb₂ η₁' ζ₁ x₁ x₂) t ω)) := by
  filter_upwards [ha₁, hag₂, d.ae₁, d.ae₂] with ω e₁ eb₂ ec₁ ec₂ hω hlt
  have hG := hMg ω hω
  obtain ⟨q, w, -, hK⟩ := hG.sample
  have hgood := hG.isAGood
  have htL : (t : ℝ≥0∞) < pStop N E ηb₂ η₁' ζ₁ x₁ x₂ ω := hgood.aClock_lt_aLife_iff.1 hlt
  have htζ : (t : ℝ≥0∞) < ζ₁ ω := lt_of_lt_of_le htL (physStop_le _ _ _ _ _)
  have hle : ζ₂ ω ≤ N := by rw [← hE2]; exact hG.life
  -- the hull at the clock
  rw [fwdHull_aClock hgood (hgen ω hω) htL]
  -- the chart inverse on `ℍ`
  have hinv : ∀ v ∈ H, (physChart x₂ (pRec N E ω) (pSeed N E x₁ x₂ ω)).2.1 v =
      kInv (pU N E ω) (pT N E ω : ℝ) (x₁ - x₂) v + (x₁ : ℂ) := by
    intro v hv
    rw [physChart_inv]
    show fwdMapInv (pU N E ω) (pT N E ω : ℝ) (v + (markPos (pU N E ω) (pT N E ω : ℝ) (x₁ - x₂) : ℂ)) +
      (x₂ : ℂ) = _
    rw [hK.fwdMapInv_eq_kInv hv]
    push_cast
    ring
  have himg : (physChart x₂ (pRec N E ω) (pSeed N E x₁ x₂ ω)).2.1 ''
      (H \ fillH (pPath N E ηb₂ η₁' ζ₁ x₁ x₂ ω '' Icc 0 t)) =
      (fun v => kInv (pU N E ω) (pT N E ω : ℝ) (x₁ - x₂) v + (x₁ : ℂ)) ''
        (H \ fillH (pPath N E ηb₂ η₁' ζ₁ x₁ x₂ ω '' Icc 0 t)) :=
    image_congr fun v hv => hinv v hv.1
  rw [himg]
  have hid := hK.image_kInv_diff x₁ htL
  rw [show pPath N E ηb₂ η₁' ζ₁ x₁ x₂ ω =
    kPath (pU N E ω) (pRho₂ ηb₂ x₂ ω) (pT N E ω) (x₁ - x₂) (pRho₁ η₁' x₁ ω) (ζ₁ ω) from rfl, hid]
  -- the two paths
  have hcap₂ : ∀ m : ℝ≥0, N ≤ m → ∀ s : ℝ≥0, capTime m (ζ₂ ω) s = min s (ζ₂ ω).toNNReal := by
    intro m hm s
    unfold capTime
    rw [min_eq_left (hle.trans (ENNReal.coe_le_coe.2 hm))]
  have hret : (fun s : ℝ≥0 => pRho₂ ηb₂ x₂ ω (s : ℝ) + ((x₁ - (x₁ - x₂) : ℝ) : ℂ)) '' Icc 0 (pT N E ω) =
      ηc₂ ω '' Icc 0 N := by
    have h1 : (fun s : ℝ≥0 => pRho₂ ηb₂ x₂ ω (s : ℝ) + ((x₁ - (x₁ - x₂) : ℝ) : ℂ)) '' Icc 0 (pT N E ω) =
        ηb₂ ω '' Icc 0 (pT N E ω) := by
      refine image_congr fun s _ => ?_
      show ηb₂ ω (s : ℝ).toNNReal - (x₂ : ℂ) + ((x₁ - (x₁ - x₂) : ℝ) : ℂ) = ηb₂ ω s
      rw [Real.toNNReal_coe]
      push_cast
      ring
    rw [h1, ← hG.image_Icc_N]
    refine image_congr fun s _ => ?_
    rw [eb₂ s, ec₂ s, hcap₂ _ (lt_capR_right 0 N).le, hcap₂ _ (lt_capR_right t N).le]
  have hexp : (fun s : ℝ≥0 => pRho₁ η₁' x₁ ω s + (x₁ : ℂ)) '' Icc 0 t = ηc₁ ω '' Icc 0 t := by
    refine image_congr fun s hs => ?_
    show η₁' ω s - (x₁ : ℂ) + (x₁ : ℂ) = ηc₁ ω s
    rw [sub_add_cancel, ec₁ s, capTime_eq_of_lt htζ (lt_capR_left t N) hs.2,
      e₁ s ((ENNReal.coe_le_coe.2 hs.2).trans htζ.le)]
  rw [hret, hexp]
  rfl

end Line

end Term

end InteractingSLE.RealContact
