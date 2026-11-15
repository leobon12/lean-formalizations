/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdgRead
import InteractingSLE.Spec.Sec7.SideHeightGeom
import InteractingSLE.Spec.Supplement.GB6LifeBase

/-!
# GW2's near buffer facts in terms of the comparison driver alone

Packet PROVE-GW2-SDE (round 4). `NearBufferFact` is about the state `(W, V^L, V^R)` of the chosen comparison dynamics.
In `comparisonFamilyO F` only `W` and the stop are prescribed; the force points `V^L, V^R` are chosen. Under the
stopped SDE (`LocalDynamics.IsStopped`, which the SDE half supplies for the same comparisons), the force points are
the Loewner images of the marks under the driver. This holds before the stop, and at a finite positive stop by the
endpoint continuity clause. So the near buffer facts can be stated with the image state of the driver; no chosen
object remains.

* `vR_eq_rightImg_upTo`, `vL_eq_neg_rightImg_upTo`: the force points of a stopped path are the
  images of the marks under the driver frozen at the current time (port of
  `Sec7.SideHeight.vR_eq_rightImg_frozenDrive` to stopped paths);
* `imgState xL xR w t`: the image state `(w t, −R^{−xL}_t[−w̃], R^{xR}_t[w̃])` with `w̃` the driver frozen at `t`;
* **`state_eq_imgState`** (before the stop) and **`state_eq_imgState_of_continuousOn`** (at a finite positive stop,
  from continuity of the state on `[0, stop]`); **`ae_state_eq_of_isStopped`**;
* `NearImgPath`: the kernel clauses of `NearBufferFact` with the image state of the driver;
  **`nearBufferFact_of_imgPath`**, **`retainedBuffer_near_of_imgPath`** (any `D`, `C` with the SDE half);
* ROOT2's frame: **`RootNearImg`** (the near facts for the actual stage driver `(−1)^{|l|} 2^{r.2} R(·/4^{r.2})`, its
  stop `4^{r.2} τ` and the actual sample), **`retainedBuffer_near_rootFrame`**, and
  **`retainedBufferStatement_rootFrame_of_img`** (the whole buffer statement for ROOT2's construction and the
  comparison family of the SDE half, from the named inputs).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdg

open GW2JDetR11 GW2Sde GW2Sdf GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6 GW2TipSystem.RootN4 Restart
  MartChar.RealFlow

/-! ### Force points of a stopped path are images of the marks -/

section Images

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}

/-- **Right force points of a stopped path** are the images of the marks for the driver frozen at `t`. -/
theorem vR_eq_rightImg_upTo (hp : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < τ) (i : Fin nR) : vR i t = rightImg (frozenDrive w t) (xR i) t := by
  have ht₂ : ENNReal.ofReal (t : ℝ) < τ := by rwa [ENNReal.ofReal_coe_nnreal]
  have htt₂ : (t : ℝ) ≤ (t : ℝ) := le_rfl
  have hrw : Continuous (frozenDrive w t) := continuous_frozenDrive_of_lt hp.continuousOn_w ht₂
  have hζ0 : ((0 : ℝ≥0) : ℝ≥0∞) < τ := lt_of_le_of_lt (by simp) ht
  have hx : 0 ≤ xR i := by
    have := hp.w_le_vR hζ0 i
    rwa [hp.w_zero, hp.vR_zero] at this
  have hlt := fun s (hs : s ∈ Icc (0 : ℝ) t) => Sec7.SideHeight.toNNReal_lt_of_le ht₂ htt₂ hs
  have hfr : ∀ s ∈ Icc (0 : ℝ) t, frozenDrive w t s = w s.toNNReal := fun s hs =>
    frozenDrive_eq ⟨hs.1, hs.2.trans htt₂⟩
  have hint : IntervalIntegrable (fun s : ℝ => 2 / (vR i s.toNNReal - frozenDrive w t s)) volume 0 t := by
    have h0 : IntervalIntegrable (fun s : ℝ => (-2) * (w s.toNNReal - vR i s.toNNReal)⁻¹) volume 0 t :=
      (hp.integrable_gapR ht i).const_mul (-2)
    refine h0.congr ?_
    intro s hs
    rw [uIoc_of_le t.coe_nonneg] at hs
    show _ = 2 / (vR i s.toNNReal - frozenDrive w t s)
    rw [hfr s ⟨hs.1.le, hs.2⟩, div_eq_mul_inv, ← neg_sub, inv_neg]
    ring
  have hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ frozenDrive w t s = vR i s.toNNReal} = 0 :=
    measure_mono_null (fun s (hs : s ∈ Icc (0 : ℝ) t ∧ frozenDrive w t s = vR i s.toNNReal) =>
      (⟨hs.1.1, hlt s hs.1, (hfr s hs.1).symm.trans hs.2⟩ :
        0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < τ ∧ w s.toNNReal = vR i s.toNNReal))
      (hp.volume_collisionR i)
  have key := WangWu.eq_rightImg_of_forceEq (v := fun s : ℝ => vR i s.toNNReal) (T := t) hrw
    (by rw [frozenDrive_zero t.coe_nonneg, hp.w_zero]) hx
    ((hp.continuousOn_vR i).comp continuous_real_toNNReal.continuousOn fun s hs => hlt s hs)
    (fun s hs => by rw [hfr s hs]; exact hp.w_le_vR (hlt s hs) i) hint
    (fun s hs => by
      have h1 := hp.vR_eq (hlt s hs) i
      rw [Real.coe_toNNReal _ hs.1] at h1
      rw [h1]
      congr 1
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      simp only [hfr r ⟨hr.1, hr.2.trans hs.2⟩])
    hnull ⟨t.coe_nonneg, le_rfl⟩
  simpa using key

/-- **Left force points of a stopped path** are the reflected images of the marks for the driver frozen at `t`. -/
theorem vL_eq_neg_rightImg_upTo (hp : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < τ) (i : Fin nL) : vL i t = -rightImg (fun s => -frozenDrive w t s) (-xL i) t := by
  have ht₂ : ENNReal.ofReal (t : ℝ) < τ := by rwa [ENNReal.ofReal_coe_nnreal]
  have htt₂ : (t : ℝ) ≤ (t : ℝ) := le_rfl
  have hrw : Continuous (fun s => -frozenDrive w t s) := (continuous_frozenDrive_of_lt hp.continuousOn_w ht₂).neg
  have hζ0 : ((0 : ℝ≥0) : ℝ≥0∞) < τ := lt_of_le_of_lt (by simp) ht
  have hx : 0 ≤ -xL i := by
    have := hp.vL_le_w hζ0 i
    rw [hp.w_zero, hp.vL_zero] at this
    linarith
  have hlt := fun s (hs : s ∈ Icc (0 : ℝ) t) => Sec7.SideHeight.toNNReal_lt_of_le ht₂ htt₂ hs
  have hfr : ∀ s ∈ Icc (0 : ℝ) t, frozenDrive w t s = w s.toNNReal := fun s hs =>
    frozenDrive_eq ⟨hs.1, hs.2.trans htt₂⟩
  have hint : IntervalIntegrable (fun s : ℝ => 2 / (-vL i s.toNNReal - -frozenDrive w t s)) volume 0 t := by
    have h0 : IntervalIntegrable (fun s : ℝ => 2 * (w s.toNNReal - vL i s.toNNReal)⁻¹) volume 0 t :=
      (hp.integrable_gapL ht i).const_mul 2
    refine h0.congr ?_
    intro s hs
    rw [uIoc_of_le t.coe_nonneg] at hs
    show _ = 2 / (-vL i s.toNNReal - -frozenDrive w t s)
    rw [hfr s ⟨hs.1.le, hs.2⟩, div_eq_mul_inv]
    ring
  have hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ -frozenDrive w t s = -vL i s.toNNReal} = 0 :=
    measure_mono_null (fun s (hs : s ∈ Icc (0 : ℝ) t ∧ -frozenDrive w t s = -vL i s.toNNReal) =>
      (⟨hs.1.1, hlt s hs.1, (hfr s hs.1).symm.trans (neg_injective hs.2)⟩ :
        0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < τ ∧ w s.toNNReal = vL i s.toNNReal))
      (hp.volume_collisionL i)
  have key := WangWu.eq_rightImg_of_forceEq (v := fun s : ℝ => -vL i s.toNNReal) (T := t) hrw
    (by simp only [frozenDrive_zero t.coe_nonneg, hp.w_zero, neg_zero]) hx
    ((hp.continuousOn_vL i).comp continuous_real_toNNReal.continuousOn fun s hs => hlt s hs).neg
    (fun s hs => by rw [hfr s hs]; exact neg_le_neg (hp.vL_le_w (hlt s hs) i)) hint
    (fun s hs => by
      have h1 := hp.vL_eq (hlt s hs) i
      rw [Real.coe_toNNReal _ hs.1] at h1
      rw [h1, neg_add, ← intervalIntegral.integral_neg]
      congr 1
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      simp only [hfr r ⟨hr.1, hr.2.trans hs.2⟩]
      rw [show -vL i r.toNNReal - -w r.toNNReal = -(vL i r.toNNReal - w r.toNNReal) by ring, div_neg])
    hnull ⟨t.coe_nonneg, le_rfl⟩
  rw [Real.toNNReal_coe] at key
  linarith

/-- **The image state** of a driver path at time `t`: the driver and the images of the marks for the driver frozen
at `t`. -/
def imgState (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (w t, fun i => -rightImg (fun s => -frozenDrive w t s) (-xL i) t, fun j => rightImg (frozenDrive w t) (xR j) t)

/-- **Before the stop, the state of a stopped path is the image state.** -/
theorem state_eq_imgState (hp : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < τ) : (w t, fun i => vL i t, fun j => vR j t) = imgState xL xR w t := by
  simp only [imgState, Prod.mk.injEq, true_and]
  exact ⟨funext fun i => vL_eq_neg_rightImg_upTo hp ht i, funext fun j => vR_eq_rightImg_upTo hp ht j⟩

/-- Images for drivers frozen at `t ≤ v` agree up to time `t`. -/
theorem rightImg_frozenDrive_eq {v : ℝ≥0} (hw : ContinuousOn w (Iic v)) {t : ℝ≥0} (htv : t ≤ v) (x : ℝ) :
    rightImg (frozenDrive w t) x t = rightImg (frozenDrive w v) x t ∧
      rightImg (fun s => -frozenDrive w t s) x t = rightImg (fun s => -frozenDrive w v s) x t := by
  have hc : Continuous (frozenDrive w v) := continuous_frozenDrive (by rwa [Real.toNNReal_coe])
  have he : ∀ r ∈ Icc (0 : ℝ) t, frozenDrive w t r = frozenDrive w v r := fun r hr => by
    rw [frozenDrive_eq hr, frozenDrive_eq ⟨hr.1, hr.2.trans (NNReal.coe_le_coe.2 htv)⟩]
  have hc' : Continuous fun s => -frozenDrive w v s := hc.neg
  exact ⟨Supp8.GB6.rightImg_congr hc t.coe_nonneg he,
    Supp8.GB6.rightImg_congr hc' t.coe_nonneg fun r hr => by rw [he r hr]⟩

/-- **At a finite positive stop, the state of a stopped path is the image state**, as soon as the state is continuous
on `[0, stop]` (the endpoint clause of `LocalDynamics.IsStopped`). -/
theorem state_eq_imgState_of_continuousOn (hp : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ)
    {v : ℝ≥0} (hv : (v : ℝ≥0∞) = τ) (hv0 : 0 < v)
    (hc : ContinuousOn (fun t => (w t, fun i => vL i t, fun j => vR j t)) (Iic v)) :
    (w v, fun i => vL i v, fun j => vR j v) = imgState xL xR w v := by
  have hwc : ContinuousOn w (Iic v) := continuous_fst.comp_continuousOn hc
  have hfc : Continuous (frozenDrive w v) := continuous_frozenDrive (by rwa [Real.toNNReal_coe])
  set G : ℝ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) := fun t =>
    (w t, fun i => -rightImg (fun s => -frozenDrive w v s) (-xL i) t, fun j => rightImg (frozenDrive w v) (xR j) t)
    with hG
  have hcoe : ContinuousOn (fun t : ℝ≥0 => (t : ℝ)) (Iic v) := NNReal.continuous_coe.continuousOn
  have hmaps : MapsTo (fun t : ℝ≥0 => (t : ℝ)) (Iic v) (Ici 0) := fun t _ => t.coe_nonneg
  have hGc : ContinuousOn G (Iic v) := by
    refine hwc.prodMk (ContinuousOn.prodMk (continuousOn_pi.2 fun i => ?_) (continuousOn_pi.2 fun j => ?_))
    · exact ((continuousOn_rightImg hfc.neg (-xL i)).comp hcoe hmaps).neg
    · exact (continuousOn_rightImg hfc (xR j)).comp hcoe hmaps
  have heq : EqOn (fun t => (w t, fun i => vL i t, fun j => vR j t)) G (Iio v) := fun t ht => by
    have htv : t ≤ v := le_of_lt ht
    show (w t, fun i => vL i t, fun j => vR j t) = G t
    rw [state_eq_imgState hp (hv ▸ ENNReal.coe_lt_coe.2 ht)]
    simp only [imgState, hG, Prod.mk.injEq, true_and]
    exact ⟨funext fun i => by rw [(rightImg_frozenDrive_eq hwc htv (-xL i)).2],
      funext fun j => (rightImg_frozenDrive_eq hwc htv (xR j)).1⟩
  have hcl : Iic v ⊆ closure (Iio v) := (closure_Iio' (a := v) ⟨0, hv0⟩).ge
  exact (heq.of_subset_closure hc hGc Iio_subset_Iic_self hcl) (mem_Iic.2 le_rfl)

end Images

/-! ### Stopped dynamics -/

/-- **The state of stopped dynamics is the image state of its driver**, before the stop and at a finite positive
stop, almost surely. -/
theorem ae_state_eq_of_isStopped {Ω : Type u} [MeasurableSpace Ω] {nL nR : ℕ}
    {d : LocalDynamics Ω nL nR} {μ : Measure Ω} {κ : ℝ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    (hd : d.IsStopped μ κ xL ρL xR ρR) :
    ∀ᵐ ξ ∂μ, (∀ t : ℝ≥0, (t : ℝ≥0∞) < d.stop ξ →
        Coupling.stateAt d.W d.VL d.VR t ξ = imgState xL xR (fun s => d.W s ξ) t) ∧
      ∀ v : ℝ≥0, (v : ℝ≥0∞) = d.stop ξ → 0 < v →
        Coupling.stateAt d.W d.VL d.VR v ξ = imgState xL xR (fun s => d.W s ξ) v := by
  filter_upwards [hd.1.ae_path, hd.2] with ξ hp hc
  exact ⟨fun t ht => state_eq_imgState hp ht,
    fun v hv hv0 => state_eq_imgState_of_continuousOn hp hv hv0 (hc v hv)⟩

/-! ### The near buffer facts with image states -/

/-- **The kernel clauses of `NearBufferFact` with the image state of the comparison driver** in place of the chosen
state. -/
def NearImgPath {Ω : Type u} [MeasurableSpace Ω] {κ : ℝ} (z : NearData Ω κ) (μ : Measure Ω)
    (sample : ℕ → Ω → RootV7.DriverRecord) (reach : ℕ → Set RootV7.DriverRecord) (n m : ℕ) : Prop :=
  ∀ᵐ ξ ∂μ, 0 < (z.dynamics n m).stop ξ ∧
    (∀ v : ℝ≥0, (v : ℝ≥0∞) = (z.dynamics n m).stop ξ → v < (n : ℝ≥0) →
      imgState z.family.xL z.family.xR (fun s => (z.dynamics n m).W s ξ) v ∉ nearBuffer z.family n) ∧
    ∀ t : ℝ≥0, t < (n : ℝ≥0) → (t : ℝ≥0∞) < (z.dynamics n m).stop ξ →
      imgState z.family.xL z.family.xR (fun s => (z.dynamics n m).W s ξ) t ∈ nearTarget z.family →
      sample (z.candidate n m) ξ ∈ reach (z.candidate n m)

/-- **`NearBufferFact` from the image-state facts** for stopped comparison dynamics. -/
theorem nearBufferFact_of_imgPath {Ω : Type u} [MeasurableSpace Ω] {κ κ' : ℝ} {z : NearData Ω κ} {μ : Measure Ω}
    {sample : ℕ → Ω → RootV7.DriverRecord} {reach : ℕ → Set RootV7.DriverRecord} {n m : ℕ}
    {ρL : Fin z.family.nL → ℝ} {ρR : Fin z.family.nR → ℝ}
    (hst : (z.dynamics n m).IsStopped μ κ' z.family.xL ρL z.family.xR ρR)
    (hreach : MeasurableSet (reach (z.candidate n m))) (h : NearImgPath z μ sample reach n m) :
    NearBufferFact z μ sample reach n m := by
  refine ⟨hreach, ?_⟩
  filter_upwards [h, ae_state_eq_of_isStopped hst] with ξ hξ hs
  obtain ⟨h0, hex, htg⟩ := hξ
  refine ⟨h0, fun v hv hvn => ?_, fun t htn ht htar => ?_⟩
  · have hv0 : 0 < v := by
      have : (0 : ℝ≥0∞) < v := hv ▸ h0
      exact_mod_cast this
    rw [hs.2 v hv hv0]
    exact hex v hv hvn
  · rw [hs.1 t ht] at htar
    exact htg t htn ht htar

/-- **The `near` field of `RetainedBufferStatement D C` from the image-state facts**, for comparisons satisfying the
SDE half. -/
theorem retainedBuffer_near_of_imgPath {D : ConstructionFamily.{u}} {C : ComparisonFamily.{u}}
    (hsde : RetainedStoppedSDEStatement D C)
    (hreach : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
      MeasurableSet (((D Ω c).experiment r).data.reach l a))
    (himg : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
        ∀ n, ∀ᶠ m in atTop, NearImgPath ((C Ω c r).near l ω) (condExpKernel c.P (c.sigma r l) ω)
          (((D Ω c).experiment r).data.sample l) (((D Ω c).experiment r).data.reach l) n m)
    (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
      ∀ n, ∀ᶠ m in atTop, NearBufferFact ((C Ω c r).near l ω)
        (condExpKernel c.P (c.sigma r l) ω) (((D Ω c).experiment r).data.sample l)
        (((D Ω c).experiment r).data.reach l) n m := by
  filter_upwards [hsde.near Ω c r l, himg Ω c r l] with ω hs hi halive n
  filter_upwards [hs halive n, hi halive n] with m h1 h2
  exact nearBufferFact_of_imgPath h1 (hreach Ω c r l _) h2

/-! ### ROOT2's frame -/

/-- **The near facts for ROOT2's construction in terms of the actual stage driver** (ROOT2): for the comparison
driver `(−1)^{|l|} 2^{r.2} R(·/4^{r.2})` (`R` the stage relative driver of the selected candidate's instance) and
the stop `4^{r.2} τ` (`τ` the near stage stop), the stop is positive, the image state at the stop is outside the
buffer, and an image-state visit of the target before the stop puts the actual sample in ROOT2's reach set. -/
def RootNearImg (K : PkgFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) : Prop :=
  ∀ᵐ ω ∂c.P, ω ∈ ((RootJ31.constructionFamily Ω c).experiment r).data.alive ((RootJ31.constructionFamily Ω c).G r) l →
    ∀ n : ℕ, ∀ᶠ m in atTop, ∀ᵐ ξ ∂(condExpKernel c.P (c.sigma r l) ω),
      0 < (4 : ℝ≥0∞) ^ r.2 * ((K Ω c r).nearStop l n m ((K Ω c r).nearCandidate l ω n m)).stop ξ ∧
      (∀ v : ℝ≥0,
        (v : ℝ≥0∞) = (4 : ℝ≥0∞) ^ r.2 * ((K Ω c r).nearStop l n m ((K Ω c r).nearCandidate l ω n m)).stop ξ →
        v < (n : ℝ≥0) →
        imgState ((K Ω c r).nearFamily l ω).xL ((K Ω c r).nearFamily l ω).xR (fun s => (-1 : ℝ) ^ l.length *
          ((2 : ℝ) ^ r.2 * ((K Ω c r).inst l ((K Ω c r).nearCandidate l ω n m)).drv c (s / (4 : ℝ≥0) ^ r.2) ξ))
          v ∉ nearBuffer ((K Ω c r).nearFamily l ω) n) ∧
      ∀ t : ℝ≥0, t < (n : ℝ≥0) →
        (t : ℝ≥0∞) < (4 : ℝ≥0∞) ^ r.2 * ((K Ω c r).nearStop l n m ((K Ω c r).nearCandidate l ω n m)).stop ξ →
        imgState ((K Ω c r).nearFamily l ω).xL ((K Ω c r).nearFamily l ω).xR (fun s => (-1 : ℝ) ^ l.length *
          ((2 : ℝ) ^ r.2 * ((K Ω c r).inst l ((K Ω c r).nearCandidate l ω n m)).drv c (s / (4 : ℝ≥0) ^ r.2) ξ))
          t ∈ nearTarget ((K Ω c r).nearFamily l ω) →
        RootJ31.sourceSample c r l ((K Ω c r).nearCandidate l ω n m) ξ ∈ RootD25.reachSet

/-- `RootNearImg` is `NearImgPath` for ROOT2's construction and the comparison family of the SDE half. -/
theorem nearImgPath_rootFrame (K : PkgFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (h : RootNearImg K Ω c r l) :
    ∀ᵐ ω ∂c.P, ω ∈ ((RootJ31.constructionFamily Ω c).experiment r).data.alive ((RootJ31.constructionFamily Ω c).G r) l →
      ∀ n, ∀ᶠ m in atTop, NearImgPath ((comparisonFamilyO K.rootFrame.frame Ω c r).near l ω)
        (condExpKernel c.P (c.sigma r l) ω) (((RootJ31.constructionFamily Ω c).experiment r).data.sample l)
        (((RootJ31.constructionFamily Ω c).experiment r).data.reach l) n m := by
  filter_upwards [h] with ω hω halive n
  filter_upwards [hω halive n] with m hm
  filter_upwards [hm] with ξ hξ
  obtain ⟨h0, hex, htg⟩ := hξ
  have hW : (fun s => (((comparisonFamilyO K.rootFrame.frame Ω c r).near l ω).dynamics n m).W s ξ) =
      fun s => (-1 : ℝ) ^ l.length *
        ((2 : ℝ) ^ r.2 * ((K Ω c r).inst l ((K Ω c r).nearCandidate l ω n m)).drv c (s / (4 : ℝ≥0) ^ r.2) ξ) :=
    funext fun s => rootFrame_near_W K Ω c r l ω n m s ξ
  have hS := rootFrame_near_stop K Ω c r l ω n m ξ
  refine ⟨hS ▸ h0, fun v hv hvn => ?_, fun t htn ht htar => ?_⟩
  · rw [hW]
    exact hex v (hv.trans hS) hvn
  · rw [hW] at htar
    exact htg t htn (ht.trans_eq hS) htar

/-- **The `near` field of ROOT2's buffer statement for the comparison family of the SDE half**, from the SDE half and
`RootNearImg`. -/
theorem retainedBuffer_near_rootFrame (K : PkgFamily.{u})
    (hsde : RetainedStoppedSDEStatement RootJ31.constructionFamily (comparisonFamilyO K.rootFrame.frame))
    (himg : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), RootNearImg K Ω c r l)
    (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω ∂c.P, ω ∈ ((RootJ31.constructionFamily Ω c).experiment r).data.alive ((RootJ31.constructionFamily Ω c).G r) l →
      ∀ n, ∀ᶠ m in atTop, NearBufferFact ((comparisonFamilyO K.rootFrame.frame Ω c r).near l ω)
        (condExpKernel c.P (c.sigma r l) ω) (((RootJ31.constructionFamily Ω c).experiment r).data.sample l)
        (((RootJ31.constructionFamily Ω c).experiment r).data.reach l) n m :=
  retainedBuffer_near_of_imgPath hsde (fun _ _ _ c r l a => RootJ31.experiment_reach_measurable c r l a)
    (fun Ω _ _ c r l => nearImgPath_rootFrame K Ω c r l (himg Ω c r l)) Ω c r l

/-- **ROOT2's whole buffer statement for the comparison family of the SDE half**, from the SDE half (for the near
dynamics), `RootNearImg`, and the slow inputs of `GW2SdgRead`. -/
theorem retainedBufferStatement_rootFrame_of_img (K : PkgFamily.{u})
    (hsde : RetainedStoppedSDEStatement RootJ31.constructionFamily (comparisonFamilyO K.rootFrame.frame))
    (himg : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), RootNearImg K Ω c r l)
    (hid : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a, RootDriverId K Ω c r l a)
    (hst : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a, RootStartFrozen Ω c r l a)
    (hcov : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a, RootStopCovers K Ω c r l a)
    (hsh : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a, RootShellChoice K Ω c r l a) :
    RetainedBufferStatement RootJ31.constructionFamily (comparisonFamilyO K.rootFrame.frame) :=
  retainedBufferStatement_rootFrame K (retainedBuffer_near_rootFrame K hsde himg) hid hst hcov hsh

end InteractingSLE.Theorem14.GW2Sdg
