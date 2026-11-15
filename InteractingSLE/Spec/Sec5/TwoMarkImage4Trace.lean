/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkImage4Geometry

/-!
# The canonical forward image of a given generating trace

The inverse capacity clock and target change define the image trace before
its horizon. Its continuity and hull generation use the original trace and
the existing deterministic image-hull identity, without stochastic inputs.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Sec5.TwoMark.Image4

open Zhan.Retarget

/-- The forward image trace read in the inverse capacity clock. -/
def imageTrace (a : ℝ) (w vk : ℝ≥0 → ℝ) (η : ℝ≥0 → ℂ) (u : ℝ≥0) : ℂ :=
  Sec7.targetChange a (η (invClk (rate a w vk) u).toNNReal)

variable {a : ℝ} {w vk : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- At an original time the forward image has precisely the target-changed value. -/
theorem imageTrace_clk (hd : PullData w vk a T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    imageTrace a w vk η (clk (rate a w vk) t).toNNReal = Sec7.targetChange a (η t) := by
  have h0 := (hd.isRate ht).clk_nonneg ⟨t.coe_nonneg, le_rfl⟩
  simp only [imageTrace, Real.coe_toNNReal _ h0, (hd.isRate ht).invClk_clk ⟨t.coe_nonneg, le_rfl⟩,
    Real.toNNReal_coe]

/-- The canonical image starts at the origin. -/
theorem imageTrace_zero (hη : IsGeneratingTrace w T η) : imageTrace a w vk η 0 = 0 := by
  simp only [imageTrace, NNReal.coe_zero, invClk_zero_eq, Real.toNNReal_zero, hη.1,
    Sec7.targetChange, zero_div]

/-- The canonical image is continuous at every time before its image horizon. -/
theorem continuousAt_imageTrace (hd : PullData w vk a T) (hη : IsGeneratingTrace w T η)
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < newHorizon a w vk T) :
    ContinuousAt (imageTrace a w vk η) u := by
  obtain ⟨S, hST, hR, huS, hmem, -⟩ := newTime_spec hd.sep hd.pos hu
  have hC0 := hR.clk_nonneg ⟨S.coe_nonneg, le_rfl⟩
  have huS' : u < (clk (rate a w vk) S).toNNReal := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hC0]
    exact huS
  have hic : ContinuousOn (fun v : ℝ≥0 => invClk (rate a w vk) v)
      (Iic (clk (rate a w vk) S).toNNReal) := by
    refine hR.continuousOn_invClk.comp NNReal.continuous_coe.continuousOn fun v hv => ?_
    refine ⟨v.coe_nonneg, ?_⟩
    have h := NNReal.coe_le_coe.2 hv
    rwa [Real.coe_toNNReal _ hC0] at h
  have hclock : ContinuousAt (fun v : ℝ≥0 => (invClk (rate a w vk) v).toNNReal) u :=
    continuous_real_toNNReal.continuousAt.comp (hic.continuousAt (Iic_mem_nhds huS'))
  have ht := invClk_lt hd.sep hd.pos hu
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < T} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hηc : ContinuousAt η (invClk (rate a w vk) u).toNNReal :=
    (hη.2.1 _ ht.le).continuousAt (Filter.mem_of_superset (hopen.mem_nhds ht) fun v (hs : (v : ℝ≥0∞) < T) => hs.le)
  have hcη : ContinuousAt (fun v : ℝ≥0 => η (invClk (rate a w vk) v).toNNReal) u :=
    ContinuousAt.comp (f := fun v : ℝ≥0 => (invClk (rate a w vk) v).toNNReal) hηc hclock
  exact ContinuousAt.comp (f := fun v : ℝ≥0 => η (invClk (rate a w vk) v).toNNReal)
    (Local2.continuousAt_targetChange_of_ne (trace_ne_target hd hη ht)) hcη

/-- The image of the trace prefix is the target change of the original prefix. -/
theorem image_imageTrace_Icc (hd : PullData w vk a T) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < newHorizon a w vk T) :
    imageTrace a w vk η '' Icc 0 u =
      Sec7.targetChange a '' (η '' Icc 0 (invClk (rate a w vk) u).toNNReal) := by
  obtain ⟨S, hST, hR, -, hmem, hclk⟩ := newTime_spec hd.sep hd.pos hu
  set t := (invClk (rate a w vk) u).toNNReal
  have ht : (t : ℝ≥0∞) < T := invClk_lt hd.sep hd.pos hu
  have he : (clk (rate a w vk) t).toNNReal = u := by
    rw [show (t : ℝ) = invClk (rate a w vk) u from Real.coe_toNNReal _ hmem.1,
      hclk, Real.toNNReal_coe]
  calc imageTrace a w vk η '' Icc 0 u =
        imageTrace a w vk η '' ((fun s : ℝ≥0 => (clk (rate a w vk) s).toNNReal) '' Icc 0 t) := by
          rw [hd.image_clk_Icc ht, he]
    _ = Sec7.targetChange a '' (η '' Icc 0 t) := by
      rw [image_image, image_image]
      exact image_congr fun s hs => imageTrace_clk hd ((ENNReal.coe_le_coe.2 hs.2).trans_lt ht)

/-- The image curve generates the canonical image hull before its horizon. -/
theorem isFilling_imageTrace (hd : PullData w vk a T) (hη : IsGeneratingTrace w T η)
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < newHorizon a w vk T) :
    IsFilling (fwdHull (fun s : ℝ => newDrv a w vk s.toNNReal) u)
      (imageTrace a w vk η '' Icc 0 u) := by
  obtain ⟨S, hST, hR, -, hmem, hclk⟩ := newTime_spec hd.sep hd.pos hu
  set t := (invClk (rate a w vk) u).toNNReal
  have ht : (t : ℝ≥0∞) < T := invClk_lt hd.sep hd.pos hu
  have he : clk (rate a w vk) t = u := by
    rw [show (t : ℝ) = invClk (rate a w vk) u from Real.coe_toNNReal _ hmem.1, hclk]
  obtain ⟨r, hr, hdj⟩ := exists_ball_disjoint_originalHull hd ht
  have hm : QuantumZipper.CA.realMobius 1 0 (-1) a = Sec7.targetChange a := by
    funext z
    simp only [QuantumZipper.CA.realMobius, Sec7.targetChange, Complex.ofReal_one, one_mul,
      Complex.ofReal_zero, add_zero, Complex.ofReal_neg, neg_mul]
    congr 1
    ring
  have hpole : CrossRestart.mobPole (-1) a = a := by simp [CrossRestart.mobPole]
  have hfill := CrossRestart.isFilling_image_realMobius (a := 1) (b := 0) (c := -1) (d := a)
    (by simpa only [one_mul, zero_mul, sub_zero] using hd.pos) (by norm_num)
    (hd.isHPHull_fwdHull ht) hr (by simpa only [hpole] using hdj) (hη.2.2 t ht)
  rw [hm] at hfill
  have hH : ∀ s ∈ Icc (0 : ℝ≥0) t, Sec7.targetChange a (η s) ∈ H ↔ η s ∈ H := by
    intro s hs
    refine ⟨fun hz => ?_, Sec7.targetChange_mem_H hd.pos⟩
    have h := Sec7.targetChangeInv_mem_H hd.pos hz
    rwa [Sec7.targetChangeInv_targetChange hd.pos.ne'
      (trace_ne_target hd hη ((ENNReal.coe_le_coe.2 hs.2).trans_lt ht))] at h
  have himg : Sec7.targetChange a '' (η '' Icc 0 t ∩ H) =
      (Sec7.targetChange a '' (η '' Icc 0 t)) ∩ H := by
    ext z
    constructor
    · rintro ⟨_, ⟨⟨s, hs, rfl⟩, hz⟩, rfl⟩
      exact ⟨⟨_, ⟨s, hs, rfl⟩, rfl⟩, (hH s hs).2 hz⟩
    · rintro ⟨⟨_, ⟨s, hs, rfl⟩, rfl⟩, hz⟩
      exact ⟨_, ⟨⟨s, hs, rfl⟩, (hH s hs).1 hz⟩, rfl⟩
  rw [himg] at hfill
  have hK := hd.fwdHull_newDrv_eq ht
  rw [he] at hK
  rw [hK, image_imageTrace_Icc hd hu]
  exact CrossRestart.isFilling_inter_H_iff.1 hfill

/-- Every compact interval before the image horizon has the canonical image trace. -/
theorem isGeneratingTrace_imageTrace_before (hd : PullData w vk a T) (hη : IsGeneratingTrace w T η)
    {U : ℝ≥0} (hU : (U : ℝ≥0∞) < newHorizon a w vk T) :
    IsGeneratingTrace (newDrv a w vk) U (imageTrace a w vk η) := by
  refine ⟨imageTrace_zero hη, fun t ht => ?_, fun t ht => ?_⟩
  · exact (continuousAt_imageTrace hd hη ((show (t : ℝ≥0∞) ≤ U from ht).trans_lt hU)).continuousWithinAt
  · exact isFilling_imageTrace hd hη (ht.trans hU)

/-- Original trace injectivity gives image injectivity before the image horizon. -/
theorem injOn_imageTrace (hd : PullData w vk a T) (hη : IsGeneratingTrace w T η)
    (hinj : InjOn η {t : ℝ≥0 | (t : ℝ≥0∞) ≤ T}) :
    InjOn (imageTrace a w vk η) {u : ℝ≥0 | (u : ℝ≥0∞) < newHorizon a w vk T} := by
  intro u hu v hv he
  have htu := invClk_lt hd.sep hd.pos hu
  have htv := invClk_lt hd.sep hd.pos hv
  have hηeq := congrArg (Sec7.targetChangeInv a) he
  change Sec7.targetChangeInv a (Sec7.targetChange a (η (invClk (rate a w vk) u).toNNReal)) =
    Sec7.targetChangeInv a (Sec7.targetChange a (η (invClk (rate a w vk) v).toNNReal)) at hηeq
  rw [Sec7.targetChangeInv_targetChange hd.pos.ne' (trace_ne_target hd hη htu),
    Sec7.targetChangeInv_targetChange hd.pos.ne' (trace_ne_target hd hη htv)] at hηeq
  have htime := hinj htu.le htv.le hηeq
  obtain ⟨Su, -, -, -, hmu, hcu⟩ := newTime_spec hd.sep hd.pos hu
  obtain ⟨Sv, -, -, -, hmv, hcv⟩ := newTime_spec hd.sep hd.pos hv
  have heq := congrArg (fun s : ℝ≥0 => clk (rate a w vk) s) htime
  rw [Real.coe_toNNReal _ hmu.1, Real.coe_toNNReal _ hmv.1, hcu, hcv] at heq
  exact NNReal.coe_injective heq

/-- No endpoint extension is needed when the image horizon is infinite. -/
theorem isGeneratingTrace_imageTrace_top (hd : PullData w vk a T) (hη : IsGeneratingTrace w T η)
    (hH : newHorizon a w vk T = ⊤) :
    IsGeneratingTrace (newDrv a w vk) ⊤ (imageTrace a w vk η) := by
  have hu : ∀ u : ℝ≥0, (u : ℝ≥0∞) < newHorizon a w vk T := fun u => by
    rw [hH]; exact ENNReal.coe_lt_top
  exact ⟨imageTrace_zero hη, fun u _ => (continuousAt_imageTrace hd hη (hu u)).continuousWithinAt,
    fun u _ => isFilling_imageTrace hd hη (hu u)⟩

end InteractingSLE.Sec5.TwoMark.Image4
