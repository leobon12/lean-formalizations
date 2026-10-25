import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Frame
import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate




 






set_option autoImplicit false
noncomputable section
open Set

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge

 
theorem lerp_image_eq_uIcc (a b : ℝ) :
    (fun t : ℝ => a + t * (b - a)) '' Icc (0 : ℝ) 1 = uIcc a b := by
  rw [← segment_eq_uIcc, segment_eq_image_lineMap]
  ext x
  simp only [Set.mem_image, AffineMap.lineMap_apply_module']
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by simp only [smul_eq_mul]; ring⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by simp only [smul_eq_mul]; ring⟩

 
theorem segment_eq_segment (a b : ℂ) : Objects.CorrectedEvent.segment a b = segment ℝ a b := by
  ext z
  simp only [Objects.CorrectedEvent.segment, Set.mem_ofPred_eq, segment_eq_image_lineMap,
    Set.mem_image, AffineMap.lineMap_apply_module']
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    simp only [Complex.real_smul]
    ring
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    simp only [Complex.real_smul]
    ring

 
theorem radial_range_eq_segment (a b θ : ℝ) :
    range (Objects.Tube.polarPath a b θ θ) = Objects.CorrectedEvent.segment (Objects.Tube.pol a θ) (Objects.Tube.pol b θ) := by
  rw [segment_eq_segment, segment_eq_image_lineMap]
  ext z
  simp only [Set.mem_range, Set.mem_image, AffineMap.lineMap_apply_module']
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨(t : ℝ), t.property, ?_⟩
    rw [Objects.Tube.polarPath_apply]
    simp only [sub_self, mul_zero, add_zero, Objects.Tube.pol]
    push_cast
    simp only [Complex.real_smul]
    ring
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [Objects.Tube.polarPath_apply]
    simp only [sub_self, mul_zero, add_zero, Objects.Tube.pol]
    push_cast
    simp only [Complex.real_smul]
    ring

 
theorem angular_range_eq_arc (R φ₁ φ₂ : ℝ) :
    range (Objects.Tube.polarPath R R φ₁ φ₂) = Objects.CorrectedEvent.arc R φ₁ φ₂ := by
  ext z
  simp only [Objects.CorrectedEvent.arc, Set.mem_ofPred_eq, Set.mem_range,
    Objects.Tube.polarPath_apply, sub_self, mul_zero, add_zero]
  change (∃ t : unitInterval, Objects.Tube.pol R (φ₁ + (t : ℝ) * (φ₂ - φ₁)) = z) ↔
    ∃ θ ∈ uIcc φ₁ φ₂, z = Objects.Tube.pol R θ
  rw [← lerp_image_eq_uIcc]
  simp only [Set.mem_image]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, ⟨(t : ℝ), t.property, rfl⟩, rfl⟩
  · rintro ⟨θ, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩

 
theorem spoke_range_eq_interval (a b θ : ℝ) :
    range (Objects.Tube.polarPath a b θ θ) =
      {z : ℂ | ∃ R ∈ uIcc a b, z = Objects.Tube.pol R θ} := by
  ext z
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨a + (t : ℝ) * (b - a), ?_, ?_⟩
    · rw [← lerp_image_eq_uIcc]
      exact ⟨(t : ℝ), t.property, rfl⟩
    · rw [Objects.Tube.polarPath_apply]
      simp only [sub_self, mul_zero, add_zero]
  · rintro ⟨R, hR, rfl⟩
    rw [← lerp_image_eq_uIcc] at hR
    obtain ⟨t, ht, rfl⟩ := hR
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [Objects.Tube.polarPath_apply]
    simp only [sub_self, mul_zero, add_zero]

 
theorem out_twist_eq_ranges (T : Objects.CorrectedEvent.TubeData) (k : Fin T.K) :
    Objects.CorrectedEvent.outTwist T k =
      range (Objects.Tube.t1 (Objects.CorrectedEvent.twistAngle T k)) ∪
      range (Objects.Tube.t2 (Objects.CorrectedEvent.twistAngle T k)) ∪
      range (Objects.Tube.t3 (Objects.CorrectedEvent.twistAngle T k)) ∪
      range (Objects.Tube.t4 (Objects.CorrectedEvent.twistAngle T k)) := by
  unfold Objects.CorrectedEvent.outTwist Objects.Tube.t1 Objects.Tube.t2 Objects.Tube.t3 Objects.Tube.t4
  rw [angular_range_eq_arc, angular_range_eq_arc,
    spoke_range_eq_interval, spoke_range_eq_interval]
  simp only [uIcc_of_le (show (5 / 2 : ℝ) ≤ 7 / 2 by norm_num),
    uIcc_of_le (show (7 / 2 : ℝ) ≤ 4 by norm_num)]
  rw [show (2.5 : ℝ) = 5 / 2 by norm_num,
      show (3.5 : ℝ) = 7 / 2 by norm_num]
  rfl

 
theorem out_stub_eq_ranges (T : Objects.CorrectedEvent.TubeData)
    (hsp : Objects.CorrectedEvent.sPrime T ≤ 2 / 3) :
    Objects.CorrectedEvent.outStub T =
      range (Objects.Tube.o1 (Objects.CorrectedEvent.sPrime T) T.psiV) ∪
      range (Objects.Tube.o2 T.psiV) ∪ range Objects.Tube.o3 := by
  have hrad : 1 + 3 * Objects.CorrectedEvent.sPrime T / 4 ≤ (3 / 2 : ℝ) := by linarith
  have h1 : range (Objects.Tube.o1 (Objects.CorrectedEvent.sPrime T) T.psiV) =
      {w : ℂ | ∃ t ∈ Icc (1 + 3 * Objects.CorrectedEvent.sPrime T / 4) (1.5 : ℝ),
        w = Objects.CorrectedEvent.polar t T.psiV} := by
    unfold Objects.Tube.o1
    rw [spoke_range_eq_interval, uIcc_of_le hrad]
    rw [show (1.5 : ℝ) = 3 / 2 by norm_num]
    rfl
  have h2 : range (Objects.Tube.o2 T.psiV) = Objects.CorrectedEvent.arc 1.5 T.psiV 0 := by
    unfold Objects.Tube.o2
    rw [angular_range_eq_arc]
    norm_num
  have h3 : range Objects.Tube.o3 = Objects.CorrectedEvent.segment (1.5 : ℂ) (2.5 : ℂ) := by
    unfold Objects.Tube.o3
    rw [radial_range_eq_segment]
    simp only [Objects.Tube.pol, Objects.Tube.ex_zero, mul_one]
    norm_num
  rw [h1, h2, h3]
  rfl

 
theorem in_stub_eq_ranges (T : Objects.CorrectedEvent.TubeData) :
    Objects.CorrectedEvent.inStub T =
      range (Objects.Tube.i1 T.alpha (Objects.CorrectedEvent.sPrime T) T.psiU) ∪ range Objects.Tube.i2 := by
  have h1 : range (Objects.Tube.i1 T.alpha (Objects.CorrectedEvent.sPrime T) T.psiU) =
      Objects.CorrectedEvent.segment 0 (Objects.CorrectedEvent.polar (T.alpha - 3 * Objects.CorrectedEvent.sPrime T / 4) T.psiU) := by
    rw [Objects.Tube.range_i1, radial_range_eq_segment, Objects.Tube.pol_zero_left]
    rfl
  have h2 : range Objects.Tube.i2 = Objects.CorrectedEvent.segment (-(2.5 : ℂ)) 0 := by
    unfold Objects.Tube.i2
    rw [radial_range_eq_segment, Objects.Tube.pol_pi, Objects.Tube.pol_zero_left]
    norm_num
  rw [h1, h2]
  rfl

 
theorem out_path_eq_literal (T : Objects.CorrectedEvent.TubeData) (k : Fin T.K)
    (hsp : Objects.CorrectedEvent.sPrime T ≤ 2 / 3) :
    range (Objects.Tube.outPath (Objects.CorrectedEvent.sPrime T) T.psiV (Objects.CorrectedEvent.twistAngle T k)) =
      Objects.CorrectedEvent.outStub T ∪ Objects.CorrectedEvent.outTwist T k := by
  rw [Objects.Tube.range_outPath, out_stub_eq_ranges T hsp, out_twist_eq_ranges]
  unfold Objects.Tube.outRest
  ext x
  simp only [Set.mem_union]
  tauto

 
theorem neg_image_polar_range (R₁ R₂ φ₁ φ₂ : ℝ) :
    (fun z : ℂ => -z) '' range (Objects.Tube.polarPath R₁ R₂ φ₁ φ₂) =
      range (Objects.Tube.polarPath R₁ R₂ (φ₁ + Real.pi) (φ₂ + Real.pi)) := by
  ext z
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
    refine ⟨t, ?_⟩
    rw [Objects.Tube.polarPath_apply, Objects.Tube.polarPath_apply]
    have ha : (φ₁ + Real.pi) + (t : ℝ) * ((φ₂ + Real.pi) - (φ₁ + Real.pi)) =
        (φ₁ + (t : ℝ) * (φ₂ - φ₁)) + Real.pi := by ring
    rw [ha, Objects.Tube.pol_add_pi]
  · rintro ⟨t, rfl⟩
    refine ⟨Objects.Tube.polarPath R₁ R₂ φ₁ φ₂ t, ⟨t, rfl⟩, ?_⟩
    rw [Objects.Tube.polarPath_apply, Objects.Tube.polarPath_apply]
    have ha : (φ₁ + Real.pi) + (t : ℝ) * ((φ₂ + Real.pi) - (φ₁ + Real.pi)) =
        (φ₁ + (t : ℝ) * (φ₂ - φ₁)) + Real.pi := by ring
    rw [ha, Objects.Tube.pol_add_pi]

 
theorem radial_range_swap (a b θ : ℝ) :
    range (Objects.Tube.polarPath a b θ θ) = range (Objects.Tube.polarPath b a θ θ) := by
  rw [spoke_range_eq_interval, spoke_range_eq_interval, uIcc_comm]

 
theorem angular_range_swap (R a b : ℝ) :
    range (Objects.Tube.polarPath R R a b) = range (Objects.Tube.polarPath R R b a) := by
  rw [angular_range_eq_arc, angular_range_eq_arc]
  unfold Objects.CorrectedEvent.arc
  simp only [min_comm, max_comm]

 
theorem reflected_twist_eq_ranges (T : Objects.CorrectedEvent.TubeData) (k : Fin T.K) :
    (fun z : ℂ => -z) '' Objects.CorrectedEvent.outTwist T k =
      range (Objects.Tube.nt4 (Objects.CorrectedEvent.twistAngle T k)) ∪
      range (Objects.Tube.nt3 (Objects.CorrectedEvent.twistAngle T k)) ∪
      range (Objects.Tube.nt2 (Objects.CorrectedEvent.twistAngle T k)) ∪
      range (Objects.Tube.nt1 (Objects.CorrectedEvent.twistAngle T k)) := by
  let d := Objects.CorrectedEvent.twistAngle T k
  have h1 : (fun z : ℂ => -z) '' range (Objects.Tube.t1 d) = range (Objects.Tube.nt1 d) := by
    unfold Objects.Tube.t1 Objects.Tube.nt1
    rw [neg_image_polar_range, angular_range_swap]
    rw [angular_range_eq_arc, angular_range_eq_arc]
    simp only [zero_add]
  have h2 : (fun z : ℂ => -z) '' range (Objects.Tube.t2 d) = range (Objects.Tube.nt2 d) := by
    unfold Objects.Tube.t2 Objects.Tube.nt2
    rw [neg_image_polar_range, radial_range_swap]
  have h3 : (fun z : ℂ => -z) '' range (Objects.Tube.t3 d) = range (Objects.Tube.nt3 d) := by
    unfold Objects.Tube.t3 Objects.Tube.nt3
    rw [neg_image_polar_range, angular_range_swap]
  have h4 : (fun z : ℂ => -z) '' range (Objects.Tube.t4 d) = range (Objects.Tube.nt4 d) := by
    unfold Objects.Tube.t4 Objects.Tube.nt4
    rw [neg_image_polar_range, radial_range_swap]
  rw [out_twist_eq_ranges]
  simp only [Set.image_union]
  rw [h1, h2, h3, h4]
  ext x
  simp only [Set.mem_union]
  tauto

 
theorem in_path_eq_literal (T : Objects.CorrectedEvent.TubeData) (k : Fin T.K) :
    range (Objects.Tube.inPath T.alpha (Objects.CorrectedEvent.sPrime T) T.psiU (Objects.CorrectedEvent.twistAngle T k)) =
      (fun z : ℂ => -z) '' Objects.CorrectedEvent.outTwist T k ∪ Objects.CorrectedEvent.inStub T := by
  rw [Objects.Tube.range_inPath, reflected_twist_eq_ranges, in_stub_eq_ranges]
  unfold Objects.Tube.inRest
  ext x
  simp only [Set.mem_union]
  tauto


end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge
