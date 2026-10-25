import SupercriticalLQGUniqueness.B2.LscTop.Compact
import SupercriticalLQGUniqueness.B2.LscTop.Limits

 













set_option autoImplicit false
noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

def IsMetricLSCFun (f : LSCFun) : Prop :=
  (∀ p, 0 ≤ f.1 p) ∧ IsExtMetric (fun p => (f.1 p).toENNReal)

 

theorem isClosed_setOf_apply_le (a : EReal) :
    IsClosed {u : LSCFun × (ℂ × ℂ) | u.1.1 u.2 ≤ a} := by
  apply IsSeqClosed.isClosed
  intro u v hu hv
  have h1 : Tendsto (fun n => (u n).1) atTop (𝓝 v.1) :=
    (continuous_fst.tendsto v).comp hv
  have h2 : Tendsto (fun n => (u n).2) atTop (𝓝 v.2) :=
    (continuous_snd.tendsto v).comp hv
  have hl := (LSCFun.lscTendsto_of_tendsto h1).1 (fun n => (u n).2) v.2 h2
  exact hl.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n => hu n))

 
theorem isOpen_setOf_lt_apply_prod (a : EReal) :
    IsOpen {u : LSCFun × (ℂ × ℂ) | a < u.1.1 u.2} := by
  have h := (isClosed_setOf_apply_le a).isOpen_compl
  simpa only [compl_ofPred, not_le] using h

 

def ballFamily (j : ℕ × ℕ) : Set (ℂ × ℂ) :=
  Metric.closedBall (denseSeq (ℂ × ℂ) j.1) (1 / ((j.2 : ℝ) + 1))

theorem isCompact_ballFamily (j : ℕ × ℕ) : IsCompact (ballFamily j) :=
  isCompact_closedBall _ _

theorem exists_ballFamily {p : ℂ × ℂ} {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hp : p ∈ U) : ∃ j, p ∈ ballFamily j ∧ ballFamily j ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU p hp
  obtain ⟨i, hi⟩ := exists_nat_one_div_lt (half_pos hε)
  obtain ⟨k, hk⟩ := (denseRange_denseSeq (ℂ × ℂ)).exists_dist_lt p
    (Nat.one_div_pos_of_nat (n := i))
  refine ⟨(k, i), ?_, ?_⟩
  · change dist p (denseSeq (ℂ × ℂ) k) ≤ 1 / ((i : ℝ) + 1)
    exact hk.le
  · intro q hq
    change dist q (denseSeq (ℂ × ℂ) k) ≤ 1 / ((i : ℝ) + 1) at hq
    apply hball
    rw [Metric.mem_ball]
    calc dist q p ≤ dist q (denseSeq (ℂ × ℂ) k) + dist (denseSeq (ℂ × ℂ) k) p :=
          dist_triangle _ _ _
      _ < 1 / ((i : ℝ) + 1) + 1 / ((i : ℝ) + 1) :=
          add_lt_add_of_le_of_lt hq (by rw [dist_comm]; exact hk)
      _ < ε := by linarith

 

theorem isClosed_fst_image_of_compact {Y : Type*} [TopologicalSpace Y]
    {C : Set (LSCFun × Y)} (hC : IsClosed C) {K : Set Y} (hK : IsCompact K)
    (hCK : C ⊆ univ ×ˢ K) : IsClosed (Prod.fst '' C) :=
  ((isCompact_univ.prod hK).of_isClosed_subset hC hCK).image continuous_fst
    |>.isClosed

theorem isClosed_nonneg : IsClosed {f : LSCFun | ∀ p, 0 ≤ f.1 p} := by
  have h := (LSCFun.isOpen_setOf_exists_lt (O := univ) isOpen_univ 0).isClosed_compl
  convert h using 1
  ext f
  simp only [mem_ofPred_eq, mem_compl_iff, mem_univ, true_and, not_exists, not_lt]

theorem isClosed_diag : IsClosed {f : LSCFun | ∀ x : ℂ, f.1 (x, x) ≤ 0} := by
  have h : IsOpen (⋃ x : ℂ, {f : LSCFun | 0 < f.1 (x, x)}) :=
    isOpen_iUnion fun x => LSCFun.isOpen_setOf_lt_apply (x, x) 0
  convert h.isClosed_compl using 1
  ext f
  simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion, not_exists, not_lt]

theorem isClosed_symm : IsClosed {f : LSCFun | ∀ p, f.1 p.swap ≤ f.1 p} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro f hf
  simp only [mem_compl_iff, mem_ofPred_eq, not_forall, not_le] at hf
  obtain ⟨p, hp⟩ := hf
  obtain ⟨t, ht1, ht2⟩ := exists_between hp
  have hO : IsOpen {q : ℂ × ℂ | t < f.1 q} := f.2.isOpen_preimage t
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO p.swap ht2
  let K : Set (ℂ × ℂ) := Metric.closedBall p.swap (r / 2)
  let O : Set (ℂ × ℂ) := Prod.swap ⁻¹' Metric.ball p.swap (r / 2)
  have hOo : IsOpen O := Metric.isOpen_ball.preimage continuous_swap
  refine ⟨{g | ∃ q ∈ O, g.1 q < t} ∩ {g | ∀ q ∈ K, t < g.1 q}, ?_, ?_, ?_⟩
  · rintro g ⟨⟨q, hqO, hq⟩, hK⟩
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, not_le]
    exact ⟨q, lt_trans hq (hK q.swap (Metric.ball_subset_closedBall hqO))⟩
  · exact (LSCFun.isOpen_setOf_exists_lt hOo t).inter
      (LSCFun.isOpen_setOf_forall_lt (isCompact_closedBall _ _) t)
  · refine ⟨⟨p, ?_, ht1⟩, fun q hq => hball ?_⟩
    · change dist p.swap p.swap < r / 2
      simpa using half_pos hr
    · exact Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hq)
        (half_lt_self hr))

 
def triSet : Set LSCFun :=
  {f | ∀ x y z : ℂ, (f.1 (x, z)).toENNReal ≤
    (f.1 (x, y)).toENNReal + (f.1 (y, z)).toENNReal}

 
def sepSet : Set LSCFun :=
  {f | ∀ x y : ℂ, (f.1 (x, y)).toENNReal = 0 → x = y}

private theorem toENNReal_le_ofReal_iff {x : EReal} {a : ℝ} (ha : 0 ≤ a) :
    x.toENNReal ≤ ENNReal.ofReal a ↔ x ≤ (a : EReal) := by
  constructor
  · intro h
    calc x ≤ max 0 x := le_max_right _ _
      _ = (x.toENNReal : EReal) := EReal.coe_toENNReal_eq_max.symm
      _ ≤ ((ENNReal.ofReal a : ℝ≥0∞) : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.2 h
      _ = (a : EReal) := by rw [EReal.coe_ennreal_ofReal, max_eq_left ha]
  · intro h
    calc x.toENNReal ≤ ((a : ℝ) : EReal).toENNReal := EReal.toENNReal_le_toENNReal h
      _ = ENNReal.ofReal a := by
          rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top a), EReal.toReal_coe]

private theorem ofReal_lt_toENNReal_iff {x : EReal} {a : ℝ} (ha : 0 ≤ a) :
    ENNReal.ofReal a < x.toENNReal ↔ (a : EReal) < x := by
  rw [← not_le, ← not_le, toENNReal_le_ofReal_iff ha]

 

def triPiece (a b : ℚ) (j : ℕ × ℕ) (m : ℕ) : Set (LSCFun × (ℂ × ℂ × ℂ)) :=
  {u | u.1.1 (u.2.1, u.2.2.1) ≤ ((a : ℝ) : EReal) ∧
    u.1.1 (u.2.2.1, u.2.2.2) ≤ ((b : ℝ) : EReal) ∧
    (u.2.1, u.2.2.2) ∈ ballFamily j ∧ ‖u.2.2.1‖ ≤ m}

theorem isClosed_triPiece (a b : ℚ) (j : ℕ × ℕ) (m : ℕ) :
    IsClosed (triPiece a b j m) := by
  have h1 : IsClosed {u : LSCFun × (ℂ × ℂ × ℂ) |
      u.1.1 (u.2.1, u.2.2.1) ≤ ((a : ℝ) : EReal)} :=
    (isClosed_setOf_apply_le _).preimage
      (continuous_fst.prodMk (continuous_snd.fst.prodMk continuous_snd.snd.fst))
  have h2 : IsClosed {u : LSCFun × (ℂ × ℂ × ℂ) |
      u.1.1 (u.2.2.1, u.2.2.2) ≤ ((b : ℝ) : EReal)} :=
    (isClosed_setOf_apply_le _).preimage
      (continuous_fst.prodMk (continuous_snd.snd.fst.prodMk continuous_snd.snd.snd))
  have h3 : IsClosed {u : LSCFun × (ℂ × ℂ × ℂ) | (u.2.1, u.2.2.2) ∈ ballFamily j} :=
    Metric.isClosed_closedBall.preimage
      (continuous_snd.fst.prodMk continuous_snd.snd.snd)
  have h4 : IsClosed {u : LSCFun × (ℂ × ℂ × ℂ) | ‖u.2.2.1‖ ≤ m} :=
    isClosed_le continuous_snd.snd.fst.norm continuous_const
  exact h1.inter (h2.inter (h3.inter h4))

theorem isClosed_fst_image_triPiece (a b : ℚ) (j : ℕ × ℕ) (m : ℕ) :
    IsClosed (Prod.fst '' triPiece a b j m) := by
  obtain ⟨R, hR⟩ := (isCompact_ballFamily j).isBounded.subset_closedBall 0
  refine isClosed_fst_image_of_compact (K := Metric.closedBall (0 : ℂ × ℂ × ℂ) (R + m))
    (isClosed_triPiece a b j m) (isCompact_closedBall _ _) ?_
  rintro u ⟨-, -, hj, hm⟩
  refine ⟨mem_univ _, ?_⟩
  have hxz := hR hj
  rw [Metric.mem_closedBall, dist_zero_right] at hxz ⊢
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) hxz
  have hx : ‖u.2.1‖ ≤ R := le_trans (norm_fst_le (u.2.1, u.2.2.2)) hxz
  have hz : ‖u.2.2.2‖ ≤ R := le_trans (norm_snd_le (u.2.1, u.2.2.2)) hxz
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [Prod.norm_def, Prod.norm_def]
  refine max_le (by linarith) (max_le (by linarith) (by linarith))

theorem triSet_compl_eq :
    triSetᶜ = ⋃ (a : ℚ) (b : ℚ) (c : ℚ) (_ : 0 ≤ a ∧ 0 ≤ b ∧ a + b < c)
      (j : ℕ × ℕ) (m : ℕ),
      (Prod.fst '' triPiece a b j m) ∩
        {f : LSCFun | ∀ q ∈ ballFamily j, ((c : ℝ) : EReal) < f.1 q} := by
  ext f
  simp only [triSet, mem_compl_iff, mem_ofPred_eq, not_forall, not_le, mem_iUnion,
    mem_inter_iff, mem_image, exists_prop]
  constructor
  · rintro ⟨x, y, z, hlt⟩
    set A := (f.1 (x, y)).toENNReal
    set B := (f.1 (y, z)).toENNReal
    set C := (f.1 (x, z)).toENNReal
    have hAB : A + B < ⊤ := lt_of_lt_of_le hlt le_top
    have hA : A ≠ ⊤ := (ENNReal.add_lt_top.1 hAB).1.ne
    have hB : B ≠ ⊤ := (ENNReal.add_lt_top.1 hAB).2.ne
    
    obtain ⟨c', hc'0, hc'2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hlt
    
    set s : ℝ := c' - (A.toReal + B.toReal) with hs
    have hAB' : A.toReal + B.toReal < c' := by
      have h := hc'2.1
      rw [← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_toReal hB,
        ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg] at h
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).1 h
    have hs0 : 0 < s := by linarith
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show A.toReal < A.toReal + s / 3 by linarith)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show B.toReal < B.toReal + s / 3 by linarith)
    obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (show (a : ℝ) + b < c' by linarith)
    have ha0 : (0 : ℝ) ≤ a := le_trans ENNReal.toReal_nonneg ha1.le
    have hb0 : (0 : ℝ) ≤ b := le_trans ENNReal.toReal_nonneg hb1.le
    have hc0 : (0 : ℝ) ≤ c := by linarith
    have hfxy : f.1 (x, y) ≤ ((a : ℝ) : EReal) := by
      rw [← toENNReal_le_ofReal_iff ha0]
      calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA).symm
        _ ≤ ENNReal.ofReal a := ENNReal.ofReal_le_ofReal ha1.le
    have hfyz : f.1 (y, z) ≤ ((b : ℝ) : EReal) := by
      rw [← toENNReal_le_ofReal_iff hb0]
      calc B = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hB).symm
        _ ≤ ENNReal.ofReal b := ENNReal.ofReal_le_ofReal hb1.le
    have hfxz : ((c : ℝ) : EReal) < f.1 (x, z) := by
      rw [← ofReal_lt_toENNReal_iff hc0]
      exact lt_trans (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc0 |>.2 hc2) hc'2.2
    have hO : IsOpen {q : ℂ × ℂ | ((c : ℝ) : EReal) < f.1 q} := f.2.isOpen_preimage _
    obtain ⟨j, hj, hjsub⟩ := exists_ballFamily hO hfxz
    obtain ⟨m, hm⟩ := exists_nat_ge ‖y‖
    refine ⟨a, b, c, ⟨by exact_mod_cast ha0, by exact_mod_cast hb0, ?_⟩, j, m,
      ⟨(f, (x, y, z)), ⟨hfxy, hfyz, hj, hm⟩, rfl⟩, fun q hq => hjsub hq⟩
    exact_mod_cast hc1
  · rintro ⟨a, b, c, ⟨ha0, hb0, habc⟩, j, m, ⟨u, ⟨h1, h2, h3, -⟩, rfl⟩, hU⟩
    refine ⟨u.2.1, u.2.2.1, u.2.2.2, ?_⟩
    have ha0' : (0 : ℝ) ≤ a := by exact_mod_cast ha0
    have hb0' : (0 : ℝ) ≤ b := by exact_mod_cast hb0
    have hc0' : (0 : ℝ) ≤ c := by
      have : (0 : ℚ) ≤ c := le_trans (add_nonneg ha0 hb0) habc.le
      exact_mod_cast this
    have hA := (toENNReal_le_ofReal_iff ha0').2 h1
    have hB := (toENNReal_le_ofReal_iff hb0').2 h2
    have hC := (ofReal_lt_toENNReal_iff hc0').2 (hU _ h3)
    calc (u.1.1 (u.2.1, u.2.2.1)).toENNReal + (u.1.1 (u.2.2.1, u.2.2.2)).toENNReal
        ≤ ENNReal.ofReal a + ENNReal.ofReal b := add_le_add hA hB
      _ = ENNReal.ofReal ((a : ℝ) + b) := (ENNReal.ofReal_add ha0' hb0').symm
      _ < ENNReal.ofReal c := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
          (add_nonneg ha0' hb0')).2 (by exact_mod_cast habc)
      _ < (u.1.1 (u.2.1, u.2.2.2)).toENNReal := hC

 
def sepPiece (m : ℕ) : Set (LSCFun × (ℂ × ℂ)) :=
  {u | u.1.1 u.2 ≤ 0 ∧ 1 / ((m : ℝ) + 1) ≤ dist u.2.1 u.2.2 ∧ ‖u.2‖ ≤ m}

theorem isClosed_fst_image_sepPiece (m : ℕ) : IsClosed (Prod.fst '' sepPiece m) := by
  have hC : IsClosed (sepPiece m) :=
    (isClosed_setOf_apply_le 0).inter
      ((isClosed_le continuous_const (continuous_snd.fst.dist continuous_snd.snd)).inter
        (isClosed_le continuous_snd.norm continuous_const))
  refine isClosed_fst_image_of_compact hC (isCompact_closedBall (0 : ℂ × ℂ) m) ?_
  rintro u ⟨-, -, hm⟩
  exact ⟨mem_univ _, by rwa [Metric.mem_closedBall, dist_zero_right]⟩

theorem sepSet_compl_eq : sepSetᶜ = ⋃ m : ℕ, Prod.fst '' sepPiece m := by
  ext f
  simp only [sepSet, mem_compl_iff, mem_ofPred_eq, not_forall, mem_iUnion, mem_image,
    exists_prop]
  constructor
  · rintro ⟨x, y, h0, hne⟩
    have hd : 0 < dist x y := dist_pos.2 hne
    obtain ⟨m₁, hm₁⟩ := exists_nat_one_div_lt hd
    obtain ⟨m₂, hm₂⟩ := exists_nat_ge ‖(x, y)‖
    refine ⟨max m₁ m₂, (f, (x, y)), ⟨EReal.toENNReal_eq_zero_iff.1 h0, ?_, ?_⟩, rfl⟩
    · refine le_trans ?_ hm₁.le
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right (le_max_left m₁ m₂) 1
    · exact hm₂.trans (by exact_mod_cast le_max_right m₁ m₂)
  · rintro ⟨m, u, ⟨h0, hd, -⟩, rfl⟩
    refine ⟨u.2.1, u.2.2, EReal.toENNReal_eq_zero_iff.2 h0, ?_⟩
    intro he
    have : dist u.2.1 u.2.2 = 0 := by rw [he, dist_self]
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := Nat.one_div_pos_of_nat
    linarith

theorem isMetricLSCFun_iff (f : LSCFun) :
    IsMetricLSCFun f ↔
      (∀ p, 0 ≤ f.1 p) ∧ (∀ x : ℂ, f.1 (x, x) ≤ 0) ∧
        (∀ p, f.1 p.swap ≤ f.1 p) ∧ f ∈ triSet ∧ f ∈ sepSet := by
  constructor
  · rintro ⟨h0, hd, hs, hsym, htri⟩
    refine ⟨h0, fun x => EReal.toENNReal_eq_zero_iff.1 (hd x), ?_, htri, hs⟩
    intro p
    have h := hsym p.2 p.1
    rw [EReal.toENNReal_eq_toENNReal (h0 _) (h0 _)] at h
    exact h.le
  · rintro ⟨h0, hd, hsym, htri, hs⟩
    refine ⟨h0, fun x => EReal.toENNReal_eq_zero_iff.2 (hd x), hs, ?_, htri⟩
    intro x y
    have h1 := hsym (x, y)
    have h2 := hsym (y, x)
    exact congrArg EReal.toENNReal (le_antisymm h2 h1)

 
theorem measurableSet_isMetricLSCFun [MeasurableSpace LSCFun] [BorelSpace LSCFun] :
    MeasurableSet {f : LSCFun | IsMetricLSCFun f} := by
  have hTri : MeasurableSet triSet := by
    rw [← compl_compl triSet, triSet_compl_eq]
    refine MeasurableSet.compl ?_
    refine MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
      MeasurableSet.iUnion fun c => MeasurableSet.iUnion fun _ =>
        MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun m => ?_
    exact (isClosed_fst_image_triPiece a b j m).measurableSet.inter
      (LSCFun.isOpen_setOf_forall_lt (isCompact_ballFamily j) _).measurableSet
  have hSep : MeasurableSet sepSet := by
    rw [← compl_compl sepSet, sepSet_compl_eq]
    exact (MeasurableSet.iUnion fun m =>
      (isClosed_fst_image_sepPiece m).measurableSet).compl
  have heq : {f : LSCFun | IsMetricLSCFun f} =
      {f | ∀ p, 0 ≤ f.1 p} ∩ {f | ∀ x : ℂ, f.1 (x, x) ≤ 0} ∩
        {f | ∀ p, f.1 p.swap ≤ f.1 p} ∩ triSet ∩ sepSet := by
    ext f
    simp only [mem_ofPred_eq, mem_inter_iff, isMetricLSCFun_iff, and_assoc]
  rw [heq]
  exact (((isClosed_nonneg.measurableSet.inter isClosed_diag.measurableSet).inter
    isClosed_symm.measurableSet).inter hTri).inter hSep

 
def metricOfLSCFun (f : LSCFun) (hf : IsMetricLSCFun f) : LSCMetric :=
  ⟨fun p => (f.1 p).toENNReal, hf.2,
    EReal.continuous_toENNReal.comp_lowerSemicontinuous f.2
      (fun _ _ h => EReal.toENNReal_le_toENNReal h)⟩

theorem toLSCFun_metricOfLSCFun (f : LSCFun) (hf : IsMetricLSCFun f) :
    (metricOfLSCFun f hf).toLSCFun = f := by
  apply Subtype.ext
  funext p
  exact EReal.coe_toENNReal (hf.1 p)

theorem isMetricLSCFun_toLSCFun (D : LSCMetric) : IsMetricLSCFun D.toLSCFun := by
  refine ⟨fun p => EReal.coe_ennreal_nonneg _, ?_⟩
  have h : (fun p => (D.toLSCFun.1 p).toENNReal) = fun p => D p := by
    funext p
    exact EReal.toENNReal_coe
  rw [h]
  exact D.2.1

end SupercriticalLQGUniqueness.B2.PfeAxioms
