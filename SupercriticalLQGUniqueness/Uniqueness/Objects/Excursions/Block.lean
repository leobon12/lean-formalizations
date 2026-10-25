import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.T57f
import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.Geom




 




















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

open LQGMetric (DistC addFun)

 

 
def blockShape (T : Objects.CorrectedEvent.TubeData) : Set ℂ :=
  (fun w : ℂ => ((T.rho * T.r : ℝ) : ℂ) * T.orientation * w) '' Objects.CorrectedEvent.blockNorm T

 
def cU (T : Objects.CorrectedEvent.TubeData) : ℂ := ((T.rho * T.r : ℝ) : ℂ) * T.orientation * Objects.CorrectedEvent.uNorm T

 
def cV (T : Objects.CorrectedEvent.TubeData) : ℂ := ((T.rho * T.r : ℝ) : ℂ) * T.orientation * Objects.CorrectedEvent.vNorm T

 
def shieldAt (C : Objects.CorrectedEvent.Constants) (D : LSCMetric) (t : ℝ) : Prop :=
  Objects.CorrectedEvent.around D 0 t (2 * t) < ⊤ ∧
    Objects.CorrectedEvent.around D 0 t (2 * t) ≤ ENNReal.ofReal C.lamConst * Objects.CorrectedEvent.acr D 0 (2 * t) (3 * t)

 
def shield (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (D : LSCMetric) : Prop :=
  ∃ k ∈ Finset.Icc 1 Ksh, shieldAt C D (3 * 8 ^ (Ksh - k) * (T.rho * T.r))

 
def blockRaw (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (Cmid0 : ℝ)
    (D D' : DistC → LSCMetric) (g : DistC) : Prop :=
  (∃ u v : ℂ, ‖u‖ = T.alpha * (T.rho * T.r) ∧ dist u (cU T) < T.blockRadius / 2 ∧
    ‖v‖ = T.rho * T.r ∧ dist v (cV T) < T.blockRadius / 2 ∧
    D' g (u, v) ≤ ENNReal.ofReal Cmid0 * D g (u, v) ∧
    D' g (u, v) < ⊤ ∧
    (∃ (P : ℝ → ℂ) (a b : ℝ), (D' g).IsCurve P a b ∧ P a = u ∧ P b = v ∧
      (∀ t ∈ Icc a b, P t ∈ closure (blockShape T)) ∧ (D' g).len P a b = D' g (u, v)) ∧
    (∃ hu : u ∈ closedBall (cU T) T.blockRadius,
      Objects.Shadow.circleOuter (cU T) T.blockRadius.toNNReal 0
          (sphere (cU T) T.blockRadius \
            Objects.Producer.goodSet (D g) (cU T) u T.blockRadius (C.lamConst * (D' g (u, v)).toReal) hu) ≤
        ENNReal.ofReal (C.lamConst * T.blockRadius / 2)) ∧
    (∃ hv : v ∈ closedBall (cV T) T.blockRadius,
      Objects.Shadow.circleOuter (cV T) T.blockRadius.toNNReal 0
          (sphere (cV T) T.blockRadius \
            Objects.Producer.goodSet (D g) (cV T) v T.blockRadius (C.lamConst * (D' g (u, v)).toReal) hv) ≤
        ENNReal.ofReal (C.lamConst * T.blockRadius / 2))) ∧
  shield C T Ksh (D g)

 
def blockEvent (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (Cmid0 : ℝ)
    (D D' : DistC → LSCMetric) (z : ℂ) (g : DistC) : Prop :=
  blockRaw C T Ksh Cmid0 D D' (Objects.Producer.normTranslate z g)

 

section Geometry

variable {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData}

theorem innerCenter_eq_add (k : Fin T.K) : Objects.CorrectedEvent.innerCenter T k = cU T + Objects.CorrectedEvent.site T k := by
  simp only [Objects.CorrectedEvent.innerCenter, Objects.CorrectedEvent.moduleMap, cU]
  ring

theorem outerCenter_eq_add (k : Fin T.K) : Objects.CorrectedEvent.outerCenter T k = cV T + Objects.CorrectedEvent.site T k := by
  simp only [Objects.CorrectedEvent.outerCenter, Objects.CorrectedEvent.moduleMap, cV]
  ring

 
theorem image_blockShape (k : Fin T.K) :
    (fun x => x + Objects.CorrectedEvent.site T k) '' blockShape T = Objects.CorrectedEvent.block T k := by
  simp only [blockShape, Objects.CorrectedEvent.block, image_image]
  congr 1
  funext w
  rw [Objects.CorrectedEvent.moduleMap]
  ring

theorem blockShape_subset (hn : ‖T.orientation‖ = 1) (hρr : 0 < T.rho * T.r) :
    blockShape T ⊆ closedBall 0 (T.rho * T.r) := by
  rintro _ ⟨w, hw, rfl⟩
  rw [mem_closedBall, dist_zero_right, norm_mul, norm_mul, Complex.norm_real, hn, mul_one,
    Real.norm_eq_abs, abs_of_pos hρr]
  have := hw.2.1
  nlinarith [norm_nonneg w]

 
theorem mem_closure_tubeSet (k : Fin T.K) {x : ℂ} (hx : x ∈ closure (blockShape T)) :
    x + Objects.CorrectedEvent.site T k ∈ closure (Objects.CorrectedEvent.tubeSet T) := by
  have h1 : x + Objects.CorrectedEvent.site T k ∈ closure (Objects.CorrectedEvent.block T k) := by
    rw [← image_blockShape k]
    exact image_closure_subset_closure_image (continuous_id.add continuous_const) ⟨x, hx, rfl⟩
  refine closure_mono (fun y hy => ?_) h1
  exact mem_iUnion.2 ⟨k, Or.inl (Or.inl (Or.inl hy))⟩

 
theorem mem_ann_of_closure (hData : Objects.CorrectedEvent.DataMatch C T) (hlam : C.lamConst ≤ 1 / 48) (k : Fin T.K)
    {x : ℂ} (hx : x ∈ closure (blockShape T)) : x + Objects.CorrectedEvent.site T k ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r) := by
  obtain ⟨hr, hρ, -, -, -, -, hn4, -⟩ := hData
  have hrp := C.rPos
  have hρp := C.rhoPos
  have hρ1 := Objects.Producer.rho_lt_of_constants C hlam
  have hρr : 0 < T.rho * T.r := by rw [hρ, hr]; exact mul_pos hρp hrp
  have hxle : ‖x‖ ≤ T.rho * T.r := by
    have := closure_minimal (blockShape_subset (Objects.Producer.norm_orientation hn4) hρr) isClosed_closedBall hx
    rwa [mem_closedBall, dist_zero_right] at this
  have hsite := Objects.Producer.norm_site T (hr ▸ hrp) k
  rw [hr] at hsite
  rw [hρ, hr] at hxle
  have hρr' : C.ρ * C.r < C.r / 64 := by nlinarith
  have h1 := norm_sub_norm_le (Objects.CorrectedEvent.site T k) (-x)
  rw [sub_neg_eq_add, add_comm, norm_neg] at h1
  have h2 := norm_add_le x (Objects.CorrectedEvent.site T k)
  show C.r < dist (x + Objects.CorrectedEvent.site T k) 0 ∧ dist (x + Objects.CorrectedEvent.site T k) 0 < 4 * C.r
  rw [dist_zero_right]
  constructor <;> linarith

end Geometry

 

theorem circleOuter_translate (c z : ℂ) (R : NNReal) (θ₀ : ℝ) (S : Set ℂ) :
    Objects.Shadow.circleOuter (c + z) R θ₀ {x | x - z ∈ S} = Objects.Shadow.circleOuter c R θ₀ S := by
  have e : ∀ w : ℂ, c + z + w - z = c + w := fun w => by ring
  unfold Objects.Shadow.circleOuter
  congr 2
  ext θ
  constructor
  · rintro ⟨h1, h2⟩
    have h2' : c + z + (R : ℂ) * Complex.exp (θ * Complex.I) - z ∈ S := h2
    exact ⟨h1, by rwa [e] at h2'⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    show c + z + (R : ℂ) * Complex.exp (θ * Complex.I) - z ∈ S
    rwa [e]

 

section Content

variable {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData}

 

theorem bad_transport {D E : LSCMetric} {κ : ℝ} (hκ : 0 < κ) {z : ℂ}
    (hE : ∀ a b : ℂ, E (a, b) = ENNReal.ofReal κ * D (a + z, b + z)) {c u : ℂ} {s B : ℝ}
    (hu : u ∈ closedBall c s) (hu' : u + z ∈ closedBall (c + z) s) (R : NNReal) :
    Objects.Shadow.circleOuter (c + z) R 0 (sphere (c + z) s \ Objects.Producer.goodSet D (c + z) (u + z) s B hu') ≤
      Objects.Shadow.circleOuter c R 0 (sphere c s \ Objects.Producer.goodSet E c u s (κ * B) hu) := by
  rw [← circleOuter_translate c z]
  refine Objects.Shadow.circleOuter_mono (fun x hx => ?_)
  obtain ⟨hxs, hxg⟩ := hx
  have hxs' : x - z ∈ sphere c s := by
    rw [mem_sphere] at hxs ⊢
    rw [← hxs, dist_eq_norm, dist_eq_norm]
    congr 1
    ring
  refine ⟨hxs', fun hg => hxg ⟨hxs, ?_⟩⟩
  obtain ⟨-, hxB, hint⟩ := hg
  have hxB' : x ∈ closedBall (c + z) s := sphere_subset_closedBall hxs
  refine ⟨hxB', ?_⟩
  have hY : ∀ w : ℂ, w ∈ closedBall (c + z) s ↔ w - z ∈ closedBall c s := by
    intro w
    rw [mem_closedBall, mem_closedBall, dist_eq_norm, dist_eq_norm]
    rw [show w - (c + z) = w - z - c by ring]
  have hsh := Objects.Producer.internal_shift hκ hE hY hxB hu hxB' hu' (sub_add_cancel x z).symm rfl
  rw [hsh] at hint
  have hk0 : ENNReal.ofReal κ ≠ 0 := by simpa using hκ
  rw [ENNReal.ofReal_mul hκ.le] at hint
  exact (ENNReal.mul_le_mul_iff_right hk0 ENNReal.ofReal_ne_top).1 hint

 

theorem block_content_gen {Ksh : ℕ} {Cmid0 : ℝ} {D D' : DistC → LSCMetric} {g : DistC}
    {Wc : Set ℂ} {Cc : Set (Set.Ioi (0 : ℝ) × ℂ)} (hgood : Objects.Producer.LocalGood C.ξ D D' Wc Cc g) {z : ℂ}
    (hz : z ∈ Wc) (hF : blockEvent C T Ksh Cmid0 D D' z g) (hs0 : 0 ≤ T.blockRadius)
    (hne : T.alpha * (T.rho * T.r) ≠ T.rho * T.r) {g₀ : C(ℂ, ℝ)}
    (hg₀ : ∀ x, 0 ≤ g₀ x ∧ g₀ x ≤ C.A_max)
    (hcl_ann : ∀ x ∈ closure (blockShape T), x + z ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r))
    (hcl_max : ∀ x ∈ closure (blockShape T), g₀ (x + z) = C.A_max)
    {cin cout : ℂ} (hcin : cin = cU T + z) (hcout : cout = cV T + z) :
    ∃ (u v : ℂ) (dt : ℝ) (hu : u ∈ closedBall cin T.blockRadius)
      (hv : v ∈ closedBall cout T.blockRadius),
      dist u cin < T.blockRadius / 2 ∧ dist v cout < T.blockRadius / 2 ∧
      0 < dt ∧ D' g (u, v) = ENNReal.ofReal dt ∧
      ENNReal.ofReal dt ≤ ENNReal.ofReal Cmid0 * D g (u, v) ∧
      (∀ (hu' : u ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (hv' : v ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)),
        (D' (addFun g (-g₀))).internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨u, hu'⟩, ⟨v, hv'⟩) ≤
          ENNReal.ofReal (Real.exp (-C.ξ * C.A_max) * dt)) ∧
      Objects.Shadow.circleOuter cin ⟨T.blockRadius, hs0⟩ 0
          (sphere cin T.blockRadius \
            Objects.Producer.goodSet (D g) cin u T.blockRadius (C.lamConst * dt) hu) ≤
        ENNReal.ofReal (C.lamConst * T.blockRadius / 2) ∧
      Objects.Shadow.circleOuter cout ⟨T.blockRadius, hs0⟩ 0
          (sphere cout T.blockRadius \
            Objects.Producer.goodSet (D g) cout v T.blockRadius (C.lamConst * dt) hv) ≤
        ENNReal.ofReal (C.lamConst * T.blockRadius / 2) := by
  subst hcin hcout
  obtain ⟨⟨u', v', hu'n, hu'd, hv'n, hv'd, hF1, hfin, ⟨P', a, b, hP', hPa, hPb, hPcl, hPlen⟩,
    ⟨hu'm, hF3u⟩, ⟨hv'm, hF3v⟩⟩, -⟩ := hF
  
  have hκ : 0 < Real.exp (C.ξ * -(LQGMetric.circleAvg g 1 z)) := Real.exp_pos _
  have hD := Objects.Producer.tlc_metric hgood hz
  have hD' := Objects.Producer.tlc_metric' hgood hz
  generalize Real.exp (C.ξ * -(LQGMetric.circleAvg g 1 z)) = κ at hκ hD hD'
  have hκ0 : ENNReal.ofReal κ ≠ 0 := by simpa using hκ
  
  have hdist : ∀ p c : ℂ, dist (p + z) (c + z) = dist p c := fun p c => dist_add_right p c z
  have hu_near : dist (u' + z) (cU T + z) < T.blockRadius / 2 := by rw [hdist]; exact hu'd
  have hv_near : dist (v' + z) (cV T + z) < T.blockRadius / 2 := by rw [hdist]; exact hv'd
  have hu_mem : u' + z ∈ closedBall (cU T + z) T.blockRadius := by
    rw [mem_closedBall]; linarith
  have hv_mem : v' + z ∈ closedBall (cV T + z) T.blockRadius := by
    rw [mem_closedBall]; linarith
  have hDuv : D' (Objects.Producer.normTranslate z g) (u', v') = ENNReal.ofReal κ * D' g (u' + z, v' + z) :=
    hD' u' v'
  have hfin' : D' g (u' + z, v' + z) < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (by rw [← hDuv]; exact hfin.ne) hκ0
  have huv : u' + z ≠ v' + z := by
    intro h
    have h1 : u' = v' := add_right_cancel h
    rw [h1, hv'n] at hu'n
    exact hne hu'n.symm
  have hpos0 : D' g (u' + z, v' + z) ≠ 0 := fun h0 => huv ((D' g).isExtMetric.2.1 _ _ h0)
  obtain ⟨dt, hdt⟩ : ∃ dt : ℝ, D' g (u' + z, v' + z) = ENNReal.ofReal dt :=
    ⟨_, (ENNReal.ofReal_toReal hfin'.ne).symm⟩
  have hdt_pos : 0 < dt := ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 (hdt ▸ hpos0))
  have hdt' : (D' (Objects.Producer.normTranslate z g) (u', v')).toReal = κ * dt := by
    rw [hDuv, hdt, ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ.le, ENNReal.toReal_ofReal hdt_pos.le]
  
  have hratio : ENNReal.ofReal dt ≤ ENNReal.ofReal Cmid0 * D g (u' + z, v' + z) := by
    rw [← hdt]
    rw [hDuv, hD u' v', mul_left_comm] at hF1
    exact (ENNReal.mul_le_mul_iff_right hκ0 ENNReal.ofReal_ne_top).1 hF1
  
  have hPsub : (fun t => (fun s => P' s + z) t - z) = P' :=
    funext fun t => by simp only [add_sub_cancel_right]
  have hPc : (D' g).IsCurve (fun s => P' s + z) a b := by
    rw [← Objects.Producer.isCurve_sub_iff hκ hD' _ a b, hPsub]
    exact hP'
  have hPlen' : (D' g).len (fun s => P' s + z) a b = ENNReal.ofReal dt := by
    have h1 := Objects.Producer.len_sub hD' (fun s => P' s + z) a b
    rw [hPsub, hPlen, hDuv] at h1
    rw [← hdt]
    exact ((ENNReal.mul_right_inj hκ0 ENNReal.ofReal_ne_top).1 h1).symm
  have hgood' := hgood.2.1
  have hforget' : Continuous (BiLipschitz.Barrier.forget (D' g)) :=
    BiLipschitz.Barrier.continuous_forget_of_barrier _ hgood'.2 hgood'.1.1
  have hWeyl' : ∀ x y : ℂ, D' (addFun g (-g₀)) (x, y) = weylScale C.ξ (-g₀) (D' g) (x, y) :=
    fun x y => (congrFun (hgood'.1.2 (-g₀)) (x, y)).symm
  have hPb' : (D' (addFun g (-g₀))).IsCurve (fun s => P' s + z) a b :=
    Objects.Splice.bumped_curve_transfer C (D' g) _ g₀ hforget' hWeyl' hg₀ hgood'.1.1 hPc
  have hcost : ∀ (hu' : u' + z ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (hv' : v' + z ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)),
      (D' (addFun g (-g₀))).internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨u' + z, hu'⟩, ⟨v' + z, hv'⟩) ≤
        ENNReal.ofReal (Real.exp (-C.ξ * C.A_max) * dt) := by
    intro hu' hv'
    have h1 := Objects.Producer.internal_le_len_pts (D' (addFun g (-g₀))) hPb'
      (fun t ht => hcl_ann _ (hPcl t ht)) hu' hv' (by simp only [hPa]) (by simp only [hPb])
    have h2 := Objects.Producer.bumped_len_max_trace C (D' g) _ g₀ hforget' hWeyl' hPc
      (fun t ht => hcl_max _ (hPcl t ht))
    rw [hPlen', ← ENNReal.ofReal_mul (Real.exp_pos _).le] at h2
    exact h1.trans h2
  
  have hR : T.blockRadius.toNNReal = ⟨T.blockRadius, hs0⟩ := Real.toNNReal_of_nonneg hs0
  have hbad : ∀ (c₀ w₀ : ℂ) (hw₀ : w₀ ∈ closedBall c₀ T.blockRadius)
      (hw : w₀ + z ∈ closedBall (c₀ + z) T.blockRadius),
      Objects.Shadow.circleOuter c₀ T.blockRadius.toNNReal 0
          (sphere c₀ T.blockRadius \ Objects.Producer.goodSet (D (Objects.Producer.normTranslate z g)) c₀ w₀ T.blockRadius
            (C.lamConst * (D' (Objects.Producer.normTranslate z g) (u', v')).toReal) hw₀) ≤
        ENNReal.ofReal (C.lamConst * T.blockRadius / 2) →
      Objects.Shadow.circleOuter (c₀ + z) ⟨T.blockRadius, hs0⟩ 0
          (sphere (c₀ + z) T.blockRadius \
            Objects.Producer.goodSet (D g) (c₀ + z) (w₀ + z) T.blockRadius (C.lamConst * dt) hw) ≤
        ENNReal.ofReal (C.lamConst * T.blockRadius / 2) := by
    intro c₀ w₀ hw₀ hw h
    rw [hR, hdt', show C.lamConst * (κ * dt) = κ * (C.lamConst * dt) by ring] at h
    exact (bad_transport hκ hD hw₀ hw _).trans h
  exact ⟨u' + z, v' + z, dt, hu_mem, hv_mem, hu_near, hv_near, hdt_pos, hdt, hratio, hcost,
    hbad _ _ hu'm hu_mem hF3u, hbad _ _ hv'm hv_mem hF3v⟩

 

theorem block_content (hData : Objects.CorrectedEvent.DataMatch C T) (hE : C.A_endpt ≤ 1) (hlam : C.lamConst ≤ 1 / 48)
    {Ksh : ℕ} {Cmid0 : ℝ} {D D' : DistC → LSCMetric} {g : DistC} {Wc : Set ℂ}
    {Cc : Set (Set.Ioi (0 : ℝ) × ℂ)} (hgood : Objects.Producer.LocalGood C.ξ D D' Wc Cc g) (k : Fin T.K)
    (hk : Objects.CorrectedEvent.site T k ∈ Wc) (hF : blockEvent C T Ksh Cmid0 D D' (Objects.CorrectedEvent.site T k) g)
    {g₀ : C(ℂ, ℝ)} (hg₀ : ∀ x, 0 ≤ g₀ x ∧ g₀ x ≤ C.A_max)
    (hg₀max : ∀ x ∈ closure (Objects.CorrectedEvent.tubeSet T), g₀ x = C.A_max) :
    ∃ (u v : ℂ) (dt : ℝ) (hu : u ∈ closedBall (Objects.CorrectedEvent.innerCenter T k) T.blockRadius)
      (hv : v ∈ closedBall (Objects.CorrectedEvent.outerCenter T k) T.blockRadius),
      dist u (Objects.CorrectedEvent.innerCenter T k) < T.blockRadius / 2 ∧
      dist v (Objects.CorrectedEvent.outerCenter T k) < T.blockRadius / 2 ∧
      0 < dt ∧ D' g (u, v) = ENNReal.ofReal dt ∧
      ENNReal.ofReal dt ≤ ENNReal.ofReal Cmid0 * D g (u, v) ∧
      (∀ (hu' : u ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (hv' : v ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)),
        (D' (addFun g (-g₀))).internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨u, hu'⟩, ⟨v, hv'⟩) ≤
          ENNReal.ofReal (Real.exp (-C.ξ * C.A_max) * dt)) ∧
      Objects.Shadow.circleOuter (Objects.CorrectedEvent.innerCenter T k)
          ⟨T.blockRadius, (Objects.Producer.blockRadius_bounds C T hData hE).1.le⟩ 0
          (sphere (Objects.CorrectedEvent.innerCenter T k) T.blockRadius \
            Objects.Producer.goodSet (D g) (Objects.CorrectedEvent.innerCenter T k) u T.blockRadius (C.lamConst * dt) hu) ≤
        ENNReal.ofReal (C.lamConst * T.blockRadius / 2) ∧
      Objects.Shadow.circleOuter (Objects.CorrectedEvent.outerCenter T k)
          ⟨T.blockRadius, (Objects.Producer.blockRadius_bounds C T hData hE).1.le⟩ 0
          (sphere (Objects.CorrectedEvent.outerCenter T k) T.blockRadius \
            Objects.Producer.goodSet (D g) (Objects.CorrectedEvent.outerCenter T k) v T.blockRadius (C.lamConst * dt) hv) ≤
        ENNReal.ofReal (C.lamConst * T.blockRadius / 2) := by
  have hr : T.r = C.r := hData.1
  have hρ : T.rho = C.ρ := hData.2.1
  have hα : T.alpha = C.K_ann := hData.2.2.2.2.1
  have hne : T.alpha * (T.rho * T.r) ≠ T.rho * T.r := by
    have hK1 := Objects.Producer.kann_lt_one C
    have hρr : 0 < C.ρ * C.r := mul_pos C.rhoPos C.rPos
    rw [hα, hρ, hr]
    intro h
    nlinarith
  exact block_content_gen hgood hk hF (Objects.Producer.blockRadius_bounds C T hData hE).1.le hne hg₀
    (fun x hx => mem_ann_of_closure hData hlam k hx)
    (fun x hx => hg₀max _ (mem_closure_tubeSet k hx)) (innerCenter_eq_add k) (outerCenter_eq_add k)

end Content

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
