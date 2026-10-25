import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.Event
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.InterfaceV2
import LQGMetric.Papers.GM.S2.TightLaw




 




















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

open LQGMetric (DistC TestC addConst addFun ofCont)
open LQGMetric.MetricGeometry (eVariationOn_eq_mul_of_edist hasUnitSpeedOn_rescale curveLength
  curveLength_comp_of_continuousOn_monotoneOn)

 

 
theorem internal_le_of_curve {D : LSCMetric} {Y : Set ℂ} {x y : ℂ} (hx : x ∈ Y) (hy : y ∈ Y)
    {P : ℝ → ℂ} {a b : ℝ} (hc : D.IsCurve P a b) (hin : ∀ t ∈ Icc a b, P t ∈ Y) (h0 : P a = x)
    (h1 : P b = y) : D.internal Y (⟨x, hx⟩, ⟨y, hy⟩) ≤ D.len P a b :=
  iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <| iInf_le_of_le hc <|
    iInf_le_of_le hin <| iInf_le_of_le h0 <| iInf_le _ h1

 

section shift

variable {D E : LSCMetric} {k : ℝ} {z : ℂ}

 
theorem shift_apply (hE : ∀ a b : ℂ, E (a, b) = ENNReal.ofReal k * D (a + z, b + z)) (x y : ℂ) :
    E (x - z, y - z) = ENNReal.ofReal k * D (x, y) := by
  rw [hE, sub_add_cancel, sub_add_cancel]

 
theorem lipschitz_sub (hE : ∀ a b : ℂ, E (a, b) = ENNReal.ofReal k * D (a + z, b + z)) :
    LipschitzWith (Real.toNNReal k) (fun x : D.Space => E.pt (BiLipschitz.Barrier.forget D x - z)) := by
  intro x y
  change E (BiLipschitz.Barrier.forget D x - z, BiLipschitz.Barrier.forget D y - z) ≤
    ENNReal.ofReal k * D (BiLipschitz.Barrier.forget D x, BiLipschitz.Barrier.forget D y)
  rw [shift_apply hE]

 
theorem lipschitz_add (hk : 0 < k)
    (hE : ∀ a b : ℂ, E (a, b) = ENNReal.ofReal k * D (a + z, b + z)) :
    LipschitzWith (Real.toNNReal k⁻¹) (fun x : E.Space => D.pt (BiLipschitz.Barrier.forget E x + z)) := by
  intro x y
  change D (BiLipschitz.Barrier.forget E x + z, BiLipschitz.Barrier.forget E y + z) ≤
    ENNReal.ofReal k⁻¹ * E (BiLipschitz.Barrier.forget E x, BiLipschitz.Barrier.forget E y)
  rw [hE (BiLipschitz.Barrier.forget E x) (BiLipschitz.Barrier.forget E y), ← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.2 hk).le, inv_mul_cancel₀ hk.ne',
    ENNReal.ofReal_one, one_mul]

theorem isCurve_sub_iff (hk : 0 < k)
    (hE : ∀ a b : ℂ, E (a, b) = ENNReal.ofReal k * D (a + z, b + z)) (P : ℝ → ℂ) (a b : ℝ) :
    E.IsCurve (fun t => P t - z) a b ↔ D.IsCurve P a b := by
  constructor
  · rintro ⟨hab, hc⟩
    refine ⟨hab, ((lipschitz_add hk hE).continuous.comp_continuousOn hc).congr fun t _ => ?_⟩
    show P t = P t - z + z
    rw [sub_add_cancel]
  · rintro ⟨hab, hc⟩
    exact ⟨hab, (lipschitz_sub hE).continuous.comp_continuousOn hc⟩

theorem len_sub (hE : ∀ a b : ℂ, E (a, b) = ENNReal.ofReal k * D (a + z, b + z))
    (P : ℝ → ℂ) (a b : ℝ) : E.len (fun t => P t - z) a b = ENNReal.ofReal k * D.len P a b :=
  eVariationOn_eq_mul_of_edist (fun s t => shift_apply hE (P s) (P t)) _

 
theorem internal_shift (hk : 0 < k)
    (hE : ∀ a b : ℂ, E (a, b) = ENNReal.ofReal k * D (a + z, b + z)) {Y Y' : Set ℂ}
    (hY : ∀ w : ℂ, w ∈ Y' ↔ w - z ∈ Y) {x y x' y' : ℂ} (hx : x ∈ Y) (hy : y ∈ Y) (hx' : x' ∈ Y')
    (hy' : y' ∈ Y') (hxx : x' = x + z) (hyy : y' = y + z) :
    E.internal Y (⟨x, hx⟩, ⟨y, hy⟩) = ENNReal.ofReal k * D.internal Y' (⟨x', hx'⟩, ⟨y', hy'⟩) := by
  subst hxx hyy
  have hk0 : ENNReal.ofReal k ≠ 0 := by simpa using hk
  apply le_antisymm
  · show _ ≤ ENNReal.ofReal k * ⨅ (P : ℝ → ℂ) (a : ℝ) (b : ℝ) (_ : D.IsCurve P a b)
        (_ : ∀ t ∈ Icc a b, P t ∈ Y') (_ : P a = x + z) (_ : P b = y + z), D.len P a b
    simp_rw [ENNReal.mul_iInf_of_ne hk0 ENNReal.ofReal_ne_top]
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hc => le_iInf fun hin =>
      le_iInf fun h0 => le_iInf fun h1 => ?_
    rw [← len_sub hE]
    refine internal_le_of_curve hx hy ((isCurve_sub_iff hk hE P a b).2 hc)
      (fun t ht => (hY _).1 (hin t ht)) ?_ ?_
    · show P a - z = x
      rw [h0, add_sub_cancel_right]
    · show P b - z = y
      rw [h1, add_sub_cancel_right]
  · refine le_iInf fun Q => le_iInf fun a => le_iInf fun b => le_iInf fun hc => le_iInf fun hin =>
      le_iInf fun h0 => le_iInf fun h1 => ?_
    have hQ : (fun t => (Q t + z) - z) = Q := funext fun t => add_sub_cancel_right (Q t) z
    have hc' : D.IsCurve (fun t => Q t + z) a b :=
      (isCurve_sub_iff hk hE (fun t => Q t + z) a b).1 (by rw [hQ]; exact hc)
    have hlen : E.len Q a b = ENNReal.ofReal k * D.len (fun t => Q t + z) a b := by
      rw [← len_sub hE, hQ]
    rw [hlen]
    gcongr
    refine internal_le_of_curve hx' hy' hc' (fun t ht => (hY _).2 ?_) ?_ ?_
    · rw [add_sub_cancel_right]; exact hin t ht
    · show Q a + z = x + z
      rw [show Q a = x from h0]
    · show Q b + z = y + z
      rw [show Q b = y from h1]

 

theorem continuous_forget_shift (hk : 0 < k)
    (hE : ∀ a b : ℂ, E (a, b) = ENNReal.ofReal k * D (a + z, b + z))
    (hD : Continuous (BiLipschitz.Barrier.forget D)) : Continuous (BiLipschitz.Barrier.forget E) := by
  have h := (continuous_sub_right z).comp (hD.comp (lipschitz_add hk hE).continuous)
  refine h.congr fun x => ?_
  show BiLipschitz.Barrier.forget E x + z - z = BiLipschitz.Barrier.forget E x
  rw [add_sub_cancel_right]

 
def shiftCurve (k : ℝ) (z : ℂ) (P : ℝ → ℂ) : ℝ → ℂ := fun t => P (t / k) - z

theorem shiftCurve_mul (hk : 0 < k) (P : ℝ → ℂ) (t : ℝ) :
    shiftCurve k z P (k * t) = P t - z := by
  simp only [shiftCurve, mul_div_cancel_left₀ t hk.ne']

theorem hasUnitSpeedOn_shiftCurve (hk : 0 < k)
    (hE : ∀ a b : ℂ, E (a, b) = ENNReal.ofReal k * D (a + z, b + z)) {P : ℝ → ℂ} {T : ℝ}
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T)) :
    HasUnitSpeedOn (E.pt ∘ shiftCurve k z P) (Icc 0 (k * T)) :=
  hasUnitSpeedOn_rescale (F := E.pt ∘ fun t => P t - z) (G := D.pt ∘ P) hk
    (fun s t => by
      show E (P s - z, P t - z) = ENNReal.ofReal k * D (P s, P t)
      exact shift_apply hE (P s) (P t)) hu

theorem isCurve_shiftCurve (hk : 0 < k)
    (hE : ∀ a b : ℂ, E (a, b) = ENNReal.ofReal k * D (a + z, b + z)) {P : ℝ → ℂ} {T : ℝ}
    (hc : D.IsCurve P 0 T) : E.IsCurve (shiftCurve k z P) 0 (k * T) := by
  refine ⟨mul_nonneg hk.le hc.1, ?_⟩
  have h1 : ContinuousOn (E.pt ∘ fun t => P t - z) (Icc 0 T) :=
    ((isCurve_sub_iff hk hE P 0 T).2 hc).2
  have hmaps : MapsTo (fun t : ℝ => t / k) (Icc 0 (k * T)) (Icc 0 T) := fun t ht =>
    ⟨div_nonneg ht.1 hk.le, (div_le_iff₀ hk).2 (by rw [mul_comm]; exact ht.2)⟩
  exact h1.comp (by fun_prop) hmaps

theorem len_shiftCurve (hk : 0 < k)
    (hE : ∀ a b : ℂ, E (a, b) = ENNReal.ofReal k * D (a + z, b + z)) (P : ℝ → ℂ) {a b : ℝ}
    (hab : a ≤ b) :
    E.len (shiftCurve k z P) (k * a) (k * b) = ENNReal.ofReal k * D.len P a b := by
  have h1 := curveLength_comp_of_continuousOn_monotoneOn (E.pt ∘ fun t => P t - z)
    (φ := fun t : ℝ => t / k) (mul_le_mul_of_nonneg_left hab hk.le) (by fun_prop)
    (fun x _ y _ hxy => div_le_div_of_nonneg_right hxy hk.le)
  rw [mul_div_cancel_left₀ a hk.ne', mul_div_cancel_left₀ b hk.ne'] at h1
  rw [← len_sub hE]
  exact h1

 

theorem bumpedGeodesic_shift (hk : 0 < k)
    (hE : ∀ a b : ℂ, E (a, b) = ENNReal.ofReal k * D (a + z, b + z)) {P : ℝ → ℂ} {T : ℝ}
    (h : EndSaving.Interfaces.BumpedGeodesic D P T) : EndSaving.Interfaces.BumpedGeodesic E (shiftCurve k z P) (k * T) := by
  obtain ⟨hc, hu, hlen, hfin⟩ := h
  have e0 : shiftCurve k z P 0 = P 0 - z := by simp only [shiftCurve, zero_div]
  have eT : shiftCurve k z P (k * T) = P T - z := shiftCurve_mul hk P T
  refine ⟨isCurve_shiftCurve hk hE hc, hasUnitSpeedOn_shiftCurve hk hE hu, ?_, ?_⟩
  · have h1 := len_shiftCurve hk hE P hc.1
    rw [mul_zero] at h1
    rw [h1, hlen, e0, eT, shift_apply hE]
  · rw [e0, eT, shift_apply hE]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

 
theorem excursion_shift (hk : 0 < k) {P : ℝ → ℂ} {T : ℝ} {O O₀ : Set ℂ}
    {V V₀ : TopologicalSpace.Opens ℂ} (hO : ∀ w : ℂ, w ∈ O₀ ↔ w + z ∈ O)
    (hV : ∀ w : ℂ, w ∈ (V₀ : Set ℂ) ↔ w + z ∈ (V : Set ℂ)) {τ' τ σ σ' : ℝ}
    (h : EndSaving.Interfaces.Excursion P T O V τ' τ σ σ') :
    EndSaving.Interfaces.Excursion (shiftCurve k z P) (k * T) O₀ V₀ (k * τ') (k * τ) (k * σ) (k * σ') := by
  have hO' : O₀ = (Homeomorph.addRight z) ⁻¹' O := Set.ext fun w => hO w
  have hV' : (V₀ : Set ℂ) = (Homeomorph.addRight z) ⁻¹' (V : Set ℂ) := Set.ext fun w => hV w
  have hfr : ∀ w, w ∈ frontier O₀ ↔ w + z ∈ frontier O := by
    intro w
    rw [hO', ← Homeomorph.preimage_frontier]
    rfl
  have hcl : ∀ w, w ∈ closure (V₀ : Set ℂ) ↔ w + z ∈ closure (V : Set ℂ) := by
    intro w
    rw [hV', ← Homeomorph.preimage_closure]
    rfl
  have ev : ∀ t, shiftCurve k z P (k * t) = P t - z := shiftCurve_mul hk P
  have es : ∀ t, P t - z + z = P t := fun t => sub_add_cancel _ _
  have hdiv : ∀ {a b t : ℝ}, t ∈ Ioo (k * a) (k * b) → t / k ∈ Ioo a b := fun {a b t} ht =>
    ⟨(lt_div_iff₀ hk).2 (by rw [mul_comm]; exact ht.1),
      (div_lt_iff₀ hk).2 (by rw [mul_comm]; exact ht.2)⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  refine ⟨mul_nonneg hk.le h1, mul_le_mul_of_nonneg_left h2 hk.le,
    mul_le_mul_of_nonneg_left h3 hk.le, mul_le_mul_of_nonneg_left h4 hk.le,
    mul_le_mul_of_nonneg_left h5 hk.le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ev, hfr, es]; exact h6
  · rw [ev, hfr, es]; exact h7
  · intro t ht
    rw [hO]
    exact (es _).symm ▸ h8 _ (hdiv ht)
  · rw [ev, hcl, es]; exact h9
  · rw [ev, hcl, es]; exact h10
  · intro t ht
    rw [hcl]
    exact (es _).symm ▸ h11 _ (hdiv ht)
  · intro t ht
    rw [hcl]
    exact (es _).symm ▸ h12 _ (hdiv ht)

 
theorem weylScale_shift_le (ξ : ℝ) (hk : 0 < k)
    (hE : ∀ a b : ℂ, E (a, b) = ENNReal.ofReal k * D (a + z, b + z)) {g g' : C(ℂ, ℝ)}
    (hg : ∀ x, g' x = g (x + z)) (a b : ℂ) :
    weylScale ξ g' E (a, b) ≤ ENNReal.ofReal k * weylScale ξ g D (a + z, b + z) := by
  have hk0 : ENNReal.ofReal k ≠ 0 := by simpa using hk
  rw [mul_comm, ← ENNReal.div_le_iff hk0 ENNReal.ofReal_ne_top]
  show _ ≤ ⨅ (P : ℝ → ℂ) (L : ℝ) (_ : D.IsCurve P 0 L)
      (_ : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) (_ : P 0 = a + z) (_ : P L = b + z),
      ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g (P t)))
  refine le_iInf fun P => le_iInf fun L => le_iInf fun hc => le_iInf fun hu =>
    le_iInf fun h0 => le_iInf fun h1 => ?_
  rw [ENNReal.div_le_iff hk0 ENNReal.ofReal_ne_top, mul_comm]
  have hL : 0 ≤ L := hc.1
  have hle : weylScale ξ g' E (a, b) ≤
      ∫⁻ s in Icc 0 (k * L), ENNReal.ofReal (Real.exp (ξ * g' (shiftCurve k z P s))) := by
    refine iInf_le_of_le (shiftCurve k z P) <| iInf_le_of_le (k * L) <|
      iInf_le_of_le (isCurve_shiftCurve hk hE hc) <|
      iInf_le_of_le (hasUnitSpeedOn_shiftCurve hk hE hu) <| iInf_le_of_le ?_ <| iInf_le _ ?_
    · show P (0 / k) - z = a
      rw [zero_div, h0, add_sub_cancel_right]
    · show shiftCurve k z P (k * L) = b
      rw [shiftCurve_mul hk, h1, add_sub_cancel_right]
  refine hle.trans_eq ?_
  rw [setLIntegral_congr_fun measurableSet_Icc
    (g := fun s => ENNReal.ofReal (Real.exp (ξ * g (P (s / k)))))
    (fun s _ => by rw [hg]; simp only [shiftCurve, sub_add_cancel])]
  have himg : (fun x => k * x) '' Icc 0 L = Icc 0 (k * L) := by
    rw [image_mul_left_Icc hk.le hL, mul_zero]
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc (f' := fun _ => k)
    (fun x _ => by simpa using ((hasDerivAt_id x).const_mul k).hasDerivWithinAt)
    (fun x _ y _ hxy => mul_left_cancel₀ hk.ne' hxy)]
  rw [setLIntegral_congr_fun measurableSet_Icc
    (g := fun x => ENNReal.ofReal |k| * ENNReal.ofReal (Real.exp (ξ * g (P x))))
    (fun x _ => by simp [hk.ne'])]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, abs_of_pos hk]

 
theorem weylScale_shift (ξ : ℝ) (hk : 0 < k)
    (hE : ∀ a b : ℂ, E (a, b) = ENNReal.ofReal k * D (a + z, b + z)) {g g' : C(ℂ, ℝ)}
    (hg : ∀ x, g' x = g (x + z)) (a b : ℂ) :
    weylScale ξ g' E (a, b) = ENNReal.ofReal k * weylScale ξ g D (a + z, b + z) := by
  refine le_antisymm (weylScale_shift_le ξ hk hE hg a b) ?_
  have hE' : ∀ a b : ℂ, D (a, b) = ENNReal.ofReal k⁻¹ * E (a + -z, b + -z) := by
    intro a b
    rw [hE, neg_add_cancel_right, neg_add_cancel_right, ← mul_assoc,
      ← ENNReal.ofReal_mul (inv_pos.2 hk).le, inv_mul_cancel₀ hk.ne', ENNReal.ofReal_one, one_mul]
  have hg' : ∀ x, g x = g' (x + -z) := fun x => by rw [hg, neg_add_cancel_right]
  have h2 := weylScale_shift_le (D := E) (E := D) ξ (inv_pos.2 hk) hE' hg' (a + z) (b + z)
  rw [add_neg_cancel_right, add_neg_cancel_right] at h2
  calc ENNReal.ofReal k * weylScale ξ g D (a + z, b + z)
      ≤ ENNReal.ofReal k * (ENNReal.ofReal k⁻¹ * weylScale ξ g' E (a, b)) := by gcongr
    _ = weylScale ξ g' E (a, b) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hk.le, mul_inv_cancel₀ hk.ne', ENNReal.ofReal_one,
          one_mul]

end shift

 

 
theorem isCircleAverage_translateDist (g : DistC) (r : Set.Ioi (0 : ℝ)) (z : ℂ) (c : ℝ) :
    IsCircleAverage (translateDist z g) r 0 c ↔ IsCircleAverage g r z c := by
  unfold IsCircleAverage
  have h : (fun n : ℕ => Real.circleAverage (fun x => (translateDist z g)
      (LQGMetric.bumpTest n x)) 0 (r : ℝ)) =
      fun n : ℕ => Real.circleAverage (fun x => g (LQGMetric.bumpTest n x)) z (r : ℝ) := by
    funext n
    have hfun : (fun x => (translateDist z g) (LQGMetric.bumpTest n x)) =
        fun x => g (LQGMetric.bumpTest n (x + z)) := by
      funext x
      rw [translateDist_eq_affineComp_one, LQGMetric.GFFInv.affineComp_apply,
        LQGMetric.GM.Tight.testAffinePull_one_bumpTest]
      simp
    rw [hfun]
    exact Real.circleAverage_map_add_const (f := fun x => g (LQGMetric.bumpTest n x))
  rw [h]

 
theorem isCircleAverage_normTranslate {u : DistC} {s : Set.Ioi (0 : ℝ)} {z : ℂ} {c : ℝ}
    (h : IsCircleAverage u s z c) :
    IsCircleAverage (normTranslate z u) s 0 (c + -(LQGMetric.circleAvg u 1 z)) :=
  isCircleAverage_addConst ((isCircleAverage_translateDist u s z c).2 h) _

section field

variable {ξ : ℝ} {D D' : DistC → LSCMetric} {Wc : Set ℂ} {Cc : Set (Set.Ioi (0 : ℝ) × ℂ)}
  {u : DistC}

 
theorem LocalGood.weylReg_normTranslate (h : LocalGood ξ D D' Wc Cc u) {z : ℂ} (hz : z ∈ Wc) :
    WeylReg ξ D (normTranslate z u) ∧ WeylReg ξ D' (normTranslate z u) := by
  obtain ⟨h1, h2, -, -⟩ := h.2.2.1 z hz
  exact ⟨h1.addConst _, h2.addConst _⟩

 
theorem tlc_bumped (h : LocalGood ξ D D' Wc Cc u) {z : ℂ} (hz : z ∈ Wc) {g g₀ : C(ℂ, ℝ)}
    (hg : ∀ x, g₀ x = g (x + z)) (a b : ℂ) :
    D (addFun (normTranslate z u) g₀) (a, b) =
      ENNReal.ofReal (Real.exp (ξ * -(LQGMetric.circleAvg u 1 z))) * D (addFun u g) (a + z, b + z) := by
  have hW0 := (h.weylReg_normTranslate hz).1
  change (D (addFun (normTranslate z u) g₀)).1 (a, b) = _ * (D (addFun u g)).1 (a + z, b + z)
  rw [← hW0.2 g₀, ← h.1.1.2 g]
  exact weylScale_shift ξ (Real.exp_pos _) (fun a b => tlc_metric h hz a b) hg a b

 
theorem tlc_bumped' (h : LocalGood ξ D D' Wc Cc u) {z : ℂ} (hz : z ∈ Wc) {g g₀ : C(ℂ, ℝ)}
    (hg : ∀ x, g₀ x = g (x + z)) (a b : ℂ) :
    D' (addFun (normTranslate z u) g₀) (a, b) =
      ENNReal.ofReal (Real.exp (ξ * -(LQGMetric.circleAvg u 1 z))) *
        D' (addFun u g) (a + z, b + z) := by
  have hW0 := (h.weylReg_normTranslate hz).2
  change (D' (addFun (normTranslate z u) g₀)).1 (a, b) = _ * (D' (addFun u g)).1 (a + z, b + z)
  rw [← hW0.2 g₀, ← h.2.1.1.2 g]
  exact weylScale_shift ξ (Real.exp_pos _) (fun a b => tlc_metric' h hz a b) hg a b

end field

 

 

def ShortcutAt (D D' : DistC → LSCMetric) (ξ Q Ctime Cinc cMid : ℝ) (z : ℂ) (r : Set.Ioi (0 : ℝ))
    (V : TopologicalSpace.Opens ℂ) (g : C(ℂ, ℝ)) (u : DistC) : Prop :=
  ∀ c : ℝ, IsCircleAverage u r z c →
    ∀ (P' : ℝ → ℂ) (T τ' τ σ σ' : ℝ),
      EndSaving.Interfaces.BumpedGeodesic (D (addFun u (-g))) P' T →
      P' 0 ∉ ball z (4 * (r : ℝ)) → P' T ∉ ball z (4 * (r : ℝ)) →
      EndSaving.Interfaces.Excursion P' T (ball z (4 * (r : ℝ))) V τ' τ σ σ' →
      ∃ (hτ : P' τ ∈ ball z (4 * (r : ℝ))) (hσ : P' σ ∈ ball z (4 * (r : ℝ))),
        ENNReal.ofReal Ctime * ENNReal.ofReal ((r : ℝ) ^ (ξ * Q) * Real.exp (ξ * c)) ≤
          (D u).internal (ball z (4 * (r : ℝ))) (⟨P' τ, hτ⟩, ⟨P' σ, hσ⟩) →
        ∃ s t : ℝ, τ ≤ s ∧ s < t ∧ t ≤ σ ∧
          ENNReal.ofReal Cinc * ENNReal.ofReal ((r : ℝ) ^ (ξ * Q) * Real.exp (ξ * c)) ≤
            ENNReal.ofReal (t - s) ∧
          ∃ (hs : P' s ∈ ball z (4 * (r : ℝ))) (ht : P' t ∈ ball z (4 * (r : ℝ))),
            (D' (addFun u (-g))).internal (ball z (4 * (r : ℝ))) (⟨P' s, hs⟩, ⟨P' t, ht⟩) ≤
              ENNReal.ofReal (cMid * (t - s))

theorem mem_ball_shift (z w : ℂ) (ρ : ℝ) : w ∈ ball (0 : ℂ) ρ ↔ w + z ∈ ball z ρ := by
  rw [mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, add_sub_cancel_right, sub_zero]

theorem mem_ball_shift' (z w : ℂ) (ρ : ℝ) : w ∈ ball z ρ ↔ w - z ∈ ball (0 : ℂ) ρ := by
  rw [mem_ball_shift z (w - z) ρ, sub_add_cancel]

 
theorem ofReal_mul_cancel {a x y : ℝ} (ha : 0 < a)
    (h : ENNReal.ofReal a * ENNReal.ofReal x ≤ ENNReal.ofReal a * ENNReal.ofReal y) :
    ENNReal.ofReal x ≤ ENNReal.ofReal y := by
  have ha0 : ENNReal.ofReal a ≠ 0 := by simpa using ha
  calc ENNReal.ofReal x = (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal a * ENNReal.ofReal x) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal a * ENNReal.ofReal y) := by gcongr
    _ = ENNReal.ofReal y := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 ENNReal.ofReal_ne_top, one_mul]

 
theorem ennreal_cancel {a : ℝ} (ha : 0 < a) {x y : ℝ≥0∞}
    (h : ENNReal.ofReal a * x ≤ ENNReal.ofReal a * y) : x ≤ y := by
  have ha0 : ENNReal.ofReal a ≠ 0 := by simpa using ha
  calc x = (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal a * x) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal a * y) := by gcongr
    _ = y := by rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 ENNReal.ofReal_ne_top, one_mul]

 


theorem shortcutAt_of_normTranslate {ξ : ℝ} {D D' : DistC → LSCMetric} {Wc : Set ℂ}
    {Cc : Set (Set.Ioi (0 : ℝ) × ℂ)} {u : DistC} (hgood : LocalGood ξ D D' Wc Cc u) {z : ℂ}
    (hz : z ∈ Wc) {Q Ctime Cinc cMid : ℝ} {r : Set.Ioi (0 : ℝ)}
    {V V₀ : TopologicalSpace.Opens ℂ} (hV : ∀ w : ℂ, w ∈ (V₀ : Set ℂ) ↔ w + z ∈ (V : Set ℂ))
    {g g₀ : C(ℂ, ℝ)} (hg : ∀ x, g₀ x = g (x + z))
    (h0 : ShortcutAt D D' ξ Q Ctime Cinc cMid 0 r V₀ g₀ (normTranslate z u)) :
    ShortcutAt D D' ξ Q Ctime Cinc cMid z r V g u := by
  intro c hc P' T τ' τ σ σ' hgeo hP0 hPT hexc
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = Real.exp (ξ * -(LQGMetric.circleAvg u 1 z)) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; exact Real.exp_pos _
  have hg' : ∀ x, (-g₀) x = (-g) (x + z) := fun x => by
    simp only [ContinuousMap.neg_apply, hg]
  have hd : ∀ a b : ℂ, D (addFun (normTranslate z u) (-g₀)) (a, b) =
      ENNReal.ofReal κ * D (addFun u (-g)) (a + z, b + z) := by
    rw [hκdef]; exact tlc_bumped hgood hz hg'
  have he : ∀ a b : ℂ, D' (addFun (normTranslate z u) (-g₀)) (a, b) =
      ENNReal.ofReal κ * D' (addFun u (-g)) (a + z, b + z) := by
    rw [hκdef]; exact tlc_bumped' hgood hz hg'
  have hD0 : ∀ a b : ℂ, D (normTranslate z u) (a, b) = ENNReal.ofReal κ * D u (a + z, b + z) := by
    rw [hκdef]; exact tlc_metric hgood hz
  have hW : ∀ w : ℂ, w ∈ ball (0 : ℂ) (4 * (r : ℝ)) ↔ w + z ∈ ball z (4 * (r : ℝ)) :=
    fun w => mem_ball_shift z w _
  have hW' : ∀ w : ℂ, w ∈ ball z (4 * (r : ℝ)) ↔ w - z ∈ ball (0 : ℂ) (4 * (r : ℝ)) :=
    fun w => mem_ball_shift' z w _
  have ev : ∀ t, shiftCurve κ z P' (κ * t) = P' t - z := shiftCurve_mul hκ P'
  have es : ∀ t, P' t - z + z = P' t := fun t => sub_add_cancel _ _
  have hc0 := isCircleAverage_normTranslate hc
  have hQ0 : shiftCurve κ z P' 0 ∉ ball (0 : ℂ) (4 * (r : ℝ)) := by
    rw [hW, show shiftCurve κ z P' 0 = P' 0 - z by simp only [shiftCurve, zero_div], es]
    exact hP0
  have hQT : shiftCurve κ z P' (κ * T) ∉ ball (0 : ℂ) (4 * (r : ℝ)) := by
    rw [hW, ev, es]; exact hPT
  obtain ⟨hτ0, hσ0, himp⟩ := h0 _ hc0 (shiftCurve κ z P') (κ * T) (κ * τ') (κ * τ) (κ * σ) (κ * σ')
    (bumpedGeodesic_shift hκ hd hgeo) hQ0 hQT (excursion_shift hκ hW hV hexc)
  have hτ : P' τ ∈ ball z (4 * (r : ℝ)) := by
    have := (hW _).1 hτ0; rwa [ev, es] at this
  have hσ : P' σ ∈ ball z (4 * (r : ℝ)) := by
    have := (hW _).1 hσ0; rwa [ev, es] at this
  
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * c) := ⟨_, rfl⟩
  have hN0 : (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * (c + -(LQGMetric.circleAvg u 1 z))) = κ * N := by
    rw [hNdef, hκdef, mul_add, Real.exp_add]; ring
  refine ⟨hτ, hσ, fun hCt => ?_⟩
  have hint0 : (D (normTranslate z u)).internal (ball (0 : ℂ) (4 * (r : ℝ)))
      (⟨shiftCurve κ z P' (κ * τ), hτ0⟩, ⟨shiftCurve κ z P' (κ * σ), hσ0⟩) =
      ENNReal.ofReal κ * (D u).internal (ball z (4 * (r : ℝ))) (⟨P' τ, hτ⟩, ⟨P' σ, hσ⟩) :=
    internal_shift hκ hD0 hW' hτ0 hσ0 hτ hσ (by rw [ev, es]) (by rw [ev, es])
  have hCt0 : ENNReal.ofReal Ctime *
      ENNReal.ofReal ((r : ℝ) ^ (ξ * Q) * Real.exp (ξ * (c + -(LQGMetric.circleAvg u 1 z)))) ≤
      (D (normTranslate z u)).internal (ball (0 : ℂ) (4 * (r : ℝ)))
        (⟨shiftCurve κ z P' (κ * τ), hτ0⟩, ⟨shiftCurve κ z P' (κ * σ), hσ0⟩) := by
    rw [hint0, hN0, ENNReal.ofReal_mul hκ.le]
    calc ENNReal.ofReal Ctime * (ENNReal.ofReal κ * ENNReal.ofReal N)
        = ENNReal.ofReal κ * (ENNReal.ofReal Ctime * ENNReal.ofReal N) := by ring
      _ ≤ _ := by gcongr; rw [hNdef]; exact hCt
  obtain ⟨s₀, t₀, hs₀, hst₀, ht₀, hinc₀, hs0, ht0, hcost₀⟩ := himp hCt0
  have hs : P' (s₀ / κ) ∈ ball z (4 * (r : ℝ)) := by
    have := (hW _).1 hs0; rwa [show shiftCurve κ z P' s₀ = P' (s₀ / κ) - z from rfl, es] at this
  have ht : P' (t₀ / κ) ∈ ball z (4 * (r : ℝ)) := by
    have := (hW _).1 ht0; rwa [show shiftCurve κ z P' t₀ = P' (t₀ / κ) - z from rfl, es] at this
  have hts : t₀ - s₀ = κ * (t₀ / κ - s₀ / κ) := by field_simp
  refine ⟨s₀ / κ, t₀ / κ, (le_div_iff₀ hκ).2 (by rw [mul_comm]; exact hs₀),
    div_lt_div_of_pos_right hst₀ hκ, (div_le_iff₀ hκ).2 (by rw [mul_comm]; exact ht₀), ?_, hs, ht, ?_⟩
  · rw [hN0, ENNReal.ofReal_mul hκ.le, hts, ENNReal.ofReal_mul hκ.le] at hinc₀
    refine ennreal_cancel hκ ?_
    calc ENNReal.ofReal κ * (ENNReal.ofReal Cinc * ENNReal.ofReal ((r : ℝ) ^ (ξ * Q) * Real.exp (ξ * c)))
        = ENNReal.ofReal Cinc * (ENNReal.ofReal κ * ENNReal.ofReal N) := by rw [hNdef]; ring
      _ ≤ _ := hinc₀
  · have hint1 : (D' (addFun (normTranslate z u) (-g₀))).internal (ball (0 : ℂ) (4 * (r : ℝ)))
        (⟨shiftCurve κ z P' s₀, hs0⟩, ⟨shiftCurve κ z P' t₀, ht0⟩) =
        ENNReal.ofReal κ * (D' (addFun u (-g))).internal (ball z (4 * (r : ℝ)))
          (⟨P' (s₀ / κ), hs⟩, ⟨P' (t₀ / κ), ht⟩) :=
      internal_shift hκ he hW' hs0 ht0 hs ht (es _).symm (es _).symm
    rw [hint1, hts, show cMid * (κ * (t₀ / κ - s₀ / κ)) = κ * (cMid * (t₀ / κ - s₀ / κ)) by ring,
      ENNReal.ofReal_mul hκ.le] at hcost₀
    exact ennreal_cancel hκ hcost₀

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
