import SupercriticalLQGUniqueness.B2.PfeLocal.L6Coupling
import SupercriticalLQGUniqueness.B2.PfeLocal.L6Obs
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteMeasurable
import LQGMetric.Field.MarkovFinal
import LQGMetric.Field.CircleAvgRate

 
























set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Topology Metric TopologicalSpace
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open LQGMetric LQGMetric.Blueprint LQGMetric.DFGPS LQGMetric.DFGPS.L217 LQGMetric.GM.Bilip
open LQGMetric.LFPP
open Uniqueness.Toolkit.CompactPathInfimum

 
structure L6Geo where
  z : ℂ
  r : ℝ
  hr : 0 < r
  V₁ : Opens ℂ
  hball : closedBall z r ⊆ (V₁ : Set ℂ)
  U₁ : Opens ℂ
  φ : C(ℂ, ℝ)
  hφc : HasCompactSupport φ
  δ : ℝ
  hδ : 0 < δ
  hφU : ∀ x, φ x ≠ 0 → closedBall x δ ⊆ (closure (V₁ : Set ℂ))ᶜ
  hφ1 : ∀ x ∈ (U₁ : Set ℂ), φ x = 1
  R : ℝ
  hV₁R : (V₁ : Set ℂ) ⊆ closedBall 0 R
  hU₁R : (U₁ : Set ℂ) ⊆ closedBall 0 R

namespace L6Geo

variable (S : L6Geo)

 
def Uc : Opens ℂ := ⟨(closure (S.V₁ : Set ℂ))ᶜ, isClosed_closure.isOpen_compl⟩

theorem disjoint_Uc_sphere : Disjoint (S.Uc : Set ℂ) (sphere S.z S.r) := by
  refine Set.disjoint_compl_left_iff_subset.2 ?_
  calc sphere S.z S.r ⊆ closedBall S.z S.r := sphere_subset_closedBall
    _ ⊆ (S.V₁ : Set ℂ) := S.hball
    _ ⊆ closure (S.V₁ : Set ℂ) := subset_closure

 
def ren : DistC → DistC := normField (id : DistC → DistC) S.z S.r

 
def cA (g : DistC) : ℝ := circleAvg g S.r S.z

 
def Fb (g₀ : L6S → DistC) (g : DistC) : C(ℂ, ℝ) := harmFn S.φ S.δ S.hδ (g₀ (pairJ ⊤ g))

 
def N2 (g₀ : L6S → DistC) (g : DistC) : DistC := S.ren g - ofCont (S.Fb g₀ g)

 
def u (g₀ : L6S → DistC) (g : DistC) : C(L6K S.R, ℝ) :=
  l6Res S.R (S.Fb g₀ g + ContinuousMap.const ℂ (S.cA g))

theorem measurable_ren : Measurable S.ren :=
  measurable_distOn_iff.2 fun ψ => by
    have : (fun g : DistC => S.ren g ψ) =
        fun g => g ψ + (∫ x, ψ x) * (-circleAvg g S.r S.z) := by
      funext g; exact GFFInv.addConst_apply _ _ _
    rw [this]
    exact (measurable_distOn_apply ψ).add
      ((measurable_circleAvg_left S.r S.z).neg.const_mul _)

theorem measurable_cA : Measurable S.cA := measurable_circleAvg_left S.r S.z

theorem measurable_Fb {g₀ : L6S → DistC} (hg₀ : Measurable g₀) : Measurable (S.Fb g₀) :=
  (measurable_harmFn S.φ S.δ S.hδ).comp (hg₀.comp (measurable_pairJ ⊤))

theorem bound_Fb (g₀ : L6S → DistC) (g : DistC) : ∃ M, ∀ x, |S.Fb g₀ g x| ≤ M :=
  exists_bound_harmFn S.hφc S.δ S.hδ _

theorem measurable_u {g₀ : L6S → DistC} (hg₀ : Measurable g₀) : Measurable (S.u g₀) := by
  have h1 : Measurable fun g => S.Fb g₀ g + ContinuousMap.const ℂ (S.cA g) :=
    ContinuousMap.measurable_iff_eval.2 fun x =>
      ((continuous_eval_const x).measurable.comp (S.measurable_Fb hg₀)).add S.measurable_cA
  exact (continuous_l6Res S.R).measurable.comp h1

end L6Geo

 
def l6Act (U : Set ℂ) (ε : ℝ) (d : L5Code) : Prop :=
  cthickening (2 * Real.sqrt ε) (l5Rect d.1) ⊆ U

theorem l6Act_ball {U : Set ℂ} {ε : ℝ} {d : L5Code} (h : l6Act U ε d) {x : ℂ}
    (hx : x ∈ thickening (Real.sqrt ε) (l5Rect d.1)) : closedBall x (Real.sqrt ε) ⊆ U := by
  have hs := Real.sqrt_nonneg ε
  refine ((closedBall_subset_cthickening (thickening_subset_cthickening _ _ hx) _).trans
    (cthickening_cthickening_subset hs hs _)).trans ?_
  rw [← two_mul]; exact h

 
theorem l6_eventually_act {U : Set ℂ} (hU : IsOpen U) {d : L5Code} (hd : l5Rect d.1 ⊆ U)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) : ∀ᶠ n in atTop, l6Act U (e n) d := by
  obtain ⟨δ, hδ, hδU⟩ := (l5Rect_isCompact d.1).exists_cthickening_subset_open hU hd
  have hs : Tendsto (fun n => 2 * Real.sqrt (e n)) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0 |>.comp he).const_mul 2
  filter_upwards [hs.eventually (ge_mem_nhds hδ)] with n hn
  exact (cthickening_mono hn _).trans hδU

theorem l6_locMollifyC_congr {U : Opens ℂ} {f f' : DistC} (he : restrictTo U f = restrictTo U f')
    {ε : ℝ} (hε : 0 < ε) {x : ℂ} (hx : closedBall x (Real.sqrt ε) ⊆ U) :
    locMollifyC ε hε f x = locMollifyC ε hε f' x :=
  apply_eq_of_restrictTo_eq he _ ((tsupport_locTest_subset ε hε x).trans hx)

 
theorem l6_obs_congr_of_restrictTo (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) {U : Opens ℂ} {ε : ℝ}
    (hε : 0 < ε) {d : L5Code} (h : l6Act U ε d) {f f' : DistC}
    (he : restrictTo U f = restrictTo U f') (W : C(ℂ, ℝ)) :
    l5Obs (PfeWeyl.normalizedLFPPMetric ξ a (locMollifyC ε hε f + W)) d =
      l5Obs (PfeWeyl.normalizedLFPPMetric ξ a (locMollifyC ε hε f' + W)) d := by
  unfold l5Obs
  refine (l6_compactPathInf_lfpp_congr ξ a isOpen_thickening (fun x hx => ?_)
    (self_subset_thickening (Real.sqrt_pos.2 hε) _)).symm
  simp only [ContinuousMap.add_apply]
  rw [l6_locMollifyC_congr he hε (l6Act_ball h hx)]

 
def l6ObsFn (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (U : Set ℂ) (ε : Set.Ioi (0 : ℝ)) (W : ℕ → C(ℂ, ℝ))
    (f : DistC) : L5Code × ℕ → ℝ≥0∞ := by
  classical
  exact fun dj => if l6Act U ε dj.1 then
    l5Obs (PfeWeyl.normalizedLFPPMetric ξ a (locMollifyC ε ε.2 f + W dj.2)) dj.1 else 0

theorem measurable_l6ObsFn (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (U : Set ℂ) (ε : Set.Ioi (0 : ℝ))
    (W : ℕ → C(ℂ, ℝ)) : Measurable (l6ObsFn ξ a U ε W) := by
  classical
  refine measurable_pi_iff.2 fun dj => ?_
  by_cases h : l6Act U ε dj.1
  · have e : (fun f => l6ObsFn ξ a U ε W f dj) = fun f =>
        l5Obs (PfeWeyl.normalizedLFPPMetric ξ a (locMollifyC ε ε.2 f + W dj.2)) dj.1 := by
      funext f; simp only [l6ObsFn, h, ite_true]
    rw [e]
    refine (measurable_l5Obs dj.1).comp (PfeAxioms.measurable_normalizedLFPPMetric_comp ξ a ?_)
    intro z
    simp only [ContinuousMap.add_apply]
    exact ((continuous_eval_const z).measurable.comp (measurable_locMollifyC ε ε.2)).add_const _
  · have e : (fun f => l6ObsFn ξ a U ε W f dj) = fun _ => 0 := by
      funext f; simp only [l6ObsFn, h, ite_false]
    rw [e]; exact measurable_const

theorem l6ObsFn_congr (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (U : Opens ℂ) (ε : Set.Ioi (0 : ℝ))
    (W : ℕ → C(ℂ, ℝ)) {f f' : DistC} (he : restrictTo U f = restrictTo U f') :
    l6ObsFn ξ a U ε W f = l6ObsFn ξ a U ε W f' := by
  classical
  funext dj
  by_cases h : l6Act U ε dj.1
  · simp only [l6ObsFn, h, ite_true]
    exact l6_obs_congr_of_restrictTo ξ a ε.2 h he _
  · simp only [l6ObsFn, h, ite_false]

 
def l6AFn (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (U : Set ℂ) (ε : Set.Ioi (0 : ℝ)) (f : DistC) : L6T1 :=
  fun d => l6ObsFn ξ a U ε (fun _ => 0) f (d, 0)

theorem measurable_l6AFn (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (U : Set ℂ) (ε : Set.Ioi (0 : ℝ)) :
    Measurable (l6AFn ξ a U ε) :=
  measurable_pi_iff.2 fun d => (measurable_pi_apply (d, 0)).comp (measurable_l6ObsFn _ _ _ _ _)

theorem l6AFn_congr (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (U : Opens ℂ) (ε : Set.Ioi (0 : ℝ))
    {f f' : DistC} (he : restrictTo U f = restrictTo U f') :
    l6AFn ξ a U ε f = l6AFn ξ a U ε f' := by
  funext d; simp only [l6AFn, l6ObsFn_congr ξ a U ε (fun _ => 0) he]

 
def l6An (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (e : ℕ → Set.Ioi (0 : ℝ)) (S : L6Geo)
    (n : ℕ) (g : DistC) : L6T1 :=
  l6AFn ξ (m (e n)) S.V₁ (e n) (S.ren g)

 
def l6Bn (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (e : ℕ → Set.Ioi (0 : ℝ)) (S : L6Geo)
    (g₀ : L6S → DistC) (n : ℕ) (g : DistC) : L6T2 :=
  l6ObsFn ξ (m (e n)) S.U₁ (e n) (l6W S.R) (S.N2 g₀ g)

theorem l6An_apply {ξ : ℝ} {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {e : ℕ → Set.Ioi (0 : ℝ)}
    {S : L6Geo} {n : ℕ} {d : L5Code} (h : l6Act S.V₁ (e n) d) (g : DistC) :
    l6An ξ m e S n g d = l5Obs (PfeWeyl.normalizedLFPPMetric ξ (m (e n))
      (locMollifyC (e n) (e n).2 (S.ren g) + 0)) d := by
  classical
  simp only [l6An, l6AFn, l6ObsFn, h, ite_true]

theorem l6Bn_apply {ξ : ℝ} {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {e : ℕ → Set.Ioi (0 : ℝ)}
    {S : L6Geo} {g₀ : L6S → DistC} {n : ℕ} {d : L5Code} (h : l6Act S.U₁ (e n) d) (j : ℕ)
    (g : DistC) :
    l6Bn ξ m e S g₀ n g (d, j) = l5Obs (PfeWeyl.normalizedLFPPMetric ξ (m (e n))
      (locMollifyC (e n) (e n).2 (S.N2 g₀ g) + l6W S.R j)) d := by
  classical
  simp only [l6Bn, l6ObsFn, h, ite_true]

theorem measurable_l6An (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (S : L6Geo) (n : ℕ) : Measurable (l6An ξ m e S n) :=
  (measurable_l6AFn _ _ _ _).comp S.measurable_ren

 
theorem l6_comap_An_le (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (e : ℕ → Set.Ioi (0 : ℝ))
    (S : L6Geo) (n : ℕ) :
    MeasurableSpace.comap (l6An ξ m e S n) inferInstance ≤ fieldSigma S.ren S.V₁ :=
  comap_le_fieldSigma_of_local (measurable_l6AFn ξ (m (e n)) S.V₁ (e n)) S.V₁
    (fun _ _ he => l6AFn_congr ξ (m (e n)) S.V₁ (e n) he) S.ren

theorem isGFFPlusBddCont_normField_pairJInv_measurable (S : L6Geo) :
    Measurable (normField (pairJInv ⊤) S.z S.r) :=
  S.measurable_ren.comp (measurable_pairJInv ⊤)

set_option warn.classDefReducibility false in
 
def l6Germ (S : L6Geo) : MeasurableSpace DistC := fieldSigmaClosed S.ren (closure (S.V₁ : Set ℂ))

set_option warn.classDefReducibility false in
 
def l6G (S : L6Geo) : MeasurableSpace L6S :=
  MeasurableSpace.map (pairJ ⊤) (l6Germ S) ⊓ MeasurableSpace.pi

set_option warn.classDefReducibility false in
 
def l6H (S : L6Geo) (g₀ : L6S → DistC) : MeasurableSpace L6S :=
  MeasurableSpace.comap (fun x => normField (pairJInv ⊤) S.z S.r x - g₀ x)
    (inferInstance : MeasurableSpace DistC)

theorem l6G_le (S : L6Geo) : l6G S ≤ MeasurableSpace.pi := inf_le_right

theorem l6H_le (S : L6Geo) {g₀ : L6S → DistC} (hg₀ : Measurable g₀) :
    l6H S g₀ ≤ MeasurableSpace.pi :=
  (measurable_distOn_iff.2 fun ψ =>
    ((measurable_distOn_apply ψ).comp (isGFFPlusBddCont_normField_pairJInv_measurable S)).sub
      ((measurable_distOn_apply ψ).comp hg₀)).comap_le

 
theorem l6_canonical {μ : Measure DistC} [IsProbabilityMeasure μ] (hμ : IsNormalizedWPGFF id μ)
    (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (e : ℕ → Set.Ioi (0 : ℝ)) (S : L6Geo) :
    ∃ g₀ : L6S → DistC, Measurable g₀ ∧
      (∀ n, Indep ((l6G S).comap (pairJ ⊤) ⊔
          MeasurableSpace.comap (l6An ξ m e S n) inferInstance)
        ((l6H S g₀).comap (pairJ ⊤) ⊔ MeasurableSpace.comap (l6Bn ξ m e S g₀ n) inferInstance)
        μ) ∧
      (l6G S).comap (pairJ ⊤) ≤ l6Germ S ∧
      MeasurableSpace.comap (normField (pairJInv ⊤) S.z S.r) inferInstance ≤
        l6G S ⊔ l6H S g₀ := by
  set X : DistC → L6S := pairJ ⊤ with hXdef
  have hrec := isNormalizedAt_recenter hμ.1 S.hr S.z
  have hrenwp : IsWholePlaneGFF S.ren μ := hrec.1
  have hrenn : ∀ᵐ g ∂μ, circleAvg (S.ren g) S.r S.z = 0 := hrec.2
  obtain ⟨hh, hz, hsum, hharm, ⟨G₀, hG₀m, hG₀ae⟩, -, -, -, hind⟩ :=
    markov_normAt MarkovFinal.lmLem2_1 μ S.ren hrenwp S.hr S.z hrenn S.Uc S.disjoint_Uc_sphere
  have hUcc : ((S.Uc : Set ℂ))ᶜ = closure (S.V₁ : Set ℂ) := compl_compl _
  rw [hUcc] at hG₀m hind
  set N : L6S → DistC := normField (pairJInv ⊤) S.z S.r with hNdef
  have hNX : ∀ g, N (X g) = S.ren g := fun g =>
    normField_pairJInv_pairJ (h := (id : DistC → DistC)) S.z S.r g
  have hNm : Measurable N := isGFFPlusBddCont_normField_pairJInv_measurable S
  
  have hGX : l6Germ S ≤ MeasurableSpace.comap X (l6G S) := by
    intro s hs
    have hle : MeasurableSpace.comap (fun g => pairJ ⊤ (S.ren g)) MeasurableSpace.pi ≤
        MeasurableSpace.comap X MeasurableSpace.pi := by
      rw [show (fun g => pairJ ⊤ (S.ren g)) = (fun x => pairJ ⊤ (N x)) ∘ X from
        funext fun g => by simp only [Function.comp, hNX], ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono ((measurable_pairJ ⊤).comp hNm).comap_le
    obtain ⟨t, ht, rfl⟩ := hle s (fieldSigmaClosed_le_comap_pairJ _ _ s hs)
    exact ⟨t, MeasurableSpace.measurableSet_inf.2 ⟨hs, ht⟩, rfl⟩
  obtain ⟨g₀, hg, hG₀eq⟩ := Measurable.exists_eq_measurable_comp (mY := l6G S)
    (hG₀m.mono hGX le_rfl)
  have hae : hh =ᵐ[μ] fun g => g₀ (X g) := hG₀ae.trans (EventuallyEq.of_eq hG₀eq)
  have hgm : Measurable g₀ := hg.mono (l6G_le S) le_rfl
  
  set hz' : DistC → DistC := fun g => S.ren g - g₀ (X g) with hz'def
  have hz'ae : hz' =ᵐ[μ] hz := by
    filter_upwards [hae] with g hg'
    simp only [hz'def, hsum g]
    rw [show g₀ (X g) = hh g from hg'.symm]
    exact add_sub_cancel_left _ _
  have hind' : Indep (MeasurableSpace.comap hz' inferInstance) (l6Germ S) μ :=
    indep_of_le_aeClosure hind (L219.comap_le_aeClosure_of_ae_eq (comap_measurable hz) hz'ae)
      (le_aeClosure _)
  
  have hagree : ∀ᵐ g ∂μ, ∀ ψ : TestC, tsupport (ψ : ℂ → ℝ) ⊆ (S.U₁ : Set ℂ) →
      S.N2 g₀ g ψ = hz' g ψ := by
    have H := (exists_harmFun (P := μ) (h' := S.ren) (U := S.Uc) hsum hharm hae S.hφc S.hδ
      S.hφU S.hφ1).2
    filter_upwards [H, hz'ae] with g hg' hg''
    intro ψ hψ
    have := hg' ψ hψ
    simp only [L6Geo.N2, L6Geo.Fb]
    rw [this, hg'']
  
  have hL : ∀ n, (l6G S).comap X ⊔ MeasurableSpace.comap (l6An ξ m e S n) inferInstance ≤
      l6Germ S :=
    fun n => sup_le ((MeasurableSpace.comap_mono inf_le_left).trans MeasurableSpace.comap_map_le)
      ((l6_comap_An_le ξ m e S n).trans (fieldSigma_le_fieldSigmaClosed_of_subset _ subset_closure))
  have hR : ∀ n, (l6H S g₀).comap X ⊔ MeasurableSpace.comap (l6Bn ξ m e S g₀ n) inferInstance ≤
      aeClosure μ (MeasurableSpace.comap hz' inferInstance) := by
    intro n
    refine sup_le ?_ ?_
    · refine le_trans ?_ (le_aeClosure _)
      unfold l6H
      rw [MeasurableSpace.comap_comp]
      have : (fun x => N x - g₀ x) ∘ X = hz' := funext fun g => by
        simp only [Function.comp, hNX, hz'def]
      rw [this]
    · have hloc := comap_le_fieldSigma_of_local (measurable_l6ObsFn ξ (m (e n)) S.U₁ (e n)
        (l6W S.R)) S.U₁ (fun f f' he => l6ObsFn_congr ξ (m (e n)) S.U₁ (e n) (l6W S.R) he)
        (S.N2 g₀)
      refine hloc.trans (comap_le_aeClosure_of_restrictTo_ae_eq ?_)
      filter_upwards [hagree] with g hg'
      ext φ
      show S.N2 g₀ g (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := S.U₁) (Ω₂ := ⊤) φ) =
        hz' g (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := S.U₁) (Ω₂ := ⊤) φ)
      refine hg' _ ?_
      have e'' : ((TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := S.U₁) (Ω₂ := ⊤) φ :
          TestC) : ℂ → ℝ) = φ := by
        rw [TestFunction.monoCLM_apply]
        simp only [le_refl, le_top, and_self, ite_true]
      rw [e'']
      exact φ.tsupport_subset
  refine ⟨g₀, hgm, fun n => ?_,
    (MeasurableSpace.comap_mono inf_le_left).trans MeasurableSpace.comap_map_le, ?_⟩
  · exact indep_of_le_aeClosure hind'.symm ((hL n).trans (le_aeClosure _)) (hR n)
  · 
    have hk : Measurable[l6G S ⊔ l6H S g₀] fun x => g₀ x + (N x - g₀ x) :=
      (@measurable_distOn_iff _ L6S (l6G S ⊔ l6H S g₀) _).2 fun ψ => by
        show Measurable[l6G S ⊔ l6H S g₀] fun x => g₀ x ψ + (N x - g₀ x) ψ
        exact (((measurable_distOn_apply ψ).comp hg).mono le_sup_left le_rfl).add
          (((measurable_distOn_apply ψ).comp (comap_measurable (fun x => N x - g₀ x))).mono
            le_sup_right le_rfl)
    have e' : (fun x => g₀ x + (N x - g₀ x)) = N := funext fun x => add_sub_cancel _ _
    rw [e'] at hk
    exact hk.comap_le

end SupercriticalLQGUniqueness.B2.PfeLocal
