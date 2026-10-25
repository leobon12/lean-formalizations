import SupercriticalLQGUniqueness.B2.PfeLocal.L6StageMain
import LQGMetric.Papers.LM.LocEquiv
import LQGMetric.Papers.DG.S3P18R1

 






















set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Topology Metric TopologicalSpace
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open LQGMetric LQGMetric.Blueprint LQGMetric.DFGPS LQGMetric.DFGPS.L217 LQGMetric.GM.Bilip PfeWeyl
open Uniqueness.Toolkit.CompactPathInfimum

namespace Inputs

 

def L6SmallAnnuli (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (e : ℕ → Set.Ioi (0 : ℝ)) {Ω' : Type}
    [MeasurableSpace Ω'] (P' : Measure Ω') (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric) : Prop :=
  ∀ k : ℕ, ∀ᵐ ω ∂P', SmallAnnulusCosts
    (fun n => normalizedLFPPMetric ξ (m (e n)) (V (e n) (hN n ω))) (L ω) (closedBall 0 k)
    (ball 0 ((k : ℝ) + 1))

end Inputs

 

 
def l6Exh (U : Set ℂ) (j : ℕ) : Set ℂ :=
  {w | ‖w‖ < j ∧ ∃ ρ : ℝ, 1 / ((j : ℝ) + 1) < ρ ∧ ball w ρ ⊆ U}

theorem isOpen_l6Exh (U : Set ℂ) (j : ℕ) : IsOpen (l6Exh U j) := by
  refine Metric.isOpen_iff.2 fun w ⟨hw, ρ, hρ, hρU⟩ => ?_
  refine ⟨min ((j : ℝ) - ‖w‖) (ρ - 1 / ((j : ℝ) + 1)), lt_min (by linarith) (by linarith),
    fun w' hw' => ?_⟩
  have hd : dist w' w < min ((j : ℝ) - ‖w‖) (ρ - 1 / ((j : ℝ) + 1)) := hw'
  have h1 := lt_of_lt_of_le hd (min_le_left _ _)
  have h2 := lt_of_lt_of_le hd (min_le_right _ _)
  refine ⟨?_, ρ - dist w' w, by linarith, fun y hy => hρU ?_⟩
  · have := norm_le_norm_add_norm_sub' w' w
    rw [← dist_eq_norm] at this
    linarith
  · rw [mem_ball] at hy ⊢
    linarith [dist_triangle y w' w]

theorem l6Exh_mono (U : Set ℂ) : Monotone (l6Exh U) := by
  intro j j' hjj' w ⟨hw, ρ, hρ, hρU⟩
  have hjj'' : (j : ℝ) ≤ j' := by exact_mod_cast hjj'
  refine ⟨lt_of_lt_of_le hw hjj'', ρ, lt_of_le_of_lt ?_ hρ, hρU⟩
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem l6Exh_subset_closedBall (U : Set ℂ) (j : ℕ) : l6Exh U j ⊆ closedBall 0 j :=
  fun w hw => by rw [mem_closedBall, dist_zero_right]; exact hw.1.le

theorem isClosed_setOf_ball_subset (U : Set ℂ) (r : ℝ) : IsClosed {w : ℂ | ball w r ⊆ U} := by
  have : {w : ℂ | ball w r ⊆ U} = (⋃ y ∈ Uᶜ, ball y r)ᶜ := by
    ext w
    simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion, not_exists]
    constructor
    · intro h y hy hw
      exact hy (h (by rw [mem_ball, dist_comm]; exact hw))
    · intro h y hy
      by_contra hyU
      exact h y hyU (by rw [mem_ball, dist_comm]; exact hy)
  rw [this]
  exact (isOpen_biUnion fun y _ => isOpen_ball).isClosed_compl

theorem closure_l6Exh_subset (U : Set ℂ) (j : ℕ) : closure (l6Exh U j) ⊆ U := by
  have hsub : l6Exh U j ⊆ {w : ℂ | ball w (1 / ((j : ℝ) + 1)) ⊆ U} :=
    fun w ⟨_, ρ, hρ, hρU⟩ => (ball_subset_ball hρ.le).trans hρU
  refine (closure_minimal hsub (isClosed_setOf_ball_subset U _)).trans fun w hw => hw ?_
  exact mem_ball_self (by positivity)

theorem closure_l6Exh_subset_closedBall (U : Set ℂ) (j : ℕ) :
    closure (l6Exh U j) ⊆ closedBall 0 j :=
  closure_minimal (l6Exh_subset_closedBall U j) isClosed_closedBall

theorem isCompact_closure_l6Exh (U : Set ℂ) (j : ℕ) : IsCompact (closure (l6Exh U j)) :=
  (isCompact_closedBall 0 (j : ℝ)).of_isClosed_subset isClosed_closure
    (closure_l6Exh_subset_closedBall U j)

theorem exists_l6Exh_of_compact {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ j, K ⊆ l6Exh U j := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU hKU
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨j, hj⟩ := exists_nat_gt (max M (2 / δ))
  refine ⟨j, fun w hw => ⟨?_, δ, ?_, (ball_subset_thickening hw δ).trans hδU⟩⟩
  · have := hM hw
    rw [mem_closedBall, dist_zero_right] at this
    linarith [le_max_left M (2 / δ)]
  · have h2 : 2 / δ < (j : ℝ) + 1 := by linarith [le_max_right M (2 / δ)]
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at h2
    linarith

theorem exists_mem_l6Exh_iSup {Ω : Type} {L : Ω → LSCMetric} {U : Set ℂ} (hU : IsOpen U) :
    l5ObsSigma L U ≤ ⨆ j, l5ObsSigma L (l6Exh U j) := by
  refine iSup₂_le fun c hc => ?_
  obtain ⟨j, hj⟩ := exists_l6Exh_of_compact (l5Rect_isCompact c.1) hU hc
  exact le_iSup_of_le j (le_iSup₂_of_le (f := fun (c : L5Code) (_ : l5Rect c.1 ⊆ l6Exh U j) =>
    MeasurableSpace.comap (fun ω => l5Obs (L ω) c) inferInstance) c hj le_rfl)

theorem l6ObsSigma_mono_l6Exh {Ω : Type} (L : Ω → LSCMetric) (U : Set ℂ) :
    Monotone fun j => l5ObsSigma L (l6Exh U j) :=
  fun _ _ hjj' => l5ObsSigma_mono L (l6Exh_mono U hjj')

 

theorem l6_obs_empty (D : LSCMetric) {c : L5Code} (hc : l5Rect c.1 = ∅) : l5Obs D c = ⊤ := by
  unfold l5Obs compactPathInf
  refine le_antisymm le_top (le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP =>
    le_iInf fun htr => ?_)
  have := htr s ⟨le_rfl, hP.1⟩
  rw [hc] at this
  exact absurd this (notMem_empty _)

theorem l6_comap_le_pairJ {Ω' : Type} [MeasurableSpace Ω'] (h' : Ω' → DistC) :
    MeasurableSpace.comap h' inferInstance ≤
      MeasurableSpace.comap (fun ω => pairJ ⊤ (h' ω)) MeasurableSpace.pi := by
  have e : h' = (pairJInv ⊤) ∘ fun ω => pairJ ⊤ (h' ω) := funext fun ω => (pairJInv_pairJ ⊤ _).symm
  conv_lhs => rw [e]
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pairJInv ⊤).comap_le

theorem l6_measurable_cA_fieldSigma (S : L6Geo) {Ω' : Type} (h' : Ω' → DistC) {V : Opens ℂ}
    (hS : sphere S.z S.r ⊆ (V : Set ℂ)) :
    Measurable[fieldSigma h' V] fun ω => S.cA (h' ω) := by
  obtain ⟨ε, hε, hεV⟩ := (isCompact_sphere S.z S.r).exists_thickening_subset_open V.isOpen hS
  have hεV' : thickening ε (sphere S.z |S.r|) ⊆ (V : Set ℂ) := by rwa [abs_of_pos S.hr]
  exact (GM.measurable_circleAvg_fieldSigma h' S.r S.z hε).mono
    (GM.fieldSigma_mono h' (V := nbhdO ε (sphere S.z |S.r|)) (W := V) hεV') le_rfl

 
theorem l6_fieldSigma_ren_le (S : L6Geo) {Ω' : Type} (h' : Ω' → DistC) {V : Opens ℂ}
    (hS : sphere S.z S.r ⊆ (V : Set ℂ)) :
    fieldSigma (fun ω => S.ren (h' ω)) V ≤ fieldSigma h' V := by
  have hm : Measurable[fieldSigma h' V] fun ω => restrictTo V (S.ren (h' ω)) :=
    L219.measurable_restrictTo_addConst V (comap_measurable _)
      (l6_measurable_cA_fieldSigma S h' hS).neg
  exact hm.comap_le

 
theorem l6_G_le_fieldSigma (S : L6Geo) {Ω' : Type} [MeasurableSpace Ω'] (h' : Ω' → DistC)
    {V : Opens ℂ} (hV : closure (S.V₁ : Set ℂ) ⊆ (V : Set ℂ)) (hV₁c : IsCompact (closure (S.V₁ : Set ℂ))) :
    MeasurableSpace.comap (fun ω => pairJ ⊤ (h' ω)) (l6G S) ≤ fieldSigma h' V := by
  obtain ⟨δ, hδ, hδV⟩ := hV₁c.exists_thickening_subset_open V.isOpen hV
  have hS : sphere S.z S.r ⊆ (V : Set ℂ) :=
    sphere_subset_closedBall.trans (S.hball.trans (subset_closure.trans hV))
  have h1 : l6Germ S ≤ fieldSigma S.ren V :=
    (iInf₂_le δ hδ).trans (GM.fieldSigma_mono _ (V := nbhdO δ (closure (S.V₁ : Set ℂ)))
      (W := V) hδV)
  rw [show (fun ω => pairJ ⊤ (h' ω)) = pairJ ⊤ ∘ h' from rfl, ← MeasurableSpace.comap_comp]
  refine (MeasurableSpace.comap_mono ((l6_comap_G_le S).trans h1)).trans ?_
  have e : MeasurableSpace.comap h' (fieldSigma S.ren V) = fieldSigma (fun ω => S.ren (h' ω)) V := by
    unfold fieldSigma; rw [MeasurableSpace.comap_comp]; rfl
  rw [e]
  exact l6_fieldSigma_ren_le S h' hS

 

section SigmaAlgebras

set_option warn.classDefReducibility false

variable {Ω' : Type}

 
def l6σB' (h' : Ω' → DistC) (L : Ω' → LSCMetric) (W : Opens ℂ) : MeasurableSpace Ω' :=
  fieldSigmaClosed h' (W : Set ℂ)ᶜ ⊔ l5ObsSigma L (closure (W : Set ℂ))ᶜ

 
def l6σG₀ (S : L6Geo) (h' : Ω' → DistC) : MeasurableSpace Ω' :=
  MeasurableSpace.comap (fun ω => pairJ ⊤ (h' ω)) (l6G S)

 
def l6σA₀ (ξ : ℝ) (z : ℂ) (ρ : ℝ) (V₁ : Set ℂ) (h' : Ω' → DistC) (L : Ω' → LSCMetric) :
    MeasurableSpace Ω' :=
  ⨆ (d : L5Code) (_ : l5Rect d.1 ⊆ V₁), MeasurableSpace.comap
    (fun ω => ENNReal.ofReal (Real.exp (-(ξ * circleAvg (h' ω) ρ z))) * l5Obs (L ω) d)
    (inferInstance : MeasurableSpace ℝ≥0∞)

 
def l6σBk (h' : Ω' → DistC) (L : Ω' → LSCMetric) (U : Set ℂ) : MeasurableSpace Ω' :=
  MeasurableSpace.comap (fun ω => pairJ ⊤ (h' ω)) MeasurableSpace.pi ⊔ l5ObsSigma L U

end SigmaAlgebras

 

 
theorem l6_obsLocality (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (hVm : ∀ δ, Measurable (V δ))
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    (e : ℕ → Set.Ioi (0 : ℝ)) (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0))
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h' : Ω' → DistC) (hh' : IsNormalizedWholePlaneGFF h' P')
    (hN : ℕ → Ω' → DistC) (hNm : ∀ n, Measurable (hN n))
    (hNlaw : ∀ n, P'.map (hN n) = normGFFLaw)
    (hpair : ∀ φ : TestC, ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω φ) atTop (𝓝 (h' ω φ)))
    (L : Ω' → LSCMetric) (hL : Measurable L)
    (hconv : ∀ᵐ ω ∂P', Tendsto (fun n =>
      PfeWeyl.normalizedLFPPMetric ξ (m (e n)) (V (e n) (hN n ω))) atTop (𝓝 (L ω)))
    (hsmall : Inputs.L6SmallAnnuli ξ m V e P' hN L) :
    Inputs.L5ObsLocality P' h' L := by
  have hold := Uniqueness.Toolkit.AnnulusIteration.normalized_old_of_new hh'
  have hlaw : normGFFLaw = P'.map h' := GM.normGFFLaw_eq hold
  have hh'm : Measurable h' := hold.1.measurable
  have hμ : IsNormalizedWPGFF id normGFFLaw := by
    rw [hlaw]
    exact ⟨GM.isWholePlaneGFF_id_map hold.1, (ae_map_iff hh'm.aemeasurable
      (measurableSet_eq_fun (measurable_circleAvg_left 1 0) measurable_const)).2 hold.2⟩
  have : IsProbabilityMeasure (normGFFLaw : Measure DistC) := by
    rw [hlaw]; exact (Measure.isProbabilityMeasure_map_iff hh'm.aemeasurable).2 inferInstance
  have hξ : (0 : ℝ) ≤ ξ := le_of_lt ξ.2
  intro W
  change CondIndepEv (fieldSigma h' W) (l5ObsSigma L W) (l6σB' h' L W) P'
  have hG'm : fieldSigma h' W ≤ (inferInstance : MeasurableSpace Ω') :=
    (LM.fieldSigma_le_comapH h' W).trans hh'm.comap_le
  have hB'm : l6σB' h' L W ≤ (inferInstance : MeasurableSpace Ω') :=
    sup_le ((iInf₂_le 1 one_pos).trans ((LM.fieldSigma_le_comapH h' _).trans hh'm.comap_le))
      (l5ObsSigma_le hL _)
  by_cases hW0 : (W : Set ℂ) = ∅
  · 
    have hA : l5ObsSigma L W ≤ aeClosure P' (fieldSigma h' W) := by
      refine iSup₂_le fun c hc => ?_
      have hc' : l5Rect c.1 = ∅ := Set.subset_eq_empty hc hW0
      have : (fun ω => l5Obs (L ω) c) = fun _ => ⊤ := funext fun ω => l6_obs_empty (L ω) hc'
      rw [this, MeasurableSpace.comap_const]; exact bot_le
    exact condIndepEv_of_le_aeClosure hG'm hA (hB'm.trans (le_aeClosure _))
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.2 hW0
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 W.isOpen z hz
  have hρ : 0 < ε / 2 := half_pos hε
  obtain ⟨j₀, hj₀⟩ := exists_l6Exh_of_compact (isCompact_closedBall z (ε / 2)) W.isOpen
    ((closedBall_subset_ball (half_lt_self hε)).trans hεW)
  
  have hj : ∀ j : ℕ, CondIndepEv (fieldSigma h' W) (l5ObsSigma L (l6Exh W (j₀ + j)))
      (l6σB' h' L W) P' := by
    intro j
    have hball : closedBall z (ε / 2) ⊆ l6Exh W (j₀ + j) :=
      hj₀.trans (l6Exh_mono W (Nat.le_add_right _ _))
    have hV₁W : closure (l6Exh W (j₀ + j)) ⊆ (W : Set ℂ) := closure_l6Exh_subset _ _
    have hV₁c : IsCompact (closure (l6Exh W (j₀ + j))) := isCompact_closure_l6Exh _ _
    have hUco : IsOpen (closure (l6Exh W (j₀ + j)))ᶜ := isClosed_closure.isOpen_compl
    
    have hstage : ∀ k : ℕ, ∃ S : L6Geo, S.z = z ∧ S.r = ε / 2 ∧
        (S.V₁ : Set ℂ) = l6Exh W (j₀ + j) ∧
        (S.U₁ : Set ℂ) = l6Exh (closure (l6Exh W (j₀ + j)))ᶜ k := by
      intro k
      obtain ⟨φ, U₁', δ, hφc, -, hKU₁', hφ1', hδ, hφU⟩ := exists_bump_of_isCompact
        (isCompact_closure_l6Exh (closure (l6Exh W (j₀ + j)))ᶜ k) hUco
        (closure_l6Exh_subset _ k)
      refine ⟨⟨z, ε / 2, hρ, ⟨l6Exh W (j₀ + j), isOpen_l6Exh _ _⟩, hball,
        ⟨l6Exh (closure (l6Exh W (j₀ + j)))ᶜ k, isOpen_l6Exh _ _⟩, φ, hφc, δ, hδ, hφU,
        fun x hx => hφ1' x (hKU₁' (subset_closure hx)), (j₀ + j : ℕ) + k, ?_, ?_⟩,
        rfl, rfl, rfl, rfl⟩
      · exact (l6Exh_subset_closedBall _ _).trans (closedBall_subset_closedBall (by
          push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))
      · exact (l6Exh_subset_closedBall _ _).trans (closedBall_subset_closedBall (by
          push_cast; linarith [(Nat.cast_nonneg (j₀ + j) : (0 : ℝ) ≤ (j₀ + j : ℕ))]))
    choose S hSz hSr hSV hSU using hstage
    have hGeq : ∀ k, l6G (S k) = l6G (S 0) := by
      intro k; unfold l6G l6Germ L6Geo.ren; rw [hSz, hSz, hSr, hSr, hSV, hSV]
    have hk : ∀ k, CondIndepEv (l6σG₀ (S 0) h') (l6σA₀ (ξ : ℝ) z (ε / 2) (l6Exh W (j₀ + j)) h' L)
        (l6σBk h' L (l6Exh (closure (l6Exh W (j₀ + j)))ᶜ k)) P' := by
      intro k
      have H := l6_stage hξ m e he hVm hμ hV hh'm hlaw.symm hNm hNlaw hpair hL hconv hsmall (S k)
      rw [hGeq k] at H
      simp only [L6Geo.cA, hSz, hSr, hSV, hSU] at H
      exact H
    have hG₀m : l6σG₀ (S 0) h' ≤ (inferInstance : MeasurableSpace Ω') :=
      (MeasurableSpace.comap_mono (l6G_le _)).trans ((measurable_pairJ ⊤).comp hh'm).comap_le
    have hcA : Measurable fun ω => ENNReal.ofReal (Real.exp (-((ξ : ℝ) *
        circleAvg (h' ω) (ε / 2) z))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (((measurable_circleAvg_left (ε / 2) z).comp hh'm).const_mul _).neg)
    have hA₀m : l6σA₀ (ξ : ℝ) z (ε / 2) (l6Exh W (j₀ + j)) h' L ≤
        (inferInstance : MeasurableSpace Ω') :=
      iSup₂_le fun d _ => (hcA.mul ((measurable_l5Obs d).comp hL)).comap_le
    have hBkm : ∀ k, l6σBk h' L (l6Exh (closure (l6Exh W (j₀ + j)))ᶜ k) ≤
        (inferInstance : MeasurableSpace Ω') := fun k =>
      sup_le ((measurable_pairJ ⊤).comp hh'm).comap_le (l5ObsSigma_le hL _)
    have hBmono : Monotone fun k => l6σBk h' L (l6Exh (closure (l6Exh W (j₀ + j)))ᶜ k) :=
      fun k k' hkk' => sup_le_sup_left (l5ObsSigma_mono L (l6Exh_mono _ hkk')) _
    have hlim := condIndepEv_iSup_of_monotone hG₀m (fun _ => hA₀m) hBkm monotone_const hBmono hk
    rw [iSup_const] at hlim
    
    have hS0' : sphere (S 0).z (S 0).r ⊆ (W : Set ℂ) := by
      rw [hSz, hSr]
      exact sphere_subset_closedBall.trans (hball.trans (subset_closure.trans hV₁W))
    have h1 : l6σG₀ (S 0) h' ≤ aeClosure P' (fieldSigma h' W) :=
      (l6_G_le_fieldSigma (S 0) h' (by rw [hSV]; exact hV₁W) (by rw [hSV]; exact hV₁c)).trans
        (le_aeClosure _)
    have h2 : fieldSigma h' W ≤ aeClosure P'
        ((⨆ k, l6σBk h' L (l6Exh (closure (l6Exh W (j₀ + j)))ᶜ k)) ⊔ l6σG₀ (S 0) h') := by
      refine le_trans ?_ (le_aeClosure _)
      exact ((LM.fieldSigma_le_comapH h' W).trans (l6_comap_le_pairJ h')).trans
        ((le_sup_left.trans (le_iSup (fun k => l6σBk h' L
          (l6Exh (closure (l6Exh W (j₀ + j)))ᶜ k)) 0)).trans le_sup_left)
    have h3 : l5ObsSigma L (l6Exh W (j₀ + j)) ≤ aeClosure P'
        (l6σA₀ (ξ : ℝ) z (ε / 2) (l6Exh W (j₀ + j)) h' L ⊔ fieldSigma h' W) := by
      refine le_trans (iSup₂_le fun d hd => ?_) (le_aeClosure _)
      have hcm : Measurable[fieldSigma h' W] fun ω =>
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * circleAvg (h' ω) (ε / 2) z)) := by
        have := l6_measurable_cA_fieldSigma (S 0) h' hS0'
        simp only [L6Geo.cA, hSz, hSr] at this
        exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (this.const_mul _))
      have hom : Measurable[l6σA₀ (ξ : ℝ) z (ε / 2) (l6Exh W (j₀ + j)) h' L] fun ω =>
          ENNReal.ofReal (Real.exp (-((ξ : ℝ) * circleAvg (h' ω) (ε / 2) z))) * l5Obs (L ω) d :=
        (comap_measurable _).mono (le_iSup₂_of_le (f := fun (d : L5Code)
          (_ : l5Rect d.1 ⊆ l6Exh W (j₀ + j)) => MeasurableSpace.comap (fun ω =>
            ENNReal.ofReal (Real.exp (-((ξ : ℝ) * circleAvg (h' ω) (ε / 2) z))) * l5Obs (L ω) d)
              (inferInstance : MeasurableSpace ℝ≥0∞)) d hd le_rfl) le_rfl
      have hprod : Measurable[l6σA₀ (ξ : ℝ) z (ε / 2) (l6Exh W (j₀ + j)) h' L ⊔ fieldSigma h' W]
          fun ω => ENNReal.ofReal (Real.exp ((ξ : ℝ) * circleAvg (h' ω) (ε / 2) z)) *
            (ENNReal.ofReal (Real.exp (-((ξ : ℝ) * circleAvg (h' ω) (ε / 2) z))) *
              l5Obs (L ω) d) :=
        (hcm.mono le_sup_right le_rfl).mul (hom.mono le_sup_left le_rfl)
      have e1 : (fun ω => ENNReal.ofReal (Real.exp ((ξ : ℝ) * circleAvg (h' ω) (ε / 2) z)) *
          (ENNReal.ofReal (Real.exp (-((ξ : ℝ) * circleAvg (h' ω) (ε / 2) z))) *
            l5Obs (L ω) d)) = fun ω => l5Obs (L ω) d := by
        funext ω
        rw [← mul_assoc, l6_ofReal_exp_mul, add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one,
          one_mul]
      rw [e1] at hprod
      exact hprod.comap_le
    have h4 : l6σB' h' L W ≤ aeClosure P'
        ((⨆ k, l6σBk h' L (l6Exh (closure (l6Exh W (j₀ + j)))ᶜ k)) ⊔ fieldSigma h' W) := by
      refine le_trans (sup_le ?_ ?_) (le_aeClosure _)
      · exact ((iInf₂_le 1 one_pos).trans ((LM.fieldSigma_le_comapH h' _).trans
          (l6_comap_le_pairJ h'))).trans ((le_sup_left.trans (le_iSup (fun k => l6σBk h' L
            (l6Exh (closure (l6Exh W (j₀ + j)))ᶜ k)) 0)).trans le_sup_left)
      · refine (l5ObsSigma_mono L (compl_subset_compl.2 (closure_mono
          (subset_closure.trans hV₁W)))).trans ?_
        refine (exists_mem_l6Exh_iSup hUco).trans (iSup_le fun k => ?_)
        exact (le_sup_right.trans (le_iSup (fun k => l6σBk h' L
          (l6Exh (closure (l6Exh W (j₀ + j)))ᶜ k)) k)).trans le_sup_left
    exact L219.condIndepEv_transfer hG₀m hA₀m (iSup_le hBkm) hG'm hlim h1 h2 h3 h4
  
  have hAjm : ∀ j, l5ObsSigma L (l6Exh W (j₀ + j)) ≤ (inferInstance : MeasurableSpace Ω') :=
    fun j => l5ObsSigma_le hL _
  have hAmono : Monotone fun j => l5ObsSigma L (l6Exh W (j₀ + j)) := fun j j' hjj' =>
    l5ObsSigma_mono L (l6Exh_mono W (Nat.add_le_add_left hjj' _))
  have hlim := condIndepEv_iSup_of_monotone hG'm hAjm (fun _ => hB'm) hAmono monotone_const hj
  rw [iSup_const] at hlim
  refine hlim.mono ?_ le_rfl
  refine (exists_mem_l6Exh_iSup W.isOpen).trans (iSup_le fun j => ?_)
  exact (l6ObsSigma_mono_l6Exh L W (Nat.le_add_left j j₀)).trans
    (le_iSup (fun j => l5ObsSigma L (l6Exh W (j₀ + j))) j)

end SupercriticalLQGUniqueness.B2.PfeLocal
