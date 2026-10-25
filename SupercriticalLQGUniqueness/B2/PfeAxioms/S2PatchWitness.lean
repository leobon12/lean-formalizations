import SupercriticalLQGUniqueness.B2.PfeAxioms.S2GammaLower
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLowerLocalized

 




















set_option autoImplicit false
noncomputable section

open Set Filter Topology TopologicalSpace MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.DFGPS.L217

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open Classical

 

theorem coe_ennreal_iInf_eq {ι : Sort*} (f : ι → ℝ≥0∞) :
    (((⨅ i, f i : ℝ≥0∞)) : EReal) = ⨅ i, ((f i : ℝ≥0∞) : EReal) := by
  apply le_antisymm
  · exact le_iInf fun i => EReal.coe_ennreal_le_coe_ennreal_iff.2 (iInf_le f i)
  · set L : EReal := ⨅ i, ((f i : ℝ≥0∞) : EReal)
    have hL0 : 0 ≤ L := le_iInf fun i => EReal.coe_ennreal_nonneg _
    rw [← EReal.coe_toENNReal hL0]
    refine EReal.coe_ennreal_le_coe_ennreal_iff.2 (le_iInf fun i => ?_)
    have h := EReal.toENNReal_le_toENNReal (iInf_le (fun i => ((f i : ℝ≥0∞) : EReal)) i)
    rwa [EReal.toENNReal_coe] at h

theorem coe_ennreal_iSup_eq {ι : Sort*} [Nonempty ι] (f : ι → ℝ≥0∞) :
    (((⨆ i, f i : ℝ≥0∞)) : EReal) = ⨆ i, ((f i : ℝ≥0∞) : EReal) := by
  apply le_antisymm
  · set S : EReal := ⨆ i, ((f i : ℝ≥0∞) : EReal)
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have hS0 : 0 ≤ S :=
      (EReal.coe_ennreal_nonneg (f i₀)).trans (le_iSup (fun i => ((f i : ℝ≥0∞) : EReal)) i₀)
    rw [← EReal.coe_toENNReal hS0]
    refine EReal.coe_ennreal_le_coe_ennreal_iff.2 (iSup_le fun i => ?_)
    have h := EReal.toENNReal_le_toENNReal (le_iSup (fun i => ((f i : ℝ≥0∞) : EReal)) i)
    rwa [EReal.toENNReal_coe] at h
  · exact iSup_le fun i => EReal.coe_ennreal_le_coe_ennreal_iff.2 (le_iSup f i)

theorem coe_ennreal_liminf_eq (u : ℕ → ℝ≥0∞) :
    ((liminf u atTop : ℝ≥0∞) : EReal) = liminf (fun n => ((u n : ℝ≥0∞) : EReal)) atTop :=
  EReal.coe_ennreal_strictMono.monotone.map_liminf_of_continuousAt u
    continuous_coe_ennreal_ereal.continuousAt

 

 

def locLFPP (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (n : ℕ) (g : DistC) : LSCMetric :=
  PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (locMollifyC (ε n : ℝ) (ε n).property g)

 
def patchBall (k : ℕ) : Set ℂ := Metric.ball 0 ((k : ℝ) + 1)

theorem isOpen_patchBall (k : ℕ) : IsOpen (patchBall k) := Metric.isOpen_ball

theorem isBounded_patchBall (k : ℕ) : Bornology.IsBounded (patchBall k) :=
  Metric.isBounded_ball

 
def patchFun (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (k : ℕ) (g : DistC) (n : ℕ) (p : ℂ × ℂ) : EReal :=
  if hp : p.1 ∈ patchBall k ∧ p.2 ∈ patchBall k then
    (((locLFPP ξ m ε n g).internal (patchBall k) (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩) : ℝ≥0∞) : EReal)
  else ⊤

 
def patchApprox (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (k : ℕ) (g : DistC) : LSCFun :=
  gammaLower (patchFun ξ m ε k g)

 

def patchLimit (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (g : DistC) : LSCFun :=
  limUnder atTop (fun k => patchApprox ξ m ε k g)

 

def patchLocus (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) : Set DistC :=
  {g | (∃ f : LSCFun, Tendsto (fun k => patchApprox ξ m ε k g) atTop (𝓝 f)) ∧
    IsMetricLSCFun (patchLimit ξ m ε g)}

 

def patchWitness (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (g : DistC) : LSCMetric :=
  if hg : g ∈ patchLocus ξ m ε then metricOfLSCFun (patchLimit ξ m ε g) hg.2
  else LscTop.euclideanLSCMetric

 

theorem ballInf_patchFun (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (k : ℕ) (g : DistC) (n : ℕ) {x y : ℂ}
    (hx : x ∈ patchBall k) (hy : y ∈ patchBall k) (ρ : ℝ) :
    ballInf (patchFun ξ m ε k g) n (x, y) ρ =
      ((neighborhoodInternal (locLFPP ξ m ε n g) (patchBall k) ⟨x, hx⟩ ⟨y, hy⟩ ρ :
        ℝ≥0∞) : EReal) := by
  unfold ballInf neighborhoodInternal
  simp_rw [coe_ennreal_iInf_eq]
  apply le_antisymm
  · refine le_iInf fun u => le_iInf fun hu => le_iInf fun v => le_iInf fun hv => ?_
    have hmem : ((u : ℂ), (v : ℂ)) ∈ Metric.ball (x, y) ρ := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt hu hv
    refine (iInf₂_le _ hmem).trans (le_of_eq ?_)
    simp only [patchFun, dif_pos (And.intro u.property v.property)]
  · refine le_iInf₂ fun p hp => ?_
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hp
    unfold patchFun
    split_ifs with hpV
    · exact iInf_le_of_le ⟨p.1, hpV.1⟩ <| iInf_le_of_le hp.1 <|
        iInf_le_of_le ⟨p.2, hpV.2⟩ <| iInf_le_of_le hp.2 le_rfl
    · exact le_top

 

theorem patchApprox_apply_of_mem (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (k : ℕ) (g : DistC) {x y : ℂ}
    (hx : x ∈ patchBall k) (hy : y ∈ patchBall k) :
    (patchApprox ξ m ε k g).1 (x, y) =
      ((lowerNeighborhoodObservable (fun n => locLFPP ξ m ε n g) (patchBall k)
        ⟨x, hx⟩ ⟨y, hy⟩ : ℝ≥0∞) : EReal) := by
  change gammaLowerFun (patchFun ξ m ε k g) (x, y) = _
  unfold gammaLowerFun lowerNeighborhoodObservable
  rw [coe_ennreal_iSup_eq]
  congr 1
  funext j
  rw [coe_ennreal_liminf_eq]
  congr 1
  funext n
  exact ballInf_patchFun ξ m ε k g n hx hy _

 

theorem measurable_locLFPP (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (n : ℕ) : Measurable (locLFPP ξ m ε n) :=
  measurable_normalizedLocalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ε n : ℝ) (ε n).property

theorem measurable_openInf_patchFun (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (k n : ℕ) {O : Set (ℂ × ℂ)} (_hO : IsOpen O) :
    Measurable fun g => openInf (patchFun ξ m ε k g) n O := by
  let V := patchBall k
  let S : Set (V × V) := {p | ((p.1 : ℂ), (p.2 : ℂ)) ∈ O}
  have heq : ∀ g, openInf (patchFun ξ m ε k g) n O =
      ⨅ p : S, ((((locLFPP ξ m ε n g).internal V (p.1.1, p.1.2)) : ℝ≥0∞) : EReal) := by
    intro g
    unfold openInf
    apply le_antisymm
    · refine le_iInf fun p => (iInf₂_le (f := fun q (_ : q ∈ O) => patchFun ξ m ε k g n q)
        ((p.1.1 : ℂ), (p.1.2 : ℂ)) p.2).trans (le_of_eq ?_)
      simp only [patchFun]
      rw [dif_pos (⟨p.1.1.property, p.1.2.property⟩ :
        (p.1.1 : ℂ) ∈ patchBall k ∧ (p.1.2 : ℂ) ∈ patchBall k)]
    · refine le_iInf₂ fun q hq => ?_
      unfold patchFun
      split_ifs with hqV
      · exact iInf_le_of_le ⟨(⟨q.1, hqV.1⟩, ⟨q.2, hqV.2⟩), hq⟩ le_rfl
      · exact le_top
  simp_rw [heq]
  have hfun : (fun g : DistC => ⨅ p : S,
      ((((locLFPP ξ m ε n g).internal V (p.1.1, p.1.2)) : ℝ≥0∞) : EReal)) =
      (⨅ p : S, fun g : DistC =>
        ((((locLFPP ξ m ε n g).internal V (p.1.1, p.1.2)) : ℝ≥0∞) : EReal)) := by
    funext g
    simp only [iInf_apply]
  rw [hfun]
  apply measurable_iInf_of_upperSemicontinuous
  · intro p
    let O' : TopologicalSpace.Opens ℂ := ⟨V, isOpen_patchBall k⟩
    have hm := (Uniqueness.Toolkit.CountableBase.internalBoundedOpen_borel
      (isOpen_patchBall k) (isBounded_patchBall k) (p.1.1 : O') (p.1.2 : O')).comp
      (measurable_locLFPP ξ m ε n)
    exact measurable_coe_ennreal_ereal.comp hm
  · intro g
    exact (continuous_coe_ennreal_ereal.comp
      ((continuous_normalizedLFPPMetric_internal (ξ : ℝ) (m (ε n))
        (locMollifyC (ε n : ℝ) (ε n).property g) (isOpen_patchBall k)).comp
        continuous_subtype_val)).upperSemicontinuous

theorem measurable_patchApprox [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (k : ℕ) : Measurable (patchApprox ξ m ε k) :=
  measurable_gammaLower (fun g => patchFun ξ m ε k g)
    fun n _ hO => measurable_openInf_patchFun ξ m ε k n hO

theorem measurable_patchLimit [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) : Measurable (patchLimit ξ m ε) :=
  LscTop.measurable_limUnder fun k => measurable_patchApprox ξ m ε k

 
theorem measurableSet_patchLocus [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) : MeasurableSet (patchLocus ξ m ε) :=
  (LscTop.measurableSet_exists_tendsto fun k => measurable_patchApprox ξ m ε k).inter
    (measurable_patchLimit ξ m ε measurableSet_isMetricLSCFun)

theorem toLSCFun_patchWitness (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (g : DistC) :
    (patchWitness ξ m ε g).toLSCFun =
      (patchLocus ξ m ε).piecewise (patchLimit ξ m ε)
        (fun _ => LscTop.euclideanLSCMetric.toLSCFun) g := by
  by_cases hg : g ∈ patchLocus ξ m ε
  · rw [Set.piecewise_eq_of_mem _ _ _ hg]
    simp only [patchWitness, dif_pos hg]
    exact toLSCFun_metricOfLSCFun _ _
  · rw [Set.piecewise_eq_of_notMem _ _ _ hg]
    simp only [patchWitness, dif_neg hg]

 
theorem measurable_patchWitness (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) : Measurable (patchWitness ξ m ε) := by
  let _ : MeasurableSpace LSCFun := borel LSCFun
  have _ : BorelSpace LSCFun := ⟨rfl⟩
  rw [LscTop.measurable_iff_toLSCFun]
  have h : (fun g => (patchWitness ξ m ε g).toLSCFun) =
      (patchLocus ξ m ε).piecewise (patchLimit ξ m ε)
        (fun _ => LscTop.euclideanLSCMetric.toLSCFun) := by
    funext g
    exact toLSCFun_patchWitness ξ m ε g
  rw [h]
  exact (measurable_patchLimit ξ m ε).piecewise (measurableSet_patchLocus ξ m ε)
    measurable_const

 

theorem patchWitness_eq_of_tendsto (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) {g : DistC} {D : LSCMetric}
    (h : Tendsto (fun k => patchApprox ξ m ε k g) atTop (𝓝 D.toLSCFun)) :
    g ∈ patchLocus ξ m ε ∧ patchWitness ξ m ε g = D := by
  have hlim : patchLimit ξ m ε g = D.toLSCFun := h.limUnder_eq
  have hg : g ∈ patchLocus ξ m ε :=
    ⟨⟨_, h⟩, by rw [hlim]; exact isMetricLSCFun_toLSCFun D⟩
  refine ⟨hg, LscTop.toLSCFun_injective ?_⟩
  rw [toLSCFun_patchWitness, Set.piecewise_eq_of_mem _ _ _ hg, hlim]

 

 


theorem tendsto_lscFun_of_sandwich (Γ : ℕ → LSCFun) (D : LSCMetric) (R : ℕ → ℝ)
    (hR : Tendsto R atTop atTop)
    (hlow : ∀ k (p : ℂ × ℂ), ‖p.1‖ < R k → ‖p.2‖ < R k →
      ((D p : ℝ≥0∞) : EReal) ≤ (Γ k).1 p)
    (hupp : ∀ p, limsup (fun k => (Γ k).1 p) atTop ≤ ((D p : ℝ≥0∞) : EReal)) :
    Tendsto Γ atTop (𝓝 D.toLSCFun) := by
  have hDlsc := lowerSemicontinuous_iff_seq.1 D.toLSCFun.2
  have hlow' : ∀ (p : ℕ → ℂ × ℂ) (q : ℂ × ℂ), Tendsto p atTop (𝓝 q) →
      ((D q : ℝ≥0∞) : EReal) ≤ liminf (fun k => (Γ k).1 (p k)) atTop := by
    intro p q hp
    have hb : ∀ᶠ k in atTop, ‖(p k).1‖ < R k ∧ ‖(p k).2‖ < R k := by
      have h1 : Tendsto (fun k => ‖(p k).1‖) atTop (𝓝 ‖q.1‖) :=
        ((continuous_fst.tendsto q).comp hp).norm
      have h2 : Tendsto (fun k => ‖(p k).2‖) atTop (𝓝 ‖q.2‖) :=
        ((continuous_snd.tendsto q).comp hp).norm
      have hR1 := hR.eventually_gt_atTop (max ‖q.1‖ ‖q.2‖ + 1)
      filter_upwards [h1.eventually (gt_mem_nhds (lt_add_one ‖q.1‖)),
        h2.eventually (gt_mem_nhds (lt_add_one ‖q.2‖)), hR1] with k hk1 hk2 hk3
      exact ⟨by linarith [le_max_left ‖q.1‖ ‖q.2‖],
        by linarith [le_max_right ‖q.1‖ ‖q.2‖]⟩
    calc ((D q : ℝ≥0∞) : EReal) = D.toLSCFun.1 q := rfl
      _ ≤ liminf (fun k => D.toLSCFun.1 (p k)) atTop := hDlsc p q hp
      _ ≤ liminf (fun k => (Γ k).1 (p k)) atTop :=
          Filter.liminf_le_liminf (hb.mono fun k hk => hlow k (p k) hk.1 hk.2)
  apply LSCFun.tendsto_of_lscTendsto
  refine ⟨hlow', fun q => ⟨fun _ => q, tendsto_const_nhds, ?_⟩⟩
  exact tendsto_of_le_liminf_of_limsup_le (hlow' (fun _ => q) q tendsto_const_nhds)
    (hupp q)

end SupercriticalLQGUniqueness.B2.PfeAxioms
