import HigherDimLQGMetric.Bilip.Uniform

/-!
# Uniform shell bounds for an arbitrary tight family

The index can contain both a radius and a centre.  This is the part of
MA5 A20(b) independent of translation invariance in law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Filter Topology Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ} {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {X : ι → Ω → C(Rd d × Rd d, ℝ)} {S : Set ι}

/-- Compact-law control with the arbitrary-index `TightFamily` interface. -/
theorem bilip_tightFamily_mapsTo (hT : TightFamily P X S)
    {A : ℕ → Set (Rd d × Rd d)} (hA : ∀ n, IsCompact (A n))
    (hAa : Antitone A) {U : ℕ → Set ℝ} (hU : ∀ n, IsOpen (U n))
    (hUm : Monotone U)
    (hmet : ∀ g : C(Rd d × Rd d, ℝ), IsContinuousMetric g →
      ∀ x ∈ ⋂ n, A n, ∃ n, g x ∈ U n)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n, ∀ i ∈ S, P {ω | ¬ MapsTo (X i ω) (A n) (U n)} < ε := by
  have hS : IsCompact (closure {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ i ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (X i)}) := by
    refine isCompact_closure_of_isTightMeasureSet (hT.2.1.subset ?_)
    rintro _ ⟨ν, ⟨i, hi, hν⟩, rfl⟩
    exact ⟨i, hi, hν⟩
  let C : ℕ → Set C(Rd d × Rd d, ℝ) := fun n => {g | ¬ MapsTo g (A n) (U n)}
  have hCc : ∀ n, IsClosed (C n) := fun n =>
    LQGMetric.GM.Tight.isClosed_setOf_not_mapsTo (hA n) (hU n)
  have hCa : Antitone C := fun m n hmn g hg hg' =>
    hg (fun x hx => hUm hmn (hg' (hAa hmn hx)))
  have h0 : ∀ μ ∈ closure {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ i ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (X i)},
      (μ : Measure C(Rd d × Rd d, ℝ)) (⋂ n, C n) = 0 := by
    intro μ hμ
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hT.2.2 μ hμ] with g hg hmem
    obtain ⟨x, hx, hxU⟩ := LQGMetric.GM.Tight.exists_mem_iInter_of_not_mapsTo
      hA hAa hU hUm (d := g) (mem_iInter.1 hmem)
    obtain ⟨n, hn⟩ := hmet g hg.1 x hx
    exact hxU n hn
  obtain ⟨n, hn⟩ := LQGMetric.GM.Tight.exists_measure_lt_of_isCompact_closure
    hS hCc hCa h0 hε
  refine ⟨n, fun i hi => ?_⟩
  have hmeas := hT.1 i hi
  have hprob : IsProbabilityMeasure (P.map (X i)) := inferInstance
  have heq : P {ω | ¬ MapsTo (X i ω) (A n) (U n)} =
      (P.map (X i)) (C n) := by
    rw [Measure.map_apply_of_aemeasurable hmeas (hCc n).measurableSet]
    rfl
  rw [heq]
  exact hn ⟨P.map (X i), hprob⟩ ⟨i, hi, rfl⟩

private theorem cmetric_nonneg {g : C(Rd d × Rd d, ℝ)} (hg : IsContinuousMetric g)
    (p : Rd d × Rd d) : 0 ≤ g p := by
  have ht := hg.triangle p.1 p.2 p.1
  rw [hg.self_eq_zero, hg.symm p.2 p.1] at ht
  linarith

theorem bilip_tightFamily_lower_offDiag (hT : TightFamily P X S)
    {A : Set (Rd d × Rd d)} (hA : IsCompact A)
    (hAd : ∀ p ∈ A, p.1 ≠ p.2) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ ∀ i ∈ S, P {ω | ¬ ∀ p ∈ A, s < X i ω p} < ε := by
  have hanti : Antitone (fun _ : ℕ => A) := fun _ _ _ => le_rfl
  have hmono : Monotone (fun n : ℕ => Ioi ((1 : ℝ) / (n + 1))) := by
    intro m n hmn
    exact Ioi_subset_Ioi (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.succ_le_succ hmn))
  obtain ⟨n, hn⟩ := bilip_tightFamily_mapsTo hT (A := fun _ => A)
    (fun _ => hA) hanti (U := fun n => Ioi ((1 : ℝ) / (n + 1)))
    (fun _ => isOpen_Ioi) hmono
    (by
      intro g hg x hx
      have hxA : x ∈ A := mem_iInter.1 hx 0
      have hpos : 0 < g x := lt_of_le_of_ne (cmetric_nonneg hg x)
        (fun h0 => hAd x hxA (hg.eq_of_eq_zero x.1 x.2 h0.symm))
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
      exact ⟨k, hk⟩) hε
  refine ⟨1 / (n + 1), by positivity, ?_⟩
  intro i hi
  exact hn i hi

private theorem compact_near_diag {K : Set (Rd d)} (hK : IsCompact K) (b : ℝ) :
    IsCompact {p : Rd d × Rd d | p ∈ K ×ˢ K ∧ ‖p.1 - p.2‖ ≤ b} :=
  (hK.prod hK).inter_right
    (isClosed_le (continuous_fst.sub continuous_snd).norm continuous_const)

theorem bilip_tightFamily_modulus (hT : TightFamily P X S)
    {K : Set (Rd d)} (hK : IsCompact K)
    {a : ℝ} (ha : 0 < a) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ ∀ i ∈ S,
      P {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → X i ω (u, v) < a} < ε := by
  have hanti : Antitone (fun n : ℕ =>
      {p : Rd d × Rd d | p ∈ K ×ˢ K ∧ ‖p.1 - p.2‖ ≤ 1 / (n + 1)}) := by
    intro m n hmn p hp
    exact ⟨hp.1, hp.2.trans
      (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn))⟩
  obtain ⟨n, hn⟩ := bilip_tightFamily_mapsTo hT
    (A := fun n => {p : Rd d × Rd d |
      p ∈ K ×ˢ K ∧ ‖p.1 - p.2‖ ≤ 1 / (n + 1)})
    (fun n => compact_near_diag hK _) hanti
    (U := fun _ => Iio a) (fun _ => isOpen_Iio) (fun _ _ _ => le_rfl)
    (by
      intro g hg x hx
      have h0 : ‖x.1 - x.2‖ ≤ 0 := by
        refine le_of_forall_pos_le_add fun δ hδ => ?_
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
        exact ((mem_iInter.1 hx n).2.trans hn.le).trans (by linarith)
      have hxy : x.1 = x.2 := sub_eq_zero.1 (norm_le_zero_iff.1 h0)
      refine ⟨0, ?_⟩
      show g x < a
      obtain ⟨u, v⟩ := x
      simp only at hxy
      subst v
      simpa only [hg.self_eq_zero] using ha) hε
  refine ⟨1 / (n + 1), by positivity, fun i hi => ?_⟩
  simpa [MapsTo, Set.mem_prod, Set.mem_ofPred_eq] using hn i hi

theorem bilip_tightFamily_across_lower
    {G : ι → Ω → ContMetric d} (hT : TightFamily P (fun i ω => (G i ω).1) S)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ i ∈ S,
      P {ω | acrossDist (G i ω) 0 (1 / 2) 1 < ENNReal.ofReal a} < ε := by
  have hOff : ∀ p : Rd d × Rd d,
      p ∈ sphere (0 : Rd d) (1 / 2) ×ˢ sphere (0 : Rd d) 1 → p.1 ≠ p.2 := by
    intro p hp heq
    have h1 : dist p.1 (0 : Rd d) = 1 / 2 := by
      simpa only [Metric.mem_sphere] using hp.1
    have h2 : dist p.2 (0 : Rd d) = 1 := by
      simpa only [Metric.mem_sphere] using hp.2
    rw [heq] at h1
    linarith
  obtain ⟨a, ha, H⟩ := bilip_tightFamily_lower_offDiag hT
    ((isCompact_sphere (0 : Rd d) (1 / 2)).prod (isCompact_sphere 0 1)) hOff hε
  refine ⟨a, ha, fun i hi => ?_⟩
  refine lt_of_le_of_lt (measure_mono ?_) (H i hi)
  intro ω hbad hgood
  have hle : ENNReal.ofReal a ≤ acrossDist (G i ω) 0 (1 / 2) 1 := by
    unfold acrossDist
    refine le_iInf fun u => le_iInf fun hu => le_iInf fun v => le_iInf fun hv => ?_
    exact ENNReal.ofReal_le_ofReal (hgood (u, v) ⟨hu, hv⟩).le
  exact (not_lt_of_ge hle) hbad

theorem bilip_tightFamily_sphereDiam_upper (hd : 2 ≤ d)
    {G : ι → Ω → ContMetric d}
    (hT : TightFamily P (fun i ω => (G i ω).1) S)
    (hLen : ∀ i ∈ S, ∀ᵐ ω ∂P, (G i ω).IsLength)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ∈ S,
      P {ω | ENNReal.ofReal C < sphereDiam (G i ω) 0 1} < ε := by
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  let K : Set (Rd d) := sphere 0 1
  let V : Set (Rd d) := ann 0 (1 / 2) 2
  obtain ⟨a, ha, Hsep⟩ := bilip_tightFamily_lower_offDiag hT
    ((isCompact_sphere (0 : Rd d) 1).prod compact_frontier_unit_ann)
    sphere_frontier_offDiag hε2
  obtain ⟨b, hb, Hmod⟩ := bilip_tightFamily_modulus hT
    (isCompact_sphere (0 : Rd d) 1) ha hε2
  obtain ⟨N, hN⟩ := compact_connected_chain_bound
    (isCompact_sphere (0 : Rd d) 1) (isConnected_unit_sphere hd) hb
  let C : ℝ := (N + 1) * a
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro i hi
  have hgood (ω : Ω) (hl : (G i ω).IsLength)
      (hs : ∀ p ∈ K ×ˢ frontier V, a < (G i ω).1 p)
      (hm : ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → (G i ω).1 (u, v) < a) :
      sphereDiam (G i ω) 0 1 ≤ ENNReal.ofReal C := by
    have hsep' : ∀ u ∈ K, ∀ v ∈ frontier V, a < (G i ω).1 (u, v) :=
      fun u hu v hv => hs (u, v) ⟨hu, hv⟩
    have hdiam := sphereDiam_le_of_modulus N hN (G i ω) hl ha hsep' hm
    have hle : (N : ℝ≥0∞) * ENNReal.ofReal a ≤ ENNReal.ofReal C := by
      have hNa : (N : ℝ) * a ≤ C := by dsimp [C]; nlinarith
      calc
        (N : ℝ≥0∞) * ENNReal.ofReal a = ENNReal.ofReal ((N : ℝ) * a) := by
          rw [ENNReal.ofReal_mul (p := (N : ℝ)) (by positivity), ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hNa
    exact hdiam.trans hle
  have hbad : P {ω | ENNReal.ofReal C < sphereDiam (G i ω) 0 1} ≤
      P ({ω | ¬ ∀ p ∈ K ×ˢ frontier V, a < (G i ω).1 p} ∪
        {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → (G i ω).1 (u, v) < a}) := by
    refine measure_mono_ae ?_
    filter_upwards [hLen i hi] with ω hl hω
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hnot
    exact (not_lt_of_ge (hgood ω hl hnot.1 hnot.2)) hω
  calc
    P {ω | ENNReal.ofReal C < sphereDiam (G i ω) 0 1} ≤ P _ := hbad
    _ ≤ P {ω | ¬ ∀ p ∈ K ×ˢ frontier V, a < (G i ω).1 p} +
        P {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → (G i ω).1 (u, v) < a} :=
      measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add (Hsep i hi) (Hmod i hi)
    _ = ε := ENNReal.add_halves ε

theorem bilip_uniformShellBounds_family (hd : 2 ≤ d)
    {G : ι → Ω → ContMetric d}
    (hT : TightFamily P (fun i ω => (G i ω).1) S)
    (hLen : ∀ i ∈ S, ∀ᵐ ω ∂P, (G i ω).IsLength)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ A : ℝ, 1 < A ∧ ∀ i ∈ S,
      P {ω | acrossDist (G i ω) 0 (1 / 2) 1 < ENNReal.ofReal A⁻¹} < η ∧
      P {ω | ENNReal.ofReal A < sphereDiam (G i ω) 0 1} < η := by
  obtain ⟨a, ha, hlo⟩ := bilip_tightFamily_across_lower hT hη
  obtain ⟨b, hb, hup⟩ := bilip_tightFamily_sphereDiam_upper hd hT hLen hη
  let A : ℝ := max 2 (max a⁻¹ b)
  have hA : 1 < A := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hAi : A⁻¹ ≤ a := by
    have haA : a⁻¹ ≤ A := (le_max_left _ _).trans (le_max_right _ _)
    simpa only [one_div] using
      ((one_div_le (by linarith : 0 < A) ha).mpr (by simpa only [one_div] using haA))
  have hbA : b ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨A, hA, ?_⟩
  intro i hi
  constructor
  · refine lt_of_le_of_lt (measure_mono ?_) (hlo i hi)
    intro ω hω
    exact lt_of_lt_of_le hω (ENNReal.ofReal_le_ofReal hAi)
  · refine lt_of_le_of_lt (measure_mono ?_) (hup i hi)
    intro ω hω
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hbA) hω

omit [IsProbabilityMeasure P] in
theorem bilip_tightFamily_congr_on
    {Y : ι → Ω → C(Rd d × Rd d, ℝ)}
    (hXY : ∀ i ∈ S, X i = Y i) (hT : TightFamily P X S) :
    TightFamily P Y S := by
  have hset : {μ | ∃ i ∈ S, μ = P.map (X i)} =
      {μ | ∃ i ∈ S, μ = P.map (Y i)} := by
    ext μ
    constructor
    · rintro ⟨i, hi, hμ⟩
      exact ⟨i, hi, by simpa only [hXY i hi] using hμ⟩
    · rintro ⟨i, hi, hμ⟩
      exact ⟨i, hi, by simpa only [← hXY i hi] using hμ⟩
  have hprob : {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
        ∃ i ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (X i)} =
      {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
        ∃ i ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (Y i)} := by
    ext ν
    constructor
    · rintro ⟨i, hi, hν⟩
      exact ⟨i, hi, by simpa only [hXY i hi] using hν⟩
    · rintro ⟨i, hi, hν⟩
      exact ⟨i, hi, by simpa only [← hXY i hi] using hν⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [← hXY i hi]
    exact hT.1 i hi
  · rw [← hset]
    exact hT.2.1
  · intro μ hμ
    exact hT.2.2 μ (by simpa only [hprob] using hμ)

omit [IsProbabilityMeasure P] in
/-- The map-law form of A20(a) transfers origin tightness to all centres. -/
theorem bilip_tightFamily_centres_of_law
    {Y : ℝ → Ω → C(Rd d × Rd d, ℝ)}
    {Z : (ℝ × Rd d) → Ω → C(Rd d × Rd d, ℝ)}
    (hY : TightFamily P Y (Ioi 0))
    (hZm : ∀ r : ℝ, 0 < r → ∀ z : Rd d, AEMeasurable (Z (r, z)) P)
    (hLaw : ∀ r : ℝ, 0 < r → ∀ z : Rd d,
      P.map (Z (r, z)) = P.map (Y r)) :
    TightFamily P Z {rz : ℝ × Rd d | 0 < rz.1} := by
  have hset : {μ | ∃ rz ∈ {rz : ℝ × Rd d | 0 < rz.1}, μ = P.map (Z rz)} =
      {μ | ∃ r ∈ Ioi (0 : ℝ), μ = P.map (Y r)} := by
    ext μ
    constructor
    · rintro ⟨⟨r, z⟩, hr, hμ⟩
      exact ⟨r, hr, by rw [← hLaw r hr z]; exact hμ⟩
    · rintro ⟨r, hr, hμ⟩
      exact ⟨(r, 0), hr, by rw [hLaw r hr 0]; exact hμ⟩
  have hprob : {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
        ∃ rz ∈ {rz : ℝ × Rd d | 0 < rz.1},
          (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (Z rz)} =
      {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
        ∃ r ∈ Ioi (0 : ℝ),
          (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (Y r)} := by
    ext ν
    constructor
    · rintro ⟨⟨r, z⟩, hr, hν⟩
      exact ⟨r, hr, by rw [← hLaw r hr z]; exact hν⟩
    · rintro ⟨r, hr, hν⟩
      exact ⟨(r, 0), hr, by rw [hLaw r hr 0]; exact hν⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨r, z⟩ hr
    exact hZm r hr z
  · rw [hset]
    exact hY.2.1
  · intro μ hμ
    exact hY.2.2 μ (by simpa only [← hprob] using hμ)

/-- A20(b) simultaneously at every centre and scale, given tightness of the
joint centred family.  A20(a) supplies this tightness from the origin family. -/
theorem bilip_uniformShellBounds_allCentres (hd : 2 ≤ d)
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℝ)
    (h : Ω → DistRd d) (D : Ω → ContMetric d) (c : ℝ → ℝ)
    (hc : ∀ r : ℝ, 0 < r → 0 < c r)
    (hT : TightFamily P
      (fun rz ω => scaledField ξ (fun _ => D ω) c rz.1 rz.2 (h ω))
      {rz : ℝ × Rd d | 0 < rz.1})
    (hLen : ∀ᵐ ω ∂P, (D ω).IsLength)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ A : ℝ, 1 < A ∧ ∀ (r : ℝ), 0 < r → ∀ z : Rd d,
      P {ω | ENNReal.ofReal ((c r)⁻¹ * Real.exp (-ξ * sphereAvg (h ω) r z)) *
          acrossDist (D ω) z (r / 2) r < ENNReal.ofReal A⁻¹} < η ∧
      P {ω | ENNReal.ofReal A <
          ENNReal.ofReal ((c r)⁻¹ * Real.exp (-ξ * sphereAvg (h ω) r z)) *
            sphereDiam (D ω) z r} < η := by
  let S : Set (ℝ × Rd d) := {rz | 0 < rz.1}
  let G : (ℝ × Rd d) → Ω → ContMetric d := fun rz ω =>
    if hr : 0 < rz.1 then
      weakScaledMetric ξ (fun _ => D ω) c (h ω) hr rz.2 (hc rz.1 hr)
    else D ω
  have hGfun (rz : ℝ × Rd d) (hr : rz ∈ S) :
      (fun ω => (G rz ω).1) =
        (fun ω => scaledField ξ (fun _ => D ω) c rz.1 rz.2 (h ω)) := by
    have hr0 : 0 < rz.1 := hr
    funext ω
    dsimp [G]
    rw [dite_eq_left hr0]
    exact ContinuousMap.ext fun p =>
      weakScaledMetric_apply ξ (fun _ => D ω) c (h ω) hr0 rz.2 (hc rz.1 hr0) p
  have hTG : TightFamily P (fun rz ω => (G rz ω).1) S :=
    bilip_tightFamily_congr_on (fun rz hr => (hGfun rz hr).symm) hT
  have hGLen : ∀ rz ∈ S, ∀ᵐ ω ∂P, (G rz ω).IsLength := by
    intro rz hr
    have hr0 : 0 < rz.1 := hr
    filter_upwards [hLen] with ω hω
    dsimp [G]
    rw [dite_eq_left hr0]
    exact weakScaledMetric_isLength ξ (fun _ => D ω) c (h ω)
      hr0 rz.2 (hc rz.1 hr0) hω
  obtain ⟨A, hA, hB⟩ := bilip_uniformShellBounds_family
    (P := P) (S := S) hd hTG hGLen hη
  refine ⟨A, hA, ?_⟩
  intro r hr z
  obtain ⟨hlo, hup⟩ := hB (r, z) hr
  constructor
  · convert hlo using 1
    congr 1
    ext ω
    dsimp [G]
    rw [dite_eq_left hr, weakScaledMetric_acrossDist]
  · convert hup using 1
    congr 1
    ext ω
    dsimp [G]
    rw [dite_eq_left hr, weakScaledMetric_sphereDiam]

/-- A20(b) in the form consumed by the copies argument: origin tightness from
`L6f_tightScales` and the scaled-map law equality from A20(a) give a single
constant for all centres and all scales. -/
theorem bilip_uniformShellBounds_limit_allCentres (hd : 2 ≤ d)
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℝ)
    (h : Ω → DistRd d) (D : Ω → ContMetric d) (c : ℝ → ℝ)
    (hc : ∀ r : ℝ, 0 < r → 0 < c r)
    (hT : TightFamily P
      (fun r ω => normalizedAtScale ξ (fun _ => D ω) c (h ω) r) (Ioi 0))
    (hZm : ∀ r : ℝ, 0 < r → ∀ z : Rd d,
      AEMeasurable (fun ω => scaledField ξ (fun _ => D ω) c r z (h ω)) P)
    (hLaw : ∀ r : ℝ, 0 < r → ∀ z : Rd d,
      P.map (fun ω => scaledField ξ (fun _ => D ω) c r z (h ω)) =
        P.map (fun ω => normalizedAtScale ξ (fun _ => D ω) c (h ω) r))
    (hLen : ∀ᵐ ω ∂P, (D ω).IsLength)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ A : ℝ, 1 < A ∧ ∀ (r : ℝ), 0 < r → ∀ z : Rd d,
      P {ω | ENNReal.ofReal ((c r)⁻¹ * Real.exp (-ξ * sphereAvg (h ω) r z)) *
          acrossDist (D ω) z (r / 2) r < ENNReal.ofReal A⁻¹} < η ∧
      P {ω | ENNReal.ofReal A <
          ENNReal.ofReal ((c r)⁻¹ * Real.exp (-ξ * sphereAvg (h ω) r z)) *
            sphereDiam (D ω) z r} < η := by
  have hZT : TightFamily P
      (fun rz ω => scaledField ξ (fun _ => D ω) c rz.1 rz.2 (h ω))
      {rz : ℝ × Rd d | 0 < rz.1} :=
    bilip_tightFamily_centres_of_law hT hZm hLaw
  exact bilip_uniformShellBounds_allCentres hd P ξ h D c hc hZT hLen hη

end HigherDimLQGMetric
