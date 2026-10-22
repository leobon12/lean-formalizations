import HigherDimLQGMetric.Sharp.W2Around
import HigherDimLQGMetric.Shell.Across

/-!
# Deterministic multiscale shell geometry

The open-shell crossing extracted below is used to connect paths at adjacent
grid scales through `aroundDist`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric Filter Topology
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- A path travelling from inside one sphere to outside another contains a
reparameterized crossing of the open shell. Its image remains in the original
path image. -/
theorem w3_crossing_segment {P : ℝ → Rd d} {z : Rd d} {a b : ℝ}
    (hP : ContinuousOn P (Icc 0 1)) (hab : a < b)
    (ha : ‖P 0 - z‖ ≤ a) (hb : b ≤ ‖P 1 - z‖) :
    ∃ Q : ℝ → Rd d, IsShellCrossing z a b Q ∧ Q '' Icc 0 1 ⊆ P '' Icc 0 1 := by
  let f : ℝ → ℝ := fun t => ‖P t - z‖
  have hf : ContinuousOn f (Icc 0 1) := (hP.sub continuousOn_const).norm
  obtain ⟨t₂, ht₂, hft₂, hbef⟩ := exists_first_hit (P := f) hf
    (isClosed_Ici (a := b)) ⟨1, ⟨zero_le_one, le_rfl⟩, hb⟩
  have ht₂pos : 0 < t₂ := by
    rcases ht₂.1.eq_or_lt with h | h
    · rw [← h] at hft₂
      exact False.elim (not_lt_of_ge ha (hab.trans_le hft₂))
    · exact h
  have hft₂eq : f t₂ = b := by
    refine le_antisymm ?_ hft₂
    have hne : (𝓝[Ico 0 t₂] t₂).NeBot := right_nhdsWithin_Ico_neBot ht₂pos
    have hcw : ContinuousWithinAt f (Ico 0 t₂) t₂ :=
      (hf t₂ ht₂).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht₂.2))
    exact le_of_tendsto hcw (eventually_nhdsWithin_of_forall fun t ht =>
      (not_le.1 fun h => hbef t ht h).le)
  let S : Set ℝ := Icc 0 t₂ ∩ f ⁻¹' Iic a
  have hSc : IsClosed S :=
    (hf.mono (Icc_subset_Icc le_rfl ht₂.2)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨0, ⟨le_rfl, ht₂pos.le⟩, ha⟩
  have hSb : BddAbove S := ⟨t₂, fun t ht => ht.1.2⟩
  let t₁ := sSup S
  have ht₁S : t₁ ∈ S := hSc.csSup_mem hSne hSb
  have hft₁ : f t₁ ≤ a := ht₁S.2
  have hafter : ∀ t ∈ Ioc t₁ t₂, a < f t := fun t ht => by
    by_contra hc
    exact absurd (le_csSup hSb ⟨⟨ht₁S.1.1.trans ht.1.le, ht.2⟩,
      mem_Iic.2 (not_lt.1 hc)⟩) (not_le.2 ht.1)
  have ht₁₂ : t₁ < t₂ := by
    rcases ht₁S.1.2.eq_or_lt with h | h
    · rw [h, hft₂eq] at hft₁
      linarith only [hft₁, hab]
    · exact h
  have hft₁eq : f t₁ = a := by
    refine le_antisymm hft₁ ?_
    have hne : (𝓝[Ioc t₁ t₂] t₁).NeBot := left_nhdsWithin_Ioc_neBot ht₁₂
    have hcw : ContinuousWithinAt f (Ioc t₁ t₂) t₁ :=
      (hf t₁ ⟨ht₁S.1.1, ht₁S.1.2.trans ht₂.2⟩).mono
        (Ioc_subset_Icc_self.trans (Icc_subset_Icc ht₁S.1.1 ht₂.2))
    exact ge_of_tendsto hcw (eventually_nhdsWithin_of_forall fun t ht => (hafter t ht).le)
  have hbefore : ∀ t ∈ Ico t₁ t₂, f t < b := by
    intro t ht
    exact not_le.1 (hbef t ⟨ht₁S.1.1.trans ht.1, ht.2⟩)
  let φ : ℝ → ℝ := fun u => t₁ + (t₂ - t₁) * u
  have hφc : Continuous φ := by fun_prop
  have hφIcc : MapsTo φ (Icc 0 1) (Icc t₁ t₂) := by
    intro u hu
    dsimp [φ]
    constructor <;> nlinarith only [hu.1, hu.2, ht₁₂]
  have hφIoo : MapsTo φ (Ioo 0 1) (Ioo t₁ t₂) := by
    intro u hu
    dsimp [φ]
    constructor <;> nlinarith only [hu.1, hu.2, ht₁₂]
  let Q : ℝ → Rd d := P ∘ φ
  refine ⟨Q, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hP.mono (Icc_subset_Icc ht₁S.1.1 ht₂.2) |>.comp hφc.continuousOn hφIcc
  · simpa only [Q, Function.comp_apply, φ, mul_zero, add_zero, mem_sphere,
      dist_eq_norm] using hft₁eq
  · have hφ1 : φ 1 = t₂ := by dsimp [φ]; ring
    simpa only [Q, Function.comp_apply, hφ1, mem_sphere, dist_eq_norm] using hft₂eq
  · intro u hu
    have hφu := hφIoo hu
    have hlow := hafter (φ u) ⟨hφu.1, hφu.2.le⟩
    have hhigh := hbefore (φ u) ⟨hφu.1.le, hφu.2⟩
    exact ⟨hlow, hhigh⟩
  · rintro x ⟨u, hu, rfl⟩
    exact ⟨φ u, (Icc_subset_Icc ht₁S.1.1 ht₂.2) (hφIcc hu), rfl⟩

/-- Two paths that both cross the same shell can be linked inside a larger
domain at a cost controlled by the shell's around-distance. -/
theorem w3_link_crossing_paths (D : ContMetric d) {U : Set (Rd d)}
    {z : Rd d} {a b β η : ℝ} (hab : a < b) (hη : 0 < η)
    (hannU : ann z a b ⊆ U) (haround : aroundDist D z a b ≤ ENNReal.ofReal β)
    {P₁ P₂ : ℝ → Rd d} (hP₁ : ContinuousOn P₁ (Icc 0 1))
    (hP₂ : ContinuousOn P₂ (Icc 0 1))
    (hstart₁ : ‖P₁ 0 - z‖ ≤ a) (hfinish₁ : b ≤ ‖P₁ 1 - z‖)
    (hstart₂ : ‖P₂ 0 - z‖ ≤ a) (hfinish₂ : b ≤ ‖P₂ 1 - z‖) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      D.internal U (P₁ s) (P₂ t) ≤ ENNReal.ofReal β + ENNReal.ofReal η := by
  obtain ⟨Q₁, hQ₁, hQ₁P⟩ := w3_crossing_segment hP₁ hab hstart₁ hfinish₁
  obtain ⟨Q₂, hQ₂, hQ₂P⟩ := w3_crossing_segment hP₂ hab hstart₂ hfinish₂
  have hpair : (⨅ (s ∈ Ioo (0 : ℝ) 1) (t ∈ Ioo (0 : ℝ) 1),
      D.internal (ann z a b) (Q₁ s) (Q₂ t)) ≤ aroundDist D z a b := by
    unfold aroundDist
    exact le_iSup_of_le Q₁ (le_iSup_of_le Q₂
      (le_iSup_of_le hQ₁ (le_iSup_of_le hQ₂ le_rfl)))
  have hlt : (⨅ (s ∈ Ioo (0 : ℝ) 1) (t ∈ Ioo (0 : ℝ) 1),
      D.internal (ann z a b) (Q₁ s) (Q₂ t)) <
      ENNReal.ofReal β + ENNReal.ofReal η :=
    (hpair.trans haround).trans_lt (ENNReal.lt_add_right ENNReal.ofReal_ne_top
      (ne_of_gt (ENNReal.ofReal_pos.mpr hη)))
  simp only [iInf_lt_iff] at hlt
  obtain ⟨s, hs, t, ht, hst⟩ := hlt
  obtain ⟨s', hs', hs'eq⟩ := hQ₁P ⟨s, Ioo_subset_Icc_self hs, rfl⟩
  obtain ⟨t', ht', ht'eq⟩ := hQ₂P ⟨t, Ioo_subset_Icc_self ht, rfl⟩
  refine ⟨s', hs', t', ht', ?_⟩
  rw [hs'eq, ht'eq]
  exact (D.internal_anti hannU _ _).trans hst.le

/-- Any two points of a path have internal distance at most its total length
in a domain containing the path. -/
theorem w3_internal_le_path_len (D : ContMetric d) {U : Set (Rd d)}
    {P : ℝ → Rd d} (hP : ContinuousOn P (Icc 0 1))
    (hPU : MapsTo P (Icc 0 1) U) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    D.internal U (P s) (P t) ≤ D.len P 0 1 := by
  rcases le_total s t with hst | hts
  · exact (D.internal_le_len hst
      (hP.mono (Icc_subset_Icc hs.1 ht.2))
      (fun u hu => hPU ((Icc_subset_Icc hs.1 ht.2) hu))).trans
      (eVariationOn.mono _ (Icc_subset_Icc hs.1 ht.2))
  · rw [D.internal_comm]
    exact (D.internal_le_len hts
      (hP.mono (Icc_subset_Icc ht.1 hs.2))
      (fun u hu => hPU ((Icc_subset_Icc ht.1 hs.2) hu))).trans
      (eVariationOn.mono _ (Icc_subset_Icc ht.1 hs.2))

/-- The set-to-set distance bound supplies a near-minimal path across an
annulus, with endpoints on the prescribed spheres. -/
theorem w3_short_across_path (D : ContMetric d) {V A B : Set (Rd d)}
    {β η : ℝ} (hη : 0 < η)
    (hcross : setDistIn D V A B ≤ ENNReal.ofReal β) :
    ∃ P : ℝ → Rd d, ContinuousOn P (Icc 0 1) ∧
      P 0 ∈ A ∧ P 1 ∈ B ∧ MapsTo P (Icc 0 1) V ∧
      D.len P 0 1 ≤ ENNReal.ofReal β + ENNReal.ofReal η := by
  have hlt : setDistIn D V A B < ENNReal.ofReal β + ENNReal.ofReal η :=
    hcross.trans_lt (ENNReal.lt_add_right ENNReal.ofReal_ne_top
      (ne_of_gt (ENNReal.ofReal_pos.mpr hη)))
  unfold setDistIn at hlt
  simp only [iInf_lt_iff] at hlt
  obtain ⟨x, hx, y, hy, hxy⟩ := hlt
  rw [D.internal_eq_iInf_len] at hxy
  simp only [iInf_lt_iff] at hxy
  obtain ⟨P, hPc, hP0, hP1, hPV, hPL⟩ := hxy
  exact ⟨P, hPc, hP0 ▸ hx, hP1 ▸ hy, hPV, hPL.le⟩

/-- Radial bounds for a crossing path viewed from a nearby shell centre. -/
theorem w3_shifted_crossing_radii {P : ℝ → Rd d} {w z : Rd d}
    {r a b : ℝ} (h0 : P 0 ∈ Metric.sphere w (r / 8))
    (h1 : P 1 ∈ Metric.sphere w r)
    (ha : r / 8 + ‖w - z‖ ≤ a)
    (hb : b + ‖w - z‖ ≤ r) :
    ‖P 0 - z‖ ≤ a ∧ b ≤ ‖P 1 - z‖ := by
  have hs : ‖P 0 - w‖ = r / 8 := by
    simpa only [Metric.mem_sphere, dist_eq_norm] using h0
  have hf : ‖P 1 - w‖ = r := by
    simpa only [Metric.mem_sphere, dist_eq_norm] using h1
  have ht₀ : ‖P 0 - z‖ ≤ ‖P 0 - w‖ + ‖w - z‖ := by
    calc ‖P 0 - z‖ = ‖(P 0 - w) + (w - z)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have ht₁ : ‖P 1 - w‖ ≤ ‖P 1 - z‖ + ‖w - z‖ := by
    calc ‖P 1 - w‖ = ‖(P 1 - z) + (z - w)‖ := by congr 1; abel
      _ ≤ ‖P 1 - z‖ + ‖z - w‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev z w]
  constructor <;> linarith only [hs, hf, ht₀, ht₁, ha, hb]

/-- Link a radius-`r` across path to a nearby path with radius between `r/2`
and `r`. The linking shell is the annulus around the first centre. -/
theorem w3_link_nearby_across (D : ContMetric d) {U : Set (Rd d)}
    {z w : Rd d} {r s β η : ℝ} (hr : 0 < r) (hη : 0 < η)
    (hslo : r / 2 ≤ s) (hshi : s ≤ r) (hzw : ‖z - w‖ ≤ r / 16)
    (hball : Metric.closedBall z (2 * r) ⊆ U)
    (haround : aroundDist D z (3 * r / 16) (3 * r / 8) ≤ ENNReal.ofReal β)
    {Pz Pw : ℝ → Rd d} (hPzc : ContinuousOn Pz (Icc 0 1))
    (hPwc : ContinuousOn Pw (Icc 0 1))
    (hPz0 : Pz 0 ∈ Metric.sphere z (r / 8))
    (hPz1 : Pz 1 ∈ Metric.sphere z r)
    (hPw0 : Pw 0 ∈ Metric.sphere w (s / 8))
    (hPw1 : Pw 1 ∈ Metric.sphere w s) :
    ∃ u ∈ Icc (0 : ℝ) 1, ∃ v ∈ Icc (0 : ℝ) 1,
      D.internal U (Pz u) (Pw v) ≤ ENNReal.ofReal β + ENNReal.ofReal η := by
  have hradii₁ : ‖Pz 0 - z‖ ≤ 3 * r / 16 ∧ 3 * r / 8 ≤ ‖Pz 1 - z‖ := by
    have h := w3_shifted_crossing_radii (w := z) (z := z) hPz0 hPz1
      (a := 3 * r / 16) (b := 3 * r / 8)
      (by simp only [sub_self, norm_zero, add_zero]; linarith only [hr])
      (by simp only [sub_self, norm_zero, add_zero]; linarith only [hr])
    exact h
  have hradii₂ : ‖Pw 0 - z‖ ≤ 3 * r / 16 ∧ 3 * r / 8 ≤ ‖Pw 1 - z‖ := by
    have hdist : ‖w - z‖ ≤ r / 16 := by rwa [norm_sub_rev]
    apply w3_shifted_crossing_radii (w := w) (z := z) hPw0 hPw1
    · linarith only [hshi, hdist]
    · calc
        3 * r / 8 + ‖w - z‖ ≤ 3 * r / 8 + r / 16 := by
          simpa only [add_comm] using add_le_add_right hdist (3 * r / 8)
        _ ≤ r / 2 := by linarith only [hr]
        _ ≤ s := hslo
  have hannU : ann z (3 * r / 16) (3 * r / 8) ⊆ U := by
    intro x hx
    apply hball
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hx.2.le.trans (by linarith only [hr])
  exact w3_link_crossing_paths D (by linarith only [hr]) hη hannU haround
    hPzc hPwc hradii₁.1 hradii₁.2 hradii₂.1 hradii₂.2

end HigherDimLQGMetric
