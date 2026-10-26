import SupercriticalConformalCovariance.ZBConformal.Independence
import LQGMetric.Papers.DFGPS.L2_17CoreH

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter Topology
open LQGMetric
open SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.ZBConformal

variable (V : Opens ℂ)

private theorem cover_exhaustK (x : V) : ∃ n : ℕ, (x : ℂ) ∈ exhaustK V n := by
  obtain ⟨n, hn⟩ := exists_exhaustK_superset V (isCompact_singleton) (by
    intro y hy
    simpa only [Set.mem_singleton_iff] using hy.symm ▸ x.property)
  exact ⟨n, hn (Set.mem_singleton _)⟩

private def firstK (x : V) : ℕ := by
  classical
  exact Nat.find (cover_exhaustK V x)

private theorem firstK_mem (x : V) : (x : ℂ) ∈ exhaustK V (firstK V x) :=
  by
    classical
    exact Nat.find_spec (cover_exhaustK V x)

private theorem measurable_firstK : Measurable (firstK V) := by
  classical
  apply measurable_find (cover_exhaustK V)
  intro n
  exact (exhaustK V n).isCompact.isClosed.measurableSet.preimage measurable_subtype_coe

private def radius (n : ℕ) : ℝ :=
  Classical.choose ((exhaustK V n).isCompact.exists_cthickening_subset_open V.isOpen
    (exhaustK_subset V n))

private theorem radius_pos (n : ℕ) : 0 < radius V n :=
  (Classical.choose_spec ((exhaustK V n).isCompact.exists_cthickening_subset_open V.isOpen
    (exhaustK_subset V n))).1

private theorem radius_ball (n : ℕ) {x : ℂ} (hx : x ∈ exhaustK V n) :
    closedBall x (radius V n) ⊆ V := by
  have h := (Classical.choose_spec ((exhaustK V n).isCompact.exists_cthickening_subset_open
    V.isOpen (exhaustK_subset V n))).2
  exact (closedBall_subset_cthickening hx (radius V n)).trans h

/-- Explicit point value of a distribution using a radius selected from a compact exhaustion. -/
def canonicalHarm (T : DistC) (x : V) : ℝ :=
  T (GM.radBump (radius V (firstK V x)) (radius_pos V _).le (x : ℂ)) /
    ∫ y, GM.radProf (radius V (firstK V x)) y

theorem canonicalHarm_eq {g : ℂ → ℝ} (hg : InnerProductSpace.HarmonicOnNhd g V)
    {T : DistC} (hT : ∀ ψ : TestOn V, restrictTo V T ψ = ∫ y, g y * ψ y)
    (x : V) : canonicalHarm V T x = g x := by
  unfold canonicalHarm
  rw [GM.pair_radBump_of_harmonic hg hT (radius_pos V _)
    (radius_ball V _ (firstK_mem V x))]
  exact mul_div_cancel_right₀ _ (GM.integral_radProf_pos (radius_pos V _)).ne'

theorem measurable_canonicalHarm : Measurable (fun p : DistC × V => canonicalHarm V p.1 p.2) := by
  let f : ℕ → DistC × V → ℝ := fun n p =>
    p.1 (GM.radBump (radius V n) (radius_pos V n).le (p.2 : ℂ)) /
      ∫ y, GM.radProf (radius V n) y
  have hf : ∀ n, Measurable (f n) := by
    intro n
    apply Measurable.div_const
    exact (GM.measurable_apply_radBump (radius V n) (radius_pos V n).le).comp
      (Measurable.prodMk measurable_fst (measurable_subtype_coe.comp measurable_snd))
  have hall : Measurable (fun p : ℕ × (DistC × V) => f p.1 p.2) :=
    measurable_from_prod_countable_right hf
  have hidx : Measurable (fun p : DistC × V => firstK V p.2) :=
    (measurable_firstK V).comp measurable_snd
  simpa only [f, canonicalHarm, Function.comp_def, id_eq, Prod.fst, Prod.snd] using
    hall.comp (Measurable.prodMk hidx measurable_id)

variable {Ω : Type} [MeasurableSpace Ω]

theorem measurable_canonicalHarm_random {G : Ω → DistC} (hG : Measurable G) :
    Measurable (fun p : Ω × V => canonicalHarm V (G p.1) p.2) := by
  exact (measurable_canonicalHarm V).comp
    (Measurable.prodMk (hG.comp measurable_fst) measurable_snd)

def canonicalHarmExt (V : Opens ℂ) (T : DistC) (x : ℂ) : ℝ := by
  classical
  exact if hx : x ∈ V then canonicalHarm V T ⟨x, hx⟩ else 0

theorem measurable_canonicalHarmExt :
    Measurable (fun p : DistC × ℂ => canonicalHarmExt V p.1 p.2) := by
  classical
  let s : Set (DistC × ℂ) := {p | p.2 ∈ V}
  have hs : MeasurableSet s := V.isOpen.measurableSet.preimage measurable_snd
  have hinside : Measurable (fun p : s =>
      canonicalHarm V p.1.1 ⟨p.1.2, p.2⟩) := by
    have hpair : Measurable (fun p : s => (p.1.1, (⟨p.1.2, p.2⟩ : V))) := by
      apply Measurable.prodMk
      · exact measurable_fst.comp measurable_subtype_coe
      · apply Measurable.subtype_mk
        exact measurable_snd.comp measurable_subtype_coe
    exact (measurable_canonicalHarm V).comp hpair
  have hout : Measurable (fun _ : (sᶜ : Set (DistC × ℂ)) => (0 : ℝ)) := measurable_const
  convert Measurable.dite hinside hout hs using 1
  funext p
  by_cases hv : p.2 ∈ V
  · simp [canonicalHarmExt, s, hv]
  · simp [canonicalHarmExt, s, hv]

theorem canonicalHarmExt_eq {g : ℂ → ℝ} (hg : InnerProductSpace.HarmonicOnNhd g V)
    {T : DistC} (hT : ∀ ψ : TestOn V, restrictTo V T ψ = ∫ y, g y * ψ y)
    {x : ℂ} (hx : x ∈ V) : canonicalHarmExt V T x = g x := by
  simp only [canonicalHarmExt, dif_pos hx]
  exact canonicalHarm_eq V hg hT ⟨x, hx⟩

theorem canonicalHarmExt_harmonic {g : ℂ → ℝ}
    (hg : InnerProductSpace.HarmonicOnNhd g V)
    {T : DistC} (hT : ∀ ψ : TestOn V, restrictTo V T ψ = ∫ y, g y * ψ y) :
    InnerProductSpace.HarmonicOnNhd (canonicalHarmExt V T) V := by
  intro x hx
  have he : canonicalHarmExt V T =ᶠ[𝓝 x] g := by
    filter_upwards [V.isOpen.mem_nhds hx] with y hy
    exact canonicalHarmExt_eq V hg hT hy
  exact (InnerProductSpace.harmonicAt_congr_nhds he).2 (hg x hx)

theorem canonicalHarmExt_pair {g : ℂ → ℝ}
    (hg : InnerProductSpace.HarmonicOnNhd g V)
    {T : DistC} (hT : ∀ ψ : TestOn V, restrictTo V T ψ = ∫ y, g y * ψ y)
    (ψ : TestOn V) :
    restrictTo V T ψ = ∫ y, canonicalHarmExt V T y * ψ y := by
  rw [hT ψ]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    by_cases hy : ψ y = 0
    · simp [hy]
    · change g y * ψ y = canonicalHarmExt V T y * ψ y
      rw [canonicalHarmExt_eq V hg hT (ψ.tsupport_subset (subset_tsupport _ hy))]

section Pull

variable {φ : ℂ → ℂ} {U : Opens ℂ} (hφ : IsConformalBijection φ U V)

def pulledHarm {φ : ℂ → ℂ} {U V : Opens ℂ} (hφ : IsConformalBijection φ U V)
    (G : Ω → DistC) (c : Ω → ℝ) (ω : Ω) (x : ℂ) : ℝ := by
  classical
  exact if x ∈ U then canonicalHarmExt V (G ω) (φ x) + c ω else 0

theorem measurable_pulledHarm {G : Ω → DistC} (hG : Measurable G)
    {c : Ω → ℝ} (hc : Measurable c) :
    Measurable (fun p : Ω × U => pulledHarm hφ G c p.1 p.2) := by
  have hφm : Measurable (fun x : U => φ x) :=
    (continuousOn_iff_continuous_domRestrict.mp hφ.1.continuousOn).measurable
  have hpair : Measurable (fun p : Ω × U => (G p.1, φ (p.2 : ℂ))) :=
    Measurable.prodMk (hG.comp measurable_fst) (hφm.comp measurable_snd)
  have hbase := (measurable_canonicalHarmExt V).comp hpair
  have hcm : Measurable (fun p : Ω × U => c p.1) := hc.comp measurable_fst
  convert hbase.add hcm using 1
  funext p
  simp [pulledHarm, p.2.property]

end Pull

end SupercriticalConformalCovariance.ZBConformal
