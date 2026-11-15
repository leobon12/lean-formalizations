/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11FaceAttachment

/-!
# GB11: the canonical forward lift on unvisited closed-half-plane wall points

The forward chart extends continuously and injectively to `Hbar \ closure K_t`.
This covers every finite unvisited wall point, including real contacts. A continuous
incoming prefix in this domain has a unique real attachment gate by the existing
cluster-set theorem; no open-half-plane restriction is imposed on the prefix.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart

/-- Unvisited finite wall points, with real contacts included. -/
def freeUpper (W : ℝ → ℝ) (t : ℝ) : Set ℂ := Hbar \ closure (fwdHull W t)

/-- The canonical boundary extension of the centered forward chart. -/
def forwardExt (W : ℝ → ℝ) (t : ℝ) : ℂ → ℂ :=
  extendFrom (H \ fwdHull W t) (fwdMap W t)

/-- Every unvisited closed-half-plane point is adherent to the active domain. -/
theorem freeUpper_subset_closure {W : ℝ → ℝ} {t : ℝ} :
    freeUpper W t ⊆ closure (H \ fwdHull W t) := by
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hz.2
  have hsub : ball z r ∩ H ⊆ H \ fwdHull W t := fun w hw =>
    ⟨hw.2, fun hwK => hball hw.1 (subset_closure hwK)⟩
  exact closure_mono hsub
    (subset_closure_ball_inter_H _ _ ⟨mem_ball_self hr, hz.1⟩)

/-- Reflection supplies a finite forward-chart limit at every unvisited real point;
interior points use the existing holomorphic forward map. -/
theorem exists_limit_forward_freeUpper {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ freeUpper W t) :
    ∃ v : ℂ, Tendsto (fwdMap W t) (𝓝[H \ fwdHull W t] z) (𝓝 v) := by
  rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z.im from hz.1) with hpos | hzero
  · have hzD : z ∈ H \ fwdHull W t :=
      ⟨hpos, fun hK => hz.2 (subset_closure hK)⟩
    exact ⟨fwdMap W t z,
      ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht).continuousOn z hzD).tendsto⟩
  · have hre : (z.re : ℂ) = z := Complex.ext rfl (by
      simp only [Complex.ofReal_im, hzero.symm])
    have hy : (z.re : ℂ) ∉ closure (fwdHull W t) := by rw [hre]; exact hz.2
    obtain ⟨ρ, hρ, G, hGd, -, hGeq, -, -, -⟩ :=
      exists_local_chart_at_real hη hW hW0 ht hy
    have hzB : z ∈ ball (z.re : ℂ) ρ := by rw [hre]; exact mem_ball_self hρ
    have hGc := hGd.continuousOn.continuousAt (isOpen_ball.mem_nhds hzB)
    refine ⟨G z, (hGc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_⟩
    have hball : ∀ᶠ w in 𝓝[H \ fwdHull W t] z, w ∈ ball (z.re : ℂ) ρ :=
      mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hzB)
    filter_upwards [hball, self_mem_nhdsWithin] with w hwB hwD
    exact hGeq ⟨hwB, hwD.1⟩

/-- The canonical forward lift is continuous across all unvisited real contacts. -/
theorem continuousOn_forwardExt {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) : ContinuousOn (forwardExt W t) (freeUpper W t) :=
  continuousOn_extendFrom freeUpper_subset_closure
    (fun _ hz => exists_limit_forward_freeUpper hη hW hW0 ht hz)

/-- The canonical forward lift takes unvisited wall points into the closed half-plane. -/
theorem forwardExt_mem_Hbar {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ freeUpper W t) : forwardExt W t z ∈ Hbar := by
  have : (𝓝[H \ fwdHull W t] z).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (freeUpper_subset_closure hz)
  have hlim := tendsto_extendFrom (exists_limit_forward_freeUpper hη hW hW0 ht hz)
  exact isClosed_Hbar.mem_of_tendsto hlim (eventually_nhdsWithin_of_forall
    fun w hw => H_subset_Hbar (QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hw))

/-- The ambient inverse inverts the forward lift at every finite unvisited wall point. -/
theorem trMap_forwardExt {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ freeUpper W t) :
    trMap W 0 t (forwardExt W t z) = z := by
  have : (𝓝[H \ fwdHull W t] z).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (freeUpper_subset_closure hz)
  have hlim := tendsto_extendFrom (exists_limit_forward_freeUpper hη hW hW0 ht hz)
  have hlimH : Tendsto (fwdMap W t) (𝓝[H \ fwdHull W t] z)
      (𝓝[Hbar] (forwardExt W t z)) := tendsto_nhdsWithin_iff.2
    ⟨hlim, eventually_nhdsWithin_of_forall fun w hw =>
      H_subset_Hbar (QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hw)⟩
  have htc := YuanSimpleApprox.trMap_continuousOn hη hW hW0 (a := 0) le_rfl ht
  have hcomp := (htc _ (forwardExt_mem_Hbar hη hW hW0 ht hz)).tendsto.comp hlimH
  have hid : Tendsto (fun w => trMap W 0 t (fwdMap W t w))
      (𝓝[H \ fwdHull W t] z) (𝓝 z) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall fun w hw =>
        (Sec6.trMap_zero_fwdMap hW hW0 ht hw).symm)
  exact tendsto_nhds_unique hcomp hid

/-- The canonical forward lift preserves simplicity even along original-real contacts. -/
theorem injOn_forwardExt {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) : InjOn (forwardExt W t) (freeUpper W t) := by
  intro z hz w hw he
  rw [← trMap_forwardExt hη hW hW0 ht hz, he, trMap_forwardExt hη hW hW0 ht hw]

/-- A physical incoming wall prefix that remains unvisited, with arbitrary real
contacts, lifts canonically and converges to one real attachment gate. -/
theorem exists_gate_forwardExt {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t a b : ℝ} (ht : 0 ≤ t) (hab : a < b) {α : ℝ → ℂ}
    (hα : ContinuousOn α (Icc a b)) (hfree : MapsTo α (Ico a b) (freeUpper W t))
    (hend : α b ∉ H \ fwdHull W t) :
    ∃ q : ℝ, trMap W 0 t q = α b ∧
      Tendsto (fun u => forwardExt W t (α u)) (𝓝[<] b) (𝓝 (q : ℂ)) :=
  exists_attachment_gate hη hW hW0 ht hab
    hα ((continuousOn_forwardExt hη hW hW0 ht).comp
      (hα.mono Ico_subset_Icc_self) hfree)
    (fun _ hu => forwardExt_mem_Hbar hη hW hW0 ht (hfree hu))
    (fun _ hu => trMap_forwardExt hη hW hW0 ht (hfree hu)) hend

/-- A simple unvisited physical arc, including arbitrary real contacts, lifts to a
continuous simple closed-interval arc ending at a real attachment gate. -/
theorem exists_continuous_lift_unvisited_arc {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t a b : ℝ} (ht : 0 ≤ t) (hab : a < b) {α : ℝ → ℂ}
    (hα : ContinuousOn α (Icc a b)) (hαi : InjOn α (Icc a b))
    (hfree : MapsTo α (Ico a b) (freeUpper W t)) (hend : α b ∉ H \ fwdHull W t) :
    ∃ (q : ℝ) (β : ℝ → ℂ), ContinuousOn β (Icc a b) ∧ InjOn β (Icc a b) ∧
      MapsTo β (Icc a b) Hbar ∧ (∀ u ∈ Icc a b, trMap W 0 t (β u) = α u) ∧
      β b = (q : ℂ) ∧ EqOn β (fun u => forwardExt W t (α u)) (Ico a b) := by
  set β₀ : ℝ → ℂ := fun u => forwardExt W t (α u)
  have hc₀ : ContinuousOn β₀ (Ico a b) :=
    (continuousOn_forwardExt hη hW hW0 ht).comp (hα.mono Ico_subset_Icc_self) hfree
  have hH₀ : MapsTo β₀ (Ico a b) Hbar :=
    fun _ hu => forwardExt_mem_Hbar hη hW hW0 ht (hfree hu)
  have hF₀ : ∀ u ∈ Ico a b, trMap W 0 t (β₀ u) = α u :=
    fun _ hu => trMap_forwardExt hη hW hW0 ht (hfree hu)
  obtain ⟨q, -, hq⟩ := exists_gate_forwardExt hη hW hW0 ht hab hα hfree hend
  have hcl : Icc a b ⊆ closure (Ico a b) := by
    rw [closure_Ico hab.ne]
  have hlim : ∀ u ∈ Icc a b, ∃ v, Tendsto β₀ (𝓝[Ico a b] u) (𝓝 v) := by
    intro u hu
    rcases lt_or_eq_of_le hu.2 with hlt | heq
    · exact ⟨β₀ u, (hc₀ u ⟨hu.1, hlt⟩).tendsto⟩
    · subst u
      exact ⟨(q : ℂ), hq.mono_left (nhdsWithin_mono _ (fun _ hv => hv.2))⟩
  set β : ℝ → ℂ := extendFrom (Ico a b) β₀
  have hc : ContinuousOn β (Icc a b) := continuousOn_extendFrom hcl hlim
  have hH : MapsTo β (Icc a b) Hbar := by
    intro u hu
    have : (𝓝[Ico a b] u).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hcl hu)
    exact isClosed_Hbar.mem_of_tendsto (tendsto_extendFrom (hlim u hu))
      (eventually_nhdsWithin_of_forall (fun v hv => hH₀ hv))
  have hF : ∀ u ∈ Icc a b, trMap W 0 t (β u) = α u := by
    intro u hu
    have : (𝓝[Ico a b] u).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hcl hu)
    have hβlim : Tendsto β₀ (𝓝[Ico a b] u) (𝓝[Hbar] (β u)) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_extendFrom (hlim u hu),
        eventually_nhdsWithin_of_forall (fun v hv => hH₀ hv)⟩
    have htc := YuanSimpleApprox.trMap_continuousOn hη hW hW0 (a := 0) le_rfl ht
    have hFlim := (htc _ (hH hu)).tendsto.comp hβlim
    have hαlim : Tendsto (fun v => trMap W 0 t (β₀ v)) (𝓝[Ico a b] u) (𝓝 (α u)) :=
      ((hα u hu).tendsto.mono_left (nhdsWithin_mono _ Ico_subset_Icc_self)).congr'
        (eventually_nhdsWithin_of_forall (fun v hv => (hF₀ v hv).symm))
    exact tendsto_nhds_unique hFlim hαlim
  refine ⟨q, β, hc, ?_, hH, hF, ?_, ?_⟩
  · intro u hu v hv huv
    exact hαi hu hv ((hF u hu).symm.trans ((congrArg (trMap W 0 t) huv).trans (hF v hv)))
  · exact extendFrom_eq (hcl ⟨hab.le, le_rfl⟩)
      (hq.mono_left (nhdsWithin_mono _ (fun _ hv => hv.2)))
  · exact extendFrom_extends hc₀

end InteractingSLE.Theorem14.GB11Chart
