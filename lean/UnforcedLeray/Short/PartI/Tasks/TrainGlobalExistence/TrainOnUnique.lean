import UnforcedLeray.Short.PartI.Sub.T04.Defs
import UnforcedLeray.Short.PartI.Sub.T02_3
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalUniquenessBounded
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalCutoffEnergyIneq
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalEnergyBound
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.SlicePoisson
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.VelocityDecayOfEnergy
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound

/-!
# Part I, task `PartI:T04/4`: `TrainOnUnique`

Source: `the November 2 reference manuscript` lines 276-277, 288 (uniqueness) and
447 (decaying pressure gauge).  Velocity by `classicalUniquenessBounded` on `[0, min S S']`;
pressure and stream by the zero-gradient-and-decay argument.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.GaussianVortex (perpendicularGradient)
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

namespace TrainOnUniqueAux

/-- A differentiable function on the plane with vanishing partials and decaying to `0` is `0`. -/
theorem eq_zero_of_partials {f : Plane → ℝ} (hd : Differentiable ℝ f)
    (hq : ∀ z : Plane, deriv (fun t : ℝ => f (t, z.2)) z.1 = 0)
    (hη : ∀ z : Plane, deriv (fun t : ℝ => f (z.1, t)) z.2 = 0)
    (hlim : Tendsto f (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)) : ∀ z, f z = 0 := by
  have hconst : ∀ z : Plane, f z = f (0, 0) := by
    intro z
    have hq' : f (z.1, z.2) = f (0, z.2) :=
      is_const_of_deriv_eq_zero (f := fun t => f (t, z.2))
        (fun t => (hd _).comp t (differentiableAt_id.prodMk (differentiableAt_const _)))
        (fun t => hq (t, z.2)) z.1 0
    have hη' : f (0, z.2) = f (0, 0) :=
      is_const_of_deriv_eq_zero (f := fun t => f (0, t))
        (fun t => (hd _).comp t ((differentiableAt_const _).prodMk differentiableAt_id))
        (fun t => hη (0, t)) z.2 0
    exact hq'.trans hη'
  have := B0140.neBot_comap_abs_snd
  have h2 : Tendsto f (comap (fun z : Plane => |z.2|) atTop) (𝓝 (f (0, 0))) := by
    rw [show f = fun _ => f (0, 0) from funext hconst]
    exact tendsto_const_nhds
  have hK : f (0, 0) = 0 := tendsto_nhds_unique h2 hlim
  intro z
  rw [hconst z, hK]

theorem classical_restrict {ν c S T : ℝ} {v : ℝ → Plane → Vec} {p ψ : ℝ → Plane → ℝ}
    (h : IsTrainOn ν c S v p ψ) (hT : T ≤ S) (hT0 : 0 < T) : IsClassicalOn ν c T v p where
  smooth_v := h.smooth_v.mono (prod_mono (Icc_subset_Icc le_rfl hT) subset_rfl)
  smooth_p := h.smooth_p.mono (prod_mono (Icc_subset_Icc le_rfl hT) subset_rfl)
  periodic_v s hs := h.periodic_v s ⟨hs.1, hs.2.trans hT⟩
  periodic_p s hs := h.periodic_p s ⟨hs.1, hs.2.trans hT⟩
  solenoidal s hs := h.solenoidal s ⟨hs.1, hs.2.trans hT⟩
  momentum s hs := h.momentum s ⟨hs.1, hs.2.trans_le hT⟩
  initial := h.initial
  finite_energy s hs := h.finite_energy s ⟨hs.1, hs.2.trans hT⟩

theorem bounded_restrict {S T : ℝ} {v : ℝ → Plane → Vec} (h : HasBoundedDerivsOn S v)
    (hT : T ≤ S) : HasBoundedDerivsOn T v := by
  intro k
  obtain ⟨M, hM⟩ := h k
  exact ⟨M, fun s hs z => hM s ⟨hs.1, hs.2.trans hT⟩ z⟩

theorem pressure_decay_restrict {ν c S T : ℝ} {v : ℝ → Plane → Vec} {p ψ : ℝ → Plane → ℝ}
    (h : IsTrainOn ν c S v p ψ) (hT : T ≤ S) : PressureDecayOn T p :=
  fun s hs => h.pressure_decay s ⟨hs.1, hs.2.trans hT⟩

/-- Velocities of two bounded trains agree on `[0,T]`, `T ≤ S, S'`. -/
theorem velocity_eq {ν c S S' : ℝ} {v v' : ℝ → Plane → Vec} {p p' ψ ψ' : ℝ → Plane → ℝ}
    (hν : 0 < ν) (hc : 1 ≤ c) (hS : 0 < S) (hS' : 0 < S')
    (h : IsTrainOn ν c S v p ψ) (h' : IsTrainOn ν c S' v' p' ψ')
    (hb : HasBoundedDerivsOn S v) (hb' : HasBoundedDerivsOn S' v') :
    ∀ s : ℝ, 0 ≤ s → s ≤ S → s ≤ S' → v s = v' s := by
  intro s hs0 hsS hsS'
  set T := min S S' with hTdef
  have hTS : T ≤ S := min_le_left _ _
  have hTS' : T ≤ S' := min_le_right _ _
  have hT : 0 < T := lt_min hS hS'
  have hcl := classical_restrict h hTS hT
  have hcl' := classical_restrict h' hTS' hT
  have hbT := bounded_restrict hb hTS
  have hbT' := bounded_restrict hb' hTS'
  have hp := pressure_decay_restrict h hTS
  have hp' := pressure_decay_restrict h' hTS'
  have hP := classicalPressureBound_of slicePoisson velocityDecayOfEnergy cylinderPoissonBound
  have hE := classicalEnergyBound
  obtain ⟨Mp, hMp⟩ := hP ν c T v p hν hc hT hcl hbT hp
  obtain ⟨Mp', hMp'⟩ := hP ν c T v' p' hν hc hT hcl' hbT' hp'
  obtain ⟨Me, hMe⟩ := hE ν c T Mp v p hν hc hT hcl hbT hMp
  obtain ⟨Me', hMe'⟩ := hE ν c T Mp' v' p' hν hc hT hcl' hbT' hMp'
  obtain ⟨Mv, hMv⟩ := exists_sup_bound_of_hasBoundedDerivsOn hbT
  obtain ⟨Mv', hMv'⟩ := exists_sup_bound_of_hasBoundedDerivsOn hbT'
  set M : ℝ := max (max Mv Mv') (max (max Mp Mp') (max Me Me')) with hM
  have hB : ClassicalBoundedBy c T M v p := fun r hr =>
    ⟨fun w => (hMv r hr w).trans (by simp [hM]), fun w => (hMp r hr w).trans (by simp [hM]),
      (hMe r hr).trans (by simp [hM])⟩
  have hB' : ClassicalBoundedBy c T M v' p' := fun r hr =>
    ⟨fun w => (hMv' r hr w).trans (by simp [hM]), fun w => (hMp' r hr w).trans (by simp [hM]),
      (hMe' r hr).trans (by simp [hM])⟩
  exact classicalUniquenessBounded_of classicalCutoffEnergyIneq ν c T M v v' p p' hν hc hT hcl hcl'
    hbT hbT' hB hB' s ⟨hs0, le_min hsS hsS'⟩

theorem slice_diff {T s : ℝ} {p : ℝ → Plane → ℝ}
    (h : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => p x.1 x.2) (Icc 0 T ×ˢ univ))
    (hs : s ∈ Icc (0 : ℝ) T) : Differentiable ℝ (p s) := by
  have h2 := h.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (s := univ) (fun z _ => (⟨hs, mem_univ z⟩ : (s, z) ∈ Icc 0 T ×ˢ univ))
  exact (contDiffOn_univ.1 h2).differentiable (by simp)

/-- Pressures agree for `0 < s < T`, given equal velocities on `[0,T]`. -/
theorem pressure_eq_open {ν c T : ℝ} {v v' : ℝ → Plane → Vec} {p p' ψ ψ' : ℝ → Plane → ℝ}
    (h : IsTrainOn ν c T v p ψ) (h' : IsTrainOn ν c T v' p' ψ')
    (hv : ∀ s ∈ Icc (0 : ℝ) T, v s = v' s) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) :
    p s = p' s := by
  have hgrad : ∀ z, Train.gradS (p s) z = Train.gradS (p' s) z := by
    intro z
    have h1 := h.momentum s hs z
    have h2 := h'.momentum s hs z
    have hev : (fun t => v t z) =ᶠ[𝓝 s] (fun t => v' t z) := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
      rw [hv t ⟨ht.1.le, ht.2.le⟩]
    have hd := hev.deriv_eq
    have hvs := hv s ⟨hs.1.le, hs.2.le⟩
    simp only [Train.momentumResidual] at h1 h2
    rw [hd, hvs] at h1
    have e1 := eq_neg_of_add_eq_zero_right h1
    have e2 := eq_neg_of_add_eq_zero_right h2
    rw [e1, e2]
  set f : Plane → ℝ := fun z => p s z - p' s z with hf
  have hpd := slice_diff h.smooth_p ⟨hs.1.le, hs.2.le⟩
  have hpd' := slice_diff h'.smooth_p ⟨hs.1.le, hs.2.le⟩
  have hfd : Differentiable ℝ f := hpd.sub hpd'
  have hcomp : ∀ z, Cyl.partialQ (p s) z = Cyl.partialQ (p' s) z ∧
      Cyl.partialEta (p s) z = Cyl.partialEta (p' s) z := by
    intro z
    have := Train.toVec_injective (hgrad z)
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hlim : Tendsto f (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
    simpa only [sub_zero, hf] using
      (h.pressure_decay s ⟨hs.1.le, hs.2.le⟩).sub (h'.pressure_decay s ⟨hs.1.le, hs.2.le⟩)
  have hz := eq_zero_of_partials hfd
    (fun z => by
      have h1 : HasDerivAt (fun t : ℝ => p s (t, z.2)) (Cyl.partialQ (p s) z) z.1 :=
        ((hpd _).comp z.1 (differentiableAt_id.prodMk (differentiableAt_const _))).hasDerivAt
      have h2 : HasDerivAt (fun t : ℝ => p' s (t, z.2)) (Cyl.partialQ (p' s) z) z.1 :=
        ((hpd' _).comp z.1 (differentiableAt_id.prodMk (differentiableAt_const _))).hasDerivAt
      have := (h1.fun_sub h2).deriv
      simp only [hf]
      rw [this, (hcomp z).1, sub_self])
    (fun z => by
      have h1 : HasDerivAt (fun t : ℝ => p s (z.1, t)) (Cyl.partialEta (p s) z) z.2 :=
        ((hpd _).comp z.2 ((differentiableAt_const _).prodMk differentiableAt_id)).hasDerivAt
      have h2 : HasDerivAt (fun t : ℝ => p' s (z.1, t)) (Cyl.partialEta (p' s) z) z.2 :=
        ((hpd' _).comp z.2 ((differentiableAt_const _).prodMk differentiableAt_id)).hasDerivAt
      have := (h1.fun_sub h2).deriv
      simp only [hf]
      rw [this, (hcomp z).2, sub_self])
    hlim
  funext z
  have := hz z
  simp only [hf] at this
  linarith

end TrainOnUniqueAux

open TrainOnUniqueAux in
/-- **Bounded classical trains agree on their common interval** (lines 276-277, 288, 447). -/
theorem trainOnUnique : TrainOnUnique := by
  intro ν c S S' v v' p p' ψ ψ' hν hc hS hS' h h' hb hb' s hs0 hsS hsS'
  have hv := velocity_eq hν hc hS hS' h h' hb hb'
  set T := min S S' with hTdef
  have hTS : T ≤ S := min_le_left _ _
  have hTS' : T ≤ S' := min_le_right _ _
  have hT : 0 < T := lt_min hS hS'
  have hvT : ∀ r ∈ Icc (0 : ℝ) T, v r = v' r := fun r hr => hv r hr.1 (hr.2.trans hTS) (hr.2.trans hTS')
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs0, le_min hsS hsS'⟩
  have hTr : IsTrainOn ν c T v p ψ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h.initial, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact h.smooth_v.mono (prod_mono (Icc_subset_Icc le_rfl hTS) subset_rfl)
    · exact h.smooth_p.mono (prod_mono (Icc_subset_Icc le_rfl hTS) subset_rfl)
    · exact fun r hr => h.periodic_v r ⟨hr.1, hr.2.trans hTS⟩
    · exact fun r hr => h.periodic_p r ⟨hr.1, hr.2.trans hTS⟩
    · exact fun r hr => h.solenoidal r ⟨hr.1, hr.2.trans hTS⟩
    · exact fun r hr => h.momentum r ⟨hr.1, hr.2.trans_le hTS⟩
    · exact fun r hr => h.finite_energy r ⟨hr.1, hr.2.trans hTS⟩
    · exact fun r hr => h.pressure_decay r ⟨hr.1, hr.2.trans hTS⟩
    · exact fun r hr => h.stream_differentiable r ⟨hr.1, hr.2.trans hTS⟩
    · exact fun r hr => h.stream r ⟨hr.1, hr.2.trans hTS⟩
    · exact fun r hr => h.stream_decay r ⟨hr.1, hr.2.trans hTS⟩
    · exact fun r hr => h.odd r ⟨hr.1, hr.2.trans hTS⟩
  have hTr' : IsTrainOn ν c T v' p' ψ' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h'.initial, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact h'.smooth_v.mono (prod_mono (Icc_subset_Icc le_rfl hTS') subset_rfl)
    · exact h'.smooth_p.mono (prod_mono (Icc_subset_Icc le_rfl hTS') subset_rfl)
    · exact fun r hr => h'.periodic_v r ⟨hr.1, hr.2.trans hTS'⟩
    · exact fun r hr => h'.periodic_p r ⟨hr.1, hr.2.trans hTS'⟩
    · exact fun r hr => h'.solenoidal r ⟨hr.1, hr.2.trans hTS'⟩
    · exact fun r hr => h'.momentum r ⟨hr.1, hr.2.trans_le hTS'⟩
    · exact fun r hr => h'.finite_energy r ⟨hr.1, hr.2.trans hTS'⟩
    · exact fun r hr => h'.pressure_decay r ⟨hr.1, hr.2.trans hTS'⟩
    · exact fun r hr => h'.stream_differentiable r ⟨hr.1, hr.2.trans hTS'⟩
    · exact fun r hr => h'.stream r ⟨hr.1, hr.2.trans hTS'⟩
    · exact fun r hr => h'.stream_decay r ⟨hr.1, hr.2.trans hTS'⟩
    · exact fun r hr => h'.odd r ⟨hr.1, hr.2.trans hTS'⟩
  refine ⟨hvT s hsT, ?_, ?_⟩
  · -- pressure: interior, then endpoints by continuity in `s`
    funext z
    have hcont : ∀ (q : ℝ → Plane → ℝ),
        ContDiffOn ℝ ∞ (fun x : ℝ × Plane => q x.1 x.2) (Icc 0 T ×ˢ univ) →
        ContinuousOn (fun r => q r z) (Icc 0 T) := by
      intro q hq
      have h1 : ContinuousOn (fun r : ℝ => (r, z)) (Icc 0 T) :=
        (continuous_id.prodMk continuous_const).continuousOn
      exact (hq.continuousOn).comp h1 (fun r hr => ⟨hr, mem_univ z⟩)
    have heq : EqOn (fun r => p r z) (fun r => p' r z) (Ioo 0 T) := by
      intro r hr
      exact congrFun (pressure_eq_open hTr hTr' hvT hr) z
    have := heq.of_subset_closure (hcont p hTr.smooth_p) (hcont p' hTr'.smooth_p)
      Ioo_subset_Icc_self (by rw [closure_Ioo hT.ne]) hsT
    exact this
  · -- stream: equal perpendicular gradients and decay
    have hd := hTr.stream_differentiable s hsT
    have hd' := hTr'.stream_differentiable s hsT
    have hvs := hvT s hsT
    have hpg : ∀ z, perpendicularGradient (ψ s) z = perpendicularGradient (ψ' s) z := by
      intro z
      apply Train.toVec_injective
      rw [← hTr.stream s hsT z, ← hTr'.stream s hsT z, hvs]
    have hX : ∀ z, GaussianVortex.partialX (ψ s) z = GaussianVortex.partialX (ψ' s) z :=
      fun z => congrArg Prod.snd (hpg z)
    have hY : ∀ z, GaussianVortex.partialY (ψ s) z = GaussianVortex.partialY (ψ' s) z := by
      intro z
      have := congrArg Prod.fst (hpg z)
      simp only [perpendicularGradient, neg_inj] at this
      exact this
    have hlim : Tendsto (fun z => ψ s z - ψ' s z) (comap (fun z : Plane => |z.2|) atTop)
        (𝓝 0) := by
      simpa only [sub_zero] using (hTr.stream_decay s hsT).sub (hTr'.stream_decay s hsT)
    have hz := eq_zero_of_partials (f := fun z => ψ s z - ψ' s z) (hd.sub hd')
      (fun z => by
        have h1 : HasDerivAt (fun t : ℝ => ψ s (t, z.2)) (GaussianVortex.partialX (ψ s) z) z.1 :=
          ((hd _).comp z.1 (differentiableAt_id.prodMk (differentiableAt_const _))).hasDerivAt
        have h2 : HasDerivAt (fun t : ℝ => ψ' s (t, z.2)) (GaussianVortex.partialX (ψ' s) z) z.1 :=
          ((hd' _).comp z.1 (differentiableAt_id.prodMk (differentiableAt_const _))).hasDerivAt
        rw [(h1.fun_sub h2).deriv, hX z, sub_self])
      (fun z => by
        have h1 : HasDerivAt (fun t : ℝ => ψ s (z.1, t)) (GaussianVortex.partialY (ψ s) z) z.2 :=
          ((hd _).comp z.2 ((differentiableAt_const _).prodMk differentiableAt_id)).hasDerivAt
        have h2 : HasDerivAt (fun t : ℝ => ψ' s (z.1, t)) (GaussianVortex.partialY (ψ' s) z) z.2 :=
          ((hd' _).comp z.2 ((differentiableAt_const _).prodMk differentiableAt_id)).hasDerivAt
        rw [(h1.fun_sub h2).deriv, hY z, sub_self])
      hlim
    funext z
    have := hz z
    linarith

end UnforcedLeray.Short.PartI
