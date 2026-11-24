import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3_3
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdDilDeriv

/-!
# `C²` phase tests (helper for `PartII-a:N04/3/3/1`)

The vector test fields `IsTestFieldVec ε c V` of `PartII-a_N04_3_3` are `C²` (not smooth). This
file introduces the `C²` analogue `IsPhaseTest2` of the smooth phase tests `IsPhaseTest` of the
PartIII-b outer-generator chain, the phase function `phaseFn V (τ, x) = V(x, τ)` (complexified),
and the elementary facts (continuity, periodicity, support) of `dτ`, `radialT`, `lapT` on it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.OuterSGen

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartIIIb.NearInst (XC)

/-- `C²` phase tests: `C²` on `ℝ × ℝ³`, `P`-periodic in the phase, vanishing for large `‖y‖`. -/
structure IsPhaseTest2 (P : ℝ) (Φ : ℝ × Space → CVec3) : Prop where
  smooth : ContDiff ℝ 2 Φ
  periodic : ∀ τ y, Φ (τ + P, y) = Φ (τ, y)
  bounded_support : ∃ R, ∀ τ y, R < ‖y‖ → Φ (τ, y) = 0

/-- The complexified phase function `(τ, x) ↦ V(x, τ)` of a physical vector field. -/
def phaseFn (V : Space × ℝ → Space) : ℝ × Space → CVec3 := fun q =>
  UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.cplx3 (V (q.2, q.1))

/-- A vector test field is `C²` everywhere (it vanishes near the axis). -/
theorem contDiff_of_isTestFieldVec {ε c : ℝ} {V : Space × ℝ → Space}
    (hV : IsTestFieldVec ε c V) : ContDiff ℝ 2 V := by
  refine (contDiff_piLp 2).2 fun j => ?_
  show ContDiff ℝ 2 fun y => V y j
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : UnforcedLeray.B0220.radius y.1 = 0
  · obtain ⟨δ, hδ, h0⟩ := (hV j).axis
    have hopen : IsOpen {y' : Space × ℝ | UnforcedLeray.B0220.radius y'.1 < δ} :=
      isOpen_lt (UnforcedLeray.B0220.continuous_radius.comp continuous_fst) continuous_const
    have hmem : y ∈ {y' : Space × ℝ | UnforcedLeray.B0220.radius y'.1 < δ} := by
      show UnforcedLeray.B0220.radius y.1 < δ
      rw [hy]
      exact hδ
    have hev : (fun _ : Space × ℝ => (0 : ℝ)) =ᶠ[𝓝 y] fun y' => V y' j :=
      Filter.eventually_of_mem (hopen.mem_nhds hmem) fun y' hy' => (h0 y' hy').symm
    exact contDiffAt_const.congr_of_eventuallyEq hev.symm
  · exact (hV j).smooth y hy

theorem isPhaseTest2_phaseFn {ε c : ℝ} {V : Space × ℝ → Space} (hV : IsTestFieldVec ε c V) :
    IsPhaseTest2 (2 * ε * c) (phaseFn V) where
  smooth := by
    have hV2 := contDiff_of_isTestFieldVec hV
    exact UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.cplx3.contDiff.comp
      (hV2.comp (contDiff_snd.prodMk contDiff_fst))
  periodic τ y := by
    have h : V (y, τ + 2 * ε * c) = V (y, τ) := by
      ext j
      exact (hV j).periodic y τ
    simp only [phaseFn, h]
  bounded_support := by
    choose R hR using fun j => (hV j).bounded
    refine ⟨∑ j, |R j|, fun τ y hy => ?_⟩
    have h : V (y, τ) = 0 := by
      ext j
      refine hR j (y, τ) (lt_of_le_of_lt ?_ hy)
      exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |R j|)
        (fun i _ => abs_nonneg _) (Finset.mem_univ j))
    simp only [phaseFn, h, map_zero]

/-- Every continuous periodic function with bounded `x`-support has an `X`-representative. -/
theorem exists_rep {P : ℝ} [Fact (0 < P)] (f : ℝ × Space → CVec3) (hc : Continuous f)
    (hper : ∀ τ y, f (τ + P, y) = f (τ, y)) (hR : ∃ R, ∀ τ y, R < ‖y‖ → f (τ, y) = 0) :
    ∃ Ψ : XC P, (Ψ : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      fun z => f ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1) := by
  have hP : 0 < P := Fact.out
  obtain ⟨R, hR⟩ := hR
  have hKc : IsCompact (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hc.continuousOn
  have hbound : ∀ w : ℝ × Space, ‖f w‖ ≤ max C 0 := by
    rintro ⟨τ, y⟩
    by_cases hy : R < ‖y‖
    · rw [hR τ y hy, norm_zero]
      exact le_max_right _ _
    · have hper' : Function.Periodic (fun s => f (s, y)) P := fun s => hper s y
      obtain ⟨τ', hτ', heq⟩ := hper'.exists_mem_Ico₀ hP τ
      have hmem : (τ', y) ∈ Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R :=
        ⟨Ico_subset_Icc_self hτ', by simpa using not_lt.mp hy⟩
      have heq' : f (τ, y) = f (τ', y) := heq
      rw [heq']
      exact (hC _ hmem).trans (le_max_left _ _)
  set S : Set (UnforcedLeray.B0223.PSpace P) := {z | ‖z.1‖ ≤ R} with hSdef
  have hSm : MeasurableSet S :=
    measurableSet_le (measurable_norm.comp measurable_fst) measurable_const
  have hSfin : volume S < ⊤ := by
    have hEq : S = Metric.closedBall (0 : Space) R ×ˢ (univ : Set (AddCircle P)) := by
      ext z
      simp [hSdef]
    rw [hEq, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top measure_closedBall_lt_top (measure_lt_top _ _)
  set g : UnforcedLeray.B0223.PSpace P → CVec3 := fun z =>
    f ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1) with hgdef
  have hgmeas : Measurable g := by
    refine hc.measurable.comp ?_
    exact (measurable_snd.comp (UnforcedLeray.B0223.measurable_toCell (P := P))).prodMk
      (measurable_fst.comp (UnforcedLeray.B0223.measurable_toCell (P := P)))
  have hgind : g = S.indicator g := by
    funext z
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz]
      have h1 : R < ‖z.1‖ := by
        have h2 := hz
        simp only [hSdef, mem_setOf_eq, not_le] at h2
        exact h2
      exact hR _ _ h1
  have hmemS : MemLp (S.indicator g) 2 volume := by
    rw [memLp_indicator_iff_restrict hSm]
    have : IsFiniteMeasure (volume.restrict S) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hSfin⟩
    exact MemLp.of_bound hgmeas.aestronglyMeasurable (max C 0)
      (Filter.Eventually.of_forall fun z => hbound _)
  have hmemg : MemLp g 2 volume := by
    rw [hgind]
    exact hmemS
  exact ⟨hmemg.toLp g, MemLp.coeFn_toLp hmemg⟩

/-! ### Periodicity, support and continuity of the phase derivatives -/

theorem fderiv_add_period {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × Space → F} (a : ℝ × Space) (hf : ∀ p, f (p + a) = f p) (p : ℝ × Space) :
    fderiv ℝ f (p + a) = fderiv ℝ f p := by
  have h : (fun x => f (x + a)) = f := funext hf
  rw [← fderiv_comp_add_right, h]

theorem fderiv_vanish {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × Space → F} {R : ℝ} (hR : ∀ τ y, R < ‖y‖ → f (τ, y) = 0) (τ : ℝ) (y : Space)
    (hy : R < ‖y‖) : fderiv ℝ f (τ, y) = 0 := by
  have hopen : IsOpen {q : ℝ × Space | R < ‖q.2‖} :=
    isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
  have hev : f =ᶠ[𝓝 (τ, y)] fun _ => (0 : F) :=
    Filter.eventually_of_mem (hopen.mem_nhds hy) fun q hq => by
      obtain ⟨q1, q2⟩ := q
      exact hR q1 q2 hq
  rw [hev.fderiv_eq]
  simp

/-- Periodic in the phase, as a translation identity. -/
theorem periodic_add {F : Type*} {f : ℝ × Space → F} {P : ℝ}
    (hf : ∀ τ y, f (τ + P, y) = f (τ, y)) (p : ℝ × Space) : f (p + (P, 0)) = f p := by
  obtain ⟨τ, y⟩ := p
  have : ((τ, y) + (P, (0 : Space)) : ℝ × Space) = (τ + P, y) := by simp
  rw [this, hf]

theorem periodic_of_add {F : Type*} {f : ℝ × Space → F} {P : ℝ}
    (hf : ∀ p : ℝ × Space, f (p + (P, 0)) = f p) (τ : ℝ) (y : Space) : f (τ + P, y) = f (τ, y) := by
  have : ((τ, y) + (P, (0 : Space)) : ℝ × Space) = (τ + P, y) := by simp
  rw [← this, hf]

section Ops

variable {P : ℝ} {ψ : ℝ × Space → CVec3}

theorem dir_periodic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × Space → F} (hf : ∀ τ y, f (τ + P, y) = f (τ, y)) (v : ℝ × Space) :
    ∀ τ y, fderiv ℝ f (τ + P, y) v = fderiv ℝ f (τ, y) v := by
  refine periodic_of_add (f := fun q => fderiv ℝ f q v) fun p => ?_
  simp only [fderiv_add_period (P, 0) (periodic_add hf) p]

theorem dir_vanish {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × Space → F} {R : ℝ} (hR : ∀ τ y, R < ‖y‖ → f (τ, y) = 0) (v : ℝ × Space) :
    ∀ τ y, R < ‖y‖ → fderiv ℝ f (τ, y) v = 0 := by
  intro τ y hy
  rw [fderiv_vanish hR τ y hy]
  rfl

theorem IsPhaseTest2.dτ_periodic (hψ : IsPhaseTest2 P ψ) :
    ∀ τ y, dτ ψ (τ + P, y) = dτ ψ (τ, y) := dir_periodic hψ.periodic (1, 0)

theorem IsPhaseTest2.dy_periodic (hψ : IsPhaseTest2 P ψ) (j : Fin 3) :
    ∀ τ y, dy j ψ (τ + P, y) = dy j ψ (τ, y) :=
  dir_periodic hψ.periodic (0, UnforcedLeray.coordinateVector j)

theorem IsPhaseTest2.radialT_periodic (hψ : IsPhaseTest2 P ψ) :
    ∀ τ y, radialT ψ (τ + P, y) = radialT ψ (τ, y) := by
  intro τ y
  simp only [radialT, hψ.dy_periodic]

theorem IsPhaseTest2.lapT_periodic (hψ : IsPhaseTest2 P ψ) :
    ∀ τ y, lapT ψ (τ + P, y) = lapT ψ (τ, y) := by
  intro τ y
  simp only [lapT]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact dir_periodic (hψ.dy_periodic j) (0, UnforcedLeray.coordinateVector j) τ y

theorem IsPhaseTest2.dτ_support (hψ : IsPhaseTest2 P ψ) :
    ∃ R, ∀ τ y, R < ‖y‖ → dτ ψ (τ, y) = 0 := by
  obtain ⟨R, hR⟩ := hψ.bounded_support
  exact ⟨R, dir_vanish hR (1, 0)⟩

theorem IsPhaseTest2.radialT_support (hψ : IsPhaseTest2 P ψ) :
    ∃ R, ∀ τ y, R < ‖y‖ → radialT ψ (τ, y) = 0 := by
  obtain ⟨R, hR⟩ := hψ.bounded_support
  refine ⟨R, fun τ y hy => ?_⟩
  simp only [radialT, dy, dir_vanish hR _ τ y hy, smul_zero, Finset.sum_const_zero]

theorem IsPhaseTest2.lapT_support (hψ : IsPhaseTest2 P ψ) :
    ∃ R, ∀ τ y, R < ‖y‖ → lapT ψ (τ, y) = 0 := by
  obtain ⟨R, hR⟩ := hψ.bounded_support
  refine ⟨R, fun τ y hy => ?_⟩
  simp only [lapT]
  refine Finset.sum_eq_zero fun j _ => ?_
  exact dir_vanish (dir_vanish hR (0, UnforcedLeray.coordinateVector j))
    (0, UnforcedLeray.coordinateVector j) τ y hy

theorem IsPhaseTest2.continuous_dir (hψ : IsPhaseTest2 P ψ) (v : ℝ × Space) :
    Continuous fun p => fderiv ℝ ψ p v :=
  (hψ.smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem IsPhaseTest2.contDiff_dir (hψ : IsPhaseTest2 P ψ) (v : ℝ × Space) :
    ContDiff ℝ 1 fun p => fderiv ℝ ψ p v :=
  (hψ.smooth.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem IsPhaseTest2.continuous_dτ (hψ : IsPhaseTest2 P ψ) : Continuous (dτ ψ) :=
  hψ.continuous_dir (1, 0)

theorem IsPhaseTest2.continuous_radialT (hψ : IsPhaseTest2 P ψ) : Continuous (radialT ψ) := by
  unfold radialT
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp continuous_snd).smul
    (hψ.continuous_dir (0, UnforcedLeray.coordinateVector j))

theorem IsPhaseTest2.continuous_lapT (hψ : IsPhaseTest2 P ψ) : Continuous (lapT ψ) := by
  unfold lapT
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((hψ.contDiff_dir (0, UnforcedLeray.coordinateVector j)).continuous_fderiv one_ne_zero).clm_apply
    continuous_const

end Ops

end UnforcedLeray.Short.PartIIa.OuterSGen
