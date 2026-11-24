import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt

/-!
# `sliceProdPairing`

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Test the phase pairing identity with the product test `Θ(t,y) = φ(t) θ(y)`:
`lapT Θ = φ ⊗ lapS θ`, both pairings reduce to `∫_{(0,P]} φ(t) (ν ∫Φ·Δθ - ∫a·θ)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Integrability of the slice integrals `t ↦ ∫_y Φ(t,y)·g(y)` on `(0,P]`, from local
integrability of `Φ ∈ Y_2` and boundedness/compact support of `g`. -/
theorem sliceInt_integrableOn {P : ℝ} (hP : 0 < P) {Φ : ℝ × Space → CVec3}
    (hΦ : UnforcedLeray.Short.IIb.IsInYr P 2 Φ) {g : Space → CVec3} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    IntegrableOn (fun t : ℝ => ∫ y : Space, ∑ i : Fin 3, Φ (t, y) i * g y i) (Ioc 0 P) := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : Space)
  set K : Set (ℝ × Space) := Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R with hKdef
  set S : Set (ℝ × Space) := Ioc (0 : ℝ) P ×ˢ (univ : Set Space) with hSdef
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hloc : LocallyIntegrable Φ volume := locInt_of_isInYr hP hΦ
  have hΦK : IntegrableOn Φ K volume := hloc.integrableOn_isCompact hK
  set h : ℝ × Space → ℂ := fun x => ∑ i : Fin 3, Φ x i * g x.2 i with hhdef
  have hdot : h = fun x => UnforcedLeray.PhaseSpace.dotL (Φ x) (g x.2) := by
    funext x
    simp only [hhdef, UnforcedLeray.PhaseSpace.dotL_apply]
  have hh_meas : AEStronglyMeasurable h volume := by
    rw [hdot]
    exact ContinuousLinearMap.aestronglyMeasurable_comp₂ UnforcedLeray.PhaseSpace.dotL
      hΦ.meas ((hg.comp continuous_snd).aestronglyMeasurable)
  have hbound : ∀ x, ‖h x‖ ≤ (‖UnforcedLeray.PhaseSpace.dotL‖ * C) * ‖Φ x‖ := by
    intro x
    rw [hdot]
    have h1 := UnforcedLeray.PhaseSpace.dotL.le_opNorm₂ (Φ x) (g x.2)
    have h2 := hC x.2
    calc ‖UnforcedLeray.PhaseSpace.dotL (Φ x) (g x.2)‖
        ≤ ‖UnforcedLeray.PhaseSpace.dotL‖ * ‖Φ x‖ * ‖g x.2‖ := h1
      _ ≤ ‖UnforcedLeray.PhaseSpace.dotL‖ * ‖Φ x‖ * C := by gcongr
      _ = (‖UnforcedLeray.PhaseSpace.dotL‖ * C) * ‖Φ x‖ := by ring
  have hIntK : IntegrableOn h K volume :=
    Integrable.mono' ((Integrable.norm hΦK).const_mul (‖UnforcedLeray.PhaseSpace.dotL‖ * C))
      hh_meas.restrict (ae_of_all _ fun x => hbound x)
  have hIntS : IntegrableOn h S volume := by
    refine IntegrableOn.of_forall_sdiff_eq_zero hIntK ?_ ?_
    · exact (measurableSet_Ioc).prod MeasurableSet.univ
    · intro x hx
      have hy : x.2 ∉ Metric.closedBall (0 : Space) R := fun hc =>
        hx.2 (mk_mem_prod (Ioc_subset_Icc_self hx.1.1) hc)
      have hnot : x.2 ∉ tsupport g := fun ht => hy (hR ht)
      have hg0 : g x.2 = 0 := image_eq_zero_of_notMem_tsupport hnot
      show ∑ i : Fin 3, Φ x i * g x.2 i = 0
      simp [hg0]
  have e : (volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)
      = (volume : Measure (ℝ × Space)).restrict S := by
    conv_lhs => rw [← Measure.restrict_univ (μ := (volume : Measure Space))]
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  have hprod : Integrable h ((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)) := by
    rw [e]
    exact hIntS
  exact hprod.integral_prod_left


theorem dy_phaseProd_eq (φ : ℝ → ℂ) (hφ : Differentiable ℝ φ) {g : Space → CVec3}
    (hg : Differentiable ℝ g) (j : Fin 3) (x : ℝ × Space) :
    UnforcedLeray.PhaseSpace.dy j (fun p : ℝ × Space => φ p.1 • g p.2) x
      = φ x.1 • fderiv ℝ g x.2 (coordinateVector j) := by
  obtain ⟨τ, y⟩ := x
  have hG : Differentiable ℝ (fun p : ℝ × Space => φ p.1 • g p.2) :=
    (hφ.comp differentiable_fst).smul (hg.comp differentiable_snd)
  have hinner : HasFDerivAt (fun y' : Space => ((τ, y') : ℝ × Space))
      (ContinuousLinearMap.inr ℝ ℝ Space) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have hcomp : HasFDerivAt ((fun p : ℝ × Space => φ p.1 • g p.2) ∘
      (fun y' : Space => ((τ, y') : ℝ × Space)))
      ((fderiv ℝ (fun p : ℝ × Space => φ p.1 • g p.2) (τ, y)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    ((hG (τ, y)).hasFDerivAt).comp y hinner
  have hslice : HasFDerivAt (fun y' : Space => φ τ • g y') (φ τ • fderiv ℝ g y) y :=
    (hg y).hasFDerivAt.const_smul (φ τ)
  have hD := hslice.unique hcomp
  have h4 := congrArg (fun L : Space →L[ℝ] CVec3 => L (coordinateVector j)) hD
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply] at h4
  show fderiv ℝ (fun p : ℝ × Space => φ p.1 • g p.2) (τ, y) (0, coordinateVector j)
    = φ τ • fderiv ℝ g y (coordinateVector j)
  rw [h4]
  rfl


theorem lapS_props {θ : Space → CVec3} (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) :
    ContDiff ℝ ∞ (UnforcedLeray.Short.PartIIIb.Concrete.lapS θ) ∧
      HasCompactSupport (UnforcedLeray.Short.PartIIIb.Concrete.lapS θ) := by
  have hfj : ∀ j : Fin 3, ContDiff ℝ ∞ (fun z : Space => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => (contDiff_infty_iff_fderiv.mp hθ).2.clm_apply contDiff_const
  have hDj : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y : Space => fderiv ℝ (fun z : Space => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => (contDiff_infty_iff_fderiv.mp (hfj j)).2.clm_apply contDiff_const
  have hcj : ∀ j : Fin 3, HasCompactSupport (fun z : Space => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => HasCompactSupport.fderiv_apply ℝ hc (EuclideanSpace.single j (1 : ℝ))
  have hsum_eq : UnforcedLeray.Short.PartIIIb.Concrete.lapS θ
      = fun y : Space => ∑ j : Fin 3, fderiv ℝ (fun z : Space => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single j (1 : ℝ)) := by
    funext y
    rfl
  have hcs : HasCompactSupport (∑ j : Fin 3, (fun y : Space => fderiv ℝ (fun z : Space => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single j (1 : ℝ)))) :=
    HasCompactSupport.finset_sum fun j _ => HasCompactSupport.fderiv_apply ℝ (hcj j) (EuclideanSpace.single j (1 : ℝ))
  rw [hsum_eq]
  refine ⟨ContDiff.sum fun j _ => hDj j, ?_⟩
  convert hcs using 1
  funext y
  simp [Finset.sum_apply]

theorem integrableOn_mul_bdd {P : ℝ} {φ : ℝ → ℂ} (hφc : Continuous φ) {F : ℝ → ℂ}
    (hF : IntegrableOn F (Ioc (0 : ℝ) P)) :
    IntegrableOn (fun t => φ t * F t) (Ioc (0 : ℝ) P) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := φ) hφc.continuousOn (s := Icc (0 : ℝ) P)
  exact Integrable.bdd_mul hF hφc.aestronglyMeasurable
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => hC t (Ioc_subset_Icc_self ht))

theorem prodTest_lapT (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    {θ : Space → CVec3} (hθ : ContDiff ℝ ∞ θ) (x : ℝ × Space) :
    UnforcedLeray.PhaseSpace.lapT (fun p : ℝ × Space => φ p.1 • θ p.2) x
      = φ x.1 • UnforcedLeray.Short.PartIIIb.Concrete.lapS θ x.2 := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hθd : Differentiable ℝ θ := hθ.differentiable (by simp)
  have hgd : ∀ j : Fin 3, Differentiable ℝ (fun y : Space => fderiv ℝ θ y (coordinateVector j)) :=
    fun j => ((contDiff_infty_iff_fderiv.mp hθ).2.clm_apply contDiff_const).differentiable (by simp)
  have h1 : ∀ j : Fin 3, UnforcedLeray.PhaseSpace.dy j (fun p : ℝ × Space => φ p.1 • θ p.2)
      = fun p => φ p.1 • fderiv ℝ θ p.2 (coordinateVector j) :=
    fun j => funext fun p => dy_phaseProd_eq φ hφd hθd j p
  have h2 : ∀ j : Fin 3, UnforcedLeray.PhaseSpace.dy j
      (UnforcedLeray.PhaseSpace.dy j (fun p : ℝ × Space => φ p.1 • θ p.2)) x
      = φ x.1 • fderiv ℝ (fun y : Space => fderiv ℝ θ y (coordinateVector j)) x.2 (coordinateVector j) := by
    intro j
    rw [h1 j]
    exact dy_phaseProd_eq φ hφd (hgd j) j x
  show ∑ j : Fin 3, UnforcedLeray.PhaseSpace.dy j
      (UnforcedLeray.PhaseSpace.dy j (fun p : ℝ × Space => φ p.1 • θ p.2)) x = _
  simp only [h2]
  unfold UnforcedLeray.Short.PartIIIb.Concrete.lapS
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rfl


theorem sliceProdPairing : SliceProdPairing := by
  intro P ν hP Φ a hΦ ha hop θ hθ hc φ hφ hpφ
  have hθd : Differentiable ℝ θ := hθ.differentiable (by simp)
  have hφc : ContDiff ℝ ∞ φ := hφ
  have hΘs : ContDiff ℝ ∞ (fun p : ℝ × Space => φ p.1 • θ p.2) :=
    (hφc.comp contDiff_fst).smul (hθ.comp contDiff_snd)
  have hΘphase : IsPhaseTest P (fun p : ℝ × Space => φ p.1 • θ p.2) := by
    refine ⟨hΘs, ?_, ?_⟩
    · intro τ y
      show φ (τ + P) • θ y = φ τ • θ y
      rw [hpφ τ]
    · obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Space)
      refine ⟨R, fun τ y hy => ?_⟩
      have hnot : y ∉ tsupport θ := fun ht => by
        have := hR ht
        rw [Metric.mem_closedBall, dist_zero_right] at this
        linarith
      show φ τ • θ y = 0
      rw [image_eq_zero_of_notMem_tsupport hnot, smul_zero]
  have hpair := hop _ hΘphase
  have hG1 : ∀ t : ℝ, ∫ y : Space,
      UnforcedLeray.PhaseSpace.dotL (UnforcedLeray.PhaseSpace.nuLapT ν
        (fun p : ℝ × Space => φ p.1 • θ p.2) (t, y)) (Φ (t, y))
      = φ t * ((ν : ℂ) * ∫ y : Space, ∑ i : Fin 3,
          Φ (t, y) i * UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i) := by
    intro t
    have hpt : ∀ y : Space,
        UnforcedLeray.PhaseSpace.dotL (UnforcedLeray.PhaseSpace.nuLapT ν
          (fun p : ℝ × Space => φ p.1 • θ p.2) (t, y)) (Φ (t, y))
        = φ t * ((ν : ℂ) * ∑ i : Fin 3, Φ (t, y) i * UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i) := by
      intro y
      simp only [UnforcedLeray.PhaseSpace.nuLapT, Pi.smul_apply,
        prodTest_lapT φ hφc hθ, Complex.real_smul,
        UnforcedLeray.PhaseSpace.dotL_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    simp only [hpt]
    rw [integral_const_mul, integral_const_mul]
  have hG2 : ∀ t : ℝ, ∫ y : Space,
      UnforcedLeray.PhaseSpace.dotL ((fun p : ℝ × Space => φ p.1 • θ p.2) (t, y)) (a (t, y))
      = φ t * ∫ y : Space, ∑ i : Fin 3, a (t, y) i * θ y i := by
    intro t
    have hpt : ∀ y : Space,
        UnforcedLeray.PhaseSpace.dotL ((fun p : ℝ × Space => φ p.1 • θ p.2) (t, y)) (a (t, y))
        = φ t * ∑ i : Fin 3, a (t, y) i * θ y i := by
      intro y
      simp only [UnforcedLeray.PhaseSpace.dotL_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    simp only [hpt]
    rw [integral_const_mul]
  have hpair' : ∫ t in Ioc (0 : ℝ) P, φ t * ((ν : ℂ) * ∫ y : Space, ∑ i : Fin 3,
          Φ (t, y) i * UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i)
      = ∫ t in Ioc (0 : ℝ) P, φ t * ∫ y : Space, ∑ i : Fin 3, a (t, y) i * θ y i := by
    have h := hpair
    simp only [UnforcedLeray.Short.IIb.HasPtwOp, UnforcedLeray.Cons.C03.Concrete.pairF,
      UnforcedLeray.Cons.C03.Concrete.phaseInt, hG1, hG2] at h
    exact smul_right_injective ℂ (inv_ne_zero hP.ne') h
  have hdef : ∀ t : ℝ, φ t * sliceDefect ν Φ a θ t
      = φ t * ((ν : ℂ) * ∫ y : Space, ∑ i : Fin 3,
          Φ (t, y) i * UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i)
        - φ t * ∫ y : Space, ∑ i : Fin 3, a (t, y) i * θ y i := by
    intro t
    unfold sliceDefect
    ring
  obtain ⟨hLs, hLc⟩ := lapS_props hθ hc
  have hI1 : IntegrableOn (fun t : ℝ => ∫ y : Space, ∑ i : Fin 3,
      Φ (t, y) i * UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i) (Ioc 0 P) :=
    sliceInt_integrableOn hP hΦ hLs.continuous hLc
  have hI2 : IntegrableOn (fun t : ℝ => ∫ y : Space, ∑ i : Fin 3, a (t, y) i * θ y i) (Ioc 0 P) :=
    sliceInt_integrableOn hP ha hθ.continuous hc
  have hint1 := integrableOn_mul_bdd (P := P) hφc.continuous (hI1.const_mul (ν : ℂ))
  have hint2 := integrableOn_mul_bdd (P := P) hφc.continuous hI2
  show ∫ t in Ioc (0 : ℝ) P, φ t * sliceDefect ν Φ a θ t = 0
  simp only [hdef]
  rw [integral_sub hint1 hint2, hpair', sub_self]

end UnforcedLeray.Short.PartIIIb.Concrete
