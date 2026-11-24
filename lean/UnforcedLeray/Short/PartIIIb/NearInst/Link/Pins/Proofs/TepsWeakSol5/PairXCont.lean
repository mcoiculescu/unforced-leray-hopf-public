import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellHolder

/-!
# `PairXCont` (task `PartIII-b:C/near/pins/3/5/2`)

For a phase test `φ`, the pairing `F ↦ ⟨∇φ, F⟩ = pairX P (gradT φ) F` is a bounded linear functional
on `X SpaceC P = L²(PSpace P)`.  The pairing is realised as `P⁻¹ ∫_{PSpace} dotL (Φ̃ z) (F z)`, where
`Φ̃ (y, s) = Φ(τ, y)` for any lift `τ` of `s`; `Φ̃` is continuous with compact support, hence in `L²`,
and `ContinuousLinearMap.lpPairing` gives the bounded functional.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0223 (MeridC SpaceC X PSpace volume_pspace)

/-- The periodicity of a phase test, as a periodic family of slices. -/
theorem pxc_periodic {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    Function.Periodic (fun τ : ℝ => fun y : Space => Φ (τ, y)) P :=
  fun τ => funext fun y => hΦ.periodic τ y

/-- The phase-space lift `(y, s) ↦ Φ(τ, y)` for any lift `τ` of `s ∈ ℝ/Pℤ`. -/
def pxcLift {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hper : Function.Periodic (fun τ : ℝ => fun y : Space => Φ (τ, y)) P) :
    PSpace P → CVec3 :=
  fun z => hper.lift z.2 z.1

theorem pxcLift_coe {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hper : Function.Periodic (fun τ : ℝ => fun y : Space => Φ (τ, y)) P) (t : ℝ) (y : Space) :
    pxcLift hper (y, (t : AddCircle P)) = Φ (t, y) := by
  simp only [pxcLift]
  exact congrFun (hper.lift_coe t) y

theorem pxcLift_continuous {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (hper : Function.Periodic (fun τ : ℝ => fun y : Space => Φ (τ, y)) P) :
    Continuous (pxcLift hper) := by
  have h1 : IsOpenQuotientMap
      (Prod.map (id : Space → Space) (QuotientAddGroup.mk : ℝ → AddCircle P)) :=
    IsOpenQuotientMap.prodMap IsOpenQuotientMap.id QuotientAddGroup.isOpenQuotientMap_mk
  have h2 : IsOpenQuotientMap (Prod.swap : ℝ × Space → Space × ℝ) :=
    (Homeomorph.prodComm ℝ Space).isOpenQuotientMap
  have hq : Topology.IsQuotientMap (fun x : ℝ × Space => ((x.2, (x.1 : AddCircle P)) : PSpace P)) :=
    (h1.comp h2).isQuotientMap
  refine hq.continuous_iff.mpr ?_
  have hcomp : (pxcLift hper) ∘ (fun x : ℝ × Space => ((x.2, (x.1 : AddCircle P)) : PSpace P))
      = Φ := by
    funext x
    exact pxcLift_coe hper x.1 x.2
  rw [hcomp]
  exact hΦ.smooth.continuous

theorem pxcLift_hasCompactSupport {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (hper : Function.Periodic (fun τ : ℝ => fun y : Space => Φ (τ, y)) P) :
    HasCompactSupport (pxcLift hper) := by
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  refine HasCompactSupport.intro ((isCompact_closedBall (0 : Space) R).prod isCompact_univ) ?_
  rintro ⟨y, s⟩ hz
  obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective s
  have hy : R < ‖y‖ := by
    by_contra h
    exact hz ⟨mem_closedBall_zero_iff.mpr (not_lt.mp h), mem_univ _⟩
  exact (pxcLift_coe hper τ y).trans (hR τ y hy)

theorem pxcLift_memLp {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (hper : Function.Periodic (fun τ : ℝ => fun y : Space => Φ (τ, y)) P) :
    MemLp (pxcLift hper) 2 (volume : Measure (PSpace P)) :=
  (pxcLift_continuous hΦ hper).memLp_of_hasCompactSupport (pxcLift_hasCompactSupport hΦ hper)

/-- Integrability of the pairing integrand against an `L²` field. -/
theorem pxc_integrable {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (F : X SpaceC P) :
    Integrable (fun z : PSpace P => dotL (pxcLift (pxc_periodic hΦ) z) ((F : PSpace P → SpaceC) z))
      (volume : Measure (PSpace P)) := by
  have : ENNReal.HolderTriple 2 2 1 := ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  exact integrable_dotL_of_memLp_holder (pxcLift_memLp hΦ (pxc_periodic hΦ)) (Lp.memLp F)

/-- The pairing as an integral over the phase space. -/
theorem pairX_eq_smul_integral {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (F : X SpaceC P) :
    pairX P Φ F = (P⁻¹ : ℝ) •
      ∫ z : PSpace P, dotL (pxcLift (pxc_periodic hΦ) z) ((F : PSpace P → SpaceC) z) := by
  have e1 : (∫ t in Ioc (0 : ℝ) P, (∫ y : Space,
      dotL (Φ (t, y)) ((F : PSpace P → SpaceC) (y, (t : AddCircle P))))) =
      ∫ t in Ioc (0 : ℝ) P, (∫ y : Space,
        dotL (pxcLift (pxc_periodic hΦ) (y, (t : AddCircle P)))
          ((F : PSpace P → SpaceC) (y, (t : AddCircle P)))) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    congr 1
  have e2 : (∫ t in Ioc (0 : ℝ) P, (∫ y : Space,
      dotL (pxcLift (pxc_periodic hΦ) (y, (t : AddCircle P)))
        ((F : PSpace P → SpaceC) (y, (t : AddCircle P))))) =
      ∫ s : AddCircle P, ∫ y : Space,
        dotL (pxcLift (pxc_periodic hΦ) (y, s)) ((F : PSpace P → SpaceC) (y, s)) := by
    have h := AddCircle.integral_preimage P 0
      (fun s : AddCircle P => ∫ y : Space,
        dotL (pxcLift (pxc_periodic hΦ) (y, s)) ((F : PSpace P → SpaceC) (y, s)))
    simpa only [zero_add] using h
  have e3 : ∫ z : PSpace P, dotL (pxcLift (pxc_periodic hΦ) z) ((F : PSpace P → SpaceC) z)
      = ∫ s : AddCircle P, ∫ y : Space,
        dotL (pxcLift (pxc_periodic hΦ) (y, s)) ((F : PSpace P → SpaceC) (y, s)) :=
    integral_prod_symm _ (pxc_integrable hΦ F)
  show (P⁻¹ : ℝ) • ∫ t in Ioc (0 : ℝ) P, (∫ y : Space,
      dotL (Φ (t, y)) ((F : PSpace P → SpaceC) (y, (t : AddCircle P)))) =
      (P⁻¹ : ℝ) • ∫ z : PSpace P, dotL (pxcLift (pxc_periodic hΦ) z) ((F : PSpace P → SpaceC) z)
  rw [e1, e2, e3]

theorem pairXCont : PairXCont := by
  intro P _ φ hφ
  have hΦ : IsPhaseTest P (gradT φ) := IsPhaseTest.gradT hφ
  obtain ⟨G, hG⟩ : ∃ G : Lp CVec3 2 (volume : Measure (PSpace P)),
      (G : PSpace P → CVec3) =ᵐ[volume] pxcLift (pxc_periodic hΦ) :=
    ⟨(pxcLift_memLp hΦ (pxc_periodic hΦ)).toLp _, MemLp.coeFn_toLp _⟩
  refine ⟨(P⁻¹ : ℝ) • dotL.lpPairing (volume : Measure (PSpace P)) 2 2 G, fun F => ?_⟩
  rw [smul_apply, ContinuousLinearMap.lpPairing_eq_integral,
    pairX_eq_smul_integral hΦ F]
  congr 1
  apply integral_congr_ae
  filter_upwards [hG] with z hz
  rw [hz]

end UnforcedLeray.Short.PartIIIb.NearInst
