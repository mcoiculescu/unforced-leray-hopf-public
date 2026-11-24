import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.RecvConv.HolderPhase
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.RbFacts
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.VelSliceMeas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.RepPhasePointwise
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLift.CartLift
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WeakDmuAdd


set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.PhaseSpace

/-- Pure ENNReal algebra: `(K A)^{1/2} ≤ X (K I)^{1/2}` when `A ≤ X² I`. -/
private theorem holder_alg (K A I X : ℝ≥0∞) (h : A ≤ X ^ 2 * I) :
    (K * A) ^ (1 / 2 : ℝ) ≤ X * (K * I) ^ (1 / 2 : ℝ) := by
  have hsq : (X ^ 2) ^ (1 / 2 : ℝ) = X := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc (K * A) ^ (1 / 2 : ℝ) ≤ (K * (X ^ 2 * I)) ^ (1 / 2 : ℝ) := by gcongr
    _ = (X ^ 2) ^ (1 / 2 : ℝ) * (K * I) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        congr 1
        ring
    _ = X * (K * I) ^ (1 / 2 : ℝ) := by rw [hsq]

/-- **(iii), all phases** (source 5134-5139, 5336): the physical repair stress satisfies the
phase `L²_τL²_y` bound `‖𝒩_T repG w‖ ≤ 2ρ_b ‖𝒩_vw‖_{L²_τL^{22/3}}`, from the pointwise bound at
every `(τ, y)`, `RecvHolderPhase` at each phase and `‖r_b(τ)‖_{11/4} ≤ ρ_b`. -/
theorem RecvConvOrg.recvHolder : RecvConvOrg.RecvHolder := by
  intro Pl K L S hC0 hsplit hP w
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf L.ν := cOf_pos hν
  obtain ⟨hax, hper, hrbm⟩ := rbFacts Pl K L S hsplit hP
  set P := 2 * L.ε * cOf L.ν with hPdef
  have hP0 : 0 < P := by rw [hPdef]; positivity
  -- pointwise bound at every (τ, y)
  have hbound : ∀ τ y, UnforcedLeray.Short.IIIa.tensorNorm
      (strPhys L.ε⁻¹ (cOf L.ν) (repG Pl K L w) (τ, y)) ≤
        2 * ‖L.rb τ y‖ * ‖velPhys L.ε⁻¹ (cOf L.ν) w (τ, y)‖ := by
    intro τ y
    have e : strPhys L.ε⁻¹ (cOf L.ν) (repG Pl K L w) (τ, y) =
        symProd (L.rb τ y) (Nv L.ε⁻¹ (perExt (cOf L.ν) w) τ y) :=
      cartLiftSymOuter_proved L.ε⁻¹ (cOf L.ν) L.rb hR hc hax hper w τ y
    have hv : ‖velPhys L.ε⁻¹ (cOf L.ν) w (τ, y)‖ =
        ‖Nv L.ε⁻¹ (perExt (cOf L.ν) w) τ y‖ :=
      wda_norm_realC _
    rw [e, hv]
    exact tensorNorm_symProd_le' _ _
  -- the per-phase Hölder bound
  have hphase : ∀ᵐ τ ∂(volume.restrict (Ioc 0 P)),
      (∫⁻ y : Space, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
          (strPhys L.ε⁻¹ (cOf L.ν) (repG Pl K L w) (τ, y))) ^ (2 : ℝ)) ^ (2 / (2 : ℝ)) ≤
        ENNReal.ofReal (2 * L.ρb Pl K) ^ 2 *
          (∫⁻ y : Space, ‖velPhys L.ε⁻¹ (cOf L.ν) w (τ, y)‖ₑ ^ (22 / 3 : ℝ)) ^
            (2 / (22 / 3 : ℝ)) := by
    filter_upwards [velSliceMeas Pl L w] with τ h2
    have he : eLpNorm (L.rb τ) (ENNReal.ofReal UnforcedLeray.Short.IIb.bgp) volume ≤
        ENNReal.ofReal (L.ρb Pl K) :=
      le_trans le_self_add (hsplit.energy τ)
    have hH := RecvConvOrg.recvHolderPhase (L.rb τ)
      (fun y => velPhys L.ε⁻¹ (cOf L.ν) w (τ, y))
      (fun y => UnforcedLeray.Short.IIIa.tensorNorm
        (strPhys L.ε⁻¹ (cOf L.ν) (repG Pl K L w) (τ, y)))
      (hrbm τ) h2 (ae_of_all _ fun y => hbound τ y)
    refine le_trans hH ?_
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), mul_pow]
    gcongr
  -- integrate over the phase cell
  have hne : ENNReal.ofReal (2 * L.ρb Pl K) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hA : (∫⁻ t in Ioc (0 : ℝ) P, (∫⁻ y : Space, ENNReal.ofReal
          (UnforcedLeray.Short.IIIa.tensorNorm (strPhys L.ε⁻¹ (cOf L.ν) (repG Pl K L w) (t, y))) ^
            (2 : ℝ)) ^ (2 / (2 : ℝ))) ≤
      ENNReal.ofReal (2 * L.ρb Pl K) ^ 2 * ∫⁻ τ in Ioc (0 : ℝ) P,
        (∫⁻ y : Space, ‖velPhys L.ε⁻¹ (cOf L.ν) w (τ, y)‖ₑ ^ (22 / 3 : ℝ)) ^
          (2 / (22 / 3 : ℝ)) := by
    rw [← lintegral_const_mul' _ _ hne]
    exact lintegral_mono_ae hphase
  have hK : ENNReal.ofReal P⁻¹ = (ENNReal.ofReal P)⁻¹ := ENNReal.ofReal_inv_of_pos hP0
  unfold phaseL2Lr UnforcedLeray.Short.IIIa.ltauLq
  rw [hK]
  exact holder_alg _ _ _ _ hA

end UnforcedLeray.Short.PartIIIb.Concrete
