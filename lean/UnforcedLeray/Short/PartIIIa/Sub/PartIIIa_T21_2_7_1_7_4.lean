import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_1_7
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.Pairing

/-!
# `PartIII-a:T21/2/7/1/7/4`: decomposition of `LocAdjPointwise`

Source: `the November 2 reference manuscript`
lines 3052-3058 (adjoint localized interaction; `K_c^T` applied to `F_j = w ∂_jE(r)`), 2875-2896.

`LocAdjChi m`: for each `r ∈ [0,T]` and `w ∈ X_{-m,c}`, `K_c^T (w ∇E(r))` is an element `χ` of
`X_{-m,c}` with `‖χ‖ ≤ β₀ ‖w‖` and `∫ χ ψ = ∫ w (uψ·∇E)` for every cylinder test with kernel
velocity (from `KernelAdjointBound`, `LocFieldBound`, and measurability of `χ`).
`locAdjPointwise_of_chi`: linearity of `w ↦ χ_w` follows from `LocCylUniq`, `LocBSExists` and
integrability (`LocPairInt`), giving the bounded operator.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Weak derivatives force measurability (SP 3052-3057): if `χ` has a weak cell derivative
(so `χ ψ` is integrable for every cylinder test `ψ`, in particular for tests equal to `1` on
`|η| ≤ n`), then `χ` is a.e.-strongly measurable on the cell. -/
def LocWeakMeas : Prop :=
  ∀ (d : ℝ), 1 ≤ d → ∀ (j : Fin 2) (χ g : ℝ × ℝ → ℂ), HasWeakCellDerivC d j χ g →
    AEStronglyMeasurable χ (volume.restrict (B0579.cell d))

/-- Existence of the kernel Biot-Savart velocity of a cylinder test (SP 2875-2896, 3052-3057;
`u = kerVel c ψ`). -/
def LocBSExists : Prop :=
  ∀ c : ℝ, 1 ≤ c → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → ∃ u, IsKernelBiotSavart c ψ u

/-- The kernel adjoint of `w ∇E(r)` as an element of `X_{-m,c}` (SP 3052-3058). -/
def LocAdjChi (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), ∀ T C : ℝ,
    0 ≤ T → LadTrainBdd tr m T C →
    ∃ β₀ : ℝ, 0 ≤ β₀ ∧ ∀ r ∈ Icc (0 : ℝ) T, ∀ w : AdjX (ν ^ (-2 : ℝ)) m,
      ∃ χ : AdjX (ν ^ (-2 : ℝ)) m, ‖χ‖ ≤ β₀ * ‖w‖ ∧
        ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ),
          B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ → IsKernelBiotSavart (ν ^ (-2 : ℝ)) ψ uψ →
            ∫ x in B0579.cell (ν ^ (-2 : ℝ)), χ x * (ψ x : ℂ) =
              ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w x *
                ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
                  uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)

namespace LocPtAux

theorem ae_add {c m : ℝ} (f g : AdjX c m) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ((f + g : AdjX c m) : ℝ × ℝ → ℂ) x = f x + g x :=
  (B0579.ac_cellMeasure c (-m)).ae_le (Lp.coeFn_add f g)

theorem ae_sub {c m : ℝ} (f g : AdjX c m) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ((f - g : AdjX c m) : ℝ × ℝ → ℂ) x = f x - g x :=
  (B0579.ac_cellMeasure c (-m)).ae_le (Lp.coeFn_sub f g)

theorem ae_smul {c m : ℝ} (a : ℂ) (f : AdjX c m) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ((a • f : AdjX c m) : ℝ × ℝ → ℂ) x = a * f x := by
  filter_upwards [(B0579.ac_cellMeasure c (-m)).ae_le (Lp.coeFn_smul a f)] with x hx
  simpa using hx

end LocPtAux

open LocPtAux in
/-- Linearity of the kernel adjoint via uniqueness, then boundedness (SP 3052-3058). -/
theorem locAdjPointwise_of_chi (m : ℝ) (hI : LocPairInt m) (hU : LocCylUniq) (hB : LocBSExists)
    (hA : LocAdjChi m) : LocAdjPointwise m := by
  intro ν hν hν1 tr T C hT hb
  obtain ⟨β₀, hβ₀, hχ⟩ := hA ν hν hν1 tr T C hT hb
  refine ⟨β₀, fun r hr => ?_⟩
  have hc0 : 0 < (ν ^ (-2 : ℝ)) := Real.rpow_pos_of_pos hν _
  have hc1 : 1 ≤ (ν ^ (-2 : ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  choose! χ hχn hχid using hχ r hr
  -- the integrand of the right-hand side
  set g : (ℝ × ℝ → Fin 2 → ℝ) → ℝ × ℝ → ℂ := fun uψ x =>
    ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
      uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) with hg
  have hint : ∀ (w : AdjX (ν ^ (-2 : ℝ)) m) ψ uψ, B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ → IsKernelBiotSavart (ν ^ (-2 : ℝ)) ψ uψ →
      IntegrableOn (fun x => w x * g uψ x) (B0579.cell (ν ^ (-2 : ℝ))) := fun w ψ uψ hψ hu =>
    hI ν hν hν1 tr T C hT hb r hr w ψ uψ hψ hu
  have hpint : ∀ (f : AdjX (ν ^ (-2 : ℝ)) m) ψ, B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ →
      IntegrableOn (fun x => f x * (ψ x : ℂ)) (B0579.cell (ν ^ (-2 : ℝ))) := fun f ψ hψ =>
    (adjPairing (ν ^ (-2 : ℝ)) m hc0 ψ hψ).1 f
  -- uniqueness
  have huniq : ∀ f : AdjX (ν ^ (-2 : ℝ)) m, (∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ),
      B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ → IsKernelBiotSavart (ν ^ (-2 : ℝ)) ψ uψ →
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f x * (ψ x : ℂ) = 0) → f = 0 := fun f h =>
    hU (ν ^ (-2 : ℝ)) m hc0 f fun ψ hψ => by
      obtain ⟨u, hu⟩ := hB (ν ^ (-2 : ℝ)) hc1 ψ hψ
      exact h ψ u hψ hu
  have hadd : ∀ w₁ w₂, χ (w₁ + w₂) = χ w₁ + χ w₂ := by
    intro w₁ w₂
    rw [← sub_eq_zero]
    apply huniq
    intro ψ u hψ hu
    have e1 : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (χ (w₁ + w₂) - (χ w₁ + χ w₂) : AdjX (ν ^ (-2 : ℝ)) m) x * (ψ x : ℂ) =
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (χ (w₁ + w₂) x * (ψ x : ℂ) - (χ w₁ x * (ψ x : ℂ) +
          χ w₂ x * (ψ x : ℂ))) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_sub (χ (w₁ + w₂)) (χ w₁ + χ w₂), ae_add (χ w₁) (χ w₂)] with x h1 h2
      rw [h1, h2]; ring
    have hs : IntegrableOn (fun x => χ w₁ x * (ψ x : ℂ) + χ w₂ x * (ψ x : ℂ))
        (B0579.cell (ν ^ (-2 : ℝ))) := (hpint _ ψ hψ).add (hpint _ ψ hψ)
    rw [e1, integral_sub (hpint _ ψ hψ) hs,
      integral_add (hpint _ ψ hψ) (hpint _ ψ hψ), hχid _ ψ u hψ hu, hχid _ ψ u hψ hu,
      hχid _ ψ u hψ hu]
    have e2 : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (w₁ + w₂ : AdjX (ν ^ (-2 : ℝ)) m) x * g u x =
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (w₁ x * g u x + w₂ x * g u x) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_add w₁ w₂] with x h
      rw [h]; ring
    rw [e2, integral_add (hint w₁ ψ u hψ hu) (hint w₂ ψ u hψ hu)]
    ring
  have hsmul : ∀ (a : ℂ) w, χ (a • w) = a • χ w := by
    intro a w
    rw [← sub_eq_zero]
    apply huniq
    intro ψ u hψ hu
    have e1 : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (χ (a • w) - a • χ w : AdjX (ν ^ (-2 : ℝ)) m) x * (ψ x : ℂ) =
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (χ (a • w) x * (ψ x : ℂ) - a * (χ w x * (ψ x : ℂ))) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_sub (χ (a • w)) (a • χ w), ae_smul a (χ w)] with x h1 h2
      rw [h1, h2]; ring
    rw [e1, integral_sub (hpint _ ψ hψ) ((hpint _ ψ hψ).const_mul a), integral_const_mul,
      hχid _ ψ u hψ hu, hχid _ ψ u hψ hu]
    have e2 : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (a • w : AdjX (ν ^ (-2 : ℝ)) m) x * g u x =
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), a * (w x * g u x) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_smul a w] with x h
      rw [h]; ring
    rw [e2, integral_const_mul]
    ring
  let L : AdjX (ν ^ (-2 : ℝ)) m →ₗ[ℂ] AdjX (ν ^ (-2 : ℝ)) m :=
    { toFun := χ, map_add' := hadd, map_smul' := fun a w => by simpa using hsmul a w }
  refine ⟨L.mkContinuous β₀ hχn, LinearMap.mkContinuous_norm_le _ hβ₀ _, ?_⟩
  intro w ψ uψ hψ hu
  exact hχid w ψ uψ hψ hu

end UnforcedLeray.Short.IIIa
