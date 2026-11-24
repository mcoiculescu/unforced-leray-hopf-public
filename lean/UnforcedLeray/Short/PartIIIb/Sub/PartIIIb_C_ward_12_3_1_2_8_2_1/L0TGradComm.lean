import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1.ProjCommuteProps
import UnforcedLeray.Units.B0005.Bridge.Commute

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/1`: `L₀ᵗ` on gradients

Source `the November 2 reference manuscript`
lines 1393-1400, 1409-1412.  Proves `L0TGradComm` (`ProjCommuteProps.lean`):
`L₀ᵗ(∇ψ) = ∇(L0Tscal ν ψ)` for smooth scalar `ψ`.  The scalar identities
`driftT (∇ψ) = ∇(driftT ψ - ½ψ)` and `Δ(∇ψ) = ∇(Δψ)` are `B0005.driftT_gradT` and
`B0005.lapT_gradT` (`Units/B0005/Bridge/Commute.lean`); what remains is linearity of `∇` and the
algebraic identity `driftT ψ - ν Δψ - ψ = L0Tscal ν ψ`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped ContDiff

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Short.PartIIIb.Concrete

namespace UnforcedLeray.Short.PartIIIb.Concrete.L0TGradCommAux

theorem diffS {G : ℝ × UnforcedLeray.Space → ℂ} (hG : ContDiff ℝ ∞ G) :
    Differentiable ℝ G :=
  hG.differentiable (by simp)

theorem contDiff_csmul_S {G : ℝ × UnforcedLeray.Space → ℂ} (c : ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (c • G) :=
  ContDiff.const_smul c hG

theorem dy_add_S {G H : ℝ × UnforcedLeray.Space → ℂ} (hG : Differentiable ℝ G)
    (hH : Differentiable ℝ H) (j : Fin 3) : dy j (G + H) = dy j G + dy j H := by
  funext p
  simp [dy, fderiv_add (hG p) (hH p)]

theorem dy_sub_S {G H : ℝ × UnforcedLeray.Space → ℂ} (hG : Differentiable ℝ G)
    (hH : Differentiable ℝ H) (j : Fin 3) : dy j (G - H) = dy j G - dy j H := by
  funext p
  simp [dy, fderiv_sub (hG p) (hH p)]

theorem dy_smul_S {G : ℝ × UnforcedLeray.Space → ℂ} (hG : Differentiable ℝ G) (c : ℝ)
    (j : Fin 3) : dy j (c • G) = c • dy j G := by
  funext p
  simp [dy, fderiv_const_smul (hG p) c]

theorem gradT_add_S {G H : ℝ × UnforcedLeray.Space → ℂ} (hG : Differentiable ℝ G)
    (hH : Differentiable ℝ H) : gradT (G + H) = gradT G + gradT H := by
  funext p
  simp only [gradT, Pi.add_apply, dy_add_S hG hH, add_smul, Finset.sum_add_distrib]

theorem gradT_sub_S {G H : ℝ × UnforcedLeray.Space → ℂ} (hG : Differentiable ℝ G)
    (hH : Differentiable ℝ H) : gradT (G - H) = gradT G - gradT H := by
  funext p
  simp only [gradT, Pi.sub_apply, dy_sub_S hG hH, sub_smul, Finset.sum_sub_distrib]

theorem gradT_smul_S {G : ℝ × UnforcedLeray.Space → ℂ} (hG : Differentiable ℝ G) (c : ℝ) :
    gradT (c • G) = c • gradT G := by
  funext p
  simp only [gradT, Pi.smul_apply, dy_smul_S hG c, Finset.smul_sum, smul_assoc]

theorem contDiff_lapT_S {G : ℝ × UnforcedLeray.Space → ℂ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (lapT G) := by
  show ContDiff ℝ ∞ (fun p => ∑ j : Fin 3, dy j (dy j G) p)
  exact ContDiff.sum fun j _ => UnforcedLeray.B0005.contDiff_dy' (UnforcedLeray.B0005.contDiff_dy' hG j) j

theorem L0T_gradComm_aux (ν : ℝ) (ψ : ℝ × UnforcedLeray.Space → ℂ) (hψ : ContDiff ℝ ∞ ψ) :
    L0T ν (gradT ψ) = gradT (L0Tscal ν ψ) := by
  have h1 := UnforcedLeray.B0005.driftT_gradT hψ
  have h2 := UnforcedLeray.B0005.lapT_gradT hψ
  have hR : L0Tscal ν ψ = driftT ψ - (1 / 2 : ℝ) • ψ - ν • lapT ψ - (1 / 2 : ℝ) • ψ := by
    funext p
    simp only [L0Tscal, driftT, Pi.sub_apply, Pi.smul_apply]
    module
  have hdr : ContDiff ℝ ∞ (driftT ψ) := UnforcedLeray.B0005.contDiff_driftT' hψ
  have hlap : ContDiff ℝ ∞ (lapT ψ) := contDiff_lapT_S hψ
  have hX : Differentiable ℝ (driftT ψ - (1 / 2 : ℝ) • ψ) :=
    diffS (hdr.sub (contDiff_csmul_S _ hψ))
  have hY : Differentiable ℝ (ν • lapT ψ) := diffS (contDiff_csmul_S _ hlap)
  have hC : Differentiable ℝ ((1 / 2 : ℝ) • ψ) := diffS (contDiff_csmul_S _ hψ)
  have hXY : Differentiable ℝ (driftT ψ - (1 / 2 : ℝ) • ψ - ν • lapT ψ) :=
    hX.sub hY
  simp only [L0T, nuLapT]
  rw [h1, h2, hR, gradT_sub_S hXY hC, gradT_sub_S hX hY, gradT_smul_S (diffS hlap) ν,
    gradT_smul_S (diffS hψ) (1 / 2 : ℝ)]

end UnforcedLeray.Short.PartIIIb.Concrete.L0TGradCommAux

theorem l0TGradComm : UnforcedLeray.Short.PartIIIb.Concrete.L0TGradComm := by
  intro ν ψ hψ
  exact UnforcedLeray.Short.PartIIIb.Concrete.L0TGradCommAux.L0T_gradComm_aux ν ψ hψ
