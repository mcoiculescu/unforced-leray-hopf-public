import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_1_7_4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.Pairing

/-!
# `PartIII-a:T21/2/7/1/7/5`: decomposition of `LocAdjStrongCont`

Source: `the November 2 reference manuscript`
lines 3052-3058 (adjoint localized interaction `K_c^T(w ∇E(r))`), 2875-2896 (periodic kernel).

Route: for `r, r₀ ∈ [0, T]` the kernel adjoint of the difference field
`F_j = w ∂_jE(r) - w ∂_jE(r₀)` is an element `χ` of `X_{-m,c}` (`LocKerAdjElt`); by the
characterising identities, the pairing integrability (`LocPairInt`), the existence of the kernel
Biot-Savart velocity (`LocBSExists`) and uniqueness (`LocCylUniq`) one has `K r w - K r₀ w = χ`, so
`‖K r w - K r₀ w‖ ≤ C_K Σ_j (‖F_j‖₁ + ‖F_j‖₂)`, and the right side tends to `0` as `r → r₀`
(dominated convergence, `LocFieldDiffSmall`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **(S1) The kernel adjoint as an element of `X_{-m,c}`** (SP 3052-3058, 2875-2896): for `c ≥ 1`
and any `L¹ ∩ L²` field `F` on the cell, the kernel adjoint `χ = K_c^T F` of `KernelAdjointBound`
is a.e.-strongly measurable (`LocWeakMeas`: a weak cell derivative forces measurability), and
`xNorm c (-m) χ ≤ h1Norm c m χ g` is finite, so `χ` is an element of `X_{-m,c}` with norm at most
`C_K Σ_j (‖F_j‖₁ + ‖F_j‖₂)` and `∫ χ ψ = ∫ Σ_j F_j (uψ)_j` for every cylinder test `ψ` with kernel
velocity. -/
def LocKerAdjElt (m : ℝ) : Prop :=
  ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ c : ℝ, 1 ≤ c → ∀ F : Fin 2 → ℝ × ℝ → ℂ,
    (∀ j, IntegrableOn (F j) (B0579.cell c) ∧
      MemLp (F j) 2 (volume.restrict (B0579.cell c))) →
    ∃ χ : AdjX c m, ‖χ‖ₑ ≤ ENNReal.ofReal Ck * ∑ j : Fin 2,
        (eLpNorm (F j) 1 (volume.restrict (B0579.cell c)) +
          eLpNorm (F j) 2 (volume.restrict (B0579.cell c))) ∧
      ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ),
        B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ uψ →
          ∫ x in B0579.cell c, χ x * (ψ x : ℂ) =
            ∫ x in B0579.cell c, ∑ j : Fin 2, F j x * ((uψ x j : ℝ) : ℂ)

/-- **(S2) Time continuity of the vorticity gradient, pointwise in space** (joint smoothness of the
train on `[0, ∞) × ℝ²`, `tr.isTrain.smooth_v`; `E = ∂_q v₂ - ∂_η v₁`, so `∂_jE` is a second
derivative of the jointly smooth `v`). -/
def LocPdEcCont : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (j : Fin 2) (x : ℝ × ℝ),
    ContinuousOn (fun r => B0579.pd j (UnforcedLeray.B0238.Ec tr r) x) (Ici 0)

/-- **(S3) The field difference is small** (SP 3052-3058; dominated convergence). For
`F_j(r) = w ∂_jE(r)`: `‖F_j(r) - F_j(r₀)‖_{L¹(cell)} + ‖F_j(r) - F_j(r₀)‖_{L²(cell)} → 0` as
`r → r₀` in `[0, T]`. Dominating function `2C |w| jb^{-(m+2)/2}` (`LadTrainBdd`), which lies in
`L¹ ∩ L²(cell)` since `‖w jb^{-m/2}‖_{L²} = ‖w‖_{X_{-m,c}}` and `jb^{-1} ∈ L² ∩ L^∞`. -/
def LocFieldDiffSmall (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), ∀ T C : ℝ,
    0 ≤ T → LadTrainBdd tr m T C →
    ∀ (w : AdjX (ν ^ (-2 : ℝ)) m) (r₀ : ℝ), r₀ ∈ Icc (0 : ℝ) T → ∀ j : Fin 2,
      Tendsto (fun r : ℝ =>
        eLpNorm (fun x => w x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) -
            w x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ)) 1
          (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) +
        eLpNorm (fun x => w x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) -
            w x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ)) 2
          (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))))
        (𝓝[Icc (0 : ℝ) T] r₀) (𝓝 0)

open LocPtAux in
/-- Assembly of `LocAdjStrongCont` from the kernel-adjoint element, the pairing integrability,
the Biot-Savart existence, uniqueness, the field bound and the smallness of the field difference. -/
theorem locAdjStrongCont_of (m : ℝ) (hI : LocPairInt m) (hF : LocFieldBound m)
    (hU : LocCylUniq) (hB : LocBSExists) (hE : LocKerAdjElt m) (hD : LocFieldDiffSmall m) :
    LocAdjStrongCont m := by
  intro ν hν hν1 tr T C hT hb K β hKn hKid w r₀ hr₀
  have hc0 : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hc1 : (1 : ℝ) ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  obtain ⟨Ck, hCk0, hCk⟩ := hE
  obtain ⟨C', hC'0, hC'⟩ := hF ν hν hν1 tr T C hT hb
  set μ : Measure (ℝ × ℝ) := volume.restrict (B0579.cell (ν ^ (-2 : ℝ))) with hμ
  set pdE : ℝ → Fin 2 → ℝ × ℝ → ℂ := fun r j x =>
    w x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) with hpdE
  have hpint : ∀ (f : AdjX (ν ^ (-2 : ℝ)) m) ψ, B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ →
      IntegrableOn (fun x => f x * (ψ x : ℂ)) (B0579.cell (ν ^ (-2 : ℝ))) := fun f ψ hψ =>
    (adjPairing (ν ^ (-2 : ℝ)) m hc0 ψ hψ).1 f
  have key : ∀ r ∈ Icc (0 : ℝ) T, ‖K r w - K r₀ w‖ₑ ≤ ENNReal.ofReal Ck * ∑ j : Fin 2,
      (eLpNorm (fun x => pdE r j x - pdE r₀ j x) 1 μ +
        eLpNorm (fun x => pdE r j x - pdE r₀ j x) 2 μ) := by
    intro r hr
    have hF_ : ∀ j, IntegrableOn (fun x => pdE r j x - pdE r₀ j x)
        (B0579.cell (ν ^ (-2 : ℝ))) ∧ MemLp (fun x => pdE r j x - pdE r₀ j x) 2 μ :=
      fun j => ⟨((hC' r hr w j).1).sub ((hC' r₀ hr₀ w j).1),
        ((hC' r hr w j).2.1).sub ((hC' r₀ hr₀ w j).2.1)⟩
    obtain ⟨χ, hχn, hχid⟩ := hCk _ hc1 (fun j x => pdE r j x - pdE r₀ j x) hF_
    have hD0 : K r w - K r₀ w - χ = 0 := by
      apply hU (ν ^ (-2 : ℝ)) m hc0
      intro ψ hψ
      obtain ⟨u, hu⟩ := hB (ν ^ (-2 : ℝ)) hc1 ψ hψ
      have e1 : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (K r w - K r₀ w - χ : AdjX (ν ^ (-2 : ℝ)) m) x *
          (ψ x : ℂ) = ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            ((K r w x * (ψ x : ℂ) - K r₀ w x * (ψ x : ℂ)) - χ x * (ψ x : ℂ)) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_sub (K r w - K r₀ w) χ, ae_sub (K r w) (K r₀ w)] with x h1 h2
        rw [h1, h2]; ring
      have i1 := hpint (K r w) ψ hψ
      have i2 := hpint (K r₀ w) ψ hψ
      have i3 := hpint χ ψ hψ
      have i12 : IntegrableOn (fun x => K r w x * (ψ x : ℂ) - K r₀ w x * (ψ x : ℂ))
          (B0579.cell (ν ^ (-2 : ℝ))) := i1.sub i2
      rw [e1, integral_sub i12 i3, integral_sub i1 i2, hKid r hr w ψ u hψ hu,
        hKid r₀ hr₀ w ψ u hψ hu, hχid ψ u hψ hu]
      have e2 : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), ∑ j : Fin 2,
          (pdE r j x - pdE r₀ j x) * ((u x j : ℝ) : ℂ) =
          ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (w x *
            ((u x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
              u x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) -
            w x * ((u x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r₀) x +
              u x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ)) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [Fin.sum_univ_two, hpdE]
        push_cast
        ring
      rw [e2, integral_sub (hI ν hν hν1 tr T C hT hb r hr w ψ u hψ hu)
        (hI ν hν hν1 tr T C hT hb r₀ hr₀ w ψ u hψ hu)]
      ring
    have : K r w - K r₀ w = χ := sub_eq_zero.1 hD0
    rw [this]
    exact hχn
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal Ck * ∑ j : Fin 2,
      (eLpNorm (fun x => pdE r j x - pdE r₀ j x) 1 μ +
        eLpNorm (fun x => pdE r j x - pdE r₀ j x) 2 μ)) (𝓝[Icc (0 : ℝ) T] r₀) (𝓝 0) := by
    have h0 : Tendsto (fun r : ℝ => ∑ j : Fin 2,
        (eLpNorm (fun x => pdE r j x - pdE r₀ j x) 1 μ +
          eLpNorm (fun x => pdE r j x - pdE r₀ j x) 2 μ)) (𝓝[Icc (0 : ℝ) T] r₀) (𝓝 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (Fin 2))
        (fun j _ => hD ν hν hν1 tr T C hT hb w r₀ hr₀ j)
      simpa only [Finset.sum_const_zero] using this
    have := ENNReal.Tendsto.const_mul h0 (Or.inr (ENNReal.ofReal_ne_top (r := Ck)))
    simpa only [mul_zero] using this
  have hz : Tendsto (fun r : ℝ => ‖K r w - K r₀ w‖ₑ) (𝓝[Icc (0 : ℝ) T] r₀) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => bot_le)
      (eventually_nhdsWithin_of_forall fun r hr => key r hr)
  exact tendsto_iff_enorm_sub_tendsto_zero.2 hz

end UnforcedLeray.Short.IIIa
