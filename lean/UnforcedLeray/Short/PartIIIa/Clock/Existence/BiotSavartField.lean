import UnforcedLeray.Short.PartIIIa.Sub.T21_3_Strip
import UnforcedLeray.Short.PartIIIa.T20_4_VelocityIsBiotSavart

/-!
# Part III-a, `PartIII-a:T21/3/4`: the real Biot-Savart field of an actual vorticity

Source of record: `the November 2 reference manuscript`, lines 2823-2830.
`BiotSavartField hm`: for every `w` in the physical state space, the real velocity
`stripVel hm w = realBiotSavart w` is an `IsBiotSavart` velocity of `vortFn hm w`.

Proof. `CTE.velocityIsBiotSavart` is stated for `1 < m`; `velocityIsBiotSavart_one` is the same
proof (Sub/T20_4.lean, `velocityIsBiotSavart_of_weak`) with `1 ≤ m`, since its body uses only
`0 ≤ m` and the mode identities, which are `m`-free. The real part of a complex Biot-Savart
velocity of a real vorticity is a real Biot-Savart velocity (`isBS_re`: the complex identities
with real test functions, taking real parts, and the imaginary part of the curl identity is zero
because its left side is real). `realBiotSavart` is the real part of `B0583.velocity` a.e.
(`coeFn_realPartVelocityLp`), and `IsBiotSavart` depends on its velocity only up to a.e. equality
on the cell (`isBS_congr`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.IIIa

namespace CTE

/-- `CTE.velocityIsBiotSavart` for `1 ≤ m` (copy of the proof of `velocityIsBiotSavart_of_weak`). -/
theorem velocityIsBiotSavart_one : ∀ (c : ℝ) [Fact (0 < c)] (m : ℝ) (hm : 1 ≤ m)
    (ω : B0579.X c m) (hcirc : ∫ x in B0579.cell c, ω x = 0),
    IsBiotSavart c (fun x => ((ω x : ℝ) : ℂ))
      (fun x j => (B0583.velocity c hm ω hcirc : B0579.Plane → B0581.Vel) x j) := by
  have hD : NonzeroDivWeak := nonzeroDivWeak_of modeDiv
  have hC : NonzeroCurlWeak := nonzeroCurlWeak_of modeCurl synthEmbed0
  have hM : MeanPartOfX := meanPartOfX
  intro c hc m hm ω hcirc
  have hm0 : 0 ≤ m := (zero_le_one.trans hm)
  set u : Lp B0581.Vel 2 (B0581.cellVol c) := B0583.velocity c hm ω hcirc with hu
  set W : Lp ℂ 2 (B0581.cellVol c) := B0581.ofX c m hm0 ω with hW
  set nz : Lp ℂ 2 (B0581.cellVol c) := B0581.nonzeroPart c W with hnz
  have hq := (B0583.hasWeakVelDeriv_iff_inner c 0 u _).1
    (B0583.hasWeakVelDeriv_velocity_q c hm ω hcirc)
  have he := (B0583.hasWeakVelDeriv_iff_inner c 1 u _).1
    (B0583.hasWeakVelDeriv_velocity_eta c hm ω hcirc)
  have hw2 : MemLp (fun η => -B0583.omegaBar c ω η) 2 volume :=
    (B0583.zeroMode_facts hc.out hm ω hcirc).2.1.neg
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj j : B0581.Vel →L[ℂ] ℂ)
      (Lp.memLp u)
  · intro ψ hψ
    have I0 := B0583.integrable_testLp_mul c (hψ.pd 0) 0 u
    have I1 := B0583.integrable_testLp_mul c (hψ.pd 1) 1 u
    have hz1 : ⟪B0583.testLp c hψ 1, B0583.zeroVelEtaLp c hm ω hcirc⟫_ℂ = 0 := by
      rw [show B0583.zeroVelEtaLp c hm ω hcirc = (B0583.memLp_profField c hw2).toLp
          (B0583.profField fun η => -B0583.omegaBar c ω η) from rfl,
        B0583.inner_testLp_profField c hψ 1 hw2]
      simp
    have h0 := hq ψ hψ 0
    have h1 := he ψ hψ 1
    have hdiv := hD c nz hψ
    have e1 : ∫ x in B0579.cell c, (u x 0 * (B0579.pd 0 ψ x : ℂ) + u x 1 * (B0579.pd 1 ψ x : ℂ)) =
        ⟪B0583.testLp c (hψ.pd 0) 0, u⟫_ℂ + ⟪B0583.testLp c (hψ.pd 1) 1, u⟫_ℂ := by
      rw [B0583.inner_testLp, B0583.inner_testLp, ← integral_add I0 I1]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [mul_comm]
    have hg : B0583.velGradEta c hm ω hcirc =
        B0583.gradEta c nz + B0583.zeroVelEtaLp c hm ω hcirc := rfl
    have hg' : B0583.velGradQ c hm ω = B0583.gradQ c nz := rfl
    rw [e1, h0, h1, hg, hg', inner_add_right, hz1, add_zero]
    linear_combination -hdiv
  · intro ψ hψ
    have J0 := B0583.integrable_testLp_mul c (hψ.pd 1) 0 u
    have J1 := B0583.integrable_testLp_mul c (hψ.pd 0) 1 u
    have hz0 : ⟪B0583.testLp c hψ 0, B0583.zeroVelEtaLp c hm ω hcirc⟫_ℂ =
        -(∫ x, (ψ x : ℂ) * ((B0583.omegaBar c ω x.2 : ℝ) : ℂ) ∂(B0581.cellVol c)) := by
      rw [show B0583.zeroVelEtaLp c hm ω hcirc = (B0583.memLp_profField c hw2).toLp
          (B0583.profField fun η => -B0583.omegaBar c ω η) from rfl,
        B0583.inner_testLp_profField c hψ 0 hw2]
      simp only [PiLp.single_apply, ite_true, mul_one]
      have : ∫ x, ψ x * -B0583.omegaBar c ω x.2 ∂(B0581.cellVol c) =
          -∫ x, ψ x * B0583.omegaBar c ω x.2 ∂(B0581.cellVol c) := by
        simp only [mul_neg]
        exact integral_neg _
      rw [this, Complex.ofReal_neg, ← integral_complex_ofReal]
      push_cast
      rfl
    have hidem : B0581.nonzeroPart c nz = nz := by
      have h0 : B0581.meanPart c nz = 0 := by
        rw [B0581.meanPart, hnz, B0581.modes_nonzeroPart]
        simp only [↓reduceIte, map_zero]
      rw [B0581.nonzeroPart, h0, sub_zero]
    have hcurl := hC c nz hψ
    rw [hidem] at hcurl
    have e2 : ∫ x in B0579.cell c, (u x 0 * (B0579.pd 1 ψ x : ℂ) - u x 1 * (B0579.pd 0 ψ x : ℂ)) =
        ⟪B0583.testLp c (hψ.pd 1) 0, u⟫_ℂ - ⟪B0583.testLp c (hψ.pd 0) 1, u⟫_ℂ := by
      rw [B0583.inner_testLp, B0583.inner_testLp, ← integral_sub J0 J1]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [mul_comm]
    have hmean : ∫ x, (ψ x : ℂ) * (B0581.meanPart c W : B0579.Plane → ℂ) x ∂(B0581.cellVol c) =
        ∫ x, (ψ x : ℂ) * ((B0583.omegaBar c ω x.2 : ℝ) : ℂ) ∂(B0581.cellVol c) := by
      refine integral_congr_ae ?_
      filter_upwards [hM c m hm0 ω] with x hx
      rw [hx]
    have hsplit : ∫ x, ((ω x : ℝ) : ℂ) * (ψ x : ℂ) ∂(B0581.cellVol c) =
        ∫ x, (ψ x : ℂ) * (B0581.meanPart c W : B0579.Plane → ℂ) x ∂(B0581.cellVol c) +
          ∫ x, (ψ x : ℂ) * (nz : B0579.Plane → ℂ) x ∂(B0581.cellVol c) := by
      rw [← integral_add (integrable_psi_mul_lp c hψ _) (integrable_psi_mul_lp c hψ nz)]
      refine integral_congr_ae ?_
      filter_upwards [B0581.coeFn_ofX c m hm0 ω,
        Lp.coeFn_add (B0581.meanPart c W) nz] with x h1 h2
      rw [B0581.meanPart_add_nonzeroPart c W] at h2
      have h1' : (W : B0579.Plane → ℂ) x = ((ω x : ℝ) : ℂ) := h1
      rw [← h1', h2, Pi.add_apply]
      ring
    have hg : B0583.velGradEta c hm ω hcirc =
        B0583.gradEta c nz + B0583.zeroVelEtaLp c hm ω hcirc := rfl
    have hg' : B0583.velGradQ c hm ω = B0583.gradQ c nz := rfl
    beta_reduce
    rw [e2, he ψ hψ 0, hq ψ hψ 1, hg, hg', inner_add_right, hz0]
    show ∫ x, ((ω x : ℝ) : ℂ) * (ψ x : ℂ) ∂(B0581.cellVol c) = _
    rw [hsplit, hmean]
    linear_combination -hcurl

end CTE

namespace BSAux

/-- Integrability of an `L²(cell)` function times a real cylinder test function. -/
theorem integrable_u_mul {c : ℝ} (v : ℝ × ℝ → ℂ)
    (hv : MemLp v 2 (volume.restrict (UnforcedLeray.B0579.cell c)))
    {φ : ℝ × ℝ → ℝ} (hφ : UnforcedLeray.B0579.IsCylTest c φ) :
    Integrable (fun x => v x * ((φ x : ℝ) : ℂ)) (volume.restrict (UnforcedLeray.B0579.cell c)) := by
  have h := (UnforcedLeray.B0583.memLp_cellVol_of_isCylTest hφ).ofReal.integrable_mul hv
  exact h.congr (Filter.Eventually.of_forall fun x => mul_comm _ _)

/-- Real part of a complex integral (`RCLike.re` specialised to `ℂ`). -/
theorem integral_re' {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : Integrable f μ) : ∫ x, (f x).re ∂μ = (∫ x, f x ∂μ).re :=
  integral_re hf

/-- Almost-everywhere invariance of `IsBiotSavart` in the velocity. -/
theorem isBS_congr {c : ℝ} {ω : ℝ × ℝ → ℂ} {u v : ℝ × ℝ → Fin 2 → ℂ}
    (h : IsBiotSavart c ω u)
    (hv : ∀ j, ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)), u x j = v x j) :
    IsBiotSavart c ω v := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j => (h1 j).ae_eq (hv j), fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · refine Eq.trans (integral_congr_ae ?_) (h2 ψ hψ)
    filter_upwards [hv 0, hv 1] with x h0 h1'
    rw [h0, h1']
  · refine (h3 ψ hψ).trans (integral_congr_ae ?_)
    filter_upwards [hv 0, hv 1] with x h0 h1'
    rw [h0, h1']

/-- The real part of a complex Biot-Savart velocity of a real vorticity is a Biot-Savart velocity. -/
theorem isBS_re {c : ℝ} {ω : ℝ × ℝ → ℝ} {u : ℝ × ℝ → Fin 2 → ℂ}
    (h : IsBiotSavart c (fun x => ((ω x : ℝ) : ℂ)) u) :
    IsBiotSavart c (fun x => ((ω x : ℝ) : ℂ)) (fun x j => (((u x j).re : ℝ) : ℂ)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j => ((h1 j).re).ofReal, fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have hI : Integrable (fun x => u x 0 * ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ) +
        u x 1 * ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ))
        (volume.restrict (UnforcedLeray.B0579.cell c)) :=
      (integrable_u_mul (fun x => u x 0) (h1 0) (hψ.pd 0)).add
        (integrable_u_mul (fun x => u x 1) (h1 1) (hψ.pd 1))
    have key := h2 ψ hψ
    calc ∫ x in UnforcedLeray.B0579.cell c,
          ((((u x 0).re : ℝ) : ℂ) * ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ) +
            (((u x 1).re : ℝ) : ℂ) * ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ))
        = ∫ x in UnforcedLeray.B0579.cell c,
            ((((u x 0 * ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ) +
              u x 1 * ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ))).re : ℝ) : ℂ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp [Complex.add_re, Complex.mul_re]
      _ = (((∫ x in UnforcedLeray.B0579.cell c,
              (u x 0 * ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ) +
                u x 1 * ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ))).re : ℝ) : ℂ) := by
          rw [integral_complex_ofReal, integral_re' hI]
      _ = 0 := by rw [key]; simp
  · have hf0 : Integrable (fun x => u x 0 * ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ))
        (volume.restrict (UnforcedLeray.B0579.cell c)) :=
      integrable_u_mul (fun x => u x 0) (h1 0) (hψ.pd 1)
    have hf1 : Integrable (fun x => u x 1 * ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ))
        (volume.restrict (UnforcedLeray.B0579.cell c)) :=
      integrable_u_mul (fun x => u x 1) (h1 1) (hψ.pd 0)
    have hf : Integrable (fun x => u x 0 * ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ) -
        u x 1 * ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ))
        (volume.restrict (UnforcedLeray.B0579.cell c)) := hf0.sub hf1
    have hl := h3 ψ hψ
    have hωψ : ∫ x in UnforcedLeray.B0579.cell c, ((ω x : ℝ) : ℂ) * ((ψ x : ℝ) : ℂ) =
        (((∫ x in UnforcedLeray.B0579.cell c, ω x * ψ x : ℝ)) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      push_cast
      rfl
    have hcomp : (((∫ x in UnforcedLeray.B0579.cell c, ω x * ψ x : ℝ)) : ℂ) =
        ∫ x in UnforcedLeray.B0579.cell c,
          (u x 0 * ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ) -
            u x 1 * ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ)) :=
      hωψ.symm.trans hl
    have hre : (∫ x in UnforcedLeray.B0579.cell c,
          (u x 0 * ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ) -
            u x 1 * ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ))).re =
        ∫ x in UnforcedLeray.B0579.cell c, ω x * ψ x := by
      rw [← hcomp, Complex.ofReal_re]
    calc ∫ x in UnforcedLeray.B0579.cell c, ((ω x : ℝ) : ℂ) * ((ψ x : ℝ) : ℂ)
        = (((∫ x in UnforcedLeray.B0579.cell c, ω x * ψ x : ℝ)) : ℂ) := hωψ
      _ = ((((∫ x in UnforcedLeray.B0579.cell c,
              (u x 0 * ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ) -
                u x 1 * ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ))).re : ℝ)) : ℂ) := by
          rw [hre]
      _ = (((∫ x in UnforcedLeray.B0579.cell c,
              ((u x 0 * ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ) -
                u x 1 * ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ))).re : ℝ)) : ℂ) := by
          rw [integral_re' hf]
      _ = ∫ x in UnforcedLeray.B0579.cell c,
            ((((u x 0).re : ℝ) : ℂ) * ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ) -
              (((u x 1).re : ℝ) : ℂ) * ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ)) := by
          refine Eq.trans integral_complex_ofReal.symm (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
          simp [Complex.sub_re, Complex.mul_re]

end BSAux

namespace BSAux

end BSAux

end UnforcedLeray.Short.IIIa

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

theorem biotSavartFieldAll : UnforcedLeray.Short.IIIa.Exist.BiotSavartFieldAll := by
  intro c m _ hm w
  have hcirc : ∫ x in UnforcedLeray.B0579.cell c, (w.1 : UnforcedLeray.B0579.X c m) x = 0 :=
    (mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2
  have h := BSAux.isBS_re (CTE.velocityIsBiotSavart_one c m hm w.1 hcirc)
  refine BSAux.isBS_congr h ?_
  intro j
  filter_upwards [coeFn_realPartVelocityLp (UnforcedLeray.B0583.velocity c hm w.1 hcirc)] with x hx
  simp only [stripVel, realBiotSavart, realPartVelocityCLM_apply]
  rw [hx, realPartVelocityCLM_apply]

end UnforcedLeray.Short.IIIa.Exist
