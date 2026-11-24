import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGradOrg

/-!
# `PartIII-b:C/rep/8/2/2/2/org`: the fourth derivative of the mean Newton field off the ray

Source `the November 2 reference manuscript`
5380-5387 (`Y^mt = D_{μ+1}X^mt = (-½y·∇ - νΔ + μ + ½)X^mt`), 5400-5413 ("the gradient Newton kernel
has degree `-5`", "the outward stream primitive has the same degree", "fixed conormal derivatives of
`χ̂_y(νs)` are bounded"), 5438-5448 (Hessian estimate).

The Hessian of `Y^mt` contains `ν D²ΔX^mt`, i.e. the fourth derivative of `X^mt`.  The library
bounds `XmtJetOff`, `SCXJetOff`, `SCPsiBoundOff` (`MeanGradOrg`) stop at `m = 3`; the same kernel
argument (the Newton kernel `V` has `‖∂^mV(w)‖ ≤ C_m N₀^χ|w|^{-4-m}`, `m ≤ 7`: `NewtonVCutBound`;
each further derivative costs one factor `r^{-1}`) gives `m = 4`.  This file states the `m = 4`
analogues as `Prop`s and proves `XmtJetOff4` from `NewtonVCutBound` and `SCXJetOff4`
exactly as `xmtJetOff_of` (the proof is the same with `m = 4`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Outward stream primitive, fourth derivative** (source 4180-4182, 5400-5413): `m = 4` case of
`SCPsiBoundOff`: `‖∂^4Ψ_Z(y)‖ ≤ C₁ B r^{-4}|y|^{-2}` for `ν ≤ r²`. -/
def SCPsiBoundOff4 : Prop :=
  ∃ C1 : ℝ, ∀ (ν B : ℝ) (Z : Vec3 → Vec3), 0 < ν → 0 ≤ B → SCZHyp ν B Z →
    ∀ m : ℕ, m = 4 → ∀ y : Vec3, ν ≤ cylR y ^ 2 →
      ‖iteratedFDeriv ℝ m (streamPsi Z) y‖ ≤ C1 * B * cylR y ^ (-(m : ℝ)) * (eucSq y)⁻¹

/-- **Stream-cut field, fourth derivative** (source 4178-4186, 5400-5413): `m = 4` case of
`SCXJetOff`: `‖∂^4𝒞_yZ(y)‖ ≤ C₄ B r^{-6}|y|^{-2}` for `ν ≤ r²`. -/
def SCXJetOff4 (χy : ℝ → ℝ) : Prop :=
  ∃ C4 : ℝ, ∀ (ν B : ℝ), 0 < ν → 0 ≤ B → ∀ Z : Vec3 → Vec3, SCZHyp ν B Z → IsStreamCutoff χy →
    ∀ y : Vec3, ν ≤ cylR y ^ 2 → ∀ m : ℕ, m = 4 →
      ‖iteratedFDeriv ℝ m (streamCut ν 1 χy Z) y‖ ≤
        C4 * B * cylR y ^ (-(2 : ℝ) - m) * (eucSq y)⁻¹

/-- **The mean field off the ray at `ε = 1`, fourth derivative** (source 4776-4791, 4870-4900,
5400-5413): `‖∂^4X^mt_1(w)‖ ≤ C r^{-6}|w|^{-2}N₀^χ(M)` for `ν ≤ r²`. -/
def XmtJetOff4 (χo χy : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ (c ν μ : ℝ), LHyp c ν 1 μ χo χy → ∀ M : Chart → Mat3, OldThinFinite c ν M →
    ∀ w : Vec3, ν ≤ cylR w ^ 2 → ∀ m : ℕ, m = 4 →
      ‖iteratedFDeriv ℝ m (Xmt c ν 1 μ χo χy M) w‖ ≤
        C * cylR w ^ (-(2 : ℝ) - m) * (eucSq w)⁻¹ * oldN0cut c ν χo M

/-- `XmtJetOff4` from the Newton kernel bound and `SCXJetOff4` (same proof as `xmtJetOff_of`). -/
theorem xmtJetOff4_of {χo χy : ℝ → ℝ} (hV : NewtonVCutBound χo) (hS : SCXJetOff4 χy) :
    XmtJetOff4 χo χy := by
  obtain ⟨C, hC⟩ := hV
  obtain ⟨C4, hC4⟩ := hS
  set S : ℝ := ∑ m ∈ Finset.range 8, (|C m| + |C m|) with hSdef
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun m _ => by positivity
  refine ⟨|C4| * S, ?_⟩
  intro c ν μ h M hM w hw m hm
  have hN0 := oldN0cut_nonneg c ν h.nu_pos h.chiO M
  have hmu0 : 0 ≤ μ := h.mu_pos.le
  have hmu1 : 0 ≤ μ + 1 := by linarith
  obtain ⟨h1, h1b⟩ := hC c ν μ h.c_pos h.nu_pos h.chiO hmu0 M hM
  obtain ⟨h2, h2b⟩ := hC c ν (μ + 1) h.c_pos h.nu_pos h.chiO hmu1 M hM
  have hY : ∀ μ' : ℝ, youngW c ν 1 μ' χo M = newtonV c ν μ' χo M := by
    intro μ'; funext y; simp [youngW]
  set Z : Vec3 → Vec3 := newtonV c ν μ χo M - newtonV c ν (μ + 1) χo M with hZ
  have hopen : IsOpen {w : Vec3 | ν * (11 / 12) < eucSq w} := by
    unfold eucSq
    exact isOpen_lt continuous_const (by fun_prop)
  have hZs : ContDiffOn ℝ 7 Z {w | ν * (11 / 12) < eucSq w} := h1.sub h2
  have hZb : ∀ m : ℕ, m ≤ 7 → ∀ w : Vec3, ν * (11 / 12) < eucSq w →
      ‖iteratedFDeriv ℝ m Z w‖ ≤
        (S * oldN0cut c ν χo M) * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by
    intro m hm w hw
    have hat1 : ContDiffAt ℝ 7 (newtonV c ν μ χo M) w := h1.contDiffAt (hopen.mem_nhds hw)
    have hat2 : ContDiffAt ℝ 7 (newtonV c ν (μ + 1) χo M) w :=
      h2.contDiffAt (hopen.mem_nhds hw)
    have hmle : (m : WithTop ℕ∞) ≤ 7 := by exact_mod_cast hm
    rw [hZ, iteratedFDeriv_sub_apply (hat1.of_le hmle) (hat2.of_le hmle)]
    have hp : 0 ≤ (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) :=
      Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hb1 := h1b m hm w hw
    have hb2 := h2b m hm w hw
    have hSm : |C m| + |C m| ≤ S :=
      Finset.single_le_sum (f := fun m => |C m| + |C m|) (fun m _ => by positivity)
        (Finset.mem_range.2 (by omega))
    have hCm : C m + C m ≤ S := le_trans (add_le_add (le_abs_self _) (le_abs_self _)) hSm
    calc ‖iteratedFDeriv ℝ m (newtonV c ν μ χo M) w -
            iteratedFDeriv ℝ m (newtonV c ν (μ + 1) χo M) w‖
        ≤ ‖iteratedFDeriv ℝ m (newtonV c ν μ χo M) w‖ +
            ‖iteratedFDeriv ℝ m (newtonV c ν (μ + 1) χo M) w‖ := norm_sub_le _ _
      _ ≤ C m * oldN0cut c ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) +
          C m * oldN0cut c ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) :=
          add_le_add hb1 hb2
      _ = (C m + C m) * (oldN0cut c ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)) := by
          ring
      _ ≤ S * (oldN0cut c ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)) :=
          mul_le_mul_of_nonneg_right hCm (mul_nonneg hN0 hp)
      _ = (S * oldN0cut c ν χo M) * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by ring
  have hL : Xmt c ν 1 μ χo χy M = streamCut ν 1 χy Z := by
    funext y'
    simp only [Xmt, hY, hZ]
  rw [hL]
  have key := hC4 ν (S * oldN0cut c ν χo M) h.nu_pos (mul_nonneg hSnn hN0) Z ⟨hZs, hZb⟩
    h.chiY w hw m hm
  have hr : 0 ≤ cylR w ^ (-(2 : ℝ) - m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have he : 0 ≤ (eucSq w)⁻¹ := inv_nonneg.2 (Finset.sum_nonneg fun i _ => sq_nonneg (w i))
  have hX : 0 ≤ S * oldN0cut c ν χo M * cylR w ^ (-(2 : ℝ) - m) * (eucSq w)⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg hSnn hN0) hr) he
  calc ‖iteratedFDeriv ℝ m (streamCut ν 1 χy Z) w‖
      ≤ C4 * (S * oldN0cut c ν χo M) * cylR w ^ (-(2 : ℝ) - m) * (eucSq w)⁻¹ := key
    _ = C4 * (S * oldN0cut c ν χo M * cylR w ^ (-(2 : ℝ) - m) * (eucSq w)⁻¹) := by ring
    _ ≤ |C4| * (S * oldN0cut c ν χo M * cylR w ^ (-(2 : ℝ) - m) * (eucSq w)⁻¹) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hX
    _ = |C4| * S * cylR w ^ (-(2 : ℝ) - m) * (eucSq w)⁻¹ * oldN0cut c ν χo M := by ring


end UnforcedLeray.Short.PartIIIb.Concrete
end
