import UnforcedLeray.Short.PartIIb.Sub.T22_1_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TrainGap.Lattice
import UnforcedLeray.Lib.Gaussian.Periodization
import UnforcedLeray.Lib.Train.PeriodizedVortex

/-!
# `PartII-b:T22/1/1/4`: `V_c` is differentiable with bounded derivative

Source `the November 2 reference manuscript`, lines 2074-2105 and 2205-2211
(lattice sum of the Gaussian vortex of width `1 + νσ ∈ [1, 1 + Σ]`).

(`IsoVGaussBound`, `GaussLeRpow`), the periodization API
(`Gaussian.hasFDerivAt_tsum_translates`) and `TrainGap.lattice_uniform`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb.CylPDE

/-- **Leaf V1** (Gaussian decay of the isolated vortex and of its derivative, uniform in the width;
source lines 2204-2211 and 2217-2234). For each `K ≥ 1` there are `B, β > 0` such that for all
`ν, s` with `1 ≤ 1 + ν s ≤ K` the isolated heat vortex `isoV ν s` is differentiable and
`‖isoV ν s z‖, ‖fderiv ℝ (isoV ν s) z‖ ≤ B e^{-β z₁²}`. Route: `isoV = toVec ∘ B0146.isoVelocity`,
`B0146.isoVelocity_apply`, the partial derivatives and Gaussian decay in
`Units/B0146/Explicit.lean:56-150`, and `GF.unif`/`GF.xdecay` (`Units/B0146/LatticeSums.lean`);
the norm of a `CLM ℝ² → Vec` is bounded by the sum of the norms on the basis `(1,0), (0,1)`. -/
def IsoVGaussBound : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∃ B β : ℝ, 0 < β ∧ ∀ ν s : ℝ, 1 ≤ 1 + ν * s → 1 + ν * s ≤ K →
    Differentiable ℝ (UnforcedLeray.Train.isoV ν s) ∧
    ∀ z : Pl, ‖UnforcedLeray.Train.isoV ν s z‖ ≤ B * Real.exp (-(β * z.1 ^ 2)) ∧
      ‖fderiv ℝ (UnforcedLeray.Train.isoV ν s) z‖ ≤ B * Real.exp (-(β * z.1 ^ 2))

/-- **Leaf V2** (Gaussian to polynomial decay). For `β > 0` there is `C` with
`e^{-β q²} ≤ C (1 + |q|)^{-2}` for all real `q`. Sketch: `(1+|q|)² ≤ 2 + 2q²` and
`e^{βq²} ≥ 1 + β²q⁴/2`; or `TrainGap.t_mul_exp_le`. -/
def GaussLeRpow : Prop :=
  ∀ β : ℝ, 0 < β → ∃ C : ℝ, ∀ q : ℝ, Real.exp (-(β * q ^ 2)) ≤ C * (1 + |q|) ^ (-(2 : ℝ))

theorem tcVcDeriv_of (h1 : IsoVGaussBound) (h2 : GaussLeRpow) : TcVcDeriv := by
  intro Sg hSg ν c hν hc
  obtain ⟨B, β, hβ, hiso⟩ := h1 (1 + Sg) (by linarith)
  obtain ⟨C, hC⟩ := h2 β hβ
  have hc0 : c ≠ 0 := by positivity
  have hcpos : 0 < c := by linarith
  have hmem : ∀ σ ∈ Icc 0 (Sg / ν), 1 ≤ 1 + ν * σ ∧ 1 + ν * σ ≤ 1 + Sg := by
    intro σ hσ
    have h0 : 0 ≤ ν * σ := mul_nonneg hν.le hσ.1
    have h3 : ν * σ ≤ Sg := by
      have := mul_le_mul_of_nonneg_left hσ.2 hν.le
      rwa [mul_div_cancel₀ _ hν.ne'] at this
    exact ⟨by linarith, by linarith⟩
  have hB : 0 ≤ B := by
    have := (hiso 0 0 (by norm_num) (by linarith)).2 0
    exact le_trans (norm_nonneg _) (by simpa using this.1)
  have hVc : ∀ σ, UnforcedLeray.Train.Vc ν c σ =
      fun y => ∑' n : ℤ, UnforcedLeray.Train.isoV ν σ (y - UnforcedLeray.Gaussian.shiftVec c n) := by
    intro σ; funext y
    exact UnforcedLeray.Gaussian.periodize_eq c _ y
  have key : ∀ σ ∈ Icc 0 (Sg / ν), ∀ x : Pl,
      HasFDerivAt (UnforcedLeray.Train.Vc ν c σ)
        (∑' n : ℤ, fderiv ℝ (fun y => UnforcedLeray.Train.isoV ν σ
          (y - UnforcedLeray.Gaussian.shiftVec c n)) x) x := by
    intro σ hσ x
    obtain ⟨hd, hb⟩ := hiso ν σ (hmem σ hσ).1 (hmem σ hσ).2
    rw [hVc σ]
    refine UnforcedLeray.Gaussian.hasFDerivAt_tsum_translates (C₀ := B * C) (C₁ := B * C)
      (s := 2) hd (by norm_num) hc0 (fun z => ?_) (fun z => ?_) x
    · calc ‖UnforcedLeray.Train.isoV ν σ z‖ ≤ B * Real.exp (-(β * z.1 ^ 2)) := (hb z).1
        _ ≤ B * (C * (1 + |z.1|) ^ (-(2:ℝ))) := mul_le_mul_of_nonneg_left (hC _) hB
        _ = B * C * (1 + |z.1|) ^ (-(2:ℝ)) := by ring
    · calc ‖fderiv ℝ (UnforcedLeray.Train.isoV ν σ) z‖ ≤ B * Real.exp (-(β * z.1 ^ 2)) := (hb z).2
        _ ≤ B * (C * (1 + |z.1|) ^ (-(2:ℝ))) := mul_le_mul_of_nonneg_left (hC _) hB
        _ = B * C * (1 + |z.1|) ^ (-(2:ℝ)) := by ring
  refine ⟨fun σ hσ x => (key σ hσ x).differentiableAt, B * ∑' m : ℤ, Real.exp (-((β / 4) * (m : ℝ) ^ 2)), ?_⟩
  intro σ hσ x
  obtain ⟨hd, hb⟩ := hiso ν σ (hmem σ hσ).1 (hmem σ hσ).2
  rw [(key σ hσ x).fderiv]
  have hterm : ∀ n : ℤ, ‖fderiv ℝ (fun y => UnforcedLeray.Train.isoV ν σ
      (y - UnforcedLeray.Gaussian.shiftVec c n)) x‖ ≤ B * Real.exp (-(β * (x.1 - n * c) ^ 2)) := by
    intro n
    rw [fderiv_comp_sub]
    have := (hb (x - UnforcedLeray.Gaussian.shiftVec c n)).2
    simpa [UnforcedLeray.Gaussian.shiftVec] using this
  have hsum : Summable (fun n : ℤ => B * Real.exp (-(β * (x.1 - n * c) ^ 2))) :=
    (UnforcedLeray.B0146.summable_exp_shift hβ hc0 x.1).mul_left B
  calc ‖∑' n : ℤ, fderiv ℝ (fun y => UnforcedLeray.Train.isoV ν σ
        (y - UnforcedLeray.Gaussian.shiftVec c n)) x‖
      ≤ ∑' n : ℤ, B * Real.exp (-(β * (x.1 - n * c) ^ 2)) :=
        tsum_of_norm_bounded hsum.hasSum hterm
    _ = B * ∑' n : ℤ, Real.exp (-(β * (x.1 - n * c) ^ 2)) := tsum_mul_left
    _ ≤ B * ∑' m : ℤ, Real.exp (-((β / 4) * (m : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (UnforcedLeray.Short.IIb.TrainGap.lattice_uniform hβ hc x.1) hB

end UnforcedLeray.Short.IIb.CylPDE
