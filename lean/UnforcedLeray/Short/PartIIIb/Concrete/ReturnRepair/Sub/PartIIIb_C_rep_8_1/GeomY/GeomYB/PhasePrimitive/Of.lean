import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.Comm

/-!
# `PartIII-b:C/rep/8/1/1/2/5/1` (`GeomYB.PhasePrimitive.Of`): reduction to the commutator
oscillation leaf

Source `the November 2 reference manuscript`
lines 5427-5432 ("For `Y` use the exact formula `Y = 𝒞_{χ_y}W_μ + [D_{μ+1},𝒞_{χ_y}](W_μ-W_{μ+1})`.
Apply the spatial kernel comparison to these terms separately"), 4195-4215 (`ward:shifted-resolvent`,
`ward:cutoff-source` `Y = 𝒞_yW_μ + [D_{μ+1},𝒞_y]X₀`; `Ψ_{AZ} = AΨ_Z + Ψ_Z`,
`Ψ_{ΔZ} = (∂_r² - r⁻¹∂_r + ∂_z²)Ψ_Z`; the commutator is supported on the cutoff transition
region), 5400-5427 (one phase primitive in the dilation variable with its dilation-one boundary
term retained; separated kernels, old/young radius ratio `≤ 1/√1.2`).

`phasePrimitiveYBBound_of` proves `D.PhasePrimitiveYBBound` from the single analytic leaf
`SepCommOscFar`, the Hessian-level analogue of `SepOscFar` (`GeomX/PhasePrimitive/Leaf.lean`) for
the commutator `YBComm.comm = [D_{μ+1}, 𝒞_y]`: for a measurable `c`-periodic thin source `F`
supported in `|x'| ≤ √(5ν/6)` with finite first moment, at every young receiver
`ν ≤ |x_obs'|²`, `D_y[D_{μ+1},𝒞_y]X₀(F) - D_y[D_{μ+1},𝒞_y]X₀(F̄)` at `ε⁻¹x_obs` has a measurable
periodic phase majorant with `‖·‖_{L²_τ} ≤ C(1 + ν⁻¹ + c)^k ε⁴|x_obs'|^{-5}N₁(F)`
(`X₀ = YBComm.srcX0`, `F̄` the phase mean).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace YBPhase

open YBComm PhasePrim

/-- **Leaf: phase primitive for the commutator** (source 5427-5432, 4195-4215, 5400-5427; SP
3768-3790 with the degree `-5` kept; Hessian level): for a measurable, `c`-periodic thin source
`F(x',Y,q)` supported in `|x'| ≤ √(5ν/6)`, with finite first transverse moment, at every young
receiver `|x_obs'|² ≥ ν`, the oscillating part of `D_y[D_{μ+1},𝒞_y]X₀` at `y = ε⁻¹x_obs`
(`X₀(F) - X₀(F̄)`, `F̄` the phase mean) has a measurable periodic phase majorant `B` with
`‖B‖_{L²_τ} ≤ C(1 + ν⁻¹ + c)^k ε⁴ |x_obs'|^{-5} N₁(F)`. -/
def SepCommOscFar : Prop :=
  ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ ν c ε μ : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 →
      0 < μ → μ < 1 / 4 →
      ∀ F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) →
        (∀ x' Y q, F x' Y (q + c) = F x' Y q) →
        (∀ x' Y q, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → F x' Y q = 0) →
        IIIa.thinMoment c F ≠ ⊤ →
        ∀ xo : Space, ν ≤ xo 0 ^ 2 + xo 1 ^ 2 →
          ∃ B : ℝ → ℝ≥0∞, Measurable B ∧ Function.Periodic B (2 * ε * c) ∧
            (∀ᵐ τ ∂(volume : Measure ℝ),
              ‖fderiv ℝ (comm ν μ ε⁻¹ χy (srcX0 ν μ (IIIa.thinSource ε F)) τ) (ε⁻¹ • xo) -
                fderiv ℝ (comm ν μ ε⁻¹ χy
                  (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F)))) τ)
                  (ε⁻¹ • xo)‖ₑ ≤ B τ) ∧
            IIIa.ltauAt (2 * ε * c) B ≤
              ENNReal.ofReal (C * (1 + ν⁻¹ + c) ^ k * ε ^ 4 *
                Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ)) * IIIa.thinMoment c F

/-- **The regime form** of the reduction: one constant for every regime with `ε ≤ 1`. -/
theorem phasePrimitiveYBBoundAt_uniform (hLeaf : SepCommOscFar)
    (K : ReturnConsts) (hχy : IsStreamCutoff K.χy) :
    ∃ (C : ℝ) (k : ℕ), ∀ (Pl : PlanarData) (L : ReturnLevel) (μ : ℝ),
      L.ε ≤ 1 → 0 < K.C0 → 3 / 2 < K.mZ → PhasePrimitiveYBBoundAt Pl K L μ C k := by
  obtain ⟨C, k, hC, hlf⟩ := hLeaf K.χy hχy
  refine ⟨Real.pi * (C + 1) * 3 ^ k, 2 * k, ?_⟩
  intro Pl L μ hε1 hC0 hmZ hL T s hs η
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hs0 : 0 < s := hs.1
  set N := oldN1 Pl K L T with hN
  have hs52 : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
  have hcoef : 0 < Real.pi * (C + 1) * 3 ^ k * L.ν⁻¹ ^ (2 * k) * (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
    have := Real.pi_pos
    positivity
  by_cases hNtop : N = ⊤
  · rw [hNtop, ENNReal.mul_top (by simpa using hcoef)]
    exact le_top
  -- the thin source
  set F := liftSrc Pl K L T with hF
  have hFN : IIIa.thinMoment (cOf L.ν) F ≤ ENNReal.ofReal Real.pi * N :=
    thinMoment_liftSrc_le Pl K L hC0 T
  have hFfin : IIIa.thinMoment (cOf L.ν) F ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hNtop) hFN
  -- the receiver
  set y := NearInst.chartY L.ε⁻¹ (s, (0, η)) with hy
  obtain ⟨hyx, hνx, hrad⟩ := receiver L.ν L.ε s 0 η hν hε hs
  rw [← hy] at hyx hνx hrad
  set xo := L.ε • y with hxo
  -- the leaf
  obtain ⟨B, hBm, hBp, hBae, hBle⟩ := hlf L.ν (cOf L.ν) L.ε μ hν hL.nu_le hc hε hε1
    hL.mu_pos hL.mu_lt F (liftSrc_measurable Pl K L T) (liftSrc_periodic Pl K L T)
    (liftSrc_support Pl K L T) hFfin xo hνx
  rw [hyx] at hBae
  rw [hrad] at hBle
  -- the actual and middle commutators
  have hact : actYB Pl K L μ T = comm L.ν μ L.ε⁻¹ K.χy (srcX0 L.ν μ (IIIa.thinSource L.ε F)) := by
    rw [actYB_eq_comm, zAct0_eq_srcX0 Pl K L μ hC0 T]
  have hmid : actYBMid Pl K L μ T = comm L.ν μ L.ε⁻¹ K.χy
      (srcX0 L.ν μ (IIIa.thinSource L.ε (IIIa.meanLift (IIIa.phaseMean (cOf L.ν) F)))) := by
    rw [actYBMid_eq_comm, zMid_eq_srcX0 Pl K L μ hC0 hmZ T]
    rfl
  have hmaj : ∀ᵐ τ ∂(volume : Measure ℝ),
      ENNReal.ofReal (dPhaseYB Pl K L μ T τ (NearInst.chartY L.ε⁻¹ (s, (0, η)))) ≤ B τ := by
    filter_upwards [hBae] with τ hτ
    rw [← hy]
    unfold dPhaseYB
    rw [hact, hmid, ofReal_norm]
    exact hτ
  have hcell := cellL2_le L.ε (cOf L.ν) hε hc (dPhaseYB Pl K L μ T) s η B hBm hBp hmaj
  -- the constants
  set M := 1 + L.ν⁻¹ + cOf L.ν with hM
  have hM0 : 0 ≤ M := by have := hc.le; have := inv_pos.2 hν; positivity
  have hMle : M ^ k ≤ 3 ^ k * L.ν⁻¹ ^ (2 * k) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ hM0 (poly3 L.ν hν hL.nu_le) k
  set a := C * M ^ k * L.ε ^ 4 * s ^ (5 / 2 : ℝ) with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha_le : a * Real.pi ≤ Real.pi * (C + 1) * 3 ^ k * L.ν⁻¹ ^ (2 * k) *
      (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
    have hpi := Real.pi_pos
    have h1 : C * M ^ k ≤ (C + 1) * (3 ^ k * L.ν⁻¹ ^ (2 * k)) :=
      mul_le_mul (by linarith) hMle (pow_nonneg hM0 _) (by linarith)
    have h2 : 0 ≤ L.ε ^ 4 * s ^ (5 / 2 : ℝ) := by positivity
    calc a * Real.pi = Real.pi * (C * M ^ k) * (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
          rw [ha]; ring
      _ ≤ Real.pi * ((C + 1) * (3 ^ k * L.ν⁻¹ ^ (2 * k))) * (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
          gcongr
      _ = _ := by ring
  calc cellL2 L.ε⁻¹ (cOf L.ν) (dPhaseYB Pl K L μ T) s η
      ≤ IIIa.ltauAt (2 * L.ε * cOf L.ν) B := hcell
    _ ≤ ENNReal.ofReal a * IIIa.thinMoment (cOf L.ν) F := hBle
    _ ≤ ENNReal.ofReal a * (ENNReal.ofReal Real.pi * N) := by gcongr
    _ = ENNReal.ofReal (a * Real.pi) * N := by
        rw [ENNReal.ofReal_mul ha0, mul_assoc]
    _ ≤ _ := by gcongr

/-- **`D.PhasePrimitiveYBBound` from the commutator oscillation leaf** (source 5427-5432,
4195-4215). -/
theorem phasePrimitiveYBBound_of (hLeaf : SepCommOscFar) (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) : D.PhasePrimitiveYBBound := by
  obtain ⟨C, k, h⟩ := phasePrimitiveYBBoundAt_uniform hLeaf D.K hst.chiY
  refine ⟨C, k, ?_⟩
  filter_upwards [retNu_retEps_eventually_le_one (σ₀ := D.σ₀) hst.omega_ne hst.gamma_pos
    D.coeff_ne] with n hνε z _
  exact h D.Pl (D.level n) (D.mu n z) hνε.2 hst.C0_pos hst.mZ_gt

end YBPhase

end UnforcedLeray.Short.PartIIIb.Concrete
