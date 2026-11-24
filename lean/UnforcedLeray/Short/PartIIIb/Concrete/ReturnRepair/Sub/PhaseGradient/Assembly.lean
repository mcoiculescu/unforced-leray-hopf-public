import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps
import UnforcedLeray.Short.PartIIIa.Compose

/-!
# Assembly of `repair:phase-gradient` (S6 of `PartIII-b:C/rep/2`, source 5203-5223)

Source of record: `the November 2 reference manuscript` 5203-5223, with the
regime 5111-5146 and the sequence 5926-5950.

* `pg_scale_le` : the physical rescaling `(R√ν)^{-46/11} = ν^{-23/11}ε^{46/11} ≤ ν^{-3}ε^{46/11}`
  (`R = ε⁻¹`, `0 < ν ≤ 1`).
* `phaseGradientAt_of_bounds` : `PhaseGradientAt` at one regime from the separated representative
  (`RepairSepBridge`) and the phase-wise bounds of `WardGradXPhase`, `WardGradYPhase` (with their
  constants fixed), for `ν, ε ≤ 1`, `P = 2εc ≤ 1`, `μ` in the window.
* **`phaseGradient_of`** : `SeqData.PhaseGradient` from `RepairSepBridge`, `WardGradXPhase`,
  `WardGradYPhase` and `SeqData.RepairStanding` (window `[σ₀/2, (σ₀+1/4)/2]` by
  `mu_eventually_mem`, `ν, ε ≤ 1` by `retNu_retEps_eventually_le_one`, `P ≤ 1` by
  `IIIa.period_le_one_of_small` on the actual regime).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- The physical rescaling (source 5212-5217): `(ε⁻¹√ν)^{-46/11} ≤ ν⁻³ ε^{46/11}` for `0 < ν ≤ 1`. -/
theorem pg_scale_le {ν ε : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hε : 0 < ε) :
    (ε⁻¹ * Real.sqrt ν) ^ (-(46 / 11 : ℝ)) ≤ ν⁻¹ ^ 3 * ε ^ (46 / 11 : ℝ) := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have e1 : (ε⁻¹) ^ (-(46 / 11 : ℝ)) = ε ^ (46 / 11 : ℝ) := by
    rw [Real.inv_rpow hε.le, Real.rpow_neg hε.le, inv_inv]
  have e2 : Real.sqrt ν ^ (-(46 / 11 : ℝ)) = ν⁻¹ ^ (23 / 11 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hν.le, Real.inv_rpow hν.le, ← Real.rpow_neg hν.le]
    norm_num
  have hν' : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have e3 : ν⁻¹ ^ (23 / 11 : ℝ) ≤ ν⁻¹ ^ 3 := by
    have := Real.rpow_le_rpow_of_exponent_le hν' (show (23 / 11 : ℝ) ≤ (3 : ℕ) by norm_num)
    rwa [Real.rpow_natCast] at this
  rw [Real.mul_rpow (inv_pos.2 hε).le hs.le, e1, e2, mul_comm]
  exact mul_le_mul_of_nonneg_right e3 (Real.rpow_nonneg hε.le _)

/-- `PhaseGradientAt` at one regime from the bridge and the phase-wise bounds (constants fixed). -/
theorem phaseGradientAt_of_bounds (hB : RepairSepBridge) (Pl : PlanarData) (K : ReturnConsts)
    (L : ReturnLevel) (μ : ℝ) {σ₁ σ₂ CX CY : ℝ} {kX kY : ℕ} (hCX : 0 ≤ CX) (hCY : 0 ≤ CY)
    (hXb : ∀ (ν μ R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P → P ≤ 1 → μ ∈ Icc σ₁ σ₂ →
      ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
        ∀ᵐ τ : ℝ, sliceLq (22 / 3) (fun y => ‖fderiv ℝ (sepWX ν μ R K.χy T τ) y‖) ≤
          ENNReal.ofReal (CX * ν⁻¹ ^ kX * (R * Real.sqrt ν) ^ (-(46 / 11 : ℝ))) *
            IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T))
    (hYb : ∀ (ν μ R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P → P ≤ 1 → μ ∈ Icc σ₁ σ₂ →
      ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
        ∀ᵐ τ : ℝ, sliceLq (22 / 3) (fun y => ‖fderiv ℝ (sepWY ν μ R K.χy T τ) y‖) ≤
          ENNReal.ofReal (CY * ν⁻¹ ^ kY * (R * Real.sqrt ν) ^ (-(46 / 11 : ℝ))) *
            IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T))
    (hμ : μ ∈ Icc σ₁ σ₂) (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1) (hP : 2 * L.ε * cOf L.ν ≤ 1)
    (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) :
    PhaseGradientAt Pl K L μ (CX + CY) (kX + kY + 3) := by
  intro w
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hc := cOf_pos hν
  have hρ : 0 < L.ρb Pl K := by
    unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
    have h1 := (L.params Pl).ν_pos
    have h2 := (L.params Pl).ε_pos
    positivity
  obtain ⟨T, hS, hM, hA, hW, hN⟩ := hB (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε K.χo K.hχo
    hc hρ hmZ hν hε (multOp Pl K L w)
  have hX0 : wardX0 L.ν μ L.ε⁻¹ (cOf L.ν) (repSrcTen Pl K L w) = sepX0 L.ν μ T := by
    rw [wardX0_eq_sepX0]
    exact sepX0_congr hW
  have hX : repX Pl K L μ w = sepWX L.ν μ L.ε⁻¹ K.χy T := by
    show wardStreamCut L.ν L.ε⁻¹ K.χy (wardX0 L.ν μ L.ε⁻¹ (cOf L.ν) (repSrcTen Pl K L w)) = _
    rw [hX0]
    rfl
  have hY : repY Pl K L μ w = sepWY L.ν μ L.ε⁻¹ K.χy T := by
    show physDmu L.ν (μ + 1) (repX Pl K L μ w) = _
    rw [hX]
    rfl
  have hR1 : 1 ≤ L.ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hP0 : 0 < 2 * L.ε * cOf L.ν := by positivity
  have h1 := hXb L.ν μ L.ε⁻¹ _ hν hν1 hR1 hP0 hP hμ T hS hM hA
  have h2 := hYb L.ν μ L.ε⁻¹ _ hν hν1 hR1 hP0 hP hμ T hS hM hA
  set F := IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 19) (IIIa.srcNorm T) with hF
  set Λ := (L.ε⁻¹ * Real.sqrt L.ν) ^ (-(46 / 11 : ℝ)) with hΛ
  have hΛ0 : 0 ≤ Λ := Real.rpow_nonneg (by positivity) _
  have hν' : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hpX : L.ν⁻¹ ^ kX ≤ L.ν⁻¹ ^ (kX + kY) := pow_le_pow_right₀ hν' (Nat.le_add_right _ _)
  have hpY : L.ν⁻¹ ^ kY ≤ L.ν⁻¹ ^ (kX + kY) := pow_le_pow_right₀ hν' (Nat.le_add_left _ _)
  have hq0 : 0 ≤ L.ν⁻¹ ^ (kX + kY) := by positivity
  have e1 : phaseSupLr (2 * L.ε * cOf L.ν) (22 / 3)
      (fun x => ‖fderiv ℝ (repX Pl K L μ w x.1) x.2‖) ≤
        ENNReal.ofReal (CX * L.ν⁻¹ ^ (kX + kY) * Λ) * F := by
    rw [hX]
    refine (phaseSupLr_le_of_ae
      (f := fun x => ‖fderiv ℝ (sepWX L.ν μ L.ε⁻¹ K.χy T x.1) x.2‖) h1).trans ?_
    gcongr
  have e2 : phaseSupLr (2 * L.ε * cOf L.ν) (22 / 3)
      (fun x => ‖fderiv ℝ (repY Pl K L μ w x.1) x.2‖) ≤
        ENNReal.ofReal (CY * L.ν⁻¹ ^ (kX + kY) * Λ) * F := by
    rw [hY]
    refine (phaseSupLr_le_of_ae
      (f := fun x => ‖fderiv ℝ (sepWY L.ν μ L.ε⁻¹ K.χy T x.1) x.2‖) h2).trans ?_
    gcongr
  have hscale : (CX + CY) * L.ν⁻¹ ^ (kX + kY) * Λ ≤
      (CX + CY) * L.ν⁻¹ ^ (kX + kY + 3) * L.ε ^ (46 / 11 : ℝ) := by
    have h := pg_scale_le hν hν1 hε
    have hCC : 0 ≤ (CX + CY) * L.ν⁻¹ ^ (kX + kY) := mul_nonneg (add_nonneg hCX hCY) hq0
    calc (CX + CY) * L.ν⁻¹ ^ (kX + kY) * Λ
        ≤ (CX + CY) * L.ν⁻¹ ^ (kX + kY) * (L.ν⁻¹ ^ 3 * L.ε ^ (46 / 11 : ℝ)) :=
          mul_le_mul_of_nonneg_left h hCC
      _ = (CX + CY) * L.ν⁻¹ ^ (kX + kY + 3) * L.ε ^ (46 / 11 : ℝ) := by
          rw [pow_add]; ring
  calc phaseSupLr (2 * L.ε * cOf L.ν) (22 / 3) (fun x => ‖fderiv ℝ (repX Pl K L μ w x.1) x.2‖) +
        phaseSupLr (2 * L.ε * cOf L.ν) (22 / 3) (fun x => ‖fderiv ℝ (repY Pl K L μ w x.1) x.2‖)
      ≤ ENNReal.ofReal (CX * L.ν⁻¹ ^ (kX + kY) * Λ) * F +
          ENNReal.ofReal (CY * L.ν⁻¹ ^ (kX + kY) * Λ) * F := add_le_add e1 e2
    _ = ENNReal.ofReal ((CX + CY) * L.ν⁻¹ ^ (kX + kY) * Λ) * F := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        ring
    _ ≤ ENNReal.ofReal ((CX + CY) * L.ν⁻¹ ^ (kX + kY + 3) * L.ε ^ (46 / 11 : ℝ)) *
          phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hscale) hN

/-- **`repair:phase-gradient` along the concrete sequence** (source 5203-5223): from the
separated representative (S5), the phase-wise gradient bounds of `X` (S3) and `Y` (S4) and the
standing hypotheses of the repair section. -/
theorem phaseGradient_of (hB : RepairSepBridge) (hX : WardGradXPhase) (hY : WardGradYPhase)
    (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.PhaseGradient := by
  have hσ : -(1 / 4 : ℝ) < D.σ₀ / 2 := by linarith [hst.sigma_pos]
  obtain ⟨CX, kX, hCX, hXb⟩ := hX (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) hσ D.K.χy hst.chiY
  obtain ⟨CY, kY, hCY, hYb⟩ := hY (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) hσ D.K.χy hst.chiY
  refine ⟨CX + CY, kX + kY + 3, ?_⟩
  have hev1 := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  have hev2 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  have hev3 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ dm ^ 3 / 12 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually_le_const (by have := hst.dm_pos; positivity)
  filter_upwards [hev1, hev2, hev3, hst.actual] with n h1 h2 h3 h4 z hz
  have hP : 2 * (D.level n).ε * cOf (D.level n).ν ≤ 1 :=
    UnforcedLeray.Short.IIIa.period_le_one_of_small h4.regime h3
  exact phaseGradientAt_of_bounds hB D.Pl D.K (D.level n) (D.mu n z) hCX hCY hXb hYb (h1 z hz)
    h2.1 h2.2 hP hst.C0_pos (by linarith [hst.mZ_gt])

end UnforcedLeray.Short.PartIIIb.Concrete

end
