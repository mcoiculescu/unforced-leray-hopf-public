import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.Comm
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.TaylorWidth.FarLeaf
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.TableSupport
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_2_11

/-!
# Definitions and proved reductions for `PartIII-b:C/rep/8/1/1/2/5/2/1` (`YBWidth.SepCommMeanFar`)

Source `the November 2 reference manuscript`
lines 5427-5432, 5383-5387, 5415-5427; SP 3604-3610, 3700-3712, 3735-3766, 4195-4215.

## Contents

1. **Support reduction to the transition annulus (`fderiv_comm_eq_zero_of_gt`)**:
   Outside `ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4` (i.e. for `5 * ν / 4 < xo 0 ^ 2 + xo 1 ^ 2`),
   `comm ν μ ε⁻¹ χy Z τ` vanishes on a neighbourhood of `ε⁻¹ • xo`, so its spatial derivative is `0`.
2. **All-order separated kernel difference estimate (`sepKernelDiffIter`)**:
   For every derivative order `j : ℕ`, `IIIa.sepKernelBounds` yields the heat-to-Newton plus
   vertical Taylor bound along vertical segments at horizontal distance `≥ D > 0`.
3. **Commutator decomposition (`cutMain`, `cutPsi`, `commMain`, `commPsi`)**:
   Splits `wardStreamCut = cutMain + cutPsi` and the commutator comparison on the transition
   annulus into the main cutoff part `commMain` (involving `Z₁ - Z₂`, `D(Z₁ - Z₂)`, `D²(Z₁ - Z₂)`)
   and the outward stream-primitive commutator `commPsi = [D_{μ+1}, cutPsi]`.
4. **Proved order-1 difference bound (`sepCommMainDiff1`)**:
   Proves the first-derivative difference bound `‖D_y srcX0 - D_y newtonX0‖` unconditionally from
   `sepMeanFar` (`GeomX/TaylorWidth/FarLeaf.lean`).
5. **Conditional assembly (`sepCommMeanFarFixed_of`)**:
   Assembles the quantifier-corrected commutator leaf `SepCommMeanFarFixed` from the four annulus
   sub-leaves `SepCommMainLeibniz`, `SepCommMainDiff0`, `SepCommMainDiff2`, and `SepCommPsiDiff`
   (with `SepCommMainDiff1` discharged by `sepCommMainDiff1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.IIIa

namespace YBWidth

open YBComm PhasePrim

/-! ## 1. Vanishing of `comm` and `fderiv comm` outside the transition annulus -/

/-- On the open young region `{y' | 0 < ϱ y' ∧ ν * R² < (4/5) * ϱ y'²}`, the commutator
`comm ν μ R χy Z τ` vanishes identically for every field `Z`. -/
theorem comm_eq_zero_of_young {ν μ R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (Z : ℝ → Space → Space) (τ : ℝ) {y : Space} (hy : 0 < ϱ y)
    (h : ν * R ^ 2 < (4 / 5) * ϱ y ^ 2) :
    comm ν μ R χy Z τ y = 0 := by
  have hn : {y' : Space | 0 < ϱ y' ∧ ν * R ^ 2 < (4 / 5) * ϱ y' ^ 2} ∈ 𝓝 y :=
    (isOpen_young ν R).mem_nhds ⟨hy, h⟩
  have hage : ∀ y' : Space, 0 < ϱ y' → ν * R ^ 2 < (4 / 5) * ϱ y' ^ 2 →
      ν * age R y' < 4 / 5 := by
    intro y' hy' h'
    unfold age
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
    exact h'
  have hX : ∀ τ', wardStreamCut ν R χy Z τ' =ᶠ[𝓝 y] Z τ' := by
    intro τ'
    filter_upwards [hn] with y' hy'
    exact wardStreamCut_eq_self_young hχ Z τ' (hage y' hy'.1 hy'.2)
  unfold YBComm.comm
  rw [physDmu_congr_nhds hX τ, wardStreamCut_eq_self_young hχ _ τ (hage y hy h), sub_self]

/-- For any point `y` with `0 < ϱ y` and `ν * R² < (4/5) * ϱ y²`, `comm ν μ R χy Z τ` is
eventually zero in `𝓝 y`. -/
theorem comm_eventuallyEq_zero_of_young {ν μ R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (Z : ℝ → Space → Space) (τ : ℝ) {y : Space} (hy : 0 < ϱ y)
    (h : ν * R ^ 2 < (4 / 5) * ϱ y ^ 2) :
    YBComm.comm ν μ R χy Z τ =ᶠ[𝓝 y] fun _ => 0 := by
  have hn : {y' : Space | 0 < ϱ y' ∧ ν * R ^ 2 < (4 / 5) * ϱ y' ^ 2} ∈ 𝓝 y :=
    (isOpen_young ν R).mem_nhds ⟨hy, h⟩
  filter_upwards [hn] with y' hy'
  exact comm_eq_zero_of_young hχ Z τ hy'.1 hy'.2

/-- At any scaled receiver `ε⁻¹ • xo` with `5 * ν / 4 < xo 0 ^ 2 + xo 1 ^ 2`, the spatial
derivative `fderiv ℝ (comm ν μ ε⁻¹ χy Z τ) (ε⁻¹ • xo)` vanishes for every field `Z`. -/
theorem fderiv_comm_eq_zero_of_gt {ν μ ε : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (hν : 0 < ν) (hε : 0 < ε) (Z : ℝ → Space → Space) (τ : ℝ) {xo : Space}
    (hxo : 5 * ν / 4 < xo 0 ^ 2 + xo 1 ^ 2) :
    fderiv ℝ (YBComm.comm ν μ ε⁻¹ χy Z τ) (ε⁻¹ • xo) = 0 := by
  have hxo0 : 0 < xo 0 ^ 2 + xo 1 ^ 2 := lt_trans (by positivity) hxo
  have hϱ_sq : ϱ (ε⁻¹ • xo) ^ 2 = (ε⁻¹) ^ 2 * (xo 0 ^ 2 + xo 1 ^ 2) := by
    unfold ϱ
    have hnn : 0 ≤ (ε⁻¹ • xo) 0 ^ 2 + (ε⁻¹ • xo) 1 ^ 2 := by positivity
    rw [Real.sq_sqrt hnn]
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have hϱ_pos : 0 < ϱ (ε⁻¹ • xo) := by
    unfold ϱ
    refine Real.sqrt_pos.2 ?_
    have : (ε⁻¹ • xo) 0 ^ 2 + (ε⁻¹ • xo) 1 ^ 2 = (ε⁻¹) ^ 2 * (xo 0 ^ 2 + xo 1 ^ 2) := by
      simp only [PiLp.smul_apply, smul_eq_mul]; ring
    rw [this]
    positivity
  have hyoung : ν * (ε⁻¹) ^ 2 < (4 / 5) * ϱ (ε⁻¹ • xo) ^ 2 := by
    rw [hϱ_sq]
    have hR2 : 0 < (ε⁻¹) ^ 2 := by positivity
    nlinarith
  have hev := comm_eventuallyEq_zero_of_young (μ := μ) hχ Z τ hϱ_pos hyoung
  rw [hev.fderiv_eq]
  simp

/-! ## 2. Higher-order separated kernel difference estimate (`sepKernelDiffIter`) -/

/-- **All-order separated kernel difference estimate** (SP 3604-3610, 3760-3766): for every
derivative order `j : ℕ`, `IIIa.sepKernelBounds` yields `C ≥ 0` such that along any vertical
segment `[u₀, u]` (`u 0 = u₀ 0`, `u 1 = u₀ 1`) at horizontal radius `√(u₀ 0² + u₀ 1²) ≥ D > 0`
and heat parameter `s > 0`,
`‖D^j K_s(u) - D^j K_0(u₀)‖ ≤ C (s + ‖u - u₀‖) (D^{-5-j} + D^{-4-j})`. -/
theorem sepKernelDiffIter (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i k : Fin 3) (s : ℝ), 0 < s → ∀ (u₀ u : Space) (D : ℝ), 0 < D →
      D ≤ Real.sqrt (u₀ 0 ^ 2 + u₀ 1 ^ 2) → u 0 = u₀ 0 → u 1 = u₀ 1 →
        ‖iteratedFDeriv ℝ j (fun x => IIIa.heatLerayK s i k x) u -
            iteratedFDeriv ℝ j (fun x => IIIa.heatLerayK0 i k x) u₀‖ ≤
          C * (s + ‖u - u₀‖) * (D ^ (-5 - (j : ℝ)) + D ^ (-4 - (j : ℝ))) := by
  obtain ⟨C, hCb⟩ := IIIa.sepKernelBounds j
  have hne1 : (!₂[(1 : ℝ), 0, 0] : Space) ≠ 0 := by
    intro h0
    have := congrArg (fun x : Space => x 0) h0
    simp at this
  have hC0 : 0 ≤ C := by
    have h1 := (hCb (!₂[1, 0, 0]) hne1 0 0).2.2 1 one_pos
    have h2 := norm_nonneg (iteratedFDeriv ℝ j
      (fun y => IIIa.heatLerayK 1 0 0 y - IIIa.heatLerayK0 0 0 y) (!₂[1, 0, 0]))
    have hpos : 0 < ‖(!₂[(1 : ℝ), 0, 0] : Space)‖ := norm_pos_iff.2 hne1
    have h3 : 0 < ‖(!₂[(1 : ℝ), 0, 0] : Space)‖ ^ (-5 - (j : ℝ)) := Real.rpow_pos_of_pos hpos _
    by_contra hneg
    have hneg' : C < 0 := lt_of_not_ge hneg
    have : C * 1 * ‖(!₂[(1 : ℝ), 0, 0] : Space)‖ ^ (-5 - (j : ℝ)) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) h3
    linarith
  refine ⟨2 * C, by positivity, ?_⟩
  intro i k s hs u₀ u D hD hDu₀ hu0 hu1
  have hρ := IIIa.mp_rho_sub u₀ u hu0 hu1
  have hnormu : D ≤ ‖u‖ := hDu₀.trans (by rw [← hρ]; exact IIIa.rho_le_norm u)
  have hu_ne : u ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnormu; linarith
  have hK1 : ContDiffAt ℝ j (fun x => IIIa.heatLerayK s i k x) u :=
    by simpa using contDiffAt_nat ((IIIa.heatLerayKSmoothAll s hs i k).contDiffAt) j
  have hK0 : ContDiffAt ℝ j (fun x => IIIa.heatLerayK0 i k x) u :=
    by simpa using contDiffAt_nat (IIIa.mp_K0_contDiffAt u hu_ne i k) j
  have hdiff : iteratedFDeriv ℝ j (fun x => IIIa.heatLerayK s i k x) u -
      iteratedFDeriv ℝ j (fun x => IIIa.heatLerayK0 i k x) u =
      iteratedFDeriv ℝ j (fun y => IIIa.heatLerayK s i k y - IIIa.heatLerayK0 i k y) u :=
    (iteratedFDeriv_sub_apply hK1 hK0).symm
  have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hheat : ‖iteratedFDeriv ℝ j (fun x => IIIa.heatLerayK s i k x) u -
      iteratedFDeriv ℝ j (fun x => IIIa.heatLerayK0 i k x) u‖ ≤ C * s * D ^ (-5 - (j : ℝ)) := by
    rw [hdiff]
    refine ((hCb u hu_ne i k).2.2 s hs).trans ?_
    have hexp : (-5 - (j : ℝ)) ≤ 0 := by linarith
    have hpow := Real.rpow_le_rpow_of_nonpos hD hnormu hexp
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hseg : ∀ x ∈ segment ℝ u₀ u, D ≤ ‖x‖ := by
    intro x hx
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
    have h0 : (a • u₀ + b • u) 0 = u₀ 0 := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hu0]
      rw [← add_mul, hab, one_mul]
    have h1 : (a • u₀ + b • u) 1 = u₀ 1 := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hu1]
      rw [← add_mul, hab, one_mul]
    refine hDu₀.trans ?_
    have := IIIa.rho_le_norm (a • u₀ + b • u)
    rw [h0, h1] at this
    exact this
  have hne : ∀ x ∈ segment ℝ u₀ u, x ≠ 0 := by
    intro x hx h0
    have := hseg x hx
    rw [h0, norm_zero] at this
    linarith
  have hdf : ∀ x ∈ segment ℝ u₀ u,
      DifferentiableAt ℝ (iteratedFDeriv ℝ j (fun y => IIIa.heatLerayK0 i k y)) x := by
    intro x hx
    exact (IIIa.mp_K0_contDiffAt x (hne x hx) i k).differentiableAt_iteratedFDeriv
      (m := j) (n := ∞) (by exact_mod_cast WithTop.coe_lt_top j)
  have hbd : ∀ x ∈ segment ℝ u₀ u,
      ‖fderiv ℝ (iteratedFDeriv ℝ j (fun y => IIIa.heatLerayK0 i k y)) x‖ ≤
        C * D ^ (-4 - (j : ℝ)) := by
    intro x hx
    rw [norm_fderiv_iteratedFDeriv]
    refine ((hCb x (hne x hx) i k).2.1).trans ?_
    have hexp : (-4 - (j : ℝ)) ≤ 0 := by linarith
    have hpow := Real.rpow_le_rpow_of_nonpos hD (hseg x hx) hexp
    exact mul_le_mul_of_nonneg_left hpow hC0
  have hmv := (convex_segment u₀ u).norm_image_sub_le_of_norm_fderiv_le hdf hbd
    (left_mem_segment ℝ u₀ u) (right_mem_segment ℝ u₀ u)
  have hD5 : 0 ≤ D ^ (-5 - (j : ℝ)) := Real.rpow_nonneg hD.le _
  have hD4 : 0 ≤ D ^ (-4 - (j : ℝ)) := Real.rpow_nonneg hD.le _
  calc ‖iteratedFDeriv ℝ j (fun x => IIIa.heatLerayK s i k x) u -
        iteratedFDeriv ℝ j (fun x => IIIa.heatLerayK0 i k x) u₀‖
      = ‖(iteratedFDeriv ℝ j (fun x => IIIa.heatLerayK s i k x) u -
          iteratedFDeriv ℝ j (fun x => IIIa.heatLerayK0 i k x) u) +
          (iteratedFDeriv ℝ j (fun x => IIIa.heatLerayK0 i k x) u -
          iteratedFDeriv ℝ j (fun x => IIIa.heatLerayK0 i k x) u₀)‖ := by congr 1; abel
    _ ≤ ‖iteratedFDeriv ℝ j (fun x => IIIa.heatLerayK s i k x) u -
          iteratedFDeriv ℝ j (fun x => IIIa.heatLerayK0 i k x) u‖ +
        ‖iteratedFDeriv ℝ j (fun x => IIIa.heatLerayK0 i k x) u -
          iteratedFDeriv ℝ j (fun x => IIIa.heatLerayK0 i k x) u₀‖ := norm_add_le _ _
    _ ≤ C * s * D ^ (-5 - (j : ℝ)) + C * D ^ (-4 - (j : ℝ)) * ‖u - u₀‖ := add_le_add hheat hmv
    _ ≤ 2 * C * (s + ‖u - u₀‖) * (D ^ (-5 - (j : ℝ)) + D ^ (-4 - (j : ℝ))) := by
      have h1 : 0 ≤ ‖u - u₀‖ := norm_nonneg _
      nlinarith [mul_nonneg hC0 hs.le, mul_nonneg hC0 h1, mul_nonneg (mul_nonneg hC0 hs.le) hD4,
        mul_nonneg (mul_nonneg hC0 h1) hD5, mul_nonneg (mul_nonneg hC0 hs.le) hD5,
        mul_nonneg (mul_nonneg hC0 h1) hD4]

/-! ## 3. Moment and commutator decomposition definitions -/

theorem tn_nonneg (M : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ IIIa.tensorNorm M := by
  unfold IIIa.tensorNorm; exact Real.sqrt_nonneg _

theorem thinMoment_meanLift_eq' (c : ℝ) (hc : 0 < c) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) :
    IIIa.thinMoment c (IIIa.meanLift G) = ∫⁻ w : (ℝ × ℝ) × ℝ, ENNReal.ofReal (1 + |w.2|) *
      ENNReal.ofReal (IIIa.tensorNorm (G w.1 w.2)) := by
  unfold IIIa.thinMoment IIIa.meanLift
  refine lintegral_congr fun w => ?_
  congr 1
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, mul_assoc,
    mul_comm (ENNReal.ofReal _) (ENNReal.ofReal c), ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne']
  simp only [ENNReal.ofReal_one, one_mul]
  rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num)]
  congr 1
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (tn_nonneg _)]

/-- The scalar cutoff part `tcC0(ϱ y) • Z τ y` of `wardStreamCut`. -/
def cutMain (ν R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  tcC0 ν R χy (ϱ y) • Z τ y

/-- The outward stream-primitive part `tcF0(ϱ y) • psiFld Z τ y` of `wardStreamCut`. -/
def cutPsi (ν R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  tcF0 ν R χy (ϱ y) • psiFld Z τ y

/-- The `[D_{μ+1}, cutMain]` part of the commutator (source 3700-3712, 4203-4214):
`tcA1(ϱ y) • Z τ y + tcA2(ϱ y) • fderiv ℝ (Z τ) y (radialUnit y)`. -/
def commMain (ν R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  tcA1 ν R χy (ϱ y) • Z τ y + tcA2 ν R χy (ϱ y) • fderiv ℝ (Z τ) y (radialUnit y)

/-- The `[D_{μ+1}, cutPsi]` outward stream-primitive part of the commutator (source 4195-4215). -/
def commPsi (ν μ R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  physDmu ν (μ + 1) (cutPsi ν R χy Z) τ y - cutPsi ν R χy (physDmu ν (μ + 1) Z) τ y

/-- `wardStreamCut = cutMain + cutPsi` identically. -/
theorem wardStreamCut_eq_cutMain_add_cutPsi (ν R : ℝ) (χy : ℝ → ℝ)
    (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) :
    wardStreamCut ν R χy Z τ y = cutMain ν R χy Z τ y + cutPsi ν R χy Z τ y := by
  unfold wardStreamCut cutMain cutPsi psiFld tcC0 tcF0 age
  rw [mul_smul]

/-- The 3-term main commutator derivative majorant at `y = ε⁻¹ • xo`, `r = √(xo 0² + xo 1²)`
(source 3700-3712, 4207-4213, 5427-5432): combines 0th, 1st, and 2nd spatial derivatives of
`Z₁ - Z₂` at `y`. -/
def commMainMaj (ν ε r : ℝ) (Z₁ Z₂ : ℝ → Space → Space) (τ : ℝ) (y : Space) : ℝ :=
  ε * r⁻¹ * ‖Z₁ τ y - Z₂ τ y‖ +
    ‖fderiv ℝ (Z₁ τ) y - fderiv ℝ (Z₂ τ) y‖ +
    ν * ε * r⁻¹ * ‖iteratedFDeriv ℝ 2 (Z₁ τ) y - iteratedFDeriv ℝ 2 (Z₂ τ) y‖

/-! ## 4. The transition-annulus sub-leaves -/

/-- **Sub-leaf 1 (`SepCommMainLeibniz`, task `PartIII-b:C/rep/8/1/1/2/5/2/1/1`)**:
Leibniz derivative inequality for `comm = commMain + commPsi` on the transition annulus
`ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4` (source 3700-3712, 4195-4215, 5427-5432). -/
def SepCommMainLeibniz : Prop :=
  ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ ν c ε μ : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 →
      0 < μ → μ < 1 / 4 →
      ∀ G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j) →
        (∀ x' Y, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
        Integrable (fun w : (ℝ × ℝ) × ℝ => (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)) volume →
        ∀ (τ : ℝ) (xo : Space), ν ≤ xo 0 ^ 2 + xo 1 ^ 2 → xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4 →
          let Z₁ := srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G))
          let Z₂ := newtonX0 ε μ G
          let y := ε⁻¹ • xo
          let r := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
          ‖fderiv ℝ (comm ν μ ε⁻¹ χy Z₁ τ) y - fderiv ℝ (comm ν μ ε⁻¹ χy Z₂ τ) y‖ ≤
            C₀ * commMainMaj ν ε r Z₁ Z₂ τ y +
              ‖fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y -
                fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y‖

/-- **Sub-leaf 2 (`SepCommMainDiff0`, task `PartIII-b:C/rep/8/1/1/2/5/2/1/2`)**:
Order-0 finite-width and heat-to-Newton bound on the transition annulus (source 5415-5427,
SP 3735-3766 at `j = 1` via `sepKernelDiffIter 1`): `∇K_s - ∇K_0` has degree `-5` with factor
`ε`, giving `‖srcX0 - newtonX0‖ ≲ ε³ |xo'|⁻⁴ N₁(G)`, and multiplying by `ε |xo'|⁻¹` gives
`ε⁴ |xo'|⁻⁵ N₁(G)`. -/
def SepCommMainDiff0 : Prop :=
  ∃ (C₀ : ℝ) (k : ℕ), 0 ≤ C₀ ∧
    ∀ ν c ε μ : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 < μ → μ < 1 / 4 →
      ∀ G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j) →
        (∀ x' Y, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
        Integrable (fun w : (ℝ × ℝ) × ℝ => (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)) volume →
        ∀ (τ : ℝ) (xo : Space), ν ≤ xo 0 ^ 2 + xo 1 ^ 2 → xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4 →
          ε * (Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2))⁻¹ *
              ‖srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G)) τ (ε⁻¹ • xo) -
                newtonX0 ε μ G τ (ε⁻¹ • xo)‖ ≤
            C₀ * (1 + ν⁻¹ + c) ^ k * ε ^ 4 * Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ) *
              ∫ w : (ℝ × ℝ) × ℝ, (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)

/-- **Sub-leaf 3 (`SepCommMainDiff1`)**: Order-1 finite-width and heat-to-Newton bound on the
transition annulus. Proved below (`sepCommMainDiff1`) from `sepMeanFar`. -/
def SepCommMainDiff1 : Prop :=
  ∃ (C₁ : ℝ) (k : ℕ), 0 ≤ C₁ ∧
    ∀ ν c ε μ : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 < μ → μ < 1 / 4 →
      ∀ G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j) →
        (∀ x' Y, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
        Integrable (fun w : (ℝ × ℝ) × ℝ => (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)) volume →
        ∀ (τ : ℝ) (xo : Space), ν ≤ xo 0 ^ 2 + xo 1 ^ 2 → xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4 →
          ‖fderiv ℝ (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G)) τ) (ε⁻¹ • xo) -
              fderiv ℝ (newtonX0 ε μ G τ) (ε⁻¹ • xo)‖ ≤
            C₁ * (1 + ν⁻¹ + c) ^ k * ε ^ 4 * Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ) *
              ∫ w : (ℝ × ℝ) × ℝ, (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)

/-- **Sub-leaf 4 (`SepCommMainDiff2`, task `PartIII-b:C/rep/8/1/1/2/5/2/1/3`)**:
Order-2 (Hessian) finite-width and heat-to-Newton bound on the transition annulus (source
5415-5427, SP 3735-3766 at `j = 3` via `sepKernelDiffIter 3`): `D²∇K_s - D²∇K_0` has degree `-7`
with factor `ε`, giving `‖D²_y srcX0 - D²_y newtonX0‖ ≲ ε⁵ |xo'|⁻⁶ N₁(G)`, and multiplying by
`ν ε |xo'|⁻¹` (`ν |xo'|⁻² ≤ 1`, `ε ≤ 1`) gives `ε⁴ |xo'|⁻⁵ N₁(G)`. -/
def SepCommMainDiff2 : Prop :=
  ∃ (C₂ : ℝ) (k : ℕ), 0 ≤ C₂ ∧
    ∀ ν c ε μ : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 < μ → μ < 1 / 4 →
      ∀ G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j) →
        (∀ x' Y, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
        Integrable (fun w : (ℝ × ℝ) × ℝ => (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)) volume →
        ∀ (τ : ℝ) (xo : Space), ν ≤ xo 0 ^ 2 + xo 1 ^ 2 → xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4 →
          ν * ε * (Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2))⁻¹ *
              ‖iteratedFDeriv ℝ 2 (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G)) τ) (ε⁻¹ • xo) -
                iteratedFDeriv ℝ 2 (newtonX0 ε μ G τ) (ε⁻¹ • xo)‖ ≤
            C₂ * (1 + ν⁻¹ + c) ^ k * ε ^ 4 * Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ) *
              ∫ w : (ℝ × ℝ) × ℝ, (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)

/-- **Sub-leaf 5 (`SepCommPsiDiff`, task `PartIII-b:C/rep/8/1/1/2/5/2/1/4`)**:
Outward stream-primitive commutator difference bound on the transition annulus (source 4178-4215,
5415-5432): `tcF0(ϱ y)` carries `ν ε² |xo'|⁻⁴` and `outPrim (srcX0 - newtonX0)` along the outward
ray `ρ ≥ ϱ y` carries `ε |xo'|⁻² N₁(G)` (from `sepKernelDiffIter`), so `D_y commPsi` of
`srcX0 - newtonX0` is bounded by `C (1 + ν⁻¹ + c)^k ε⁴ |xo'|⁻⁵ N₁(G)`. -/
def SepCommPsiDiff : Prop :=
  ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ (C₃ : ℝ) (k : ℕ), 0 ≤ C₃ ∧
    ∀ ν c ε μ : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 < μ → μ < 1 / 4 →
      ∀ G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j) →
        (∀ x' Y, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
        Integrable (fun w : (ℝ × ℝ) × ℝ => (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)) volume →
        ∀ (τ : ℝ) (xo : Space), ν ≤ xo 0 ^ 2 + xo 1 ^ 2 → xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4 →
          ‖fderiv ℝ (commPsi ν μ ε⁻¹ χy
                (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G))) τ) (ε⁻¹ • xo) -
              fderiv ℝ (commPsi ν μ ε⁻¹ χy (newtonX0 ε μ G) τ) (ε⁻¹ • xo)‖ ≤
            C₃ * (1 + ν⁻¹ + c) ^ k * ε ^ 4 * Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ) *
              ∫ w : (ℝ × ℝ) × ℝ, (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)

/-! ## 5. Proof of `sepCommMainDiff1` from `sepMeanFar` -/

private theorem fderiv_srcX0_mean (ν μ : ℝ) (src : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (τ : ℝ) (y : Space)
    (hA : DifferentiableAt ℝ (fun y => IIIa.sepW ν (μ : ℂ) src y τ) y)
    (hB : DifferentiableAt ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) src y τ) y) :
    fderiv ℝ (srcX0 ν μ src τ) y =
      PhasePrim.reMap.comp (fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) src y τ) y -
        fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) src y τ) y) := by
  have hw : srcX0 ν μ src τ = fun y => PhasePrim.reMap
      ((fun y => IIIa.sepW ν (μ : ℂ) src y τ) y -
        (fun y => IIIa.sepW ν ((μ : ℂ) + 1) src y τ) y) := rfl
  rw [hw]
  exact (PhasePrim.reMap.hasFDerivAt.comp y (hA.hasFDerivAt.sub hB.hasFDerivAt)).fderiv

private theorem hasFDerivAt_sepVmu0_scale {ε : ℝ} {μc : ℂ}
    {G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ} {xo : Space} (hε : 0 < ε)
    (hV : DifferentiableAt ℝ (IIIa.sepVmu0 μc G) xo) :
    HasFDerivAt (fun y : Space => IIIa.sepVmu0 μc G (ε • y))
      (ε • fderiv ℝ (IIIa.sepVmu0 μc G) xo) (ε⁻¹ • xo) := by
  have h1 : HasFDerivAt (fun y : Space => ε • y) (ε • ContinuousLinearMap.id ℝ Space)
      (ε⁻¹ • xo) := (hasFDerivAt_id (ε⁻¹ • xo)).const_smul ε
  have h2 : HasFDerivAt (IIIa.sepVmu0 μc G) (fderiv ℝ (IIIa.sepVmu0 μc G) xo)
      (ε • (ε⁻¹ • xo)) := by
    rw [smul_inv_smul₀ hε.ne']
    exact hV.hasFDerivAt
  have h3 := h2.comp (ε⁻¹ • xo) h1
  have heq : (fderiv ℝ (IIIa.sepVmu0 μc G) xo).comp (ε • ContinuousLinearMap.id ℝ Space) =
      ε • fderiv ℝ (IIIa.sepVmu0 μc G) xo := by
    ext v; simp
  rwa [heq] at h3

private theorem fderiv_newtonX0 {ε μ : ℝ} (hε : 0 < ε)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) {xo : Space}
    (hV0 : DifferentiableAt ℝ (IIIa.sepVmu0 (μ : ℂ) G) xo)
    (hV1 : DifferentiableAt ℝ (IIIa.sepVmu0 ((μ : ℂ) + 1) G) xo) :
    fderiv ℝ (newtonX0 ε μ G τ) (ε⁻¹ • xo) =
      PhasePrim.reMap.comp
        ((ε ^ 3 : ℝ) • fderiv ℝ (IIIa.sepVmu0 (μ : ℂ) G) xo -
          (ε ^ 3 : ℝ) • fderiv ℝ (IIIa.sepVmu0 ((μ : ℂ) + 1) G) xo) := by
  have hd0 := hasFDerivAt_sepVmu0_scale hε hV0
  have hd1 := hasFDerivAt_sepVmu0_scale hε hV1
  have hsub := hd0.sub hd1
  have hre := PhasePrim.reMap.hasFDerivAt.comp (ε⁻¹ • xo) hsub
  have hsm := hre.const_smul (ε ^ 2)
  change fderiv ℝ (ε ^ 2 • ⇑PhasePrim.reMap ∘
      ((fun y => IIIa.sepVmu0 (μ : ℂ) G (ε • y)) -
        fun y => IIIa.sepVmu0 ((μ : ℂ) + 1) G (ε • y))) (ε⁻¹ • xo) = _
  rw [hsm.fderiv]
  ext v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub, map_smul, smul_sub, smul_smul]
  have he : ε ^ 2 * ε = ε ^ 3 := by ring
  rw [he]

private theorem poly_le_13 (ν c : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) (hc : 0 < c) :
    1 + ν⁻¹ + c + (Real.sqrt ν)⁻¹ +
        Real.sqrt ν * (Real.sqrt ν - Real.sqrt (5 * ν / 6))⁻¹ ≤ 13 * (1 + ν⁻¹ + c) := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hg := PhasePrim.gap_le ν hν
  have hd : 0 < Real.sqrt ν - Real.sqrt (5 * ν / 6) := by linarith
  have h1 : Real.sqrt ν * (Real.sqrt ν - Real.sqrt (5 * ν / 6))⁻¹ ≤ 12 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hd]
    linarith
  have hνi : 1 ≤ ν⁻¹ := one_le_inv_iff₀.2 ⟨hν, hν1⟩
  have hsν : ν ≤ Real.sqrt ν := by
    have := Real.sqrt_le_sqrt (mul_le_of_le_one_left hν.le hν1 : ν * ν ≤ ν)
    rwa [Real.sqrt_mul_self hν.le] at this
  have h3 : (Real.sqrt ν)⁻¹ ≤ ν⁻¹ := inv_anti₀ hν hsν
  linarith

/-- **Proof of `SepCommMainDiff1`** from `sepMeanFar` (`GeomX/TaylorWidth/FarLeaf.lean`). -/
theorem sepCommMainDiff1 : SepCommMainDiff1 := by
  obtain ⟨C₀, k₀, hC₀, hlf⟩ := sepMeanFar PhasePrim.Kmu PhasePrim.Kmu_compact PhasePrim.Kmu_re
  refine ⟨4 * C₀ * 13 ^ k₀, k₀, by positivity, ?_⟩
  intro ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 G hGm hGs hwint τ xo hxo _
  set ρo := Real.sqrt (5 * ν / 6)
  set ρi := Real.sqrt ν
  have hρo : 0 ≤ ρo := Real.sqrt_nonneg _
  have hρ : ρo < ρi := Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hρi_xo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) := Real.sqrt_le_sqrt hxo
  have hμK : ((μ : ℝ) : ℂ) ∈ PhasePrim.Kmu := ⟨μ, ⟨hμ0.le, by linarith⟩, rfl⟩
  have hμ1K : ((μ : ℂ) + 1) ∈ PhasePrim.Kmu :=
    ⟨μ + 1, ⟨by linarith, by linarith⟩, by push_cast; rfl⟩
  have hreμ : -(1 / 4) < ((μ : ℝ) : ℂ).re := by simp; linarith
  have hreμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hmeas : Measurable fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2) := by
    unfold IIIa.tensorNorm
    exact Measurable.sqrt (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => (hGm i j).pow_const 2)
  have hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume := by
    refine Integrable.mono' hwint hmeas.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [Real.norm_of_nonneg (tn_nonneg _)]
    exact le_mul_of_one_le_left (tn_nonneg _) (by linarith [abs_nonneg w.2])
  have hW0 := (IIIa.mp_W_eval IIIa.sepKernelBounds ν c ε ρo ρi (μ : ℂ) hν hc hε hρo hρ hreμ
    G hGm hGs hint xo hρi_xo 0).1
  have hW1 := (IIIa.mp_W_eval IIIa.sepKernelBounds ν c ε ρo ρi ((μ : ℂ) + 1) hν hc hε hρo hρ hreμ1
    G hGm hGs hint xo hρi_xo 0).1
  have hV0 := (IIIa.mp_V_deriv IIIa.sepKernelBounds (μ : ℂ) hreμ ρo ρi hρo hρ G hGm hGs hint
    xo hρi_xo).1
  have hV1 := (IIIa.mp_V_deriv IIIa.sepKernelBounds ((μ : ℂ) + 1) hreμ1 ρo ρi hρo hρ G hGm hGs hint
    xo hρi_xo).1
  have hsrc_tau : srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G)) τ =
      srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G)) 0 := rfl
  rw [hsrc_tau, fderiv_srcX0_mean ν μ _ 0 (ε⁻¹ • xo) hW0 hW1,
    fderiv_newtonX0 hε G τ hV0 hV1, ← ContinuousLinearMap.comp_sub]
  set A0 := fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ)
    (IIIa.thinSource ε (IIIa.meanLift G)) y 0) (ε⁻¹ • xo)
  set A1 := fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1)
    (IIIa.thinSource ε (IIIa.meanLift G)) y 0) (ε⁻¹ • xo)
  set B0 := (ε ^ 3 : ℝ) • fderiv ℝ (IIIa.sepVmu0 (μ : ℂ) G) xo
  set B1 := (ε ^ 3 : ℝ) • fderiv ℝ (IIIa.sepVmu0 ((μ : ℂ) + 1) G) xo
  have h_re : ‖PhasePrim.reMap.comp (A0 - A1 - (B0 - B1))‖ ≤ 2 * (‖A0 - B0‖ + ‖A1 - B1‖) := by
    have e : A0 - A1 - (B0 - B1) = (A0 - B0) - (A1 - B1) := by abel
    rw [e]
    calc ‖PhasePrim.reMap.comp ((A0 - B0) - (A1 - B1))‖
        ≤ ‖PhasePrim.reMap‖ * ‖(A0 - B0) - (A1 - B1)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 2 * (‖A0 - B0‖ + ‖A1 - B1‖) :=
          mul_le_mul PhasePrim.opNorm_reMap_le (norm_sub_le _ _) (norm_nonneg _) (by norm_num)
  set Nr : ℝ := ∫ w : (ℝ × ℝ) × ℝ, (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)
  have hNr0 : 0 ≤ Nr := integral_nonneg fun w => mul_nonneg (by positivity) (tn_nonneg _)
  have hNrE : IIIa.thinMoment c (IIIa.meanLift G) = ENNReal.ofReal Nr := by
    rw [thinMoment_meanLift_eq' c hc G,
      ofReal_integral_eq_lintegral_ofReal hwint (Eventually.of_forall fun w =>
        mul_nonneg (by positivity) (tn_nonneg _))]
    refine lintegral_congr fun w => ?_
    rw [ENNReal.ofReal_mul (by positivity)]
  set r := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
  have hr : 0 < r := lt_of_lt_of_le (Real.sqrt_pos.2 hν) hρi_xo
  have hr5 : 0 ≤ r ^ (-5 : ℝ) := Real.rpow_nonneg hr.le _
  set P := 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
  have hP0 : 0 ≤ P := by
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < ρi⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hν)
    have : 0 < ρi - ρo := sub_pos.2 hρ
    positivity
  have hcoef0 : 0 ≤ C₀ * P ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ) := by positivity
  have hB_0 : ‖A0 - B0‖ ≤ C₀ * P ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ) * Nr := by
    have h := hlf ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ (μ : ℂ) hμK G hGm hGs xo hρi_xo
    rw [hNrE, ← ENNReal.ofReal_mul hcoef0, ← ofReal_norm] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hcoef0 hNr0)).1 h
  have hB_1 : ‖A1 - B1‖ ≤ C₀ * P ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ) * Nr := by
    have h := hlf ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ ((μ : ℂ) + 1) hμ1K G hGm hGs xo hρi_xo
    rw [hNrE, ← ENNReal.ofReal_mul hcoef0, ← ofReal_norm] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hcoef0 hNr0)).1 h
  have hP_le : P ^ k₀ ≤ (13 * (1 + ν⁻¹ + c)) ^ k₀ :=
    pow_le_pow_left₀ hP0 (poly_le_13 ν c hν hν1 hc) k₀
  have h_fac : C₀ * P ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ) * Nr ≤
      C₀ * 13 ^ k₀ * (1 + ν⁻¹ + c) ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ) * Nr := by
    rw [mul_pow] at hP_le
    have h1 : C₀ * P ^ k₀ ≤ C₀ * (13 ^ k₀ * (1 + ν⁻¹ + c) ^ k₀) :=
      mul_le_mul_of_nonneg_left hP_le hC₀
    have h2 : 0 ≤ ε ^ 4 * r ^ (-5 : ℝ) * Nr := by positivity
    calc C₀ * P ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ) * Nr
        = (C₀ * P ^ k₀) * (ε ^ 4 * r ^ (-5 : ℝ) * Nr) := by ring
      _ ≤ (C₀ * (13 ^ k₀ * (1 + ν⁻¹ + c) ^ k₀)) * (ε ^ 4 * r ^ (-5 : ℝ) * Nr) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = _ := by ring
  linarith

/-! ## 6. Quantifier-corrected commutator leaf and assembly from the sub-leaves -/

/-- **Transition-annulus commutator bound** (with `∀ χy : ℝ → ℝ, IsStreamCutoff χy →` preceding
`∃ (C : ℝ) (k : ℕ)`). -/
def SepCommAnnulusBoundFixed : Prop :=
  ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ ν c ε μ : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 →
      0 < μ → μ < 1 / 4 →
      ∀ G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j) →
        (∀ x' Y, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
        Integrable (fun w : (ℝ × ℝ) × ℝ => (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)) volume →
        ∀ (τ : ℝ) (xo : Space), ν ≤ xo 0 ^ 2 + xo 1 ^ 2 → xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4 →
          ‖fderiv ℝ (comm ν μ ε⁻¹ χy (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G))) τ)
                (ε⁻¹ • xo) -
              fderiv ℝ (comm ν μ ε⁻¹ χy (newtonX0 ε μ G) τ) (ε⁻¹ • xo)‖ ≤
            C * (1 + ν⁻¹ + c) ^ k * ε ^ 4 * Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ) *
              ∫ w : (ℝ × ℝ) × ℝ, (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)

/-- **Quantifier-corrected `SepCommMeanFar`** (source 5427-5432, 5383-5387, 5415-5427): places
`∀ χy : ℝ → ℝ, IsStreamCutoff χy →` before `∃ (C : ℝ) (k : ℕ)` (matching `StreamCutAlgStmt` and
`TCCoeff`). -/
def SepCommMeanFarFixed : Prop :=
  ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ ν c ε μ : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 →
      0 < μ → μ < 1 / 4 →
      ∀ G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j) →
        (∀ x' Y, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
        ∀ (τ : ℝ) (xo : Space), ν ≤ xo 0 ^ 2 + xo 1 ^ 2 →
          ‖fderiv ℝ (comm ν μ ε⁻¹ χy (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G))) τ)
                (ε⁻¹ • xo) -
              fderiv ℝ (comm ν μ ε⁻¹ χy (newtonX0 ε μ G) τ) (ε⁻¹ • xo)‖ₑ ≤
            ENNReal.ofReal (C * (1 + ν⁻¹ + c) ^ k * ε ^ 4 *
              Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ)) * IIIa.thinMoment c (IIIa.meanLift G)

/-- Reduction of `SepCommMeanFarFixed` to the transition annulus `SepCommAnnulusBoundFixed`. -/
theorem sepCommMeanFarFixed_of_annulus (hAnn : SepCommAnnulusBoundFixed) : SepCommMeanFarFixed := by
  intro χy hχ
  obtain ⟨C, k, hC0, hB⟩ := hAnn χy hχ
  refine ⟨C + 1, k, by positivity, ?_⟩
  intro ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 G hGm hGs τ xo hxo
  have hr2 : 0 < xo 0 ^ 2 + xo 1 ^ 2 := lt_of_lt_of_le hν hxo
  have hr : 0 < Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) := Real.sqrt_pos.2 hr2
  have hcoef : 0 < (C + 1) * (1 + ν⁻¹ + c) ^ k * ε ^ 4 *
      Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ) := by
    have : 0 < 1 + ν⁻¹ + c := by have := inv_pos.2 hν; positivity
    have : 0 < Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ) := Real.rpow_pos_of_pos hr _
    positivity
  by_cases hgt : 5 * ν / 4 < xo 0 ^ 2 + xo 1 ^ 2
  · rw [fderiv_comm_eq_zero_of_gt hχ hν hε _ τ hgt,
      fderiv_comm_eq_zero_of_gt hχ hν hε _ τ hgt, sub_self,
      ← ofReal_norm, norm_zero, ENNReal.ofReal_zero]
    exact zero_le
  have hle : xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4 := le_of_not_gt hgt
  by_cases hN : IIIa.thinMoment c (IIIa.meanLift G) = ⊤
  · rw [hN, ENNReal.mul_top (by simpa using hcoef)]
    exact le_top
  rw [thinMoment_meanLift_eq' c hc G] at hN ⊢
  have hmeas : Measurable fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2) := by
    unfold IIIa.tensorNorm
    exact Measurable.sqrt (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => (hGm i j).pow_const 2)
  have hwm : Measurable fun w : (ℝ × ℝ) × ℝ => (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2) :=
    (measurable_const.add (continuous_abs.measurable.comp measurable_snd)).mul hmeas
  have hwint : Integrable (fun w : (ℝ × ℝ) × ℝ => (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2))
      volume := by
    refine ⟨hwm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have hpt : ∀ w : (ℝ × ℝ) × ℝ, ‖(1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)‖ₑ =
        ENNReal.ofReal (1 + |w.2|) * ENNReal.ofReal (IIIa.tensorNorm (G w.1 w.2)) := by
      intro w
      rw [← ofReal_norm, Real.norm_of_nonneg (mul_nonneg (by positivity) (tn_nonneg _)),
        ENNReal.ofReal_mul (by positivity)]
    simp_rw [hpt]
    exact lt_top_iff_ne_top.2 hN
  set Nr : ℝ := ∫ w : (ℝ × ℝ) × ℝ, (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2) with hNr
  have hNrE : ENNReal.ofReal Nr = ∫⁻ w : (ℝ × ℝ) × ℝ, ENNReal.ofReal (1 + |w.2|) *
      ENNReal.ofReal (IIIa.tensorNorm (G w.1 w.2)) := by
    rw [hNr, ofReal_integral_eq_lintegral_ofReal hwint (Eventually.of_forall fun w =>
      mul_nonneg (by positivity) (tn_nonneg _))]
    refine lintegral_congr fun w => ?_
    rw [ENNReal.ofReal_mul (by positivity)]
  rw [← hNrE, ← ofReal_norm, ← ENNReal.ofReal_mul hcoef.le]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := hB ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 G hGm hGs hwint τ xo hxo hle
  have hp : 0 ≤ (1 + ν⁻¹ + c) ^ k * ε ^ 4 *
      Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ) * Nr := by
    have : 0 ≤ 1 + ν⁻¹ + c := by have := inv_pos.2 hν; positivity
    have : 0 ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ) := Real.rpow_nonneg hr.le _
    have : 0 ≤ Nr := integral_nonneg fun w => mul_nonneg (by positivity) (tn_nonneg _)
    positivity
  nlinarith

/-- Assembly of `SepCommAnnulusBoundFixed` from the five sub-leaves. -/
theorem sepCommAnnulusBoundFixed_of (hL : SepCommMainLeibniz) (h0 : SepCommMainDiff0)
    (h1 : SepCommMainDiff1) (h2 : SepCommMainDiff2) (hP : SepCommPsiDiff) :
    SepCommAnnulusBoundFixed := by
  intro χy hχ
  obtain ⟨CL, hCL, hLb⟩ := hL χy hχ
  obtain ⟨C₀, k₀, hC₀, h0b⟩ := h0
  obtain ⟨C₁, k₁, hC₁, h1b⟩ := h1
  obtain ⟨C₂, k₂, hC₂, h2b⟩ := h2
  obtain ⟨C₃, k₃, hC₃, h3b⟩ := hP χy hχ
  set K := max (max k₀ k₁) (max k₂ k₃)
  refine ⟨CL * (C₀ + C₁ + C₂) + C₃, K, by positivity, ?_⟩
  intro ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 G hGm hGs hwint τ xo hxo hle
  set M := 1 + ν⁻¹ + c
  have hM1 : 1 ≤ M := by
    have : 0 < ν⁻¹ := inv_pos.2 hν
    linarith
  set r := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
  have hr : 0 < r := lt_of_lt_of_le (Real.sqrt_pos.2 hν) (Real.sqrt_le_sqrt hxo)
  have hr5 : 0 ≤ r ^ (-5 : ℝ) := Real.rpow_nonneg hr.le _
  set Nr : ℝ := ∫ w : (ℝ × ℝ) × ℝ, (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)
  have hNr0 : 0 ≤ Nr := integral_nonneg fun w => mul_nonneg (by positivity) (tn_nonneg _)
  have hk0 : k₀ ≤ K := (le_max_left k₀ k₁).trans (le_max_left _ _)
  have hk1 : k₁ ≤ K := (le_max_right k₀ k₁).trans (le_max_left _ _)
  have hk2 : k₂ ≤ K := (le_max_left k₂ k₃).trans (le_max_right _ _)
  have hk3 : k₃ ≤ K := (le_max_right k₂ k₃).trans (le_max_right _ _)
  have hbL := hLb ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 G hGm hGs hwint τ xo hxo hle
  have hb0 := (h0b ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 G hGm hGs hwint τ xo hxo hle).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM1 hk0) hC₀) (by positivity)) hr5) hNr0)
  have hb1 := (h1b ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 G hGm hGs hwint τ xo hxo hle).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM1 hk1) hC₁) (by positivity)) hr5) hNr0)
  have hb2 := (h2b ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 G hGm hGs hwint τ xo hxo hle).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM1 hk2) hC₂) (by positivity)) hr5) hNr0)
  have hb3 := (h3b ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 G hGm hGs hwint τ xo hxo hle).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM1 hk3) hC₃) (by positivity)) hr5) hNr0)
  have hmaj : commMainMaj ν ε r (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G)))
      (newtonX0 ε μ G) τ (ε⁻¹ • xo) ≤
      (C₀ + C₁ + C₂) * M ^ K * ε ^ 4 * r ^ (-5 : ℝ) * Nr := by
    unfold commMainMaj
    linarith
  calc ‖fderiv ℝ (comm ν μ ε⁻¹ χy (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G))) τ) (ε⁻¹ • xo) -
          fderiv ℝ (comm ν μ ε⁻¹ χy (newtonX0 ε μ G) τ) (ε⁻¹ • xo)‖
      ≤ CL * commMainMaj ν ε r (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G)))
          (newtonX0 ε μ G) τ (ε⁻¹ • xo) +
        ‖fderiv ℝ (commPsi ν μ ε⁻¹ χy (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G))) τ)
            (ε⁻¹ • xo) -
          fderiv ℝ (commPsi ν μ ε⁻¹ χy (newtonX0 ε μ G) τ) (ε⁻¹ • xo)‖ := hbL
    _ ≤ CL * ((C₀ + C₁ + C₂) * M ^ K * ε ^ 4 * r ^ (-5 : ℝ) * Nr) +
        C₃ * M ^ K * ε ^ 4 * r ^ (-5 : ℝ) * Nr :=
      add_le_add (mul_le_mul_of_nonneg_left hmaj hCL) hb3
    _ = (CL * (C₀ + C₁ + C₂) + C₃) * M ^ K * ε ^ 4 * r ^ (-5 : ℝ) * Nr := by ring

/-- **Conditional assembly of `SepCommMeanFarFixed`** from the four remaining annulus leaves
(`SepCommMainDiff1` is discharged by `sepCommMainDiff1`). -/
theorem sepCommMeanFarFixed_of (hL : SepCommMainLeibniz) (h0 : SepCommMainDiff0)
    (h2 : SepCommMainDiff2) (hP : SepCommPsiDiff) : SepCommMeanFarFixed :=
  sepCommMeanFarFixed_of_annulus (sepCommAnnulusBoundFixed_of hL h0 sepCommMainDiff1 h2 hP)

end YBWidth

end UnforcedLeray.Short.PartIIIb.Concrete
