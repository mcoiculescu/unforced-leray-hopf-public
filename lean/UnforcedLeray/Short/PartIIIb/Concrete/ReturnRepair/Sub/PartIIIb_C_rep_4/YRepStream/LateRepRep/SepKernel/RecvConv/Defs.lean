import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.RepPhasePointwise
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.PeriodSmall

/-!
# `PartIII-b:C/rep/4/4/1/org/8/1/org/1/2` (design): `RepRecvConv` from four leaves

Source `the November 2 reference manuscript` 5336 ("followed by `√ρ`"), 5134-5139
(`‖r_b‖_{C_τL^{11/4}} ≤ ρ_b`), 2683-2700 (lifts `𝒩_T T = sT`, `‖𝒩_T T‖²_{Y₂} = πR²‖T‖²_{H_T}`, the
norm of `ρ_b^{-1/2}H_T`), 4147 (`𝒩_T(M_Uw) = U⊗𝒩_vw + 𝒩_vw⊗U`).

At one level `L` (`R = ε⁻¹`, `P = 2εc = 2c/R`), with `G = repG w = r_b ⊗ w + w ⊗ r_b` (the chart
tensor of the exact multiplier):

* `RecvExact` (i): `(M_Uw)₂ = repG w` a.e. for `s^{-1/2}dς`;
* `RecvLift` (ii): `‖repG w‖_{htUng} = (ρ_b π R²)^{-1/2} · (P⁻¹∫₀ᴾ∫|𝒩_T repG w|²)^{1/2}`;
* `RecvHolderPhase` (iii, one phase): Hölder `1/2 = 4/11 + 3/22`;
* `RecvHolder` (iii, all phases): `(P⁻¹∫₀ᴾ∫|𝒩_T repG w|²)^{1/2} ≤ 2ρ_b‖𝒩_vw‖_{L²_τL^{22/3}}`.

`repRecvConv_of` (iv) assembles: `2ρ_b/√(ρ_bπR²) = 2π^{-1/2}ε√ρ_b`, `√ρ_b = √C₀ ν^{-k₀/2}
ε^{3/22}e^{m₀/(2ν)}` (`rhoB_eq`, `ν ≤ 1`), `ε·ε^{3/22} = ε^{25/22}`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace RecvConvOrg

/-- **(i) The exact multiplier** (source 4147, 2706, 3876-3877; `concreteBase_isExactMultiplier`
with `NearInst.multPinOfLink`, then `NearInst.ae_gainHTMeasure`, `NearInst.ae_htRhoMeasure`; needs
`0 < ρ_b`, from `0 < C₀`, `rhoB_eq`): the repair component of `M_Uw` is `repG w` a.e. for the
measure `s^{-1/2}dς` of `H_T`. -/
def RecvExact : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ), 0 < K.C0 → NearAt Pl K L μ →
    (∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb) →
    ∀ w : LVel Pl L,
      ((multOp Pl K L w).snd : Chart → Ten3) =ᵐ[ageμ (cOf L.ν) (-1 / 2)] repG Pl K L w

/-- **(ii) The lift identity** (source 2683-2700 `stress-short:lifts`, i.e. `IIIa.stressLifts` /
`Axi.lintegral_NT_sq`; chart change `FarMajorantL2/ChartChange`, `PolarReduction`, `AgeShift`
as in `chartL2Source_of`): for the symmetric no-swirl tensor `repG w` (meridional entries only; its
`cartLift` is `s·nsSym` at the chart point, `P = 2εc = 2c/R`),
`‖repG w‖_{htUng} = (ρ_b πR²)^{-1/2} (P⁻¹∫₀ᴾ∫|𝒩_T repG w|²)^{1/2}` (`phaseL2Lr P 2` is that
phase `L²_τL²_y` norm; `hTUng² = ρ_b⁻¹∫|·|²s^{-1/2}dς`).  Measurability of `repG w` (a.e. for
`s^{-1/2}dς`), its `c`-periodic reduction to the cell and the null-set transfer
(`chartOfNullPullback`) are part of the proof; `rb` is axisymmetric, periodic and measurable by
`rbFacts` (this is where `2εc ≤ 1` and the exact split are used). -/
def RecvLift : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (S : ℝ), 0 < K.C0 →
    UnforcedLeray.Short.IIb.ExactSplitII (L.params Pl) (L.ρb Pl K) S L.V L.rb →
    2 * L.ε * cOf L.ν ≤ 1 → ∀ w : LVel Pl L,
      htUng (cOf L.ν) (L.ρb Pl K) (repG Pl K L w) =
        ENNReal.ofReal (Real.sqrt (L.ρb Pl K * (Real.pi * (L.ε⁻¹) ^ 2)))⁻¹ *
          phaseL2Lr (2 * L.ε * cOf L.ν) 2 (strPhys L.ε⁻¹ (cOf L.ν) (repG Pl K L w))

/-- **(iii), one phase** (source 5175 with `1/2 = 4/11 + 3/22`; copy of `holderPhase`,
`Concrete/ReturnRepair/Sub/PartIII-b_C_rep_1/HolderPhase.lean`, with the exponent triple
`(r, p, q) = (2, 11/4, 22/3)`, `ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr`): if `f ≤ 2|a||b|` a.e. then
`(∫ f²)^{2/2} ≤ 4‖a‖_{11/4}² (∫|b|^{22/3})^{2/(22/3)}` (`bgp = 11/4`). -/
def RecvHolderPhase : Prop :=
  ∀ (a : Space → Space) (b : Space → UnforcedLeray.PhaseSpace.CVec3) (f : Space → ℝ),
    AEStronglyMeasurable a volume → AEStronglyMeasurable b volume →
    (∀ᵐ y, f y ≤ 2 * ‖a y‖ * ‖b y‖) →
    (∫⁻ y : Space, ENNReal.ofReal (f y) ^ (2 : ℝ)) ^ (2 / (2 : ℝ)) ≤
      ENNReal.ofReal 2 ^ 2 *
        eLpNorm a (ENNReal.ofReal UnforcedLeray.Short.IIb.bgp) volume ^ 2 *
        (∫⁻ y : Space, ‖b y‖ₑ ^ (22 / 3 : ℝ)) ^ (2 / (22 / 3 : ℝ))

/-- **(iii), all phases** (source 5134-5139, 5336; mirror of `repairSourceAt_level`, using
`RecvHolderPhase`, the pointwise bound `|𝒩_T repG w| ≤ 2|r_b||𝒩_vw|` at every `(τ, y)` from
`cartLiftSymOuter_proved` and `tensorNorm_symProd_le'` (as in `repPhasePointwise`, without the
cutoff), `rbFacts`, `velSliceMeas`, and `‖r_b(τ)‖_{L^{11/4}} ≤ ρ_b` from
`ExactSplitII.energy`): the physical repair stress has
`‖𝒩_T repG w‖_{L²_τL²} ≤ 2ρ_b‖𝒩_vw‖_{L²_τL^{22/3}}`. -/
def RecvHolder : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (S : ℝ), 0 < K.C0 →
    UnforcedLeray.Short.IIb.ExactSplitII (L.params Pl) (L.ρb Pl K) S L.V L.rb →
    2 * L.ε * cOf L.ν ≤ 1 → ∀ w : LVel Pl L,
      phaseL2Lr (2 * L.ε * cOf L.ν) 2 (strPhys L.ε⁻¹ (cOf L.ν) (repG Pl K L w)) ≤
        ENNReal.ofReal (2 * L.ρb Pl K) *
          UnforcedLeray.Short.IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 3)
            (fun τ y => ‖velPhys L.ε⁻¹ (cOf L.ν) w (τ, y)‖ₑ)

/-- The constants of (iv): `2ρ_b/√(ρ_bπε⁻²) ≤ (2π^{-1/2}√C₀) ν^{-k₀} ε^{25/22} e^{m₀/(2ν)}` for
`ρ_b = C₀ν^{-k₀}ε^{3/11}e^{m₀/ν}`, `0 < ν ≤ 1`. -/
theorem key_real (C0 ν ε m0 : ℝ) (k0 : ℕ) (hC0 : 0 < C0) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hε : 0 < ε) :
    2 * (C0 * ν⁻¹ ^ k0 * (ε ^ (3 / 11 : ℝ) * Real.exp (m0 / ν))) /
        Real.sqrt ((C0 * ν⁻¹ ^ k0 * (ε ^ (3 / 11 : ℝ) * Real.exp (m0 / ν))) *
          (Real.pi * (ε⁻¹) ^ 2)) ≤
      2 / Real.sqrt Real.pi * Real.sqrt C0 * ν⁻¹ ^ k0 * ε ^ (25 / 22 : ℝ) *
        Real.exp (m0 / 2 / ν) := by
  have ha1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have ha : 1 ≤ ν⁻¹ ^ k0 := one_le_pow₀ ha1
  have hE : 0 < Real.exp (m0 / ν) := Real.exp_pos _
  have hεp : 0 < ε ^ (3 / 11 : ℝ) := Real.rpow_pos_of_pos hε _
  have hρ : 0 < C0 * ν⁻¹ ^ k0 * (ε ^ (3 / 11 : ℝ) * Real.exp (m0 / ν)) := by positivity
  set ρ := C0 * ν⁻¹ ^ k0 * (ε ^ (3 / 11 : ℝ) * Real.exp (m0 / ν)) with hρdef
  have hsq : Real.sqrt (ρ * (Real.pi * (ε⁻¹) ^ 2)) =
      Real.sqrt ρ * Real.sqrt Real.pi * ε⁻¹ := by
    rw [Real.sqrt_mul hρ.le, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq (inv_pos.2 hε).le]
    ring
  have hs0 : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  have hpi0 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hss : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ.le
  have h1 : 2 * ρ / (Real.sqrt ρ * Real.sqrt Real.pi * ε⁻¹) =
      2 / Real.sqrt Real.pi * Real.sqrt ρ * ε := by
    rw [div_eq_iff (by positivity)]
    field_simp
    nlinarith [hss]
  have hexp : Real.sqrt (Real.exp (m0 / ν)) = Real.exp (m0 / 2 / ν) := by
    rw [show Real.exp (m0 / ν) = Real.exp (m0 / 2 / ν) * Real.exp (m0 / 2 / ν) by
      rw [← Real.exp_add]; congr 1; ring]
    exact Real.sqrt_mul_self (Real.exp_pos _).le
  have hrp : Real.sqrt (ε ^ (3 / 11 : ℝ)) = ε ^ (3 / 22 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hε.le]; norm_num
  have hsa : Real.sqrt (ν⁻¹ ^ k0) ≤ ν⁻¹ ^ k0 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith
  have hsρ : Real.sqrt ρ = Real.sqrt C0 * Real.sqrt (ν⁻¹ ^ k0) *
      (ε ^ (3 / 22 : ℝ) * Real.exp (m0 / 2 / ν)) := by
    rw [hρdef, Real.sqrt_mul (by positivity), Real.sqrt_mul hC0.le,
      Real.sqrt_mul hεp.le, hrp, hexp]
  have hε25 : ε ^ (25 / 22 : ℝ) = ε ^ (3 / 22 : ℝ) * ε := by
    rw [show (25 / 22 : ℝ) = 3 / 22 + 1 by norm_num, Real.rpow_add hε, Real.rpow_one]
  rw [hsq, h1, hsρ, hε25]
  have hC0s : 0 < Real.sqrt C0 := Real.sqrt_pos.2 hC0
  have hε3 : 0 < ε ^ (3 / 22 : ℝ) := Real.rpow_pos_of_pos hε _
  have hE2 : 0 < Real.exp (m0 / 2 / ν) := Real.exp_pos _
  have : 2 / Real.sqrt Real.pi * (Real.sqrt C0 * Real.sqrt (ν⁻¹ ^ k0) *
        (ε ^ (3 / 22 : ℝ) * Real.exp (m0 / 2 / ν))) * ε ≤
      2 / Real.sqrt Real.pi * (Real.sqrt C0 * (ν⁻¹ ^ k0) *
        (ε ^ (3 / 22 : ℝ) * Real.exp (m0 / 2 / ν))) * ε := by
    gcongr
  calc _ ≤ _ := this
    _ = _ := by ring


/-- **The assembly (iv) at one level**: the bound of `RepRecvConv` for one level `L` with
`ν ≤ 1`, `2εc ≤ 1`, the exact split and the near pins (`C = 2π^{-1/2}√C₀`, `k = k₀`). -/
theorem recvConv_level (h1 : RecvExact) (h2 : RecvLift) (h3 : RecvHolder)
    (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (S μ : ℝ) (hC0 : 0 < K.C0)
    (hν1 : L.ν ≤ 1) (hP : 2 * L.ε * cOf L.ν ≤ 1)
    (hsplit : UnforcedLeray.Short.IIb.ExactSplitII (L.params Pl) (L.ρb Pl K) S L.V L.rb)
    (hnear : NearAt Pl K L μ)
    (hs : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb) (v : LVel Pl L) :
    htUng (cOf L.ν) (L.ρb Pl K) ((multOp Pl K L v).snd : Chart → Ten3) ≤
      ENNReal.ofReal (2 / Real.sqrt Real.pi * Real.sqrt K.C0 * L.ν⁻¹ ^ K.k0 *
          L.ε ^ (25 / 22 : ℝ) * Real.exp (K.m0 / 2 / L.ν)) *
        UnforcedLeray.Short.IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 3)
          (fun τ y => ‖velPhys L.ε⁻¹ (cOf L.ν) v (τ, y)‖ₑ) := by
  have hνpos : 0 < L.ν := L.ν_pos
  have hεpos : 0 < L.ε := L.ε_pos
  have hρeq := rhoB_eq Pl K L
  have hrhoRep : 0 < rhoRep K L := by
    unfold rhoRep
    exact mul_pos (Real.rpow_pos_of_pos hεpos _) (Real.exp_pos _)
  have hρpos : 0 < L.ρb Pl K := by
    rw [hρeq]
    exact mul_pos (mul_pos hC0 (pow_pos (inv_pos.2 hνpos) _)) hrhoRep
  have hEx := h1 Pl K L μ hC0 hnear hs v
  have hA : htUng (cOf L.ν) (L.ρb Pl K) ((multOp Pl K L v).snd : Chart → Ten3) =
      htUng (cOf L.ν) (L.ρb Pl K) (repG Pl K L v) := by
    unfold htUng
    congr 1
    refine lintegral_congr_ae ?_
    have hEx' := hEx
    rw [← NearInst.ae_htRhoMeasure hρpos] at hEx'
    filter_upwards [hEx'] with p hp
    rw [hp]
  have hB := h2 Pl K L S hC0 hsplit hP v
  have hC := h3 Pl K L S hC0 hsplit hP v
  have hρeq' : L.ρb Pl K = K.C0 * L.ν⁻¹ ^ K.k0 *
      (L.ε ^ (3 / 11 : ℝ) * Real.exp (K.m0 / L.ν)) := by
    rw [hρeq]; rfl
  have hkey := key_real K.C0 L.ν L.ε K.m0 K.k0 hC0 hνpos hν1 hεpos
  have hkey' : (Real.sqrt (L.ρb Pl K * (Real.pi * (L.ε⁻¹) ^ 2)))⁻¹ * (2 * L.ρb Pl K) ≤
      2 / Real.sqrt Real.pi * Real.sqrt K.C0 * L.ν⁻¹ ^ K.k0 * L.ε ^ (25 / 22 : ℝ) *
        Real.exp (K.m0 / 2 / L.ν) := by
    rw [inv_mul_eq_div, hρeq']
    exact hkey
  have hk0 : 0 ≤ (Real.sqrt (L.ρb Pl K * (Real.pi * (L.ε⁻¹) ^ 2)))⁻¹ := by positivity
  rw [hA, hB]
  calc ENNReal.ofReal (Real.sqrt (L.ρb Pl K * (Real.pi * (L.ε⁻¹) ^ 2)))⁻¹ *
        phaseL2Lr (2 * L.ε * cOf L.ν) 2 (strPhys L.ε⁻¹ (cOf L.ν) (repG Pl K L v))
      ≤ ENNReal.ofReal (Real.sqrt (L.ρb Pl K * (Real.pi * (L.ε⁻¹) ^ 2)))⁻¹ *
        (ENNReal.ofReal (2 * L.ρb Pl K) *
          UnforcedLeray.Short.IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 3)
            (fun τ y => ‖velPhys L.ε⁻¹ (cOf L.ν) v (τ, y)‖ₑ)) := by gcongr
    _ = ENNReal.ofReal ((Real.sqrt (L.ρb Pl K * (Real.pi * (L.ε⁻¹) ^ 2)))⁻¹ * (2 * L.ρb Pl K)) *
        UnforcedLeray.Short.IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 3)
          (fun τ y => ‖velPhys L.ε⁻¹ (cOf L.ν) v (τ, y)‖ₑ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hk0]
    _ ≤ _ := by gcongr

/-- **The assembly (iv)**: `RepRecvConv` from `RecvExact`, `RecvLift`, `RecvHolder`
(`C = 2π^{-1/2}√C₀`, `k = k₀`; `ν ≤ 1` and `2εc ≤ 1` for large `n`). -/
theorem repRecvConv_of (dm dp : ℝ) (h1 : RecvExact) (h2 : RecvLift) (h3 : RecvHolder) :
    RepRecvConv dm dp := by
  intro D hst
  refine ⟨2 / Real.sqrt Real.pi * Real.sqrt D.K.C0, D.K.k0, ?_, ?_⟩
  · have := hst.C0_pos
    positivity
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (Iio_mem_nhds one_pos)
  filter_upwards [hν1, periodSmall D hst, hst.actual, hst.pins, hst.near] with n hν hP hact
    hpins hnear
  intro v
  have hpin0 := hpins 0 ⟨by norm_num, by norm_num⟩
  exact recvConv_level h1 h2 h3 D.Pl D.K (D.level n) (D.Sin n) (D.mu n 0) hst.C0_pos hν.le hP
    hact.split (hnear 0 ⟨by norm_num, by norm_num⟩) hpin0.split v

end RecvConvOrg

end UnforcedLeray.Short.PartIIIb.Concrete
