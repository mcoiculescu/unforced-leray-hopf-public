import UnforcedLeray.Short.PartIIb.Sub.ComparisonAndStrongDesign
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphFlat

/-!
# Part II-b, task `PartII-b:G2` (`Sub/PartII-b_G2.lean`): Young and late operator bounds (`YoungLateOperatorBounds`, SP 2432–2445)

Source of record: `the November 2 reference manuscript`
(SP), lines 2432–2445:
* Late physical tail (`s > S ≥ 1`, SP 2434–2437): `StrongLateCoeff` (`G1`) and `ProfileGraphPhys`
  (`T10`) together with the exact norm identity give
  `‖1_{s > S} K_ε‖_{X → X} ≤ 𝒫_ν (S^{-1/2} + ε)`;
* Late flat tail (`s > S ≥ 1`, SP 2439–2442): `v = O(𝒫_ν / s)` and `Dv = O(𝒫_ν / s^{3/2})` paired
  with the free `√s Db_0` graph bound (`ProfileGraphFlat`, `T14`) give
  `‖1_{s > S} K_0‖_{X → X} ≤ 𝒫_ν S^{-1/2}`;
* Young tails (`0 < s < σ ≤ 1`, SP 2443–2445): smooth train/raw coefficients paired with the free
  graph bounds give `‖1_{s < σ} K_ε‖ + ‖1_{s < σ} K_0‖ ≤ 𝒫_ν √σ`.

## Decomposition into 3 leaf tasks

1. **`PartII-b:G2/1` (`PhysKopExists`, SP 2007–2010, 2432–2437)**:
   Existence of the physical interaction operator `K_ε = s B_{U_raw} T_ε` as a bounded linear
   operator `Ke : HpR p.c →L[ℝ] HpR p.c` satisfying `IsKop p Ke` in `BgRegime p d dm dp` for small
   `p.ν`.
2. **`PartII-b:G2/2` (`PhysKopYoungLateBounds`, SP 2434–2437, 2443–2445)**:
   Young (`0 < σ ≤ 1`) and late (`1 ≤ S`) `H_p` indicator bounds for any `Ke : HpR p.c →L[ℝ] HpR p.c`
   satisfying `IsKop p Ke`, using `StrongLateCoeff` (`G1`) and `ProfileGraphPhys` (`T10`).
3. **`PartII-b:G2/3` (`FlatK0opYoungLateBounds`, SP 2439–2445)**:
   Young (`0 < σ ≤ 1`) and late (`1 ≤ S`) `H_p` indicator bounds for any `K0 : HpR p.c →L[ℝ] HpR p.c`
   satisfying `IsK0op p K0`, using `ProfileGraphFlat` (`T14`).

## Proved here (zero `sorry`)

* `young_age_weight_le`, `late_age_inv_sqrt_le`, `bgRegime_eps_le_one`,
  `exists_period_le_one_of_bgRegime`: young/late age-weight inequalities and regime helpers;
* `youngLateOperatorBounds_of_sub`: conditional assembly of `YoungLateOperatorBounds` from
  `PhysKopExists` (`PartII-b:G2/1`), `PhysKopYoungLateBounds` (`PartII-b:G2/2`),
  `FlatK0opYoungLateBounds` (`PartII-b:G2/3`), and `StrongLateCoeff` (`G1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Young and late age-weight inequalities and regime helpers (SP 2432–2445) -/

/-- On the young age region `0 < s ≤ σ ≤ 1`, `s ≤ √σ · √s` and `s ≤ √σ` (SP 2441–2444). -/
theorem young_age_weight_le {s σ : ℝ} (hs0 : 0 ≤ s) (hsσ : s ≤ σ) (hσ1 : σ ≤ 1) :
    s ≤ Real.sqrt σ * Real.sqrt s ∧ s ≤ Real.sqrt σ := by
  have hσ0 : 0 ≤ σ := hs0.trans hsσ
  have hsqrt_le : Real.sqrt s ≤ Real.sqrt σ := Real.sqrt_le_sqrt hsσ
  constructor
  · calc s = Real.sqrt s * Real.sqrt s := (Real.mul_self_sqrt hs0).symm
      _ ≤ Real.sqrt σ * Real.sqrt s :=
          mul_le_mul_of_nonneg_right hsqrt_le (Real.sqrt_nonneg s)
  · calc s ≤ σ := hsσ
      _ = Real.sqrt σ * Real.sqrt σ := (Real.mul_self_sqrt hσ0).symm
      _ ≤ Real.sqrt σ * 1 := by
          gcongr
          simpa using Real.sqrt_le_sqrt hσ1
      _ = Real.sqrt σ := mul_one _

/-- On the late age region `0 < S ≤ s`, `s ^ (-1 / 2 : ℝ) ≤ S ^ (-1 / 2 : ℝ)` (SP 2434–2440). -/
theorem late_age_inv_sqrt_le {S s : ℝ} (hS0 : 0 < S) (hSs : S ≤ s) :
    s ^ (-(1 / 2 : ℝ)) ≤ S ^ (-(1 / 2 : ℝ)) := by
  have hs0 : 0 < s := lt_of_lt_of_le hS0 hSs
  rw [Real.rpow_neg hs0.le, Real.rpow_neg hS0.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hS0 (1 / 2 : ℝ))
    (Real.rpow_le_rpow hS0.le hSs (by norm_num))

/-- In `BgRegime p d dm dp`, `0 < p.ε` and `p.ε ≤ 1`. -/
theorem bgRegime_eps_le_one {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp) :
    p.ε ≤ 1 := by
  rw [hreg.eps_eq]
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (by linarith [hreg.dm_pos, hreg.dm_le]) p.ν_pos.le

/-- For `0 < dm`, there is `ν_per > 0` such that in `BgRegime p d dm dp` with `p.ν ≤ ν_per`,
`2 * p.ε * p.c ≤ 1`. -/
theorem exists_period_le_one_of_bgRegime {dm dp : ℝ} (hdm : 0 < dm) :
    ∃ ν_per : ℝ, 0 < ν_per ∧ ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_per →
      2 * p.ε * p.c ≤ 1 := by
  obtain ⟨ν_per, hν_per, hPer⟩ := poly_exp_small 2 dm 2 hdm
  refine ⟨ν_per, hν_per, fun p d hreg hν => ?_⟩
  exact period_le_one_of hreg (hPer p.ν p.ν_pos hν)

/-! ## 2. Leaf statements (`PartII-b:G2/1`, `PartII-b:G2/2`, `PartII-b:G2/3`) -/

/-- **Leaf 1 (`PartII-b:G2/1`, `PhysKopExists`, SP 2007–2010, 2432–2437)**:
given the Cartesian late coefficient bound (`StrongLateCoeff` with `C_late > 0`, `k_late : ℕ`) and
the physical profile graph bound (`ProfileGraphPhys` at `r = bgp`, `μ = 0` with constant
`C_phys > 0`), in `BgRegime p d dm dp` for small `p.ν` (`p.ε ≤ 1`, `2 * p.ε * p.c ≤ 1`), the
physical interaction operator `K_ε = s B_{U_raw} T_ε` exists as a bounded linear operator
`Ke : HpR p.c →L[ℝ] HpR p.c` satisfying `IsKop p Ke`. -/
def PhysKopExists : Prop :=
  ∀ dm dp : ℝ, 0 < dm →
  ∀ (C_late : ℝ) (k_late : ℕ) (C_phys : ℝ), 0 < C_late → 0 < C_phys →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
        p.ε ≤ 1 → 2 * p.ε * p.c ≤ 1 →
        (∀ S : ℝ, 1 ≤ S → ∀ (τ : ℝ) (y : Space), (y ∈ Axi.axis ∨ S < Axi.age p.R y) →
          DifferentiableAt ℝ (p.raw τ) y ∧
          ‖p.raw τ y‖ + ‖fderiv ℝ (p.raw τ) y‖ ≤
            C_late * (p.ν ^ k_late)⁻¹ * (S ^ (-(1 / 2 : ℝ)) + p.ε)) →
        (∀ F : CProf, InHr p.c bgp F →
          (∃ b, InHr p.c bgp b ∧ IsResponse p.ν p.c p.ε 0 bgp F b) ∧
          ∀ b, IsResponse p.ν p.c p.ε 0 bgp F b → GraphBound p.ν p.c bgp p.ε C_phys F b) →
        ∃ Ke : HpR p.c →L[ℝ] HpR p.c, IsKop p Ke

/-- **Leaf 2 (`PartII-b:G2/2`, `PhysKopYoungLateBounds`, SP 2434–2437, 2443–2445)**:
given the Cartesian late coefficient bound (`StrongLateCoeff` with `C_late > 0`, `k_late : ℕ`) and
the physical profile graph bound (`ProfileGraphPhys` at `r = bgp`, `μ = 0` with constant
`C_phys > 0`), there exist `C_ke > 0`, `k_ke : ℕ`, and `ν₀ > 0` such that in `BgRegime p d dm dp`
with `p.ν ≤ ν₀`, `p.ε ≤ 1`, and `2 * p.ε * p.c ≤ 1`, any operator `Ke : HpR p.c →L[ℝ] HpR p.c`
satisfying `IsKop p Ke` obeys the young (`0 < σ ≤ 1`) and late (`1 ≤ S`) indicator norm bounds
`hpIndNorm p.c (youngAgeSet σ) (Ke f) ≤ C_ke * (p.ν ^ k_ke)⁻¹ * √σ * ‖f‖` and
`hpIndNorm p.c (lateAgeSet S) (Ke f) ≤ C_ke * (p.ν ^ k_ke)⁻¹ * (S^{-1/2} + p.ε) * ‖f‖`. -/
def PhysKopYoungLateBounds : Prop :=
  ∀ dm dp : ℝ, 0 < dm →
  ∀ (C_late : ℝ) (k_late : ℕ) (C_phys : ℝ), 0 < C_late → 0 < C_phys →
    ∃ (C_ke : ℝ) (k_ke : ℕ) (ν₀ : ℝ), 0 < C_ke ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
        p.ε ≤ 1 → 2 * p.ε * p.c ≤ 1 →
        (∀ S : ℝ, 1 ≤ S → ∀ (τ : ℝ) (y : Space), (y ∈ Axi.axis ∨ S < Axi.age p.R y) →
          DifferentiableAt ℝ (p.raw τ) y ∧
          ‖p.raw τ y‖ + ‖fderiv ℝ (p.raw τ) y‖ ≤
            C_late * (p.ν ^ k_late)⁻¹ * (S ^ (-(1 / 2 : ℝ)) + p.ε)) →
        (∀ F : CProf, InHr p.c bgp F →
          (∃ b, InHr p.c bgp b ∧ IsResponse p.ν p.c p.ε 0 bgp F b) ∧
          ∀ b, IsResponse p.ν p.c p.ε 0 bgp F b → GraphBound p.ν p.c bgp p.ε C_phys F b) →
        ∀ Ke : HpR p.c →L[ℝ] HpR p.c, IsKop p Ke →
          (∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ f : HpR p.c,
            hpIndNorm p.c (youngAgeSet σ) (Ke f) ≤
              C_ke * (p.ν ^ k_ke)⁻¹ * Real.sqrt σ * ‖f‖) ∧
          (∀ S : ℝ, 1 ≤ S → ∀ f : HpR p.c,
            hpIndNorm p.c (lateAgeSet S) (Ke f) ≤
              C_ke * (p.ν ^ k_ke)⁻¹ * (S ^ (-(1 / 2 : ℝ)) + p.ε) * ‖f‖)

/-- **Leaf 3 (`PartII-b:G2/3`, `FlatK0opYoungLateBounds`, SP 2439–2445)**:
given the flat profile graph bound (`ProfileGraphFlat` at `r = bgp`, `μ = 0` with constant
`C_flat > 0`), there exist `C_k0 > 0`, `k_k0 : ℕ`, and `ν₀ > 0` such that in `BgRegime p d dm dp`
with `p.ν ≤ ν₀`, any operator `K0 : HpR p.c →L[ℝ] HpR p.c` satisfying `IsK0op p K0` obeys the young
(`0 < σ ≤ 1`) and late (`1 ≤ S`) indicator norm bounds
`hpIndNorm p.c (youngAgeSet σ) (K0 f) ≤ C_k0 * (p.ν ^ k_k0)⁻¹ * √σ * ‖f‖` and
`hpIndNorm p.c (lateAgeSet S) (K0 f) ≤ C_k0 * (p.ν ^ k_k0)⁻¹ * S^{-1/2} * ‖f‖`. -/
def FlatK0opYoungLateBounds : Prop :=
  ∀ dm dp : ℝ, 0 < dm →
  ∀ C_flat : ℝ, 0 < C_flat →
    ∃ (C_k0 : ℝ) (k_k0 : ℕ) (ν₀ : ℝ), 0 < C_k0 ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
        (∀ F : CProf, InHr p.c bgp F →
          ∃ b, InFlatClass p.c bgp b ∧ IsFlatResponse p.ν 0 F b ∧
            GraphBound p.ν p.c bgp 0 C_flat F b ∧
            ∀ b', InFlatClass p.c bgp b' → IsFlatResponse p.ν 0 F b' → b' =ᵐ[hMeas p.c bgp] b) →
        ∀ K0 : HpR p.c →L[ℝ] HpR p.c, IsK0op p K0 →
          (∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ f : HpR p.c,
            hpIndNorm p.c (youngAgeSet σ) (K0 f) ≤
              C_k0 * (p.ν ^ k_k0)⁻¹ * Real.sqrt σ * ‖f‖) ∧
          (∀ S : ℝ, 1 ≤ S → ∀ f : HpR p.c,
            hpIndNorm p.c (lateAgeSet S) (K0 f) ≤
              C_k0 * (p.ν ^ k_k0)⁻¹ * S ^ (-(1 / 2 : ℝ)) * ‖f‖)

private theorem inv_pow_mono_of_le_one' {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) {j k : ℕ}
    (hjk : j ≤ k) : (ν ^ j)⁻¹ ≤ (ν ^ k)⁻¹ := by
  rw [inv_le_inv₀ (pow_pos hν0 j) (pow_pos hν0 k)]
  exact pow_le_pow_of_le_one hν0.le hν1 hjk

/-- **Conditional assembly of `YoungLateOperatorBounds` (`PartII-b:G2`, SP 2432–2445)** from
`PhysKopExists` (`PartII-b:G2/1`), `PhysKopYoungLateBounds` (`PartII-b:G2/2`),
`FlatK0opYoungLateBounds` (`PartII-b:G2/3`), `StrongLateCoeff` (`G1`), and the proved
`profileGraphPhys_proof` (`T10`) and `profileGraphFlat_proof` (`T14`). -/
theorem youngLateOperatorBounds_of_sub
    (hEx : PhysKopExists)
    (hKe : PhysKopYoungLateBounds)
    (hK0 : FlatK0opYoungLateBounds)
    (h1 : UnforcedLeray.Short.IIb.StrongLateCoeff) :
    UnforcedLeray.Short.IIb.YoungLateOperatorBounds := by
  have hbgp1 : (1 : ℝ) < bgp := by norm_num [bgp]
  have hbgp3 : bgp < (3 : ℝ) := by norm_num [bgp]
  have hgap0 : (0 : ℝ) < (0 : ℂ).re + (3 / bgp - 1) / 2 := by norm_num [bgp]
  obtain ⟨C_phys, hC_phys, hPhys⟩ := profileGraphPhys_proof bgp hbgp1 hbgp3 0 hgap0
  obtain ⟨C_flat, hC_flat, hFlat⟩ := profileGraphFlat_proof bgp hbgp1 hbgp3 0 hgap0
  intro dm dp hdm
  obtain ⟨C_late, k_late, ν_late, hC_late, hν_late, hLate⟩ := h1 dm dp hdm
  obtain ⟨ν_per, hν_per, hPer⟩ := exists_period_le_one_of_bgRegime (dp := dp) hdm
  obtain ⟨ν_ex, hν_ex, hEx_p⟩ := hEx dm dp hdm C_late k_late C_phys hC_late hC_phys
  obtain ⟨C_ke, k_ke, ν_ke, hC_ke, hν_ke, hKe_p⟩ :=
    hKe dm dp hdm C_late k_late C_phys hC_late hC_phys
  obtain ⟨C_k0, k_k0, ν_k0, hC_k0, hν_k0, hK0_p⟩ :=
    hK0 dm dp hdm C_flat hC_flat
  set C : ℝ := C_ke + C_k0
  set k : ℕ := max k_ke k_k0
  set ν₀ : ℝ := min (min ν_ex (min ν_ke ν_k0)) (min (min ν_late ν_per) 1)
  have hC : 0 < C := add_pos hC_ke hC_k0
  have hν₀ : 0 < ν₀ :=
    lt_min (lt_min hν_ex (lt_min hν_ke hν_k0)) (lt_min (lt_min hν_late hν_per) one_pos)
  refine ⟨C, k, ν₀, hC, hν₀, ?_⟩
  intro p d hreg hν
  have hν_pos : 0 < p.ν := p.ν_pos
  have hν_ex' : p.ν ≤ ν_ex := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_ke' : p.ν ≤ ν_ke :=
    hν.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν_k0' : p.ν ≤ ν_k0 :=
    hν.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hν_late' : p.ν ≤ ν_late :=
    hν.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hν_per' : p.ν ≤ ν_per :=
    hν.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hν1 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε1 : p.ε ≤ 1 := bgRegime_eps_le_one hreg
  have hP1 : 2 * p.ε * p.c ≤ 1 := hPer p d hreg hν_per'
  have hLate_p := hLate p d hreg hν_late'
  have hPhys_p := hPhys p.ν p.c p.ε p.ν_pos p.c_pos p.ε_pos hε1 hP1
  have hFlat_p := hFlat p.ν p.c p.ν_pos p.c_pos
  refine ⟨hEx_p p d hreg hν_ex' hε1 hP1 hLate_p hPhys_p, ?_⟩
  intro Ke K0 hKe_op hK0_op
  obtain ⟨hy_ke, hl_ke⟩ := hKe_p p d hreg hν_ke' hε1 hP1 hLate_p hPhys_p Ke hKe_op
  obtain ⟨hy_k0, hl_k0⟩ := hK0_p p d hreg hν_k0' hFlat_p K0 hK0_op
  have hk_ke : (p.ν ^ k_ke)⁻¹ ≤ (p.ν ^ k)⁻¹ :=
    inv_pow_mono_of_le_one' hν_pos hν1 (le_max_left _ _)
  have hk_k0 : (p.ν ^ k_k0)⁻¹ ≤ (p.ν ^ k)⁻¹ :=
    inv_pow_mono_of_le_one' hν_pos hν1 (le_max_right _ _)
  refine ⟨fun σ hσ0 hσ1 f => ?_, fun S hS1 f => ⟨?_, ?_⟩⟩
  · have b1 := hy_ke σ hσ0 hσ1 f
    have b2 := hy_k0 σ hσ0 hσ1 f
    have b1' : hpIndNorm p.c (youngAgeSet σ) (Ke f) ≤
        C_ke * (p.ν ^ k)⁻¹ * Real.sqrt σ * ‖f‖ := by
      refine b1.trans ?_
      gcongr
    have b2' : hpIndNorm p.c (youngAgeSet σ) (K0 f) ≤
        C_k0 * (p.ν ^ k)⁻¹ * Real.sqrt σ * ‖f‖ := by
      refine b2.trans ?_
      gcongr
    calc hpIndNorm p.c (youngAgeSet σ) (Ke f) + hpIndNorm p.c (youngAgeSet σ) (K0 f)
        ≤ C_ke * (p.ν ^ k)⁻¹ * Real.sqrt σ * ‖f‖ +
            C_k0 * (p.ν ^ k)⁻¹ * Real.sqrt σ * ‖f‖ := add_le_add b1' b2'
      _ = C * (p.ν ^ k)⁻¹ * Real.sqrt σ * ‖f‖ := by dsimp [C]; ring
  · have b1 := hl_ke S hS1 f
    have hS_pos : 0 ≤ S ^ (-(1 / 2 : ℝ)) + p.ε := by
      have : 0 ≤ p.ε := p.ε_pos.le
      positivity
    calc hpIndNorm p.c (lateAgeSet S) (Ke f)
        ≤ C_ke * (p.ν ^ k_ke)⁻¹ * (S ^ (-(1 / 2 : ℝ)) + p.ε) * ‖f‖ := b1
      _ ≤ C * (p.ν ^ k)⁻¹ * (S ^ (-(1 / 2 : ℝ)) + p.ε) * ‖f‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg f)
          refine mul_le_mul_of_nonneg_right ?_ hS_pos
          calc C_ke * (p.ν ^ k_ke)⁻¹
              ≤ C_ke * (p.ν ^ k)⁻¹ := mul_le_mul_of_nonneg_left hk_ke hC_ke.le
            _ ≤ C * (p.ν ^ k)⁻¹ :=
                mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)
  · have b2 := hl_k0 S hS1 f
    have hS_pos : 0 ≤ S ^ (-(1 / 2 : ℝ)) := by positivity
    calc hpIndNorm p.c (lateAgeSet S) (K0 f)
        ≤ C_k0 * (p.ν ^ k_k0)⁻¹ * S ^ (-(1 / 2 : ℝ)) * ‖f‖ := b2
      _ ≤ C * (p.ν ^ k)⁻¹ * S ^ (-(1 / 2 : ℝ)) * ‖f‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg f)
          refine mul_le_mul_of_nonneg_right ?_ hS_pos
          calc C_k0 * (p.ν ^ k_k0)⁻¹
              ≤ C_k0 * (p.ν ^ k)⁻¹ := mul_le_mul_of_nonneg_left hk_k0 hC_k0.le
            _ ≤ C * (p.ν ^ k)⁻¹ :=
                mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)

end UnforcedLeray.Short.IIb

end
