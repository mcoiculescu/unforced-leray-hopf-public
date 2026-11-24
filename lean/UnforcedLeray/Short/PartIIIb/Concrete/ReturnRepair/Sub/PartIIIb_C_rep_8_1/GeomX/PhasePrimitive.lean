import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.Transfer
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeaf
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.DPhaseMeas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps

/-!
# `PartIII-b:C/rep/8/1/1/1/2` (`GeomX.PhasePrimitive`): reduction to the far-field leaf

Source `the November 2 reference manuscript`
lines 5400-5427: "One phase primitive in the dilation variable, with its dilation-one boundary
term retained, gives `‖D_yX₁ - D_yX^mt‖_{L²_τ} ≤ P_ν ε⁴ s^{5/2} N`"; the gradient kernel has
degree `-5` and the old-source / young-receiver radius ratio is at most `1/√1.2`.

`phasePrimitive_of` proves the target `D.PhasePrimitive` from the single analytic leaf
`SepOscFar` (`PhasePrimitive/Leaf.lean`: the decay form of `IIIa.SepSplit + IIIa.SepOscPart`;
the docstring there explains why `IIIa.SepOscPart`, whose constant does not decay in the receiver
radius, cannot give the factor `s^{5/2}`).  All bridges are proved:

1. `oldPhys ε⁻¹ c g = thinSource ε F` for the cut planar lift `F = cutLift c √(5ν/6) g`
   (`Lift.lean`), and `oldPhys ε⁻¹ c (meanQ c g)` has the response of
   `thinSource ε (meanLift (phaseMean c F))` (`Mean.lean`); `N₁(F) ≤ π N`, `N = oldN1 T`
   (`Moment.lean`);
2. the receiver `chartY ε⁻¹ (s, q, η) = ε⁻¹ x_obs` with `|x_obs'| = s^{-1/2} ≥ ρ_i = √ν >
   ρ_o = √(5ν/6)`, `ρ_i/(ρ_i - ρ_o) ≤ 12`, and `D_yX₀` through `D_yW_μ`, `D_yW_{μ+1}`
   (`Deriv.lean`);
3. the periodic phase majorant controls `cellL2` (`Transfer.lean`); uniformity in
   `μ = μ_n(z) ∈ (0, 1/4)` through the compact set `K = [0, 2] ⊂ ℂ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace PhasePrim

/-- The compact set of the two Floquet parameters `μ, μ + 1`, `μ ∈ [0, 1]`. -/
def Kmu : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc 0 2

theorem Kmu_compact : IsCompact Kmu := isCompact_Icc.image Complex.continuous_ofReal

theorem Kmu_re : ∀ μ ∈ Kmu, -(1 / 4) < μ.re := by
  rintro μ ⟨x, hx, rfl⟩
  simp only [Complex.ofReal_re]
  linarith [hx.1]

theorem gap_le (ν : ℝ) (hν : 0 < ν) :
    Real.sqrt (5 * ν / 6) ≤ 11 / 12 * Real.sqrt ν := by
  have h : 11 / 12 * Real.sqrt ν = Real.sqrt ((11 / 12 * Real.sqrt ν) ^ 2) :=
    (Real.sqrt_sq (by positivity)).symm
  rw [h]
  apply Real.sqrt_le_sqrt
  rw [mul_pow, Real.sq_sqrt hν.le]
  nlinarith

/-- The polynomial of the leaf is at most `16 ν⁻²` on the young receivers. -/
theorem poly_le (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) :
    1 + ν⁻¹ + cOf ν + (Real.sqrt ν)⁻¹ +
        Real.sqrt ν * (Real.sqrt ν - Real.sqrt (5 * ν / 6))⁻¹ ≤ 16 * ν⁻¹ ^ 2 := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hg := gap_le ν hν
  have hd : 0 < Real.sqrt ν - Real.sqrt (5 * ν / 6) := by linarith
  have h1 : Real.sqrt ν * (Real.sqrt ν - Real.sqrt (5 * ν / 6))⁻¹ ≤ 12 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hd]
    linarith
  have hνi : 1 ≤ ν⁻¹ := one_le_inv_iff₀.2 ⟨hν, hν1⟩
  have h2 : ν⁻¹ ≤ ν⁻¹ ^ 2 := by nlinarith
  have hsν : ν ≤ Real.sqrt ν := by
    have := Real.sqrt_le_sqrt (mul_le_of_le_one_left hν.le hν1 : ν * ν ≤ ν)
    rwa [Real.sqrt_mul_self hν.le] at this
  have h3 : (Real.sqrt ν)⁻¹ ≤ ν⁻¹ := inv_anti₀ hν hsν
  have hc : cOf ν = ν⁻¹ ^ 2 := by unfold cOf; rw [inv_pow]
  rw [hc]
  nlinarith

theorem rpow_neg_five (s : ℝ) (hs : 0 < s) : ((Real.sqrt s)⁻¹) ^ (-5 : ℝ) = s ^ (5 / 2 : ℝ) := by
  have h0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have h5 : Real.sqrt s ^ (5 : ℝ) = Real.sqrt s ^ (5 : ℕ) := by
    exact_mod_cast Real.rpow_natCast (Real.sqrt s) 5
  rw [Real.rpow_neg (inv_nonneg.2 h0), Real.inv_rpow h0, inv_inv, h5,
    GeomXAsm.sqrt_pow_five hs.le]

theorem ltauAt_two_mul (P : ℝ) {g h : ℝ → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h) :
    IIIa.ltauAt P (fun τ => 2 * (g τ + h τ)) ≤ 2 * (IIIa.ltauAt P g + IIIa.ltauAt P h) := by
  have e : (fun τ => 2 * (g τ + h τ)) = fun τ => (g τ + h τ) + (g τ + h τ) := by
    funext τ; rw [two_mul]
  rw [e, two_mul]
  refine le_trans (IIIa.ltauAt_add_le P (hg.add hh) (hg.add hh)) ?_
  exact add_le_add (IIIa.ltauAt_add_le P hg hh) (IIIa.ltauAt_add_le P hg hh)

/-- **The regime form** of the reduction: one constant for every regime with `ν, ε ≤ 1` and
`μ ∈ [0, 1]`. -/
theorem phasePrimitiveAt_uniform (hLeaf : SepOscFar) : ∃ (C : ℝ) (k : ℕ),
    ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ), 0 ≤ μ → μ ≤ 1 →
      L.ν ≤ 1 → L.ε ≤ 1 → 0 < K.C0 → 3 / 2 < K.mZ → ZRegularAt Pl K L μ →
        PhasePrimitiveAt Pl K L μ C k := by
  obtain ⟨C, k, hC, hlf⟩ := hLeaf Kmu Kmu_compact Kmu_re
  refine ⟨4 * Real.pi * (C + 1) * 16 ^ k, 2 * k, ?_⟩
  intro Pl K L μ hμ0 hμ1 hν1 hε1 hC0 hmZ hZR T s hs η
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hs0 : 0 < s := hs.1
  have hνs : L.ν * s ≤ 1 := by
    have := hs.2
    rw [le_div_iff₀ hν] at this
    linarith
  -- the receiver
  set y : Space := NearInst.chartY L.ε⁻¹ (s, (0, η)) with hy
  have hyq : ∀ q, NearInst.chartY L.ε⁻¹ (s, (q, η)) = y := fun q => rfl
  have hϱy : ϱ y = L.ε⁻¹ / Real.sqrt s := by
    rw [hy, GeomXAsm.chartY_eq_hpt, GeomXAsm.ϱ_hpt (by positivity)]
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hclear : y ∈ clearSet L.ε L.ν := by
    rw [hy, GeomXAsm.chartY_eq_hpt]
    refine GeomXAsm.hpt_mem_clearSet (by positivity) ?_ _
    rw [mul_div_assoc', mul_inv_cancel₀ hε.ne', div_pow, one_pow, Real.sq_sqrt hs0.le]
    rw [div_lt_div_iff₀ (by norm_num) hs0]
    nlinarith
  -- measurability
  have hmeasA : AEMeasurable (fun q : ℝ => dPhase Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
      (NearInst.chartY L.ε⁻¹ (s, (q, η)))) (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) := by
    have hm := GeomXAsm.DPhaseMeasAux.dPhase_measurable Pl K L μ hZR T
    have hq : Measurable fun q : ℝ => (NearInst.chartTau L.ε⁻¹ (s, (q, η)), y) :=
      (GeomXAsm.continuous_chartTau_q L.ε⁻¹ s η).measurable.prodMk measurable_const
    have e : (fun q : ℝ => dPhase Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) = (fun p : ℝ × Space =>
          (clearSet L.ε L.ν).indicator (fun y => dPhase Pl K L μ T p.1 y) p.2) ∘
          (fun q : ℝ => (NearInst.chartTau L.ε⁻¹ (s, (q, η)), y)) := by
      funext q
      simp only [Function.comp_apply, hyq, Set.indicator_of_mem hclear]
    rw [e]
    exact (hm.comp hq).aemeasurable
  refine ⟨hmeasA, ?_⟩
  -- the bound
  set N := oldN1 Pl K L T with hN
  have hcoef : 0 < 4 * Real.pi * (C + 1) * 16 ^ k * L.ν⁻¹ ^ (2 * k) *
      (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
    have := Real.pi_pos
    have : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
    positivity
  by_cases hNtop : N = ⊤
  · rw [hNtop, ENNReal.mul_top (by simpa using hcoef)]
    exact le_top
  -- the old thin source and its standing properties
  set g := thinG Pl K L T with hgdef
  have hρb : 0 < L.ρb Pl K := ZRegAux.rho_b_pos' Pl K L hC0
  have hgm : Measurable g := by
    rw [hgdef]
    unfold thinG
    exact (Lp.stronglyMeasurable _).measurable.add (Lp.stronglyMeasurable _).measurable
  have hmom : ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) < ⊤ :=
    strChartL2 (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν hρb (by linarith) hν _
  have hz : ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), L.ν * p.1 ≤ 6 / 5 → g p = 0 :=
    ZRegAux.strSum_zero_young _ _ _ _ _ K.hχo hρb _
  have hz' := ZRegAux.mean_ae_zero (cOf L.ν) (-1 / 2) L.ν hc g hgm hz
  -- the thin source
  set F := cutLift (cOf L.ν) (Real.sqrt (5 * L.ν / 6)) g with hF
  have hFm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j :=
    cutLift_measurable _ _ g hgm
  have hFp : ∀ x' Y q, F x' Y (q + cOf L.ν) = F x' Y q :=
    cutLift_periodic _ _ hc.ne' g
  have hFs : ∀ x' Y q, Real.sqrt (5 * L.ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) →
      F x' Y q = 0 := fun x' Y q h => cutLift_support _ _ g x' Y q h
  have hFN : IIIa.thinMoment (cOf L.ν) F ≤ ENNReal.ofReal Real.pi * N := by
    have := thinMoment_cutLift_le (cOf L.ν) (Real.sqrt (5 * L.ν / 6)) hc g hgm
    rwa [firstMoment_thinG Pl K L hC0 T] at this
  have hFfin : IIIa.thinMoment (cOf L.ν) F ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hNtop) hFN
  -- the observation point
  set xo : Space := L.ε • y with hxo
  have hxo' : L.ε⁻¹ • xo = y := by
    rw [hxo, smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
  have hxr : Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) = (Real.sqrt s)⁻¹ := by
    have h0 : xo 0 = (Real.sqrt s)⁻¹ := by
      rw [hxo, hy, GeomXAsm.chartY_eq_hpt]
      show L.ε * (L.ε⁻¹ / Real.sqrt s) = _
      field_simp
    have h1 : xo 1 = 0 := by
      rw [hxo, hy, GeomXAsm.chartY_eq_hpt]
      show L.ε * 0 = _
      ring
    rw [h0, h1, show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq (by positivity)]
  have hρ : Real.sqrt (5 * L.ν / 6) < Real.sqrt L.ν :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hρi : Real.sqrt L.ν ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) := by
    rw [hxr, le_inv_comm₀ (Real.sqrt_pos.2 hν) hss, ← Real.sqrt_inv]
    apply Real.sqrt_le_sqrt
    exact hs.2.trans (le_of_eq (one_div _))
  -- the two leaf applications
  have hμK : ((μ : ℝ) : ℂ) ∈ Kmu := ⟨μ, ⟨hμ0, by linarith⟩, rfl⟩
  have hμ1K : ((μ : ℂ) + 1) ∈ Kmu := ⟨μ + 1, ⟨by linarith, by linarith⟩, by push_cast; rfl⟩
  obtain ⟨B₁, hB₁m, hB₁p, hB₁ae, hB₁le⟩ := hlf L.ν (cOf L.ν) L.ε (Real.sqrt (5 * L.ν / 6))
    (Real.sqrt L.ν) hν hν1 hc hε hε1 (Real.sqrt_nonneg _) hρ (μ : ℂ) hμK F hFm hFp hFs hFfin xo hρi
  obtain ⟨B₂, hB₂m, hB₂p, hB₂ae, hB₂le⟩ := hlf L.ν (cOf L.ν) L.ε (Real.sqrt (5 * L.ν / 6))
    (Real.sqrt L.ν) hν hν1 hc hε hε1 (Real.sqrt_nonneg _) hρ ((μ : ℂ) + 1) hμ1K F hFm hFp hFs
    hFfin xo hρi
  -- the responses of the thin sources are those of the old sources
  have eA : ∀ (μc : ℂ) τ, (fun y => IIIa.sepW L.ν μc (IIIa.thinSource L.ε F) y τ) =
      fun y => IIIa.sepW L.ν μc (oldPhys L.ε⁻¹ (cOf L.ν) g) y τ := fun μc τ =>
    funext fun y => sepW_cut (cOf L.ν) L.ν L.ε μc hc hν hε g hz y τ
  have eM : ∀ (μc : ℂ) τ, (fun y => IIIa.sepW L.ν μc
      (IIIa.thinSource L.ε (IIIa.meanLift (IIIa.phaseMean (cOf L.ν) F))) y τ) =
      fun y => IIIa.sepW L.ν μc (oldPhys L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) g)) y τ :=
    fun μc τ => funext fun y => sepW_mean (cOf L.ν) L.ν L.ε μc hc hν hε g hgm hmom hz' y τ
  -- differentiability at the receiver
  have hyr : L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) < ϱ y := by
    rw [hϱy, show L.ε⁻¹ / Real.sqrt s = L.ε⁻¹ * (Real.sqrt s)⁻¹ from div_eq_mul_inv _ _]
    apply mul_lt_mul_of_pos_left _ (inv_pos.2 hε)
    rw [← Real.sqrt_inv]
    apply Real.sqrt_lt_sqrt (by positivity)
    rw [← one_div, lt_div_iff₀ hs0]
    nlinarith
  have hmean_m := ZRegAux.measurable_meanQ' (cOf L.ν) hgm
  have hmean_mom : ∫⁻ p, ‖meanQ (cOf L.ν) g p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) < ⊤ :=
    lt_of_le_of_lt (ZRegAux.mean_moment_le _ _ hc _ hgm) hmom
  have hreμ : -(1 / 4) < ((μ : ℝ) : ℂ).re := by simp; linarith
  have hreμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hdiff := fun τ => dX0_le L.ν μ L.ε⁻¹ (cOf L.ν) g (meanQ (cOf L.ν) g) τ y
    (sepW_diff (cOf L.ν) L.ν L.ε _ hc hν hε hreμ g hgm hmom hz τ y hyr)
    (sepW_diff (cOf L.ν) L.ν L.ε _ hc hν hε hreμ1 g hgm hmom hz τ y hyr)
    (sepW_diff (cOf L.ν) L.ν L.ε _ hc hν hε hreμ _ hmean_m hmean_mom hz' τ y hyr)
    (sepW_diff (cOf L.ν) L.ν L.ε _ hc hν hε hreμ1 _ hmean_m hmean_mom hz' τ y hyr)
  -- the pointwise majorant
  have hmaj : ∀ᵐ τ ∂(volume : Measure ℝ),
      ENNReal.ofReal (dPhase Pl K L μ T τ (NearInst.chartY L.ε⁻¹ (s, (0, η)))) ≤
        2 * (B₁ τ + B₂ τ) := by
    filter_upwards [hB₁ae, hB₂ae] with τ h1 h2
    rw [hxo', eA, eM] at h1 h2
    have hd := hdiff τ
    have e : dPhase Pl K L μ T τ (NearInst.chartY L.ε⁻¹ (s, (0, η))) =
        ‖fderiv ℝ (wardX0 L.ν μ L.ε⁻¹ (cOf L.ν) g τ) y -
          fderiv ℝ (wardX0 L.ν μ L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) g) τ) y‖ := rfl
    rw [e]
    calc ENNReal.ofReal ‖fderiv ℝ (wardX0 L.ν μ L.ε⁻¹ (cOf L.ν) g τ) y -
          fderiv ℝ (wardX0 L.ν μ L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) g) τ) y‖
        ≤ ENNReal.ofReal (2 * (‖fderiv ℝ (fun y => IIIa.sepW L.ν (μ : ℂ)
              (oldPhys L.ε⁻¹ (cOf L.ν) g) y τ) y - fderiv ℝ (fun y => IIIa.sepW L.ν (μ : ℂ)
              (oldPhys L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) g)) y τ) y‖ +
            ‖fderiv ℝ (fun y => IIIa.sepW L.ν ((μ : ℂ) + 1)
              (oldPhys L.ε⁻¹ (cOf L.ν) g) y τ) y - fderiv ℝ (fun y => IIIa.sepW L.ν ((μ : ℂ) + 1)
              (oldPhys L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) g)) y τ) y‖)) :=
          ENNReal.ofReal_le_ofReal hd
      _ = 2 * (‖fderiv ℝ (fun y => IIIa.sepW L.ν (μ : ℂ)
              (oldPhys L.ε⁻¹ (cOf L.ν) g) y τ) y - fderiv ℝ (fun y => IIIa.sepW L.ν (μ : ℂ)
              (oldPhys L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) g)) y τ) y‖ₑ +
            ‖fderiv ℝ (fun y => IIIa.sepW L.ν ((μ : ℂ) + 1)
              (oldPhys L.ε⁻¹ (cOf L.ν) g) y τ) y - fderiv ℝ (fun y => IIIa.sepW L.ν ((μ : ℂ) + 1)
              (oldPhys L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) g)) y τ) y‖ₑ) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
            ofReal_norm, ofReal_norm]
          norm_num
      _ ≤ 2 * (B₁ τ + B₂ τ) := by gcongr
  have hcell := cellL2_le L.ε (cOf L.ν) hε hc (dPhase Pl K L μ T) s η
    (fun τ => 2 * (B₁ τ + B₂ τ)) ((hB₁m.add hB₂m).const_mul 2)
    (fun τ => by simp only [hB₁p τ, hB₂p τ]) hmaj
  -- the constants
  set M := 1 + L.ν⁻¹ + cOf L.ν + (Real.sqrt L.ν)⁻¹ +
    Real.sqrt L.ν * (Real.sqrt L.ν - Real.sqrt (5 * L.ν / 6))⁻¹ with hM
  have hM0 : 0 ≤ M := by
    have hd : 0 < Real.sqrt L.ν - Real.sqrt (5 * L.ν / 6) := by linarith
    have := hc.le
    positivity
  have hMle : M ^ k ≤ 16 ^ k * L.ν⁻¹ ^ (2 * k) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ hM0 (by have := poly_le L.ν hν hν1; rw [← hM] at this; linarith) k
  have hrad : Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ) = s ^ (5 / 2 : ℝ) := by
    rw [hxr, rpow_neg_five s hs0]
  set a := C * M ^ k * L.ε ^ 4 * s ^ (5 / 2 : ℝ) with ha
  have ha0 : 0 ≤ a := by
    have : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
    rw [ha]
    positivity
  have hLi : ∀ B : ℝ → ℝ≥0∞, IIIa.ltauAt (2 * L.ε * cOf L.ν) B ≤
      ENNReal.ofReal (C * M ^ k * L.ε ^ 4 *
        Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ)) * IIIa.thinMoment (cOf L.ν) F →
      IIIa.ltauAt (2 * L.ε * cOf L.ν) B ≤ ENNReal.ofReal (a * Real.pi) * N := by
    intro B hB
    refine hB.trans ?_
    rw [hrad, ← ha, ENNReal.ofReal_mul ha0, mul_assoc]
    exact mul_le_mul_right hFN _
  have ha_le : a * Real.pi * 4 ≤ 4 * Real.pi * (C + 1) * 16 ^ k * L.ν⁻¹ ^ (2 * k) *
      (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
    have hs52 : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
    have hpi := Real.pi_pos
    have h1 : C * M ^ k ≤ (C + 1) * (16 ^ k * L.ν⁻¹ ^ (2 * k)) :=
      mul_le_mul (by linarith) hMle (pow_nonneg hM0 _) (by linarith)
    have h2 : 0 ≤ L.ε ^ 4 * s ^ (5 / 2 : ℝ) := by positivity
    calc a * Real.pi * 4 = 4 * Real.pi * (C * M ^ k) * (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
          rw [ha]; ring
      _ ≤ 4 * Real.pi * ((C + 1) * (16 ^ k * L.ν⁻¹ ^ (2 * k))) * (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
          gcongr
      _ = _ := by ring
  calc cellL2 L.ε⁻¹ (cOf L.ν) (dPhase Pl K L μ T) s η
      ≤ IIIa.ltauAt (2 * L.ε * cOf L.ν) (fun τ => 2 * (B₁ τ + B₂ τ)) := hcell
    _ ≤ 2 * (IIIa.ltauAt (2 * L.ε * cOf L.ν) B₁ + IIIa.ltauAt (2 * L.ε * cOf L.ν) B₂) :=
        ltauAt_two_mul _ hB₁m hB₂m
    _ ≤ 2 * (ENNReal.ofReal (a * Real.pi) * N + ENNReal.ofReal (a * Real.pi) * N) := by
        gcongr
        · exact hLi B₁ hB₁le
        · exact hLi B₂ hB₂le
    _ = ENNReal.ofReal (a * Real.pi * 4) * N := by
        rw [← two_mul, ← mul_assoc, ← mul_assoc,
          ENNReal.ofReal_mul (mul_nonneg ha0 Real.pi_pos.le)]
        congr 1
        rw [mul_comm, ← mul_assoc]
        norm_num
        ring
    _ ≤ ENNReal.ofReal (4 * Real.pi * (C + 1) * 16 ^ k * L.ν⁻¹ ^ (2 * k) *
          (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * N := by
        gcongr

end PhasePrim

open PhasePrim in
/-- **`phasePrimitive` from the far-field oscillation leaf** (source 5400-5427). -/
theorem phasePrimitive_of (hLeaf : SepOscFar) (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) : D.PhasePrimitive := by
  obtain ⟨C, k, h⟩ := phasePrimitiveAt_uniform hLeaf
  refine ⟨C, k, ?_⟩
  filter_upwards [D.eventually_lHyp hst.omega_ne hst.gamma_pos hst.sigma_pos hst.sigma_lt
    hst.chiY, retNu_retEps_eventually_le_one (σ₀ := D.σ₀) hst.omega_ne hst.gamma_pos D.coeff_ne,
    zRegular D hst] with n hL hνε hZ z hz
  have hLz := hL z hz
  exact h D.Pl D.K (D.level n) (D.mu n z) hLz.mu_pos.le (by linarith [hLz.mu_lt]) hνε.1 hνε.2
    hst.C0_pos hst.mZ_gt (hZ z hz)

theorem phasePrimitive (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.PhasePrimitive :=
  phasePrimitive_of sepOscFar D hst

end UnforcedLeray.Short.PartIIIb.Concrete
