import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1

/-!
# `T0gMem`: the dilated heat flow of a continuous band-supported periodic section is in `L²`

Source `the November 2 reference manuscript`
1640-1656. Helpers are prefixed `t0gMem_`.

Argument: with `F(s,q,η) = G(e^t s, q, η)` (continuous, `c`-periodic in `q`, supported in the box
`e^t s ∈ [s0, s1]`, `|η| ≤ L`), the planar heat flow at the age-dependent time `θ(s)` is the fibre
heat `H_θ F` of `B0224` (`fiberHeat`). Its `L²(measureH c)` norm is at most that of `F`
(`eLpNorm_fiberHeat_le`, the contraction property), and `F` lies in `L²(measureH c)` because on the
cell `s^{-3/2}` is bounded on the band `s ≥ s0 e^{-t}` and `G` is bounded on a compact box.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile QPeriodic)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0226 (ProfileTest IsProfileTest)

/-- Continuity of `(s, q, η) ↦ G(e^t s, q, η)`. -/
theorem t0gMem_cont {E : Type*} [NormedAddCommGroup E] {t : ℝ} {G : Profile → E}
    (hG : Continuous G) : Continuous fun p : Profile => G (Real.exp t * p.1, p.2) :=
  hG.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)

/-- The `L²(measureH c)` membership of `F(s,q,η) = G(e^t s, q, η)` for a continuous `G` supported in
`e^t s ∈ [s0, s1]`, `|η| ≤ L`, with `s0 > 0`. -/
theorem t0gMem_L2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c t : ℝ}
    {G : Profile → E} (hG : Continuous G) {s0 s1 L : ℝ} (hs0 : 0 < s0)
    (hsupp : ∀ p : Profile, G p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) :
    MemLp (fun p : Profile => G (Real.exp t * p.1, p.2)) 2 (measureH c) := by
  have hexp : 0 < Real.exp t := Real.exp_pos t
  set F : Profile → E := fun p => G (Real.exp t * p.1, p.2) with hFdef
  have hF : Continuous F := t0gMem_cont hG
  set a : ℝ := s0 / Real.exp t with ha_def
  set b : ℝ := s1 / Real.exp t with hb_def
  have ha : 0 < a := div_pos hs0 hexp
  set K0 : Set Profile := Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L) with hK0
  set B : Set Profile := Icc a b ×ˢ (Icc 0 c ×ˢ Icc (-L) L) with hB
  have hK0c : IsCompact K0 := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hBc : IsCompact B := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C, hC⟩ := hK0c.exists_bound_of_continuousOn hG.continuousOn
  set K : ENNReal := ENNReal.ofReal (a ^ (-(3 / 2 : ℝ))) * ENNReal.ofReal C ^ 2 with hKdef
  have hbound : ∀ p ∈ UnforcedLeray.B0220.cell c,
      ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * ‖F p‖ₑ ^ 2 ≤ B.indicator (fun _ => K) p := by
    intro p hp
    by_cases hFp : F p = 0
    · simp [hFp]
    · have hmem1 : s0 ≤ Real.exp t * p.1 ∧ Real.exp t * p.1 ≤ s1 := by
        have := hsupp (Real.exp t * p.1, p.2) hFp
        exact this.1
      have hmem2 : |p.2.2| ≤ L := (hsupp (Real.exp t * p.1, p.2) hFp).2
      have hq : p.2.1 ∈ Icc 0 c := Ioc_subset_Icc_self hp.2.1
      have hpa : a ≤ p.1 := by
        rw [ha_def, div_le_iff₀ hexp, mul_comm]
        exact hmem1.1
      have hpb : p.1 ≤ b := by
        rw [hb_def, le_div_iff₀ hexp, mul_comm]
        exact hmem1.2
      have hpB : p ∈ B := by
        refine ⟨⟨hpa, hpb⟩, hq, ?_⟩
        exact abs_le.1 hmem2
      rw [Set.indicator_of_mem hpB]
      have hw : ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) ≤ ENNReal.ofReal (a ^ (-(3 / 2 : ℝ))) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos ha hpa (by norm_num))
      have hn : ‖F p‖ₑ ≤ ENNReal.ofReal C := by
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal (hC (Real.exp t * p.1, p.2) ?_)
        exact ⟨hmem1, hq, abs_le.1 hmem2⟩
      calc ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * ‖F p‖ₑ ^ 2
          ≤ ENNReal.ofReal (a ^ (-(3 / 2 : ℝ))) * ENNReal.ofReal C ^ 2 := by gcongr
        _ = K := rfl
  have hBmeas : MeasurableSet B := hBc.isClosed.measurableSet
  have hBlt : volume B < ⊤ := hBc.measure_lt_top
  have hKlt : K < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
  have hint : ∫⁻ p, ‖F p‖ₑ ^ 2 ∂(measureH c) < ⊤ := by
    rw [UnforcedLeray.B0224.lintegral_measureH_eq (fun p => ‖F p‖ₑ ^ 2) (hF.enorm.measurable.pow_const 2)]
    calc ∫⁻ p, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * ‖F p‖ₑ ^ 2 ∂(UnforcedLeray.B0220.cellMeasure c)
        ≤ ∫⁻ p in UnforcedLeray.B0220.cell c, B.indicator (fun _ => K) p :=
          setLIntegral_mono' (UnforcedLeray.B0220.measurableSet_cell c) hbound
      _ ≤ ∫⁻ p, B.indicator (fun _ => K) p := lintegral_mono' Measure.restrict_le_self le_rfl
      _ = K * volume B := lintegral_indicator_const hBmeas K
      _ < ⊤ := ENNReal.mul_lt_top hKlt hBlt
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  rw [UnforcedLeray.B0224.eLpNorm_two_eq]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hint.ne

theorem t0gMem_proof : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gMem := by
  unfold T0gMem
  intro c ν t hc E _ _ _ G hG hper hsupp
  obtain ⟨s0, s1, L, hs0, hsupp'⟩ := hsupp
  have hL2 := t0gMem_L2 (c := c) (t := t) hG hs0 hsupp'
  have hF'' : QPeriodic c (fun p : Profile => G (Real.exp t * p.1, p.2)) := by
    intro p
    exact hper (Real.exp t * p.1, p.2)
  have hFsm : StronglyMeasurable (fun p : Profile => G (Real.exp t * p.1, p.2)) :=
    (t0gMem_cont (t := t) hG).stronglyMeasurable
  have hθm : Measurable (fun s : ℝ => ν * s * (Real.exp t - 1)) := by fun_prop
  have hfh : MemLp (UnforcedLeray.B0224.fiberHeat c (fun s : ℝ => ν * s * (Real.exp t - 1))
      (fun p : Profile => G (Real.exp t * p.1, p.2))) 2 (measureH c) := by
    refine ⟨(UnforcedLeray.B0224.stronglyMeasurable_fiberHeat hθm hFsm).aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (UnforcedLeray.B0224.eLpNorm_fiberHeat_le hc hθm hFsm) hL2.eLpNorm_lt_top
  have hsm : MemLp (fun p : Profile => Real.exp (-t / 2) • UnforcedLeray.B0224.fiberHeat c
      (fun s : ℝ => ν * s * (Real.exp t - 1)) (fun p : Profile => G (Real.exp t * p.1, p.2)) p)
      2 (measureH c) := hfh.const_smul (Real.exp (-t / 2))
  have hfun : (fun p : Profile => Real.exp (-t / 2) • UnforcedLeray.B0224.planeHeat
      (ν * p.1 * (Real.exp t - 1)) (fun z => G (Real.exp t * p.1, z)) p.2) =
      fun p : Profile => Real.exp (-t / 2) • UnforcedLeray.B0224.fiberHeat c
        (fun s : ℝ => ν * s * (Real.exp t - 1)) (fun p : Profile => G (Real.exp t * p.1, p.2)) p := by
    funext p
    unfold UnforcedLeray.B0224.fiberHeat
    rw [UnforcedLeray.B0220.periodize_of_periodic _ hF'']
  rw [hfun]
  exact hsm

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
