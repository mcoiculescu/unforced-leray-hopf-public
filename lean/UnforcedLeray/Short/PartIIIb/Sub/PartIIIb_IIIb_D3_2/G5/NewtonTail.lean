import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_6_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Kflat
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.AMuInAff
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ret_1_closure

/-!
# Transition and tail regime `s ≥ 4 / (5ν)` for `NewtonTaylor` (`PartIII-b:IIIb-D3/2/G5/2/org`)

Source of record: `the November 2 reference manuscript`, lines 4894-4901 and
4917-4937.  On `s ≥ 4 / (5ν)`, the weight `e^{-a_s s} ≤ e^{-4a_s/(5ν)}` absorbs both `𝓛M(s)`
(via `jetEps1W` and `lptScale`) and `ℓ_μ(M) a_μ(s)` (via `|ℓ_μ(M)| ≤ (1/4) ε³ N₀^χ(M)` and
`sDerivIter_aMuFun`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5

open ConcreteYF

/-- `cellInt c F` equals the integral of `F` with respect to `Cyl.avgμ c` (`Ioo` and `Ico` have
the same Lebesgue restriction). -/
theorem cellInt_eq_integral_avgμ {c : ℝ} (hc : 0 ≤ c) (F : ℝ × ℝ → ℝ) :
    cellInt c F = ∫ z, F z ∂(Cyl.avgμ c) := by
  rw [Cyl.integral_avgμ hc, smul_eq_mul, cellInt]
  congr 1
  rw [Cyl.volume_restrict_cell, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ, Measure.restrict_congr_set Ioo_ae_eq_Ico]

/-- Pointwise bound `|2 A_{zz} - A_{rr}| ≤ 3 |A|_F`. -/
theorem abs_two_zz_sub_rr_le (A : Mat3) :
    |2 * A 2 2 - A 0 0| ≤ 3 * frob A := by
  have h22 : |A 2 2| ≤ frob A := NewtonVGeom.abs_le_frob A 2 2
  have h00 : |A 0 0| ≤ frob A := NewtonVGeom.abs_le_frob A 0 0
  have h1 : |2 * A 2 2 - A 0 0| ≤ |2 * A 2 2| + |A 0 0| := abs_sub _ _
  rw [abs_mul, abs_two] at h1
  linarith

/-- For an `OldThinFinite` tensor `M`, the slice `y ↦ frob (M (u, y))` is integrable on the cell
for a.e. `u > 6 / (5ν)`. -/
theorem ae_integrable_frob_slice {c ν : ℝ} (hν : 0 < ν) {M : Chart → Mat3}
    (hM : OldThinFinite c ν M) :
    ∀ᵐ u ∂(volume.restrict (Ioi (6 / 5 / ν))),
      Integrable (fun y => frob (M (u, y))) (Cyl.avgμ c) := by
  have ha : (0 : ℝ) < 6 / 5 / ν := div_pos (by norm_num) hν
  filter_upwards [hM.2.prod_right_ae, ae_restrict_mem measurableSet_Ioi] with u hu hu_mem
  have hu0 : 0 < u := ha.trans hu_mem
  have h1 := hu.const_mul (u ^ (3 / 2 : ℝ))
  refine h1.congr (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [← mul_assoc, ← Real.rpow_add hu0]
  norm_num

/-- Bound on the outer integral in `ellMuGen`: `|I_T(M)| ≤ 3 N₀^χ(M)`. -/
theorem abs_it_integral_le {c ν : ℝ} {χo : ℝ → ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) {M : Chart → Mat3} (hM : OldThinFinite c ν M) :
    |∫ s in Ioi (0 : ℝ), χo (ν * s) * s ^ (-(3 / 2 : ℝ)) *
        cellInt c (fun p => 2 * M (s, p) 2 2 - M (s, p) 0 0)| ≤
      3 * oldN0w c ν χo M := by
  have ha : (0 : ℝ) < 6 / 5 / ν := div_pos (by norm_num) hν
  set f : ℝ → ℝ := fun s => χo (ν * s) * s ^ (-(3 / 2 : ℝ)) *
    cellInt c (fun p => 2 * M (s, p) 2 2 - M (s, p) 0 0) with hf_def
  have hind : ∀ s ∈ Ioi (0 : ℝ), (Ioi (6 / 5 / ν)).indicator f s = f s := by
    intro s _
    by_cases hs : s ∈ Ioi (6 / 5 / ν)
    · exact Set.indicator_of_mem hs _
    · rw [Set.indicator_of_notMem hs]
      have hsle : s ≤ 6 / 5 / ν := not_lt.1 hs
      have hνs : ν * s ≤ 6 / 5 := by
        calc ν * s ≤ ν * (6 / 5 / ν) := mul_le_mul_of_nonneg_left hsle hν.le
          _ = 6 / 5 := by field_simp
      simp [hf_def, hχ.zero _ hνs]
  have hIeq : ∫ s in Ioi (0 : ℝ), f s = ∫ s in Ioi (6 / 5 / ν), f s := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hind,
      integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      Set.Ioi_inter_Ioi, sup_eq_left.2 ha.le]
  rw [hIeq, ← Real.norm_eq_abs]
  have hmaj : Integrable (fun u : ℝ =>
      3 * (u ^ (-(3 / 2 : ℝ)) * (χo (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))))
      (volume.restrict (Ioi (6 / 5 / ν))) :=
    (w_int hν hχ M hM).const_mul 3
  have hle : ∀ᵐ u ∂(volume.restrict (Ioi (6 / 5 / ν))),
      ‖f u‖ ≤ 3 * (u ^ (-(3 / 2 : ℝ)) * (χo (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))) := by
    filter_upwards [ae_integrable_frob_slice hν hM, ae_restrict_mem measurableSet_Ioi]
      with u hu hu_mem
    have hu0 : 0 < u := ha.trans hu_mem
    have hcell : |cellInt c (fun p => 2 * M (u, p) 2 2 - M (u, p) 0 0)| ≤
        3 * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c) := by
      rw [cellInt_eq_integral_avgμ hc.le, ← Real.norm_eq_abs, ← integral_const_mul]
      refine norm_integral_le_of_norm_le (hu.const_mul 3) (Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs]
      exact abs_two_zz_sub_rr_le (M (u, p))
    have hχ0 : 0 ≤ χo (ν * u) := (hχ.range _).1
    have hr0 : 0 ≤ u ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hu0.le _
    rw [Real.norm_eq_abs, hf_def, abs_mul, abs_mul, abs_of_nonneg hχ0, abs_of_nonneg hr0]
    calc χo (ν * u) * u ^ (-(3 / 2 : ℝ)) *
          |cellInt c (fun p => 2 * M (u, p) 2 2 - M (u, p) 0 0)|
        ≤ χo (ν * u) * u ^ (-(3 / 2 : ℝ)) * (3 * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)) :=
          mul_le_mul_of_nonneg_left hcell (mul_nonneg hχ0 hr0)
      _ = 3 * (u ^ (-(3 / 2 : ℝ)) * (χo (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))) := by ring
  calc ‖∫ s in Ioi (6 / 5 / ν), f s‖
      ≤ ∫ u in Ioi (6 / 5 / ν),
          3 * (u ^ (-(3 / 2 : ℝ)) * (χo (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))) :=
        norm_integral_le_of_norm_le hmaj hle
    _ = 3 * oldN0w c ν χo M := by
        unfold oldN0w
        exact integral_const_mul 3 _

/-- Bound on `|ellMuGen|`: for `0 < μ`, `|ℓ_μ(M)| ≤ (1/4) ε³ N₀^χ(M)`. -/
theorem abs_ellMuGen_le {c ν ε μ : ℝ} {χo χy : ℝ → ℝ} (h : LHyp c ν ε μ χo χy)
    {M : Chart → Mat3} (hM : OldThinFinite c ν M) :
    |ellMuGen c ν ε μ χo M| ≤ (1 / 4 : ℝ) * ε ^ 3 * oldN0w c ν χo M := by
  have hε3 : 0 ≤ ε ^ 3 := pow_nonneg h.eps_pos.le 3
  have hμden : 12 ≤ 8 * (μ + 3 / 2) := by linarith [h.mu_pos]
  have hμpos : 0 < 8 * (μ + 3 / 2) := by linarith [h.mu_pos]
  have hN0 : 0 ≤ oldN0w c ν χo M := rj6_oldN0w_nonneg c ν h.nu_pos h.chiO M
  have hI := abs_it_integral_le h.c_pos h.nu_pos h.chiO hM
  unfold ellMuGen
  rw [abs_div, abs_mul, abs_of_nonneg hε3, abs_of_pos hμpos]
  calc ε ^ 3 * |∫ s in Ioi (0 : ℝ), χo (ν * s) * s ^ (-(3 / 2 : ℝ)) *
          cellInt c (fun p => 2 * M (s, p) 2 2 - M (s, p) 0 0)| / (8 * (μ + 3 / 2))
      ≤ ε ^ 3 * (3 * oldN0w c ν χo M) / (8 * (μ + 3 / 2)) := by gcongr
    _ ≤ ε ^ 3 * (3 * oldN0w c ν χo M) / 12 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hμden
    _ = (1 / 4 : ℝ) * ε ^ 3 * oldN0w c ν χo M := by ring

/-- On `s ≥ 4 / (5ν)` with `0 < as`, `e^{-as s} ≤ e^{-(4 as / 5) / ν}`. -/
theorem exp_le_of_ge_four_fifths {as ν s : ℝ} (has : 0 < as) (_hν : 0 < ν)
    (hs : 4 / (5 * ν) ≤ s) :
    Real.exp (-as * s) ≤ Real.exp (-(4 * as / 5) / ν) := by
  apply Real.exp_le_exp.2
  have h1 : 4 * as / (5 * ν) ≤ as * s := by
    calc 4 * as / (5 * ν) = as * (4 / (5 * ν)) := by ring
      _ ≤ as * s := mul_le_mul_of_nonneg_left hs has.le
  have h2 : -(4 * as / 5) / ν = -(4 * as / (5 * ν)) := by ring
  linarith

/-- On `s ≥ 4 / (5ν)`, `affTerm as 6 (aMuFun μ) s ≤ C_a e^{-(4 as / 5) / ν}`. -/
theorem affTerm_aMuFun_tail {as ν μ s : ℝ} (has : 0 < as) (hν : 0 < ν) (hμ : 0 < μ)
    (hs : 4 / (5 * ν) ≤ s) :
    affTerm as 6 (aMuFun μ) s ≤
      ((∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j) * (frob (fun i j => Dzero i j) / (5 / 2))) *
        Real.exp (-(4 * as / 5) / ν) := by
  have hs0 : 0 < s := lt_of_lt_of_le (div_pos (by norm_num) (mul_pos (by norm_num) hν)) hs
  have hμ2 : 0 < μ + 5 / 2 := by linarith
  have hterm : ∀ j ∈ Finset.range 7, frob (sDerivIter j (aMuFun μ) s) =
      (5 / 2 : ℝ) ^ j * (s ^ (5 / 2 : ℝ) / (μ + 5 / 2)) * frob (fun i j => Dzero i j) := by
    intro j _
    rw [sDerivIter_aMuFun μ j s hs0, frobSmulAux,
      abs_of_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
        (div_nonneg (Real.rpow_nonneg hs0.le _) hμ2.le))]
  have hS : affSum 6 (aMuFun μ) s = (∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j) *
      (s ^ (5 / 2 : ℝ) / (μ + 5 / 2) * frob (fun i j => Dzero i j)) := by
    unfold affSum
    rw [Finset.sum_congr rfl hterm, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hq : s ^ (-(5 / 2 : ℝ)) * (s ^ (5 / 2 : ℝ) / (μ + 5 / 2) * frob (fun i j => Dzero i j))
      = frob (fun i j => Dzero i j) / (μ + 5 / 2) := by
    have hp : s ^ (5 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hs0 _).ne'
    rw [Real.rpow_neg hs0.le]
    field_simp
  have hT : affTerm as 6 (aMuFun μ) s = Real.exp (-as * s) *
      ((∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j) * (frob (fun i j => Dzero i j) / (μ + 5 / 2))) := by
    unfold affTerm
    rw [hS]
    linear_combination (Real.exp (-as * s) * (∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j)) * hq
  have hdiv : frob (fun i j => Dzero i j) / (μ + 5 / 2) ≤
      frob (fun i j => Dzero i j) / (5 / 2) :=
    div_le_div_of_nonneg_left (frob_nonneg' _) (by norm_num) (by linarith)
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j :=
    Finset.sum_nonneg fun j _ => pow_nonneg (by norm_num) _
  have hexp := exp_le_of_ge_four_fifths has hν hs
  rw [hT, mul_comm (Real.exp (-as * s))]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hdiv hsum0) hexp
    (Real.exp_pos _).le (mul_nonneg hsum0 (div_nonneg (frob_nonneg' _) (by norm_num)))

/-- **Transition and tail bound (`s ≥ 4 / (5ν)`)** (source 4894-4901, 4917-4937): on `s ≥ 4 / (5ν)`,
`affTerm as 6 (Lpt c ν ε μ χo χy M - ellMuGen c ν ε μ χo M • aMuFun μ) s` is bounded by
`C₀ ε³ e^{-(4a_s/5)/ν} N₀^χ(M)`. -/
theorem newtonTail (as : ℝ) (χo χy : ℝ → ℝ) (has : 0 < as) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (c ν ε μ : ℝ), LHyp c ν ε μ χo χy →
      ∀ M : Chart → Mat3, OldThinFinite c ν M → ∀ s : ℝ, 4 / (5 * ν) ≤ s →
        affTerm as 6 (Lpt c ν ε μ χo χy M - ellMuGen c ν ε μ χo M • aMuFun μ) s ≤
          C₀ * ε ^ 3 * Real.exp (-(4 * as / 5) / ν) * oldN0w c ν χo M := by
  obtain ⟨CJ, hCJ⟩ := jetEps1W (univ : Set ℝ) χo χy
  set Ca : ℝ := (∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j) *
    (frob (fun i j => Dzero i j) / (5 / 2)) with hCa_def
  have hCa0 : 0 ≤ Ca :=
    mul_nonneg (Finset.sum_nonneg fun j _ => pow_nonneg (by norm_num) _)
      (div_nonneg (frob_nonneg' _) (by norm_num))
  refine ⟨7 * |CJ| + (1 / 4) * Ca, by positivity, ?_⟩
  intro c ν ε μ h M hM s hs
  have hs0 : 0 < s := lt_of_lt_of_le (div_pos (by norm_num) (mul_pos (by norm_num) h.nu_pos)) hs
  have hLsm : ContDiffOn ℝ 6 (Lpt c ν ε μ χo χy M) (Ioi 0) :=
    lpt_contDiffOn_of xmtSmooth h hM
  have hAsm : ContDiffOn ℝ 6 (aMuFun μ) (Ioi 0) :=
    (aMuInAff as μ has.le h.mu_pos).smooth
  set ℓ : ℝ := ellMuGen c ν ε μ χo M with hℓ_def
  have hsub : Lpt c ν ε μ χo χy M - ℓ • aMuFun μ =
      Lpt c ν ε μ χo χy M + (-ℓ) • aMuFun μ := by
    funext t; simp [sub_eq_add_neg]
  have hadd := affTerm_add_le_aux as (Lpt c ν ε μ χo χy M) ((-ℓ) • aMuFun μ)
    hLsm (hAsm.const_smul (-ℓ)) s hs0
  have hsmul : affTerm as 6 ((-ℓ) • aMuFun μ) s = |ℓ| * affTerm as 6 (aMuFun μ) s := by
    unfold affTerm affSum
    have hsum : ∑ j ∈ Finset.range 7, frob (sDerivIter j ((-ℓ) • aMuFun μ) s) =
        |ℓ| * ∑ j ∈ Finset.range 7, frob (sDerivIter j (aMuFun μ) s) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj6 : j ≤ 6 := by have := Finset.mem_range.1 hj; omega
      rw [sdi_smul_aux (-ℓ) (aMuFun μ) hAsm j hj6 s hs0, frob_smul_aux, abs_neg]
    rw [hsum]
    ring
  -- Bound the `Lpt` term via `jetEps1W` and `lptScale`
  have hL1 : LHyp c ν 1 μ χo χy :=
    ⟨h.c_pos, h.nu_pos, h.nu_le, one_pos, h.mu_pos, h.mu_lt, h.chiO, h.chiY⟩
  have hN0 : 0 ≤ oldN0w c ν χo M := rj6_oldN0w_nonneg c ν h.nu_pos h.chiO M
  have hε3 : 0 ≤ ε ^ 3 := pow_nonneg h.eps_pos.le 3
  have hs52 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  have hLscale : Lpt c ν ε μ χo χy M = fun t => ε ^ 3 • Lpt c ν 1 μ χo χy M t :=
    funext fun t => Scale.lptScale c ν ε μ χo χy M h.eps_pos t
  have hLj : ∀ j ∈ Finset.range 7,
      frob (sDerivIter j (Lpt c ν ε μ χo χy M) s) ≤
        |CJ| * ε ^ 3 * s ^ (5 / 2 : ℝ) * oldN0w c ν χo M := by
    intro j hj
    have hj6 : j ≤ 6 := by have := Finset.mem_range.1 hj; omega
    rw [hLscale, rj6_sDerivIter_smul, rj6_frob_smul, abs_of_pos (pow_pos h.eps_pos 3)]
    have h1 := hCJ c ν μ hL1 (mem_univ μ) M hM s hs0 j hj6
    have h2 : CJ * s ^ (5 / 2 : ℝ) * oldN0w c ν χo M ≤
        |CJ| * s ^ (5 / 2 : ℝ) * oldN0w c ν χo M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self CJ) hs52) hN0
    calc ε ^ 3 * frob (sDerivIter j (Lpt c ν 1 μ χo χy M) s)
        ≤ ε ^ 3 * (|CJ| * s ^ (5 / 2 : ℝ) * oldN0w c ν χo M) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hε3
      _ = |CJ| * ε ^ 3 * s ^ (5 / 2 : ℝ) * oldN0w c ν χo M := by ring
  have hLsum : affSum 6 (Lpt c ν ε μ χo χy M) s ≤
      7 * |CJ| * ε ^ 3 * s ^ (5 / 2 : ℝ) * oldN0w c ν χo M := by
    unfold affSum
    calc ∑ j ∈ Finset.range 7, frob (sDerivIter j (Lpt c ν ε μ χo χy M) s)
        ≤ ∑ _j ∈ Finset.range 7, (|CJ| * ε ^ 3 * s ^ (5 / 2 : ℝ) * oldN0w c ν χo M) :=
          Finset.sum_le_sum hLj
      _ = 7 * |CJ| * ε ^ 3 * s ^ (5 / 2 : ℝ) * oldN0w c ν χo M := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hexp := exp_le_of_ge_four_fifths has h.nu_pos hs
  have hLterm : affTerm as 6 (Lpt c ν ε μ χo χy M) s ≤
      7 * |CJ| * ε ^ 3 * Real.exp (-(4 * as / 5) / ν) * oldN0w c ν χo M := by
    unfold affTerm
    have hw : 0 ≤ Real.exp (-as * s) * s ^ (-(5 / 2 : ℝ)) :=
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hs0.le _)
    have hcancel : s ^ (-(5 / 2 : ℝ)) * s ^ (5 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add hs0, neg_add_cancel, Real.rpow_zero]
    calc Real.exp (-as * s) * s ^ (-(5 / 2 : ℝ)) * affSum 6 (Lpt c ν ε μ χo χy M) s
        ≤ Real.exp (-as * s) * s ^ (-(5 / 2 : ℝ)) *
            (7 * |CJ| * ε ^ 3 * s ^ (5 / 2 : ℝ) * oldN0w c ν χo M) :=
          mul_le_mul_of_nonneg_left hLsum hw
      _ = Real.exp (-as * s) * (7 * |CJ| * ε ^ 3 * oldN0w c ν χo M) := by
          linear_combination (Real.exp (-as * s) * (7 * |CJ| * ε ^ 3 * oldN0w c ν χo M)) * hcancel
      _ ≤ Real.exp (-(4 * as / 5) / ν) * (7 * |CJ| * ε ^ 3 * oldN0w c ν χo M) :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = 7 * |CJ| * ε ^ 3 * Real.exp (-(4 * as / 5) / ν) * oldN0w c ν χo M := by ring
  -- Bound the `ℓ • a_μ` term
  have hℓb := abs_ellMuGen_le h hM
  have hab := affTerm_aMuFun_tail has h.nu_pos h.mu_pos hs
  have hAterm : |ℓ| * affTerm as 6 (aMuFun μ) s ≤
      (1 / 4) * Ca * ε ^ 3 * Real.exp (-(4 * as / 5) / ν) * oldN0w c ν χo M := by
    calc |ℓ| * affTerm as 6 (aMuFun μ) s
        ≤ ((1 / 4 : ℝ) * ε ^ 3 * oldN0w c ν χo M) *
            (Ca * Real.exp (-(4 * as / 5) / ν)) :=
          mul_le_mul hℓb hab (affTerm_six_nonneg as (aMuFun μ) hs0) (by positivity)
      _ = (1 / 4) * Ca * ε ^ 3 * Real.exp (-(4 * as / 5) / ν) * oldN0w c ν χo M := by ring
  rw [hsub]
  calc affTerm as 6 (Lpt c ν ε μ χo χy M + (-ℓ) • aMuFun μ) s
      ≤ affTerm as 6 (Lpt c ν ε μ χo χy M) s + affTerm as 6 ((-ℓ) • aMuFun μ) s := hadd
    _ = affTerm as 6 (Lpt c ν ε μ χo χy M) s + |ℓ| * affTerm as 6 (aMuFun μ) s := by rw [hsmul]
    _ ≤ 7 * |CJ| * ε ^ 3 * Real.exp (-(4 * as / 5) / ν) * oldN0w c ν χo M +
          (1 / 4) * Ca * ε ^ 3 * Real.exp (-(4 * as / 5) / ν) * oldN0w c ν χo M :=
        add_le_add hLterm hAterm
    _ = (7 * |CJ| + (1 / 4) * Ca) * ε ^ 3 * Real.exp (-(4 * as / 5) / ν) * oldN0w c ν χo M := by
        ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5
