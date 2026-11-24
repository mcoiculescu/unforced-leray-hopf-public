import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_1

/-!
# Calculus for `RawResidualIteratedEnvelope` (`PartII-b:S2/1/2`)

Source of record: `the November 2 reference manuscript`,
lines 2542-2548 (large radius: unprojected derivatives of the complete source are
`O(ϱ^{-3-k}(1+|y₃|/ϱ)^{-N})`), 1206-1222 (ring lift `F_R = s^{3/2} r`).

All-order versions of the order-`≤ 3` calculus of
`PartIII-b_C_ward_12_3_1_2_5_1_1_3_1/ChartLift.lean` and of the order-`2` far jet
`FarDecaySub.age_smul_nv_far_jet2`:

1. `iterDyRev_eq_slice`, `norm_iterDyRev_le_slice`: on an open set where `G` is `C^∞`,
   `iterDyRev β G (a, y)` is the `m`-th derivative of the slice `G (a, ·)` at `y` evaluated on
   coordinate vectors, hence bounded by its norm (all-order `sliceBridge`);
2. `chart_jet_upto`, `lift_jet_upto`, `age_jet_upto`: on `ϱ ≥ R ≥ 1`, the jets of order `≤ M` of
   the chart, of the lift factor `√s · frame`, and of the age `s` are bounded by
   `(K (1+|y₃|/ϱ))^i`, `C ϱ⁻¹`, `C ϱ⁻²`;
3. `nv_far_jet_upto`, `age_smul_nv_far_jet_upto` (Faà di Bruno + Leibniz):
   `‖D^M (s • N_v b)(y)‖ ≤ A ϱ⁻³ (1+|y₃|/ϱ)^M ∑_{l ≤ M} ‖D^l b (chart y)‖` on `ϱ ≥ R`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

namespace RawIterEnvSub

open UnforcedLeray.PhaseSpace UnforcedLeray.Short.PartIIIb.Concrete

/-! ### 1. The slice bridge for `iterDyRev` -/

theorem contDiffOn_iterDyRev' {G : ℝ × Space → CVec3} {U : Set (ℝ × Space)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) :
    ∀ {m : ℕ} (β : Fin m → Fin 3), ContDiffOn ℝ ∞ (iterDyRev β G) U
  | 0, _ => hG
  | m + 1, β => sb_dy_contDiffOn hU (contDiffOn_iterDyRev' hU hG (Fin.init β)) (β (Fin.last m))

theorem iterDyRev_eq_slice {G : ℝ × Space → CVec3} {U : Set (ℝ × Space)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) :
    ∀ {m : ℕ} (β : Fin m → Fin 3) (a : ℝ) (y : Space), (a, y) ∈ U →
      iterDyRev β G (a, y) =
        iteratedFDeriv ℝ m (fun w => G (a, w)) y
          (fun i => UnforcedLeray.coordinateVector (β (Fin.rev i)))
  | 0, β, a, y, _ => by
      simp [iterDyRev, iteratedFDeriv_zero_apply]
  | m + 1, β, a, y, hy => by
      have hV : IsOpen {w : Space | (a, w) ∈ U} :=
        hU.preimage (continuous_const.prodMk continuous_id)
      have hH : ContDiffOn ℝ ∞ (iterDyRev (Fin.init β) G) U :=
        contDiffOn_iterDyRev' hU hG (Fin.init β)
      have hS : ContDiffOn ℝ ∞ (fun w => G (a, w)) {w : Space | (a, w) ∈ U} :=
        sb_slice_contDiffOn hG a
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ m (fun w => G (a, w))) y :=
        (hS.contDiffAt (hV.mem_nhds hy)).differentiableAt_iteratedFDeriv
          (by exact_mod_cast ENat.natCast_lt_top m)
      have hev : (fun w => iterDyRev (Fin.init β) G (a, w)) =ᶠ[𝓝 y]
          fun w => iteratedFDeriv ℝ m (fun w => G (a, w)) w
            (fun i => UnforcedLeray.coordinateVector (Fin.init β (Fin.rev i))) :=
        Filter.eventually_of_mem (hV.mem_nhds hy)
          (fun w hw => iterDyRev_eq_slice hU hG (Fin.init β) a w hw)
      have htail : Fin.tail (fun i : Fin (m + 1) => UnforcedLeray.coordinateVector (β (Fin.rev i))) =
          fun i => UnforcedLeray.coordinateVector (Fin.init β (Fin.rev i)) := by
        funext i
        simp [Fin.tail, Fin.init, Fin.rev_succ]
      have h0 : UnforcedLeray.coordinateVector (β (Fin.rev (0 : Fin (m + 1)))) =
          UnforcedLeray.coordinateVector (β (Fin.last m)) := by
        simp [Fin.rev_zero]
      show dy (β (Fin.last m)) (iterDyRev (Fin.init β) G) (a, y) = _
      rw [sb_slice_dy hU hH a y hy, hev.fderiv_eq, hdiff.iteratedFDeriv_succ_apply_left', htail]
      exact congrArg _ h0.symm

theorem norm_iterDyRev_le_slice {G : ℝ × Space → CVec3} {U : Set (ℝ × Space)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {m : ℕ} (β : Fin m → Fin 3) {a : ℝ} {y : Space}
    (hy : (a, y) ∈ U) :
    ‖iterDyRev β G (a, y)‖ ≤ ‖iteratedFDeriv ℝ m (fun w => G (a, w)) y‖ := by
  rw [iterDyRev_eq_slice hU hG β a y hy]
  exact sb_opnorm _ _ (fun i => sb_norm_coord _)

/-! ### 2. Chart, lift-factor and age jets of every order on `ϱ ≥ R` -/

theorem notMem_axis_of_le {R : ℝ} (hR : 0 < R) {y : Space} (hy : R ≤ Axi.ϱ y) :
    y ∉ Axi.axis := by
  intro h
  rw [Axi.mem_axis_iff] at h
  linarith

/-- Component bound for the chart jets of order `m ≥ 1` on `ϱ ≥ R` (the `key` step of
`chartJetBound`, for every `m`). -/
theorem chart_jet_key {R : ℝ} (hR : 0 < R) (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (y : Space), R ≤ Axi.ϱ y →
      ‖iteratedFDeriv ℝ m (Axi.chart R τ) y‖ ≤
        C * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by
  obtain ⟨Ca, hCa0, hCa⟩ := ageJet R hR m hm
  obtain ⟨Cp, hCp0, hCp⟩ := phaseJet R hR m hm
  obtain ⟨Ct, hCt0, hCt⟩ := transJet R hR m
  have hL1 : 0 ≤ ‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹) :=
    mul_nonneg (norm_nonneg _) (mul_nonneg hCa0 (inv_nonneg.2 (sq_nonneg R)))
  have hL2 : 0 ≤ ‖chartJetL2‖ * Cp := mul_nonneg (norm_nonneg _) hCp0
  have hL3 : 0 ≤ ‖chartJetL3‖ * Ct := mul_nonneg (norm_nonneg _) hCt0
  refine ⟨‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹) + ‖chartJetL2‖ * Cp + ‖chartJetL3‖ * Ct,
    add_nonneg (add_nonneg hL1 hL2) hL3, ?_⟩
  intro τ y hy
  have hp : 0 < Axi.ϱ y := lt_of_lt_of_le hR hy
  have hyax : y ∉ Axi.axis := notMem_axis_of_le hR hy
  have hU : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
  have hmem : (Axi.axisᶜ : Set Space) ∈ nhds y := hU.mem_nhds hyax
  have hAgeS : ContDiffOn ℝ ∞ (fun z : Space => R ^ 2 / Axi.ϱ z ^ 2) Axi.axisᶜ :=
    contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2)
      (fun z hz => pow_ne_zero 2 (Axi.ϱ_ne_zero hz))
  have hLogS : ContDiffOn ℝ ∞ (fun z : Space => Real.log (Axi.age R z)) Axi.axisᶜ :=
    ContDiffOn.log hAgeS (fun z hz => (Axi.age_pos hR.ne' hz).ne')
  have hPhaseS : ContDiffOn ℝ ∞
      (fun z : Space => R * τ / 2 - (R / 2) * Real.log (Axi.age R z)) Axi.axisᶜ :=
    contDiffOn_const.sub (contDiffOn_const.mul hLogS)
  have hTransS : ContDiffOn ℝ ∞ (fun z : Space => R * z 2 / Axi.ϱ z) Axi.axisᶜ :=
    ((show ContDiff ℝ ∞ (fun z : Space => R * z 2) by fun_prop).contDiffOn).div
      Axi.contDiffOn_ϱ (fun z hz => Axi.ϱ_ne_zero hz)
  have hAgeA : ContDiffAt ℝ ∞ (Axi.age R) y := hAgeS.contDiffAt hmem
  have hPhaseA : ContDiffAt ℝ ∞ (Axi.phase R τ) y := hPhaseS.contDiffAt hmem
  have hTransA : ContDiffAt ℝ ∞ (Axi.trans R) y := hTransS.contDiffAt hmem
  have hm' : (m : WithTop ℕ∞) ≤ ∞ := hjLe m
  have hA : ContDiffAt ℝ ∞ (chartJetL1 ∘ Axi.age R) y :=
    chartJetL1.contDiff.comp_contDiffAt y hAgeA
  have hB : ContDiffAt ℝ ∞ (chartJetL2 ∘ Axi.phase R τ) y :=
    chartJetL2.contDiff.comp_contDiffAt y hPhaseA
  have hC : ContDiffAt ℝ ∞ (chartJetL3 ∘ Axi.trans R) y :=
    chartJetL3.contDiff.comp_contDiffAt y hTransA
  have hAB : ContDiffAt ℝ ∞ (chartJetL1 ∘ Axi.age R + chartJetL2 ∘ Axi.phase R τ) y := hA.add hB
  have hDA : ‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y‖ ≤
      ‖chartJetL1‖ * (Ca * Axi.ϱ y ^ (-(2 + (m : ℝ)))) :=
    le_trans (ContinuousLinearMap.norm_iteratedFDeriv_comp_left chartJetL1 hAgeA hm')
      (mul_le_mul_of_nonneg_left (hCa y hyax) (norm_nonneg _))
  have hDB : ‖iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y‖ ≤
      ‖chartJetL2‖ * (Cp * Axi.ϱ y ^ (-(m : ℝ))) :=
    le_trans (ContinuousLinearMap.norm_iteratedFDeriv_comp_left chartJetL2 hPhaseA hm')
      (mul_le_mul_of_nonneg_left (hCp τ y hyax) (norm_nonneg _))
  have hDC : ‖iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖ ≤
      ‖chartJetL3‖ * (Ct * Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
    le_trans (ContinuousLinearMap.norm_iteratedFDeriv_comp_left chartJetL3 hTransA hm')
      (mul_le_mul_of_nonneg_left (hCt y hyax) (norm_nonneg _))
  have hq0 : 0 ≤ Axi.ϱ y ^ (-(m : ℝ)) := Real.rpow_nonneg hp.le _
  have hs0 : 0 ≤ |y 2| / Axi.ϱ y := div_nonneg (abs_nonneg _) hp.le
  have hs1 : 1 ≤ 1 + |y 2| / Axi.ϱ y := by linarith
  have hage : Axi.ϱ y ^ (-(2 + (m : ℝ))) ≤ (R ^ 2)⁻¹ * Axi.ϱ y ^ (-(m : ℝ)) := by
    have e : -(2 + (m : ℝ)) = -(m : ℝ) + -2 := by ring
    have h2 : Axi.ϱ y ^ (-2 : ℝ) = (Axi.ϱ y ^ 2)⁻¹ := by
      rw [Real.rpow_neg hp.le, Real.rpow_two]
    have hinv : (Axi.ϱ y ^ 2)⁻¹ ≤ (R ^ 2)⁻¹ :=
      inv_anti₀ (pow_pos hR 2) (by nlinarith [mul_nonneg (sub_nonneg.2 hy) (add_nonneg hR.le hp.le)])
    rw [e, Real.rpow_add hp, h2]
    calc Axi.ϱ y ^ (-(m : ℝ)) * (Axi.ϱ y ^ 2)⁻¹ = (Axi.ϱ y ^ 2)⁻¹ * Axi.ϱ y ^ (-(m : ℝ)) :=
          mul_comm _ _
      _ ≤ (R ^ 2)⁻¹ * Axi.ϱ y ^ (-(m : ℝ)) := mul_le_mul_of_nonneg_right hinv hq0
  have eA : ‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y‖ ≤
      (‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹)) *
        (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by
    refine le_trans hDA ?_
    calc ‖chartJetL1‖ * (Ca * Axi.ϱ y ^ (-(2 + (m : ℝ))))
        ≤ ‖chartJetL1‖ * (Ca * ((R ^ 2)⁻¹ * Axi.ϱ y ^ (-(m : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hage hCa0) (norm_nonneg _)
      _ = (‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹)) * Axi.ϱ y ^ (-(m : ℝ)) := by ring
      _ ≤ (‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹)) *
          (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hq0 hs1) hL1
  have eB : ‖iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y‖ ≤
      (‖chartJetL2‖ * Cp) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by
    refine le_trans hDB ?_
    calc ‖chartJetL2‖ * (Cp * Axi.ϱ y ^ (-(m : ℝ)))
        = (‖chartJetL2‖ * Cp) * Axi.ϱ y ^ (-(m : ℝ)) := by ring
      _ ≤ (‖chartJetL2‖ * Cp) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hq0 hs1) hL2
  have eC : ‖iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖ ≤
      (‖chartJetL3‖ * Ct) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by
    refine le_trans hDC (le_of_eq ?_)
    ring
  rw [chartJet_decomp R τ, iteratedFDeriv_add_apply (hAB.of_le hm') (hC.of_le hm'),
    iteratedFDeriv_add_apply (hA.of_le hm') (hB.of_le hm')]
  calc ‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y +
          iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y +
        iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖
      ≤ ‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y +
          iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y‖ +
        ‖iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖ := norm_add_le _ _
    _ ≤ (‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y‖ +
          ‖iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y‖) +
        ‖iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖ :=
          add_le_add_left (norm_add_le _ _) _
    _ ≤ ((‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹)) *
          (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) +
        (‖chartJetL2‖ * Cp) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y))) +
        (‖chartJetL3‖ * Ct) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
          add_le_add (add_le_add eA eB) eC
    _ = (‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹) + ‖chartJetL2‖ * Cp + ‖chartJetL3‖ * Ct) *
          (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by ring

/-- Chart jets of orders `1 ≤ i ≤ M` on `ϱ ≥ R ≥ 1` in Faà di Bruno form. -/
theorem chart_jet_upto {R : ℝ} (hR : 1 ≤ R) (M : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (τ : ℝ) (y : Space), R ≤ Axi.ϱ y → ∀ i : ℕ, 1 ≤ i → i ≤ M →
      ‖iteratedFDeriv ℝ i (Axi.chart R τ) y‖ ≤ (K * (1 + |y 2| / Axi.ϱ y)) ^ i := by
  have hR0 : 0 < R := by linarith
  have key' : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (y : Space), R ≤ Axi.ϱ y → 1 ≤ i →
      ‖iteratedFDeriv ℝ i (Axi.chart R τ) y‖ ≤
        C * (Axi.ϱ y ^ (-(i : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by
    intro i
    by_cases hi : 1 ≤ i
    · obtain ⟨C, hC0, hC⟩ := chart_jet_key hR0 i hi
      exact ⟨C, hC0, fun τ y hy _ => hC τ y hy⟩
    · exact ⟨0, le_rfl, fun τ y hy h => absurd h hi⟩
  choose C hC0 hC using key'
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range (M + 1), C i := Finset.sum_nonneg fun i _ => hC0 i
  refine ⟨1 + ∑ i ∈ Finset.range (M + 1), C i, by linarith, fun τ y hy i hi1 hiM => ?_⟩
  have hp : 0 < Axi.ϱ y := lt_of_lt_of_le hR0 hy
  have hp1 : 1 ≤ Axi.ϱ y := le_trans hR hy
  have ht : 0 ≤ |y 2| / Axi.ϱ y := div_nonneg (abs_nonneg _) hp.le
  have hCK : C i ≤ 1 + ∑ i ∈ Finset.range (M + 1), C i := by
    have : C i ≤ ∑ i ∈ Finset.range (M + 1), C i :=
      Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_range.2 (by omega))
    linarith
  have hq : Axi.ϱ y ^ (-(i : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 (by simp)
  have hq0 : 0 ≤ Axi.ϱ y ^ (-(i : ℝ)) := Real.rpow_nonneg hp.le _
  have hK1t : 1 ≤ (1 + ∑ i ∈ Finset.range (M + 1), C i) * (1 + |y 2| / Axi.ϱ y) := by
    nlinarith
  calc ‖iteratedFDeriv ℝ i (Axi.chart R τ) y‖
      ≤ C i * (Axi.ϱ y ^ (-(i : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := hC i τ y hy hi1
    _ ≤ (1 + ∑ i ∈ Finset.range (M + 1), C i) * (1 * (1 + |y 2| / Axi.ϱ y)) :=
        mul_le_mul hCK (mul_le_mul_of_nonneg_right hq (by linarith))
          (mul_nonneg hq0 (by linarith)) (by linarith)
    _ = (1 + ∑ i ∈ Finset.range (M + 1), C i) * (1 + |y 2| / Axi.ϱ y) := by ring
    _ ≤ ((1 + ∑ i ∈ Finset.range (M + 1), C i) * (1 + |y 2| / Axi.ϱ y)) ^ i :=
        le_self_pow₀ hK1t (by omega)

/-- Jets of the lift factor of orders `≤ M` on `ϱ ≥ R ≥ 1`: `‖D^i (√s · frame)‖ ≤ C ϱ⁻¹`. -/
theorem lift_jet_upto {R : ℝ} (hR : 1 ≤ R) (M : ℕ) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ y : Space, R ≤ Axi.ϱ y → ∀ i : ℕ, i ≤ M →
      ‖iteratedFDeriv ℝ i (liftFactor R) y‖ ≤ Cf * (Axi.ϱ y)⁻¹ := by
  have hR0 : 0 < R := by linarith
  choose C hC0 hC using fun i => liftFactorJet R hR0 i
  refine ⟨∑ i ∈ Finset.range (M + 1), C i, Finset.sum_nonneg fun i _ => hC0 i,
    fun y hy i hi => ?_⟩
  have hp : 0 < Axi.ϱ y := lt_of_lt_of_le hR0 hy
  have hp1 : 1 ≤ Axi.ϱ y := le_trans hR hy
  have hyax : y ∉ Axi.axis := notMem_axis_of_le hR0 hy
  have hrp : Axi.ϱ y ^ (-(1 + (i : ℝ))) ≤ (Axi.ϱ y)⁻¹ := by
    rw [clf_rpow _ hp.le i]
    refine inv_anti₀ hp ?_
    calc Axi.ϱ y = Axi.ϱ y ^ 1 := (pow_one _).symm
      _ ≤ Axi.ϱ y ^ (1 + i) := pow_le_pow_right₀ hp1 (by omega)
  have hCi : C i ≤ ∑ i ∈ Finset.range (M + 1), C i :=
    Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_range.2 (by omega))
  calc ‖iteratedFDeriv ℝ i (liftFactor R) y‖ ≤ C i * Axi.ϱ y ^ (-(1 + (i : ℝ))) := hC i y hyax
    _ ≤ (∑ i ∈ Finset.range (M + 1), C i) * (Axi.ϱ y)⁻¹ :=
        mul_le_mul hCi hrp (Real.rpow_nonneg hp.le _)
          (le_trans (hC0 i) hCi)

/-- Jets of the age `s = R²/ϱ²` of orders `≤ M` on `ϱ ≥ R ≥ 1`: `‖D^i s‖ ≤ C ϱ⁻²`. -/
theorem age_jet_upto {R : ℝ} (hR : 1 ≤ R) (M : ℕ) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ y : Space, R ≤ Axi.ϱ y → ∀ i : ℕ, i ≤ M →
      ‖iteratedFDeriv ℝ i (Axi.age R) y‖ ≤ Ca * (Axi.ϱ y ^ 2)⁻¹ := by
  have hR0 : 0 < R := by linarith
  have key : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, R ≤ Axi.ϱ y →
      ‖iteratedFDeriv ℝ i (Axi.age R) y‖ ≤ C * (Axi.ϱ y ^ 2)⁻¹ := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · refine ⟨R ^ 2, sq_nonneg R, fun y hy => ?_⟩
      have hp : 0 < Axi.ϱ y := lt_of_lt_of_le hR0 hy
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Axi.age,
        abs_of_nonneg (div_nonneg (sq_nonneg R) (sq_nonneg _)), div_eq_mul_inv]
    · obtain ⟨C, hC0, hC⟩ := ageJet R hR0 i hi
      refine ⟨C, hC0, fun y hy => ?_⟩
      have hp : 0 < Axi.ϱ y := lt_of_lt_of_le hR0 hy
      have hp1 : 1 ≤ Axi.ϱ y := le_trans hR hy
      have hyax : y ∉ Axi.axis := notMem_axis_of_le hR0 hy
      have hrp : Axi.ϱ y ^ (-(2 + (i : ℝ))) ≤ (Axi.ϱ y ^ 2)⁻¹ := by
        rw [show -(2 + (i : ℝ)) = -((2 + i : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hp.le,
          Real.rpow_natCast]
        exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hp1 (by omega))
      exact (hC y hyax).trans (mul_le_mul_of_nonneg_left hrp hC0)
  choose C hC0 hC using key
  refine ⟨∑ i ∈ Finset.range (M + 1), C i, Finset.sum_nonneg fun i _ => hC0 i,
    fun y hy i hi => ?_⟩
  have hp : 0 < Axi.ϱ y := lt_of_lt_of_le hR0 hy
  exact (hC i y hy).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_range.2 (by omega)))
    (by positivity))

/-! ### 3. Faà di Bruno and Leibniz for `s • N_v b` on `ϱ ≥ R` -/

/-- Faà di Bruno for `b ∘ chart` on the axis complement, orders `j ≤ M`. -/
theorem comp_chart_jet {R : ℝ} (hR : 0 < R) (K : ℝ) (M : ℕ)
    (hKb : ∀ (τ : ℝ) (y : Space), R ≤ Axi.ϱ y → ∀ i : ℕ, 1 ≤ i → i ≤ M →
      ‖iteratedFDeriv ℝ i (Axi.chart R τ) y‖ ≤ (K * (1 + |y 2| / Axi.ϱ y)) ^ i)
    (b : ℝ × (ℝ × ℝ) → Axi.Merid) (hb : ContDiffOn ℝ ∞ b {m : ℝ × (ℝ × ℝ) | 0 < m.1})
    (τ : ℝ) (y : Space) (hy : R ≤ Axi.ϱ y) (j : ℕ) (hj : j ≤ M) (S : ℝ)
    (hS : ∀ l : ℕ, l ≤ j → ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ ≤ S) :
    ‖iteratedFDerivWithin ℝ j (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖ ≤
      (j.factorial : ℝ) * S * (K * (1 + |y 2| / Axi.ϱ y)) ^ j := by
  have hyS : y ∈ (Axi.axisᶜ : Set Space) := notMem_axis_of_le hR hy
  have hT : IsOpen {m : ℝ × (ℝ × ℝ) | 0 < m.1} := isOpen_lt continuous_const continuous_fst
  have hmaps := clf_chart_mapsTo R τ hR
  have hxT : Axi.chart R τ y ∈ {m : ℝ × (ℝ × ℝ) | 0 < m.1} := hmaps hyS
  have hCb : ∀ i : ℕ, i ≤ j →
      ‖iteratedFDerivWithin ℝ i b {m : ℝ × (ℝ × ℝ) | 0 < m.1} (Axi.chart R τ y)‖ ≤ S := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) i hT hxT]
    exact hS i hi
  have hDb : ∀ i : ℕ, 1 ≤ i → i ≤ j →
      ‖iteratedFDerivWithin ℝ i (Axi.chart R τ) Axi.axisᶜ y‖ ≤
        (K * (1 + |y 2| / Axi.ϱ y)) ^ i := by
    intro i h1 hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) i Axi.isOpen_compl_axis hyS]
    exact hKb τ y hy i h1 (le_trans hi hj)
  exact norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (N := ∞) hb (clf_chart_contDiffOn R τ hR)
    (hjLe j) hT.uniqueDiffOn Axi.isOpen_compl_axis.uniqueDiffOn hmaps hyS hCb hDb

/-- Far jets of `N_v b` of orders `≤ M` on `ϱ ≥ R ≥ 1` (weak form):
`‖D^k N_v b‖ ≤ A ϱ⁻¹ (1+|y₃|/ϱ)^M ∑_{l ≤ M} ‖D^l b(chart)‖`. -/
theorem nv_far_jet_upto {R : ℝ} (hR : 1 ≤ R) (M : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (b : ℝ × (ℝ × ℝ) → Axi.Merid),
      ContDiffOn ℝ ∞ b {m : ℝ × (ℝ × ℝ) | 0 < m.1} →
      ∀ (τ : ℝ) (y : Space), R ≤ Axi.ϱ y → ∀ k : ℕ, k ≤ M →
        ‖iteratedFDeriv ℝ k (Axi.Nv R b τ) y‖ ≤
          A * (Axi.ϱ y)⁻¹ * ((1 + |y 2| / Axi.ϱ y) ^ M *
            ∑ l ∈ Finset.range (M + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖) := by
  have hR0 : 0 < R := by linarith
  obtain ⟨K, hK1, hKb⟩ := chart_jet_upto hR M
  obtain ⟨Cf, hCf0, hCf⟩ := lift_jet_upto hR M
  have hK0 : 0 ≤ K := by linarith
  refine ⟨((M : ℝ) + 1) * (2 ^ M * (Cf * ((M.factorial : ℝ) * K ^ M))), by positivity, ?_⟩
  intro b hb τ y hy k hk
  have hp : 0 < Axi.ϱ y := lt_of_lt_of_le hR0 hy
  have hyS : y ∈ (Axi.axisᶜ : Set Space) := notMem_axis_of_le hR0 hy
  have ht : 0 ≤ |y 2| / Axi.ϱ y := div_nonneg (abs_nonneg _) hp.le
  have ht1 : 1 ≤ 1 + |y 2| / Axi.ϱ y := by linarith
  set S : ℝ := ∑ l ∈ Finset.range (M + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ with hS_def
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hSl : ∀ l : ℕ, l ≤ M → ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ ≤ S := fun l hl =>
    Finset.single_le_sum (f := fun l => ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  have hgS : ContDiffOn ℝ ∞ (fun z => b (Axi.chart R τ z)) Axi.axisᶜ :=
    hb.comp (clf_chart_contDiffOn R τ hR0) (clf_chart_mapsTo R τ hR0)
  have hinv0 : 0 ≤ (Axi.ϱ y)⁻¹ := inv_nonneg.2 hp.le
  have hQ0 : 0 ≤ 2 ^ M * (Cf * (Axi.ϱ y)⁻¹) *
      ((M.factorial : ℝ) * S * (K ^ M * (1 + |y 2| / Axi.ϱ y) ^ M)) := by positivity
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (liftFactor R) Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (k - i) (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖ ≤
      2 ^ M * (Cf * (Axi.ϱ y)⁻¹) *
        ((M.factorial : ℝ) * S * (K ^ M * (1 + |y 2| / Axi.ϱ y) ^ M)) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := liftFactor R) i Axi.isOpen_compl_axis hyS]
    have h1 : ‖iteratedFDeriv ℝ i (liftFactor R) y‖ ≤ Cf * (Axi.ϱ y)⁻¹ :=
      hCf y hy i (by omega)
    have h2 := comp_chart_jet hR0 K M hKb b hb τ y hy (k - i) (by omega) S
      (fun l hl => hSl l (by omega))
    have hch : (k.choose i : ℝ) ≤ 2 ^ M := by
      have : k.choose i ≤ 2 ^ M :=
        (Nat.choose_le_two_pow k i).trans (Nat.pow_le_pow_right (by norm_num) hk)
      exact_mod_cast this
    have hfac : ((k - i).factorial : ℝ) ≤ M.factorial := by
      exact_mod_cast Nat.factorial_le (by omega)
    have hpow : (K * (1 + |y 2| / Axi.ϱ y)) ^ (k - i) ≤ K ^ M * (1 + |y 2| / Axi.ϱ y) ^ M := by
      rw [mul_pow]
      exact mul_le_mul (pow_le_pow_right₀ hK1 (by omega)) (pow_le_pow_right₀ ht1 (by omega))
        (by positivity) (by positivity)
    have h2' : ‖iteratedFDerivWithin ℝ (k - i) (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖ ≤
        (M.factorial : ℝ) * S * (K ^ M * (1 + |y 2| / Axi.ϱ y) ^ M) :=
      h2.trans (mul_le_mul (mul_le_mul_of_nonneg_right hfac hS0) hpow (by positivity)
        (by positivity))
    exact mul_le_mul (mul_le_mul hch h1 (norm_nonneg _) (by positivity)) h2' (norm_nonneg _)
      (by positivity)
  have hsum := clf_nv_leib R hR0 τ b hgS y hyS k
  calc ‖iteratedFDeriv ℝ k (Axi.Nv R b τ) y‖
      ≤ ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (liftFactor R) Axi.axisᶜ y‖ *
            ‖iteratedFDerivWithin ℝ (k - i) (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖ := hsum
    _ ≤ ∑ _i ∈ Finset.range (k + 1), 2 ^ M * (Cf * (Axi.ϱ y)⁻¹) *
          ((M.factorial : ℝ) * S * (K ^ M * (1 + |y 2| / Axi.ϱ y) ^ M)) :=
        Finset.sum_le_sum hterm
    _ = ((k : ℝ) + 1) * (2 ^ M * (Cf * (Axi.ϱ y)⁻¹) *
          ((M.factorial : ℝ) * S * (K ^ M * (1 + |y 2| / Axi.ϱ y) ^ M))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ((M : ℝ) + 1) * (2 ^ M * (Cf * (Axi.ϱ y)⁻¹) *
          ((M.factorial : ℝ) * S * (K ^ M * (1 + |y 2| / Axi.ϱ y) ^ M))) := by
        refine mul_le_mul_of_nonneg_right ?_ hQ0
        have : (k : ℝ) ≤ M := by exact_mod_cast hk
        linarith
    _ = ((M : ℝ) + 1) * (2 ^ M * (Cf * ((M.factorial : ℝ) * K ^ M))) * (Axi.ϱ y)⁻¹ *
          ((1 + |y 2| / Axi.ϱ y) ^ M * S) := by ring

/-- **All-order far jet of `s • N_v b`** on `ϱ ≥ R ≥ 1`:
`‖D^M (s • N_v b)(y)‖ ≤ A ϱ⁻³ (1+|y₃|/ϱ)^M ∑_{l ≤ M} ‖D^l b (chart y)‖`. -/
theorem age_smul_nv_far_jet_upto {R : ℝ} (hR : 1 ≤ R) (M : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (b : ℝ × (ℝ × ℝ) → Axi.Merid),
      ContDiffOn ℝ ∞ b {m : ℝ × (ℝ × ℝ) | 0 < m.1} →
      ∀ (τ : ℝ) (y : Space), R ≤ Axi.ϱ y →
        ‖iteratedFDeriv ℝ M (fun w => Axi.age R w • Axi.Nv R b τ w) y‖ ≤
          A * (Axi.ϱ y ^ 3)⁻¹ * ((1 + |y 2| / Axi.ϱ y) ^ M *
            ∑ l ∈ Finset.range (M + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖) := by
  have hR0 : 0 < R := by linarith
  obtain ⟨Ca, hCa0, hCa⟩ := age_jet_upto hR M
  obtain ⟨A, hA0, hA⟩ := nv_far_jet_upto hR M
  refine ⟨((M : ℝ) + 1) * (2 ^ M * (Ca * A)), by positivity, ?_⟩
  intro b hb τ y hy
  have hp : 0 < Axi.ϱ y := lt_of_lt_of_le hR0 hy
  have hyS : y ∈ (Axi.axisᶜ : Set Space) := notMem_axis_of_le hR0 hy
  have hgS : ContDiffOn ℝ ∞ (fun z => b (Axi.chart R τ z)) Axi.axisᶜ :=
    hb.comp (clf_chart_contDiffOn R τ hR0) (clf_chart_mapsTo R τ hR0)
  have hAgeS : ContDiffOn ℝ ∞ (Axi.age R) Axi.axisᶜ :=
    contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2)
      (fun z hz => pow_ne_zero 2 (Axi.ϱ_ne_zero hz))
  have hNvS : ContDiffOn ℝ ∞ (Axi.Nv R b τ) Axi.axisᶜ := by
    have hEq : Axi.Nv R b τ = fun z => liftFactor R z (b (Axi.chart R τ z)) :=
      funext fun z => Nv_eq_liftFactor R b τ z
    rw [hEq]
    exact (clf_lift_contDiffOn R hR0).clm_apply hgS
  have hleib : ‖iteratedFDeriv ℝ M (fun w => Axi.age R w • Axi.Nv R b τ w) y‖ ≤
      ∑ i ∈ Finset.range (M + 1), (M.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i (Axi.age R) Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (M - i) (Axi.Nv R b τ) Axi.axisᶜ y‖ := by
    rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
      (f := fun w => Axi.age R w • Axi.Nv R b τ w) M Axi.isOpen_compl_axis hyS]
    exact norm_iteratedFDerivWithin_smul_le hAgeS hNvS
      Axi.isOpen_compl_axis.uniqueDiffOn hyS (hjLe M)
  set E : ℝ := (1 + |y 2| / Axi.ϱ y) ^ M *
    ∑ l ∈ Finset.range (M + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ with hE_def
  have ht : 0 ≤ |y 2| / Axi.ϱ y := div_nonneg (abs_nonneg _) hp.le
  have hE0 : 0 ≤ E := mul_nonneg (pow_nonneg (by linarith) _)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hterm : ∀ i ∈ Finset.range (M + 1),
      (M.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (Axi.age R) Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (M - i) (Axi.Nv R b τ) Axi.axisᶜ y‖ ≤
      2 ^ M * (Ca * (Axi.ϱ y ^ 2)⁻¹) * (A * (Axi.ϱ y)⁻¹ * E) := by
    intro i hi
    have hiM : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [iteratedFDerivWithin_of_isOpen i Axi.isOpen_compl_axis hyS,
      iteratedFDerivWithin_of_isOpen (M - i) Axi.isOpen_compl_axis hyS]
    have h1 := hCa y hy i hiM
    have h2 := hA b hb τ y hy (M - i) (by omega)
    have hch : (M.choose i : ℝ) ≤ 2 ^ M := by exact_mod_cast Nat.choose_le_two_pow M i
    exact mul_le_mul (mul_le_mul hch h1 (norm_nonneg _) (by positivity)) h2 (norm_nonneg _)
      (by positivity)
  have hfin : (Axi.ϱ y ^ 2)⁻¹ * (Axi.ϱ y)⁻¹ = (Axi.ϱ y ^ 3)⁻¹ := by
    rw [← mul_inv, ← pow_succ]
  calc ‖iteratedFDeriv ℝ M (fun w => Axi.age R w • Axi.Nv R b τ w) y‖
      ≤ ∑ i ∈ Finset.range (M + 1), (M.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (Axi.age R) Axi.axisᶜ y‖ *
          ‖iteratedFDerivWithin ℝ (M - i) (Axi.Nv R b τ) Axi.axisᶜ y‖ := hleib
    _ ≤ ∑ _i ∈ Finset.range (M + 1), 2 ^ M * (Ca * (Axi.ϱ y ^ 2)⁻¹) * (A * (Axi.ϱ y)⁻¹ * E) :=
        Finset.sum_le_sum hterm
    _ = ((M : ℝ) + 1) * (2 ^ M * (Ca * A)) * ((Axi.ϱ y ^ 2)⁻¹ * (Axi.ϱ y)⁻¹) * E := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = ((M : ℝ) + 1) * (2 ^ M * (Ca * A)) * (Axi.ϱ y ^ 3)⁻¹ * E := by rw [hfin]

end RawIterEnvSub

end UnforcedLeray.Short.IIb
