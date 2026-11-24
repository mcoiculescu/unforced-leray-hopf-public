import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S2_1_2
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.RawResidualIteratedEnvelope.LateTail.FixedBaseJets

/-!
# `PartII-b:S2/1/2/2`: `RawResidualIteratedLateTail`

Source of record: `the November 2 reference manuscript`, lines 1270-1304,
1305-1325, 2548-2551.

Proves `rawResidualIteratedLateTail_proof : UnforcedLeray.Short.IIb.RawResidualIteratedLateTail`:
at a single viscosity threshold `ν₀ > 0` independent of the spatial derivative order `m : ℕ`,
decomposing `Axi.age p.R • Axi.Nv p.R (resChartProfile p) τ` off the axis into the globally smooth
Cartesian heat polynomial sum `F_heat_total p M` (weighted by `1 + y₃^2` on `ϱ(y) ≤ R`) plus the
lifted remainder `r_rem_total p M` (at an expansion order `M` chosen so that `s^{-K_lift}` cancels
`(1 + s)^{K_lift}` and `(1 + |η|)^{-(m + 2)}` cancels `(1 + |η|)^m` with two powers to spare) yields
`‖iterDyRev β (rawResidualC p) (τ, y)‖ ≤ C * (1 + |y 2|) ^ (-2 : ℝ)` on `0 < ϱ(y) ≤ R`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray UnforcedLeray.PhaseSpace Set Filter Topology
open scoped ContDiff BigOperators
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.IIb (iterDyRev rawResidualC)
open UnforcedLeray.Short.IIb.RawResidualIteratedLateTailAux

theorem rawResidualIteratedLateTail_proof :
    UnforcedLeray.Short.IIb.RawResidualIteratedLateTail := by
  obtain ⟨ν₀, hν₀, HRem⟩ := exists_late_rem_total_jet
  refine ⟨ν₀, hν₀, fun p htr hν hc hR _hper m β => ?_⟩
  obtain ⟨K_lift, hLiftR⟩ := age_smul_nv_pt_jet_all m
  obtain ⟨C_lift, hClift0, hLift⟩ := hLiftR p.R hR
  obtain ⟨M, hr_sm, B_rem, hBrem0, hr_bd⟩ := HRem p htr hν hc m (m + 2) K_lift
  obtain ⟨hF_sm, C_heat, hCheat0, hF_bd⟩ := F_heat_total_wtdJet p m M
  set C : ℝ := 2 * C_heat + C_lift * ((m + 1 : ℕ) : ℝ) * B_rem * (2 : ℝ) ^ K_lift
  refine ⟨C, 0, le_rfl, fun τ _hτ y hy0 hyR _hyZ => ?_⟩
  have hyax : y ∉ Axi.axis := mt (Axi.mem_axis_iff y).mp hy0
  have hρ_pos : 0 < Axi.ϱ y := Axi.ϱ_pos hyax
  -- 1. Slice bound off the axis:
  have h_slice := norm_iterDyRev_rawResidualC_le_iteratedFDeriv p htr hR β τ hy0
  -- 2. Split the off-axis lifted residual into `F_heat_total p M` and the lifted remainder:
  obtain ⟨hRemLift_sm, hRemLift_bd⟩ := hLift (r_rem_total p M) hr_sm τ y hyax
  let G₁ : Space → Space := F_heat_total p M
  let G₂ : Space → Space := fun w => Axi.age p.R w • Axi.Nv p.R (r_rem_total p M) τ w
  have hev : (fun w => Axi.age p.R w • Axi.Nv p.R (FarDecaySub.resChartProfile p) τ w) =ᶠ[𝓝 y]
      (G₁ + G₂) :=
    Filter.eventuallyEq_of_mem (Axi.isOpen_compl_axis.mem_nhds hyax) fun z hz =>
      late_lift_decomp_off_axis p htr hR M τ hz
  have hsplit_norm :
      ‖iteratedFDeriv ℝ m
          (fun w => Axi.age p.R w • Axi.Nv p.R (FarDecaySub.resChartProfile p) τ w) y‖ ≤
        ‖iteratedFDeriv ℝ m G₁ y‖ + ‖iteratedFDeriv ℝ m G₂ y‖ := by
    have hadd : iteratedFDeriv ℝ m (G₁ + G₂) y =
        iteratedFDeriv ℝ m G₁ y + iteratedFDeriv ℝ m G₂ y :=
      iteratedFDeriv_add_apply (hF_sm.contDiffAt.of_le (by exact_mod_cast le_top))
        ((hRemLift_sm.contDiffAt (Axi.isOpen_compl_axis.mem_nhds hyax)).of_le
          (by exact_mod_cast le_top))
    rw [(hev.iteratedFDeriv ℝ m).eq_of_nhds, hadd]
    exact norm_add_le _ _
  -- Common axial weight `1 + |y 2|`:
  have hw_pos : 0 < 1 + |y 2| := by positivity
  have hrpow_inv : (1 + |y 2|) ^ (-2 : ℝ) = ((1 + |y 2|) ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hw_pos.le, Real.rpow_natCast]
  -- 3. Bound the Cartesian heat sum `G₁`:
  have hG₁_bound : ‖iteratedFDeriv ℝ m G₁ y‖ ≤ 2 * C_heat * (1 + |y 2|) ^ (-2 : ℝ) := by
    have hsq_le : (1 + |y 2|) ^ 2 ≤ 2 * (1 + y 2 ^ 2) := by
      nlinarith [sq_nonneg (|y 2| - 1), sq_abs (y 2)]
    have hprod : (1 + |y 2|) ^ 2 * ‖iteratedFDeriv ℝ m G₁ y‖ ≤ 2 * C_heat := by
      calc (1 + |y 2|) ^ 2 * ‖iteratedFDeriv ℝ m G₁ y‖
          ≤ (2 * (1 + y 2 ^ 2)) * ‖iteratedFDeriv ℝ m G₁ y‖ :=
            mul_le_mul_of_nonneg_right hsq_le (norm_nonneg _)
        _ = 2 * ((1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ m G₁ y‖) := by ring
        _ ≤ 2 * C_heat := mul_le_mul_of_nonneg_left (hF_bd y hyR) zero_le_two
    rw [hrpow_inv]
    exact (le_mul_inv_iff₀ (pow_pos hw_pos 2)).2 (by linarith)
  -- 4. Bound the lifted remainder `G₂` on `0 < ϱ(y) ≤ p.R`:
  have hG₂_bound :
      ‖iteratedFDeriv ℝ m G₂ y‖ ≤
        C_lift * ((m + 1 : ℕ) : ℝ) * B_rem * (2 : ℝ) ^ K_lift * (1 + |y 2|) ^ (-2 : ℝ) := by
    have hdiv1 : 1 ≤ p.R / Axi.ϱ y := (one_le_div hρ_pos).2 hyR
    set s : ℝ := Axi.age p.R y
    have hs1 : 1 ≤ s := by
      change 1 ≤ Axi.age p.R y
      unfold Axi.age
      rw [← div_pow]
      exact one_le_pow₀ hdiv1
    have hs0 : 0 < s := lt_of_lt_of_le one_pos hs1
    have hy2_le_trans : |y 2| ≤ |Axi.trans p.R y| := by
      have htr_eq : |Axi.trans p.R y| = (p.R / Axi.ϱ y) * |y 2| := by
        unfold Axi.trans
        rw [mul_div_right_comm, abs_mul, abs_of_nonneg (zero_le_one.trans hdiv1)]
      rw [htr_eq]
      exact le_mul_of_one_le_left (abs_nonneg _) hdiv1
    set T : ℝ := 1 + |Axi.trans p.R y|
    have hT_pos : 0 < T := by unfold T; positivity
    have hw_le_T : 1 + |y 2| ≤ T := by unfold T; linarith
    have hsum_rem :
        ∑ l ∈ Finset.range (m + 1),
          ‖iteratedFDeriv ℝ l (r_rem_total p M) (Axi.chart p.R τ y)‖ ≤
          ((m + 1 : ℕ) : ℝ) * (B_rem * s ^ (-(K_lift : ℝ)) * (T ^ (m + 2))⁻¹) := by
      have hterm : ∀ l ∈ Finset.range (m + 1),
          ‖iteratedFDeriv ℝ l (r_rem_total p M) (Axi.chart p.R τ y)‖ ≤
            B_rem * s ^ (-(K_lift : ℝ)) * (T ^ (m + 2))⁻¹ := by
        intro l hl_mem
        have hl : l ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl_mem)
        have hbd := hr_bd (Axi.chart p.R τ y) hs1 l hl
        change T ^ (m + 2) *
          ‖iteratedFDeriv ℝ l (r_rem_total p M) (Axi.chart p.R τ y)‖ ≤
            B_rem * s ^ (-(K_lift : ℝ)) at hbd
        exact (le_mul_inv_iff₀ (pow_pos hT_pos (m + 2))).2 (by linarith)
      calc ∑ l ∈ Finset.range (m + 1),
              ‖iteratedFDeriv ℝ l (r_rem_total p M) (Axi.chart p.R τ y)‖
          ≤ ∑ _l ∈ Finset.range (m + 1),
              (B_rem * s ^ (-(K_lift : ℝ)) * (T ^ (m + 2))⁻¹) :=
            Finset.sum_le_sum hterm
        _ = ((m + 1 : ℕ) : ℝ) * (B_rem * s ^ (-(K_lift : ℝ)) * (T ^ (m + 2))⁻¹) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hs_cancel : (1 + s) ^ K_lift * s ^ (-(K_lift : ℝ)) ≤ (2 : ℝ) ^ K_lift := by
      have h1s : (1 + s) ^ K_lift ≤ (2 : ℝ) ^ K_lift * s ^ K_lift := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) K_lift
      have hs_inv : (s ^ K_lift : ℝ) * s ^ (-(K_lift : ℝ)) = 1 := by
        rw [← Real.rpow_natCast s K_lift, ← Real.rpow_add hs0, add_neg_cancel, Real.rpow_zero]
      calc (1 + s) ^ K_lift * s ^ (-(K_lift : ℝ))
          ≤ ((2 : ℝ) ^ K_lift * s ^ K_lift) * s ^ (-(K_lift : ℝ)) :=
            mul_le_mul_of_nonneg_right h1s (Real.rpow_nonneg hs0.le _)
        _ = (2 : ℝ) ^ K_lift * ((s ^ K_lift : ℝ) * s ^ (-(K_lift : ℝ))) := by ring
        _ = (2 : ℝ) ^ K_lift := by rw [hs_inv, mul_one]
    have hT_cancel : T ^ m * (T ^ (m + 2))⁻¹ ≤ (1 + |y 2|) ^ (-2 : ℝ) := by
      have hT_eq : T ^ m * (T ^ (m + 2))⁻¹ = (T ^ 2)⁻¹ := by
        have hTm_ne : T ^ m ≠ 0 := pow_ne_zero m hT_pos.ne'
        rw [pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ hTm_ne, one_mul]
      have hT_sq : (1 + |y 2|) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hw_pos.le hw_le_T 2
      rw [hT_eq, hrpow_inv]
      exact inv_anti₀ (pow_pos hw_pos 2) hT_sq
    calc ‖iteratedFDeriv ℝ m G₂ y‖
        ≤ C_lift * (1 + s) ^ K_lift * T ^ m *
            ∑ l ∈ Finset.range (m + 1),
              ‖iteratedFDeriv ℝ l (r_rem_total p M) (Axi.chart p.R τ y)‖ := hRemLift_bd
      _ ≤ C_lift * (1 + s) ^ K_lift * T ^ m *
            (((m + 1 : ℕ) : ℝ) * (B_rem * s ^ (-(K_lift : ℝ)) * (T ^ (m + 2))⁻¹)) :=
          mul_le_mul_of_nonneg_left hsum_rem (by positivity)
      _ = C_lift * ((m + 1 : ℕ) : ℝ) * B_rem *
            ((1 + s) ^ K_lift * s ^ (-(K_lift : ℝ))) *
            (T ^ m * (T ^ (m + 2))⁻¹) := by ring
      _ ≤ C_lift * ((m + 1 : ℕ) : ℝ) * B_rem *
            (2 : ℝ) ^ K_lift * (1 + |y 2|) ^ (-2 : ℝ) := by
          have h1 : C_lift * ((m + 1 : ℕ) : ℝ) * B_rem *
              ((1 + s) ^ K_lift * s ^ (-(K_lift : ℝ))) ≤
              C_lift * ((m + 1 : ℕ) : ℝ) * B_rem * (2 : ℝ) ^ K_lift :=
            mul_le_mul_of_nonneg_left hs_cancel (by positivity)
          exact mul_le_mul h1 hT_cancel (by positivity) (by positivity)
  -- 5. Combine both pieces:
  calc ‖iterDyRev β (rawResidualC p) (τ, y)‖
      ≤ ‖iteratedFDeriv ℝ m
          (fun w => Axi.age p.R w • Axi.Nv p.R (FarDecaySub.resChartProfile p) τ w) y‖ := h_slice
    _ ≤ ‖iteratedFDeriv ℝ m G₁ y‖ + ‖iteratedFDeriv ℝ m G₂ y‖ := hsplit_norm
    _ ≤ 2 * C_heat * (1 + |y 2|) ^ (-2 : ℝ) +
          C_lift * ((m + 1 : ℕ) : ℝ) * B_rem * (2 : ℝ) ^ K_lift * (1 + |y 2|) ^ (-2 : ℝ) :=
        add_le_add hG₁_bound hG₂_bound
    _ = C * (1 + |y 2|) ^ (-2 : ℝ) := by unfold C; ring

end
