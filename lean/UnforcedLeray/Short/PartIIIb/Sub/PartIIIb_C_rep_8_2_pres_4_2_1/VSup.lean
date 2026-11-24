import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.Sub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.Raw
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletJetBound

/-!
# `PartIII-b:C/rep/8/2/pres/4/2/1/2`: Sup bound of the entrance background `V`

Source `the November 2 reference manuscript`
lines 2389-2390 (`‖E_ε α‖_{W^{j,∞}} ≤ P_ν |α|`), 2519-2520 (`|α| ≤ P_ν e^{m₀/ν} ε ≤ P_ν`),
2715-2725.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Sup bound of the entrance background `V = U_raw + E_ε α`**
(`PartIII-b:C/rep/8/2/pres/4/2/1/2`, source lines 2389-2390, 2519-2520, 2715-2725). -/
theorem vSupBound (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : VSupBound D := by
  obtain ⟨C1, k1, hRaw⟩ := rawSupBound D hst
  obtain ⟨C2, k2, ν₀, hC2, hν₀, hJ⟩ := UnforcedLeray.Short.IIb.inletJetBound
    D.Sig D.Pl.eigenvalue D.Pl.mode D.Sig_pos hst.planar.eigenpair dm dp hst.dm_pos 0
  have hν0 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ ν₀ :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds hν₀)
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds one_pos)
  refine ⟨|C1| + 2 * D.K.C0 * C2, max k1 (D.K.k0 + k2), ?_⟩
  filter_upwards [hst.actual, hRaw, hν0, hν1, rhoRep_le_one_eventually D hst] with
    n hn hR hν0n hν1n hρ τ y
  have hνpos : 0 < (D.level n).ν := (D.level n).ν_pos
  have ha : (1 : ℝ) ≤ (D.level n).ν⁻¹ := one_le_inv_iff₀.2 ⟨hνpos, hν1n⟩
  set a := (D.level n).ν⁻¹ with hadef
  have hapos : 0 < a := by linarith
  have hC0 : 0 ≤ D.K.C0 := hst.C0_pos.le
  obtain ⟨z, -, hVz, -, hα⟩ := hn.split.state
  have hV_eq : (D.level n).V τ y = rawU D.Pl (D.level n) τ y +
      ∑ i : Fin 2, ((D.level n).params D.Pl).coord z i •
        ((D.level n).params D.Pl).inlet i τ y := hVz τ y
  have hρb_eq : (D.level n).ρb D.Pl D.K = D.K.C0 * a ^ D.K.k0 * rhoRep D.K (D.level n) := by
    change UnforcedLeray.Short.IIb.rhoB ((D.level n).params D.Pl) D.K.m0 D.K.C0 D.K.k0 = _
    unfold UnforcedLeray.Short.IIb.rhoB rhoRep
    have hpow : (((D.level n).params D.Pl).ν ^ D.K.k0)⁻¹ = a ^ D.K.k0 := by
      change ((D.level n).ν ^ D.K.k0)⁻¹ = a ^ D.K.k0
      rw [inv_pow]
    rw [hpow]
    change D.K.C0 * a ^ D.K.k0 * Real.exp (D.K.m0 / (D.level n).ν) *
      (D.level n).ε ^ (3 / 11 : ℝ) = _
    ring
  have hρb_le : (D.level n).ρb D.Pl D.K ≤ D.K.C0 * a ^ D.K.k0 := by
    rw [hρb_eq]
    calc D.K.C0 * a ^ D.K.k0 * rhoRep D.K (D.level n)
        ≤ D.K.C0 * a ^ D.K.k0 * 1 :=
          mul_le_mul_of_nonneg_left hρ (by positivity)
      _ = D.K.C0 * a ^ D.K.k0 := mul_one _
  have hInlet : ∀ i : Fin 2,
      ‖((D.level n).params D.Pl).coord z i • ((D.level n).params D.Pl).inlet i τ y‖ ≤
        D.K.C0 * C2 * a ^ max k1 (D.K.k0 + k2) := by
    intro i
    have hi0 := hJ ((D.level n).params D.Pl) _ hn.regime hν0n rfl rfl i τ y
    rw [norm_iteratedFDeriv_zero] at hi0
    have hpow2 : (((D.level n).params D.Pl).ν ^ k2)⁻¹ = a ^ k2 := by
      change ((D.level n).ν ^ k2)⁻¹ = a ^ k2
      rw [inv_pow]
    rw [hpow2] at hi0
    have hαi : |((D.level n).params D.Pl).coord z i| ≤ D.K.C0 * a ^ D.K.k0 :=
      (hα i).trans hρb_le
    rw [norm_smul, Real.norm_eq_abs]
    have hmul : |((D.level n).params D.Pl).coord z i| *
        ‖((D.level n).params D.Pl).inlet i τ y‖ ≤
        (D.K.C0 * a ^ D.K.k0) * (C2 * a ^ k2) :=
      mul_le_mul hαi hi0 (norm_nonneg _) (by positivity)
    refine hmul.trans ?_
    have heq : (D.K.C0 * a ^ D.K.k0) * (C2 * a ^ k2) = D.K.C0 * C2 * a ^ (D.K.k0 + k2) := by
      rw [pow_add]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha (le_max_right _ _)) (by positivity)
  have hRaw_le : ‖rawU D.Pl (D.level n) τ y‖ ≤ |C1| * a ^ max k1 (D.K.k0 + k2) := by
    refine (hR τ y).trans ?_
    calc C1 * a ^ k1 ≤ |C1| * a ^ k1 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C1| * a ^ max k1 (D.K.k0 + k2) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha (le_max_left _ _)) (abs_nonneg _)
  have hSum_le : ‖∑ i : Fin 2, ((D.level n).params D.Pl).coord z i •
      ((D.level n).params D.Pl).inlet i τ y‖ ≤
      2 * D.K.C0 * C2 * a ^ max k1 (D.K.k0 + k2) := by
    rw [Fin.sum_univ_two]
    have h0 := hInlet 0
    have h1 := hInlet 1
    have htri := norm_add_le
      (((D.level n).params D.Pl).coord z 0 • ((D.level n).params D.Pl).inlet 0 τ y)
      (((D.level n).params D.Pl).coord z 1 • ((D.level n).params D.Pl).inlet 1 τ y)
    linarith
  rw [hV_eq]
  have htri := norm_add_le (rawU D.Pl (D.level n) τ y)
    (∑ i : Fin 2, ((D.level n).params D.Pl).coord z i • ((D.level n).params D.Pl).inlet i τ y)
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
