import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VResidual.JetTerm
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VResidual.DivTerm
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu

/-!
# `VResidual` (`PartIII-b:C/rep/3/2`, source 5224-5253)

Assembles `VResidualOf` from the measurability of the three pieces (`VResidual/Meas.lean`),
the `2 V · ∇Y` age-surface/chart bound (`VResidual/DivTerm.lean`), and the
`2 ν C_diff(V, X) + (V ⊗ V) : D²X` and `(DX + DXᵀ) ∇p_V` jet bounds (`VResidual/JetTerm.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- One-regime `V`-residual estimate from `RepAgeSurfAt` and `RepVBgAt` with nonnegative
constants `C₁, C₂ ≥ 0`. -/
theorem vResidualAt_of {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    {pV : ℝ → Space → ℝ} (hν1 : L.ν ≤ 1) (hχy : IsYoungCutoff K.χy) (hμ : -(1 / 4 : ℝ) < μ)
    (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) {k₁ k₂ : ℕ}
    (hA : RepAgeSurfAt Pl K L μ C₁ k₁) (hBg : RepVBgAt K L pV C₂ k₂) :
    VResidualAt Pl K L μ pV (1 + 67 * C₁ * C₂) (k₁ + k₂ + 3) := by
  intro w
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hνinv1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  obtain ⟨hVC2, hpVC1, hVeta, _, hVcoef, hpVgrad, _, _⟩ := hBg
  obtain ⟨hDivm, hJVm, hJPm, hDYm⟩ := vr_meas_pieces hχy hμ hC0 hmZ hVC2 hpVC1 w
  set c := cOf L.ν
  set R := L.ε⁻¹
  set X := repX Pl K L μ w
  set Y := repY Pl K L μ w
  set F1 := coefOf R (vrDiv L.V Y)
  set F2 := coefOf R (vrJetV L.ν L.V X)
  set F3 := coefOf R (vrJetP X pV)
  have hsum : coefOf R (wardEXY L.ν μ R L.V pV X Y) = F1 + (F2 + F3) :=
    coefOf_wardEXY_eq_vr_sum L.ν μ R L.V pV X Y
  have hF1m : AEStronglyMeasurable F1 (srcMeasure c) := hDivm.aestronglyMeasurable
  have hMeas : AEStronglyMeasurable (coefOf R (wardEXY L.ν μ R L.V pV X Y)) (srcMeasure c) := by
    rw [hsum]
    exact hF1m.add (hJVm.add hJPm)
  refine ⟨hMeas, ?_⟩
  set Fr := phaseL2Lr (2 * L.ε * c) (22 / 19) (repStressPhys Pl K L w)
  by_cases hFr : Fr = ⊤
  · have hpos : 0 < (1 + 67 * C₁ * C₂) * L.ν⁻¹ ^ (k₁ + k₂ + 3) * L.ε ^ (101 / 22 : ℝ) := by
      have : 0 < 1 + 67 * C₁ * C₂ := by positivity
      positivity
    have hne0 : ENNReal.ofReal ((1 + 67 * C₁ * C₂) * L.ν⁻¹ ^ (k₁ + k₂ + 3) *
        L.ε ^ (101 / 22 : ℝ)) ≠ 0 := (ENNReal.ofReal_pos.2 hpos).ne'
    change eLpNorm (coefOf R (wardEXY L.ν μ R L.V pV X Y)) 2 (srcMeasure c) ≤
      ENNReal.ofReal ((1 + 67 * C₁ * C₂) * L.ν⁻¹ ^ (k₁ + k₂ + 3) * L.ε ^ (101 / 22 : ℝ)) * Fr
    rw [hFr, ENNReal.mul_top hne0]
    exact le_top
  · obtain ⟨hA1, hA2⟩ := hA w
    have hA1_Y : ∀ s : ℝ, 0 < s → L.ν * s ≤ 1 →
        ageSurfL2 (2 * L.ε * c) R s (fun τ y => ‖fderiv ℝ (Y τ) y‖) ≤
          ENNReal.ofReal (C₁ * L.ν⁻¹ ^ k₁ * L.ε ^ (101 / 22 : ℝ) * s ^ (101 / 44 : ℝ)) * Fr := by
      intro s hs hνs
      have h1 := hA1 s hs hνs
      dsimp only [c, R, X, Y, Fr] at h1 ⊢
      exact le_add_self.trans h1
    have hB1 : eLpNorm F1 2 (srcMeasure c) ≤
        ENNReal.ofReal (4 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂ + 3) * L.ε ^ (101 / 22 : ℝ)) * Fr :=
      vr_div_bound_of hν1 hχy hC₁ hC₂ hFr hDivm hDYm hA1_Y hVeta
    obtain ⟨hB2, hB3⟩ := vr_jet_bounds_of (μ := μ) hν1 hC₁ hC₂ hA2 hVcoef hpVgrad hFr
    have hpow : L.ν⁻¹ ^ (k₁ + k₂) ≤ L.ν⁻¹ ^ (k₁ + k₂ + 3) :=
      pow_le_pow_right₀ hνinv1 (by omega)
    have hreal : 4 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂ + 3) * L.ε ^ (101 / 22 : ℝ) +
        (45 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂) * L.ε ^ (101 / 22 : ℝ) +
        18 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂) * L.ε ^ (101 / 22 : ℝ)) ≤
        (1 + 67 * C₁ * C₂) * L.ν⁻¹ ^ (k₁ + k₂ + 3) * L.ε ^ (101 / 22 : ℝ) := by
      have h63 : 63 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂) * L.ε ^ (101 / 22 : ℝ) ≤
          63 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂ + 3) * L.ε ^ (101 / 22 : ℝ) := by
        gcongr
      have h1pos : 0 ≤ 1 * L.ν⁻¹ ^ (k₁ + k₂ + 3) * L.ε ^ (101 / 22 : ℝ) := by positivity
      linarith
    change eLpNorm (coefOf R (wardEXY L.ν μ R L.V pV X Y)) 2 (srcMeasure c) ≤
      ENNReal.ofReal ((1 + 67 * C₁ * C₂) * L.ν⁻¹ ^ (k₁ + k₂ + 3) * L.ε ^ (101 / 22 : ℝ)) * Fr
    rw [hsum]
    calc eLpNorm (F1 + (F2 + F3)) 2 (srcMeasure c)
        ≤ eLpNorm F1 2 (srcMeasure c) + eLpNorm (F2 + F3) 2 (srcMeasure c) :=
          eLpNorm_add_le hF1m (hJVm.add hJPm) one_le_two
      _ ≤ eLpNorm F1 2 (srcMeasure c) +
            (eLpNorm F2 2 (srcMeasure c) + eLpNorm F3 2 (srcMeasure c)) :=
          add_le_add le_rfl (eLpNorm_add_le hJVm hJPm one_le_two)
      _ ≤ ENNReal.ofReal (4 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂ + 3) * L.ε ^ (101 / 22 : ℝ)) * Fr +
            (ENNReal.ofReal (45 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂) * L.ε ^ (101 / 22 : ℝ)) * Fr +
              ENNReal.ofReal (18 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂) * L.ε ^ (101 / 22 : ℝ)) * Fr) :=
          add_le_add hB1 (add_le_add hB2 hB3)
      _ = ENNReal.ofReal (4 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂ + 3) * L.ε ^ (101 / 22 : ℝ) +
            (45 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂) * L.ε ^ (101 / 22 : ℝ) +
              18 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂) * L.ε ^ (101 / 22 : ℝ))) * Fr := by
          rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal ((1 + 67 * C₁ * C₂) * L.ν⁻¹ ^ (k₁ + k₂ + 3) * L.ε ^ (101 / 22 : ℝ)) *
            Fr :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl

/-- **`VResidualOf`** (`PartIII-b:C/rep/3/2`, source 5224-5253). -/
theorem vResidualOf : VResidualOf := by
  intro D dm dp hst hAS C₂ k₂
  obtain ⟨C₁, k₁, hAS'⟩ := hAS
  set C₁' : ℝ := max C₁ 0
  set C₂' : ℝ := max C₂ 0
  have hC₁' : 0 ≤ C₁' := le_max_right _ _
  have hC₂' : 0 ≤ C₂' := le_max_right _ _
  have hC₁le : C₁ ≤ C₁' := le_max_left _ _
  have hC₂le : C₂ ≤ C₂' := le_max_left _ _
  have hχy : IsYoungCutoff D.K.χy :=
    ⟨hst.chiY.smooth, hst.chiY.one, hst.chiY.zero, hst.chiY.range⟩
  refine ⟨1 + 67 * C₁' * C₂', k₁ + k₂ + 3, ?_⟩
  have hev := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  have hμev := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  filter_upwards [hAS', hev, hμev] with n hAn h2 hμn z hz pV hBg
  have hν1 : (D.level n).ν ≤ 1 := h2.1
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hμ : -(1 / 4 : ℝ) < D.mu n z := by linarith [(hμn z hz).1, hst.sigma_pos]
  have hA' : RepAgeSurfAt D.Pl D.K (D.level n) (D.mu n z) C₁' k₁ := by
    intro w
    obtain ⟨h1, h2'⟩ := hAn z hz w
    refine ⟨fun s hs hνs => (h1 s hs hνs).trans ?_, fun τ y => (h2' τ y).trans ?_⟩
    · refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      gcongr
    · refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      gcongr
  have hBg' : RepVBgAt D.K (D.level n) pV C₂' k₂ := by
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := hBg
    refine ⟨b1, b2, fun s hs => (b3 s hs).trans ?_, b4, b5.trans ?_, b6.trans ?_, b7, b8.trans ?_⟩
    · exact ENNReal.ofReal_le_ofReal (by gcongr)
    · exact ENNReal.ofReal_le_ofReal (by gcongr)
    · exact ENNReal.ofReal_le_ofReal (by gcongr)
    · have hρ0 := rhoRep_nonneg D.K (D.level n)
      exact ENNReal.ofReal_le_ofReal (by gcongr)
  exact vResidualAt_of hν1 hχy hμ hst.C0_pos (by linarith [hst.mZ_gt]) hC₁' hC₂' hA' hBg'

end UnforcedLeray.Short.PartIIIb.Concrete

end
