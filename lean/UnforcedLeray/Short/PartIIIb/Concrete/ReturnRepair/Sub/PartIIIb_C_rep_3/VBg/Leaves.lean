import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VBg.VSq

/-!
# The two background leaves of (H) and the reduction of `RepVBg` to them (`PartIII-b:C/rep/3/4`)

Source of record: `the November 2 reference manuscript` (73 pages), lines
5131-5139, 5225-5235, 5245-5247, 5255-5258, 2607-2612, 2641-2642, 5461-5464.

`RepVBg` (`Sub/PartIII-b_C_rep_3.lean`) is reduced (`repVBg_of_jet_presGrad`) to:

* `RepVJetY2` (source 5234-5235 `R⁻¹(‖DV‖_2 + ‖D²V‖_2) ≤ P_ν`, from the chart jets
  `DU_raw = s(D_flat v + εC₁)`, `D²U_raw = s^{3/2}(D²_flat v + εC₂)` with the weighted train bounds,
  5461-5464, and `‖E_εα‖_{W^{j,∞}} ≤ P_ν|α|` with the compact-age support of the inlet, 2347-2387):
  the derivative part of the thin-coefficient density;
* `RepPresGradY2` (`Sub/PartIII-b_C_rep_3_4.lean`; source 5245-5247, 2607-2612, 2641-2642): the
  `Y_2` bound `R⁻¹‖∇p‖_{Y_2} ≤ P_ν` of the exact pressure, which is `RepVPres` with `p_V = p`
  (`repVPres_of_presGradY2`).

The `V ⊗ V` part of the thin-coefficient bound is proved (`VBgSq.repVBg_vSq`, from
`IIIa.StressCoefficients`), and the smoothness, `vEtaSup` and measurability clauses are proved in
`Sub/PartIII-b_C_rep_3_4.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The jet density `Σ_j|∂_jV| + Σ_{j,l}|∂_j∂_lV|`: the derivative part of `vCoefDens`
(source 5234-5235). -/
def vJetDens (V : Space → Space) (y : Space) : ℝ :=
  ∑ j : Fin 3, ‖physPd V j y‖ + ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 V j l y‖

/-- **Leaf: the derivative part of the thin-coefficient bound** (source 5234-5235:
`R⁻¹(‖DV‖_{Y_2} + ‖D²V‖_{Y_2}) ≤ P_ν`, with 5131-5139, 2607-2612 and the chart jets of the raw lift
5461-5464), in the ring-chart form of `RepVCoefY2`, eventually along the sequence. -/
def RepVJetY2 (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop,
    ENNReal.ofReal (D.level n).ε *
        eLpNorm (ringRead (D.level n).ε⁻¹ fun τ => vJetDens ((D.level n).V τ)) 2
          (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν)) ≤
      ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k)

namespace VBgSq

theorem vCoefDens_eq (V : Space → Space) (y : Space) :
    vCoefDens V y = ‖V y‖ ^ 2 + vJetDens V y := by
  unfold vCoefDens vJetDens
  ring

/-- `RepVCoefY2` from the derivative leaf and the proved `V ⊗ V` part (triangle inequality in
`L²`; both densities are continuous off the axis). -/
theorem repVCoefY2_of_jet (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hJ : RepVJetY2 D) : RepVCoefY2 D := by
  obtain ⟨C₁, k₁, hC₁, hsq⟩ := repVBg_vSq D hst
  obtain ⟨C₂, k₂, hjet⟩ := hJ
  refine ⟨C₁ + |C₂|, max k₁ k₂, ?_⟩
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  filter_upwards [hle, repVBg_contDiffOn D hst, hsq, hjet] with n hν hV2 h1 h2
  have hν0 : 0 < (D.level n).ν := (D.level n).ν_pos
  have hR : (D.level n).ε⁻¹ ≠ 0 := inv_ne_zero (D.level n).ε_pos.ne'
  have hc : 0 < cOf (D.level n).ν := cOf_pos hν0
  rw [vr_offAxis_eq] at hV2
  obtain ⟨f0, f1, f2⟩ := jet_continuousOn isOpen_offAxis hV2
  have hA : AEStronglyMeasurable (ringRead (D.level n).ε⁻¹ fun τ y => ‖(D.level n).V τ y‖ ^ 2)
      (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν)) :=
    aestronglyMeasurable_ringRead (g := fun x : ℝ × Space => ‖(D.level n).V x.1 x.2‖ ^ 2) hR hc
      (f0.norm.pow 2)
  have hB : AEStronglyMeasurable (ringRead (D.level n).ε⁻¹ fun τ => vJetDens ((D.level n).V τ))
      (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν)) := by
    refine aestronglyMeasurable_ringRead
      (g := fun x : ℝ × Space => vJetDens ((D.level n).V x.1) x.2) hR hc ?_
    unfold vJetDens
    refine ContinuousOn.add ?_ ?_
    · exact continuousOn_finsetSum _ fun j _ => (f1 j).norm
    · exact continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun l _ => (f2 j l).norm
  have hsplit : (ringRead (D.level n).ε⁻¹ fun τ => vCoefDens ((D.level n).V τ)) =
      (ringRead (D.level n).ε⁻¹ fun τ y => ‖(D.level n).V τ y‖ ^ 2) +
        ringRead (D.level n).ε⁻¹ fun τ => vJetDens ((D.level n).V τ) := by
    funext p
    simp only [ringRead, Pi.add_apply, vCoefDens_eq]
  unfold RepVCoefY2At
  rw [hsplit]
  calc ENNReal.ofReal (D.level n).ε *
        eLpNorm ((ringRead (D.level n).ε⁻¹ fun τ y => ‖(D.level n).V τ y‖ ^ 2) +
          ringRead (D.level n).ε⁻¹ fun τ => vJetDens ((D.level n).V τ)) 2
          (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν))
      ≤ ENNReal.ofReal (D.level n).ε *
          (eLpNorm (ringRead (D.level n).ε⁻¹ fun τ y => ‖(D.level n).V τ y‖ ^ 2) 2
              (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν)) +
            eLpNorm (ringRead (D.level n).ε⁻¹ fun τ => vJetDens ((D.level n).V τ)) 2
              (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν))) := by
        gcongr
        exact eLpNorm_add_le hA hB (by norm_num)
    _ = ENNReal.ofReal (D.level n).ε *
            eLpNorm (ringRead (D.level n).ε⁻¹ fun τ y => ‖(D.level n).V τ y‖ ^ 2) 2
              (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν)) +
          ENNReal.ofReal (D.level n).ε *
            eLpNorm (ringRead (D.level n).ε⁻¹ fun τ => vJetDens ((D.level n).V τ)) 2
              (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν)) := mul_add _ _ _
    _ ≤ ENNReal.ofReal (C₁ * (D.level n).ν⁻¹ ^ k₁) +
          ENNReal.ofReal (C₂ * (D.level n).ν⁻¹ ^ k₂) := add_le_add h1 h2
    _ ≤ ENNReal.ofReal ((C₁ + |C₂|) * (D.level n).ν⁻¹ ^ max k₁ k₂) := by
        have hC0 : 0 ≤ C₁ + |C₂| := by positivity
        have e1 : C₁ * (D.level n).ν⁻¹ ^ k₁ ≤ C₁ * (D.level n).ν⁻¹ ^ max k₁ k₂ := by
          simpa using pnu_le_pnu hν0 hν.1 zero_le_one le_rfl hC₁ (le_max_left k₁ k₂)
        have e2 : C₂ * (D.level n).ν⁻¹ ^ k₂ ≤ |C₂| * (D.level n).ν⁻¹ ^ max k₁ k₂ := by
          simpa using pnu_le_pnu hν0 hν.1 zero_le_one (le_abs_self C₂) (abs_nonneg C₂)
            (le_max_right k₁ k₂)
        have hP : 0 ≤ (D.level n).ν⁻¹ ^ max k₁ k₂ := by positivity
        calc ENNReal.ofReal (C₁ * (D.level n).ν⁻¹ ^ k₁) +
              ENNReal.ofReal (C₂ * (D.level n).ν⁻¹ ^ k₂)
            ≤ ENNReal.ofReal (C₁ * (D.level n).ν⁻¹ ^ max k₁ k₂) +
                ENNReal.ofReal (|C₂| * (D.level n).ν⁻¹ ^ max k₁ k₂) :=
              add_le_add (ENNReal.ofReal_le_ofReal e1) (ENNReal.ofReal_le_ofReal e2)
          _ = ENNReal.ofReal ((C₁ + |C₂|) * (D.level n).ν⁻¹ ^ max k₁ k₂) := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1
              ring

/-- **Reduction of (H)**: `RepVBg` from the derivative leaf `RepVJetY2` and the pressure leaf
`RepPresGradY2` (source 5131-5139, 5225-5235, 5245-5247, 5255-5258, 2607-2612, 2641-2642). -/
theorem repVBg_of_jet_presGrad (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hJ : RepVJetY2 D) (hP : RepPresGradY2 D) : RepVBg D :=
  repVBg_of D hst (repVCoefY2_of_jet D hst hJ) (repVPres_of_presGradY2 D hst hP)

/-- **Reduction of (H)** with the general pressure leaf `RepVPres` (any `C¹` pressure `p_V`). -/
theorem repVBg_of_jet (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hJ : RepVJetY2 D) (hP : RepVPres D) : RepVBg D :=
  repVBg_of D hst (repVCoefY2_of_jet D hst hJ) hP

end VBgSq

end UnforcedLeray.Short.PartIIIb.Concrete

end
