import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_of
import UnforcedLeray.Units.B0224.FiberHeat
import UnforcedLeray.Units.B0226.Rotation
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.LerayClassEnergy

/-!
# `PepsC0SliceL2` (task `PartIII-b:C/flatset/col/7/1/1/2/4/2/3/2/1`)

Source `the November 2 reference manuscript` 1650-1656, 1676.  Strategy: Tonelli on
`measureH c = s^(-3/2) ds (cellMeasure)`, slice-wise `L²` contraction of `P0C` on the cell
`Ico (-c/2) (c/2) × ℝ`, and the periodicity in `q` to move the profile strip `(0,c] × ℝ` to the
cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem p1_vec_norm_sq (a b : ℝ) :
    ‖UnforcedLeray.Cyl.vec a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [UnforcedLeray.Cyl.vec, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

theorem p1_complex_norm_sq (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem p1_norm_toMC (v : Fin 2 → ℂ) : ‖toMC v‖ = UnforcedLeray.Short.IIIa.vnorm2 v := by
  rw [EuclideanSpace.norm_eq]
  unfold UnforcedLeray.Short.IIIa.vnorm2
  simp [toMC]

theorem p1_vnorm2_sq (z : Fin 2 → ℂ) :
    UnforcedLeray.Short.IIIa.vnorm2 z ^ 2 = ∑ i : Fin 2, ‖z i‖ ^ 2 := by
  unfold UnforcedLeray.Short.IIIa.vnorm2
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]

theorem p1_vnorm2_sq_eq_vec (z : Fin 2 → ℂ) :
    ‖UnforcedLeray.Cyl.vec (z 0).re (z 1).re‖ ^ 2 + ‖UnforcedLeray.Cyl.vec (z 0).im (z 1).im‖ ^ 2
      = UnforcedLeray.Short.IIIa.vnorm2 z ^ 2 := by
  rw [p1_vec_norm_sq, p1_vec_norm_sq, p1_vnorm2_sq, Fin.sum_univ_two,
    p1_complex_norm_sq, p1_complex_norm_sq]
  ring

/-- Pointwise contraction of `𝒫₀` in `L²(cell)`, for a real two-vector field. -/
theorem p1_P0_le (c : ℝ) (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) :
    ∫⁻ x, ENNReal.ofReal (‖UnforcedLeray.Cyl.P0 c (UnforcedLeray.Short.IIIa.toL2v c g) x‖ ^ 2)
        ∂(UnforcedLeray.Cyl.cellμ c)
      ≤ ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) := by
  by_cases h : MemLp g 2 (UnforcedLeray.Cyl.cellμ c)
  · have hT : UnforcedLeray.Short.IIIa.toL2v c g = h.toLp g := by
      unfold UnforcedLeray.Short.IIIa.toL2v
      rw [dif_pos h]
    rw [hT]
    have h2 : ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c)
        = ∫⁻ x, ENNReal.ofReal (‖h.toLp g x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) :=
      lintegral_congr_ae (h.coeFn_toLp.mono fun x hx => by simp only [hx])
    rw [h2]
    exact UnforcedLeray.Short.IIIa.ce_contract c (h.toLp g)
  · have hT : UnforcedLeray.Short.IIIa.toL2v c g = 0 := by
      unfold UnforcedLeray.Short.IIIa.toL2v
      rw [dif_neg h]
    rw [hT, map_zero]
    have h0 : ∫⁻ x, ENNReal.ofReal (‖(0 : UnforcedLeray.Cyl.L2v c) x‖ ^ 2)
        ∂(UnforcedLeray.Cyl.cellμ c) = 0 := by
      have hz : (fun x => ENNReal.ofReal (‖(0 : UnforcedLeray.Cyl.L2v c) x‖ ^ 2))
          =ᵐ[UnforcedLeray.Cyl.cellμ c] fun _ => 0 := by
        filter_upwards [Lp.coeFn_zero UnforcedLeray.Cyl.Vec2 2 (UnforcedLeray.Cyl.cellμ c)] with x hx
        have hx' : (0 : UnforcedLeray.Cyl.L2v c) x = 0 := hx.trans (Pi.zero_apply x)
        show ENNReal.ofReal (‖(0 : UnforcedLeray.Cyl.L2v c) x‖ ^ 2) = 0
        rw [hx']
        simp
      rw [lintegral_congr_ae hz]
      simp
    rw [h0]
    exact zero_le

/-- Slice-wise contraction: `∫_cell |𝒫₀ F|² ≤ ∫_cell |F|²` for `ℂ²`-valued `F`. -/
theorem p1_slice_le (c : ℝ) (F : ℝ × ℝ → Fin 2 → ℂ) (hF : ∀ i, Measurable fun x => F x i) :
    ∫⁻ x, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (UnforcedLeray.Short.IIIa.P0C c F x) ^ 2)
        ∂(UnforcedLeray.Cyl.cellμ c)
      ≤ ∫⁻ x, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (F x) ^ 2)
        ∂(UnforcedLeray.Cyl.cellμ c) := by
  have hP : ∀ x, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (UnforcedLeray.Short.IIIa.P0C c F x) ^ 2)
      = ENNReal.ofReal (‖UnforcedLeray.Short.IIIa.P0re c F x‖ ^ 2)
        + ENNReal.ofReal (‖UnforcedLeray.Short.IIIa.P0im c F x‖ ^ 2) := by
    intro x
    rw [UnforcedLeray.Short.IIIa.ce_vnorm_P0C, ENNReal.ofReal_add (by positivity) (by positivity)]
  have hR : ∀ x, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (F x) ^ 2)
      = ENNReal.ofReal (‖UnforcedLeray.Short.IIIa.reVec F x‖ ^ 2)
        + ENNReal.ofReal (‖UnforcedLeray.Short.IIIa.imVec F x‖ ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    exact (p1_vnorm2_sq_eq_vec (F x)).symm
  have hre : ∀ x, ‖UnforcedLeray.Short.IIIa.reVec F x‖ ^ 2 = (F x 0).re ^ 2 + (F x 1).re ^ 2 :=
    fun x => p1_vec_norm_sq _ _
  have him : ∀ x, ‖UnforcedLeray.Short.IIIa.imVec F x‖ ^ 2 = (F x 0).im ^ 2 + (F x 1).im ^ 2 :=
    fun x => p1_vec_norm_sq _ _
  have hmre : ∀ i, Measurable fun x => (F x i).re := fun i => Complex.measurable_re.comp (hF i)
  have hmim : ∀ i, Measurable fun x => (F x i).im := fun i => Complex.measurable_im.comp (hF i)
  have hA : Measurable fun x => ENNReal.ofReal (‖UnforcedLeray.Short.IIIa.reVec F x‖ ^ 2) := by
    simp only [hre]
    exact ENNReal.measurable_ofReal.comp (((hmre 0).pow_const 2).add ((hmre 1).pow_const 2))
  simp only [hP, hR]
  rw [lintegral_add_left' (UnforcedLeray.Short.IIIa.ce_aemeas (UnforcedLeray.Short.IIIa.P0re c F)),
    lintegral_add_left hA]
  exact add_le_add (p1_P0_le c (UnforcedLeray.Short.IIIa.reVec F))
    (p1_P0_le c (UnforcedLeray.Short.IIIa.imVec F))

/-- One-period window shift for a periodic function on `ℝ`. -/
theorem p1_window {c : ℝ} (hc : 0 < c) (F : ℝ → ℝ≥0∞) (hF : Function.Periodic F c) :
    ∫⁻ q in Ioc (-(c / 2)) (c / 2), F q = ∫⁻ q in Ioc 0 c, F q := by
  have h1 := UnforcedLeray.B0226.setLIntegral_Ioc_add_periodic hc hF (-(c / 2))
  have h2 := (measurePreserving_add_right (volume : Measure ℝ) (-(c / 2))).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight (-(c / 2))) F (Ioc (-(c / 2)) (c / 2))
  have e : c / 2 - -(c / 2) = c := by ring
  rw [preimage_add_const_Ioc, sub_self, e] at h2
  exact h2.symm.trans h1

/-- The profile strip `(0,c] × ℝ` and the centred cell `[-c/2,c/2) × ℝ` give the same integral of a
`c`-periodic (in `q`) function. -/
theorem p1_strip_cell {c : ℝ} (hc : 0 < c) (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g)
    (hper : ∀ q η, g (q + c, η) = g (q, η)) :
    ∫⁻ x in Ioc 0 c ×ˢ (univ : Set ℝ), g x
      = ∫⁻ x in Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ), g x := by
  have e : ∀ A : Set ℝ, ∫⁻ x in A ×ˢ (univ : Set ℝ), g x = ∫⁻ q in A, ∫⁻ η, g (q, η) := by
    intro A
    have hpr : (volume.restrict A).prod (volume.restrict (univ : Set ℝ))
        = (volume : Measure (ℝ × ℝ)).restrict (A ×ˢ (univ : Set ℝ)) :=
      Measure.prod_restrict A univ
    rw [← hpr, lintegral_prod _ hg.aemeasurable]
    simp only [Measure.restrict_univ]
  rw [e, e, show -c / 2 = -(c / 2) by ring]
  set F : ℝ → ℝ≥0∞ := fun q => ∫⁻ η, g (q, η) with hFdef
  have hF : Function.Periodic F c := fun q => lintegral_congr fun η => hper q η
  rw [setLIntegral_congr (Ico_ae_eq_Ioc : Ico (-(c / 2)) (c / 2) =ᵐ[volume] Ioc (-(c / 2)) (c / 2))]
  exact (p1_window hc F hF).symm

/-- Tonelli on `measureH`: the `s^(-3/2) ds` weight, then the cell integral in the plane. -/
theorem p1_tonelli {c : ℝ} (hc : 0 < c) (G : UnforcedLeray.B0220.Profile → ℝ≥0∞)
    (hG : Measurable G) (hper : ∀ s q η, G (s, (q + c, η)) = G (s, (q, η))) :
    ∫⁻ p, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * G p ∂(UnforcedLeray.B0220.cellMeasure c)
      = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ)))
          * ∫⁻ x, G (s, x) ∂(UnforcedLeray.Cyl.cellμ c) := by
  have hw : Measurable fun p : UnforcedLeray.B0220.Profile => ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
  rw [UnforcedLeray.B0224.cellMeasure_eq_prod' c,
    lintegral_prod (fun p : UnforcedLeray.B0220.Profile => ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * G p)
      ((hw.mul hG).aemeasurable)]
  refine lintegral_congr fun s => ?_
  dsimp only
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  exact p1_strip_cell hc (fun x => G (s, x)) (hG.comp measurable_prodMk_left)
    (fun q η => hper s q η)

theorem pepsC0SliceL2 : PepsC0SliceL2 := by
  intro c hc f' Φ Ψ hH
  obtain ⟨hΦm, hΨm, hΦp, hΨp, hf, hΨ⟩ := hH
  have hΦ' : Measurable Φ := measurable_pi_iff.mpr hΦm
  have hΨ' : Measurable Ψ := measurable_pi_iff.mpr hΨm
  have hTc : Continuous toMC := by
    unfold toMC
    exact PiLp.continuous_toLp 2 _
  have hTΨ : Measurable (fun p => toMC (Ψ p)) := hTc.measurable.comp hΨ'
  have hvn : Measurable fun z : Fin 2 → ℂ => UnforcedLeray.Short.IIIa.vnorm2 z := by
    unfold UnforcedLeray.Short.IIIa.vnorm2
    fun_prop
  have hGΨ : Measurable fun p => ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Ψ p) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hvn.comp hΨ').pow_const 2)
  have hGΦ : Measurable fun p => ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Φ p) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hvn.comp hΦ').pow_const 2)
  have hperΨ : ∀ s q η, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Ψ (s, (q + c, η))) ^ 2)
      = ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Ψ (s, (q, η))) ^ 2) :=
    fun s q η => by rw [hΨp s q η]
  have hperΦ : ∀ s q η, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Φ (s, (q + c, η))) ^ 2)
      = ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Φ (s, (q, η))) ^ 2) :=
    fun s q η => by rw [hΦp s q η]
  -- slice-wise comparison for a.e. `s`, here every `s > 0`
  have slice : ∀ s : ℝ, 0 < s →
      ∫⁻ x, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Ψ (s, x)) ^ 2)
          ∂(UnforcedLeray.Cyl.cellμ c)
        ≤ ∫⁻ x, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Φ (s, x)) ^ 2)
          ∂(UnforcedLeray.Cyl.cellμ c) := by
    intro s hs
    have h1 : ∫⁻ x, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Ψ (s, x)) ^ 2)
          ∂(UnforcedLeray.Cyl.cellμ c)
        = ∫⁻ x, ENNReal.ofReal
            (UnforcedLeray.Short.IIIa.vnorm2
              (UnforcedLeray.Short.IIIa.P0C c (fun y => Φ (s, y)) x) ^ 2)
            ∂(UnforcedLeray.Cyl.cellμ c) :=
      lintegral_congr_ae ((hΨ s hs).mono fun x hx => by
        simp only at hx
        simp only [hx])
    rw [h1]
    exact p1_slice_le c (fun y => Φ (s, y)) (fun i => (hΦm i).comp measurable_prodMk_left)
  have hMΨ := UnforcedLeray.B0224.lintegral_measureH_eq (c := c)
    (fun p => ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Ψ p) ^ 2)) hGΨ
  have hMΦ := UnforcedLeray.B0224.lintegral_measureH_eq (c := c)
    (fun p => ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Φ p) ^ 2)) hGΦ
  have hTΨ' := p1_tonelli hc (fun p => ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Ψ p) ^ 2))
    hGΨ hperΨ
  have hTΦ' := p1_tonelli hc (fun p => ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Φ p) ^ 2))
    hGΦ hperΦ
  have hnn : 0 ≤ᵐ[UnforcedLeray.B0220.measureH c] fun p => ‖toMC (Ψ p)‖ ^ 2 :=
    Eventually.of_forall fun p => by positivity
  have e1 : ∀ p, ENNReal.ofReal (‖toMC (Ψ p)‖ ^ 2)
      = ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Ψ p) ^ 2) := fun p => by
    rw [p1_norm_toMC]
  -- finiteness of the `Φ` side from `f' ∈ L²`
  have hfin : ∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Φ p) ^ 2)
      ∂(UnforcedLeray.B0220.measureH c) < ∞ := by
    have h1 : ∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Φ p) ^ 2)
          ∂(UnforcedLeray.B0220.measureH c)
        = ∫⁻ p, ENNReal.ofReal (‖(f' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p‖ ^ 2)
          ∂(UnforcedLeray.B0220.measureH c) :=
      lintegral_congr_ae (hf.mono fun p hp => by
        simp only at hp ⊢
        rw [hp, p1_norm_toMC])
    rw [h1]
    have hL : Integrable (fun p => ‖(f' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p‖ ^ 2)
        (UnforcedLeray.B0220.measureH c) :=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f')).1 (Lp.memLp f')
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun p => by positivity)).1 hL.2
  refine (memLp_two_iff_integrable_sq_norm hTΨ.aestronglyMeasurable).2 ⟨(hTΨ.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnn]
  simp only [e1]
  calc ∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Ψ p) ^ 2)
        ∂(UnforcedLeray.B0220.measureH c)
      = ∫⁻ p, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ)))
          * ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Ψ p) ^ 2)
          ∂(UnforcedLeray.B0220.cellMeasure c) := hMΨ
    _ = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ)))
          * ∫⁻ x, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Ψ (s, x)) ^ 2)
            ∂(UnforcedLeray.Cyl.cellμ c) := hTΨ'
    _ ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ)))
          * ∫⁻ x, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Φ (s, x)) ^ 2)
            ∂(UnforcedLeray.Cyl.cellμ c) :=
        setLIntegral_mono' measurableSet_Ioi fun s hs => mul_le_mul' le_rfl (slice s hs)
    _ = ∫⁻ p, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ)))
          * ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Φ p) ^ 2)
          ∂(UnforcedLeray.B0220.cellMeasure c) := hTΦ'.symm
    _ = ∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (Φ p) ^ 2)
          ∂(UnforcedLeray.B0220.measureH c) := hMΦ.symm
    _ < ∞ := hfin

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
