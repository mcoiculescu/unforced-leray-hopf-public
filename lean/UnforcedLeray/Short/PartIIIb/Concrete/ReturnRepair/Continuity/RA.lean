import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.FA
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.EA
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.SrcPairing
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressMapWeakSol.Closed.PairLinearPh
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WeakDmuAdd

/-!
# The leaf `RACont`: `𝔯_A` is norm continuous in `μ` (source 5001-5050, 5703)

Source of record: `the November 2 reference manuscript` (73 pages).

`𝔯_A` is pinned by `IsRAOp`: for every phase test `Φ`,
`⟨(L₀ᵗ+μ)Φ, ĥ_A⟩ - ⟨M ĥ_A, ∇Φ⟩ = ⟨Φ, F_A + E_A + 𝔯_A⟩ - ⟨sΨ_A, div Φ⟩` (5001-5008).  Only the
first pairing depends on `μ`, and affinely.  For window points `μ₁ ≠ μ₂` and the affine weight
`t(μ)` the pairings of `X(μ) := F_A + E_A + 𝔯_A` against every phase test are therefore affine in
`μ` with the same weights; phase tests separate body forces (`srcPairingNondeg`), so
`X(μ) = (1-t) X(μ₁) + t X(μ₂)`.  Then `𝔯_A(μ) = X(μ) - F_A(μ) - E_A(μ)` is continuous by
`faCont`, `eaCont`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete (pairF)
open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Linearity of the pairing in the body force (second slot) -/

/-- `pairF Φ (𝒩_v ·)` is real-linear on `SrcG c` (from `pairLinearPh`). -/
theorem pairF_velPhys_lin {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest (2 * ε * c) Φ) (f g h : SrcG c) (a b : ℝ) (hh : h = a • f + b • g) :
    pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (h : Chart → Merid)) =
      (a : ℂ) * pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (f : Chart → Merid)) +
        (b : ℂ) * pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (g : Chart → Merid)) := by
  obtain ⟨hadd, hsmul, hcongr⟩ := NearInst.pairLinearPh c ε hc hε Φ hΦ
  have fm : Measurable (f : Chart → Merid) := (Lp.stronglyMeasurable f).measurable
  have gm : Measurable (g : Chart → Merid) := (Lp.stronglyMeasurable g).measurable
  have fL := SrcPairing.sp_memLp_ageμ f
  have gL := SrcPairing.sp_memLp_ageμ g
  have haf : Measurable (a • (f : Chart → Merid)) := fm.const_smul a
  have hbg : Measurable (b • (g : Chart → Merid)) := gm.const_smul b
  have hafL : MemLp (a • (f : Chart → Merid)) 2 (ageμ c (-3 / 2)) := fL.const_smul a
  have hbgL : MemLp (b • (g : Chart → Merid)) 2 (ageμ c (-3 / 2)) := gL.const_smul b
  have hae : (h : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      a • (f : Chart → Merid) + b • (g : Chart → Merid) := by
    have hπ : ENNReal.ofReal Real.pi ≠ 0 := (ENNReal.ofReal_pos.2 Real.pi_pos).ne'
    have h1 : (h : Chart → Merid) =ᵐ[srcMeasure c]
        a • (f : Chart → Merid) + b • (g : Chart → Merid) := by
      rw [hh]
      filter_upwards [Lp.coeFn_add (a • f) (b • g), Lp.coeFn_smul a f, Lp.coeFn_smul b g]
        with p h1 h2 h3
      rw [h1, Pi.add_apply, h2, h3]
      rfl
    unfold srcMeasure at h1
    rwa [Filter.EventuallyEq, Measure.ae_ennreal_smul_measure_iff hπ] at h1
  rw [hcongr _ _ (haf.add hbg) hae, hadd _ _ haf hbg hafL hbgL, hsmul a _ fm fL,
    hsmul b _ gm gL]
  simp only [Complex.real_smul]

/-! ## 2. Affinity of the first pairing in `μ` -/

theorem pairF_smul_left {P : ℝ} (m : ℂ) (Φ u : ℝ × Space → CVec3) :
    pairF P (fun x => m • Φ x) u = m * pairF P Φ u := by
  unfold pairF phaseInt
  have h1 : ∀ x, dotL (m • Φ x) (u x) = m * dotL (Φ x) (u x) := fun x => by
    rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp only [h1, integral_const_mul]
  exact (mul_smul_comm _ _ _).symm

theorem pairF_L0T_mu {c γ ν ε : ℝ} (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest (2 * ε * c) Φ) (b : VelG c γ ν) (μ : ℝ) :
    pairF (2 * ε * c) (fun x => L0T ν Φ x + (μ : ℂ) • Φ x)
        (velPhys ε⁻¹ c (b : Chart → Merid)) =
      pairF (2 * ε * c) (L0T ν Φ) (velPhys ε⁻¹ c (b : Chart → Merid)) +
        (μ : ℂ) * pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (b : Chart → Merid)) := by
  have hP0 : 0 < 2 * ε * c := by positivity
  haveI : Fact (0 < 2 * ε * c) := ⟨hP0⟩
  have hbm : Measurable (b : Chart → Merid) := (Lp.stronglyMeasurable b).measurable
  have hbL := wda_memLp_age (c := c) (γ := γ) hν b
  have hint : ∀ Ψ : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) Ψ →
      Integrable (fun x => dotL (Ψ x) (velPhys ε⁻¹ c (b : Chart → Merid) x))
        (volume.restrict (phaseCell (2 * ε * c))) := fun Ψ hΨ =>
    (NearInst.pairBoundPh c ε hc hε Ψ hΨ).choose_spec _ hbm hbL |>.1
  have h1 := hint _ (isPhaseTest_L0T hΦ ν)
  have h2 := hint _ hΦ
  have h3 := hint _ (isPhaseTest_L0T_add (μ := μ) (ν := ν) hΦ)
  have h2' : Integrable (fun x => dotL ((μ : ℂ) • Φ x) (velPhys ε⁻¹ c (b : Chart → Merid) x))
      (volume.restrict (phaseCell (2 * ε * c))) := by
    refine (h2.const_mul (μ : ℂ)).congr (Eventually.of_forall fun x => ?_)
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [pairF_add_left_of_integrable (F := L0T ν Φ) (G := fun x => (μ : ℂ) • Φ x) h1 h2' h3,
    pairF_smul_left]

/-! ## 3. The combination of the three pinned identities -/

theorem rAOp_comb_aux {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] {M : VelG c γ ν →L[ℝ] StrG c mZ ρb γ ν} {hA : Aff →L[ℝ] VelG c γ ν}
    {ι : Aff →ₗ[ℝ] (ℝ → Mat3)} {χf : ℝ → ℝ} {ε : ℝ} (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε)
    {FA₀ EA₀ r₀ FA₁ EA₁ r₁ FA₂ EA₂ r₂ : Aff →L[ℝ] SrcG c} {μ₀ μ₁ μ₂ t : ℝ}
    (hlin : (1 - t) * μ₁ + t * μ₂ = μ₀)
    (h₀ : IsRAOp M hA FA₀ EA₀ r₀ ι χf ε μ₀) (h₁ : IsRAOp M hA FA₁ EA₁ r₁ ι χf ε μ₁)
    (h₂ : IsRAOp M hA FA₂ EA₂ r₂ ι χf ε μ₂) :
    FA₀ + EA₀ + r₀ = (1 - t) • (FA₁ + EA₁ + r₁) + t • (FA₂ + EA₂ + r₂) := by
  ext1 A
  simp only [add_apply, smul_apply]
  refine srcPairingNondeg c ε hc hε _ _ fun Φ hΦ => ?_
  have k₀ := h₀ A Φ hΦ
  have k₁ := h₁ A Φ hΦ
  have k₂ := h₂ A Φ hΦ
  rw [pairF_L0T_mu hc hν hε hΦ] at k₀ k₁ k₂
  have hl := pairF_velPhys_lin hc hε hΦ (FA₁ A + EA₁ A + r₁ A) (FA₂ A + EA₂ A + r₂ A)
    ((1 - t) • (FA₁ A + EA₁ A + r₁ A) + t • (FA₂ A + EA₂ A + r₂ A)) (1 - t) t rfl
  rw [hl]
  have hμ : (μ₀ : ℂ) = (1 - (t : ℂ)) * μ₁ + t * μ₂ := by
    rw [← hlin]; push_cast; ring
  rw [hμ] at k₀
  simp only [Complex.ofReal_sub, Complex.ofReal_one] at hl ⊢
  linear_combination (-1 : ℂ) * k₀ + (1 - (t : ℂ)) * k₁ + (t : ℂ) * k₂

/-! ## 4. The leaf -/

/-- **`𝔯_A` is norm continuous in `μ`** (source 5001-5050, 5703). -/
theorem SeqData.raCont (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.RACont := by
  have hνlt : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (Iio_mem_nhds zero_lt_one)
  filter_upwards [hst.pins, hνlt, SeqData.faCont D hst, SeqData.eaCont D hst]
    with n hpins hlt hFA hEA
  have hνpos : 0 < (D.level n).ν := (D.level n).ν_pos
  have hL : 0 < |Real.log (D.level n).ν| :=
    abs_pos.mpr (Real.log_neg hνpos hlt).ne
  have hpos : (0 : ℝ) < 2 * |Real.log (D.level n).ν| := by linarith
  have hdiv : (0 : ℝ) < 1 / (2 * |Real.log (D.level n).ν|) := one_div_pos.mpr hpos
  have hneg : (-1 : ℝ) / (2 * |Real.log (D.level n).ν|)
      = -(1 / (2 * |Real.log (D.level n).ν|)) := by ring
  have hlt12 : D.mu n (-1) < D.mu n 1 := by
    show D.σ₀ + (-1 : ℝ) / (2 * |Real.log (D.level n).ν|)
      < D.σ₀ + 1 / (2 * |Real.log (D.level n).ν|)
    rw [hneg]
    linarith
  have hne : D.mu n (-1) ≠ D.mu n 1 := ne_of_lt hlt12
  have hpin : ∀ z ∈ Icc (-1 : ℝ) 1, IsRAOp (multOp D.Pl D.K (D.level n))
      (hAOp D.Pl D.K (D.level n)) (FAOp D.K (D.level n) (D.mu n z))
      (EAOp D.K (D.level n) (D.mu n z)) (rAOp D.Pl D.K (D.level n) (D.mu n z))
      (affIota D.K.as) D.K.χf (D.level n).ε (D.mu n z) :=
    fun z hz => Classical.epsilon_spec (hpins z hz).rA
  have hp₁ := hpin (-1) ⟨le_rfl, by norm_num⟩
  have hp₂ := hpin 1 ⟨by norm_num, le_rfl⟩
  set X₁ := FAOp D.K (D.level n) (D.mu n (-1)) + EAOp D.K (D.level n) (D.mu n (-1))
    + rAOp D.Pl D.K (D.level n) (D.mu n (-1)) with hX₁
  set X₂ := FAOp D.K (D.level n) (D.mu n 1) + EAOp D.K (D.level n) (D.mu n 1)
    + rAOp D.Pl D.K (D.level n) (D.mu n 1) with hX₂
  have hcont : ContinuousOn (fun μ : ℝ =>
      ((1 - (μ - D.mu n (-1)) / (D.mu n 1 - D.mu n (-1))) • X₁
        + ((μ - D.mu n (-1)) / (D.mu n 1 - D.mu n (-1))) • X₂)
        - FAOp D.K (D.level n) μ - EAOp D.K (D.level n) μ) (D.win n) := by
    refine ContinuousOn.sub (ContinuousOn.sub ?_ hFA) hEA
    exact (by fun_prop : Continuous fun μ : ℝ =>
      (1 - (μ - D.mu n (-1)) / (D.mu n 1 - D.mu n (-1))) • X₁
        + ((μ - D.mu n (-1)) / (D.mu n 1 - D.mu n (-1))) • X₂).continuousOn
  refine hcont.congr ?_
  rintro μ ⟨z, hz, rfl⟩
  have h := rAOp_comb_aux (cOf_pos (D.level n).ν_pos) (D.level n).ν_pos (D.level n).ε_pos
    (affine_weight_fa hne) (hpin z hz) hp₁ hp₂
  have h' : FAOp D.K (D.level n) (D.mu n z) + EAOp D.K (D.level n) (D.mu n z)
      + rAOp D.Pl D.K (D.level n) (D.mu n z) = (1 - (D.mu n z - D.mu n (-1)) /
        (D.mu n 1 - D.mu n (-1))) • X₁ + ((D.mu n z - D.mu n (-1)) /
        (D.mu n 1 - D.mu n (-1))) • X₂ := h
  show _ = _ - _ - _
  rw [← h']
  abel

end UnforcedLeray.Short.PartIIIb.Concrete
