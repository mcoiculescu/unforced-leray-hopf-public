import UnforcedLeray.Short.PartIIa.Sub.N01.Defs
import UnforcedLeray.Units.B0223.Dilation
import UnforcedLeray.Lib.FreeStressCouplings.ProdLp

/-!
# `PartII-a:N01/1`: the phase lift exists (lines 1339-1343, 1639-1643)

Composite of the normalised dilation `B0223.dilN ε`, the swap, the scalar change of measure
`volume(ℝ/Pℤ) = P • haar` (an isometry `L²(P • ν) → L²(ν)` multiplying by `√P`), and the Fubini
isometry `FreeStress.prodLpEquiv`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa.N01

/-- Change of measure by a positive constant: `L²(μ') ≅ L²(ν)` with `μ' = c • ν`, the identity
on functions multiplied by `√c`. -/
theorem scaleLp_exists {α : Type*} [MeasurableSpace α] (ν μ' : Measure α)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {c : ℝ} (hc : 0 < c)
    (hμ : μ' = ENNReal.ofReal c • ν) :
    ∃ T : Lp E 2 μ' →ₗᵢ[ℂ] Lp E 2 ν,
      ∀ f : Lp E 2 μ', ∀ᵐ x ∂ν, (T f : α → E) x = ((Real.sqrt c : ℝ) : ℂ) • (f : α → E) x := by
  subst hμ
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hctop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hback : ∀ {p : α → Prop}, (∀ᵐ x ∂(ENNReal.ofReal c • ν), p x) → ∀ᵐ x ∂ν, p x :=
    fun h => (Measure.ae_ennreal_smul_measure_iff hc0).1 h
  have hle : ν ≤ (ENNReal.ofReal c)⁻¹ • (ENNReal.ofReal c • ν) := by
    rw [smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul]
  have hmem : ∀ f : Lp E 2 (ENNReal.ofReal c • ν),
      MemLp (fun x => ((Real.sqrt c : ℝ) : ℂ) • (f : α → E) x) 2 ν := fun f =>
    ((Lp.memLp f).of_measure_le_smul (ENNReal.inv_ne_top.mpr hc0) hle).const_smul _
  have key : ∀ f : Lp E 2 (ENNReal.ofReal c • ν),
      ∀ᵐ x ∂ν, ((hmem f).toLp _ : α → E) x = ((Real.sqrt c : ℝ) : ℂ) • (f : α → E) x := by
    intro f
    filter_upwards [MemLp.coeFn_toLp (hmem f)] with x hx
    exact hx
  let T0 : Lp E 2 (ENNReal.ofReal c • ν) →ₗ[ℂ] Lp E 2 ν :=
    { toFun := fun f => (hmem f).toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        show ((hmem (f + g)).toLp _ : α → E) =ᵐ[ν]
          (((hmem f).toLp _ + (hmem g).toLp _ : Lp E 2 ν) : α → E)
        filter_upwards [key (f + g), key f, key g, Lp.coeFn_add ((hmem f).toLp _) ((hmem g).toLp _),
          hback (Lp.coeFn_add f g)] with x h1 h2 h3 h5 h4
        rw [h1, h5, Pi.add_apply, h2, h3, h4, Pi.add_apply, smul_add]
      map_smul' := by
        intro a f
        apply Lp.ext
        show ((hmem (a • f)).toLp _ : α → E) =ᵐ[ν]
          (((a • (hmem f).toLp _ : Lp E 2 ν)) : α → E)
        filter_upwards [key (a • f), key f, hback (Lp.coeFn_smul a f),
          Lp.coeFn_smul a ((hmem f).toLp _)] with x h1 h2 h3 h4
        rw [h1, h3, Pi.smul_apply, h4, Pi.smul_apply, h2]
        exact smul_comm _ _ _ }
  refine ⟨{ toLinearMap := T0, norm_map' := ?_ }, key⟩
  intro f
  show ‖(hmem f).toLp _‖ = ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  have e1 : eLpNorm (fun x => ((Real.sqrt c : ℝ) : ℂ) • (f : α → E) x) 2 ν =
      ‖((Real.sqrt c : ℝ) : ℂ)‖ₑ * eLpNorm (f : α → E) 2 ν :=
    eLpNorm_const_smul _ _ _ _
  have e2 : eLpNorm (f : α → E) 2 (ENNReal.ofReal c • ν) =
      (ENNReal.ofReal c) ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm (f : α → E) 2 ν :=
    eLpNorm_smul_measure_of_ne_zero hc0 _ _ _
  have e0 : ‖((Real.sqrt c : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (Real.sqrt c) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg c)]
  have h12 : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by norm_num
  rw [e1, e2, e0, h12, ENNReal.ofReal_rpow_of_nonneg hc.le (by norm_num), Real.sqrt_eq_rpow]

/-- **`PartII-a:N01/1`**: the phase lift exists. -/
theorem phaseLiftExists : PhaseLiftExists := by
  intro ε P _ hε
  have hP0 : (0 : ℝ) < P := Fact.out
  have hμ : (volume : Measure (AddCircle P)).prod (volume : Measure Space) =
      ENNReal.ofReal P • ((AddCircle.haarAddCircle (T := P)).prod (volume : Measure Space)) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.prod_smul_left]
  obtain ⟨T, hT⟩ := scaleLp_exists (E := UnforcedLeray.B0223.SpaceC) ((AddCircle.haarAddCircle (T := P)).prod (volume : Measure Space))
    ((volume : Measure (AddCircle P)).prod (volume : Measure Space)) hP0 hμ
  have hsw : MeasurePreserving (Prod.swap : AddCircle P × Space → Space × AddCircle P)
      ((volume : Measure (AddCircle P)).prod (volume : Measure Space))
      (volume : Measure (UnforcedLeray.B0223.PSpace P)) :=
    MeasureTheory.Measure.measurePreserving_swap
  let G : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P →ₗᵢ[ℂ]
      Lp UnforcedLeray.B0223.SpaceC 2 ((volume : Measure (AddCircle P)).prod (volume : Measure Space)) :=
    Lp.compMeasurePreservingₗᵢ (E := UnforcedLeray.B0223.SpaceC) (p := 2) ℂ
      (Prod.swap : AddCircle P × Space → Space × AddCircle P) hsw
  let D : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P →ₗᵢ[ℂ]
      UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P :=
    { toLinearMap := (UnforcedLeray.B0223.dilN ε : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P
        →L[ℂ] UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P).toLinearMap
      norm_map' := fun u => UnforcedLeray.B0223.norm_dilN_apply ε u }
  let Ulin : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P →ₗᵢ[ℂ]
      UnforcedLeray.PhaseSpace.Yq P 2 :=
    (UnforcedLeray.FreeStress.prodLpEquiv (F := UnforcedLeray.B0223.SpaceC) (q := 2)
      (ν := AddCircle.haarAddCircle (T := P)) (μ := (volume : Measure Space))).toLinearIsometry.comp
      ((T.comp G).comp D)
  refine ⟨Ulin, ?_⟩
  intro F
  -- the a.e. formula for the composite dilation, swap and scaling
  have hmeas : ∀ p : AddCircle P × Space → Prop,
      (∀ᵐ w ∂((volume : Measure (AddCircle P)).prod (volume : Measure Space)), p w) →
        ∀ᵐ w ∂((AddCircle.haarAddCircle (T := P)).prod (volume : Measure Space)), p w := by
    intro p h
    have h' : ∀ᵐ w ∂(ENNReal.ofReal P • ((AddCircle.haarAddCircle (T := P)).prod
        (volume : Measure Space))), p w := by
      rw [← hμ]
      exact h
    exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr hP0).ne').1 h'
  have hG : ∀ᵐ w ∂((AddCircle.haarAddCircle (T := P)).prod (volume : Measure Space)),
      (G (D F)) w = (ε ^ (3 / 2 : ℝ) : ℝ) • F (ε • w.2, w.1) := by
    refine hmeas _ ?_
    have h1 : ∀ᵐ w ∂((volume : Measure (AddCircle P)).prod (volume : Measure Space)),
        (G (D F)) w = (D F) (Prod.swap w) :=
      Lp.coeFn_compMeasurePreserving (D F) hsw
    have h2 : ∀ᵐ w ∂((volume : Measure (AddCircle P)).prod (volume : Measure Space)),
        (D F) (Prod.swap w) = (ε ^ (3 / 2 : ℝ) : ℝ) • F (ε • w.2, w.1) := by
      filter_upwards [hsw.quasiMeasurePreserving.ae (UnforcedLeray.B0223.coeFn_dilN hε F)]
        with w hw
      exact hw
    filter_upwards [h1, h2] with w hw1 hw2
    rw [hw1, hw2]
  have hall : ∀ᵐ z ∂((AddCircle.haarAddCircle (T := P)).prod (volume : Measure Space)),
      (T (G (D F))) z = ((Real.sqrt P : ℝ) : ℂ) • ((ε ^ (3 / 2 : ℝ) : ℝ) • F (ε • z.2, z.1)) := by
    filter_upwards [hT (G (D F)), hG] with z h1 h2
    rw [h1, h2]
  filter_upwards [UnforcedLeray.FreeStress.prodLpEquiv_ae (T (G (D F))),
    Measure.ae_ae_of_ae_prod hall] with θ h1 h2
  refine h1.trans ?_
  filter_upwards [h2] with y hy
  rw [hy]
  rw [← Complex.coe_smul, smul_smul, Complex.ofReal_mul]

end UnforcedLeray.Short.PartIIa.N01
