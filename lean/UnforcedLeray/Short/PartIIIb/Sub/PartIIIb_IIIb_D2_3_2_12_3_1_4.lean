import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_12_3_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.ChartBound.Leaf1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.ChartBound.Leaf2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.ChartBound.Leaf3

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/1/4`: decomposition of `StressCSRegion`

Source of record: `the November 2 reference manuscript`,
lines 2683, 2698-2700, 4284-4286.

With `f g x = Σ_{ij} (strPhys g x)_{ij} ∂_jΦ_i(x)` and the ball term
`β g x = 1_{‖x.2‖ ≤ Y} · s(x) ‖g(chartOf x)‖` (`s = (chartOf x).1 = R²/ϱ²`):

* `StressPointwise` (leaf): `‖f g x‖ ≤ B β g x` (from `StrPhysAbsLe`, norm equivalence on `Ten3`,
  boundedness and support of `dyΦ`).
* `StressBallMeasurable` (leaf): `f g` is measurable.
* `StressBallLintegral` (leaf): Cauchy-Schwarz on `phaseCell ∩ ball`, then
  `ChartOfMemStrRegion` and `RingChartRegionLintegral` applied to the *periodised* integrand
  `G'(s,(q,η)) = 1_{StrRegion Y} s² ‖g(s,(cellRep c q,η))‖ₑ²` (note `G` itself, with `g`
  arbitrary, is not `q`-periodic; `cellRep c` fixes the `q`-coordinate of `chartOf`).

`stressCSRegion_of` assembles them (Tonelli product structure of `phaseCell`, `phaseInt`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell)

/-- The stress integrand `Σ_{ij} (𝒩_T g)_{ij} ∂_jΦ_i` of `stressPair`. -/
def stressF (R c : ℝ) (g : Chart → Ten3) (Φ : ℝ × Space → CVec3) (x : ℝ × Space) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ((strPhys R c g x i j : ℝ) : ℂ) * dy j Φ x i

/-- The ball term `1_{‖y‖ ≤ Y} · s · ‖g(chartOf)‖`. -/
def stressBall (R c Y : ℝ) (g : Chart → Ten3) (x : ℝ × Space) : ℝ :=
  if ‖x.2‖ ≤ Y then (NearInst.chartOf R c x.2 x.1).1 * ‖g (NearInst.chartOf R c x.2 x.1)‖ else 0

/-- **Leaf A** (source 2683, 2698-2700; `StrPhysAbsLe`, `|nsSym T a b| ≤ C‖T‖`, `dy j Φ` bounded by
compactness of `[0,P] × closedBall` and zero for `‖y‖ > Y`): pointwise bound
`‖stressF g x‖ ≤ B · stressBall g x`, `B` independent of `g`.  Sketch: for `‖x.2‖ > Y`,
`Φ = 0` on the open set `{‖y‖ > Y}` so `dy j Φ x = 0` (`Filter.EventuallyEq.fderiv_eq`); for
`‖x.2‖ ≤ Y`, `|stressF| ≤ Σ_{ij}|strPhys_{ij}|·|dy j Φ x i|`, with `StrPhysAbsLe`
(`strPhysAbsLe_proved`) giving `s Σ_{ab}|nsSym(g(chartOf x)) a b| ≤ 9 C s ‖g(chartOf x)‖`
(`nsSym` linear on the finite-dimensional `Ten3`). -/
def StressPointwise : Prop :=
  ∀ (R c P Y : ℝ) (Φ : ℝ × Space → CVec3), 0 < R → 0 < c → P = 2 * c / R → 0 ≤ Y →
    IsPhaseTest P Φ → (∀ τ y, Y < ‖y‖ → Φ (τ, y) = 0) →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (g : Chart → Ten3) (x : ℝ × Space),
      ‖stressF R c g Φ x‖ ≤ B * stressBall R c Y g x

/-- **Leaf B** (source 2683): measurability of the stress integrand.  Sketch: `chartOf` is
measurable (floor), `cylFrame` entries are measurable, `nsSym` is linear, `dy j Φ` is continuous
(`IsPhaseTest.dy`). -/
def StressMeasurable : Prop :=
  ∀ (R c P : ℝ) (Φ : ℝ × Space → CVec3), 0 < R → 0 < c → P = 2 * c / R →
    IsPhaseTest P Φ → ∀ g : Chart → Ten3, Measurable g →
      Measurable (stressF R c g Φ)

/-- **Leaf C** (source 2698-2700, 3256-3268, 4284-4286): Cauchy-Schwarz on the phase cell with the
weight `s^{-1/2}`.  Sketch: `∫⁻_{cell} ofReal(stressBall) ≤ (∫⁻_{cell} 1_{ball} s² ‖g‖ₑ²)^{1/2}
vol(cell ∩ ball)^{1/2}` (`ENNReal.lintegral_mul_le_Lp_mul_Lq`, `ball` of finite volume); on the ball
`chartOf x ∈ StrRegion Y` (`chartOfMemStrRegion_proved`), the `q`-coordinate of `chartOf` is fixed by
`cellRep c`, so `1_{ball} s² ‖g‖ₑ² ≤ G'∘chartOf` for the `q`-periodic
`G'(s,(q,η)) = 1_{StrRegion Y} s² ‖g(s,(cellRep c q,η))‖ₑ²`; `ringChartRegionLintegral_proved`
gives `∫⁻ G'∘chartOf = ofReal P ofReal(πR²) ∫⁻_{(0,∞)×cell} ofReal(c⁻¹ s^{-5/2}) G'`, and
`s² s^{-5/2} = s^{-1/2}`, `Axi.lintegral_ageμ` identify this with
`ofReal P ofReal(πR²) ∫⁻_{StrRegion Y} ‖g‖ₑ² d ageμ c (-1/2)`. -/
def StressBallLintegral : Prop :=
  ∀ (R c P Y : ℝ), 0 < R → 0 < c → P = 2 * c / R → 0 ≤ Y →
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ g : Chart → Ten3, Measurable g →
      ∫⁻ x in phaseCell P, ENNReal.ofReal (stressBall R c Y g x) ≤
        ENNReal.ofReal K₁ *
          (∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2 : ℝ) ∂ageμ c (-1 / 2)) ^ (1 / 2 : ℝ)

/-- **`StressCSRegion` from the three leaves.** -/
theorem stressCSRegion_of (hA : StressPointwise) (hB : StressMeasurable)
    (hC : StressBallLintegral) : StressCSRegion := by
  intro R c P Y Φ hR hc hP hY hΦ hsupp
  have hP0 : 0 < P := by
    rw [hP]
    exact div_pos (mul_pos two_pos hc) hR
  obtain ⟨B, hB0, hBb⟩ := hA R c P Y Φ hR hc hP hY hΦ hsupp
  obtain ⟨K₁, hK₁0, hK₁⟩ := hC R c P Y hR hc hP hY
  refine ⟨P⁻¹ * (B * K₁), mul_nonneg (inv_nonneg.2 hP0.le) (mul_nonneg hB0 hK₁0), ?_⟩
  intro g hg hfin
  set I : ℝ≥0∞ := ∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2 : ℝ) ∂ageμ c (-1 / 2) with hI
  have hIt : I ^ (1 / 2 : ℝ) < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne
  have hlint : ∫⁻ x in phaseCell P, ‖stressF R c g Φ x‖ₑ ≤
      ENNReal.ofReal B * (ENNReal.ofReal K₁ * I ^ (1 / 2 : ℝ)) := by
    calc ∫⁻ x in phaseCell P, ‖stressF R c g Φ x‖ₑ
        ≤ ∫⁻ x in phaseCell P, ENNReal.ofReal B * ENNReal.ofReal (stressBall R c Y g x) := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul hB0, ← ofReal_norm_eq_enorm]
          exact ENNReal.ofReal_le_ofReal (hBb g x)
      _ = ENNReal.ofReal B * ∫⁻ x in phaseCell P, ENNReal.ofReal (stressBall R c Y g x) := by
          rw [lintegral_const_mul']
          exact ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr; exact hK₁ g hg
  have hlt : ∫⁻ x in phaseCell P, ‖stressF R c g Φ x‖ₑ < ⊤ :=
    lt_of_le_of_lt hlint (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hIt))
  have hmeas := hB R c P Φ hR hc hP hΦ g hg
  have hint : Integrable (stressF R c g Φ) (volume.restrict (phaseCell P)) :=
    ⟨hmeas.aestronglyMeasurable, hlt⟩
  refine ⟨hint, ?_⟩
  have hm : (volume : Measure (ℝ × Space)).restrict (phaseCell P)
      = (volume.restrict (Ioc 0 P)).prod volume := by
    rw [show phaseCell P = Ioc 0 P ×ˢ univ from rfl, Measure.volume_eq_prod,
      ← Measure.prod_restrict, Measure.restrict_univ]
  have hit : ∫ x in phaseCell P, stressF R c g Φ x =
      ∫ t in Ioc (0 : ℝ) P, ∫ y, stressF R c g Φ (t, y) := by
    rw [hm] at hint ⊢
    exact integral_prod _ hint
  have hnorm : ‖stressPair P (strPhys R c g) Φ‖ ≤
      P⁻¹ * (∫⁻ x in phaseCell P, ‖stressF R c g Φ x‖ₑ).toReal := by
    unfold stressPair phaseInt
    show ‖P⁻¹ • ∫ t in Ioc (0 : ℝ) P, ∫ y, stressF R c g Φ (t, y)‖ ≤ _
    rw [← hit, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hP0.le)]
    gcongr
    refine (norm_integral_le_lintegral_norm _).trans ?_
    simp only [ofReal_norm_eq_enorm]
    exact le_rfl
  have htr : (∫⁻ x in phaseCell P, ‖stressF R c g Φ x‖ₑ).toReal ≤
      B * (K₁ * (I ^ (1 / 2 : ℝ)).toReal) := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIt.ne)) hlint
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0,
      ENNReal.toReal_ofReal hK₁0] at this
  calc ‖stressPair P (strPhys R c g) Φ‖ ≤ _ := hnorm
    _ ≤ P⁻¹ * (B * (K₁ * (I ^ (1 / 2 : ℝ)).toReal)) := by gcongr
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
