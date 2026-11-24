import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_2
import UnforcedLeray.Short.PartIIb.Sub.T11_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_2_2.Bochner
import UnforcedLeray.Short.PartIIb.Org.QPeriodicHalfSpace.Basic

/-!
# `PartII-b:T10/7/1/2/2` (`CTPair`): decomposition

Source of record: `the November 2 reference manuscript` lines 1639-1668
(chart `s = R²/ϱ²`, `q = R log(ϱ/R) + Rτ/2`, `η = R z/ϱ`; `H = L²(s^{-3/2} ds dq/c dη)`), 1902-1921.

With `R = ε⁻¹`, `P = 2εc = 2c/R`, `Lφ c a φ (s,q,η) = Σ_n s^a φ(s, q + n c, η)` and
`G = Lφ · √s · u_i`:
* pointwise `⟨(ctLift φ) e_i, N_v u⟩ = G(chart(τ,y))` off the axis (`D1`);
* `P⁻¹ ∫_0^P ∫_y G(chart) = π R² ∫ G dageμ c (-5/2)` (`D2`, Bochner version of
  `Axi.lintegral_Nv_rpow`);
* `∫ G dageμ c (-5/2) = c⁻¹ ∫_{Coord} s^{a-2} u_i φ`, unfolding the `q`-periodization (`D3`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- The coordinate-level periodization `Σ_n s^a φ(s, q + n c, η)`. -/
def cLift (c a : ℝ) (φ : Coord → ℝ) (x : Coord) : ℝ :=
  ∑' n : ℤ, x.1 ^ a * φ (x.1, (x.2.1 + n * c, x.2.2))

/-- **`T10/7/1/2/2/1`** (SP 1902-1906; `Axi.Nv`, `B0412.realC`, `reM`, `imM`, `Axi.frameL`):
`⟨e_i(y), N_v u (τ,y)⟩ = √(age R y) u_i(chart R τ y)` off the axis (no conjugation in `dotL`). -/
def CTFrameDot : Prop :=
  ∀ (R : ℝ) (u : CProf) (i : Fin 2) (τ : ℝ) (y : Space), 0 < R → y ∉ Axi.axis →
    dotL (frameC i y) (NvC R u (τ, y)) =
      ((Real.sqrt (Axi.age R y) : ℝ) : ℂ) * u (Axi.chart R τ y) i

/-- **`T10/7/1/2/2/2`** (SP 1639-1668, Bochner version of `Axi.lintegral_Nv_rpow`, Lift.lean:143,
and `Axi.lintegral_ageμ`, Lift.lean:62): for `G` integrable for `ageμ c (-5/2)` and a.e. `q`-periodic,
`G ∘ chart` is integrable on `(0,P] × ℝ³` and
`P⁻¹ ∫_0^P ∫ G(chart R τ y) dy dτ = π R² ∫ G dageμ c (-5/2)`.  Route: reduce to a measurable
everywhere-periodic representative (null sets pull back to null sets by the lintegral identity applied
to the indicator of the `qShift`-saturation), then real/imaginary positive/negative parts and
`integral_eq_lintegral_pos_part_sub_neg_part`. -/
def PhaseChartBochner : Prop :=
  ∀ (R c P : ℝ) (G : Coord → ℂ), 0 < R → 0 < c → P = 2 * c / R →
    Integrable G (Axi.ageμ c (-(5 / 2))) →
    (∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → G (qShift c x) = G x) →
    phaseInt P (fun x => G (Axi.chart R x.1 x.2)) =
      ((Real.pi * R ^ 2 : ℝ) : ℂ) * ∫ x, G x ∂(Axi.ageμ c (-(5 / 2)))

/-- **`T10/7/1/2/2/2` proved** (SP 1639-1668): the image of `dτ|_{(0,P]} ⊗ dy` under the chart
followed by the reduction of `q` into the cell is `P π R² · ageμ c (-5/2)`
(`PhaseChartBochnerAux.map_chartRed`, from `Axi.phaseAvg_ringChart` and `Axi.lintegral_ageμ`); the
a.e. periodicity is upgraded through the `qShift`-saturated exceptional set
(`PhaseChartBochnerAux.phase_chart_integral`, `Sub/PartII-b_T10_7_1_2_2/Bochner.lean`). -/
theorem phase_chart_bochner : UnforcedLeray.Short.IIb.PhaseChartBochner := by
  intro R c P G hR hc hP hG hper
  exact PhaseChartBochnerAux.phase_chart_integral hR hc hP hG hper

/-- **`T10/7/1/2/2/3`** (SP 1639-1668; unfolding of the `q`-periodization; reuse
`coordPeriodicUnfold`, `Tasks/FlatUnique/CellStream/PeriodicUnfold.lean` and its `puc_*` helpers,
`Axi.lintegral_ageμ`, `Cyl.cell`, `AgeCell.lean`): for `φ` a coordinate test and `g` a.e.
`q`-periodic and integrable on boxes `[σ,H] × [-R,R] × [-L,L]`, `σ > 0`, the function
`G = cLift · √s · g` is `ageμ c (-5/2)`-integrable, a.e. `q`-periodic on `s>0` for `volume`, and
`∫ G dageμ c (-5/2) = c⁻¹ ∫_{Coord} s^{a-2} g φ` (the density of `ageμ c (-5/2)` is `c⁻¹ s^{-5/2}`
on `Ioi 0 × cell`; `Σ_n` unfolds `cell` to all of `ℝ_q`). -/
def CTUnfold : Prop :=
  ∀ (c a : ℝ) (φ : Coord → ℝ) (g : Coord → ℂ), 0 < c → IsCoordTest φ →
    (∀ᵐ x : Coord, g (qShift c x) = g x) →
    (∀ σ H R L : ℝ, 0 < σ → IntegrableOn g (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) volume) →
    Integrable (fun x : Coord => ((cLift c a φ x : ℝ) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) * g x)
        (Axi.ageμ c (-(5 / 2))) ∧
      (∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 →
        ((cLift c a φ (qShift c x) : ℝ) : ℂ) * ((Real.sqrt (qShift c x).1 : ℝ) : ℂ) * g (qShift c x) =
          ((cLift c a φ x : ℝ) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) * g x) ∧
      ∫ x : Coord, ((cLift c a φ x : ℝ) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) * g x
          ∂(Axi.ageμ c (-(5 / 2))) =
        ((c⁻¹ : ℝ) : ℂ) * ∫ x : Coord, (((x.1 ^ (a - 2) : ℝ)) : ℂ) * g x * (φ x : ℂ)

/-- **`CTPair` from the four chart facts** (`HrBoxIntegrable` is `T11/1/4`, `Sub/T11_1.lean`). -/
theorem ct_pair_of (hF : CTFrameDot) (hB : PhaseChartBochner) (hU : CTUnfold)
    (hBox : HrBoxIntegrable) : CTPair := by
  intro c ε r a φ u i hc hε hr1 hr3 hφ hu
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by field_simp
  set g : Coord → ℂ := fun x => u x i with hg
  -- `u` is `q`-periodic on `s > 0` only (`QPeriodic`): unfold the cut-off `g₀ = 1_{s>0} g`
  set g₀ : Coord → ℂ := {x : Coord | 0 < x.1}.indicator g with hg₀
  have hg₀pos : ∀ x : Coord, 0 < x.1 → g₀ x = g x := fun x hx =>
    Set.indicator_of_mem (show x ∈ {x : Coord | 0 < x.1} from hx) g
  have hgper : ∀ᵐ x : Coord, g₀ (qShift c x) = g₀ x := by
    refine QPerHalf.indicator_ae le_rfl ?_
    filter_upwards [QPerHalf.ae_imp hu.periodic] with x hx hx0
    simp only [hg]
    rw [hx hx0]
  have hgbox : ∀ σ H R L : ℝ, 0 < σ →
      IntegrableOn g₀ (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) volume := by
    intro σ H R L hσ
    refine (hBox c r u hc hr1 hu σ H R L hσ i).congr_fun (fun x hx => ?_)
      (measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc))
    exact (hg₀pos x (lt_of_lt_of_le hσ hx.1.1)).symm
  obtain ⟨hI₀, hper₀, hint₀⟩ := hU c a φ g₀ hc hφ hgper hgbox
  set G : Coord → ℂ := fun x => ((cLift c a φ x : ℝ) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) * g x with hG
  -- the cut-off is invisible: `√s = 0` on `s ≤ 0`, and `φ = 0` there (`IsCoordTest.supp`)
  have hGeq : (fun x : Coord => ((cLift c a φ x : ℝ) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) * g₀ x) =
      G := by
    funext x
    by_cases hx0 : 0 < x.1
    · rw [hg₀pos x hx0]
    · simp only [hG, Real.sqrt_eq_zero'.2 (not_lt.1 hx0), Complex.ofReal_zero, mul_zero,
        zero_mul]
  have hφeq : (fun x : Coord => (((x.1 ^ (a - 2) : ℝ)) : ℂ) * g₀ x * (φ x : ℂ)) =
      fun x : Coord => (((x.1 ^ (a - 2) : ℝ)) : ℂ) * g x * (φ x : ℂ) := by
    funext x
    by_cases hx0 : 0 < x.1
    · rw [hg₀pos x hx0]
    · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx0 (hφ.supp h).1)
      simp only [hφx, Complex.ofReal_zero, mul_zero]
  have hI : Integrable G (Axi.ageμ c (-(5 / 2))) := hGeq ▸ hI₀
  have hint : ∫ x : Coord, G x ∂(Axi.ageμ c (-(5 / 2))) =
      ((c⁻¹ : ℝ) : ℂ) * ∫ x : Coord, (((x.1 ^ (a - 2) : ℝ)) : ℂ) * g x * (φ x : ℂ) := by
    rw [← hφeq, ← hGeq]
    exact hint₀
  have hper' : ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → G (qShift c x) = G x := by
    filter_upwards [hper₀] with x hx hx0
    have h := hx hx0
    rw [hg₀pos (qShift c x) hx0, hg₀pos x hx0] at h
    exact h
  have hB' := hB ε⁻¹ c (2 * ε * c) G hR hc hP hI hper'
  have hpt : phaseInt (2 * ε * c)
      (fun x => dotL (((ctLift c ε a φ x : ℝ) : ℂ) • frameC i x.2) (NvC ε⁻¹ u x)) =
      phaseInt (2 * ε * c) (fun x => G (Axi.chart ε⁻¹ x.1 x.2)) := by
    unfold phaseInt
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    refine integral_congr_ae ?_
    filter_upwards [Axi.ae_not_mem_axis] with y hy
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have h1 := hF ε⁻¹ u i t y hR hy
    rw [h1]
    simp only [hG, ctLift, cLift, Axi.chart, hg]
    ring
  unfold pairF
  rw [hpt, hB', hint]
  push_cast
  ring

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.ct_pair_of
