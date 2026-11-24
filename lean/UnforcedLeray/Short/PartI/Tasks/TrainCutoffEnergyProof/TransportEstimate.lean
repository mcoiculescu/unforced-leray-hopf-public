import UnforcedLeray.Short.PartI.Sub.T05b_2

/-!
# Part I, task `PartI:T05b/2/4`: the transport estimate (leaf `TransportEstimate`)

Source of record: `the November 2 reference manuscript`, lines 276-288.
Target: `transportEstimate : TransportEstimate` (`Short/PartI/Sub/T05b_2.lean`). The four hypotheses
`EtaCutoffFacts`, `CellIntegrableOfSupport`, `TrainSliceSmooth`, `DiffEnergyBound` are black boxes.

Route. Fix `S ≥ 0`, `R ≥ 1`, `s ∈ [0, S]`, `w = diffV tr tr' s`, `φ = etaCutoff R`, `C₀` from
`EtaCutoffFacts`, and `M ≥ 0` from `TrainBoundedBy` (at age `0`). Then

* `|v₁| ≤ ‖v‖ ≤ M` (`PiLp.norm_apply_le`);
* `|φ'| ≤ (C₀/R) √φ ≤ C₀/R` (since `0 ≤ φ ≤ 1`);
* `∫_cell ‖w‖² ≤ 4M` (`DiffEnergyBound`).

Hence `transportRhs = ∫ ‖w‖² v₁ φ' ≤ (C₀M/R) ∫ ‖w‖² ≤ 4C₀M²/R ≤ 4C₀M²/√R`, using `√R ≤ R`
for `R ≥ 1`. The constant is `K = 4 C₀ M²`. The integrand is continuous and vanishes for
`2R ≤ |η|` (there `φ = 0`, so `φ' = 0`), so `CellIntegrableOfSupport` gives integrability.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- **`PartI:T05b/2/4`, target `TransportEstimate`.** -/
theorem transportEstimate (hη : EtaCutoffFacts) (hI : CellIntegrableOfSupport)
    (hS : TrainSliceSmooth) (hE : DiffEnergyBound) : TransportEstimate := by
  unfold EtaCutoffFacts at hη
  obtain ⟨C₀, hC₀, hφ⟩ := hη
  unfold TransportEstimate
  intro ν c hν hc tr tr' S M hS0 hb hb'
  -- `M ≥ 0`, from `‖v(0, z)‖ ≤ M`
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) ((hb 0 ⟨le_rfl, hS0⟩).1 0)
  refine ⟨4 * C₀ * M ^ 2, mul_nonneg (mul_nonneg (by norm_num) hC₀) (sq_nonneg M), ?_⟩
  intro R hR s hs
  have hRpos : 0 < R := by linarith
  have hs0 : 0 ≤ s := hs.1
  obtain ⟨hφS, hφ01, -, hφ0, hφd⟩ := hφ R hR
  -- continuity of the slices, the difference, the component, and `φ'`
  have hvS : Continuous (tr.v s) := (hS ν c tr s hs0).1.continuous
  have hv'S : Continuous (tr'.v s) := (hS ν c tr' s hs0).1.continuous
  have hwS : Continuous (diffV tr tr' s) := by
    unfold diffV
    exact hvS.sub hv'S
  have hV1 : Continuous fun z : Plane => tr.v s z 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).continuous.comp hvS
  have hD : Continuous fun z : Plane => deriv (etaCutoff R) z.2 :=
    (hφS.continuous_deriv (by simp)).comp continuous_snd
  -- the transport integrand is continuous and vanishes for `2R ≤ |η|`
  have hcont : Continuous fun z : Plane =>
      ‖diffV tr tr' s z‖ ^ 2 * tr.v s z 1 * deriv (etaCutoff R) z.2 :=
    ((hwS.norm.pow 2).mul hV1).mul hD
  have hzero : ∀ z : Plane, 2 * R ≤ |z.2| →
      ‖diffV tr tr' s z‖ ^ 2 * tr.v s z 1 * deriv (etaCutoff R) z.2 = 0 := by
    intro z hz
    have h0 : deriv (etaCutoff R) z.2 = 0 := by
      have h := hφd z.2
      rw [hφ0 z.2 hz, Real.sqrt_zero, mul_zero] at h
      exact abs_nonpos_iff.mp h
    rw [h0, mul_zero]
  have hgI : IntegrableOn
      (fun z : Plane => ‖diffV tr tr' s z‖ ^ 2 * tr.v s z 1 * deriv (etaCutoff R) z.2)
      (Cyl.cell c) :=
    hI c R hc hRpos _ hcont hzero
  -- pointwise majorant: `|v₁| ≤ M` and `|φ'| ≤ C₀/R`
  have hpt : ∀ z : Plane,
      ‖diffV tr tr' s z‖ ^ 2 * tr.v s z 1 * deriv (etaCutoff R) z.2 ≤
        ‖diffV tr tr' s z‖ ^ 2 * (M * (C₀ / R)) := by
    intro z
    have ha : 0 ≤ ‖diffV tr tr' s z‖ ^ 2 := by positivity
    have hv1 : |tr.v s z 1| ≤ M := by
      have h1 : ‖tr.v s z 1‖ ≤ ‖tr.v s z‖ := PiLp.norm_apply_le (tr.v s z) 1
      rw [Real.norm_eq_abs] at h1
      exact h1.trans ((hb s hs).1 z)
    have hs1 : Real.sqrt (etaCutoff R z.2) ≤ 1 := by
      have h := Real.sqrt_le_sqrt (hφ01 z.2).2
      rwa [Real.sqrt_one] at h
    have hd1 : |deriv (etaCutoff R) z.2| ≤ C₀ / R :=
      (hφd z.2).trans (mul_le_of_le_one_right (div_nonneg hC₀ hRpos.le) hs1)
    have hkey : |‖diffV tr tr' s z‖ ^ 2 * tr.v s z 1 * deriv (etaCutoff R) z.2| ≤
        ‖diffV tr tr' s z‖ ^ 2 * (M * (C₀ / R)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha]
      calc ‖diffV tr tr' s z‖ ^ 2 * |tr.v s z 1| * |deriv (etaCutoff R) z.2|
          ≤ ‖diffV tr tr' s z‖ ^ 2 * M * (C₀ / R) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hv1 ha) hd1 (abs_nonneg _)
              (mul_nonneg ha hM0)
        _ = ‖diffV tr tr' s z‖ ^ 2 * (M * (C₀ / R)) := by ring
    exact (le_abs_self _).trans hkey
  -- the majorant is integrable, with integral at most `(4M)(M C₀/R)`
  have hmajI : IntegrableOn (fun z : Plane => ‖diffV tr tr' s z‖ ^ 2 * (M * (C₀ / R)))
      (Cyl.cell c) :=
    Integrable.mul_const (hE ν c hc tr tr' S M hb hb' s hs).1 _
  have hmono : ∫ z in Cyl.cell c, ‖diffV tr tr' s z‖ ^ 2 * tr.v s z 1 * deriv (etaCutoff R) z.2 ≤
      ∫ z in Cyl.cell c, ‖diffV tr tr' s z‖ ^ 2 * (M * (C₀ / R)) :=
    integral_mono hgI hmajI (fun z => hpt z)
  have hconst : ∫ z in Cyl.cell c, ‖diffV tr tr' s z‖ ^ 2 * (M * (C₀ / R)) =
      (∫ z in Cyl.cell c, ‖diffV tr tr' s z‖ ^ 2) * (M * (C₀ / R)) :=
    integral_mul_const (M * (C₀ / R)) (fun z : Plane => ‖diffV tr tr' s z‖ ^ 2)
  rw [hconst] at hmono
  have hbd : (∫ z in Cyl.cell c, ‖diffV tr tr' s z‖ ^ 2) * (M * (C₀ / R)) ≤
      (4 * M) * (M * (C₀ / R)) :=
    mul_le_mul_of_nonneg_right (hE ν c hc tr tr' S M hb hb' s hs).2
      (mul_nonneg hM0 (div_nonneg hC₀ hRpos.le))
  have hEq : (4 * M) * (M * (C₀ / R)) = 4 * C₀ * M ^ 2 / R := by ring
  -- `√R ≤ R` for `R ≥ 1`
  have hsqR : Real.sqrt R ≤ R := by
    have h1 : 1 ≤ Real.sqrt R := Real.one_le_sqrt.mpr hR
    have h2 : Real.sqrt R * Real.sqrt R = R := Real.mul_self_sqrt hRpos.le
    nlinarith [Real.sqrt_nonneg R]
  have hsqpos : 0 < Real.sqrt R := Real.sqrt_pos.mpr hRpos
  have hfin : 4 * C₀ * M ^ 2 / R ≤ 4 * C₀ * M ^ 2 / Real.sqrt R :=
    div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg (by norm_num) hC₀) (sq_nonneg M))
      hsqpos hsqR
  unfold transportRhs
  exact hmono.trans (hbd.trans (hEq.le.trans hfin))

end UnforcedLeray.Short.PartI
