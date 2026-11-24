import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2

/-!
# Decomposition of `sepGapMajorantIntegrable` (`PartIII-b:IIIb-D2/3/1/1/2/5`)

Source of record: `the November 2 reference manuscript`
3631-3646 (`sep:young` with `p = 2`: Cauchy-Schwarz in `z`, then `L²` in `τ'` and a geometric
series over periods), 3604-3621, 4155-4156 (`SepMoment` is the `Y₂ = L²_τL²_z` moment).

The majorant `l^{2Re μ+2}(1+l|z|)^{-4-n}|T(τ+2 log l, z)|` is integrated first in `z`
(Cauchy-Schwarz, after the scaling `z = w/l`, `‖(1+l|·|)^{-4-n}‖_{L²} ≲ l^{-3/2}`), then in `l`
(`l = e^s`, periodic `L²` function `f(τ') = ‖T(τ',·)‖_{L²_z}`, geometric series; `κ = 2Re μ + 3/2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The `L²_z` norm `f(τ') = (∫ |T(τ',z)|² dz)^{1/2}` of the source slice. -/
def fMom (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) : ℝ≥0∞ :=
  (∫⁻ z, IIIa.srcNorm T τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- Measurability of the majorant on `ℝ × Space` (3631-3646; `T` jointly measurable). -/
def L5Meas : Prop :=
  ∀ (μ : ℂ) (P rOut : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    IIIa.IsSepSource P rOut T → ∀ (τ : ℝ) (n : ℕ), Measurable (sepMajorant μ T τ n)

/-- Cauchy-Schwarz in `z` with the scaling `z = w/l` (3631-3646, `p = 2`):
`‖(1+l|·|)^{-(4+n)}‖_{L²} = l^{-3/2}‖(1+|·|)^{-(4+n)}‖_{L²} ≲ l^{-3/2}` (`2(4+n) > 3 = dim`). -/
def L5Holder : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ l ∈ Ioo (0 : ℝ) 1, ∀ F : Space → ℝ≥0∞, Measurable F →
    ∫⁻ z, ENNReal.ofReal ((1 + l * ‖z‖) ^ (-(4 + (n : ℝ)))) * F z ≤
      ENNReal.ofReal (C * l ^ (-(3 / 2 : ℝ))) * (∫⁻ z, F z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- Periodic block bound (3631-3646): for `g` measurable, `P`-periodic, with finite
`∫_0^P g² `, and `κ > 0`: `∫_{-∞}^0 e^{κ s} g(τ + 2 s) ds < ∞` (split into blocks of length `P/2`,
Cauchy-Schwarz on each, geometric series). -/
def L5PerSum : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ g : ℝ → ℝ≥0∞, Measurable g → (∀ τ, g (τ + P) = g τ) →
    ∫⁻ τ in Ioc 0 P, g τ ^ (2 : ℝ) < ⊤ → ∀ κ : ℝ, 0 < κ → ∀ τ : ℝ,
      ∫⁻ s in Iio (0 : ℝ), ENNReal.ofReal (Real.exp (κ * s)) * g (τ + 2 * s) < ⊤

/-- Change of variables `l = e^s` on `(0,1)` (`dl = e^s ds`, `l^a = e^{as}`). -/
def L5ChangeVar : Prop :=
  ∀ g : ℝ → ℝ≥0∞, Measurable g → ∀ (a τ : ℝ),
    ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) * g (τ + 2 * Real.log l) =
      ∫⁻ s in Iio (0 : ℝ), ENNReal.ofReal (Real.exp ((a + 1) * s)) * g (τ + 2 * s)

/-- `f = fMom T` is measurable, `P`-periodic, and `∫_0^P f² < ∞` is exactly `SepMoment`
(`ltauLq P 2 (srcNorm T) < ⊤`, 3631-3646, 4155-4156). -/
def L5Moment : Prop :=
  ∀ (P rOut : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), 0 < P → IIIa.IsSepSource P rOut T →
    SepMoment P T → Measurable (fMom T) ∧ (∀ τ, fMom T (τ + P) = fMom T τ) ∧
      ∫⁻ τ in Ioc 0 P, fMom T τ ^ (2 : ℝ) < ⊤

theorem sepGapMajorantIntegrable_of (h1 : L5Meas) (h2 : L5Holder) (h3 : L5PerSum)
    (h4 : L5ChangeVar) (h5 : L5Moment) : SepGapMajorantIntegrable := by
  intro μ P rOut T hμ hP hS hM τ n hn
  refine ⟨(h1 μ P rOut T hS τ n).aestronglyMeasurable, ?_⟩
  obtain ⟨C, hC0, hC⟩ := h2 n
  obtain ⟨hfm, hfp, hfi⟩ := h5 P rOut T hP hS hM
  set a : ℝ := 2 * μ.re + 2 - 3 / 2 with ha
  have hfin := h3 P hP (fMom T) hfm hfp hfi (a + 1) (by rw [ha]; linarith) τ
  rw [← h4 (fMom T) hfm a τ] at hfin
  have hmeas : Measurable (fun p => ENNReal.ofReal (sepMajorant μ T τ n p)) :=
    (h1 μ P rOut T hS τ n).ennreal_ofReal
  unfold HasFiniteIntegral
  have hnn : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 → 0 ≤ sepMajorant μ T τ n p := by
    intro p hp
    have := hp.1
    unfold sepMajorant IIIa.tensorNorm
    positivity
  calc ∫⁻ p, ‖sepMajorant μ T τ n p‖ₑ ∂sepRho
      = ∫⁻ p, ENNReal.ofReal (sepMajorant μ T τ n p) ∂sepRho := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_mem_Ioo_sepRho] with p hp
        exact Real.enorm_of_nonneg (hnn p hp)
    _ = ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z, ENNReal.ofReal (sepMajorant μ T τ n (l, z)) := by
        unfold sepRho
        exact lintegral_prod _ hmeas.aemeasurable
    _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal C *
          (ENNReal.ofReal (l ^ a) * fMom T (τ + 2 * Real.log l)) := by
        refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
        have hl0 : 0 < l := hl.1
        have hpt : ∀ z : Space, ENNReal.ofReal (sepMajorant μ T τ n (l, z)) =
            ENNReal.ofReal (l ^ (2 * μ.re + 2)) *
              (ENNReal.ofReal ((1 + l * ‖z‖) ^ (-(4 + (n : ℝ)))) *
                IIIa.srcNorm T (τ + 2 * Real.log l) z) := by
          intro z
          unfold sepMajorant IIIa.srcNorm
          simp only
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc]
        simp only [hpt]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have hF : Measurable (IIIa.srcNorm T (τ + 2 * Real.log l)) := by
          unfold IIIa.srcNorm IIIa.tensorNorm
          have hm : ∀ i j, Measurable fun z : Space => T (τ + 2 * Real.log l) z i j :=
            fun i j => (hS.measurable i j).comp (measurable_const.prodMk measurable_id)
          fun_prop
        have hH := hC l hl _ hF
        calc ENNReal.ofReal (l ^ (2 * μ.re + 2)) *
              ∫⁻ z, ENNReal.ofReal ((1 + l * ‖z‖) ^ (-(4 + (n : ℝ)))) *
                IIIa.srcNorm T (τ + 2 * Real.log l) z
            ≤ ENNReal.ofReal (l ^ (2 * μ.re + 2)) *
              (ENNReal.ofReal (C * l ^ (-(3 / 2 : ℝ))) * fMom T (τ + 2 * Real.log l)) :=
              mul_le_mul' le_rfl hH
          _ = ENNReal.ofReal C * (ENNReal.ofReal (l ^ a) * fMom T (τ + 2 * Real.log l)) := by
              have hpw : l ^ (2 * μ.re + 2) * (C * l ^ (-(3 / 2 : ℝ))) = C * l ^ a := by
                have : l ^ a = l ^ (2 * μ.re + 2) * l ^ (-(3 / 2 : ℝ)) := by
                  rw [← Real.rpow_add hl0, ha]; ring_nf
                rw [this]; ring
              rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hpw, ENNReal.ofReal_mul hC0,
                mul_assoc]
    _ = ENNReal.ofReal C * ∫⁻ l in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (l ^ a) * fMom T (τ + 2 * Real.log l) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end UnforcedLeray.Short.PartIIIb.Concrete
