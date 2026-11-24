import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Annulus.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.CartLiftNormOffAxis
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.GAxFacts
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.NsSymNormLe
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChangeTQ

/-!
# `ChartPhaseNorm`: the normalized phase norm at a chart receiver

Source `the November 2 reference manuscript` 2666-2687 (chart
`s = R²/ρ²`, `q = R log(ρ/R) + Rτ/2`, `η = Rz/ρ`; "normalized phase becomes `dq/c`"),
3611-3621, 3730.

At the receiver `chartY R p` (off the axis) the lift has norm `gAx(τ, chartY R p)`
(`CartLiftNormOffAxis`). Its normalized phase norm over one period `2c/R` is computed by the
phase change `τ = 2q/R + log s` (`ChartChangeTQ`, with `Ξ = gAx(·, z)²`). On the cell
`q ∈ [-c/2, c/2)` one has `chartOf (chartY ·) (chartTau ·) = (s, (q, η))`, so
`gAx = s · |nsSym f|` there, and `|nsSym f| ≤ ‖f‖` (`NsSymNormLe`). The constant
`(2c/R)⁻¹ · (2/R) = c⁻¹`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- The chart point of `chartY` lies on the cell: `chartOf` inverts `(chartY, chartTau)`
(copied from `NearInst/Masked/Sub/FarMajorantL2/ChartL2Source.lean`). -/
private lemma cp_chartOf_chartY (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (x : Chart) (hs : 0 < x.1)
    (hq : x.2.1 ∈ Ico (-c / 2) (c / 2)) :
    chartOf R c (chartY R x) (chartTau R x) = x := by
  have hsq : 0 < Real.sqrt x.1 := Real.sqrt_pos.2 hs
  have h0 : (chartY R x) 0 = R / Real.sqrt x.1 := by simp [chartY]
  have h1 : (chartY R x) 1 = 0 := by simp [chartY]
  have h2 : (chartY R x) 2 = x.2.2 / Real.sqrt x.1 := by simp [chartY]
  have hr : hRad (chartY R x) = R / Real.sqrt x.1 := by
    unfold hRad
    rw [h0, h1, show (R / Real.sqrt x.1) ^ 2 + (0 : ℝ) ^ 2 = (R / Real.sqrt x.1) ^ 2 by ring]
    exact Real.sqrt_sq (div_nonneg hR.le hsq.le)
  have hlog : Real.log (hRad (chartY R x) / R) = -(Real.log x.1) / 2 := by
    rw [hr, show R / Real.sqrt x.1 / R = (Real.sqrt x.1)⁻¹ by field_simp, Real.log_inv,
      Real.log_sqrt hs.le]
    ring
  have hin : R * Real.log (hRad (chartY R x) / R) + R * chartTau R x / 2 = x.2.1 := by
    rw [hlog]
    unfold chartTau
    field_simp
    ring
  have hfl : ⌊x.2.1 / c + 1 / 2⌋ = 0 := by
    rw [Int.floor_eq_zero_iff, Set.mem_Ico]
    obtain ⟨hq1, hq2⟩ := hq
    constructor
    · have : -(1 / 2 : ℝ) ≤ x.2.1 / c := by
        rw [le_div_iff₀ hc]
        linarith
      linarith
    · have : x.2.1 / c < 1 / 2 := by
        rw [div_lt_iff₀ hc]
        linarith
      linarith
  unfold chartOf
  rw [hin, hfl, hr, h2]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only
    field_simp
    rw [Real.sq_sqrt hs.le]
  · simp
  · simp only
    field_simp

/-- `‖T‖² = frobSq T` for a chart tensor. -/
private lemma cp_frob (x : Ten3) : UnforcedLeray.Short.IIIa.frobSq (Ten3.toMatrix x) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [UnforcedLeray.Short.IIIa.frobSq, Ten3.toMatrix, Fintype.sum_prod_type, Fin.sum_univ_three,
    Real.norm_eq_abs, sq_abs]

/-- The pointwise bound on the cell `q ∈ [-c/2, c/2)`. -/
private lemma cp_pointwise (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (f : Chart → Ten3) (p : Chart)
    (hs : 0 < p.1) (q : ℝ) (hq : q ∈ Ico (-c / 2) (c / 2)) :
    gAx R c f (2 * q / R + Real.log p.1) (chartY R p) ^ (2 : ℝ) ≤
      ENNReal.ofReal p.1 ^ (2 : ℝ) *
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.frobSq (Ten3.toMatrix (f (p.1, (q, p.2.2))))) := by
  have hsx : 0 < (p.1, (q, p.2.2)).1 := hs
  have hqx : (p.1, (q, p.2.2)).2.1 ∈ Ico (-c / 2) (c / 2) := hq
  have hY : chartY R (p.1, (q, p.2.2)) = chartY R p := rfl
  have hT : chartTau R (p.1, (q, p.2.2)) = 2 * q / R + Real.log p.1 := rfl
  have hg : gAx R c f (chartTau R (p.1, (q, p.2.2))) (chartY R (p.1, (q, p.2.2))) =
      ENNReal.ofReal ((p.1, (q, p.2.2)).1 *
        UnforcedLeray.Short.IIIa.tensorNorm (nsSym (f (p.1, (q, p.2.2))))) := by
    unfold gAx
    rw [cp_chartOf_chartY R c hR hc (p.1, (q, p.2.2)) hsx hqx]
  have hT0 : 0 ≤ UnforcedLeray.Short.IIIa.tensorNorm (nsSym (f (p.1, (q, p.2.2)))) := by
    unfold UnforcedLeray.Short.IIIa.tensorNorm
    positivity
  have hle : UnforcedLeray.Short.IIIa.tensorNorm (nsSym (f (p.1, (q, p.2.2)))) ^ 2 ≤
      UnforcedLeray.Short.IIIa.frobSq (Ten3.toMatrix (f (p.1, (q, p.2.2)))) := by
    rw [cp_frob]
    exact pow_le_pow_left₀ hT0 (nsSymNormLe_holds (f (p.1, (q, p.2.2)))) 2
  have hTle : ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (nsSym (f (p.1, (q, p.2.2))))) ^
      (2 : ℝ) ≤
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.frobSq (Ten3.toMatrix (f (p.1, (q, p.2.2))))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hT0 (by norm_num), Real.rpow_two]
    exact ENNReal.ofReal_le_ofReal hle
  rw [← hT, ← hY, hg, ENNReal.ofReal_mul hsx.le, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  exact mul_le_mul_of_nonneg_left hTle (by positivity)

/-- **The normalized phase norm at a chart receiver** (source 2666-2687). -/
theorem chartPhaseNorm : ChartPhaseNorm := by
  intro R c hR hc f hf p hs
  obtain ⟨_, hper, hgm⟩ := gAxFacts_holds R c f hR hc hf
  have hz : hRad (chartY R p) ≠ 0 := by
    have h0 : (chartY R p) 0 = R / Real.sqrt p.1 := by simp [chartY]
    have h1 : (chartY R p) 1 = 0 := by simp [chartY]
    unfold hRad
    rw [h0, h1, show (R / Real.sqrt p.1) ^ 2 + (0 : ℝ) ^ 2 = (R / Real.sqrt p.1) ^ 2 by ring,
      Real.sqrt_sq (div_nonneg hR.le (Real.sqrt_nonneg _))]
    exact (div_pos hR (Real.sqrt_pos.2 hs)).ne'
  have hsrc : (fun τ => UnforcedLeray.Short.IIIa.srcNorm (cartLift R c f) τ (chartY R p)) =
      fun τ => gAx R c f τ (chartY R p) :=
    funext fun τ => cartLiftNormOffAxis_holds R c f τ (chartY R p) hz
  rw [hsrc]
  unfold UnforcedLeray.Short.IIIa.ltauAt
  beta_reduce
  -- Ioc to Ico
  have hIoc : ∫⁻ τ in Ioc 0 (2 * c / R), gAx R c f τ (chartY R p) ^ (2 : ℝ) =
      ∫⁻ τ in Ico 0 (2 * c / R), gAx R c f τ (chartY R p) ^ (2 : ℝ) :=
    setLIntegral_congr (Ico_ae_eq_Ioc.symm : Ioc 0 (2 * c / R) =ᵐ[volume] Ico 0 (2 * c / R))
  rw [hIoc]
  -- the phase change over one period
  have hΞm : Measurable (fun τ : ℝ => gAx R c f τ (chartY R p) ^ (2 : ℝ)) :=
    (hgm.comp (measurable_id.prodMk measurable_const)).pow_const _
  have hΞp : ∀ τ : ℝ, gAx R c f (τ + 2 * c / R) (chartY R p) ^ (2 : ℝ) =
      gAx R c f τ (chartY R p) ^ (2 : ℝ) := fun τ => by rw [hper τ (chartY R p)]
  have hCTQ := chartChangeTQ_holds R c hR hc (fun τ => gAx R c f τ (chartY R p) ^ (2 : ℝ))
    hΞm hΞp (Real.log p.1)
  beta_reduce at hCTQ
  rw [show -c / 2 = -(c / 2) by ring] at hCTQ
  rw [hCTQ]
  -- the cell integral
  have hs2 : ENNReal.ofReal p.1 ^ (2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hc' : ENNReal.ofReal c⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hJ : ∫⁻ q in Ico (-(c / 2)) (c / 2), gAx R c f (2 * q / R + Real.log p.1) (chartY R p) ^ (2 : ℝ)
      ≤ ENNReal.ofReal p.1 ^ (2 : ℝ) *
        ∫⁻ q in Ico (-(c / 2)) (c / 2),
          ENNReal.ofReal (UnforcedLeray.Short.IIIa.frobSq (Ten3.toMatrix (f (p.1, (q, p.2.2))))) := by
    rw [← lintegral_const_mul' _ _ hs2]
    refine setLIntegral_mono' measurableSet_Ico (fun q hq => ?_)
    have hq' : q ∈ Ico (-c / 2) (c / 2) := by
      rw [show -c / 2 = -(c / 2) by ring]
      exact hq
    exact cp_pointwise R c hR hc f p hs q hq'
  rw [lintegral_const_mul' _ _ hc']
  have hK : (ENNReal.ofReal (2 * c / R))⁻¹ * ENNReal.ofReal (2 / R) = ENNReal.ofReal c⁻¹ := by
    have hc0 : c ≠ 0 := hc.ne'
    have hR0 : R ≠ 0 := hR.ne'
    have hPpos : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
    have hP : ENNReal.ofReal (2 * c / R) ≠ 0 := (ENNReal.ofReal_pos.2 hPpos).ne'
    have e : 2 / R = (2 * c / R) * c⁻¹ := by field_simp
    rw [e, ENNReal.ofReal_mul hPpos.le, ← mul_assoc,
      ENNReal.inv_mul_cancel hP ENNReal.ofReal_ne_top, one_mul]
  calc ((ENNReal.ofReal (2 * c / R))⁻¹ *
          (ENNReal.ofReal (2 / R) * ∫⁻ q in Ico (-(c / 2)) (c / 2),
            gAx R c f (2 * q / R + Real.log p.1) (chartY R p) ^ (2 : ℝ))) ^ (1 / 2 : ℝ)
      = (ENNReal.ofReal c⁻¹ *
          ∫⁻ q in Ico (-(c / 2)) (c / 2),
            gAx R c f (2 * q / R + Real.log p.1) (chartY R p) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [← mul_assoc, hK]
    _ ≤ (ENNReal.ofReal c⁻¹ * (ENNReal.ofReal p.1 ^ (2 : ℝ) *
          ∫⁻ q in Ico (-(c / 2)) (c / 2),
            ENNReal.ofReal (UnforcedLeray.Short.IIIa.frobSq (Ten3.toMatrix (f (p.1, (q, p.2.2))))))) ^
          (1 / 2 : ℝ) := by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = (ENNReal.ofReal p.1 ^ (2 : ℝ) * (ENNReal.ofReal c⁻¹ *
          ∫⁻ q in Ico (-(c / 2)) (c / 2),
            ENNReal.ofReal (UnforcedLeray.Short.IIIa.frobSq (Ten3.toMatrix (f (p.1, (q, p.2.2))))))) ^
          (1 / 2 : ℝ) := by
        rw [mul_left_comm]
    _ = ENNReal.ofReal p.1 * (ENNReal.ofReal c⁻¹ *
          ∫⁻ q in Ico (-(c / 2)) (c / 2),
            ENNReal.ofReal (UnforcedLeray.Short.IIIa.frobSq (Ten3.toMatrix (f (p.1, (q, p.2.2)))))) ^
          (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num

end UnforcedLeray.Short.PartIIIb.Concrete
