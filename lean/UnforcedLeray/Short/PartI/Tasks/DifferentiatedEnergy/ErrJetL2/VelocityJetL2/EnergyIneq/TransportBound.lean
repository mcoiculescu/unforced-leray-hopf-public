import Mathlib.Algebra.Order.Chebyshev
import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2.EnergyIneq
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.AdvCommutator
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.AdvTop

/-!
# Part I, task `PartI:T08/2/2/2/6/3`: `CutoffJetTransportBound`

Source of record: `the November 2 reference manuscript`, lines 286-287 (top
transport term) and lines 352-353 (the commutator).
Target: `cutoffJetTransportBound_proof : CutoffJetTransportBound`
(`Sub/PartI_T08_2_2/EnergyIneq.lean`).

Route. Let `N = #wordsUpTo j`, `K₀` from `cutoffAdvTop_proof`, `Kj` from
`wordAdvCommutator_proof j`.  For `u` with `|u| ≤ j` put `g_u = ∂_u h` and
`E_u = ∂_u(b·∇h) - b·∇g_u`.  Then the integrand splits pointwise as
`χ Σ_u 2 g_u ∂_u(b·∇h) = Σ_u χ 2 g_u (b·∇g_u) + χ Σ_u 2 g_u E_u`.
* The first part: each `-∫ χ 2 g_u (b·∇g_u) ≤ K₀ c |M|³` (`CutoffAdvTop`), total `N K₀ c |M|³`.
* The second part: `|Σ_u 2 g_u E_u| ≤ 2 Kj |M| (Σ_u |g_u|)² ≤ 2 Kj |M| N Σ_u g_u²`
  (Cauchy-Schwarz), so `-∫ χ Σ_u 2 g_u E_u ≤ 2 Kj |M| N ∫ χ Σ_u g_u²`.
Then `K := N K₀ c |M|³ + 2 Kj |M| N + 1` works.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- Pointwise algebra for the remainder: the transport remainder on one point is dominated by
the `L²` energy with constant `2 K M N`. -/
theorem cjtb_pointwise_aux (s : Finset (List Bool)) (g E : List Bool → ℝ) (K M χ : ℝ)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hχ : 0 ≤ χ)
    (hE : ∀ u ∈ s, |E u| ≤ K * M * ∑ u' ∈ s, |g u'|) :
    -(χ * ∑ u ∈ s, 2 * g u * E u) ≤ (2 * K * M * (s.card : ℝ)) * (χ * ∑ u ∈ s, g u ^ 2) := by
  have hX : |∑ u ∈ s, 2 * g u * E u| ≤
      2 * (∑ u' ∈ s, |g u'|) * (K * M * ∑ u' ∈ s, |g u'|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ u ∈ s, |2 * g u * E u| ≤ ∑ u ∈ s, 2 * |g u| * (K * M * ∑ u' ∈ s, |g u'|) := by
          refine Finset.sum_le_sum (fun u hu => ?_)
          rw [abs_mul, abs_mul, abs_two]
          exact mul_le_mul_of_nonneg_left (hE u hu) (mul_nonneg (by norm_num) (abs_nonneg _))
      _ = 2 * (∑ u' ∈ s, |g u'|) * (K * M * ∑ u' ∈ s, |g u'|) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hsq : (∑ u' ∈ s, |g u'|) ^ 2 ≤ (s.card : ℝ) * ∑ u ∈ s, g u ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := s) (f := fun u => |g u|)
    simpa [sq_abs] using h
  have hKM : 0 ≤ 2 * K * M := mul_nonneg (mul_nonneg (by norm_num) hK) hM
  have hmain : 2 * (∑ u' ∈ s, |g u'|) * (K * M * ∑ u' ∈ s, |g u'|) ≤
      (2 * K * M * (s.card : ℝ)) * ∑ u ∈ s, g u ^ 2 := by
    have e1 : 2 * (∑ u' ∈ s, |g u'|) * (K * M * ∑ u' ∈ s, |g u'|) =
        (2 * K * M) * (∑ u' ∈ s, |g u'|) ^ 2 := by ring
    rw [e1]
    have h2 := mul_le_mul_of_nonneg_left hsq hKM
    calc (2 * K * M) * (∑ u' ∈ s, |g u'|) ^ 2
        ≤ (2 * K * M) * ((s.card : ℝ) * ∑ u ∈ s, g u ^ 2) := h2
      _ = (2 * K * M * (s.card : ℝ)) * ∑ u ∈ s, g u ^ 2 := by ring
  have hneg : -(χ * ∑ u ∈ s, 2 * g u * E u) ≤ χ * |∑ u ∈ s, 2 * g u * E u| := by
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left (neg_le_abs _) hχ
  calc -(χ * ∑ u ∈ s, 2 * g u * E u) ≤ χ * |∑ u ∈ s, 2 * g u * E u| := hneg
    _ ≤ χ * ((2 * K * M * (s.card : ℝ)) * ∑ u ∈ s, g u ^ 2) :=
        mul_le_mul_of_nonneg_left (hX.trans hmain) hχ
    _ = (2 * K * M * (s.card : ℝ)) * (χ * ∑ u ∈ s, g u ^ 2) := by ring

theorem cutoffJetTransportBound_proof : UnforcedLeray.Short.PartI.CutoffJetTransportBound := by
  obtain ⟨K₀, hK₀, hTop⟩ := cutoffAdvTop_proof
  intro j
  obtain ⟨Kj, hKj, hComm⟩ := wordAdvCommutator_proof j
  intro c M hc
  have hN : (0 : ℝ) ≤ ((wordsUpTo j).card : ℝ) := Nat.cast_nonneg _
  refine ⟨((wordsUpTo j).card : ℝ) * K₀ * c * |M| ^ 3 + 2 * Kj * |M| * ((wordsUpTo j).card : ℝ) + 1,
    ?_, ?_⟩
  · exact add_nonneg
      (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hN hK₀) hc.le) (pow_nonneg (abs_nonneg M) 3))
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKj) (abs_nonneg M)) hN))
      zero_le_one
  intro R hR1 b h hb hh hbp hhp hdiv hbM hhM
  have hR0 : 0 < R := by linarith
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hbM [] 0 (Nat.zero_le _) (0, 0))
  rw [abs_of_nonneg hM0]
  have hbM1 : ∀ z : Plane, |b z 1| ≤ M := fun z => hbM [] 1 (Nat.zero_le _) z
  have hgs : ∀ u : List Bool, ContDiff ℝ ∞ (B0151.derivWord u h) :=
    fun u => B0151.contDiff_derivWord hh u
  have hDs : ContDiff ℝ ∞ (scalarAdv b h) := vjl_scalarAdv_contDiff hb hh
  have hgsA : ∀ u : List Bool, ContDiff ℝ ∞ (scalarAdv b (B0151.derivWord u h)) :=
    fun u => vjl_scalarAdv_contDiff hb (hgs u)
  have hDu : ∀ u : List Bool, ContDiff ℝ ∞ (B0151.derivWord u (scalarAdv b h)) :=
    fun u => B0151.contDiff_derivWord hDs u
  have hgper : ∀ u : List Bool, Cyl.IsPeriodic c (B0151.derivWord u h) := by
    intro u z
    exact B0151.periodic_derivWord (fun q η => hhp (q, η)) u z.1 z.2
  -- integrability of the top terms `χ · 2 g_u (b·∇g_u)`
  have hQint : ∀ u ∈ wordsUpTo j, IntegrableOn (fun z : Plane => etaCutoff R z.2 *
      (2 * B0151.derivWord u h z * scalarAdv b (B0151.derivWord u h) z)) (Cyl.cell c) := by
    intro u _
    have hcont : Continuous (fun z : Plane =>
        2 * B0151.derivWord u h z * scalarAdv b (B0151.derivWord u h) z) :=
      (continuous_const.mul (hgs u).continuous).mul (hgsA u).continuous
    exact vjl_cutoff_integrable hR0 hcont
  have hQsum : IntegrableOn (fun z : Plane => ∑ u ∈ wordsUpTo j, etaCutoff R z.2 *
      (2 * B0151.derivWord u h z * scalarAdv b (B0151.derivWord u h) z)) (Cyl.cell c) :=
    integrable_finsetSum (wordsUpTo j) hQint
  -- integrability of the remainder `χ Σ_u 2 g_u E_u`
  have hEcont : ∀ u : List Bool, Continuous (fun z : Plane =>
      B0151.derivWord u (scalarAdv b h) z - scalarAdv b (B0151.derivWord u h) z) :=
    fun u => (hDu u).continuous.sub (hgsA u).continuous
  have hRcont : Continuous (fun z : Plane => ∑ u ∈ wordsUpTo j,
      2 * B0151.derivWord u h z * (B0151.derivWord u (scalarAdv b h) z -
        scalarAdv b (B0151.derivWord u h) z)) :=
    continuous_finsetSum _ (fun u _ => (continuous_const.mul (hgs u).continuous).mul (hEcont u))
  have hRint : IntegrableOn (fun z : Plane => etaCutoff R z.2 * ∑ u ∈ wordsUpTo j,
      2 * B0151.derivWord u h z * (B0151.derivWord u (scalarAdv b h) z -
        scalarAdv b (B0151.derivWord u h) z)) (Cyl.cell c) :=
    vjl_cutoff_integrable hR0 hRcont
  -- the integrand splits as the top part plus the remainder
  have hsplit_int : (∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ wordsUpTo j,
        2 * B0151.derivWord u h z * B0151.derivWord u (scalarAdv b h) z)
      = (∫ z in Cyl.cell c, ∑ u ∈ wordsUpTo j, etaCutoff R z.2 *
          (2 * B0151.derivWord u h z * scalarAdv b (B0151.derivWord u h) z))
        + ∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ wordsUpTo j,
          2 * B0151.derivWord u h z * (B0151.derivWord u (scalarAdv b h) z -
            scalarAdv b (B0151.derivWord u h) z) := by
    rw [← integral_add hQsum hRint]
    congr 1
    funext z
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    ring
  -- top part: `-∫ Σ_u χ 2 g_u (b·∇g_u) ≤ N K₀ c M³`
  have hA : -(∫ z in Cyl.cell c, ∑ u ∈ wordsUpTo j, etaCutoff R z.2 *
        (2 * B0151.derivWord u h z * scalarAdv b (B0151.derivWord u h) z))
      ≤ ((wordsUpTo j).card : ℝ) * (K₀ * c * M ^ 3) := by
    rw [integral_finsetSum (wordsUpTo j) hQint, ← Finset.sum_neg_distrib]
    have hle : ∀ u ∈ wordsUpTo j, -(∫ z in Cyl.cell c, etaCutoff R z.2 *
        (2 * B0151.derivWord u h z * scalarAdv b (B0151.derivWord u h) z)) ≤ K₀ * c * M ^ 3 :=
      fun u hu => hTop c R M b (B0151.derivWord u h) hc hR1 hb (hgs u) hbp (hgper u) hdiv
        hbM1 (fun z => hhM u (mem_wordsUpTo.1 hu) z)
    calc _ ≤ ∑ u ∈ wordsUpTo j, K₀ * c * M ^ 3 := Finset.sum_le_sum hle
      _ = ((wordsUpTo j).card : ℝ) * (K₀ * c * M ^ 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- remainder: `-∫ χ Σ_u 2 g_u E_u ≤ 2 K M N ∫ χ Σ_u g_u²`
  have hF_int : IntegrableOn (fun z : Plane => etaCutoff R z.2 *
      ∑ u ∈ wordsUpTo j, B0151.derivWord u h z ^ 2) (Cyl.cell c) :=
    vjl_cutoff_integrable hR0
      (continuous_finsetSum _ (fun u _ => ((hgs u).continuous).pow 2))
  have hF_nonneg : 0 ≤ ∫ z in Cyl.cell c, etaCutoff R z.2 *
      ∑ u ∈ wordsUpTo j, B0151.derivWord u h z ^ 2 :=
    integral_nonneg (fun z => mul_nonneg (etaCutoff_nonneg R z.2)
      (Finset.sum_nonneg (fun u _ => sq_nonneg _)))
  have hpw : ∀ z : Plane,
      -(etaCutoff R z.2 * ∑ u ∈ wordsUpTo j,
          2 * B0151.derivWord u h z * (B0151.derivWord u (scalarAdv b h) z -
            scalarAdv b (B0151.derivWord u h) z))
        ≤ (2 * Kj * M * ((wordsUpTo j).card : ℝ)) * (etaCutoff R z.2 *
            ∑ u ∈ wordsUpTo j, B0151.derivWord u h z ^ 2) := by
    intro z
    exact cjtb_pointwise_aux (wordsUpTo j) (fun u => B0151.derivWord u h z)
      (fun u => B0151.derivWord u (scalarAdv b h) z - scalarAdv b (B0151.derivWord u h) z)
      Kj M (etaCutoff R z.2) hKj hM0 (etaCutoff_nonneg R z.2)
      (fun u hu => hComm M b h hb hh hbM u (mem_wordsUpTo.1 hu) z)
  have hRm_bound : -(∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ wordsUpTo j,
          2 * B0151.derivWord u h z * (B0151.derivWord u (scalarAdv b h) z -
            scalarAdv b (B0151.derivWord u h) z))
      ≤ (2 * Kj * M * ((wordsUpTo j).card : ℝ)) * ∫ z in Cyl.cell c, etaCutoff R z.2 *
          ∑ u ∈ wordsUpTo j, B0151.derivWord u h z ^ 2 := by
    rw [← integral_neg, ← integral_const_mul]
    exact integral_mono (Integrable.neg hRint) (Integrable.const_mul hF_int _) (fun z => hpw z)
  -- bookkeeping of the constants
  have hKMN : 0 ≤ 2 * Kj * M * ((wordsUpTo j).card : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKj) hM0) hN
  have hNK : 0 ≤ ((wordsUpTo j).card : ℝ) * K₀ * c * M ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg hN hK₀) hc.le) (pow_nonneg hM0 3)
  have hmul : (2 * Kj * M * ((wordsUpTo j).card : ℝ)) * (∫ z in Cyl.cell c, etaCutoff R z.2 *
          ∑ u ∈ wordsUpTo j, B0151.derivWord u h z ^ 2) ≤
      (((wordsUpTo j).card : ℝ) * K₀ * c * M ^ 3 + 2 * Kj * M * ((wordsUpTo j).card : ℝ) + 1) *
        (∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ wordsUpTo j, B0151.derivWord u h z ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ hF_nonneg
    linarith
  linarith [hsplit_int, hA, hRm_bound, hmul, hKMN, hNK]

end UnforcedLeray.Short.PartI
