import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_1
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.TransportIdentity
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.CellToolkit

/-!
# Part I, `PartI:T04/10/1/2/1/10` (`CutoffAdvTopL2`)

Source of record: `the November 2 reference manuscript`, lines 286-287.
Route: `tp_core` with the test field `w = (g, 0)` gives
`-2∫χ⟨w, (b·∇)w⟩ = ∫ g² b₁ χ'`; `|χ'| ≤ C₀/R` and `|b₁| ≤ M` give the pointwise bound
`|g² b₁ χ'| ≤ (C₀/R) M g²`, which integrates to the claim with `C₂ = C₀`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

theorem cutoffAdvTopL2_proof : CutoffAdvTopL2 := by
  obtain ⟨C₀, hC₀, hφ⟩ := etaCutoffFacts
  refine ⟨C₀, hC₀, ?_⟩
  intro c R M b g hc hR1 hb hg hbp hgp hdiv hbM hg2
  have hRpos : 0 < R := by linarith
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hbM 0)
  have hK : 0 ≤ C₀ / R := div_nonneg hC₀ hRpos.le
  obtain ⟨hφS, hφ01, -, hφ0, hφd⟩ := hφ R hR1
  have hφ1 : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
    intro η hη
    have h1 := hφd η
    rw [hφ0 η hη, Real.sqrt_zero, mul_zero, abs_nonpos_iff] at h1
    exact h1
  -- the derivative bound `|χ'| ≤ C₀/R`
  have hd : ∀ η : ℝ, |deriv (etaCutoff R) η| ≤ C₀ / R := by
    intro η
    have hs1 : Real.sqrt (etaCutoff R η) ≤ 1 := by
      have h := Real.sqrt_le_sqrt (hφ01 η).2
      rwa [Real.sqrt_one] at h
    exact (hφd η).trans (mul_le_of_le_one_right hK hs1)
  -- the test field `w = (g, 0)`
  have hwC : ContDiff ℝ ∞ (fun z : Plane => Train.toVec (g z, 0)) :=
    Train.toVecL.contDiff.comp (hg.prodMk contDiff_const)
  have hwP : Cyl.IsPeriodic c (fun z : Plane => Train.toVec (g z, 0)) := by
    intro z
    show Train.toVec (g (z.1 + c, z.2), 0) = Train.toVec (g z, 0)
    rw [hgp z]
  -- transport identity
  have hcore := tp_core c R hc hRpos (etaCutoff R) hφS hφ0 hφ1 b
    (fun z : Plane => Train.toVec (g z, 0)) hb hwC hbp hwP hdiv
    cellIntegrable_of_support cellDerivZero_of_periodic
  have hn : ∀ z : Plane, ‖Train.toVec (g z, 0)‖ ^ 2 = g z ^ 2 := by
    intro z
    simp [Train.norm_toVec_sq]
  simp only [hn] at hcore
  -- pointwise: `⟨w, (b·∇)w⟩ = g (b·∇g)`
  have hpt : ∀ z : Plane,
      inner ℝ (Train.toVec (g z, 0)) (bilinAdv b (fun y => Train.toVec (g y, 0)) z) =
        g z * scalarAdv b g z := by
    intro z
    simp [bilinAdv, scalarAdv, PiLp.inner_apply, Fin.sum_univ_two, Cyl.partialQ,
      Cyl.partialEta, RCLike.inner_apply, conj_trivial] <;> ring
  have hL : ∫ z in Cyl.cell c, etaCutoff R z.2 * (2 * g z * scalarAdv b g z) =
      2 * ∫ z in Cyl.cell c, etaCutoff R z.2 *
        inner ℝ (Train.toVec (g z, 0)) (bilinAdv b (fun y => Train.toVec (g y, 0)) z) := by
    rw [← integral_const_mul]
    congr 1
    funext z
    rw [hpt z]
    ring
  -- the pointwise bound `|g² b₁ χ'| ≤ (C₀/R) M g²`
  have hbd : ∀ z : Plane,
      |g z ^ 2 * b z 1 * deriv (etaCutoff R) z.2| ≤ C₀ / R * M * g z ^ 2 := by
    intro z
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (g z))]
    have h1 : |b z 1| * |deriv (etaCutoff R) z.2| ≤ M * (C₀ / R) :=
      mul_le_mul (hbM z) (hd z.2) (abs_nonneg _) hM0
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (g z))
    linarith
  -- continuity of the integrand
  have hbc : Continuous (fun z : Plane => b z 1) := (tp_comp_contDiff b 1 hb).continuous
  have hdc : Continuous (deriv (etaCutoff R)) := hφS.continuous_deriv (by simp)
  have hfc : Continuous (fun z : Plane => g z ^ 2 * b z 1 * deriv (etaCutoff R) z.2) :=
    ((hg.continuous.pow 2).mul hbc).mul (hdc.comp continuous_snd)
  have hJint : IntegrableOn (fun z : Plane => g z ^ 2 * b z 1 * deriv (etaCutoff R) z.2)
      (Cyl.cell c) :=
    Integrable.mono' (hg2.const_mul (C₀ / R * M)) hfc.aestronglyMeasurable
      (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact hbd z))
  have hint : ∫ z in Cyl.cell c, g z ^ 2 * b z 1 * deriv (etaCutoff R) z.2 ≤
      ∫ z in Cyl.cell c, C₀ / R * M * g z ^ 2 :=
    integral_mono hJint (hg2.const_mul (C₀ / R * M))
      (fun z => le_trans (le_abs_self _) (hbd z))
  rw [integral_const_mul] at hint
  rw [hL]
  linarith [hcore, hint]

end UnforcedLeray.Short.PartI
