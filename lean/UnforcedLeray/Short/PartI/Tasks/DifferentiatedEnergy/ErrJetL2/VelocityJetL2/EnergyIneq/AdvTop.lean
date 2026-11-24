import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2.EnergyIneq
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.TransportIdentity
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.CellToolkit

/-!
# Part I, task `PartI:T08/2/2/2/6/2`: the cutoff transport estimate (`CutoffAdvTop`)

Source of record: `the November 2 reference manuscript`, lines 286-287.
Target: `cutoffAdvTop_proof : CutoffAdvTop` (`Sub/PartI_T08_2_2/EnergyIneq.lean`).

Route. Take `K₀ = 4 C₀` with `C₀` from `EtaCutoffFacts`.  Fix `c, R ≥ 1, M, b, g` as in
`CutoffAdvTop`, and put `φ = etaCutoff R`, `w z = toVec (g z, 0)`.

* Transport identity (`tp_core`, applied to `v := b`, `w`): since `⟨w, (b·∇)w⟩ = g · (b·∇g)` and
  `‖w‖² = g²`, the left side equals `-∫_cell φ 2 g (b·∇g)` and equals `∫_cell g² b₁ φ'`.
* Pointwise: `g² b₁ φ'` vanishes for `2R ≤ |η|` (`φ' = 0` there), and on the rest
  `|g² b₁ φ'| ≤ M³ (C₀/R)` (`|φ'| ≤ (C₀/R)√φ ≤ C₀/R`).
* The support lies in the strip `cell c ∩ {|η| < 2R}`, of volume at most `c · 4R`, so the
  integral is at most `M³ (C₀/R) · 4Rc = 4 C₀ c M³`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- **`PartI:T08/2/2/2/6/2`, target `CutoffAdvTop`.** -/
theorem cutoffAdvTop_proof : UnforcedLeray.Short.PartI.CutoffAdvTop := by
  have hη := etaCutoffFacts
  unfold EtaCutoffFacts at hη
  obtain ⟨C₀, hC₀, hφ⟩ := hη
  obtain ⟨hI, hZ⟩ := cellToolkit
  refine ⟨4 * C₀, mul_nonneg (by norm_num) hC₀, ?_⟩
  intro c R M b g hc hR1 hb hg hbp hgp hdiv hbM hgM
  have hRpos : 0 < R := by linarith
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hgM 0)
  obtain ⟨hφS, hφ01, _, hφ0, hφd⟩ := hφ R hR1
  have hφ1 : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
    intro η hη
    have h1 := hφd η
    rw [hφ0 η hη, Real.sqrt_zero, mul_zero, abs_nonpos_iff] at h1
    exact h1
  -- the test field `w = (g, 0)`
  have hwC : ContDiff ℝ ∞ (fun z : Plane => Train.toVec (g z, 0)) :=
    Train.toVecL.contDiff.comp (hg.prodMk contDiff_const)
  have hwP : Cyl.IsPeriodic c (fun z : Plane => Train.toVec (g z, 0)) := by
    intro z
    show Train.toVec (g (z.1 + c, z.2), 0) = Train.toVec (g z, 0)
    rw [hgp z]
  -- transport identity
  have hcore := tp_core c R hc hRpos (etaCutoff R) hφS hφ0 hφ1 b
    (fun z : Plane => Train.toVec (g z, 0)) hb hwC hbp hwP hdiv hI hZ
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
  -- the right side of the transport identity, with its support in `|η| < 2R`
  let T : Set Plane := {z : Plane | |z.2| < 2 * R}
  have hTm : MeasurableSet T := measurableSet_lt (by fun_prop) (by fun_prop)
  have hF0 : ∀ z : Plane, z ∉ T →
      ‖Train.toVec (g z, 0)‖ ^ 2 * b z 1 * deriv (etaCutoff R) z.2 = 0 := by
    intro z hz
    have hz' : 2 * R ≤ |z.2| := not_lt.mp hz
    rw [hφ1 z.2 hz', mul_zero]
  -- pointwise bound on the strip
  have hFbd : ∀ z ∈ Cyl.cell c ∩ T,
      ‖‖Train.toVec (g z, 0)‖ ^ 2 * b z 1 * deriv (etaCutoff R) z.2‖ ≤ M ^ 2 * M * (C₀ / R) := by
    intro z _
    have hn : ‖Train.toVec (g z, 0)‖ ^ 2 = g z ^ 2 := by
      simp [Train.norm_toVec_sq]
    rw [hn, Real.norm_eq_abs]
    have hs1 : Real.sqrt (etaCutoff R z.2) ≤ 1 := by
      have h := Real.sqrt_le_sqrt (hφ01 z.2).2
      rwa [Real.sqrt_one] at h
    have hd1 : |deriv (etaCutoff R) z.2| ≤ C₀ / R :=
      (hφd z.2).trans (mul_le_of_le_one_right (div_nonneg hC₀ hRpos.le) hs1)
    have hg2 : g z ^ 2 ≤ M ^ 2 := by
      have h1 : |g z| ≤ M := hgM z
      have h2 : g z ^ 2 = |g z| ^ 2 := (sq_abs (g z)).symm
      rw [h2]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hbz : |b z 1| ≤ M := hbM z
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (g z))]
    exact mul_le_mul (mul_le_mul hg2 hbz (abs_nonneg _) (sq_nonneg _))
      hd1 (abs_nonneg _) (mul_nonneg (sq_nonneg M) hM0)
  -- the cell integral of the strip is bounded by its volume
  have hsplit : ∫ z in Cyl.cell c,
      ‖Train.toVec (g z, 0)‖ ^ 2 * b z 1 * deriv (etaCutoff R) z.2 =
      ∫ z in Cyl.cell c ∩ T,
      ‖Train.toVec (g z, 0)‖ ^ 2 * b z 1 * deriv (etaCutoff R) z.2 := by
    have hind : ∫ z in Cyl.cell c,
        ‖Train.toVec (g z, 0)‖ ^ 2 * b z 1 * deriv (etaCutoff R) z.2 =
        ∫ z in Cyl.cell c, T.indicator
          (fun z : Plane => ‖Train.toVec (g z, 0)‖ ^ 2 * b z 1 * deriv (etaCutoff R) z.2) z := by
      congr 1
      funext z
      by_cases hz : z ∈ T
      · simp [hz]
      · simp [hz, hF0 z hz]
    rw [hind, setIntegral_indicator hTm]
  have hvol : volume (Cyl.cell c ∩ T) ≤ ENNReal.ofReal c * ENNReal.ofReal (4 * R) := by
    have hsub : Cyl.cell c ∩ T ⊆ Ico (-c / 2) (c / 2) ×ˢ Ioo (-(2 * R)) (2 * R) := by
      intro z hz
      have h1 : z.1 ∈ Ico (-c / 2) (c / 2) := (Set.mem_prod.mp hz.1).1
      have h2 : |z.2| < 2 * R := hz.2
      exact Set.mem_prod.mpr ⟨h1, abs_lt.mp h2⟩
    refine (measure_mono hsub).trans (le_of_eq ?_)
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ioo]
    congr 1
    · congr 1; ring
    · congr 1; ring
  have hfin : volume (Cyl.cell c ∩ T) < ⊤ :=
    lt_of_le_of_lt hvol (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hIb : ‖(∫ z in Cyl.cell c ∩ T,
      ‖Train.toVec (g z, 0)‖ ^ 2 * b z 1 * deriv (etaCutoff R) z.2)‖ ≤
      M ^ 2 * M * (C₀ / R) * (volume (Cyl.cell c ∩ T)).toReal :=
    norm_setIntegral_le_of_norm_le_const hfin hFbd
  have hvolR : (volume (Cyl.cell c ∩ T)).toReal ≤ c * (4 * R) := by
    have h1 := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hvol
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le,
      ENNReal.toReal_ofReal (by linarith)] at h1
    exact h1
  have hbound : ‖(∫ z in Cyl.cell c ∩ T,
      ‖Train.toVec (g z, 0)‖ ^ 2 * b z 1 * deriv (etaCutoff R) z.2)‖ ≤
      4 * C₀ * c * M ^ 3 := by
    refine hIb.trans ?_
    have hCb : 0 ≤ M ^ 2 * M * (C₀ / R) :=
      mul_nonneg (mul_nonneg (sq_nonneg M) hM0) (div_nonneg hC₀ hRpos.le)
    have hmul := mul_le_mul_of_nonneg_left hvolR hCb
    have heq : M ^ 2 * M * (C₀ / R) * (c * (4 * R)) = 4 * C₀ * c * M ^ 3 := by
      field_simp
    exact hmul.trans (le_of_eq heq)
  have hJ : |(∫ z in Cyl.cell c,
      ‖Train.toVec (g z, 0)‖ ^ 2 * b z 1 * deriv (etaCutoff R) z.2)| ≤ 4 * C₀ * c * M ^ 3 := by
    rw [hsplit, ← Real.norm_eq_abs]
    exact hbound
  have key : -(∫ z in Cyl.cell c, etaCutoff R z.2 * (2 * g z * scalarAdv b g z)) =
      ∫ z in Cyl.cell c, ‖Train.toVec (g z, 0)‖ ^ 2 * b z 1 * deriv (etaCutoff R) z.2 := by
    rw [hL]
    linarith [hcore]
  have final : -(∫ z in Cyl.cell c, etaCutoff R z.2 * (2 * g z * scalarAdv b g z)) ≤
      4 * C₀ * c * M ^ 3 := by
    exact le_trans (le_of_eq key) (abs_le.mp hJ).2
  exact final

end UnforcedLeray.Short.PartI
