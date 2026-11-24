import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.FramePairing2.KerBS

/-!
# Helper for `PartIII-a:T21/c3/3/1/1/2/2/3/c/2`: uniqueness identifies `L²` Biot-Savart velocities
with the kernel velocity (cells of length `D ≥ 1`)

Source `the November 2 reference manuscript` (SP) lines 2863-2865, 2876-2881,
3230-3240.  See `KerBS.lean` for the argument.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2WeakEqFrame.KerBSAux

open UnforcedLeray.Short.IIIa

/-- The band estimate for a strongly measurable density. -/
theorem kerVelCx_ae_eq_band {D m : ℝ} (hD : 1 ≤ D) (hm : 8 < m) {Ω : ℝ × ℝ → ℂ}
    {U : ℝ × ℝ → Fin 2 → ℂ} (hΩs : StronglyMeasurable Ω)
    (hΩ : MemLp Ω 2 (B0579.cellMeasure D m)) (hZ : HasZeroCirculation D Ω)
    (hU : IsBiotSavart D Ω U) (k : Fin 2) (R : ℝ) :
    ∀ᵐ x ∂(volume.restrict (band D R)), U x k = kerVelCx D Ω x k := by
  have hm1 : 1 < m := by linarith
  obtain ⟨a, b, hab, hconv⟩ := ladTestDensity m hm D Ω hD hΩ hZ
  set ψ : ℕ → ℝ × ℝ → ℂ := fun n x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ)
    with hψ
  have hψmem : ∀ n, MemLp (ψ n) 2 (B0579.cellMeasure D m) := fun n =>
    (((hab n).1.memLp m).ofReal (K := ℂ)).add
      ((((hab n).2.1.memLp m).ofReal (K := ℂ)).const_mul Complex.I)
  have hψsm : ∀ n, StronglyMeasurable (ψ n) := fun n =>
    ((Complex.continuous_ofReal.comp (hab n).1.continuous).add
      (continuous_const.mul
        (Complex.continuous_ofReal.comp (hab n).2.1.continuous))).stronglyMeasurable
  have hψint : ∀ n, IntegrableOn (ψ n) (B0579.cell D) := fun n =>
    (Integrable.ofReal (𝕜 := ℂ) (hab n).2.2.1).add
      ((Integrable.ofReal (𝕜 := ℂ) (hab n).2.2.2.1).const_mul Complex.I)
  have hψ0 : ∀ n, ∫ x in B0579.cell D, ψ n x = 0 := by
    intro n
    have e := integral_add (Integrable.ofReal (𝕜 := ℂ) (hab n).2.2.1)
      ((Integrable.ofReal (𝕜 := ℂ) (hab n).2.2.2.1).const_mul Complex.I)
    have e2 : ∫ x in B0579.cell D, ((a n x : ℝ) : ℂ) = 0 := by
      rw [integral_complex_ofReal, (hab n).2.2.2.2.1]
      simp
    have e3 : ∫ x in B0579.cell D, Complex.I * ((b n x : ℝ) : ℂ) = 0 := by
      rw [integral_const_mul, integral_complex_ofReal, (hab n).2.2.2.2.2]
      simp
    calc ∫ x in B0579.cell D, ψ n x
        = (∫ x in B0579.cell D, ((a n x : ℝ) : ℂ)) +
            ∫ x in B0579.cell D, Complex.I * ((b n x : ℝ) : ℂ) := e
      _ = 0 := by rw [e2, e3, add_zero]
  have hψBS : ∀ n, IsBiotSavart D (ψ n) (kerVelCx D (ψ n)) := fun n =>
    isBiotSavart_kerVelCx_pair hD hm1 (hab n).1 (hab n).2.1 (hab n).2.2.2.2.1 (hab n).2.2.2.2.2
  have hE : ∀ n, IsBiotSavart D (Ω - ψ n) (U - kerVelCx D (ψ n)) := fun n =>
    ladBSSub m D Ω (ψ n) U (kerVelCx D (ψ n)) hm1 hΩ (hψmem n) hU (hψBS n)
  have hZE : ∀ n, HasZeroCirculation D (Ω - ψ n) := by
    intro n
    refine ⟨hZ.1.sub (hψint n), ?_⟩
    calc ∫ x in B0579.cell D, (Ω - ψ n) x
        = (∫ x in B0579.cell D, Ω x) - ∫ x in B0579.cell D, ψ n x := integral_sub hZ.1 (hψint n)
      _ = 0 := by rw [hZ.2, hψ0 n, sub_zero]
  obtain ⟨C, hC⟩ := ladBSBound m hm
  have hL2 : ∀ n, eLpNorm (fun x => U x k - kerVelCx D (ψ n) x k) 2
      (volume.restrict (B0579.cell D)) ≤ ENNReal.ofReal C * xNorm D m (Ω - ψ n) := fun n =>
    hC D hD (Ω - ψ n) (hΩ.sub (hψmem n)) (hZE n) _ (hE n) k
  obtain ⟨CK, hCK, hKb⟩ := lintegral_band_kerVelCx_le hD R
  obtain ⟨C1, hC1, hL1⟩ := lintegral_cell_le_xNorm hm1 D
  have hlin : ∀ n, ∀ᵐ x ∂(volume.restrict (B0579.cell D)),
      kerVelCx D (ψ n) x k - kerVelCx D Ω x k = kerVelCx D (ψ n - Ω) x k := by
    intro n
    filter_upwards [BlockPropagatorInteriorSub.OrgSplit.RelIntA.ae_integrableOn_kerVelCx hD hm1
        (hψmem n),
      BlockPropagatorInteriorSub.OrgSplit.RelIntA.ae_integrableOn_kerVelCx hD hm1 hΩ]
      with x h1 h2
    have e := integral_sub (h1 k) (h2 k)
    unfold kerVelCx
    refine e.symm.trans ?_
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply]
    ring
  have hUm : AEStronglyMeasurable (fun x => U x k) (volume.restrict (B0579.cell D)) :=
    (hU.1 k).1
  have hsub : volume.restrict (band D R) ≤ volume.restrict (B0579.cell D) :=
    Measure.restrict_mono (band_subset_cell D R) le_rfl
  set K : ℝ≥0∞ := ENNReal.ofReal C * volume (band D R) ^ (1 / 2 : ℝ) + CK * C1 with hK
  have hKtop : K ≠ ∞ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_,
      ENNReal.mul_ne_top hCK.ne hC1.ne⟩
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (volume_band_lt_top D R).ne
  set g : ℝ × ℝ → ℂ := fun x => U x k - kerVelCx D Ω x k with hg
  have hgm : AEMeasurable (fun x => ‖g x‖ₑ) (volume.restrict (band D R)) :=
    ((hUm.mono_measure hsub).sub
      (stronglyMeasurable_kerVelCx' D hΩs k).aestronglyMeasurable).enorm
  have hbound : ∀ n, ∫⁻ x in band D R, ‖g x‖ₑ ≤ K * xNorm D m (ψ n - Ω) := by
    intro n
    have hF : AEStronglyMeasurable (fun x => U x k - kerVelCx D (ψ n) x k)
        (volume.restrict (band D R)) :=
      (hUm.mono_measure hsub).sub (stronglyMeasurable_kerVelCx' D (hψsm n) k).aestronglyMeasurable
    have hpt : ∀ᵐ x ∂(volume.restrict (band D R)),
        ‖g x‖ₑ ≤ ‖U x k - kerVelCx D (ψ n) x k‖ₑ + ‖kerVelCx D (ψ n - Ω) x k‖ₑ := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (band_subset_cell D R) (hlin n)]
        with x hx
      have e : g x = (U x k - kerVelCx D (ψ n) x k) + kerVelCx D (ψ n - Ω) x k := by
        rw [← hx, hg]
        ring
      rw [e]
      exact enorm_add_le _ _
    have h1 : ∫⁻ x in band D R, ‖U x k - kerVelCx D (ψ n) x k‖ₑ ≤
        ENNReal.ofReal C * xNorm D m (Ω - ψ n) * volume (band D R) ^ (1 / 2 : ℝ) := by
      rw [← eLpNorm_one_eq_lintegral_enorm]
      refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2) hF).trans ?_
      have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
      rw [hexp, Measure.restrict_apply_univ]
      gcongr
      exact (eLpNorm_mono_measure _ hsub).trans (hL2 n)
    have h2 : ∫⁻ x in band D R, ‖kerVelCx D (ψ n - Ω) x k‖ₑ ≤
        CK * (C1 * xNorm D m (ψ n - Ω)) :=
      (hKb _ ((hψsm n).sub hΩs) k).trans
        (by gcongr; exact hL1 _ ((hψsm n).sub hΩs).aestronglyMeasurable)
    have hcomm : xNorm D m (Ω - ψ n) = xNorm D m (ψ n - Ω) := by
      unfold xNorm
      exact eLpNorm_sub_comm _ _ _ _
    calc ∫⁻ x in band D R, ‖g x‖ₑ
        ≤ ∫⁻ x in band D R, (‖U x k - kerVelCx D (ψ n) x k‖ₑ + ‖kerVelCx D (ψ n - Ω) x k‖ₑ) :=
          lintegral_mono_ae hpt
      _ = (∫⁻ x in band D R, ‖U x k - kerVelCx D (ψ n) x k‖ₑ) +
            ∫⁻ x in band D R, ‖kerVelCx D (ψ n - Ω) x k‖ₑ :=
          lintegral_add_left' hF.enorm _
      _ ≤ ENNReal.ofReal C * xNorm D m (Ω - ψ n) * volume (band D R) ^ (1 / 2 : ℝ) +
            CK * (C1 * xNorm D m (ψ n - Ω)) := add_le_add h1 h2
      _ = K * xNorm D m (ψ n - Ω) := by
          rw [hcomm, hK]
          ring
  have hconv' : Tendsto (fun n => xNorm D m (ψ n - Ω)) atTop (𝓝 0) := hconv
  have hlim : Tendsto (fun n => K * xNorm D m (ψ n - Ω)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hconv' (Or.inr hKtop)
    simpa using this
  have h0 : ∫⁻ x in band D R, ‖g x‖ₑ = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) (by positivity)
  filter_upwards [(lintegral_eq_zero_iff' hgm).1 h0] with x hx
  have hx' : g x = 0 := by simpa using hx
  exact sub_eq_zero.1 hx'

/-- **Kernel velocity = Biot-Savart velocity** (cells of length `D ≥ 1`, `m > 8`). -/
theorem kerVelCx_ae_eq_of_isBiotSavart {D m : ℝ} (hD : 1 ≤ D) (hm : 8 < m) {Ω : ℝ × ℝ → ℂ}
    {U : ℝ × ℝ → Fin 2 → ℂ} (hΩ : MemLp Ω 2 (B0579.cellMeasure D m))
    (hZ : HasZeroCirculation D Ω) (hU : IsBiotSavart D Ω U) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell D)), ∀ k : Fin 2, U x k = kerVelCx D Ω x k := by
  have hΩae : AEStronglyMeasurable Ω (volume.restrict (B0579.cell D)) :=
    hΩ.1.mono_ac (B0579.ac_cellMeasure D m)
  set Ω' := hΩae.mk Ω with hΩ'
  have hΩ's : StronglyMeasurable Ω' := hΩae.stronglyMeasurable_mk
  have hΩeq : Ω =ᵐ[volume.restrict (B0579.cell D)] Ω' := hΩae.ae_eq_mk
  have hKeq : ∀ x k, kerVelCx D Ω' x k = kerVelCx D Ω x k := by
    intro x k
    unfold kerVelCx
    refine integral_congr_ae ?_
    filter_upwards [hΩeq] with z hz
    rw [hz]
  have hΩ'mem : MemLp Ω' 2 (B0579.cellMeasure D m) :=
    hΩ.ae_eq ((B0579.cellMeasure_ac D m).ae_le hΩeq)
  have hZ' : HasZeroCirculation D Ω' :=
    ⟨hZ.1.congr hΩeq, (integral_congr_ae hΩeq).symm.trans hZ.2⟩
  have hU' : IsBiotSavart D Ω' U := isBiotSavart_congr_ae hU hΩeq
  rw [← iUnion_band D, ae_restrict_iUnion_iff]
  intro n
  rw [ae_all_iff]
  intro k
  filter_upwards [kerVelCx_ae_eq_band hD hm hΩ's hΩ'mem hZ' hU' k n] with x hx
  rw [hx, hKeq]

end UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2WeakEqFrame.KerBSAux
