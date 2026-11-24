import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.L1
import UnforcedLeray.Short.PartIIIa.T07_ScalingJaInv

/-!
# Part III-a long assembly, L4: `J_a⁻¹` on the weighted cell norm (corrected statement)

The requested statement `xNorm_JscaleInv_le` (PartIII-a:T21/long/4), with only `0 < a`, is FALSE
for `m ≠ 0`. Substituting `x = √a y` gives, for `d = c/√a`,
`‖J_a⁻¹ g‖²_{X_{m,d}} = a³ ∫_{cell c} (1 + (x₁² + x₂²)/a)^m |g(x)|² dx`, while
`a³ ‖g‖²_{X_{m,c}} = a³ ∫_{cell c} (1 + x₁² + x₂²)^m |g(x)|² dx`. For `m = 1`, `a = 1/4`, `c = 1`
and `g = 1_{cell 1} · jb⁻²` (in `L²(cellMeasure 1 1)`), the first integral strictly exceeds the second
because `jb(2x) - jb(x) = 3(x₁² + x₂²) > 0` off the origin, so the claimed bound fails.

The scalar bound needs `1 ≤ a` and `0 ≤ m` (the hypotheses of `Targets.ScalingJaInv`). This file
proves the corrected statement `xNorm_JscaleInv_le` under those hypotheses; it
does not prove the original statement.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- a.e. equality of `g` and `h` on `cell c` transports to `J_a⁻¹ g = J_a⁻¹ h` a.e. on
`cell (c/√a)`. -/
lemma jscale_ae_of_ae (c a : ℝ) (ha : 0 < a) (g h : ℝ × ℝ → ℂ)
    (hgh : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)), g x = h x) :
    ∀ᵐ y ∂(volume.restrict (UnforcedLeray.B0579.cell (cellLen c a))),
      JscaleInv a g y = JscaleInv a h y := by
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hrne : Real.sqrt a ≠ 0 := hr.ne'
  have e : Real.sqrt a * (c / Real.sqrt a / 2) = c / 2 := by field_simp
  have hmem : ∀ y : ℝ × ℝ, y ∈ UnforcedLeray.B0579.cell (cellLen c a) ↔
      Real.sqrt a • y ∈ UnforcedLeray.B0579.cell c := by
    intro y
    unfold UnforcedLeray.B0579.cell cellLen
    rw [Set.mem_prod, Set.mem_prod, Set.mem_Ico, Set.mem_Ico]
    simp only [Set.mem_univ, and_true, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · linarith [mul_le_mul_of_nonneg_left h1 hr.le]
      · linarith [mul_lt_mul_of_pos_left h2 hr]
    · rintro ⟨h1, h2⟩
      constructor
      · by_contra hc
        push_neg at hc
        linarith [mul_lt_mul_of_pos_left hc hr]
      · by_contra hc
        push_neg at hc
        linarith [mul_le_mul_of_nonneg_left hc hr.le]
  have hae_c := hgh
  rw [ae_iff, Measure.restrict_apply' (UnforcedLeray.B0579.measurableSet_cell c)] at hae_c
  have key : ∀ (k : ℝ × ℝ → ℂ) (y : ℝ × ℝ),
      JscaleInv a k y = ((a ^ 2 : ℝ) : ℂ) * k (Real.sqrt a • y) :=
    fun k y => rfl
  rw [ae_iff, Measure.restrict_apply' (UnforcedLeray.B0579.measurableSet_cell _)]
  refine measure_mono_null (t := (fun y : ℝ × ℝ => Real.sqrt a • y) ⁻¹'
      ({x : ℝ × ℝ | ¬ g x = h x} ∩ UnforcedLeray.B0579.cell c)) ?_ ?_
  · intro y hy
    refine ⟨?_, (hmem y).1 hy.2⟩
    intro heq
    apply hy.1
    rw [key, key, heq]
  · rw [Measure.addHaar_preimage_smul volume hrne, hae_c, mul_zero]

/-- Corrected version of `xNorm_JscaleInv_le`: needs `1 ≤ a` and `0 ≤ m`. -/
theorem xNorm_JscaleInv_le (c m a : ℝ) (hm : 0 ≤ m) (ha : 1 ≤ a) (g : ℝ × ℝ → ℂ)
    (hg : MemLp g 2 (UnforcedLeray.B0579.cellMeasure c m)) :
    xNorm (cellLen c a) m (JscaleInv a g) ≤ ENNReal.ofReal (a ^ ((3 : ℝ) / 2)) * xNorm c m g := by
  obtain ⟨h, hmeas, hgh, hnorm⟩ := ae_representative_xNorm c m g hg
  have ha0 : 0 < a := by linarith
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
  rcases le_or_gt c 0 with hc | hc
  · have hd : cellLen c a ≤ 0 := by
      unfold cellLen
      exact div_nonpos_of_nonpos_of_nonneg hc (Real.sqrt_nonneg a)
    have hcell : UnforcedLeray.B0579.cell c = ∅ := by
      unfold UnforcedLeray.B0579.cell
      rw [Set.Ico_eq_empty (fun h' => by linarith), Set.empty_prod]
    have hcell' : UnforcedLeray.B0579.cell (cellLen c a) = ∅ := by
      unfold UnforcedLeray.B0579.cell
      rw [Set.Ico_eq_empty (fun h' => by linarith), Set.empty_prod]
    have hμ1 : UnforcedLeray.B0579.cellMeasure c m = 0 := by
      unfold UnforcedLeray.B0579.cellMeasure
      rw [hcell, Measure.restrict_empty]
      simp
    have hμ2 : UnforcedLeray.B0579.cellMeasure (cellLen c a) m = 0 := by
      unfold UnforcedLeray.B0579.cellMeasure
      rw [hcell', Measure.restrict_empty]
      simp
    unfold xNorm
    rw [hμ1, hμ2]
    simp
  · have hd : 0 < cellLen c a := div_pos hc hr
    have hdr : cellLen c a * Real.sqrt a = c := by
      unfold cellLen
      field_simp
    have hT := scalingJaInv m hm a (cellLen c a) ha hd h hmeas
    rw [hdr, hnorm] at hT
    have hgh' : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)), g x = h x :=
      (UnforcedLeray.B0579.ac_cellMeasure c m).ae_le hgh
    have hae := jscale_ae_of_ae c a ha0 g h hgh'
    have hae2 : ∀ᵐ y ∂(UnforcedLeray.B0579.cellMeasure (cellLen c a) m),
        JscaleInv a g y = JscaleInv a h y :=
      (UnforcedLeray.B0579.cellMeasure_ac (cellLen c a) m).ae_le hae
    have heq : xNorm (cellLen c a) m (JscaleInv a g) = xNorm (cellLen c a) m (JscaleInv a h) := by
      unfold xNorm
      exact eLpNorm_congr_ae hae2
    rw [heq]
    exact hT

end UnforcedLeray.Short.IIIa
