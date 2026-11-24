import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1.DerivY.Reduction
import UnforcedLeray.Loc.L01Coefficient.Basic

/-!
# `RingResidualDerivBound` from the Part I residual bound `RingResidualBound`

Source `the November 2 reference manuscript`
lines 1206-1222, 1305-1322, 2542-2551.  `RingResidualBound` at `ρ = 2`, `p = 11/4` supplies the
periodicity of `F_R` and the `L^{q₀}` weak first derivatives `G τ j` (continuous in `τ`);
`G` is periodic only a.e. in `y`, and is replaced by the exactly periodic fundamental-domain
representative `τ ↦ G (τ - P ⌊τ/P⌋) j`, which equals `G τ j` a.e. by uniqueness of weak derivatives.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0412
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.Short.IIb (trainStream trainPressure isExactPlanarTrain_params_rpow period_eq_rpow)
open UnforcedLeray.Short.PartIIa (ringResidual RingResidualBound)

theorem ringResidualDerivBound_of (h : RingResidualBound) : RingResidualDerivBound := by
  obtain ⟨ν₁, hν₁, C, d, H1⟩ := h 2 (11 / 4) (by norm_num) (by norm_num)
  refine ⟨ν₁, hν₁, fun p htr hν hc hR hP j => ?_⟩
  obtain ⟨hper, G, hmem, hG, -, hcont⟩ :=
    H1 p.ν ⟨p.ν_pos, hν⟩ (trainStream p) (trainPressure p)
      (isExactPlanarTrain_params_rpow p htr hc) p.R hR
  have hper' : ∀ τ, ringResidual p.R p.ν (trainStream p) (trainPressure p) (τ + p.period) =
      ringResidual p.R p.ν (trainStream p) (trainPressure p) τ := fun τ => by
    rw [← period_eq_rpow p hc]; exact hper τ
  have hP0 : 0 < p.period := p.period_pos
  have hq : (q0E : ℝ≥0∞) = ENNReal.ofReal (11 / 4) := rfl
  have hGmem : ∀ τ, MemLp (G τ j) q0E volume := fun τ => by rw [hq]; exact (hG τ j).1
  have hGloc : ∀ τ, LocallyIntegrable (G τ j) volume := fun τ =>
    (hGmem τ).locallyIntegrable (by rw [hq]; exact ENNReal.one_le_ofReal.mpr (by norm_num))
  -- a.e. periodicity of G
  have hae1 : ∀ τ, G (τ + p.period) j =ᵐ[volume] G τ j := fun τ => by
    refine UnforcedLeray.Blueprint.L01.weakDerivative_ae_eq (i := j) ?_ (hG τ j).2
      (hGloc _) (hGloc _)
    have := (hG (τ + p.period) j).2
    rwa [hper' τ] at this
  have haeZ : ∀ n : ℤ, ∀ τ, G (τ + n * p.period) j =ᵐ[volume] G τ j := by
    intro n
    induction n using Int.induction_on with
    | zero => intro τ; simp
    | succ n ih =>
      intro τ
      have e : τ + ((n : ℤ) + 1 : ℤ) * p.period = (τ + n * p.period) + p.period := by
        push_cast; ring
      rw [e]
      exact (hae1 _).trans (ih τ)
    | pred n ih =>
      intro τ
      have e : τ + ((-(n : ℤ) - 1 : ℤ) : ℝ) * p.period + p.period = τ + ((-(n : ℤ) : ℤ) : ℝ) * p.period := by
        push_cast; ring
      have h1 := hae1 (τ + ((-(n : ℤ) - 1 : ℤ) : ℝ) * p.period)
      rw [e] at h1
      exact h1.symm.trans (ih τ)
  set P := p.period with hPdef
  let Gf : ℝ → SpatialField := fun τ => G (τ - P * (⌊τ / P⌋ : ℤ)) j
  have hae : ∀ τ, Gf τ =ᵐ[volume] G τ j := fun τ => by
    have e : τ - P * (⌊τ / P⌋ : ℤ) = τ + ((-⌊τ / P⌋ : ℤ) : ℝ) * P := by push_cast; ring
    show G (τ - P * (⌊τ / P⌋ : ℤ)) j =ᵐ[volume] G τ j
    rw [e]; exact haeZ _ τ
  refine ⟨Gf, hper', ?_, fun τ => by rw [hq]; exact hmem τ, fun τ => (hGmem τ).ae_eq (hae τ).symm,
    ?_, ?_, fun τ => ?_⟩
  · intro τ
    have hfl : ⌊(τ + P) / P⌋ = ⌊τ / P⌋ + 1 := by
      rw [show (τ + P) / P = τ / P + 1 by field_simp, Int.floor_add_one]
    show G (τ + P - P * (⌊(τ + P) / P⌋ : ℤ)) j = G (τ - P * (⌊τ / P⌋ : ℤ)) j
    rw [hfl]
    rw [show τ + P - P * ((⌊τ / P⌋ + 1 : ℤ) : ℝ) = τ - P * (⌊τ / P⌋ : ℤ) by push_cast; ring]
  · intro τ₀
    rw [hq]
    refine squeeze_zero (fun τ => ENNReal.toReal_nonneg) (fun τ => ?_) (hcont τ₀)
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg)
  · intro τ₀
    rw [hq]
    refine squeeze_zero (fun τ => ENNReal.toReal_nonneg) (fun τ => ?_) (hcont τ₀)
    have e : eLpNorm (Gf τ - Gf τ₀) (ENNReal.ofReal (11 / 4)) volume =
        eLpNorm (G τ j - G τ₀ j) (ENNReal.ofReal (11 / 4)) volume :=
      eLpNorm_congr_ae ((hae τ).sub (hae τ₀))
    rw [e]
    refine le_add_of_nonneg_of_le ENNReal.toReal_nonneg ?_
    exact Finset.single_le_sum (f := fun i => (eLpNorm (G τ i - G τ₀ i) (ENNReal.ofReal (11 / 4))
      volume).toReal) (fun i _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)
  · exact (hG τ j).2.congr (Filter.EventuallyEq.refl _ _) (hae τ).symm

end UnforcedLeray.Short.PartIIIb.Concrete
