import UnforcedLeray.Short.PartIIb.Sub.T12_1_1

/-!
# Part II-b, task `PartII-b:T12/1/1/3` (`PlaneLerayOfRiesz`): decomposition into leaves

Source: `the November 2 reference manuscript` lines 1670, 1923-1926 (Grafakos,
*Classical Fourier Analysis*, Cor. 5.2.8).  Given a planar Riesz family `S`, the real Leray
projection is `G = F - S F` componentwise, after transporting `ℝ × ℝ` to `Fin 2 → ℝ` by the
measure preserving `MeasurableEquiv.finTwoArrow`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The `k`-th component of `F` transported to the plane `Fin 2 → ℝ`. -/
def planeComp (F : ℝ × ℝ → RMerid) (k : Fin 2) : (Fin 2 → ℝ) → ℝ :=
  fun x => F (MeasurableEquiv.finTwoArrow x) k

theorem planeComp_memLp {F : ℝ × ℝ → RMerid} {p : ℝ≥0∞} (hF : MemLp F p volume) (k : Fin 2) :
    MemLp (planeComp F k) p volume := by
  have h1 : MemLp (fun z => F z k) p volume := by
    refine hF.of_le_mul (c := 1) ?_ (Eventually.of_forall fun z => ?_)
    · exact (continuous_apply k |>.comp (PiLp.continuous_ofLp 2 _)).comp_aestronglyMeasurable hF.1
    · simpa using PiLp.norm_apply_le (F z) k
  exact h1.comp_measurePreserving (volume_preserving_finTwoArrow ℝ)

open Classical in
/-- The Leray projection `G = F - S F` of a field `F ∈ L²(ℝ²; ℝ²)` (and `0` otherwise), with
`G_i = f̃_i - Σ_k S_{ik} f̃_k`, `f̃_k = [F_k ∘ finTwoArrow] ∈ L²(Fin 2 → ℝ)`. -/
def planeRieszG (S : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)) (F : ℝ × ℝ → RMerid) :
    ℝ × ℝ → RMerid :=
  if h : MemLp F 2 volume then
    fun z => WithLp.toLp 2 (fun i =>
      (((planeComp_memLp h i).toLp _ - ∑ k, S i k ((planeComp_memLp h k).toLp _) : PlaneL2) :
        (Fin 2 → ℝ) → ℝ) (MeasurableEquiv.finTwoArrow.symm z))
  else 0

/-- **Leaf `T12/1/1/3/a`**: `G ∈ L²`, `‖G‖₂ ≤ ‖F‖₂` (the contraction clause of the family;
`‖G z‖² = Σ_i G_i(z)²`, as in `cm_eLpNorm_two_sq`). -/
def PlaneRieszGL2 : Prop :=
  ∀ (S : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)) (B : ℝ≥0), IsPlaneRieszFamily S B →
    ∀ F : ℝ × ℝ → RMerid, MemLp F 2 volume →
      MemLp (planeRieszG S F) 2 volume ∧ eLpNorm (planeRieszG S F) 2 volume ≤ eLpNorm F 2 volume

/-- **Leaf `T12/1/1/3/b`**: `‖G‖_r ≤ C ‖F‖_r` and `G ∈ L^r` for `F ∈ L² ∩ L^r`
(`UnforcedLeray.CZ.lp_bound` for each `S_{ik}` with transpose `S_{ki}`; Minkowski). -/
def PlaneRieszGLr : Prop :=
  ∀ (S : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)) (B : ℝ≥0), IsPlaneRieszFamily S B →
    ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ∀ F : ℝ × ℝ → RMerid,
      MemLp F 2 volume → MemLp F (ENNReal.ofReal r) volume →
        MemLp (planeRieszG S F) (ENNReal.ofReal r) volume ∧
          eLpNorm (planeRieszG S F) (ENNReal.ofReal r) volume ≤
            ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) volume

/-- **Leaf `T12/1/1/3/c`**: `G` is weakly divergence free (transposition `S_{ik}ᵀ = S_{ki}` and the
first test identity `Σ_i S_{ki} ∂_iφ = ∂_kφ`; derivatives along `Pi.single i 1` correspond to
`fderiv φ z (1,0)`, `(0,1)`). -/
def PlaneRieszGDiv : Prop :=
  ∀ (S : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)) (B : ℝ≥0), IsPlaneRieszFamily S B →
    ∀ F : ℝ × ℝ → RMerid, MemLp F 2 volume → ∀ φ : ℝ × ℝ → ℝ, PlaneTest φ →
      Integrable (fun z => planeRieszG S F z 0 * fderiv ℝ φ z (1, 0) +
          planeRieszG S F z 1 * fderiv ℝ φ z (0, 1)) ∧
        ∫ z, (planeRieszG S F z 0 * fderiv ℝ φ z (1, 0) +
          planeRieszG S F z 1 * fderiv ℝ φ z (0, 1)) = 0

/-- **Leaf `T12/1/1/3/d`**: `F - G` is orthogonal to compactly supported smooth solenoidal fields
(transposition and the second test identity `Σ_i S_{ki} Ψ_i = 0`). -/
def PlaneRieszGOrth : Prop :=
  ∀ (S : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)) (B : ℝ≥0), IsPlaneRieszFamily S B →
    ∀ F : ℝ × ℝ → RMerid, MemLp F 2 volume → ∀ Ψ : ℝ × ℝ → Fin 2 → ℝ, PlaneSolTest Ψ →
      Integrable (fun z => ∑ i : Fin 2, (F z i - planeRieszG S F z i) * Ψ z i) ∧
        ∫ z, ∑ i : Fin 2, (F z i - planeRieszG S F z i) * Ψ z i = 0

theorem planeLerayOfRiesz_of (h1 : PlaneRieszGL2) (h2 : PlaneRieszGLr) (h3 : PlaneRieszGDiv)
    (h4 : PlaneRieszGOrth) : PlaneLerayOfRiesz := by
  rintro ⟨S, B, hS⟩ r hr
  obtain ⟨C, hC, hCb⟩ := h2 S B hS r hr
  refine ⟨C, hC, fun F hF2 hFr => ⟨planeRieszG S F, (h1 S B hS F hF2).1, (hCb F hF2 hFr).1,
    (h1 S B hS F hF2).2, (hCb F hF2 hFr).2, ?_, ?_⟩⟩
  · exact fun φ hφ => h3 S B hS F hF2 φ hφ
  · exact fun Ψ hΨ => h4 S B hS F hF2 Ψ hΨ

end UnforcedLeray.Short.IIb
