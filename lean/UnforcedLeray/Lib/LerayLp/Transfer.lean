import UnforcedLeray.Lib.CZCore
import UnforcedLeray.Lib.CZL2

/-!
# Transfer between `Space` and `Fin 3 → ℝ` (INF01 T13, helper)


§5, Level 2 (`rieszPair_isCZConvolution (transfer (rieszPairL2 i k)) …`); decision D5 of
`scoping/README.md` §3. The Calderón–Zygmund core (`Lib/CZCore`, namespace `UnforcedLeray.CZ`)
is stated on `Fin N → ℝ` with the anisotropic gauge, while the Newton Hessian operators of
`Lib/CZL2` live on `Space = EuclideanSpace ℝ (Fin 3)`. The coordinate map
`WithLp.toLp 2 : (Fin 3 → ℝ) → Space` preserves Lebesgue measure
(`PiLp.volume_preserving_toLp`), so composition with it is an isometry of every `L^p`.

* `toFinLp p`, `ofFinLp p`: the two mutually inverse isometries
  `L^p(Space) ≃ L^p(Fin 3 → ℝ)` (`ofFinLp_toFinLp`, `toFinLp_ofFinLp`);
* `inner_toFinLp_two`: at `p = 2` they preserve the `L²` inner product;
* `isoWeight = (1,1,1)` and the comparison of its gauge (the sup norm) with the Euclidean norm:
  `anisoNorm_iso_le_norm`, `norm_sq_le_three_mul_anisoNorm_iso`.

Nothing here is a manuscript claim; these are bookkeeping lemmas for the unit B0414
(`paper/main.tex` lines 7336–7344).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.RieszLp

/-- `toLp 2 : (Fin 3 → ℝ) → Space` preserves Lebesgue measure. -/
theorem mp_toLp : MeasurePreserving (WithLp.toLp 2 : (Fin 3 → ℝ) → Space) volume volume :=
  PiLp.volume_preserving_toLp (Fin 3)

/-- `ofLp : Space → (Fin 3 → ℝ)` preserves Lebesgue measure. -/
theorem mp_ofLp : MeasurePreserving (WithLp.ofLp : Space → (Fin 3 → ℝ)) volume volume :=
  PiLp.volume_preserving_ofLp (Fin 3)

/-- `f ↦ f ∘ toLp`, `L^p(Space) → L^p(Fin 3 → ℝ)`. -/
def toFinLp (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp ℝ p (volume : Measure Space) →L[ℝ] Lp ℝ p (volume : Measure (Fin 3 → ℝ)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (WithLp.toLp 2 : (Fin 3 → ℝ) → Space)
    mp_toLp).toContinuousLinearMap

/-- `f ↦ f ∘ ofLp`, `L^p(Fin 3 → ℝ) → L^p(Space)`. -/
def ofFinLp (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp ℝ p (volume : Measure (Fin 3 → ℝ)) →L[ℝ] Lp ℝ p (volume : Measure Space) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (WithLp.ofLp : Space → (Fin 3 → ℝ))
    mp_ofLp).toContinuousLinearMap

section Lp

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem coeFn_toFinLp (f : Lp ℝ p (volume : Measure Space)) :
    (toFinLp p f : (Fin 3 → ℝ) → ℝ) =ᵐ[volume] fun x => f (WithLp.toLp 2 x) :=
  Lp.coeFn_compMeasurePreserving f mp_toLp

theorem coeFn_ofFinLp (f : Lp ℝ p (volume : Measure (Fin 3 → ℝ))) :
    (ofFinLp p f : Space → ℝ) =ᵐ[volume] fun z => f (WithLp.ofLp z) :=
  Lp.coeFn_compMeasurePreserving f mp_ofLp

theorem ofFinLp_toFinLp (f : Lp ℝ p (volume : Measure Space)) :
    ofFinLp p (toFinLp p f) = f := by
  apply Lp.ext
  have h2 : (fun z : Space => (toFinLp p f) (WithLp.ofLp z)) =ᵐ[volume]
      fun z => f (WithLp.toLp 2 (WithLp.ofLp z)) :=
    mp_ofLp.quasiMeasurePreserving.ae_eq_comp (coeFn_toFinLp p f)
  filter_upwards [coeFn_ofFinLp p (toFinLp p f), h2] with z h1 h2
  rw [h1, h2, WithLp.toLp_ofLp]

theorem toFinLp_ofFinLp (f : Lp ℝ p (volume : Measure (Fin 3 → ℝ))) :
    toFinLp p (ofFinLp p f) = f := by
  apply Lp.ext
  have h2 : (fun x : Fin 3 → ℝ => (ofFinLp p f) (WithLp.toLp 2 x)) =ᵐ[volume]
      fun x => f (WithLp.ofLp (WithLp.toLp 2 x)) :=
    mp_toLp.quasiMeasurePreserving.ae_eq_comp (coeFn_ofFinLp p f)
  filter_upwards [coeFn_toFinLp p (ofFinLp p f), h2] with x h1 h2
  rw [h1, h2]

theorem norm_toFinLp (f : Lp ℝ p (volume : Measure Space)) : ‖toFinLp p f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f mp_toLp

theorem norm_ofFinLp (f : Lp ℝ p (volume : Measure (Fin 3 → ℝ))) : ‖ofFinLp p f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f mp_ofLp

/-- `toFinLp` of the class of a function is the class of the composed function. -/
theorem toFinLp_toLp {f : Space → ℝ} (hf : MemLp f p volume) :
    toFinLp p (hf.toLp f) = (hf.comp_measurePreserving mp_toLp).toLp (f ∘ WithLp.toLp 2) :=
  rfl

end Lp

/-- At `p = 2`, `toFinLp` preserves the inner product. -/
theorem inner_toFinLp_two (f g : Lp ℝ 2 (volume : Measure Space)) :
    inner ℝ (toFinLp 2 f) (toFinLp 2 g) = inner ℝ f g :=
  (Lp.compMeasurePreservingₗᵢ ℝ (WithLp.toLp 2 : (Fin 3 → ℝ) → Space)
    mp_toLp).inner_map_map f g

/-! ### The isotropic weight on `Fin 3 → ℝ` -/

/-- The weight `a = (1,1,1)`: its gauge `CZ.anisoNorm isoWeight` is the sup norm. -/
abbrev isoWeight : Fin 3 → ℕ+ := 1

theorem homDim_isoWeight : CZ.homDim isoWeight = 3 := rfl

theorem abs_le_anisoNorm_iso (x : Fin 3 → ℝ) (j : Fin 3) :
    |x j| ≤ CZ.anisoNorm isoWeight x := by
  simpa using CZ.abs_le_anisoNorm_pow isoWeight x j

/-- The sup norm is at most the Euclidean norm. -/
theorem anisoNorm_iso_le_norm (x : Fin 3 → ℝ) :
    CZ.anisoNorm isoWeight x ≤ ‖(WithLp.toLp 2 x : Space)‖ := by
  rw [CZ.anisoNorm_le_iff_abs _ (norm_nonneg _)]
  intro j
  simp only [Pi.one_apply, PNat.one_coe, pow_one]
  have h := PiLp.norm_apply_le (WithLp.toLp 2 x : Space) j
  simpa [Real.norm_eq_abs] using h

/-- The Euclidean norm squared is at most three times the sup norm squared. -/
theorem norm_sq_le_three_mul_anisoNorm_iso (x : Fin 3 → ℝ) :
    ‖(WithLp.toLp 2 x : Space)‖ ^ 2 ≤ 3 * CZ.anisoNorm isoWeight x ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ i : Fin 3, ‖(WithLp.toLp 2 x : Space) i‖ ^ 2
      ≤ ∑ _i : Fin 3, CZ.anisoNorm isoWeight x ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [PiLp.toLp_apply, Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_le_anisoNorm_iso x i) 2
    _ = 3 * CZ.anisoNorm isoWeight x ^ 2 := by simp

end UnforcedLeray.RieszLp
