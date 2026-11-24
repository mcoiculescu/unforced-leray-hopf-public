import UnforcedLeray.Lib.LerayC.ComplexComm

/-!
# B0414 helper: at `q = 2` the complex Leray projection is the orthogonal projection onto the
distributionally solenoidal fields

Blueprint unit B0414 (`paper/main.tex` lines 7340–7342: "it is an orthogonal projection at
`q = 2`"). The space `Y_q` of tex 7313–7317 is built on `L^q(ℝ³; ℂ³)`, so the statement is
needed for complex fields. The real statement is the drafted `RieszLp.lerayLp_two`
(`Lib/LerayLp/Leray.lean`): `lerayLp 2 = Leray.projection`, the library's orthogonal projection
onto `Leray.solenoidalSubspace` (`lean/UnforcedLeray/Analysis/LerayProjection/Basic.lean`).

* `IsSolenoidalC F`: `div F = 0` in distributions for `F : ℝ³ → ℂ³`, the complex analogue of
  the library's `IsSolenoidal` (pairing against real compactly supported smooth tests, with
  integrable pairings), and `isSolenoidalC_iff`: it holds iff the real and imaginary parts are
  solenoidal;
* `solenoidalC`: the closed `ℂ`-subspace of `L²(ℝ³; ℂ³)` of distributionally solenoidal
  fields (`mem_solenoidalC_iff`, `isClosed_solenoidalC`);
* `re_inner_L2C`: `Re ⟪u, v⟫_{L²(ℂ³)} = ⟪Re u, Re v⟫ + ⟪Im u, Im v⟫`;
* `lerayC_two`: `lerayC 2 = solenoidalC.starProjection`, the orthogonal projection;
* `lerayC_ae_eq_starProjection`: for `1 < q < ∞` and `F ∈ L^q ∩ L²(ℝ³; ℂ³)`, `lerayC q F` is
  a.e. the orthogonal projection of `F`, so `lerayC q` is the manuscript's `P_σ` at every
  exponent (scoping decision D5 and bypass §4.2 of `INF01-CZ.md`: the operator is identified
  through the `L²` orthogonal projection, not through the Fourier multiplier).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology InnerProductSpace

namespace UnforcedLeray.B0414

open UnforcedLeray.RieszLp
open UnforcedLeray.PhaseSpace (CVec3)

/-! ### Distributional solenoidality of complex fields -/

/-- **B0414 (ii), the constraint.** `div F = 0` in distributions for a complex field
`F : ℝ³ → ℂ³`: for every real compactly supported smooth test `φ` the pairing
`x ↦ ∑ᵢ Fᵢ(x) ∂ᵢφ(x)` is integrable and has integral zero (the complex analogue of the
library's `IsSolenoidal`, `lean/UnforcedLeray/Statement.lean`; tex 7333–7334, "impose
`div w = 0` distributionally"). Complex tests give nothing more, by linearity. -/
structure IsSolenoidalC (F : Space → CVec3) : Prop where
  integrable : ∀ φ, IsSpatialTest φ →
    Integrable (fun x => ∑ i : Fin 3, F x i * (spatialTestDerivative i φ x : ℂ))
  identity : ∀ φ, IsSpatialTest φ →
    (∫ x, ∑ i : Fin 3, F x i * (spatialTestDerivative i φ x : ℂ)) = 0

theorem re_divPairing (z : CVec3) (d : Fin 3 → ℝ) :
    (∑ i : Fin 3, z i * (d i : ℂ)).re = ∑ i : Fin 3, (reV z) i * d i := by
  simp [Complex.re_sum, Complex.mul_re]

theorem im_divPairing (z : CVec3) (d : Fin 3 → ℝ) :
    (∑ i : Fin 3, z i * (d i : ℂ)).im = ∑ i : Fin 3, (imV z) i * d i := by
  simp [Complex.im_sum, Complex.mul_im]

/-- A complex field is distributionally solenoidal iff its real and imaginary parts are. -/
theorem isSolenoidalC_iff (F : Space → CVec3) :
    IsSolenoidalC F ↔
      IsSolenoidal (fun x => reV (F x)) ∧ IsSolenoidal (fun x => imV (F x)) := by
  constructor
  · intro h
    refine ⟨⟨fun φ hφ => ?_, fun φ hφ => ?_⟩, ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩⟩
    · have := (h.integrable φ hφ).re
      simpa [re_divPairing] using this
    · have h1 := integral_re (h.integrable φ hφ)
      rw [h.identity φ hφ] at h1
      simpa [re_divPairing] using h1
    · have := (h.integrable φ hφ).im
      simpa [im_divPairing] using this
    · have h1 := integral_im (h.integrable φ hφ)
      rw [h.identity φ hφ] at h1
      simpa [im_divPairing] using h1
  · rintro ⟨hre, him⟩
    have hint : ∀ φ, IsSpatialTest φ →
        Integrable (fun x => ∑ i : Fin 3, F x i * (spatialTestDerivative i φ x : ℂ)) := by
      intro φ hφ
      refine Integrable.re_im_iff.mp ⟨?_, ?_⟩
      · simpa [re_divPairing] using hre.integrable φ hφ
      · simpa [im_divPairing] using him.integrable φ hφ
    refine ⟨hint, fun φ hφ => ?_⟩
    apply Complex.ext
    · have h1 := integral_re (hint φ hφ)
      simp only [RCLike.re_to_complex] at h1
      rw [← h1]
      simpa [re_divPairing] using hre.identity φ hφ
    · have h1 := integral_im (hint φ hφ)
      simp only [RCLike.im_to_complex] at h1
      rw [← h1]
      simpa [im_divPairing] using him.identity φ hφ

/-! ### Real and imaginary parts on `L^p` -/

section Parts

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem reV_ofReV_compLpL (G : Lp Space p (volume : Measure Space)) :
    reV.compLpL p volume (ofReV.compLpL p volume G) = G := by
  rw [compLpL_compLpL]
  apply Lp.ext
  filter_upwards [(reV.comp ofReV).coeFn_compLpL (μ := volume) (p := p) G] with x hx
  rw [hx, ContinuousLinearMap.comp_apply, reV_ofReV]

theorem reV_ofImV_compLpL (G : Lp Space p (volume : Measure Space)) :
    reV.compLpL p volume (ofImV.compLpL p volume G) = 0 := by
  rw [compLpL_compLpL]
  apply Lp.ext
  filter_upwards [(reV.comp ofImV).coeFn_compLpL (μ := volume) (p := p) G,
    Lp.coeFn_zero Space p (volume : Measure Space)] with x hx h0
  rw [hx, h0, ContinuousLinearMap.comp_apply]
  ext i
  simp

theorem imV_ofReV_compLpL (G : Lp Space p (volume : Measure Space)) :
    imV.compLpL p volume (ofReV.compLpL p volume G) = 0 := by
  rw [compLpL_compLpL]
  apply Lp.ext
  filter_upwards [(imV.comp ofReV).coeFn_compLpL (μ := volume) (p := p) G,
    Lp.coeFn_zero Space p (volume : Measure Space)] with x hx h0
  rw [hx, h0, ContinuousLinearMap.comp_apply, imV_ofReV]
  rfl

theorem imV_ofImV_compLpL (G : Lp Space p (volume : Measure Space)) :
    imV.compLpL p volume (ofImV.compLpL p volume G) = G := by
  rw [compLpL_compLpL]
  apply Lp.ext
  filter_upwards [(imV.comp ofImV).coeFn_compLpL (μ := volume) (p := p) G] with x hx
  rw [hx, ContinuousLinearMap.comp_apply]
  ext i
  simp

/-- `Re (𝔓F) = 𝔓(Re F)`. -/
theorem reV_lerayC (hp1 : 1 < p) (hp : p ≠ ⊤) (F : Lp CVec3 p (volume : Measure Space)) :
    reV.compLpL p volume (lerayC p hp1 hp F) = lerayLp p hp1 hp (reV.compLpL p volume F) := by
  rw [lerayC_apply, map_add, reV_ofReV_compLpL, reV_ofImV_compLpL, add_zero]

/-- `Im (𝔓F) = 𝔓(Im F)`. -/
theorem imV_lerayC (hp1 : 1 < p) (hp : p ≠ ⊤) (F : Lp CVec3 p (volume : Measure Space)) :
    imV.compLpL p volume (lerayC p hp1 hp F) = lerayLp p hp1 hp (imV.compLpL p volume F) := by
  rw [lerayC_apply, map_add, imV_ofReV_compLpL, imV_ofImV_compLpL, zero_add]

/-- `c • G = Re c • G + Im c • (i G)`. -/
theorem smul_eq_re_add_im (c : ℂ) (G : Lp CVec3 p (volume : Measure Space)) :
    c • G = c.re • G + c.im • (Complex.I • G) := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul, RCLike.real_smul_eq_coe_smul (K := ℂ) c.re G,
    RCLike.real_smul_eq_coe_smul (K := ℂ) c.im (Complex.I • G)]
  rfl

theorem reV_compLpL_smul (c : ℂ) (G : Lp CVec3 p (volume : Measure Space)) :
    reV.compLpL p volume (c • G) =
      c.re • reV.compLpL p volume G + c.im • (-(imV.compLpL p volume G)) := by
  rw [smul_eq_re_add_im c G, map_add, map_smul, map_smul, reV_compLpL_I_smul]

theorem imV_compLpL_smul (c : ℂ) (G : Lp CVec3 p (volume : Measure Space)) :
    imV.compLpL p volume (c • G) =
      c.re • imV.compLpL p volume G + c.im • reV.compLpL p volume G := by
  rw [smul_eq_re_add_im c G, map_add, map_smul, map_smul, imV_compLpL_I_smul]

end Parts

/-! ### The solenoidal subspace of `L²(ℝ³; ℂ³)` -/

/-- **B0414 (ii), the range.** The distributionally solenoidal fields in `L²(ℝ³; ℂ³)`, as a
`ℂ`-subspace (membership is `IsSolenoidalC`, `mem_solenoidalC_iff`). -/
def solenoidalC : Submodule ℂ (Lp CVec3 2 (volume : Measure Space)) where
  carrier := {F | reV.compLpL 2 volume F ∈ Leray.solenoidalSubspace ∧
    imV.compLpL 2 volume F ∈ Leray.solenoidalSubspace}
  add_mem' {F G} hF hG := by
    refine ⟨?_, ?_⟩
    · rw [map_add]; exact add_mem hF.1 hG.1
    · rw [map_add]; exact add_mem hF.2 hG.2
  zero_mem' := by
    refine ⟨?_, ?_⟩ <;> rw [map_zero] <;> exact zero_mem _
  smul_mem' c F hF := by
    refine ⟨?_, ?_⟩
    · rw [reV_compLpL_smul]
      exact add_mem (Submodule.smul_mem _ _ hF.1) (Submodule.smul_mem _ _ (neg_mem hF.2))
    · rw [imV_compLpL_smul]
      exact add_mem (Submodule.smul_mem _ _ hF.2) (Submodule.smul_mem _ _ hF.1)

theorem mem_solenoidalC_iff_parts (F : Lp CVec3 2 (volume : Measure Space)) :
    F ∈ solenoidalC ↔ reV.compLpL 2 volume F ∈ Leray.solenoidalSubspace ∧
      imV.compLpL 2 volume F ∈ Leray.solenoidalSubspace := Iff.rfl

/-- Membership in `solenoidalC` is exactly distributional solenoidality of the class. -/
theorem mem_solenoidalC_iff (F : Lp CVec3 2 (volume : Measure Space)) :
    F ∈ solenoidalC ↔ IsSolenoidalC (F : Space → CVec3) := by
  rw [mem_solenoidalC_iff_parts, Leray.mem_solenoidalSubspace_iff,
    Leray.mem_solenoidalSubspace_iff, isSolenoidalC_iff]
  have hre := reV.coeFn_compLpL (μ := (volume : Measure Space)) (p := 2) F
  have him := imV.coeFn_compLpL (μ := (volume : Measure Space)) (p := 2) F
  exact ⟨fun h => ⟨Leray.solenoidal_congr_ae h.1 hre, Leray.solenoidal_congr_ae h.2 him⟩,
    fun h => ⟨Leray.solenoidal_congr_ae h.1 hre.symm, Leray.solenoidal_congr_ae h.2 him.symm⟩⟩

theorem isClosed_solenoidalC : IsClosed (solenoidalC : Set (Lp CVec3 2 (volume : Measure Space))) :=
  (Leray.isClosed_solenoidalSubspace.preimage (reV.compLpL 2 volume).continuous).inter
    (Leray.isClosed_solenoidalSubspace.preimage (imV.compLpL 2 volume).continuous)

instance solenoidalC_completeSpace : CompleteSpace solenoidalC :=
  isClosed_solenoidalC.completeSpace_coe

/-! ### The complex `L²` inner product through real parts -/

theorem re_inner_CVec3 (z w : CVec3) :
    (⟪z, w⟫_ℂ).re = ⟪reV z, reV w⟫_ℝ + ⟪imV z, imV w⟫_ℝ := by
  simp only [PiLp.inner_apply, Complex.re_sum, RCLike.inner_apply, reV_apply, imV_apply,
    conj_trivial, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]

/-- `Re ⟪u, v⟫_{L²(ℝ³;ℂ³)} = ⟪Re u, Re v⟫_{L²(ℝ³;ℝ³)} + ⟪Im u, Im v⟫_{L²(ℝ³;ℝ³)}`. -/
theorem re_inner_L2C (u v : Lp CVec3 2 (volume : Measure Space)) :
    (⟪u, v⟫_ℂ).re =
      ⟪reV.compLpL 2 volume u, reV.compLpL 2 volume v⟫_ℝ +
        ⟪imV.compLpL 2 volume u, imV.compLpL 2 volume v⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def, L2.inner_def]
  have h1 := integral_re (L2.integrable_inner (𝕜 := ℂ) u v)
  simp only [RCLike.re_to_complex] at h1
  rw [← h1, ← integral_add (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
  refine integral_congr_ae ?_
  filter_upwards [reV.coeFn_compLpL (μ := (volume : Measure Space)) (p := 2) u,
    reV.coeFn_compLpL (μ := (volume : Measure Space)) (p := 2) v,
    imV.coeFn_compLpL (μ := (volume : Measure Space)) (p := 2) u,
    imV.coeFn_compLpL (μ := (volume : Measure Space)) (p := 2) v] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  exact re_inner_CVec3 (u x) (v x)

/-! ### `lerayC 2` is the orthogonal projection -/

theorem lerayC_two_mem (F : Lp CVec3 2 (volume : Measure Space)) :
    lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top F ∈ solenoidalC := by
  refine ⟨?_, ?_⟩
  · rw [reV_lerayC, lerayLp_two]
    exact Leray.projection_mem _
  · rw [imV_lerayC, lerayLp_two]
    exact Leray.projection_mem _

theorem re_inner_residual_eq_zero (F : Lp CVec3 2 (volume : Measure Space))
    {w : Lp CVec3 2 (volume : Measure Space)} (hw : w ∈ solenoidalC) :
    (⟪F - lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top F, w⟫_ℂ).re = 0 := by
  rw [re_inner_L2C, map_sub, map_sub, reV_lerayC, imV_lerayC, lerayLp_two,
    Submodule.inner_left_of_mem_orthogonal hw.1 (Leray.residual_mem_orthogonal _),
    Submodule.inner_left_of_mem_orthogonal hw.2 (Leray.residual_mem_orthogonal _), add_zero]

theorem inner_residual_eq_zero (F : Lp CVec3 2 (volume : Measure Space))
    {w : Lp CVec3 2 (volume : Measure Space)} (hw : w ∈ solenoidalC) :
    ⟪F - lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top F, w⟫_ℂ = 0 := by
  have hre := re_inner_residual_eq_zero F hw
  have hI := re_inner_residual_eq_zero F (Submodule.smul_mem solenoidalC Complex.I hw)
  rw [inner_smul_right, Complex.mul_re, Complex.I_re, Complex.I_im] at hI
  apply Complex.ext
  · exact hre
  · simpa using hI

/-- **B0414 (ii).** At `q = 2` the complex Leray projection is the orthogonal projection of
`L²(ℝ³; ℂ³)` onto the distributionally solenoidal fields (tex 7340–7342). -/
theorem lerayC_two :
    lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top = solenoidalC.starProjection := by
  ext1 F
  symm
  exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero (lerayC_two_mem F)
    fun w hw => inner_residual_eq_zero F hw

/-- At `q = 2` the norm of `P_σ` on `L²(ℝ³; ℂ³)` is at most `1` (`C_2 = 1` in tex 7444). -/
theorem norm_lerayC_two_le : ‖lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ ≤ 1 := by
  rw [lerayC_two]
  exact solenoidalC.starProjection_norm_le

/-- At `q = 2`, `P_σ` is symmetric on `L²(ℝ³; ℂ³)`. -/
theorem inner_lerayC_two_left_eq_right (F G : Lp CVec3 2 (volume : Measure Space)) :
    ⟪lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top F, G⟫_ℂ =
      ⟪F, lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top G⟫_ℂ := by
  rw [lerayC_two]
  exact solenoidalC.inner_starProjection_left_eq_right F G

/-- `P_σ F = F` exactly for the distributionally solenoidal `F ∈ L²(ℝ³; ℂ³)`. -/
theorem lerayC_two_eq_self_iff (F : Lp CVec3 2 (volume : Measure Space)) :
    lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top F = F ↔ IsSolenoidalC (F : Space → CVec3) := by
  rw [lerayC_two, Submodule.starProjection_eq_self_iff, mem_solenoidalC_iff]

/-- **B0414 (i), identification.** For `1 < q < ∞` and `F ∈ L^q ∩ L²(ℝ³; ℂ³)`, `lerayC q F`
is a.e. the orthogonal projection of `F` onto the solenoidal fields; so the bounded operators
`lerayC q` are one operator `P_σ` across exponents (scoping decision D5). -/
theorem lerayC_ae_eq_starProjection {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq1 : 1 < q) (hq : q ≠ ⊤)
    (F : Lp CVec3 q (volume : Measure Space)) (hF2 : MemLp F 2 volume) :
    (lerayC q hq1 hq F : Space → CVec3) =ᵐ[volume] solenoidalC.starProjection (hF2.toLp F) := by
  have h := lerayC_consistent hq1 hq ENNReal.one_lt_two ENNReal.ofNat_ne_top (Lp.memLp F) hF2
  rw [Lp.toLp_coeFn, lerayC_two] at h
  exact h

end UnforcedLeray.B0414
