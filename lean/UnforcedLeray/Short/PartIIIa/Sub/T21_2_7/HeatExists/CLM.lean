import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.Defs

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8`: the kernel operators as bounded maps of `X_{-m,c}`

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
(the free part of the Volterra iteration on `X_{-m,c}` at fixed `ν > 0`, `c > 0`).

`KerYoung c m k M` is the weighted periodic Young bound of the kernel operator `adjKerOp c k`
on `X_{-m,c} = AdjX c m`, in the absolute (`lintegral`) form:
`‖∫ |k(· - y)| |f̃(y)| dy‖_{X_{-m,c}} ≤ M ‖f‖_{X_{-m,c}}`.  Under it, `adjKerOp c k` maps
`X_{-m,c}` into itself (`memLp_adjKerOp`), its integrals converge at a.e. point of the cell
(`ae_integrable_adjKerOp`), and it is the bounded linear map `kerCLM` (built with
`LinearMap.mkContinuous`), with `⇑(kerCLM w) = adjKerOp c k ⇑w` a.e. (`coeFn_kerCLM`) and
`‖kerCLM‖ ≤ M` (`norm_kerCLM_le`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **The weighted periodic Young bound of a kernel `k` on `X_{-m,c}`** (SP 2819-2836):
`‖x ↦ ∫ |k(x - y)| |f̃(y)| dy‖_{L²(C_c, ⟨x⟩^{-2m})} ≤ M ‖f‖_{L²(C_c, ⟨x⟩^{-2m})}` for every
`f ∈ X_{-m,c}`, `f̃ = perRep c f`. -/
def KerYoung (c m : ℝ) (k : ℝ × ℝ → ℝ) (M : ℝ) : Prop :=
  ∀ w : AdjX c m,
    eLpNorm (fun x => ∫⁻ y, ‖k (x - y)‖ₑ * ‖perRep c (⇑w) y‖ₑ) 2 (B0579.cellMeasure c (-m)) ≤
      ENNReal.ofReal M * eLpNorm (⇑w) 2 (B0579.cellMeasure c (-m))

section KerCLM

variable {c m : ℝ} {k : ℝ × ℝ → ℝ} {M : ℝ}

theorem enorm_adjKerOp_le (c : ℝ) (k : ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    ‖adjKerOp c k f x‖ₑ ≤ ∫⁻ y, ‖k (x - y)‖ₑ * ‖perRep c f y‖ₑ := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun y => ?_))
  rw [enorm_mul, enorm_eq_nnnorm, enorm_eq_nnnorm (k (x - y)), Complex.nnnorm_real]

theorem aestronglyMeasurable_adjKerOp (hc : 0 < c) (hk : Continuous k) (w : AdjX c m) :
    AEStronglyMeasurable (adjKerOp c k ⇑w) (B0579.cellMeasure c (-m)) :=
  (stronglyMeasurable_adjKerOp hc hk (Lp.stronglyMeasurable w)).aestronglyMeasurable

theorem eLpNorm_adjKerOp_le (hY : KerYoung c m k M) (w : AdjX c m) :
    eLpNorm (adjKerOp c k ⇑w) 2 (B0579.cellMeasure c (-m)) ≤
      ENNReal.ofReal M * eLpNorm (⇑w) 2 (B0579.cellMeasure c (-m)) :=
  (eLpNorm_mono_enorm fun x => (enorm_adjKerOp_le c k ⇑w x).trans
    (le_of_eq (enorm_eq_self _).symm)).trans (hY w)

/-- Under the Young bound, the kernel operator maps `X_{-m,c}` into itself. -/
theorem memLp_adjKerOp (hc : 0 < c) (hk : Continuous k) (hY : KerYoung c m k M)
    (w : AdjX c m) : MemLp (adjKerOp c k ⇑w) 2 (B0579.cellMeasure c (-m)) :=
  ⟨aestronglyMeasurable_adjKerOp hc hk w,
    (eLpNorm_adjKerOp_le hY w).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top w))⟩

/-- Under the Young bound, the defining integral converges at a.e. point of the cell. -/
theorem ae_integrable_adjKerOp (hc : 0 < c) (hk : Continuous k) (hY : KerYoung c m k M)
    (w : AdjX c m) :
    ∀ᵐ x ∂(B0579.cellMeasure c (-m)),
      Integrable (fun y => (k (x - y) : ℂ) * perRep c (⇑w) y) := by
  have hper := stronglyMeasurable_perRep hc (Lp.stronglyMeasurable w)
  have hfin : eLpNorm (fun x => ∫⁻ y, ‖k (x - y)‖ₑ * ‖perRep c (⇑w) y‖ₑ) 2
      (B0579.cellMeasure c (-m)) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_lt_top w).ne) (hY w)
  have hmeas : Measurable (fun x => ∫⁻ y, ‖k (x - y)‖ₑ * ‖perRep c (⇑w) y‖ₑ) := by
    have : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
        ‖k (p.1 - p.2)‖ₑ * ‖perRep c (⇑w) p.2‖ₑ) :=
      ((hk.comp (continuous_fst.sub continuous_snd)).measurable.enorm).mul
        ((hper.measurable.comp measurable_snd).enorm)
    exact this.lintegral_prod_right'
  have hae := UnforcedLeray.B0295.ae_lt_top_of_eLpNorm_ne_top hmeas.aemeasurable
    (by norm_num) (by norm_num) hfin
  filter_upwards [hae] with x hx
  refine ⟨((Complex.continuous_ofReal.comp
    (hk.comp (continuous_const.sub continuous_id))).aestronglyMeasurable).mul
      hper.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) hx
  rw [enorm_mul, enorm_eq_nnnorm, enorm_eq_nnnorm (k (x - y)), Complex.nnnorm_real]

/-- The kernel operator as a linear map of `X_{-m,c}` (under the Young bound). -/
def kerLin (hc : 0 < c) (hk : Continuous k) (hY : KerYoung c m k M) :
    AdjX c m →ₗ[ℂ] AdjX c m where
  toFun w := (memLp_adjKerOp hc hk hY w).toLp _
  map_add' w₁ w₂ := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    rw [adjKerOp_congr_ae hc k (Lp.coeFn_add w₁ w₂)]
    filter_upwards [ae_integrable_adjKerOp hc hk hY w₁, ae_integrable_adjKerOp hc hk hY w₂]
      with x hx1 hx2
    exact adjKerOp_add_apply hx1 hx2
  map_smul' a w := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    rw [adjKerOp_congr_ae hc k (Lp.coeFn_smul a w), adjKerOp_smul]

/-- **The kernel operator as a bounded operator of `X_{-m,c}`** (SP 2819-2836), with norm at
most the Young constant `M`. -/
def kerCLM (hc : 0 < c) (hk : Continuous k) (hM : 0 ≤ M) (hY : KerYoung c m k M) :
    AdjX c m →L[ℂ] AdjX c m :=
  (kerLin hc hk hY).mkContinuous M fun w => by
    change ‖(memLp_adjKerOp hc hk hY w).toLp _‖ ≤ M * ‖w‖
    rw [Lp.norm_toLp, Lp.norm_def]
    calc (eLpNorm (adjKerOp c k ⇑w) 2 (B0579.cellMeasure c (-m))).toReal
        ≤ (ENNReal.ofReal M * eLpNorm (⇑w) 2 (B0579.cellMeasure c (-m))).toReal :=
          ENNReal.toReal_mono
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_lt_top w).ne)
            (eLpNorm_adjKerOp_le hY w)
      _ = M * (eLpNorm (⇑w) 2 (B0579.cellMeasure c (-m))).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM]

theorem coeFn_kerCLM (hc : 0 < c) (hk : Continuous k) (hM : 0 ≤ M) (hY : KerYoung c m k M)
    (w : AdjX c m) :
    ⇑(kerCLM hc hk hM hY w) =ᵐ[B0579.cellMeasure c (-m)] adjKerOp c k ⇑w :=
  (memLp_adjKerOp hc hk hY w).coeFn_toLp

theorem norm_kerCLM_le (hc : 0 < c) (hk : Continuous k) (hM : 0 ≤ M) (hY : KerYoung c m k M) :
    ‖kerCLM hc hk hM hY‖ ≤ M :=
  LinearMap.mkContinuous_norm_le _ hM _

/-- The distance from the identity, through the representative:
`‖kerCLM w - w‖ = ‖adjKerOp c k ⇑w - ⇑w‖_{X_{-m,c}}`. -/
theorem norm_kerCLM_sub (hc : 0 < c) (hk : Continuous k) (hM : 0 ≤ M) (hY : KerYoung c m k M)
    (w : AdjX c m) :
    ‖kerCLM hc hk hM hY w - w‖ =
      (eLpNorm (fun x => adjKerOp c k (⇑w) x - w x) 2 (B0579.cellMeasure c (-m))).toReal := by
  rw [Lp.norm_def]
  congr 1
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (kerCLM hc hk hM hY w) w, coeFn_kerCLM hc hk hM hY w]
    with x hx hk'
  rw [hx, Pi.sub_apply, hk']

end KerCLM

end UnforcedLeray.Short.IIIa
