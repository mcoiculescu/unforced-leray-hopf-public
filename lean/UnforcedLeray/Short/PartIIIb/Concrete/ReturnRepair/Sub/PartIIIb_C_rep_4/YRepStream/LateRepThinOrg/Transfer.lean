import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateEarly
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree

/-!
# `PartIII-b:C/rep/4/4/1/org/5/org` (a): the gain transfer on the thin receiver

Source `the November 2 reference manuscript` 5318 (late output:
`g(s)^{-1} ≤ e^{-4γ/(9ν)}` for `s ≥ 0.8/ν`), 5322-5333 (the table is "in the split stress
norm", the late-output entries are multiplied by `e^{-4γ/(9ν)}`), 2697-2700 and 5609 (the split
stress norm `‖g⁻¹T‖_Z = ‖g⁻¹T₁‖_{Z₁} + ρ_b^{-1/2}‖g⁻¹T₂‖_{H_T}`).

The stress norm of `LStr` carries the gain `g⁻¹` in its measure (`gainZ1Measure =
z1Measure·g⁻²`).  The separated-kernel bounds are proved without the gain (`z1Ung`, the norm of
`Z₁` itself, 2697); the output gain is then read off from the support of the output
(`lrt_gainZ1_le`): a thin stress vanishing at ages `s < a` has gained norm at most
`sup_{s ≥ a} g(s)^{-1}` times its ungained norm.  On late output `a = 0.8/ν` and the supremum is
`≤ e^{-4γ/(9ν)}` (`lrt_gain_late`, 5318); on young output (the early-source region) one uses
`g⁻¹ ≤ 1`.

* `lrt_gain_late` : `g(s)^{-1} ≤ e^{-4γ/(9ν)}` for `s ≥ 0.8/ν` (proved, local copy of
  `ftGain_late`).
* `z1Ung` : the ungained `Z₁` norm `(∫|T₁|² W² s^{-1/2} dς)^{1/2}` of a chart tensor.
* `lrt_norm_thinPart` : `‖(T₁,0)‖_Z = ‖T₁‖`.
* `lrt_gainZ1_le_ae`, `lrt_gainZ1_le`, `lrt_gainZ1_le_glob` : the gain transfer (proved; general,
  on an age region, with a global bound).
* `lrt_z1Ung_mono` : `z1Ung` is monotone under a pointwise a.e. bound (proved).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Late output**: `g(s)^{-1} ≤ e^{-4γ/(9ν)}` for `s ≥ 0.8/ν` (source 5318;
`g(s) = e^{γs/(1+νs)}`, 3881, 5117).  Local copy of `ftGain_late` (`Org/FarThinParts.lean`),
which cannot be imported together with `Org/YThinTrans.lean`. -/
theorem lrt_gain_late {γ ν s : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (hs : 4 / 5 / ν ≤ s) :
    (UnforcedLeray.Short.IIIa.gainG γ ν s)⁻¹ ≤ Real.exp (-(4 * γ / 9) / ν) := by
  unfold UnforcedLeray.Short.IIIa.gainG
  have hνs : 4 / 5 ≤ s * ν := (div_le_iff₀ hν).1 hs
  have hs0 : 0 < s := by
    have : 0 < s * ν := by linarith
    exact pos_of_mul_pos_left this hν.le
  have h1 : 0 < 1 + ν * s := by positivity
  rw [← Real.exp_neg, Real.exp_le_exp, neg_div, neg_le_neg_iff, div_le_div_iff₀ hν h1]
  nlinarith [mul_nonneg hγ (sub_nonneg.2 hνs)]

/-- On late output the inverse chart gain is at most `e^{-4γ/(9ν)}` (source 5318). -/
theorem lrt_ginv_late {γ ν : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (p : Chart) (hp : 4 / 5 / ν ≤ p.1) :
    ginv γ ν p ≤ Real.exp (-(4 * γ / 9) / ν) := by
  have h0 : 0 ≤ p.1 := le_trans (by positivity) hp
  unfold ginv
  rw [max_eq_left h0]
  exact lrt_gain_late hγ hν hp

/-- **The ungained `Z₁` norm** `‖T₁‖_{Z₁} = (∫ |T₁|² W² s^{-1/2} dς)^{1/2}` of a chart tensor
(source 2697; the norm of the split stress space without the gain `g⁻¹`). -/
def z1Ung (c mZ : ℝ) (f : Chart → Ten3) : ℝ≥0∞ :=
  (∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ)) ^ (1 / 2 : ℝ)

/-- The thin receiver `(T₁, 0)` of the split stress norm has norm `‖T₁‖` (source 5609). -/
theorem lrt_norm_thinPart {c mZ ρb γ ν : ℝ} (x : StrG c mZ ρb γ ν) :
    ‖thinPart x‖ = ‖x.fst‖ := by
  rw [WithLp.prod_norm_eq_of_L1]
  simp [thinPart]

/-- `z1Ung` is monotone under an a.e. pointwise bound. -/
theorem lrt_z1Ung_mono {c mZ : ℝ} {f g : Chart → Ten3}
    (h : ∀ᵐ p ∂(z1Measure c mZ), ‖f p‖ ≤ ‖g p‖) : z1Ung c mZ f ≤ z1Ung c mZ g := by
  unfold z1Ung
  refine ENNReal.rpow_le_rpow (lintegral_mono_ae (h.mono fun p hp => ?_)) (by norm_num)
  exact ENNReal.rpow_le_rpow (enorm_le_iff_norm_le.2 hp) (by norm_num)

/-- **The gain transfer, general form**: if `g⁻¹ ≤ B` a.e. on the support of a thin stress `f`,
then `‖g⁻¹f‖_{Z₁} ≤ B‖f‖_{Z₁}` (source 5318, 5322-5333). -/
theorem lrt_gainZ1_le_ae {c mZ γ ν B : ℝ} (hB : 0 ≤ B)
    (f : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
    (hfg : ∀ᵐ p ∂(gainZ1Measure c mZ γ ν), (f : Chart → Ten3) p ≠ 0 → ginv γ ν p ≤ B) :
    ENNReal.ofReal ‖f‖ ≤ ENNReal.ofReal B * z1Ung c mZ f := by
  have hf' : ∀ᵐ p ∂(z1Measure c mZ), (f : Chart → Ten3) p ≠ 0 → ginv γ ν p ≤ B := by
    rw [← NearInst.ae_gainZ1Measure c mZ γ ν]; exact hfg
  have hd : Measurable fun p : Chart => ENNReal.ofReal (ginv γ ν p ^ 2) :=
    ENNReal.measurable_ofReal.comp ((NearInst.ginv_measurable' γ ν).pow_const 2)
  have e1 : ENNReal.ofReal ‖f‖ =
      (∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν)) ^ (1 / 2 : ℝ) := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  have step1 : ∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν) ≤
      ∫⁻ p, ENNReal.ofReal (B ^ 2) * ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ) := by
    refine le_trans (lintegral_withDensity_le_lintegral_mul (z1Measure c mZ) hd
      (fun p => ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ))) (lintegral_mono_ae (hf'.mono fun p hp => ?_))
    simp only [Pi.mul_apply]
    by_cases ha : (f : Chart → Ten3) p = 0
    · rw [ha]; simp
    · have h1 : ginv γ ν p ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (NearInst.ginv_pos' γ ν p).le (hp ha) 2
      gcongr
  rw [e1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at *
  unfold z1Ung
  calc (∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (B ^ 2) *
          ∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow step1 (by norm_num)
    _ = ENNReal.ofReal B *
          (∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (sq_nonneg B) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hB]

/-- **The gain transfer on an age region** (source 5318, 5322-5333): a thin stress `f` vanishing
at ages `s < a` has gained norm `‖g⁻¹f‖_{Z₁} ≤ B‖f‖_{Z₁}` whenever `g(s)^{-1} ≤ B` for `s ≥ a`
(late output: `a = 0.8/ν`, `B = e^{-4γ/(9ν)}`). -/
theorem lrt_gainZ1_le {c mZ γ ν a B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ p : Chart, a ≤ p.1 → ginv γ ν p ≤ B)
    (f : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
    (hf : ∀ᵐ p ∂(gainZ1Measure c mZ γ ν), p.1 < a → (f : Chart → Ten3) p = 0) :
    ENNReal.ofReal ‖f‖ ≤ ENNReal.ofReal B * z1Ung c mZ f := by
  refine lrt_gainZ1_le_ae hB f (hf.mono fun p hp hne => hg p ?_)
  by_contra h
  exact hne (hp (lt_of_not_ge h))

/-- **The gain transfer with a global bound** (young output, `g⁻¹ ≤ 1`, source 5318-5319). -/
theorem lrt_gainZ1_le_glob {c mZ γ ν B : ℝ} (hB : 0 ≤ B) (hg : ∀ p : Chart, ginv γ ν p ≤ B)
    (f : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) :
    ENNReal.ofReal ‖f‖ ≤ ENNReal.ofReal B * z1Ung c mZ f :=
  lrt_gainZ1_le_ae hB f (Eventually.of_forall fun p _ => hg p)

end UnforcedLeray.Short.PartIIIb.Concrete
