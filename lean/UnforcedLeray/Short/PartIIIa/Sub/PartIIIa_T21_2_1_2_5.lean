import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelDefs
import UnforcedLeray.Units.B0592.Kernel

/-!
# `KerDivPointwise` from the regularised stream function (SP 2081-2084, 3121)

`K_d = ∇^⊥ G_d` with `G_d = (4π)⁻¹ log den`, `den d z = cosh(2πη/d) - cos(2πq/d)`.  Regularise
`G_{d,ε} = (4π)⁻¹ log (den + ε)`, which is smooth and `d`-periodic in `q`; off the lattice
`∇^⊥ G_{d,ε} = (den / (den + ε)) K_d`, so `|∇^⊥ G_{d,ε}| ≤ |K_d|`, with pointwise limit `K_d`.
Integration by parts against the cylinder test `φ` kills the regularised pairing, and dominated
convergence (dominator `|K_d(x - y)| |∇φ|`, integrable by the near/far bounds) passes to the limit.

Leaves (each a Prop with its own task):
* `KerRegSmooth`, `KerRegDeriv` (the regularised stream and the identity with `K_d`);
* `KerIBP` (integration by parts against a test, for a smooth `q`-periodic `G`);
* `KerBandInt` (integrability of `K_d(· - y) ψ` against a band-supported test `ψ`, from
  `KerNearFar`);
* `KerLatticeNull` (the lattice `{den = 0}` is a null set).
The assembly `kerDivPointwise_of_parts` is proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The regularised stream function `G_{d,ε}(z) = (4π)⁻¹ log (den d z + ε)`. -/
def kerReg (d ε : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.log (UnforcedLeray.B0592.den d z + ε) / (4 * Real.pi)

/-- `G_{d,ε}` is smooth and `d`-periodic in `q` (`den d z ≥ 0`, so `den + ε > 0`). -/
def KerRegSmooth : Prop :=
  ∀ d ε : ℝ, 0 < d → 0 < ε → ContDiff ℝ ∞ (kerReg d ε) ∧
    ∀ z : ℝ × ℝ, kerReg d ε (z.1 + d, z.2) = kerReg d ε z

/-- Off the lattice, `∂_q G_{d,ε} = (den/(den+ε)) K_{d,1}` and
`∂_η G_{d,ε} = -(den/(den+ε)) K_{d,0}` (`K_d = (Re K, -Im K)`, `K = (2πi)⁻¹(π/d)cot(πz/d)`;
`B0592.hasDerivAt_stream_fst/snd`, cot identity via `Kernels.sin_eq_re_im`, `cos_eq_re_im`). -/
def KerRegDeriv : Prop :=
  ∀ d ε : ℝ, 0 < d → 0 < ε → ∀ z : ℝ × ℝ, UnforcedLeray.B0592.den d z ≠ 0 →
    B0579.pd 0 (kerReg d ε) z =
        UnforcedLeray.B0592.den d z / (UnforcedLeray.B0592.den d z + ε) * kerD d z 1 ∧
      B0579.pd 1 (kerReg d ε) z =
        -(UnforcedLeray.B0592.den d z / (UnforcedLeray.B0592.den d z + ε)) * kerD d z 0

/-- Integration by parts on the cell: for `G` smooth and `d`-periodic in `q`, and a cylinder test
`φ`, `∫_{C_d} (∂_qG ∂_ηφ - ∂_ηG ∂_qφ) = 0` (periodicity in `q`, band support in `η`, symmetry of
the second derivatives). -/
def KerIBP : Prop :=
  ∀ d : ℝ, 0 < d → ∀ G : ℝ × ℝ → ℝ, ContDiff ℝ ∞ G → (∀ z : ℝ × ℝ, G (z.1 + d, z.2) = G z) →
    ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest d φ →
      ∫ x in B0579.cell d, (B0579.pd 0 G x * B0579.pd 1 φ x - B0579.pd 1 G x * B0579.pd 0 φ x) = 0

/-- Integrability against band-supported tests (from `KerNearFar`: integrable near part, bounded
far part, periodic shift `Cyl.lintegral_cell_comp_sub_left`). -/
def KerBandInt : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ → ∀ (y : ℝ × ℝ) (j : Fin 2),
    IntegrableOn (fun x => kerD d (x - y) j * ψ x) (B0579.cell d)

/-- The lattice `{den d = 0} = dℤ × {0}` is a null set. -/
def KerLatticeNull : Prop :=
  ∀ d : ℝ, 0 < d → volume {z : ℝ × ℝ | UnforcedLeray.B0592.den d z = 0} = 0

lemma den_nonneg (d : ℝ) (z : ℝ × ℝ) : 0 ≤ UnforcedLeray.B0592.den d z := by
  rw [UnforcedLeray.B0592.den_eq]; positivity

lemma continuous_den (d : ℝ) : Continuous (UnforcedLeray.B0592.den d) := by
  unfold UnforcedLeray.B0592.den
  fun_prop

lemma pd_shift (G : ℝ × ℝ → ℝ) (y x : ℝ × ℝ) (j : Fin 2) :
    B0579.pd j (fun x => G (x - y)) x = B0579.pd j G (x - y) := by
  unfold B0579.pd
  have : (fun x : ℝ × ℝ => G (x - y)) = fun x => G (x + -y) := by
    funext x; rw [sub_eq_add_neg]
  rw [this, fderiv_comp_add_right (-y), sub_eq_add_neg]

/-- **Assembly** (SP 2081-2084, 3121). -/
theorem kerDivPointwise_of_parts (hS : KerRegSmooth) (hD : KerRegDeriv) (hI : KerIBP)
    (hB : KerBandInt) (hN : KerLatticeNull) : KerDivPointwise := by
  intro d hd φ hφ y
  have hd0 : 0 < d := by linarith
  set F : ℝ × ℝ → ℝ := fun x =>
    kerD d (x - y) 0 * B0579.pd 0 φ x + kerD d (x - y) 1 * B0579.pd 1 φ x with hF
  set dn : ℝ × ℝ → ℝ := fun x => UnforcedLeray.B0592.den d (x - y) with hdn
  have hFint : IntegrableOn F (B0579.cell d) :=
    (hB d hd _ (hφ.pd 0) y 0).add (hB d hd _ (hφ.pd 1) y 1)
  have hdn_cont : Continuous dn := (continuous_den d).comp (continuous_id.sub continuous_const)
  have hdn_nn : ∀ x, 0 ≤ dn x := fun x => den_nonneg d _
  -- the lattice is null
  have hnull : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), dn x ≠ 0 := by
    rw [ae_iff]
    have : {x : ℝ × ℝ | ¬ dn x ≠ 0} =
        (fun h : ℝ × ℝ => h + -y) ⁻¹' {z : ℝ × ℝ | UnforcedLeray.B0592.den d z = 0} := by
      ext x; simp [hdn, sub_eq_add_neg]
    rw [this, measure_preimage_add_right]
    exact hN d hd0
  have hnull' : ∀ᵐ x ∂(volume.restrict (B0579.cell d)), dn x ≠ 0 := ae_restrict_of_ae hnull
  -- regularised pairing vanishes
  have hzero : ∀ ε : ℝ, 0 < ε → ∫ x in B0579.cell d, dn x / (dn x + ε) * F x = 0 := by
    intro ε hε
    obtain ⟨hsm, hper⟩ := hS d ε hd0 hε
    have hGsm : ContDiff ℝ ∞ (fun x : ℝ × ℝ => kerReg d ε (x - y)) :=
      hsm.comp (contDiff_id.sub contDiff_const)
    have hGper : ∀ z : ℝ × ℝ, (fun x : ℝ × ℝ => kerReg d ε (x - y)) (z.1 + d, z.2) =
        (fun x : ℝ × ℝ => kerReg d ε (x - y)) z := by
      intro z
      have : ((z.1 + d, z.2) - y : ℝ × ℝ) = ((z - y).1 + d, (z - y).2) := by
        ext <;> simp <;> ring
      simp only [this, hper]
    have h0 := hI d hd0 _ hGsm hGper φ hφ
    rw [← h0]
    refine integral_congr_ae ?_
    filter_upwards [hnull'] with x hx
    have hx' : UnforcedLeray.B0592.den d (x - y) ≠ 0 := hx
    obtain ⟨e0, e1⟩ := hD d ε hd0 hε (x - y) hx'
    rw [pd_shift, pd_shift, e0, e1]
    simp only [hF, hdn]
    ring
  have hlim : Tendsto (fun ε : ℝ => ∫ x in B0579.cell d, dn x / (dn x + ε) * F x) (𝓝[>] 0)
      (𝓝 (∫ x in B0579.cell d, F x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖F x‖) ?_ ?_ hFint.norm ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      have hc : Continuous fun x => dn x / (dn x + ε) :=
        hdn_cont.div (hdn_cont.add continuous_const) (fun x => by linarith [hdn_nn x])
      exact hc.aestronglyMeasurable.mul hFint.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      refine Eventually.of_forall fun x => ?_
      have h1 : 0 ≤ dn x / (dn x + ε) := div_nonneg (hdn_nn x) (by linarith [hdn_nn x])
      have h2 : dn x / (dn x + ε) ≤ 1 := by
        rw [div_le_one (by linarith [hdn_nn x])]; linarith
      rw [norm_mul, Real.norm_of_nonneg h1]
      exact mul_le_of_le_one_left (norm_nonneg _) h2
    · filter_upwards [hnull'] with x hx
      have hpos : 0 < dn x := lt_of_le_of_ne (hdn_nn x) (Ne.symm hx)
      have h1 : Tendsto (fun ε : ℝ => dn x / (dn x + ε)) (𝓝 0) (𝓝 (dn x / (dn x + 0))) :=
        tendsto_const_nhds.div (tendsto_const_nhds.add tendsto_id) (by simpa using hpos.ne')
      rw [add_zero, div_self hpos.ne'] at h1
      simpa using (h1.mono_left nhdsWithin_le_nhds).mul_const (F x)
  have hlim0 : Tendsto (fun ε : ℝ => ∫ x in B0579.cell d, dn x / (dn x + ε) * F x) (𝓝[>] 0)
      (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hzero ε hε).symm
  exact tendsto_nhds_unique hlim hlim0

end UnforcedLeray.Short.IIIa
