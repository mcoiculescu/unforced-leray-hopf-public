import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Weighted `L²` spaces through a square root of the density (generic tool)

For the link between the gain-normed return spaces of `Concrete/ReturnOps.lean`
(`‖·‖ = ‖g⁻¹ ·‖`, source 5116-5128, 5143, 5609) and the ungained near spaces of
`Concrete/Spaces.lean` (source 2664-2701, 3866-3872).

* `IsDensityRoot μ' μ σ` : `σ > 0` measurable with `μ' = σ² μ`;
* `IsDensityRoot.rootEquiv` : the linear isometric equivalence `L²(μ'; E) ≃ L²(μ; E)`, `f ↦ σ f`,
  with `coeFn_rootEquiv` and `coeFn_rootEquiv_symm` (`g ↦ σ⁻¹ g`);
* `prodL1Iso` : the `ℓ¹` product of two linear isometric equivalences.

The vector-valued version of `B0656.IsSqrtDensity.mulL2Equiv` (which is real-valued).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

section Root

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `σ` is a positive measurable square root of the density of `μ'` with respect to `μ`:
`μ' = σ² μ`. -/
structure IsDensityRoot (μ' μ : Measure α) (σ : α → ℝ) : Prop where
  measurable : Measurable σ
  pos : ∀ x, 0 < σ x
  eq : μ' = μ.withDensity fun x => ENNReal.ofReal (σ x ^ 2)

variable {μ' μ : Measure α} {σ : α → ℝ}

namespace IsDensityRoot

theorem measurable_density (h : IsDensityRoot μ' μ σ) :
    Measurable fun x => ENNReal.ofReal (σ x ^ 2) :=
  ENNReal.measurable_ofReal.comp (h.measurable.pow_const 2)

theorem absCont (h : IsDensityRoot μ' μ σ) : μ ≪ μ' := by
  rw [h.eq]
  exact withDensity_absolutelyContinuous' h.measurable_density.aemeasurable
    (ae_of_all _ fun x => (ENNReal.ofReal_pos.2 (pow_pos (h.pos x) 2)).ne')

theorem absCont' (h : IsDensityRoot μ' μ σ) : μ' ≪ μ := by
  rw [h.eq]
  exact withDensity_absolutelyContinuous μ _

/-- The two measures have the same null sets. -/
theorem ae_eq (h : IsDensityRoot μ' μ σ) : ae μ' = ae μ :=
  le_antisymm h.absCont'.ae_le h.absCont.ae_le

/-- `‖f‖_{L²(μ')} = ‖σ f‖_{L²(μ)}` for every function. -/
theorem eLpNorm_eq (h : IsDensityRoot μ' μ σ) (f : α → E) :
    eLpNorm f 2 μ' = eLpNorm (fun x => σ x • f x) 2 μ := by
  rw [h.eq, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  congr 1
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable μ h.measurable_density
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  simp only [Pi.mul_apply, ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_smul]
  rw [mul_pow]
  congr 1
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem memLp_smul (h : IsDensityRoot μ' μ σ) (f : Lp E 2 μ') :
    MemLp (fun x => σ x • (f : α → E) x) 2 μ := by
  refine ⟨?_, ?_⟩
  · exact h.measurable.aestronglyMeasurable.smul
      ((Lp.aestronglyMeasurable f).mono_ac h.absCont)
  · rw [← h.eLpNorm_eq]
    exact Lp.eLpNorm_lt_top f

theorem memLp_inv_smul (h : IsDensityRoot μ' μ σ) (g : Lp E 2 μ) :
    MemLp (fun x => (σ x)⁻¹ • (g : α → E) x) 2 μ' := by
  refine ⟨?_, ?_⟩
  · exact ((h.measurable.inv).aestronglyMeasurable.smul (Lp.aestronglyMeasurable g)).mono_ac
      h.absCont'
  · rw [h.eLpNorm_eq]
    have : (fun x => σ x • ((σ x)⁻¹ • (g : α → E) x)) = fun x => (g : α → E) x := by
      funext x
      rw [smul_smul, mul_inv_cancel₀ (h.pos x).ne', one_smul]
    rw [this]
    exact Lp.eLpNorm_lt_top g

/-- Multiplication by `σ`, `L²(μ') → L²(μ)`, an isometry. -/
def rootMul (h : IsDensityRoot μ' μ σ) : Lp E 2 μ' →ₗᵢ[ℝ] Lp E 2 μ where
  toFun f := (h.memLp_smul f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(h.memLp_smul (f + g)).coeFn_toLp,
      Lp.coeFn_add ((h.memLp_smul f).toLp _) ((h.memLp_smul g).toLp _),
      (h.memLp_smul f).coeFn_toLp, (h.memLp_smul g).coeFn_toLp,
      h.absCont.ae_eq (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, smul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(h.memLp_smul (c • f)).coeFn_toLp,
      Lp.coeFn_smul c ((h.memLp_smul f).toLp _),
      (h.memLp_smul f).coeFn_toLp,
      h.absCont.ae_eq (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4, Pi.smul_apply, smul_comm]
  norm_map' f := by
    change ‖(h.memLp_smul f).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def, h.eLpNorm_eq]

theorem coeFn_rootMul (h : IsDensityRoot μ' μ σ) (f : Lp E 2 μ') :
    (h.rootMul f : α → E) =ᵐ[μ] fun x => σ x • (f : α → E) x :=
  (h.memLp_smul f).coeFn_toLp

theorem rootMul_inv (h : IsDensityRoot μ' μ σ) (g : Lp E 2 μ) :
    h.rootMul ((h.memLp_inv_smul g).toLp _) = g := by
  apply Lp.ext
  filter_upwards [h.coeFn_rootMul ((h.memLp_inv_smul g).toLp _),
    h.absCont.ae_eq (h.memLp_inv_smul g).coeFn_toLp] with x h1 h2
  rw [h1, h2, smul_smul, mul_inv_cancel₀ (h.pos x).ne', one_smul]

theorem rootMul_surjective (h : IsDensityRoot μ' μ σ) :
    Function.Surjective (h.rootMul (E := E)) :=
  fun g => ⟨_, h.rootMul_inv g⟩

/-- The linear isometric equivalence `L²(μ'; E) ≃ L²(μ; E)`, `f ↦ σ f`. -/
def rootEquiv (h : IsDensityRoot μ' μ σ) : Lp E 2 μ' ≃ₗᵢ[ℝ] Lp E 2 μ :=
  LinearIsometryEquiv.ofSurjective h.rootMul h.rootMul_surjective

theorem rootEquiv_apply (h : IsDensityRoot μ' μ σ) (f : Lp E 2 μ') :
    h.rootEquiv f = h.rootMul f := rfl

theorem coeFn_rootEquiv (h : IsDensityRoot μ' μ σ) (f : Lp E 2 μ') :
    (h.rootEquiv f : α → E) =ᵐ[μ] fun x => σ x • (f : α → E) x :=
  h.coeFn_rootMul f

theorem rootEquiv_symm_apply (h : IsDensityRoot μ' μ σ) (g : Lp E 2 μ) :
    h.rootEquiv.symm g = (h.memLp_inv_smul g).toLp _ := by
  rw [LinearIsometryEquiv.symm_apply_eq, rootEquiv_apply, h.rootMul_inv]

theorem coeFn_rootEquiv_symm (h : IsDensityRoot μ' μ σ) (g : Lp E 2 μ) :
    (h.rootEquiv.symm g : α → E) =ᵐ[μ'] fun x => (σ x)⁻¹ • (g : α → E) x := by
  rw [h.rootEquiv_symm_apply]
  exact (h.memLp_inv_smul g).coeFn_toLp

end IsDensityRoot

end Root

/-! ## `ℓ¹` products of isometries -/

section Prod

variable {A B A' B' : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup A'] [NormedSpace ℝ A']
  [NormedAddCommGroup B'] [NormedSpace ℝ B']

/-- The `ℓ¹` product `WithLp 1 (A × B) ≃ WithLp 1 (A' × B')` of two linear isometric
equivalences. -/
def prodL1Iso (e₁ : A ≃ₗᵢ[ℝ] A') (e₂ : B ≃ₗᵢ[ℝ] B') :
    WithLp 1 (A × B) ≃ₗᵢ[ℝ] WithLp 1 (A' × B') where
  toLinearEquiv := (WithLp.linearEquiv 1 ℝ (A × B)).trans
    ((e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv).trans
      (WithLp.linearEquiv 1 ℝ (A' × B')).symm)
  norm_map' x := by
    rw [WithLp.prod_norm_eq_of_L1, WithLp.prod_norm_eq_of_L1]
    change ‖e₁ x.fst‖ + ‖e₂ x.snd‖ = _
    rw [e₁.norm_map, e₂.norm_map]

@[simp] theorem prodL1Iso_fst (e₁ : A ≃ₗᵢ[ℝ] A') (e₂ : B ≃ₗᵢ[ℝ] B') (x : WithLp 1 (A × B)) :
    (prodL1Iso e₁ e₂ x).fst = e₁ x.fst := rfl

@[simp] theorem prodL1Iso_snd (e₁ : A ≃ₗᵢ[ℝ] A') (e₂ : B ≃ₗᵢ[ℝ] B') (x : WithLp 1 (A × B)) :
    (prodL1Iso e₁ e₂ x).snd = e₂ x.snd := rfl

@[simp] theorem prodL1Iso_symm_fst (e₁ : A ≃ₗᵢ[ℝ] A') (e₂ : B ≃ₗᵢ[ℝ] B')
    (x : WithLp 1 (A' × B')) : ((prodL1Iso e₁ e₂).symm x).fst = e₁.symm x.fst := rfl

@[simp] theorem prodL1Iso_symm_snd (e₁ : A ≃ₗᵢ[ℝ] A') (e₂ : B ≃ₗᵢ[ℝ] B')
    (x : WithLp 1 (A' × B')) : ((prodL1Iso e₁ e₂).symm x).snd = e₂.symm x.snd := rfl

end Prod

end UnforcedLeray.Short.PartIIIb.NearInst
