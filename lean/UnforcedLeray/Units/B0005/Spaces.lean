import UnforcedLeray.Lib.PhaseSpace
import UnforcedLeray.Lib.BochnerTime.Slices

/-!
# B0005, part 2: the periodic spaces `𝒴_q`, `𝒴_{q,div}`, the operator `𝒯₀` and the graph `𝒱_q`

Blueprint unit B0005 (`unlabeled:136`), `paper/main.tex` lines 136–147:

  `𝒴_q = L^q([0,𝒯], dτ/𝒯; L^q)`, `𝒯₀ = ∂_τ - ½ y·∇`,
  `𝒱_q = {f ∈ 𝒴_{q,div} : hΔf, 𝒯₀f ∈ 𝒴_q}`;

"The periodic spaces identify their endpoints; the graph norm is the sum of the three
indicated norms. No separate phase derivative or dilation derivative is imposed."


`𝒴_q` is `PhaseSpace.Yq 𝒯 q = L^q(ℝ/𝒯ℤ; L^q(ℝ³; ℂ³))` with the normalised Haar measure of
the phase circle. Identifying the endpoints of `[0, 𝒯]` is the passage to the circle
`AddCircle 𝒯`; the measure `dτ/𝒯` is the Haar probability measure
(`measurePreserving_phase`), so `‖f‖^q = 𝒯⁻¹ ∫₀^𝒯 ‖f(τ)‖_q^q dτ` (`norm_rpow_eq`). The
scalars are complex, as in the spectral part of the manuscript (tex 7314); real fields are
the elements with real representatives (see `Bridge.lean`).

"In distributions" means testing against smooth `𝒯`-periodic fields of bounded support
(`PhaseSpace.IsPhaseTest`, scoping bypass B25-1). The operators enter only through their
transposes on tests: `Δᵗ = Δ`, `𝒯₀ᵗ = -∂_τ + ½ y·∇ + 3/2` (`PhaseSpace.driftT`;
`driftT_eq_neg_T0op` checks it against the forward operator `T0op`). The graph
`𝒱_q` is `PhaseSpace.solenoidalFreeGraph 𝒯 h q`: the triples `(f, hΔf, 𝒯₀f) ∈ 𝒴_q³` with
`div f = 0`, `hΔf = a`, `𝒯₀f = b` in distributions. Only the combination `𝒯₀ f` is
required in `𝒴_q`; there is no clause on `∂_τ f` or `y·∇f` separately (`mem_V_iff`). That the
triple is determined by `f` is `Unique.lean`; the space of `f` with the graph norm
`‖f‖ + ‖hΔf‖ + ‖𝒯₀f‖` is `Vq` there.

Status: definitions and their elementary facts. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0005

open UnforcedLeray.PhaseSpace

section Spaces

variable (𝒯 : ℝ) [hT : Fact (0 < 𝒯)] (q : ℝ≥0∞) [Fact (1 ≤ q)]

/-- **`𝒴_q = L^q([0,𝒯], dτ/𝒯; L^q)`** with endpoints identified (tex 138–139): the Bochner
space `L^q(ℝ/𝒯ℤ; L^q(ℝ³; ℂ³))` for the Haar probability measure (decision D2). -/
abbrev Y : Type := Yq 𝒯 q

/-- The phase of `τ ∈ ℝ` on the circle `ℝ/𝒯ℤ`: the endpoints `0` and `𝒯` are identified. -/
def phase (τ : ℝ) : AddCircle 𝒯 := τ

omit hT in
theorem phase_add_period (τ : ℝ) : phase 𝒯 (τ + 𝒯) = phase 𝒯 τ := by
  simp [phase]

omit hT in
theorem phase_zero_eq_phase_period : phase 𝒯 0 = phase 𝒯 𝒯 := by
  simpa using (phase_add_period 𝒯 0).symm

/-- The measure `dτ/𝒯` on one period is carried to the Haar probability measure of the circle
(tex 138: `L^q([0,𝒯], dτ/𝒯; ·)`). -/
theorem measurePreserving_phase :
    MeasurePreserving (phase 𝒯) ((ENNReal.ofReal 𝒯)⁻¹ • volume.restrict (Ioc (0 : ℝ) 𝒯))
      (AddCircle.haarAddCircle (T := 𝒯)) := by
  have h := (AddCircle.measurePreserving_mk 𝒯 0).smul_measure (ENNReal.ofReal 𝒯)⁻¹
  rw [zero_add, AddCircle.volume_eq_smul_haarAddCircle, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hT.out).ne' ENNReal.ofReal_ne_top,
    one_smul] at h
  exact h

/-- Lower integrals over the circle are period averages: `∫ g dhaar = 𝒯⁻¹ ∫₀^𝒯 g(τ) dτ`. -/
theorem lintegral_haar_eq (g : AddCircle 𝒯 → ℝ≥0∞) :
    ∫⁻ τ, g τ ∂AddCircle.haarAddCircle =
      (ENNReal.ofReal 𝒯)⁻¹ * ∫⁻ t in Ioc (0 : ℝ) 𝒯, g (phase 𝒯 t) := by
  have hv : (AddCircle.haarAddCircle (T := 𝒯)) =
      (ENNReal.ofReal 𝒯)⁻¹ • (volume : Measure (AddCircle 𝒯)) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, smul_smul,
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hT.out).ne' ENNReal.ofReal_ne_top,
      one_smul]
  rw [hv, lintegral_smul_measure, ← AddCircle.lintegral_preimage 𝒯 0, zero_add]
  rfl

variable {𝒯 q}

/-- **The norm of `𝒴_q`** (tex 138, `q < ∞`): `‖f‖^q = 𝒯⁻¹ ∫₀^𝒯 ‖f(τ)‖_{L^q}^q dτ`, in
extended reals. -/
theorem eLpNorm_rpow_eq (hq : q ≠ ⊤) (f : Y 𝒯 q) :
    eLpNorm f q AddCircle.haarAddCircle ^ q.toReal =
      (ENNReal.ofReal 𝒯)⁻¹ * ∫⁻ t in Ioc (0 : ℝ) 𝒯, ‖f (phase 𝒯 t)‖ₑ ^ q.toReal := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'
  rw [BochnerTime.eLpNorm_rpow_eq_lintegral hq0 hq, lintegral_haar_eq]

/-- **The norm of `𝒴_q`** (tex 138, `q < ∞`): `‖f‖^q = 𝒯⁻¹ ∫₀^𝒯 ‖f(τ)‖_{L^q}^q dτ`. -/
theorem norm_rpow_eq (hq : q ≠ ⊤) (f : Y 𝒯 q) :
    ‖f‖ ^ q.toReal = 𝒯⁻¹ * ∫ t in Ioc (0 : ℝ) 𝒯, ‖f (phase 𝒯 t)‖ ^ q.toReal := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'
  have hqr : 0 ≤ q.toReal := ENNReal.toReal_nonneg
  rw [Lp.norm_def, ENNReal.toReal_rpow, eLpNorm_rpow_eq hq f, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hT.out.le]
  congr 1
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => by positivity)]
  · congr 1
    refine lintegral_congr fun t => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hqr]
  · have hm : AEStronglyMeasurable (fun τ : AddCircle 𝒯 => ‖f τ‖ ^ q.toReal)
        (AddCircle.haarAddCircle (T := 𝒯)) :=
      ((Lp.aestronglyMeasurable f).norm.aemeasurable.pow_const _).aestronglyMeasurable
    have hm2 := hm.comp_measurePreserving (measurePreserving_phase 𝒯)
    exact (hm2.mono_ac (Measure.absolutelyContinuous_smul (by
      simp)))

end Spaces

/-! ### `𝒴_{q,div}` -/

section Div

variable (𝒯 : ℝ) [Fact (0 < 𝒯)] (q : ℝ≥0∞) [Fact (1 ≤ q)]

/-- **`𝒴_{q,div}`** (tex 141): the closed subspace of `f ∈ 𝒴_q` with `div f = 0` in
distributions. -/
def Ydiv : Submodule ℂ (Y 𝒯 q) where
  carrier := {f | IsPhaseSolenoidal f}
  add_mem' := fun ha hb => ha.add hb
  zero_mem' := fun φ _ => by simp
  smul_mem' := fun c _ hx => hx.smul c

theorem mem_Ydiv {f : Y 𝒯 q} : f ∈ Ydiv 𝒯 q ↔ IsPhaseSolenoidal f := Iff.rfl

theorem isClosed_Ydiv : IsClosed (Ydiv 𝒯 q : Set (Y 𝒯 q)) := isClosed_isPhaseSolenoidal

instance : CompleteSpace (Ydiv 𝒯 q) := (isClosed_Ydiv 𝒯 q).completeSpace_coe

end Div

/-! ### The operator `𝒯₀ = ∂_τ - ½ y·∇` -/

section T0

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **`𝒯₀ = ∂_τ - ½ y·∇`** (tex 140) on smooth functions of `(τ, y)`. -/
def T0op (Φ : ℝ × Space → F) : ℝ × Space → F :=
  fun p => dτ Φ p - (1 / 2 : ℝ) • radialT Φ p

/-- The transpose used for `𝒯₀` in distributions is `𝒯₀ᵗ = -𝒯₀ + 3/2` (`div y = 3`). -/
theorem driftT_eq_neg_T0op (Φ : ℝ × Space → F) :
    driftT Φ = fun p => -T0op Φ p + (3 / 2 : ℝ) • Φ p := by
  funext p
  simp only [driftT, T0op]
  abel

theorem IsPhaseTest.T0op {P : ℝ} {Φ : ℝ × Space → F} (hΦ : IsPhaseTest P Φ) :
    IsPhaseTest P (B0005.T0op Φ) := by
  have h : B0005.T0op Φ = PhaseSpace.dτ Φ + (-(1 / 2 : ℝ)) • PhaseSpace.radialT Φ := by
    funext p
    simp [B0005.T0op, sub_eq_add_neg]
  rw [h]
  exact hΦ.dτ.add (hΦ.radialT.const_smul _)

end T0

/-! ### Distributional `hΔf` and `𝒯₀f`, and the graph `𝒱_q` -/

section Graph

variable {𝒯 : ℝ} [Fact (0 < 𝒯)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- `hΔf = a` in distributions: `⟪hΔΦ, f⟫ = ⟪Φ, a⟫` for every phase test `Φ`. -/
abbrev HasHLap (h : ℝ) (f a : Y 𝒯 q) : Prop := HasPhaseOp (nuLapT h) f a

/-- `𝒯₀f = b` in distributions: `⟪𝒯₀ᵗΦ, f⟫ = ⟪Φ, b⟫` for every phase test `Φ`. -/
abbrev HasT0 (f b : Y 𝒯 q) : Prop := HasPhaseOp driftT f b

variable (𝒯 q) in
/-- **`𝒱_q`** (tex 141–145), as the graph: triples `(f, hΔf, 𝒯₀f) ∈ 𝒴_q³` with
`f ∈ 𝒴_{q,div}`, `hΔf ∈ 𝒴_q` and `𝒯₀f ∈ 𝒴_q` in distributions. -/
abbrev V (h : ℝ) : Submodule ℂ (Y 𝒯 q × Y 𝒯 q × Y 𝒯 q) := solenoidalFreeGraph 𝒯 h q

/-- Membership in `𝒱_q` is exactly the three conditions of tex 141–142; no clause on `∂_τ f`
or `y·∇ f` separately (tex 145–147). -/
theorem mem_V_iff {h : ℝ} {f a b : Y 𝒯 q} :
    (f, a, b) ∈ V 𝒯 q h ↔ f ∈ Ydiv 𝒯 q ∧ HasHLap h f a ∧ HasT0 f b := by
  show ((f, a, b) ∈ freeGraph 𝒯 h q ∧ IsPhaseSolenoidal f) ↔ _
  rw [mem_freeGraph]
  tauto

theorem isClosed_V (h : ℝ) : IsClosed (V 𝒯 q h : Set (Y 𝒯 q × Y 𝒯 q × Y 𝒯 q)) :=
  isClosed_solenoidalFreeGraph h

/-- `𝒱_q` with its graph norm is a Banach space. -/
instance (h : ℝ) : CompleteSpace (V 𝒯 q h) := solenoidalFreeGraph_completeSpace h

/-- The graph norm `‖f‖ + ‖hΔf‖ + ‖𝒯₀f‖` of tex 144 is equivalent to the norm of `𝒴_q³`. -/
theorem graphNorm_equiv (x : Y 𝒯 q × Y 𝒯 q × Y 𝒯 q) :
    ‖x‖ ≤ graphNorm x ∧ graphNorm x ≤ 3 * ‖x‖ :=
  ⟨norm_le_graphNorm x, graphNorm_le x⟩

end Graph

end UnforcedLeray.B0005
