import UnforcedLeray.Lib.AxisymmetricB.Range
import UnforcedLeray.Lib.AxisymmetricB.Average

/-!
# AX04 (range and unitarity): `J_v` is unitary onto the 𝒪-invariant subspace


§5 Layer 3, target AX04 (`range_Jv`, `JvEquiv`), risk 4 of §6. Blueprint units served: B0417
(`eq:m4-free-spaces`, tex 7272–7297: "the `𝒥`'s are unitary", `J_v = (√π R)⁻¹ N_v` onto the
axisymmetric-no-swirl subspace of the period-averaged `Y₂`), B0482 (tex 7920–7949: `J_v`
unitary, azimuthal velocity vanishes), B1005 (tex 13693–13701). The group `𝒪` and the
reflection argument: tex 112–116.

* `Y2Axi P`: the closed-under-linear-operations subspace of `L²(phaseμ P; ℝ³)` of classes whose
  phase slices are, for a.e. `τ ∈ (0, P]`, axisymmetric without swirl
  (`Statement.IsAxisymmetricNoSwirl`, a.e. invariance for each `g ∈ 𝒪` separately). The
  condition does not depend on the representative (`isAxisymmetricNoSwirl_congr`).
* `Jv_mem_Y2Axi`: the inclusion `range J_v ⊆ Y2Axi P` (from `Jv_mem_axisymmetric`);
* `mem_range_Jv` (**the inclusion `⊇`**): every `U ∈ Y2Axi P` is `J_v b` for the explicit cell
  profile `b = invLift R P A`, where `A = (A_r, A_z)` are the angular averages of
  `U·e_r`, `U_z` (`Average.ae_eq_avgLift`: rotation averaging with Fubini and the reflection)
  read through the inverse ring chart
  `b(s, ξ, η) = √π R s^{-1/2} A(τ̂, R/√s, η/√s)`, `τ̂ ≡ (2/R) ξ + log s (mod P)`;
  `b ∈ L²(ageμ c (−3/2))` because `J_v` is an isometry on measurable profiles
  (`eLpNorm_liftFun`);
* `range_Jv : LinearMap.range J_v = Y2Axi P`;
* `JvEquiv : L²(ageμ c (−3/2); ℝ²) ≃ₗᵢ[ℝ] Y2Axi P`, the unitary of tex 7280–7283.

The phase space here is the joint `L²(phaseμ P; ℝ³)` of `Jv.lean` (period average on `(0, P]`
times Lebesgue measure); its identification with the Bochner `Y₂ = L²(ℝ/Pℤ; L²(ℝ³; ℂ³))` of
decision D2 is the separate bridge recorded as missing in the main file.

Junk values: `invLift` divides by `√s`; at `s ≤ 0` (a null set of `ageμ`, `ae_ageμ_mem`) Lean's
`√s = 0` and `0⁻¹ = 0` give the value `0`. The representative `perRep P` lands in `(0, P]`
only for `P > 0`, which `hP : P = 2c/R` with `c, R > 0` guarantees.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter
open scoped ENNReal

namespace UnforcedLeray.Axi

/-! ### The 𝒪-invariance condition: a.e. congruence and linear operations -/

/-- `IsAxisymmetricNoSwirl` only depends on the a.e. class of the field. -/
theorem isAxisymmetricNoSwirl_congr {f f' : Space → Space} (hf : IsAxisymmetricNoSwirl f)
    (h : f' =ᵐ[volume] f) : IsAxisymmetricNoSwirl f' := by
  intro g hg
  have h1 := g.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [h1, hf g hg, h] with x h1 h2 h3
  simp only [Function.comp_apply] at h1
  show g (f' (g.symm x)) = f' x
  rw [h1, h3]
  exact h2

theorem isAxisymmetricNoSwirl_zero : IsAxisymmetricNoSwirl (0 : Space → Space) := fun g _ =>
  ae_of_all _ fun x => by simp

theorem IsAxisymmetricNoSwirl.add {f h : Space → Space} (hf : IsAxisymmetricNoSwirl f)
    (hh : IsAxisymmetricNoSwirl h) : IsAxisymmetricNoSwirl (f + h) := by
  intro g hg
  filter_upwards [hf g hg, hh g hg] with x h1 h2
  simp only [Pi.add_apply, map_add]
  exact congrArg₂ (· + ·) h1 h2

theorem IsAxisymmetricNoSwirl.const_smul {f : Space → Space} (hf : IsAxisymmetricNoSwirl f)
    (k : ℝ) : IsAxisymmetricNoSwirl (k • f) := by
  intro g hg
  filter_upwards [hf g hg] with x h1
  simp only [Pi.smul_apply, map_smul]
  exact congrArg (k • ·) h1

/-- An a.e. statement for `phaseμ P` holds on a.e. phase slice. -/
theorem ae_slice {P : ℝ} {p : ℝ × Space → Prop} (h : ∀ᵐ x ∂phaseμ P, p x) :
    ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)), ∀ᵐ y, p (τ, y) := by
  unfold phaseμ at h
  exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)).1
    (Measure.ae_ae_of_ae_prod h)

/-! ### The invariant subspace -/

/-- **The 𝒪-invariant subspace** of the period-averaged phase space `L²(phaseμ P; ℝ³)`: classes
whose phase slices are axisymmetric without swirl for a.e. `τ ∈ (0, P]` (tex 7280–7283,
B0417). -/
def Y2Axi (P : ℝ) : Submodule ℝ (Lp Space 2 (phaseμ P)) where
  carrier := {U | ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)),
    IsAxisymmetricNoSwirl fun y => U (τ, y)}
  add_mem' {U V} hU hV := by
    simp only [Set.mem_ofPred_eq] at hU hV ⊢
    filter_upwards [ae_slice (Lp.coeFn_add U V), hU, hV] with τ h1 h2 h3
    exact isAxisymmetricNoSwirl_congr (IsAxisymmetricNoSwirl.add h2 h3) h1
  zero_mem' := by
    filter_upwards [ae_slice (Lp.coeFn_zero (E := Space) (p := 2) (μ := phaseμ P))] with τ h1
    exact isAxisymmetricNoSwirl_congr isAxisymmetricNoSwirl_zero h1
  smul_mem' k U hU := by
    simp only [Set.mem_ofPred_eq] at hU ⊢
    filter_upwards [ae_slice (Lp.coeFn_smul k U), hU] with τ h1 h2
    exact isAxisymmetricNoSwirl_congr (IsAxisymmetricNoSwirl.const_smul h2 k) h1

theorem mem_Y2Axi {P : ℝ} (U : Lp Space 2 (phaseμ P)) :
    U ∈ Y2Axi P ↔ ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)),
      IsAxisymmetricNoSwirl fun y => U (τ, y) := Iff.rfl

/-- **AX04, inclusion `range J_v ⊆ Y2Axi P`** (B0417, B0482, B1005). -/
theorem Jv_mem_Y2Axi {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (b : Lp Merid 2 (ageμ c (-3 / 2))) : Jv hR hc hP b ∈ Y2Axi P := by
  obtain ⟨U, hU, hsym, -⟩ := Jv_mem_axisymmetric hR hc hP b
  filter_upwards [ae_slice hU] with τ hτ
  exact isAxisymmetricNoSwirl_congr (hsym τ) hτ

/-! ### The inverse ring chart -/

/-- The representative in `(0, P]` of `t` modulo `P`. -/
def perRep (P t : ℝ) : ℝ := t - P * (⌈t / P⌉ - 1)

theorem measurable_perRep (P : ℝ) : Measurable (perRep P) := by
  have h : Measurable fun t : ℝ => ((⌈t / P⌉ : ℤ) : ℝ) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
      (Int.measurable_ceil.comp (measurable_id.div_const _))
  unfold perRep
  exact measurable_id.sub (measurable_const.mul (h.sub measurable_const))

theorem perRep_sub_mul {P τ : ℝ} (hP : 0 < P) (hτ : τ ∈ Ioc 0 P) (k : ℤ) :
    perRep P (τ - k * P) = τ := by
  unfold perRep
  have h1 : ⌈τ / P⌉ = 1 := by
    rw [Int.ceil_eq_iff]
    constructor
    · norm_num
      exact div_pos hτ.1 hP
    · norm_num
      exact (div_le_one hP).2 hτ.2
  have h2 : (τ - k * P) / P = τ / P - k := by
    field_simp
  rw [h2, Int.ceil_sub_intCast, h1]
  push_cast
  ring

/-- **The inverse ring chart.** For a meridional field `A(τ, ρ, z)` (values `(A_r, A_z)`),
the cell profile `b(s, ξ, η) = √π R s^{-1/2} A(τ̂, R/√s, η/√s)` with
`τ̂ = perRep P ((2/R) ξ + log s)`; at a chart point `(s, ξ, η) = chart R τ y` one has
`τ̂ ≡ τ`, `R/√s = ϱ`, `η/√s = y₃` (tex 2994–3003, B0197). -/
def invLift (R P : ℝ) (A : ℝ × (ℝ × ℝ) → Merid) (p : ℝ × (ℝ × ℝ)) : Merid :=
  (√π * R * (√p.1)⁻¹) • A (perRep P (2 / R * p.2.1 + Real.log p.1), (R / √p.1, p.2.2 / √p.1))

theorem measurable_invLift (R P : ℝ) {A : ℝ × (ℝ × ℝ) → Merid} (hA : Measurable A) :
    Measurable (invLift R P A) := by
  have hper := measurable_perRep P
  unfold invLift
  fun_prop

/-- The ring lift of the inverse-chart profile is the frame lift of `A` (one period). -/
theorem liftFun_invLift {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (A : ℝ × (ℝ × ℝ) → Merid) {τ : ℝ} (hτ : τ ∈ Ioc 0 P) {y : Space} (hy : y ∉ axis) :
    liftFun R c (invLift R P A) (τ, y) = frameL y (A (τ, mer y)) := by
  have hPpos : 0 < P := hP ▸ div_pos (by positivity) hR
  have hρ := ϱ_pos hy
  have hπ : 0 < √π := Real.sqrt_pos.2 pi_pos
  have hs : √(age R y) = R / ϱ y := sqrt_age hR hy
  have hξ : 2 / R * cellRep c (phase R τ y) + Real.log (age R y) =
      τ - (⌊(phase R τ y + c / 2) / c⌋ : ℤ) * P := by
    rw [cellRep, phase, hP]
    field_simp
    ring
  have hr : R / √(age R y) = ϱ y := by
    rw [hs]
    field_simp
  have hz : trans R y / √(age R y) = y 2 := by
    rw [hs, trans]
    field_simp
  simp only [liftFun, Nv, perExt, chart, invLift]
  rw [hξ, perRep_sub_mul hPpos hτ, hr, hz, map_smul, smul_smul, smul_smul, hs]
  have hconst : (√π * R)⁻¹ * (R / ϱ y) * (√π * R * (R / ϱ y)⁻¹) = 1 := by
    field_simp
  rw [hconst, one_smul]
  rfl

theorem measurable_merVec {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => (!₂[f a, g a] : Merid) := by
  have hcont : Continuous fun q : ℝ × ℝ => (!₂[q.1, q.2] : Merid) := by fun_prop
  have h : (fun a => (!₂[f a, g a] : Merid)) =
      (fun q : ℝ × ℝ => (!₂[q.1, q.2] : Merid)) ∘ fun a => (f a, g a) := rfl
  rw [h]
  exact hcont.measurable.comp (hf.prodMk hg)

/-- The averaged meridional field `(A_r, A_z)` of a phase-space field. -/
def avgMer (W : ℝ × Space → Space) (p : ℝ × (ℝ × ℝ)) : Merid := !₂[avgR W p, avgZ W p]

theorem measurable_avgMer {W : ℝ × Space → Space} (hW : Measurable W) :
    Measurable (avgMer W) :=
  measurable_merVec (measurable_avgR hW) (measurable_avgZ hW)

/-! ### The inclusion `⊇` and unitarity -/

/-- **AX04 `range_Jv`, inclusion `⊇`** (B0417, tex 7280–7283; B0482, tex 7920–7949;
risk 4 of the scoping note). Every element of the period-averaged phase space whose phase
slices are axisymmetric without swirl for a.e. `τ` is a ring lift `J_v b`, with the explicit
profile `b = invLift R P (avgMer U)` (rotation averaging, Fubini, the reflection). -/
theorem mem_range_Jv {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (U : Lp Space 2 (phaseμ P)) (hU : U ∈ Y2Axi P) : ∃ b, Jv hR hc hP b = U := by
  have hW : Measurable (U : ℝ × Space → Space) := (Lp.stronglyMeasurable U).measurable
  have hsym : ∀ᵐ τ ∂((ENNReal.ofReal P)⁻¹ • volume.restrict (Ioc (0 : ℝ) P)),
      IsAxisymmetricNoSwirl fun y => U (τ, y) := Measure.ae_smul_measure hU _
  have hrep : (U : ℝ × Space → Space) =ᵐ[phaseμ P] fun x =>
      avgR (⇑U) (x.1, mer x.2) • eR x.2 + avgZ (⇑U) (x.1, mer x.2) • e3 :=
    ae_eq_avgLift hW hsym
  have hbm : Measurable (invLift R P (avgMer U)) :=
    measurable_invLift R P (measurable_avgMer hW)
  have hτ : ∀ᵐ x ∂phaseμ P, x.1 ∈ Ioc 0 P :=
    Measure.quasiMeasurePreserving_fst.ae
      (Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioc) _)
  have hy : ∀ᵐ x ∂phaseμ P, x.2 ∉ axis :=
    Measure.quasiMeasurePreserving_snd.ae ae_not_mem_axis
  have hlift : liftFun R c (invLift R P (avgMer U)) =ᵐ[phaseμ P] U := by
    filter_upwards [hrep, hτ, hy] with x h1 h2 h3
    obtain ⟨τ, y⟩ := x
    rw [h1, liftFun_invLift hR hc hP _ h2 h3, frameL_apply]
    rfl
  have hmem : MemLp (invLift R P (avgMer U)) 2 (ageμ c (-3 / 2)) :=
    ⟨hbm.aestronglyMeasurable, by
      rw [← eLpNorm_liftFun hR hc hP hbm, eLpNorm_congr_ae hlift]
      exact Lp.eLpNorm_lt_top U⟩
  refine ⟨hmem.toLp _, Lp.ext ?_⟩
  filter_upwards [coeFn_Jv hR hc hP (hmem.toLp _), liftFun_congr_ae hR hc hP
    (Lp.stronglyMeasurable _).measurable hbm hmem.coeFn_toLp, hlift] with x h1 h2 h3
  exact h1.trans (h2.trans h3)

/-- **AX04 `range_Jv`** (B0417, tex 7280–7283): the range of the ring lift is exactly the
𝒪-invariant subspace of the period-averaged phase space. -/
theorem range_Jv {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R) :
    LinearMap.range (Jv hR hc hP).toLinearMap = Y2Axi P := by
  ext U
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨b, rfl⟩
    exact Jv_mem_Y2Axi hR hc hP b
  · intro hU
    exact mem_range_Jv hR hc hP U hU

/-- `J_v` with codomain the invariant subspace. -/
def JvAxi {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R) :
    Lp Merid 2 (ageμ c (-3 / 2)) →ₗᵢ[ℝ] Y2Axi P where
  toLinearMap := (Jv hR hc hP).toLinearMap.codRestrict (Y2Axi P) (Jv_mem_Y2Axi hR hc hP)
  norm_map' b := (Jv hR hc hP).norm_map b

/-- **AX04 `JvEquiv`** (B0417, tex 7280–7283: "the `𝒥`'s are unitary"; B0482). The ring lift
`J_v = (√π R)⁻¹ N_v` is a unitary from `H = L²(ageμ c (−3/2); ℝ²)` onto the 𝒪-invariant
subspace `Y2Axi P` of the period-averaged `L²(phaseμ P; ℝ³)`, `P = 2c/R`. -/
def JvEquiv {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R) :
    Lp Merid 2 (ageμ c (-3 / 2)) ≃ₗᵢ[ℝ] Y2Axi P :=
  LinearIsometryEquiv.ofSurjective (JvAxi hR hc hP) (by
    rintro ⟨U, hU⟩
    obtain ⟨b, hb⟩ := mem_range_Jv hR hc hP U hU
    exact ⟨b, Subtype.ext hb⟩)

theorem coe_JvEquiv {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (b : Lp Merid 2 (ageμ c (-3 / 2))) :
    ((JvEquiv hR hc hP b : Y2Axi P) : Lp Space 2 (phaseμ P)) = Jv hR hc hP b := rfl

end UnforcedLeray.Axi
