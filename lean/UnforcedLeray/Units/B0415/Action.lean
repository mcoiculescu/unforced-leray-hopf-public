import UnforcedLeray.Lib.LerayC.IsometryC
import UnforcedLeray.Lib.AxisymmetricB.Average

/-!
# Unit B0415, helper: the action `(g·w)(τ, x) = g w(τ, g⁻¹x)` of `O(3)` on `Y_q`

Blueprint unit `B0415` (`eq:free-stress-2`, `paper/main.tex` lines 7346–7362). The manuscript
lets the group `𝒪` of linear isometries fixing `e₃` act on fields by pushforward,
`(g·f)(x) = g f(g⁻¹x)` (tex 112–115, `Statement.IsAxisymmetricNoSwirl`), on complex fields
componentwise, and on `Y_q` slice by slice in the phase `τ`.

* `actV g : ℂ³ →L[ℂ] ℂ³`, `z ↦ g(Re z) + i g(Im z)`: the complex-linear form of
  `RieszLp.complexifyIso g` (`Lib/LerayC/IsometryC.lean`), `actV_trans`, `actV_refl`;
* `actLp q g` on `L^q(ℝ³;ℂ³)`, `coeFn_actLp`, `actLp_restrictScalars` (it is
  `RieszLp.rotLpC q g`), the group law `actLp_trans`, `actLp_refl`;
* `actY P q g` on `Y_q = L^q(ℝ/Pℤ; L^q(ℝ³;ℂ³))`, `coeFn_actY`, `actY_restrictScalars`,
  `actY_trans`, `actY_refl`, `actY_eq_self_iff` (a fixed point of `actY g` is a field whose
  phase slices are fixed for a.e. `τ`);
* `IsAxiNoSwirlC f`: a complex field is axisymmetric without swirl when its real and imaginary
  parts are (`Statement.IsAxisymmetricNoSwirl`); `isAxiNoSwirlC_iff_actLp`: for `F ∈ L^q` this
  holds iff `actLp q g F = F` for every `g ∈ 𝒪`.

No statement depends on a Lean junk value: all objects are `Lp` classes and a.e. identities.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.B0415

open UnforcedLeray.PhaseSpace (CVec3 Yq)
open UnforcedLeray.RieszLp (complexifyIso reV imV ofReV ofImV complexifyIso_apply
  reV_complexifyIso imV_complexifyIso)

/-! ### The complexified action on `ℂ³` -/

theorem complexifyIso_I_smul (g : Space ≃ₗᵢ[ℝ] Space) (z : CVec3) :
    complexifyIso g (Complex.I • z) = Complex.I • complexifyIso g z := by
  rw [complexifyIso_apply, complexifyIso_apply, RieszLp.reV_I_smul, RieszLp.imV_I_smul,
    map_neg, map_neg, smul_add, RieszLp.I_smul_ofReV, RieszLp.I_smul_ofImV]
  abel

theorem complex_smul_eq (c : ℂ) (z : CVec3) : c • z = c.re • z + c.im • (Complex.I • z) := by
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Complex.real_smul]
  conv_lhs => rw [← Complex.re_add_im c]
  ring

theorem complexifyIso_smul (g : Space ≃ₗᵢ[ℝ] Space) (c : ℂ) (z : CVec3) :
    complexifyIso g (c • z) = c • complexifyIso g z := by
  rw [complex_smul_eq c z, map_add, map_smul, map_smul, complexifyIso_I_smul,
    ← complex_smul_eq]

/-- The action of a linear isometry `g` of `ℝ³` on `ℂ³`, `z ↦ g(Re z) + i g(Im z)`, as a
complex-linear map (it is `RieszLp.complexifyIso g`, `actV_restrictScalars`). -/
def actV (g : Space ≃ₗᵢ[ℝ] Space) : CVec3 →L[ℂ] CVec3 where
  toFun := complexifyIso g
  map_add' := (complexifyIso g).map_add
  map_smul' := complexifyIso_smul g
  cont := (complexifyIso g).continuous

@[simp] theorem actV_apply (g : Space ≃ₗᵢ[ℝ] Space) (z : CVec3) :
    actV g z = complexifyIso g z := rfl

theorem actV_restrictScalars (g : Space ≃ₗᵢ[ℝ] Space) :
    (actV g).restrictScalars ℝ = complexifyIso g := by
  ext1 z
  rfl

@[simp] theorem reV_actV (g : Space ≃ₗᵢ[ℝ] Space) (z : CVec3) : reV (actV g z) = g (reV z) :=
  reV_complexifyIso g z

@[simp] theorem imV_actV (g : Space ≃ₗᵢ[ℝ] Space) (z : CVec3) : imV (actV g z) = g (imV z) :=
  imV_complexifyIso g z

/-- Two vectors of `ℂ³` with the same real and imaginary parts are equal. -/
theorem cvec_ext {z w : CVec3} (h1 : reV z = reV w) (h2 : imV z = imV w) : z = w := by
  rw [← RieszLp.ofReV_reV_add_ofImV_imV z, ← RieszLp.ofReV_reV_add_ofImV_imV w, h1, h2]

/-- The group law on `ℂ³`: `(h ∘ g)·z = h·(g·z)`. -/
theorem actV_trans (g h : Space ≃ₗᵢ[ℝ] Space) (z : CVec3) :
    actV (g.trans h) z = actV h (actV g z) := by
  apply cvec_ext <;> simp [LinearIsometryEquiv.trans_apply]

theorem actV_refl (z : CVec3) : actV (LinearIsometryEquiv.refl ℝ Space) z = z := by
  apply cvec_ext <;> simp

/-! ### The action on `L^q(ℝ³;ℂ³)` -/

section LpAct

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

variable (q) in
/-- The action `F ↦ g F(g⁻¹ ·)` of a linear isometry `g` of `ℝ³` on `L^q(ℝ³;ℂ³)`, complex-linear
(tex 112–115). -/
def actLp (g : Space ≃ₗᵢ[ℝ] Space) :
    Lp CVec3 q (volume : Measure Space) →L[ℂ] Lp CVec3 q (volume : Measure Space) :=
  ((actV g).compLpL q volume).comp
    (Lp.compMeasurePreservingₗᵢ ℂ (g.symm : Space → Space)
      g.symm.measurePreserving).toContinuousLinearMap

theorem coeFn_actLp (g : Space ≃ₗᵢ[ℝ] Space) (F : Lp CVec3 q (volume : Measure Space)) :
    (actLp q g F : Space → CVec3) =ᵐ[volume] fun x => actV g (F (g.symm x)) := by
  have h1 := ContinuousLinearMap.coeFn_compLpL (μ := volume) (p := q) (actV g)
    (Lp.compMeasurePreserving (g.symm : Space → Space) g.symm.measurePreserving F)
  have h2 := Lp.coeFn_compMeasurePreserving F g.symm.measurePreserving
  refine h1.trans ?_
  filter_upwards [h2] with x hx
  simp only [hx, Function.comp_apply]

/-- The real restriction of `actLp q g` is the action `RieszLp.rotLpC q g` of
`Lib/LerayC/IsometryC.lean`. -/
theorem actLp_restrictScalars (g : Space ≃ₗᵢ[ℝ] Space) :
    (actLp q g).restrictScalars ℝ = RieszLp.rotLpC q g := by
  ext1 F
  apply Lp.ext
  filter_upwards [coeFn_actLp g F, RieszLp.coeFn_rotLpC g F] with x h1 h2
  rw [ContinuousLinearMap.coe_restrictScalars', h1, h2]
  rfl

theorem actLp_eq_rotLpC (g : Space ≃ₗᵢ[ℝ] Space) (F : Lp CVec3 q (volume : Measure Space)) :
    actLp q g F = RieszLp.rotLpC q g F := by
  rw [← actLp_restrictScalars]
  rfl

/-- The group law on `L^q`: `(h ∘ g)·F = h·(g·F)`. -/
theorem actLp_trans (g h : Space ≃ₗᵢ[ℝ] Space) (F : Lp CVec3 q (volume : Measure Space)) :
    actLp q (g.trans h) F = actLp q h (actLp q g F) := by
  apply Lp.ext
  have h1 := coeFn_actLp (g.trans h) F
  have h2 := coeFn_actLp h (actLp q g F)
  have h3 := h.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp (coeFn_actLp g F)
  filter_upwards [h1, h2, h3] with x e1 e2 e3
  simp only [Function.comp_apply] at e3
  rw [e1, e2, e3, actV_trans]
  rfl

theorem actLp_refl (F : Lp CVec3 q (volume : Measure Space)) :
    actLp q (LinearIsometryEquiv.refl ℝ Space) F = F := by
  apply Lp.ext
  filter_upwards [coeFn_actLp (LinearIsometryEquiv.refl ℝ Space) F] with x hx
  rw [hx, actV_refl]
  rfl

theorem actLp_eq_self_iff (g : Space ≃ₗᵢ[ℝ] Space) (F : Lp CVec3 q (volume : Measure Space)) :
    actLp q g F = F ↔ (fun x => actV g (F (g.symm x))) =ᵐ[volume] F := by
  constructor
  · intro h
    have h1 := coeFn_actLp g F
    rw [h] at h1
    exact h1.symm
  · intro h
    exact Lp.ext ((coeFn_actLp g F).trans h)

/-! ### Complex fields axisymmetric without swirl -/

/-- A complex field is **axisymmetric without swirl** when its real and imaginary parts are
(`Statement.IsAxisymmetricNoSwirl`: `g f(g⁻¹·) = f` a.e. for every `g ∈ 𝒪`; tex 112–115). -/
def IsAxiNoSwirlC (f : Space → CVec3) : Prop :=
  IsAxisymmetricNoSwirl (fun y => reV (f y)) ∧ IsAxisymmetricNoSwirl (fun y => imV (f y))

/-- `IsAxiNoSwirlC` is the invariance `actV g ∘ f ∘ g⁻¹ = f` a.e., for every `g ∈ 𝒪`. -/
theorem isAxiNoSwirlC_iff (f : Space → CVec3) :
    IsAxiNoSwirlC f ↔ ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g →
      (fun x => actV g (f (g.symm x))) =ᵐ[volume] f := by
  constructor
  · rintro ⟨hr, hi⟩ g hg
    filter_upwards [hr g hg, hi g hg] with x h1 h2
    exact cvec_ext (by rw [reV_actV]; exact h1) (by rw [imV_actV]; exact h2)
  · intro h
    refine ⟨fun g hg => ?_, fun g hg => ?_⟩
    · filter_upwards [h g hg] with x hx
      have := congrArg reV hx
      rw [reV_actV] at this
      exact this
    · filter_upwards [h g hg] with x hx
      have := congrArg imV hx
      rw [imV_actV] at this
      exact this

/-- For `F ∈ L^q(ℝ³;ℂ³)`: `F` is axisymmetric without swirl iff `g·F = F` for every `g ∈ 𝒪`. -/
theorem isAxiNoSwirlC_iff_actLp (F : Lp CVec3 q (volume : Measure Space)) :
    IsAxiNoSwirlC (F : Space → CVec3) ↔
      ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g → actLp q g F = F := by
  rw [isAxiNoSwirlC_iff]
  exact forall₂_congr fun g _ => (actLp_eq_self_iff g F).symm

end LpAct

/-! ### The action on `Y_q` -/

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

variable (P q) in
/-- **The action of `g` on `Y_q`** (tex 7348–7351), slice by slice in the phase:
`(g·w)(τ) = g w(τ)(g⁻¹·)`; complex-linear. `actY P q (Axi.rotZ θ)` is the rotation `R_θ`
about the third axis and `actY P q Axi.reflY` is the pushforward `J` by the reflection in the
meridional plane `{y₁ = 0}`. -/
def actY (g : Space ≃ₗᵢ[ℝ] Space) : Yq P q →L[ℂ] Yq P q :=
  (actLp q g).compLpL q AddCircle.haarAddCircle

theorem coeFn_actY (g : Space ≃ₗᵢ[ℝ] Space) (w : Yq P q) :
    (actY P q g w : AddCircle P → Lp CVec3 q (volume : Measure Space))
      =ᵐ[AddCircle.haarAddCircle] fun τ => actLp q g (w τ) :=
  (actLp q g).coeFn_compLpL w

/-- The real restriction of `actY` is the slice-wise `RieszLp.rotLpC`, the operator of
`RieszLp.lerayY_isometry`. -/
theorem actY_restrictScalars (g : Space ≃ₗᵢ[ℝ] Space) :
    (actY P q g).restrictScalars ℝ =
      (RieszLp.rotLpC q g).compLpL q (AddCircle.haarAddCircle (T := P)) := by
  ext1 w
  apply Lp.ext
  filter_upwards [coeFn_actY g w, (RieszLp.rotLpC q g).coeFn_compLpL
    (μ := AddCircle.haarAddCircle (T := P)) (p := q) w] with τ h1 h2
  rw [ContinuousLinearMap.coe_restrictScalars', h1, h2, actLp_eq_rotLpC]

theorem actY_trans (g h : Space ≃ₗᵢ[ℝ] Space) (w : Yq P q) :
    actY P q (g.trans h) w = actY P q h (actY P q g w) := by
  apply Lp.ext
  filter_upwards [coeFn_actY (g.trans h) w, coeFn_actY h (actY P q g w), coeFn_actY g w]
    with τ e1 e2 e3
  rw [e1, e2, e3, actLp_trans]

theorem actY_refl (w : Yq P q) : actY P q (LinearIsometryEquiv.refl ℝ Space) w = w := by
  apply Lp.ext
  filter_upwards [coeFn_actY (LinearIsometryEquiv.refl ℝ Space) w] with τ hτ
  rw [hτ, actLp_refl]

/-- A field is fixed by `g` iff its phase slices are fixed for a.e. `τ`. -/
theorem actY_eq_self_iff (g : Space ≃ₗᵢ[ℝ] Space) (w : Yq P q) :
    actY P q g w = w ↔ ∀ᵐ τ ∂AddCircle.haarAddCircle, actLp q g (w τ) = w τ := by
  constructor
  · intro h
    have h1 := coeFn_actY g w
    rw [h] at h1
    filter_upwards [h1] with τ hτ
    exact hτ.symm
  · intro h
    exact Lp.ext ((coeFn_actY g w).trans h)

end UnforcedLeray.B0415
