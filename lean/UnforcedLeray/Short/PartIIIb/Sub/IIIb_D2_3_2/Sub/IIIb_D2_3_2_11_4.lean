import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.FieldsSmooth

/-!
# Decomposition of `WardFieldsAxi` (`PartIII-b:IIIb-D2/3/2/11/4`, source 121-124, 6314-6316)

`wardFieldsAxi_of`: `WardFieldsAxi` follows from the equivariance of the first derivative
(`FderivEqv`), of the Laplacian (`LapEqv`), of the two second-order contractions
(`CdiffUUD2Eqv`) and of `(DX + DXᵀ)∇p` (`DXpEqv`) under linear isometries of `ℝ³`
(all pure chain-rule / trace-invariance facts, source 6314-6316).  The equivariance of `D_μ`, of
`[U, X]`, of `∇p` (from `IsExactProfile.equation`) and the assembly are proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `F` commutes with the linear isometry `g`. -/
def GEqv (g : Space ≃ₗᵢ[ℝ] Space) (F : Space → Space) : Prop := ∀ y, F (g y) = g (F y)

/-- **Chain rule** (source 6314-6316): `D F (g y) g = g D F (y)` for a differentiable `F`
commuting with the isometry `g`. -/
def FderivEqv : Prop :=
  ∀ (g : Space ≃ₗᵢ[ℝ] Space) (F : Space → Space), Differentiable ℝ F → GEqv g F →
    ∀ y v, fderiv ℝ F (g y) (g v) = g (fderiv ℝ F y v)

/-- **Laplacian** (source 6314-6316: orthogonal maps commute with the heat operator):
`Δ F (g y) = g (Δ F y)` for `C²` `F` commuting with `g` (trace invariance over the orthonormal
bases `e_j`, `g e_j`). -/
def LapEqv : Prop :=
  ∀ (g : Space ≃ₗᵢ[ℝ] Space) (F : Space → Space), ContDiff ℝ 2 F → GEqv g F →
    ∀ y, physLap F (g y) = g (physLap F y)

/-- **The two second-order contractions** `C_diff` and `(U⊗U):D²X` (source 4280-4282, 6314-6316)
are equivariant for `C²` fields commuting with `g` (`D²F(gy)(gu, gv) = g D²F(y)(u, v)` and
invariance of the full contraction over an orthonormal basis). -/
def CdiffUUD2Eqv : Prop :=
  ∀ (g : Space ≃ₗᵢ[ℝ] Space) (U X : Space → Space), ContDiff ℝ 2 U → ContDiff ℝ 2 X →
    GEqv g U → GEqv g X → ∀ y,
      physCdiff U X (g y) = g (physCdiff U X y) ∧ physUUD2 U X (g y) = g (physUUD2 U X y)

/-- **The pressure term** `(DX + DXᵀ)∇q` (source 4280-4282): equivariant for a `C²` field `X`
commuting with `g` and a `C¹` scalar `q` whose gradient commutes with `g`
(`fderiv q y = ⟪∇q y, ·⟫` and `D X (gy) = g D X (y) gᵀ`). -/
def DXpEqv : Prop :=
  ∀ (g : Space ≃ₗᵢ[ℝ] Space) (X : Space → Space) (q : Space → ℝ), ContDiff ℝ 2 X →
    ContDiff ℝ 1 q → GEqv g X → (∀ y, physGrad q (g y) = g (physGrad q y)) →
      ∀ y, physDXp X q (g y) = g (physDXp X q y)

theorem axi_gEqv {F : SpatialField} (h : AxiNoSwirlPt F) {g : Space ≃ₗᵢ[ℝ] Space}
    (hg : FixesAxis g) : GEqv g F := by
  intro y
  have := h g hg (g y)
  simpa using this.symm

theorem axi_of_gEqv {F : SpatialField}
    (h : ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g → GEqv g F) : AxiNoSwirlPt F := by
  intro g hg x
  have := h g hg (g.symm x)
  simp only [LinearIsometryEquiv.apply_symm_apply] at this
  rw [← this]


theorem slice_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → Space → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => F x.1 x.2)) (τ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F τ) :=
  hF.comp (contDiff_const.prodMk contDiff_id)

theorem slice_smooth' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → Space → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => F x.1 x.2)) (y : Space) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => F t y) :=
  hF.comp (contDiff_id.prodMk contDiff_const)

theorem dmu_gEqv (h1 : FderivEqv) (h2 : LapEqv) (ν μ : ℝ) (X : ℝ → Space → Space)
    (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2))
    (g : Space ≃ₗᵢ[ℝ] Space) (hg : ∀ t, GEqv g (X t)) (τ : ℝ) :
    GEqv g (physDmu ν μ X τ) := by
  intro y
  have hd : Differentiable ℝ (X τ) := (slice_smooth hX τ).differentiable (by simp)
  have ht : deriv (fun t => X t (g y)) τ = g (deriv (fun t => X t y) τ) := by
    have hdt : DifferentiableAt ℝ (fun t => X t y) τ :=
      ((slice_smooth' hX y).differentiable (by simp)) τ
    have := (g.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt τ
      hdt.hasDerivAt)
    have h3 : (fun t => X t (g y)) = fun t => g (X t y) := funext fun t => hg t y
    rw [h3]
    exact this.deriv
  unfold physDmu
  rw [ht, hg τ y, h1 g (X τ) hd (hg τ) y y, h2 g (X τ) ((slice_smooth hX τ).of_le (by simp))
    (hg τ) y]
  simp [map_sub, map_add, map_smul]


theorem grad_gEqv (h1 : FderivEqv) (h2 : LapEqv) {ν P : ℝ} {U : ℝ → SpatialField}
    {p : ℝ → Space → ℝ} (hP : IsExactProfile ν P U p) (g : Space ≃ₗᵢ[ℝ] Space)
    (hg : ∀ t, GEqv g (U t)) (t : ℝ) (y : Space) :
    physGrad (p t) (g y) = g (physGrad (p t) y) := by
  have hd : Differentiable ℝ (U t) := (slice_smooth hP.smoothU t).differentiable (by simp)
  have hD := dmu_gEqv h1 h2 ν 0 U hP.smoothU g hg t y
  have e1 := eq_neg_of_add_eq_zero_right (hP.equation t y)
  have e2 := eq_neg_of_add_eq_zero_right (hP.equation t (g y))
  rw [e2, e1, hD, hg t y, h1 g (U t) hd (hg t) y (U t y)]
  simp [map_neg, map_add]


theorem wardFieldsAxi_of (h1 : FderivEqv) (h2 : LapEqv) (h3 : CdiffUUD2Eqv) (h4 : DXpEqv) :
    WardFieldsAxi := by
  intro ν μ P U X p hP hU hX hXa τ
  have hUs := hP.smoothU
  have hD : ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g → ∀ t, GEqv g (X t) :=
    fun g hg t => axi_gEqv (hXa t) hg
  have hDU : ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g → ∀ t, GEqv g (U t) :=
    fun g hg t => axi_gEqv (hU t) hg
  have hUd : ∀ t, Differentiable ℝ (U t) := fun t =>
    (slice_smooth hUs t).differentiable (by simp)
  have hXd : ∀ t, Differentiable ℝ (X t) := fun t =>
    (slice_smooth hX t).differentiable (by simp)
  have hbr : ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g →
      GEqv g (fun y => physBracket (U τ) (X τ) y) := by
    intro g hg y
    have a := hDU g hg τ y
    have b := hD g hg τ y
    show physBracket (U τ) (X τ) (g y) = g (physBracket (U τ) (X τ) y)
    unfold physBracket
    rw [a, b, h1 g (X τ) (hXd τ) (hD g hg τ) y (U τ y),
      h1 g (U τ) (hUd τ) (hDU g hg τ) y (X τ y), map_sub]
  refine ⟨axi_of_gEqv hbr, ?_, ?_⟩
  · refine axi_of_gEqv fun g hg y => ?_
    have hX2 : ContDiff ℝ 2 (X τ) := (slice_smooth hX τ).of_le (by simp)
    have hU2 : ContDiff ℝ 2 (U τ) := (slice_smooth hUs τ).of_le (by simp)
    have hDm := dmu_gEqv h1 h2 ν (μ + 1) X hX g (hD g hg)
    have hDd : Differentiable ℝ (physDmu ν (μ + 1) X τ) :=
      ((slice_smooth (F := physDmu ν (μ + 1) X) (fs_dmu hX ν (μ + 1)) τ).differentiable
        (by simp))
    have hq : ContDiff ℝ 1 (p τ) := (slice_smooth hP.smoothP τ).of_le (by simp)
    have hgr := grad_gEqv h1 h2 hP g (hDU g hg) τ
    obtain ⟨c1, c2⟩ := h3 g (U τ) (X τ) hU2 hX2 (hDU g hg τ) (hD g hg τ) y
    have c3 := h4 g (X τ) (p τ) hX2 hq (hD g hg τ) hgr y
    unfold physResidual
    rw [hDU g hg τ y, h1 g _ hDd (hDm τ) y (U τ y), c1, c2, c3]
    simp [map_sub, map_add, map_smul]
  · refine axi_of_gEqv fun g hg y => ?_
    have : physBracket (U τ) (X τ) (g y) = g (physBracket (U τ) (X τ) y) := hbr g hg y
    have hDm := dmu_gEqv h1 h2 ν (μ + 1) X hX g (hD g hg) τ y
    simp only [map_add]
    rw [hDm, this]

end UnforcedLeray.Short.PartIIIb.Concrete
