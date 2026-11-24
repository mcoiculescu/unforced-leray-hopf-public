import UnforcedLeray.Lib.Sobolev.Space
import Mathlib.Analysis.Complex.Basic

/-!
# Value maps on `Sob.W` and complexification (INF11 target S2, last part)

Scoping note `INF11-INF14-Sobolev.md` §5.1 (S2: `W.complexify`, "isometric, with conjugation
symmetry") and §6 risk 10 ("`W.complexify` must be isometric and conjugation-equivariant");
decision D11 of the scoping README §3 ("Complexification: `W.complexify` (INF11 S2) plus WIP
`RealStructure`"). Blueprint units served: B0008 (complex-valued `H^j_M`, tex 653–660), B0062,
B0083 (complex spectral statements on real spaces), and every unit using the complexified
localisation spaces (tex 13876–13886 for the weighted pairing).

## Main declarations
* `piLp_norm_congr`: a `PiLp` norm depends only on the component norms;
* `W.mapCLM L`: a real-linear map `L : F →L[ℝ] G` of values acts componentwise
  `W D ρ 𝕜 F k p →L[ℝ] W D ρ 𝕜' G k p` (weak derivatives commute with `L`);
  `W.deriv_mapCLM`, `W.mapCLM_mapCLM`, `W.mapCLM_id`, `W.norm_mapCLM` (for isometric `L`);
* `ofRealL m : ℝ^m →ₗᵢ[ℝ] ℂ^m`, `conjL m`, `reL m`, `imL m` (componentwise);
* `W.complexify : W D ρ ℝ (ℝ^m) k p →L[ℝ] W D ρ ℂ (ℂ^m) k p`, `W.norm_complexify` (isometric);
* `W.conj` (componentwise complex conjugation; real-linear, isometric, involutive, conjugate
  linear: `W.conj_smul`), `W.conj_complexify` (conjugation equivariance: the image of
  `complexify` is fixed by `conj`);
* `W.realPart`, `W.imagPart`, `W.realPart_complexify`, `W.imagPart_complexify`,
  `W.complexify_realPart_add_imagPart` (every complex element is `x + i y` with `x, y` real),
  `W.conj_eq` (`conj (x + i y) = x - i y`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ComplexConjugate

namespace UnforcedLeray.Sob

/-! ### `PiLp` norms depend only on the component norms -/

theorem piLp_norm_congr {p : ℝ≥0∞} [hp1 : Fact (1 ≤ p)] {ι : Type*} [Fintype ι]
    {β γ : ι → Type*} [∀ i, NormedAddCommGroup (β i)] [∀ i, NormedAddCommGroup (γ i)]
    {x : PiLp p β} {y : PiLp p γ} (h : ∀ i, ‖x i‖ = ‖y i‖) : ‖x‖ = ‖y‖ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    simp only [h]
  · have hp' : 0 < p.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le hp1.out).ne' hp
    rw [PiLp.norm_eq_sum hp', PiLp.norm_eq_sum hp']
    simp only [h]

/-- An isometric map of values is isometric on `L^p`. -/
theorem norm_compLp_of_isometry {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {p : ℝ≥0∞} (L : F →ₗᵢ[ℝ] G) (f : Lp F p μ) :
    ‖L.toContinuousLinearMap.compLp f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae ?_
  filter_upwards [L.toContinuousLinearMap.coeFn_compLp f] with a ha
  rw [ha]
  exact L.norm_map _

theorem compLp_compLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H] {p : ℝ≥0∞}
    (L : F →L[ℝ] G) (L' : G →L[ℝ] H) (f : Lp F p μ) :
    L'.compLp (L.compLp f) = (L'.comp L).compLp f := by
  apply Lp.ext
  filter_upwards [L'.coeFn_compLp (L.compLp f), L.coeFn_compLp f,
    (L'.comp L).coeFn_compLp f] with a h1 h2 h3
  rw [h1, h2, h3]
  rfl

theorem compLp_id {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} (f : Lp F p μ) :
    (ContinuousLinearMap.id ℝ F).compLp f = f := by
  apply Lp.ext
  filter_upwards [(ContinuousLinearMap.id ℝ F).coeFn_compLp f] with a h1
  rw [h1]
  rfl

theorem compLp_zero_map {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {p : ℝ≥0∞} (f : Lp F p μ) : (0 : F →L[ℝ] G).compLp f = 0 := by
  apply Lp.ext
  filter_upwards [(0 : F →L[ℝ] G).coeFn_compLp f, Lp.coeFn_zero (E := G) (p := p) (μ := μ)]
    with a h1 h2
  rw [h1, h2]
  rfl

/-! ### Value maps -/

section Map

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {n : ℕ} {D : TestDomain E n} {ρ : Weight E}
  {𝕜 : Type*} [RCLike 𝕜] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F]
  {𝕜' : Type*} [RCLike 𝕜'] {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜' G]
  [NormedSpace ℝ G] [IsScalarTower ℝ 𝕜' G] [FiniteDimensional 𝕜' G]
  {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (D ρ F G k p) in
/-- Apply a real-linear map of values to every component of a tuple. -/
def tupleMap (L : F →L[ℝ] G) : SobTuple D ρ F k p →L[ℝ] SobTuple D ρ G k p :=
  (PiLp.continuousLinearEquiv p ℝ
      (fun _ : Idx n k => Lp G p (wμ D.μ ρ))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun α => (L.compLpL p (wμ D.μ ρ)).comp
      (PiLp.proj p (fun _ : Idx n k => Lp F p (wμ D.μ ρ)) α))

theorem tupleMap_apply (L : F →L[ℝ] G) (x : SobTuple D ρ F k p) (α : Idx n k) :
    (tupleMap D ρ F G k p L x) α = L.compLp (x α) := rfl

theorem mem_SobSub_tupleMap (L : F →L[ℝ] G) (x : W D ρ 𝕜 F k p) :
    tupleMap D ρ F G k p L (x : SobTuple D ρ F k p) ∈ SobSub D ρ 𝕜' G k p := by
  haveI := completeSpace_of_finiteDimensional 𝕜 F
  haveI := completeSpace_of_finiteDimensional 𝕜' G
  rw [mem_SobSub_iff]
  intro α
  refine ((W.hasWeakDeriv x α).map_clm L).congr_ae ?_ ?_
  · exact (ae_eq_wμ_iff D.μ ρ).mp (L.coeFn_compLp' ((x : SobTuple D ρ F k p) Idx.zero)).symm
  · exact (ae_eq_wμ_iff D.μ ρ).mp (L.coeFn_compLp' ((x : SobTuple D ρ F k p) α)).symm

/-- **Value maps on `W`** (S2): a real-linear map of values acts componentwise on `W`, because
weak derivatives commute with continuous linear maps. -/
def W.mapCLM (L : F →L[ℝ] G) : W D ρ 𝕜 F k p →L[ℝ] W D ρ 𝕜' G k p :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨tupleMap D ρ F G k p L (x : SobTuple D ρ F k p), mem_SobSub_tupleMap L x⟩
      map_add' := fun x y => Subtype.ext
        (map_add (tupleMap D ρ F G k p L) (x : SobTuple D ρ F k p) (y : SobTuple D ρ F k p))
      map_smul' := fun c x => Subtype.ext
        (map_smul (tupleMap D ρ F G k p L) c (x : SobTuple D ρ F k p)) }
    ‖tupleMap D ρ F G k p L‖ fun x => (tupleMap D ρ F G k p L).le_opNorm (x : SobTuple D ρ F k p)

theorem W.coe_mapCLM (L : F →L[ℝ] G) (x : W D ρ 𝕜 F k p) :
    ((W.mapCLM (𝕜' := 𝕜') L x : W D ρ 𝕜' G k p) : SobTuple D ρ G k p) =
      tupleMap D ρ F G k p L (x : SobTuple D ρ F k p) := rfl

theorem W.deriv_mapCLM (L : F →L[ℝ] G) (x : W D ρ 𝕜 F k p) (α : Idx n k) :
    W.deriv D ρ 𝕜' G k p α (W.mapCLM L x) = L.compLp (W.deriv D ρ 𝕜 F k p α x) := rfl

theorem W.value_mapCLM (L : F →L[ℝ] G) (x : W D ρ 𝕜 F k p) :
    W.value D ρ 𝕜' G k p (W.mapCLM L x) = L.compLp (W.value D ρ 𝕜 F k p x) := rfl

theorem W.coeFn_deriv_mapCLM (L : F →L[ℝ] G) (x : W D ρ 𝕜 F k p) (α : Idx n k) :
    ⇑(W.deriv D ρ 𝕜' G k p α (W.mapCLM L x)) =ᵐ[wμ D.μ ρ]
      fun y => L (W.deriv D ρ 𝕜 F k p α x y) :=
  L.coeFn_compLp' _

theorem W.mapCLM_mapCLM {𝕜'' : Type*} [RCLike 𝕜''] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜'' H] [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜'' H] [FiniteDimensional 𝕜'' H]
    (L : F →L[ℝ] G) (L' : G →L[ℝ] H) (x : W D ρ 𝕜 F k p) :
    W.mapCLM (𝕜' := 𝕜'') L' (W.mapCLM (𝕜' := 𝕜') L x) = W.mapCLM (L'.comp L) x :=
  Subtype.ext (PiLp.ext fun α => compLp_compLp L L' _)

theorem W.mapCLM_id (x : W D ρ 𝕜 F k p) :
    W.mapCLM (𝕜' := 𝕜) (ContinuousLinearMap.id ℝ F) x = x :=
  Subtype.ext (PiLp.ext fun α => compLp_id _)

/-- An isometric map of values is isometric on `W`. -/
theorem W.norm_mapCLM (L : F →ₗᵢ[ℝ] G) (x : W D ρ 𝕜 F k p) :
    ‖W.mapCLM (𝕜' := 𝕜') L.toContinuousLinearMap x‖ = ‖x‖ := by
  change ‖tupleMap D ρ F G k p L.toContinuousLinearMap (x : SobTuple D ρ F k p)‖ =
    ‖(x : SobTuple D ρ F k p)‖
  exact piLp_norm_congr fun α => norm_compLp_of_isometry L _

end Map

/-! ### Componentwise maps between `ℝ^m` and `ℂ^m` -/

section Coordinates

variable (m : ℕ)

/-- The inclusion `ℝ^m → ℂ^m`, `x ↦ (x_i : ℂ)_i`. -/
def ofRealL : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℂ (Fin m) where
  toFun x := WithLp.toLp 2 fun i => (x i : ℂ)
  map_add' x y := PiLp.ext fun i => by simp
  map_smul' c x := PiLp.ext fun i => by simp
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp

@[simp] theorem ofRealL_apply (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    ofRealL m x i = (x i : ℂ) := rfl

/-- Componentwise complex conjugation on `ℂ^m` (real-linear isometry). -/
def conjL : EuclideanSpace ℂ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℂ (Fin m) where
  toFun z := WithLp.toLp 2 fun i => conj (z i)
  map_add' x y := PiLp.ext fun i => by simp
  map_smul' c x := PiLp.ext fun i => by simp
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp

@[simp] theorem conjL_apply (z : EuclideanSpace ℂ (Fin m)) (i : Fin m) :
    conjL m z i = conj (z i) := rfl

/-- Componentwise real part `ℂ^m → ℝ^m`. -/
def reL : EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => Complex.reCLM.comp (PiLp.proj 2 (fun _ : Fin m => ℂ) i))

@[simp] theorem reL_apply (z : EuclideanSpace ℂ (Fin m)) (i : Fin m) :
    reL m z i = (z i).re := rfl

/-- Componentwise imaginary part `ℂ^m → ℝ^m`. -/
def imL : EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => Complex.imCLM.comp (PiLp.proj 2 (fun _ : Fin m => ℂ) i))

@[simp] theorem imL_apply (z : EuclideanSpace ℂ (Fin m)) (i : Fin m) :
    imL m z i = (z i).im := rfl

end Coordinates

/-! ### Complexification of `W` -/

section Complexify

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {n : ℕ} {D : TestDomain E n} {ρ : Weight E}
  {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {m : ℕ}

/-- **Complexification** (S2): `W(ρ dμ; ℝ^m) → W(ρ dμ; ℂ^m)`, `f ↦ f + 0 i`, componentwise. -/
def W.complexify :
    W D ρ ℝ (EuclideanSpace ℝ (Fin m)) k p →L[ℝ] W D ρ ℂ (EuclideanSpace ℂ (Fin m)) k p :=
  W.mapCLM (ofRealL m).toContinuousLinearMap

/-- Componentwise complex conjugation on `W(ρ dμ; ℂ^m)`. -/
def W.conj :
    W D ρ ℂ (EuclideanSpace ℂ (Fin m)) k p →L[ℝ] W D ρ ℂ (EuclideanSpace ℂ (Fin m)) k p :=
  W.mapCLM (conjL m).toContinuousLinearMap

/-- The real part `W(ρ dμ; ℂ^m) → W(ρ dμ; ℝ^m)`. -/
def W.realPart :
    W D ρ ℂ (EuclideanSpace ℂ (Fin m)) k p →L[ℝ] W D ρ ℝ (EuclideanSpace ℝ (Fin m)) k p :=
  W.mapCLM (reL m)

/-- The imaginary part `W(ρ dμ; ℂ^m) → W(ρ dμ; ℝ^m)`. -/
def W.imagPart :
    W D ρ ℂ (EuclideanSpace ℂ (Fin m)) k p →L[ℝ] W D ρ ℝ (EuclideanSpace ℝ (Fin m)) k p :=
  W.mapCLM (imL m)

theorem W.deriv_complexify (x : W D ρ ℝ (EuclideanSpace ℝ (Fin m)) k p) (α : Idx n k) :
    W.deriv D ρ ℂ (EuclideanSpace ℂ (Fin m)) k p α (W.complexify x) =
      (ofRealL m).toContinuousLinearMap.compLp
        (W.deriv D ρ ℝ (EuclideanSpace ℝ (Fin m)) k p α x) := rfl

/-- `complexify` is isometric. -/
theorem W.norm_complexify (x : W D ρ ℝ (EuclideanSpace ℝ (Fin m)) k p) :
    ‖W.complexify x‖ = ‖x‖ :=
  W.norm_mapCLM (ofRealL m) x

/-- `conj` is isometric. -/
theorem W.norm_conj (z : W D ρ ℂ (EuclideanSpace ℂ (Fin m)) k p) : ‖W.conj z‖ = ‖z‖ :=
  W.norm_mapCLM (conjL m) z

/-- `conj` is an involution. -/
theorem W.conj_conj (z : W D ρ ℂ (EuclideanSpace ℂ (Fin m)) k p) : W.conj (W.conj z) = z := by
  rw [W.conj, W.mapCLM_mapCLM]
  have : (conjL m).toContinuousLinearMap.comp (conjL m).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ _ := by
    refine ContinuousLinearMap.ext fun z => PiLp.ext fun i => ?_
    simp
  rw [this, W.mapCLM_id]

/-- **Conjugation equivariance** (critic §5b): the image of `complexify` is fixed by `conj`. -/
theorem W.conj_complexify (x : W D ρ ℝ (EuclideanSpace ℝ (Fin m)) k p) :
    W.conj (W.complexify x) = W.complexify x := by
  rw [W.conj, W.complexify, W.mapCLM_mapCLM]
  have : (conjL m).toContinuousLinearMap.comp (ofRealL m).toContinuousLinearMap =
      (ofRealL m).toContinuousLinearMap := by
    refine ContinuousLinearMap.ext fun y => PiLp.ext fun i => ?_
    simp
  rw [this]

theorem W.realPart_complexify (x : W D ρ ℝ (EuclideanSpace ℝ (Fin m)) k p) :
    W.realPart (W.complexify x) = x := by
  rw [W.realPart, W.complexify, W.mapCLM_mapCLM]
  have : (reL m).comp (ofRealL m).toContinuousLinearMap = ContinuousLinearMap.id ℝ _ := by
    refine ContinuousLinearMap.ext fun y => PiLp.ext fun i => ?_
    simp
  rw [this, W.mapCLM_id]

theorem W.imagPart_complexify (x : W D ρ ℝ (EuclideanSpace ℝ (Fin m)) k p) :
    W.imagPart (W.complexify x) = 0 := by
  rw [W.imagPart, W.complexify, W.mapCLM_mapCLM]
  have : (imL m).comp (ofRealL m).toContinuousLinearMap = 0 := by
    refine ContinuousLinearMap.ext fun y => PiLp.ext fun i => ?_
    simp
  rw [this]
  exact Subtype.ext (PiLp.ext fun α => compLp_zero_map _)

/-- **Real and imaginary parts**: every complex element is `x + i y` with `x, y` real. -/
theorem W.complexify_realPart_add_imagPart (z : W D ρ ℂ (EuclideanSpace ℂ (Fin m)) k p) :
    W.complexify (W.realPart z) + (Complex.I : ℂ) • W.complexify (W.imagPart z) = z := by
  refine Subtype.ext (PiLp.ext fun α => ?_)
  apply Lp.ext
  set w := (z : SobTuple D ρ (EuclideanSpace ℂ (Fin m)) k p) α
  have e1 := (ofRealL m).toContinuousLinearMap.coeFn_compLp ((reL m).compLp w)
  have e2 := (reL m).coeFn_compLp w
  have e3 := (ofRealL m).toContinuousLinearMap.coeFn_compLp ((imL m).compLp w)
  have e4 := (imL m).coeFn_compLp w
  have e5 := Lp.coeFn_add ((ofRealL m).toContinuousLinearMap.compLp ((reL m).compLp w))
    ((Complex.I : ℂ) • (ofRealL m).toContinuousLinearMap.compLp ((imL m).compLp w))
  have e6 := Lp.coeFn_smul (Complex.I : ℂ)
    ((ofRealL m).toContinuousLinearMap.compLp ((imL m).compLp w))
  filter_upwards [e1, e2, e3, e4, e5, e6] with a h1 h2 h3 h4 h5 h6
  change ((ofRealL m).toContinuousLinearMap.compLp ((reL m).compLp w) +
    (Complex.I : ℂ) • (ofRealL m).toContinuousLinearMap.compLp ((imL m).compLp w) :
      Lp (EuclideanSpace ℂ (Fin m)) p (wμ D.μ ρ)) a = w a
  rw [h5, Pi.add_apply, h6, Pi.smul_apply, h1, h3, h2, h4]
  refine PiLp.ext fun i => ?_
  simp only [LinearIsometry.coe_toContinuousLinearMap, PiLp.add_apply, PiLp.smul_apply,
    ofRealL_apply, reL_apply, imL_apply, smul_eq_mul]
  rw [mul_comm]
  exact Complex.re_add_im (w a i)

/-- `conj (x + i y) = x - i y`. -/
theorem W.conj_eq (z : W D ρ ℂ (EuclideanSpace ℂ (Fin m)) k p) :
    W.conj z = W.complexify (W.realPart z) - (Complex.I : ℂ) • W.complexify (W.imagPart z) := by
  refine Subtype.ext (PiLp.ext fun α => ?_)
  apply Lp.ext
  set w := (z : SobTuple D ρ (EuclideanSpace ℂ (Fin m)) k p) α
  have e0 := (conjL m).toContinuousLinearMap.coeFn_compLp w
  have e1 := (ofRealL m).toContinuousLinearMap.coeFn_compLp ((reL m).compLp w)
  have e2 := (reL m).coeFn_compLp w
  have e3 := (ofRealL m).toContinuousLinearMap.coeFn_compLp ((imL m).compLp w)
  have e4 := (imL m).coeFn_compLp w
  have e5 := Lp.coeFn_sub ((ofRealL m).toContinuousLinearMap.compLp ((reL m).compLp w))
    ((Complex.I : ℂ) • (ofRealL m).toContinuousLinearMap.compLp ((imL m).compLp w))
  have e6 := Lp.coeFn_smul (Complex.I : ℂ)
    ((ofRealL m).toContinuousLinearMap.compLp ((imL m).compLp w))
  filter_upwards [e0, e1, e2, e3, e4, e5, e6] with a h0 h1 h2 h3 h4 h5 h6
  change ((conjL m).toContinuousLinearMap.compLp w : Lp (EuclideanSpace ℂ (Fin m)) p
    (wμ D.μ ρ)) a = ((ofRealL m).toContinuousLinearMap.compLp ((reL m).compLp w) -
    (Complex.I : ℂ) • (ofRealL m).toContinuousLinearMap.compLp ((imL m).compLp w) :
      Lp (EuclideanSpace ℂ (Fin m)) p (wμ D.μ ρ)) a
  rw [h0, h5, Pi.sub_apply, h6, Pi.smul_apply, h1, h3, h2, h4]
  refine PiLp.ext fun i => ?_
  simp only [LinearIsometry.coe_toContinuousLinearMap, PiLp.sub_apply, PiLp.smul_apply,
    ofRealL_apply, reL_apply, imL_apply, conjL_apply, smul_eq_mul]
  apply Complex.ext <;> simp

/-- `conj` is conjugate-linear. -/
theorem W.conj_smul (c : ℂ) (z : W D ρ ℂ (EuclideanSpace ℂ (Fin m)) k p) :
    W.conj (c • z) = (starRingEnd ℂ c) • W.conj z := by
  refine Subtype.ext (PiLp.ext fun α => ?_)
  apply Lp.ext
  set w := (z : SobTuple D ρ (EuclideanSpace ℂ (Fin m)) k p) α
  have e0 := (conjL m).toContinuousLinearMap.coeFn_compLp (c • w)
  have e1 := (conjL m).toContinuousLinearMap.coeFn_compLp w
  have e2 := Lp.coeFn_smul c w
  have e3 := Lp.coeFn_smul (starRingEnd ℂ c) ((conjL m).toContinuousLinearMap.compLp w)
  filter_upwards [e0, e1, e2, e3] with a h0 h1 h2 h3
  change ((conjL m).toContinuousLinearMap.compLp (c • w) : Lp (EuclideanSpace ℂ (Fin m)) p
    (wμ D.μ ρ)) a = ((starRingEnd ℂ c) • (conjL m).toContinuousLinearMap.compLp w :
      Lp (EuclideanSpace ℂ (Fin m)) p (wμ D.μ ρ)) a
  rw [h0, h3, Pi.smul_apply, h1, h2, Pi.smul_apply]
  refine PiLp.ext fun i => ?_
  simp

end Complexify

end UnforcedLeray.Sob
