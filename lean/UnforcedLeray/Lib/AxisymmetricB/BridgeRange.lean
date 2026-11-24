import UnforcedLeray.Lib.AxisymmetricB.Bridge

/-!
# AX04 (range in `Y₂`): the image of `J_v` in D2's Bochner space


§5 Layer 3, target AX04 (`range_Jv` stated on `Y2 P`), decision D2 (`Y₂ = Yq P 2`). Blueprint
units served: B0417 (`eq:m4-free-spaces`, tex 7272–7297: `J_v` unitary onto the
axisymmetric-no-swirl subspace of the period-averaged `Y₂`), B0482 (tex 7920–7949). `Y₂` is
complex (tex 7313–7317), and `Statement.IsAxisymmetricNoSwirl` is a predicate on real fields;
the axisymmetric-no-swirl subspace of `Y₂` is read as the classes whose phase slices are, for
a.e. phase, complexifications of real 𝒪-invariant fields (`IsRealAxiY`).

* `reC : ℂ³ →L[ℝ] ℝ³`, the coordinatewise real part (adapted from `reL` of

* `IsRealAxiY P V`: for a.e. `θ ∈ ℝ/Pℤ`, `V(θ) = w + 0i` a.e. for some real field `w`
  axisymmetric without swirl;
* `range_JvY2` (**AX04 `range_Jv` in `Y₂`**): `range J_v = {V ∈ Y₂ | IsRealAxiY P V}`, where
  `J_v = JvY2 : H →ₗᵢ[ℝ] Y₂`. The inclusion `⊇` builds the real phase field
  `U(t, y) = Re V(t mod P)(y)` in `L²(phaseμ P; ℝ³)`, checks `U ∈ Y2Axi P` and `toY2 U = V`,
  and applies `mem_range_Jv`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter
open scoped ENNReal

namespace UnforcedLeray.Axi

open UnforcedLeray.PhaseSpace (CVec3 Yq)

/-- The coordinatewise real part `ℂ³ → ℝ³`, real-linear. -/
def reC : CVec3 →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => (x i).re)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }

@[simp] theorem reC_apply (x : CVec3) (i : Fin 3) : reC x i = (x i).re := rfl

@[simp] theorem reC_cplxV (v : Space) : reC (cplxV v) = v := by
  ext i
  simp

section Range

variable (P : ℝ) [hP : Fact (0 < P)]

theorem coe_phaseRep (θ : AddCircle P) : ((phaseRep P θ : ℝ) : AddCircle P) = θ :=
  AddCircle.coe_equivIoc

/-- `(t, y) ↦ (t mod P, y)` carries `phaseμ P` to `haar ⊗ dy`. -/
theorem measurePreserving_coeProd :
    MeasurePreserving (Prod.map (fun t : ℝ => (t : AddCircle P)) id) (phaseμ P)
      ((AddCircle.haarAddCircle (T := P)).prod (volume : Measure Space)) :=
  (measurePreserving_coe_addCircle P).prod (MeasurePreserving.id volume)

/-- **The axisymmetric-no-swirl subspace of `Y₂`**: for a.e. phase `θ`, the slice `V(θ)` is the
complexification of a real field which is axisymmetric without swirl. -/
def IsRealAxiY (V : Yq P 2) : Prop :=
  ∀ᵐ θ ∂AddCircle.haarAddCircle (T := P), ∃ w : Space → Space,
    ((V θ : Lp CVec3 2 (volume : Measure Space)) : Space → CVec3) =ᵐ[volume]
      (fun y => cplxV (w y)) ∧ IsAxisymmetricNoSwirl w

/-- For `μT`-a.e. `t` to `haar`-a.e. `θ` along `phaseRep`. -/
theorem ae_phaseRep_of_ae_Ioc {p : ℝ → Prop}
    (h : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) P)), p t) :
    ∀ᵐ θ ∂AddCircle.haarAddCircle (T := P), p (phaseRep P θ) :=
  (measurePreserving_phaseRep P).quasiMeasurePreserving.ae (Measure.ae_smul_measure h _)

/-- For `haar`-a.e. `θ` to a.e. `t ∈ (0, P]` along `t ↦ t mod P`. -/
theorem ae_Ioc_of_ae_circle {p : AddCircle P → Prop}
    (h : ∀ᵐ θ ∂AddCircle.haarAddCircle (T := P), p θ) :
    ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioc (0 : ℝ) P)), p (t : AddCircle P) := by
  have h' := (measurePreserving_coe_addCircle P).quasiMeasurePreserving.ae h
  exact (Measure.ae_ennreal_smul_measure_iff
    (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)).1 h'

/-- The real phase field of a class of `Y₂`: `U(t, y) = Re V(t mod P)(y)`. -/
def realPart (V : Yq P 2) : Lp Space 2 (phaseμ P) :=
  Lp.compMeasurePreserving (Prod.map (fun t : ℝ => (t : AddCircle P)) id)
    (measurePreserving_coeProd P)
    (reC.compLpL 2 ((AddCircle.haarAddCircle (T := P)).prod (volume : Measure Space))
      ((FreeStress.prodLpEquiv (F := CVec3) (q := 2) (ν := AddCircle.haarAddCircle (T := P))
        (μ := (volume : Measure Space))).symm V))

theorem coeFn_realPart (V : Yq P 2) :
    (realPart P V : ℝ × Space → Space) =ᵐ[phaseμ P] fun x =>
      reC (((FreeStress.prodLpEquiv (F := CVec3) (q := 2)
        (ν := AddCircle.haarAddCircle (T := P)) (μ := (volume : Measure Space))).symm V :
          AddCircle P × Space → CVec3) ((x.1 : AddCircle P), x.2)) := by
  have e1 := Lp.coeFn_compMeasurePreserving
    (reC.compLpL 2 ((AddCircle.haarAddCircle (T := P)).prod (volume : Measure Space))
      ((FreeStress.prodLpEquiv (F := CVec3) (q := 2) (ν := AddCircle.haarAddCircle (T := P))
        (μ := (volume : Measure Space))).symm V)) (measurePreserving_coeProd P)
  have e2 := (measurePreserving_coeProd P).quasiMeasurePreserving.ae_eq_comp
    (reC.coeFn_compLpL ((FreeStress.prodLpEquiv (F := CVec3) (q := 2)
      (ν := AddCircle.haarAddCircle (T := P)) (μ := (volume : Measure Space))).symm V))
  exact e1.trans e2

theorem realPart_mem_Y2Axi {V : Yq P 2} (hV : IsRealAxiY P V) : realPart P V ∈ Y2Axi P := by
  set G := (FreeStress.prodLpEquiv (F := CVec3) (q := 2) (ν := AddCircle.haarAddCircle (T := P))
    (μ := (volume : Measure Space))).symm V with hG
  have hsl := FreeStress.prodLpEquiv_symm_ae (F := CVec3) (q := 2)
    (ν := AddCircle.haarAddCircle (T := P)) (μ := (volume : Measure Space)) V
  have hθ : ∀ᵐ θ ∂AddCircle.haarAddCircle (T := P), ∃ w : Space → Space,
      (fun y => (G : AddCircle P × Space → CVec3) (θ, y)) =ᵐ[volume] (fun y => cplxV (w y)) ∧
        IsAxisymmetricNoSwirl w := by
    filter_upwards [hsl, hV] with θ h1 h2
    obtain ⟨w, hw, hax⟩ := h2
    exact ⟨w, h1.trans hw, hax⟩
  rw [mem_Y2Axi]
  filter_upwards [ae_slice (coeFn_realPart P V), ae_Ioc_of_ae_circle P hθ] with t h1 h2
  obtain ⟨w, hw, hax⟩ := h2
  refine isAxisymmetricNoSwirl_congr hax ?_
  filter_upwards [h1, hw] with y hy1 hy2
  rw [hy1]
  change reC ((G : AddCircle P × Space → CVec3) ((t : AddCircle P), y)) = w y
  rw [hy2, reC_cplxV]

theorem toY2_realPart {V : Yq P 2} (hV : IsRealAxiY P V) : toY2 P (realPart P V) = V := by
  set G := (FreeStress.prodLpEquiv (F := CVec3) (q := 2) (ν := AddCircle.haarAddCircle (T := P))
    (μ := (volume : Measure Space))).symm V with hG
  have hsl := FreeStress.prodLpEquiv_symm_ae (F := CVec3) (q := 2)
    (ν := AddCircle.haarAddCircle (T := P)) (μ := (volume : Measure Space)) V
  have hU := ae_phaseRep_of_ae_Ioc P (ae_slice (coeFn_realPart P V))
  apply Lp.ext
  filter_upwards [toY2_ae P (realPart P V), hU, hsl, hV] with θ h1 h2 h3 h4
  obtain ⟨w, hw, -⟩ := h4
  apply Lp.ext
  refine h1.trans ?_
  filter_upwards [h2, h3, hw] with y hy2 hy3 hy4
  rw [hy2]
  change cplxV (reC ((G : AddCircle P × Space → CVec3)
    (((phaseRep P θ : ℝ) : AddCircle P), y))) = _
  rw [coe_phaseRep]
  rw [hy3, hy4, reC_cplxV]

end Range

/-- **AX04 `range_Jv` in `Y₂`** (B0417, tex 7280–7283; B0482). The range of the ring lift
read in D2's Bochner space, `J_v = JvY2 : H →ₗᵢ[ℝ] Y₂`, is exactly the set of classes whose
phase slices are, for a.e. phase, complexifications of real fields axisymmetric without
swirl. -/
theorem range_JvY2 {R c P : ℝ} [Fact (0 < P)] (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R) :
    Set.range (JvY2 hR hc hP) = {V : Yq P 2 | IsRealAxiY P V} := by
  ext V
  constructor
  · rintro ⟨b, rfl⟩
    have hU := Jv_mem_Y2Axi hR hc hP b
    rw [mem_Y2Axi] at hU
    show IsRealAxiY P (toY2 P (Jv hR hc hP b))
    filter_upwards [toY2_ae P (Jv hR hc hP b), ae_phaseRep_of_ae_Ioc P hU] with θ h1 h2
    exact ⟨fun y => Jv hR hc hP b (phaseRep P θ, y), h1, h2⟩
  · intro hV
    obtain ⟨b, hb⟩ := mem_range_Jv hR hc hP (realPart P V) (realPart_mem_Y2Axi P hV)
    refine ⟨b, ?_⟩
    show toY2 P (Jv hR hc hP b) = V
    rw [hb]
    exact toY2_realPart P hV

end UnforcedLeray.Axi
