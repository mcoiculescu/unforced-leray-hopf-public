import UnforcedLeray.Units.B0223.Group
import UnforcedLeray.Units.B0220.WeightedComp

/-!
# B0223 helper: the three factors of `S_ε(t)` on the periodic `L²`

Blueprint unit B0223 (label `eq:st18-t00116`), `paper/main.tex` lines 3348–3356.

`S_ε(t)F(x, τ) = e^{t/2} [e^{νε²(e^t - 1)Δ} F(·, τ - t)](e^{t/2} x)` is the product of three
commuting-up-to-rescaling operators on `X E P = L²(ℝ³ × ℝ/Pℤ; E)`:

* the spatial heat semigroup `heatC θ = e^{θΔ_x}` (the library operator `Heat.heatLp` of
  `Lib/HeatR3/LpOp.lean` for the translations `ι y = (y, 0)`, bypass BP1), made complex linear;
* the phase translation `transC t F (x, τ) = F(x, τ - t)`, a unitary (`transEquiv`);
* the normalized dilation `dilN a F (x, τ) = a^{3/2} F(a x, τ)`, a unitary for `a > 0`
  (a weighted composition, `B0220.WeightedComp`).

Commutation rules: `transC` commutes with `heatC` and `dilN`; `heatC θ ∘ dilN a = dilN a ∘
heatC (a²θ)` (the dilation identity of the Gaussian, `Gaussian.gaussKernel_scale`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open UnforcedLeray.Gaussian (Euc gaussKernel)

namespace UnforcedLeray.B0223

variable {P : ℝ} [Fact (0 < P)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-! ### The spatial heat semigroup -/

/-- The spatial translations `y ↦ (y, 0)` of `ℝ³ × ℝ/Pℤ`. -/
def ιx (P : ℝ) : Euc 3 →+ PSpace P := AddMonoidHom.inl Space (AddCircle P)

theorem continuous_ιx : Continuous (ιx P) :=
  show Continuous fun y : Euc 3 => ((y, 0) : PSpace P) from continuous_id.prodMk continuous_const

@[simp] theorem ιx_apply (y : Euc 3) : ιx P y = (y, 0) := rfl

theorem translateLp_smul (y : Euc 3) (c : ℂ) (u : X E P) :
    Heat.translateLp (ιx P) continuous_ιx y (c • u) =
      c • Heat.translateLp (ιx P) continuous_ιx y u :=
  (Lp.compMeasurePreservingₗ ℂ _ _).map_smul c u

theorem heatLp_smul (θ : ℝ) (c : ℂ) (u : X E P) :
    Heat.heatLp (ιx P) continuous_ιx θ (c • u) = c • Heat.heatLp (ιx P) continuous_ιx θ u := by
  by_cases hθ : 0 < θ
  · rw [Heat.heatLp_eq_integral _ _ ENNReal.ofNat_ne_top hθ,
      Heat.heatLp_eq_integral _ _ ENNReal.ofNat_ne_top hθ]
    simp_rw [translateLp_smul, smul_comm (gaussKernel 3 θ _) c]
    exact integral_smul c _
  · rw [Heat.heatLp_of_nonpos _ _ (not_lt.mp hθ)]
    rfl

/-- **The spatial heat semigroup `e^{θΔ_x}`** on the periodic `L²` (complex linear). For
`θ ≤ 0` it is the identity. -/
def heatC (θ : ℝ) : X E P →L[ℂ] X E P where
  toFun := Heat.heatLp (ιx P) continuous_ιx θ
  map_add' u v := map_add _ u v
  map_smul' := heatLp_smul θ
  cont := (Heat.heatLp (ιx P) continuous_ιx θ).continuous

theorem heatC_apply (θ : ℝ) (u : X E P) :
    heatC θ u = Heat.heatLp (ιx P) continuous_ιx θ u := rfl

/-- For `θ > 0`, `e^{θΔ_x}F(x, τ) = ∫ G_θ(y) F(x - y, τ) dy`. -/
theorem heatC_rep {θ : ℝ} (hθ : 0 < θ) (u : X E P) :
    (heatC θ u : PSpace P → E) =ᵐ[volume] Heat.heatConv (ιx P) θ u :=
  Heat.heatLp_rep _ _ hθ u

theorem heatC_of_nonpos {θ : ℝ} (hθ : θ ≤ 0) (u : X E P) : heatC θ u = u := by
  rw [heatC_apply, Heat.heatLp_of_nonpos _ _ hθ]
  rfl

theorem norm_heatC_apply_le (θ : ℝ) (u : X E P) : ‖heatC θ u‖ ≤ ‖u‖ :=
  Heat.norm_heatLp_apply_le _ _ θ u

theorem norm_heatC_le (θ : ℝ) : ‖(heatC θ : X E P →L[ℂ] X E P)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    rw [one_mul]; exact norm_heatC_apply_le θ u

theorem heatC_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (u : X E P) :
    heatC (s + t) u = heatC s (heatC t u) := by
  simp only [heatC_apply]
  rw [Heat.heatLp_add _ _ hs ht, ContinuousLinearMap.comp_apply]

theorem heatC_continuousOn (u : X E P) :
    ContinuousOn (fun θ => heatC θ u) (Ici 0) :=
  Heat.heatLp_continuousOn _ _ ENNReal.ofNat_ne_top u

/-! ### The phase translation -/

/-- `(x, τ) ↦ (x, τ - t)`. -/
def shiftT (P : ℝ) (t : ℝ) (z : PSpace P) : PSpace P := z - (0, (t : AddCircle P))

theorem mp_shiftT (t : ℝ) : MeasurePreserving (shiftT P t) volume volume :=
  measurePreserving_sub_right _ _

theorem shiftT_apply (t : ℝ) (z : PSpace P) : shiftT P t z = (z.1, z.2 - (t : AddCircle P)) := by
  ext <;> simp [shiftT]

/-- **The phase translation** `F ↦ F(·, · - t)` on the periodic `L²`. -/
def transC (t : ℝ) : X E P →ₗᵢ[ℂ] X E P :=
  Lp.compMeasurePreservingₗᵢ ℂ (shiftT P t) (mp_shiftT t)

theorem coeFn_transC (t : ℝ) (u : X E P) :
    (transC t u : PSpace P → E) =ᵐ[volume] fun z => u (shiftT P t z) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem shiftT_add (s t : ℝ) (z : PSpace P) : shiftT P (s + t) z = shiftT P t (shiftT P s z) := by
  simp only [shiftT, AddCircle.coe_add]
  ext <;> simp [sub_sub]

theorem transC_add (s t : ℝ) (u : X E P) : transC (s + t) u = transC s (transC t u) := by
  refine Lp.ext ?_
  have h1 := coeFn_transC (s + t) u
  have h2 := coeFn_transC s (transC t u)
  have h3 : (fun z => (transC t u : PSpace P → E) (shiftT P s z)) =ᵐ[volume]
      fun z => u (shiftT P t (shiftT P s z)) :=
    (mp_shiftT s).quasiMeasurePreserving.ae_eq_comp (coeFn_transC t u)
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  rw [hz1, hz2, hz3, shiftT_add]

theorem transC_zero (u : X E P) : transC 0 u = u := by
  refine Lp.ext ?_
  filter_upwards [coeFn_transC 0 u] with z hz
  rw [hz]
  simp only [shiftT, AddCircle.coe_zero, Prod.mk_zero_zero, sub_zero]

theorem transC_surjective (t : ℝ) : Function.Surjective (transC t : X E P → X E P) := fun u =>
  ⟨transC (-t) u, by rw [← transC_add, add_neg_cancel, transC_zero]⟩

/-- **The phase translation is unitary** (tex line 3354). -/
def transEquiv (t : ℝ) : X E P ≃ₗᵢ[ℂ] X E P :=
  LinearIsometryEquiv.ofSurjective (transC t) (transC_surjective t)

@[simp] theorem transEquiv_apply (t : ℝ) (u : X E P) : transEquiv t u = transC t u := rfl

/-- The shifts as a continuous family of continuous maps. -/
def shiftMapT (P : ℝ) [Fact (0 < P)] (t : ℝ) : C(PSpace P, PSpace P) :=
  ⟨shiftT P t, continuous_id.sub continuous_const⟩

theorem continuous_shiftMapT : Continuous (shiftMapT P) :=
  ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_snd.sub (continuous_const.prodMk
      ((AddCircle.continuous_mk' (p := P)).comp continuous_fst)))

theorem continuous_transC (u : X E P) : Continuous fun t => transC t u :=
  Continuous.compMeasurePreservingLp (μ := volume) (ν := volume) (E := E) (p := 2)
    (f := fun _ : ℝ => u) (g := shiftMapT P) continuous_const continuous_shiftMapT
    (fun t => mp_shiftT t) ENNReal.ofNat_ne_top

/-- The phase translation commutes with the spatial heat semigroup. -/
theorem heatC_transC (θ t : ℝ) (u : X E P) : heatC θ (transC t u) = transC t (heatC θ u) := by
  by_cases hθ : 0 < θ
  · refine Lp.ext ?_
    have h1 := heatC_rep hθ (transC t u)
    have h2 := Heat.heatConv_congr_ae (ιx P) continuous_ιx.measurable θ (coeFn_transC t u)
    have h3 := coeFn_transC t (heatC θ u)
    have h4 : (fun z => (heatC θ u : PSpace P → E) (shiftT P t z)) =ᵐ[volume]
        fun z => Heat.heatConv (ιx P) θ (u : PSpace P → E) (shiftT P t z) :=
      (mp_shiftT t).quasiMeasurePreserving.ae_eq_comp (heatC_rep hθ u)
    filter_upwards [h1, h2, h3, h4] with z hz1 hz2 hz3 hz4
    rw [hz1, hz2, hz3, hz4]
    simp only [Heat.heatConv, shiftT]
    congr 1
    funext y
    rw [sub_right_comm]
  · rw [heatC_of_nonpos (not_lt.mp hθ), heatC_of_nonpos (not_lt.mp hθ)]

end UnforcedLeray.B0223
