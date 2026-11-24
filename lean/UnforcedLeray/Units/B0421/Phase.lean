import UnforcedLeray.Units.B0421.FreeC
import UnforcedLeray.Lib.PhaseSpace.Test
import UnforcedLeray.Lib.LerayC.Phase
import UnforcedLeray.Lib.BochnerTime.Translation
import UnforcedLeray.Lib.Semigroups.Laplace

/-!
# B0421 helper: the phase-translated free semigroup on `Y_q`

Blueprint unit B0421, `paper/main.tex` lines 7427–7445: "Phase translation is an isometry on
`Y_q`, so `R_μ f(τ) = ∫_0^∞ e^{-μr} S_ν(r) P_σ f(τ-r) dr` converges as a Bochner integral".
The integrand is `e^{-μr} 𝒯(r) P_σ f` for the operators

  `𝒯(r) g (τ) = S_ν(r) (g(τ - r))`, i.e. `𝒯(r) = (S_ν(r) slice-wise) ∘ (translation by -r)`,

on `Y_q = L^q(ℝ/Pℤ; L^q(ℝ³; ℂ³))` (decision D2). This file proves that `𝒯` is an exponentially
bounded strongly continuous semigroup on `Y_q` (`phaseSemigroup`, an instance of the drafted
`Infra.ExpSemigroup`, `Lib/Semigroups/ExpSemigroup.lean`), so that the Laplace-transform API of
`Lib/Semigroups/Laplace.lean` (INF07 T7.2) applies.

* `tendsto_compLpL_apply`: dominated convergence for slice-wise operators (a strongly
  convergent, eventually bounded family `A_i` gives `A_i g(·) → A₀ g(·)` in `L^q`, `q < ∞`).
* `shiftY σ`: phase translation `g ↦ g(σ + ·)` (Mathlib's `DomAddAct` action) as an isometric
  `ℂ`-linear operator; strong continuity is `BochnerTime.continuous_translate_addCircle`.
* `phaseT hq ν r = (freeC hq ν r) slice-wise ∘ shiftY (-r)`, with `coeFn_phaseT` (the literal
  `𝒯(r)g(τ) = S_ν(r) g(τ - r)`), `phaseT_zero`, `phaseT_add`, `continuousOn_phaseT`,
  `norm_phaseT_le`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UnforcedLeray.B0421

open UnforcedLeray.PhaseSpace (CVec3 Yq)
open UnforcedLeray.B0418

/-! ### Dominated convergence for slice-wise operators -/

section DCT

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- If `A_i → A₀` strongly and `‖A_i‖ ≤ B` eventually, then `A_i g(·) → A₀ g(·)` in `L^q(μ; F)`
for every `g ∈ L^q(μ; E)`, `1 ≤ q < ∞` (dominated convergence). -/
theorem tendsto_compLpL_apply {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] (hq : q ≠ ∞)
    {A : ι → E →L[ℂ] F} {A₀ : E →L[ℂ] F} (hA : ∀ e, Tendsto (fun i => A i e) l (𝓝 (A₀ e)))
    {B : ℝ} (hB : ∀ᶠ i in l, ‖A i‖ ≤ B) (x : Lp E q μ) :
    Tendsto (fun i => (A i).compLpL q μ x) l (𝓝 (A₀.compLpL q μ x)) := by
  have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
  have hq0 : q ≠ 0 := (lt_of_lt_of_le one_pos hq1).ne'
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  set D : ι → α → F := fun i a => (A i - A₀) (x a) with hD
  have hdist : ∀ i, dist ((A i).compLpL q μ x) (A₀.compLpL q μ x) =
      (eLpNorm (D i) q μ).toReal := by
    intro i
    rw [Lp.dist_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [(A i).coeFn_compLpL (p := q) (μ := μ) x,
      A₀.coeFn_compLpL (p := q) (μ := μ) x] with a h1 h2
    rw [Pi.sub_apply, h1, h2]
    rfl
  have hfin : ∫⁻ a, (ENNReal.ofReal (B + ‖A₀‖) * ‖x a‖ₑ) ^ q.toReal ∂μ ≠ ∞ := by
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hqr.le]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hqr.le ENNReal.ofReal_ne_top)]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hqr.le ENNReal.ofReal_ne_top)
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hq0 hq (Lp.memLp x).2).ne
  have hint : Tendsto (fun i => ∫⁻ a, ‖D i a‖ₑ ^ q.toReal ∂μ) l (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence' (μ := μ) (l := l)
      (F := fun i a => ‖D i a‖ₑ ^ q.toReal) (f := fun _ => 0)
      (fun a => (ENNReal.ofReal (B + ‖A₀‖) * ‖x a‖ₑ) ^ q.toReal)
      (Eventually.of_forall fun i =>
        (((A i - A₀).continuous.comp_aestronglyMeasurable
          (Lp.aestronglyMeasurable x)).enorm).pow_const _)
      (hB.mono fun i hi => Eventually.of_forall fun a => by
        have hB0 : 0 ≤ B + ‖A₀‖ := by
          have := norm_nonneg (A i)
          have := norm_nonneg A₀
          linarith
        refine ENNReal.rpow_le_rpow ?_ hqr.le
        calc ‖D i a‖ₑ = ENNReal.ofReal ‖D i a‖ := (ofReal_norm _).symm
          _ ≤ ENNReal.ofReal ((B + ‖A₀‖) * ‖x a‖) := by
              refine ENNReal.ofReal_le_ofReal (((A i - A₀).le_opNorm (x a)).trans ?_)
              refine mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
              linarith
          _ = ENNReal.ofReal (B + ‖A₀‖) * ‖x a‖ₑ := by
              rw [ENNReal.ofReal_mul hB0, ofReal_norm])
      hfin
      (Eventually.of_forall fun a => by
        have h1 : Tendsto (fun i => ‖D i a‖ₑ) l (𝓝 0) := by
          have h0 := (hA (x a)).sub_const (A₀ (x a))
          rw [sub_self] at h0
          have h0' : Tendsto (fun i => D i a) l (𝓝 0) := by
            refine h0.congr fun i => ?_
            rfl
          simpa using h0'.enorm
        have h2 := ((ENNReal.continuous_rpow_const (y := q.toReal)).tendsto 0).comp h1
        simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hqr] using h2)
    simpa using h
  have heLp : Tendsto (fun i => eLpNorm (D i) q μ) l (𝓝 0) := by
    simp_rw [eLpNorm_eq_eLpNorm' hq0 hq, eLpNorm']
    have h := ((ENNReal.continuous_rpow_const (y := 1 / q.toReal)).tendsto 0).comp hint
    simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (inv_pos.2 hqr)] using h
  rw [tendsto_iff_dist_tendsto_zero]
  simp_rw [hdist]
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp heLp
  simpa [Function.comp_def] using h

theorem compLpL_one (x : Lp E q μ) : (1 : E →L[ℂ] E).compLpL q μ x = x := by
  apply Lp.ext
  filter_upwards [(1 : E →L[ℂ] E).coeFn_compLpL (p := q) (μ := μ) x] with a h
  rw [h]
  rfl

theorem compLpL_comp (L N : E →L[ℂ] E) (x : Lp E q μ) :
    (L.comp N).compLpL q μ x = L.compLpL q μ (N.compLpL q μ x) := by
  apply Lp.ext
  filter_upwards [(L.comp N).coeFn_compLpL (p := q) (μ := μ) x,
    L.coeFn_compLpL (p := q) (μ := μ) (N.compLpL q μ x),
    N.coeFn_compLpL (p := q) (μ := μ) x] with a h1 h2 h3
  rw [h1, h2, h3]
  rfl

end DCT

/-- If `A_i → A₀` strongly, `‖A_i‖ ≤ B` eventually and `y_i → y₀`, then `A_i y_i → A₀ y₀`. -/
theorem tendsto_apply_of_strong {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] {ι : Type*} {l : Filter ι}
    {A : ι → X →L[ℂ] Y} {A₀ : X →L[ℂ] Y} (hA : ∀ e, Tendsto (fun i => A i e) l (𝓝 (A₀ e)))
    {B : ℝ} (hB : ∀ᶠ i in l, ‖A i‖ ≤ B) {y : ι → X} {y₀ : X} (hy : Tendsto y l (𝓝 y₀)) :
    Tendsto (fun i => A i (y i)) l (𝓝 (A₀ y₀)) := by
  have h1 : Tendsto (fun i => A i (y i - y₀)) l (𝓝 0) := by
    have hy' : Tendsto (fun i => B * ‖y i - y₀‖) l (𝓝 0) := by
      simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hy).const_mul B
    refine squeeze_zero_norm' ?_ hy'
    filter_upwards [hB] with i hi
    exact ((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
  have h2 := h1.add (hA y₀)
  rw [zero_add] at h2
  refine h2.congr fun i => ?_
  rw [← map_add, sub_add_cancel]

/-! ### Phase translation on `Y_q` -/

section Phase

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- Phase translation `g ↦ g(σ + ·)` on `Y_q`, an isometric `ℂ`-linear operator ("phase
translation is an isometry on `Y_q`", tex 7429–7430). -/
def shiftY (σ : AddCircle P) : Yq P q →L[ℂ] Yq P q :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun τ : AddCircle P => σ +ᵥ τ)
    (measurePreserving_vadd σ (AddCircle.haarAddCircle (T := P)))).toContinuousLinearMap

theorem shiftY_apply (σ : AddCircle P) (g : Yq P q) : shiftY σ g = DomAddAct.mk σ +ᵥ g := rfl

theorem norm_shiftY_apply (σ : AddCircle P) (g : Yq P q) : ‖shiftY σ g‖ = ‖g‖ := by
  rw [shiftY_apply, DomAddAct.norm_vadd_Lp]

theorem norm_shiftY_le (σ : AddCircle P) : ‖(shiftY σ : Yq P q →L[ℂ] Yq P q)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => by
    rw [norm_shiftY_apply, one_mul]

theorem shift_neg_add (s t : ℝ) (g : Yq P q) :
    DomAddAct.mk (-((s + t : ℝ) : AddCircle P)) +ᵥ g =
      DomAddAct.mk (-(s : AddCircle P)) +ᵥ (DomAddAct.mk (-(t : AddCircle P)) +ᵥ g) := by
  have h : -((s + t : ℝ) : AddCircle P) = -(t : AddCircle P) + -(s : AddCircle P) := by
    rw [AddCircle.coe_add, neg_add_rev]
  rw [h, DomAddAct.mk_add, ← vadd_vadd]

/-- Phase translation is strongly continuous: `r ↦ g(· - r)` is continuous into `Y_q`. -/
theorem continuous_shift_neg (hq : q ≠ ∞) (g : Yq P q) :
    Continuous fun r : ℝ => DomAddAct.mk (-(r : AddCircle P)) +ᵥ g := by
  have : Fact (q ≠ ∞) := ⟨hq⟩
  exact (BochnerTime.continuous_translate_addCircle g).comp
    ((AddCircle.continuous_mk' P).neg)

/-! ### The phase-translated free semigroup `𝒯(r)` -/

/-- **`𝒯(r) g(τ) = S_ν(r) g(τ - r)`** on `Y_q`: the free semigroup applied slice by slice after
the phase translation by `-r` (the integrand operator of `eq:free-stress-9`, tex 7432–7434). -/
def phaseT (hq : q ≠ ∞) (ν r : ℝ) : Yq P q →L[ℂ] Yq P q :=
  ((freeC hq ν r).compLpL q (AddCircle.haarAddCircle (T := P))).comp
    (shiftY (-(r : AddCircle P)))

theorem phaseT_apply (hq : q ≠ ∞) (ν r : ℝ) (g : Yq P q) :
    phaseT hq ν r g = (freeC hq ν r).compLpL q AddCircle.haarAddCircle
      (DomAddAct.mk (-(r : AddCircle P)) +ᵥ g) := rfl

/-- The slice-wise operator and the phase translation commute (`RieszLp.compLpL_vadd`). -/
theorem phaseT_apply' (hq : q ≠ ∞) (ν r : ℝ) (g : Yq P q) :
    phaseT hq ν r g = DomAddAct.mk (-(r : AddCircle P)) +ᵥ
      (freeC hq ν r).compLpL q AddCircle.haarAddCircle g := by
  exact RieszLp.compLpL_vadd (freeC hq ν r) (DomAddAct.mk (-(r : AddCircle P))) g

/-- The literal integrand of `eq:free-stress-9`: `(𝒯(r)g)(τ) = S_ν(r)(g(τ - r))` for a.e. `τ`. -/
theorem coeFn_phaseT (hq : q ≠ ∞) (ν r : ℝ) (g : Yq P q) :
    (phaseT hq ν r g : AddCircle P → Lp CVec3 q (volume : Measure Space)) =ᵐ[AddCircle.haarAddCircle]
      fun τ => freeC hq ν r (g (τ - r)) := by
  rw [phaseT_apply]
  have h1 := (freeC hq ν r).coeFn_compLpL (p := q) (μ := AddCircle.haarAddCircle (T := P))
    (DomAddAct.mk (-(r : AddCircle P)) +ᵥ g)
  have h2 := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-(r : AddCircle P))) g
  filter_upwards [h1, h2] with τ e1 e2
  rw [e1, e2]
  congr 2
  change -(r : AddCircle P) + τ = τ - r
  abel

set_option maxHeartbeats 1600000 in
theorem shiftY_zero_coe (g : Yq P q) : shiftY (-((0 : ℝ) : AddCircle P)) g = g := by
  have h0 : DomAddAct.mk (-((0 : ℝ) : AddCircle P)) = 0 := by
    rw [AddCircle.coe_zero, neg_zero]
    rfl
  rw [shiftY_apply, h0, zero_vadd]

set_option maxHeartbeats 1600000 in
theorem shiftY_neg_add (s t : ℝ) (g : Yq P q) :
    shiftY (-((s + t : ℝ) : AddCircle P)) g =
      shiftY (-(s : AddCircle P)) (shiftY (-(t : AddCircle P)) g) := by
  rw [shiftY_apply, shiftY_apply, shiftY_apply, shift_neg_add]

set_option maxHeartbeats 1600000 in
theorem compLpL_shiftY (A : Lp CVec3 q (volume : Measure Space) →L[ℂ] Lp CVec3 q volume)
    (σ : AddCircle P) (g : Yq P q) :
    A.compLpL q AddCircle.haarAddCircle (shiftY σ g) =
      shiftY σ (A.compLpL q AddCircle.haarAddCircle g) := by
  rw [shiftY_apply, shiftY_apply]
  exact RieszLp.compLpL_vadd A (DomAddAct.mk σ) g

theorem phaseT_zero_apply (hq : q ≠ ∞) (ν : ℝ) (g : Yq P q) : phaseT hq ν 0 g = g := by
  change (freeC hq ν 0).compLpL q AddCircle.haarAddCircle (shiftY (-((0 : ℝ) : AddCircle P)) g) = g
  rw [freeC_zero, compLpL_one, shiftY_zero_coe]

theorem phaseT_zero (hq : q ≠ ∞) (ν : ℝ) : (phaseT hq ν 0 : Yq P q →L[ℂ] Yq P q) = 1 :=
  ContinuousLinearMap.ext fun g => phaseT_zero_apply hq ν g

set_option maxHeartbeats 1600000 in
theorem phaseT_add_apply (hq : q ≠ ∞) {ν : ℝ} (hν : 0 ≤ ν) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (g : Yq P q) : phaseT hq ν (s + t) g = phaseT hq ν s (phaseT hq ν t g) := by
  change (freeC hq ν (s + t)).compLpL q AddCircle.haarAddCircle
      (shiftY (-((s + t : ℝ) : AddCircle P)) g) =
    (freeC hq ν s).compLpL q AddCircle.haarAddCircle (shiftY (-(s : AddCircle P))
      ((freeC hq ν t).compLpL q AddCircle.haarAddCircle (shiftY (-(t : AddCircle P)) g)))
  rw [freeC_add hq hν hs ht, shiftY_neg_add, compLpL_comp]
  exact congrArg (fun z => (freeC hq ν s).compLpL q AddCircle.haarAddCircle z)
    (compLpL_shiftY (freeC hq ν t) (-(s : AddCircle P)) (shiftY (-(t : AddCircle P)) g))

theorem phaseT_add (hq : q ≠ ∞) {ν : ℝ} (hν : 0 ≤ ν) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (phaseT hq ν (s + t) : Yq P q →L[ℂ] Yq P q) = (phaseT hq ν s).comp (phaseT hq ν t) :=
  ContinuousLinearMap.ext fun g => phaseT_add_apply hq hν hs ht g

theorem norm_phaseT_le (hq : q ≠ ∞) (ν r : ℝ) :
    ‖(phaseT hq ν r : Yq P q →L[ℂ] Yq P q)‖ ≤ ‖freeC hq ν r‖ := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc _ ≤ ‖freeC hq ν r‖ * 1 :=
        mul_le_mul (ContinuousLinearMap.norm_compLpL_le _) (norm_shiftY_le _) (norm_nonneg _)
          (norm_nonneg _)
    _ = ‖freeC hq ν r‖ := mul_one _

/-- `‖S_ν(r)‖` is bounded near every `r₀ ≥ 0` (within `[0, ∞)`). -/
theorem eventually_norm_freeC_le (hq : q ≠ ∞) (ν r₀ : ℝ) :
    ∀ᶠ r in 𝓝[Ici 0] r₀, ‖freeC hq ν r‖ ≤ 2 * Real.exp (|gammaExp q| * (r₀ + 1)) := by
  have hlt : ∀ᶠ r in 𝓝[Ici 0] r₀, r < r₀ + 1 :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by linarith))
  filter_upwards [hlt, self_mem_nhdsWithin] with r hr hr0
  refine (norm_freeC_le hq ν r).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
  have h0 : (0 : ℝ) ≤ r := hr0
  calc -gammaExp q * r ≤ |gammaExp q| * r :=
        mul_le_mul_of_nonneg_right (neg_le_abs _) h0
    _ ≤ |gammaExp q| * (r₀ + 1) := mul_le_mul_of_nonneg_left hr.le (abs_nonneg _)

/-- Strong continuity of `S_ν` acting slice by slice on `Y_q`, on `[0, ∞)`. -/
theorem continuousOn_freeY (hq : q ≠ ∞) {ν : ℝ} (hν : 0 ≤ ν) (g : Yq P q) :
    ContinuousOn (fun r => (freeC hq ν r).compLpL q (AddCircle.haarAddCircle (T := P)) g)
      (Ici 0) :=
  fun r₀ hr₀ => tendsto_compLpL_apply hq (fun F => continuousOn_freeC hq hν F r₀ hr₀)
    (eventually_norm_freeC_le hq ν r₀) g

/-- Strong continuity of `𝒯` on `[0, ∞)`. -/
theorem continuousOn_phaseT (hq : q ≠ ∞) {ν : ℝ} (hν : 0 ≤ ν) (g : Yq P q) :
    ContinuousOn (fun r => phaseT hq ν r g) (Ici 0) := by
  intro r₀ hr₀
  have hB' : ∀ᶠ r in 𝓝[Ici 0] r₀, ‖(freeC hq ν r).compLpL q (AddCircle.haarAddCircle (T := P))‖ ≤
      2 * Real.exp (|gammaExp q| * (r₀ + 1)) :=
    (eventually_norm_freeC_le hq ν r₀).mono fun r hr =>
      (ContinuousLinearMap.norm_compLpL_le _).trans hr
  have hy : Tendsto (fun r : ℝ => DomAddAct.mk (-(r : AddCircle P)) +ᵥ g) (𝓝[Ici 0] r₀)
      (𝓝 (DomAddAct.mk (-(r₀ : AddCircle P)) +ᵥ g)) :=
    ((continuous_shift_neg hq g).tendsto r₀).mono_left nhdsWithin_le_nhds
  exact tendsto_apply_of_strong (fun e => continuousOn_freeY hq hν e r₀ hr₀) hB' hy

/-- **`𝒯` is an exponentially bounded strongly continuous semigroup on `Y_q`** for `ν ≥ 0`,
with growth rate `ω = -γ_q` and any constant `M` bounding `e^{γ_q r} ‖S_ν(r)‖` on `L^q(ℂ³)`
(`M = 2` always, `norm_freeC_le`; `M = 1` at `q = 2`, `norm_freeC_two_le`). -/
def phaseSemigroup (hq : q ≠ ∞) {ν : ℝ} (hν : 0 ≤ ν) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ r, 0 ≤ r → ‖freeC hq ν r‖ ≤ M * Real.exp (-gammaExp q * r)) :
    Infra.ExpSemigroup (Yq P q) where
  T := phaseT hq ν
  T_zero := phaseT_zero hq ν
  T_add _ _ hs ht := phaseT_add hq hν hs ht
  T_cont g := continuousOn_phaseT hq hν g
  M := M
  ω := -gammaExp q
  M_nonneg := hM0
  T_le r hr := (norm_phaseT_le hq ν r).trans (hM r hr)

end Phase

end UnforcedLeray.B0421
